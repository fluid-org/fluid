module Parse where

import Prelude

import Control.Alt ((<|>))
import Control.Lazy (defer)
import Control.Monad.State (StateT)
import Data.Array (some)
import Data.Bifunctor (lmap)
import Data.CodePoint.Unicode (isSpace)
import Bind (Bind, Name, varAnon, (↦))
import Data.Either (Either(..))
import Data.Foldable (foldl)
import Data.Identity (Identity)
import Data.List (List(..), (:))
import Data.List.NonEmpty (NonEmptyList(..), cons, last, toList)
import Data.Maybe (Maybe(..), fromMaybe, maybe)
import Data.NonEmpty ((:|))
import Data.String (codePointFromChar)
import Data.String.CodeUnits as SCU
import Data.Traversable (foldr)
import DataType (cCons, cPair)
import Lattice (Raw)
import Literal (Literal)
import Literal (Literal(..)) as L
import Parse.Number (float, integer)
import Parse.Parser (Parser, align, block, braces, brackets, close, commas, constructor, context, delim, fields, lexeme, operator, parens, reserved, reservedOperator, stringLiteral, trailingCommas, variable, whitespace)
import Parsing (ParseError(..), Position(..), consume, fail, runParserT)
import Parsing.Combinators (choice, many, many1, option, optionMaybe, sepBy1, try, (<?>))
import Parsing.Expr (Assoc(..), Operator(..)) as P
import Parsing.Expr (Assoc(..), OperatorTable, buildExprParser)
import Parsing.Indent (runIndent, sameOrIndented, withPos)
import Parsing.String (eof, satisfy)
import Primitive.Parse (OpDef(..), OpType(..), Fixity(..), opDefs)
import Expr (Pattern(..))
import SExpr (Branch, Clause(..), DictEntry(..), Expr(..), Import(..), LambdaClause(..), ListRest(..), Module(..), Param(..), ParagraphElem(..), Qualifier(..), RecDefs, Stmt(..), VarDef(..), VarDefs)
import TypeExpr (TypeExpr)
import TypeExpr (Primitive(..), TypeExpr(..)) as T
import Util (type (+), type (×), error, nonEmpty, singleton, (×))

pattern :: Parser Pattern
pattern = defer \_ -> do
   p <- buildExprParser [ [ P.Infix pConsOp P.AssocRight ] ] simplePattern
   optionMaybe (reserved "as" *> variable) <#> maybe p (PAs p)

simplePattern :: Parser Pattern
simplePattern = pLit <|> pConstr <|> pVar <|> pRecord <|> pList <|> parensPattern
   where
   pVar :: Parser Pattern
   pVar = variable <#> \x -> if x == varAnon then PWild else PVar x

   pLit :: Parser Pattern
   pLit = literal <#> PLit

   pConstr :: Parser Pattern
   pConstr = defer \_ -> try do
      prefix <- many (try (variable <* delim '.'))
      c <- constructor
      args <- option Nil (parens (commas constrArg))
      let
         name = foldr cons (singleton c) prefix
         positionals = takeLefts args
         kws = takeRights args
      pure $ PConstr name positionals kws
      where
      constrArg :: Parser (Pattern + Bind Pattern)
      constrArg = defer \_ -> (Right <$> try kwArg) <|> (Left <$> simplePattern)

      kwArg :: Parser (Bind Pattern)
      kwArg = defer \_ -> do
         x <- variable
         delim '='
         p <- simplePattern
         pure (x ↦ p)

      takeLefts :: forall a b. List (a + b) -> List a
      takeLefts Nil = Nil
      takeLefts (Left x : xs) = x : takeLefts xs
      takeLefts (Right _ : _) = Nil

      takeRights :: forall a b. List (a + b) -> List b
      takeRights Nil = Nil
      takeRights (Right x : xs) = x : takeRights xs
      takeRights (Left _ : xs) = takeRights xs

   pRecord :: Parser Pattern
   pRecord = defer \_ -> braces (fields variable pattern) <#> PRecord

   pList :: Parser Pattern
   pList = defer \_ -> brackets (trailingCommas pattern) <#> PList

   parensPattern :: Parser Pattern
   parensPattern = do
      delim '('
      p <- pattern
      choice
         [ do
              delim ')'
              pure p
         , do
              delim ','
              p' <- pattern
              delim ')'
              pure $ PConstr (singleton (last cPair)) (p : p' : Nil) Nil
         ]

pConsOp :: Parser (Pattern -> Pattern -> Pattern)
pConsOp = do
   reservedOperator ":|"
   pure \e e' -> PConstr (singleton (last cCons)) (e : e' : Nil) Nil

typeExpr :: Parser TypeExpr
typeExpr = defer \_ -> do
   ψ <- typeAtom
   ψs <- many (reservedOperator "|" *> typeAtom)
   pure (foldl T.Union ψ ψs)
   where
   typeAtom :: Parser TypeExpr
   typeAtom = defer \_ -> constrType <|> varType

   constrType :: Parser TypeExpr
   constrType = do
      prefix <- many (try (variable <* delim '.'))
      c <- constructor
      case prefix, c of
         Nil, "Never" -> pure (T.Primitive T.Never)
         Nil, "None" -> pure (T.Primitive T.None)
         Nil, "Sized" -> pure (T.Primitive T.Sized)
         Nil, "Callable" -> brackets (T.Callable <$> brackets (commas typeExpr) <* delim ',' <*> typeExpr)
         Nil, "Literal" -> T.Lit <$> brackets literal
         _, _ -> pure (T.ClassName (foldr cons (singleton c) prefix))

   varType :: Parser TypeExpr
   varType = variable >>= case _ of
      "object" -> pure (T.Primitive T.Object)
      "bool" -> pure (T.Primitive T.Bool)
      "int" -> pure (T.Primitive T.Int)
      "float" -> pure (T.Primitive T.Float)
      "str" -> pure (T.Primitive T.Str)
      "list" -> T.List <$> brackets typeExpr
      "tuple" -> T.Tuple <$> brackets (commas typeExpr)
      "dict" -> brackets (reserved "str" *> delim ',' *> (T.Dict <$> typeExpr))
      x -> fail ("Not a type: " <> x)

literal :: Parser Literal
literal =
   try (float <#> L.Float)
      <|> (integer <#> L.Int)
      <|> (stringLiteral <#> L.Str)
      <|> try
         ( constructor >>= case _ of
              "True" -> pure (L.Bool true)
              "False" -> pure (L.Bool false)
              "None" -> pure L.None
              c -> fail ("Not a literal: " <> c)
         )

varDef :: Parser (Raw VarDef)
varDef = do
   p × ψ <- try do
      p <- pattern
      ψ <- optionMaybe (delim ':' *> typeExpr)
      reservedOperator "="
      pure (p × ψ)
   e <- sameOrIndented *> withPos expr
   pure $ VarDef p ψ e

varDefs :: Parser (Raw VarDefs)
varDefs = many1 varDef

stmt :: Parser (Raw Stmt)
stmt = defer \_ -> ifStmt <|> matchStmt <|> defStmt <|> dataclassStmt <|> returnStmt <|> (reserved "pass" *> pure Pass) <|> assertStmt <|> misplacedImport <|> (expr <#> ExprStmt)

returnStmt :: Parser (Raw Stmt)
returnStmt = do
   reserved "return"
   e <- optionMaybe (sameOrIndented *> expr)
   pure $ Return $ fromMaybe (Lit unit L.None) e

assertStmt :: Parser (Raw Stmt)
assertStmt = do
   reserved "assert"
   e <- expr
   msg <- optionMaybe (delim ',' *> expr)
   pure $ Assert e msg

stmts :: Parser (Raw Stmt)
stmts = defer \_ -> many1 (align stmt) <#> foldr1Seq

-- Top-level programs may omit 'return' on the trailing expression that gives
-- the program its value. Inside functions and other block bodies, 'return'
-- is required.
programStmt :: Parser (Raw Stmt)
programStmt = defer \_ -> ifStmt <|> matchStmt <|> defStmt <|> dataclassStmt <|> returnStmt <|> (reserved "pass" *> pure Pass) <|> assertStmt <|> misplacedImport <|> (Return <$> expr)

programStmts :: Parser (Raw Stmt)
programStmts = defer \_ -> many1 (align programStmt) <#> foldr1Seq

foldr1Seq :: forall a. NonEmptyList (Stmt a) -> Stmt a
foldr1Seq (NonEmptyList (s :| ss)) = case ss of
   Nil -> s
   s' : rest -> Seq s (foldr1Seq (NonEmptyList (s' :| rest)))

defStmt :: Parser (Raw Stmt)
defStmt = defer \_ -> defRecStmt <|> defValStmt
   where
   defRecStmt = defer \_ -> DefRec <$> recDefs
   defValStmt = defer \_ -> Def <$> varDef

ifStmt :: Parser (Raw Stmt)
ifStmt = defer \_ -> do
   let
      ifClause = do
         c <- expr
         b <- blockBody
         pure (c × b)
   reserved "if"
   c <- ifClause
   cs <- many (align $ reserved "elif" *> ifClause)
   b <- optionMaybe (align $ reserved "else" *> blockBody)
   pure $ If (nonEmpty (c : cs)) b

matchStmt :: Parser (Raw Stmt)
matchStmt = defer \_ -> do
   let
      branch = do
         reserved "case"
         p <- pattern
         b <- blockBody
         pure (p × b)
   reserved "match"
   e <- expr
   bs <- block (many1 (align branch))
   pure $ Match e bs

blockBody :: Parser (Raw Stmt)
blockBody = defer \_ -> block stmts

decorator :: String -> Parser Unit
decorator name = try (delim '@' *> reserved name)

dataclassStmt :: Parser (Raw Stmt)
dataclassStmt = do
   decorator "dataclass"
   reserved "class"
   c <- constructor
   b <- optionMaybe (parens constructor)
   let
      fieldDecl = do
         x <- variable
         delim ':'
         ψ <- typeExpr
         pure (x × ψ)
   xs <- block ((reserved "pass" $> Nil) <|> (toList <$> many1 (align fieldDecl)))
   pure $ Dataclass c b xs

recDefs :: Parser (Raw RecDefs)
recDefs = many1 recDef
   where
   recDef :: Parser (Raw Branch)
   recDef = do
      f <- try (reserved "def" *> variable <* delim '(')
      ps <- commas param
      delim ')'
      ψ <- optionMaybe (reservedOperator "->" *> typeExpr)
      s <- blockBody
      pure $ f × Clause unit (ps × ψ × s)

   param :: Parser Param
   param = Param <$> pattern <*> optionMaybe (delim ':' *> typeExpr)

expr :: Parser (Raw Expr)
expr = context "expr" $ cond <?> "expression"
   where
   cond :: Parser (Raw Expr)
   cond = defer \_ -> do
      e1 <- opTree
      option e1 $ try do
         reserved "if"
         e <- opTree
         reserved "else"
         e2 <- expr
         pure $ Cond e1 e e2

   opTree :: Parser (Raw Expr)
   opTree = context "opTree" (buildExprParser opTable simpleChain) <* consume -- otherwise always `consume: false`
      where

      opTable :: OperatorTable (StateT Position Identity) String (Raw Expr)
      opTable =
         opDefs # map (map toOperator)
         where
         toOperator :: OpDef -> P.Operator (StateT Position Identity) String (Raw Expr)
         toOperator (OpDef id fix opType) = case opType of
            Symbol -> op fix (reservedOperator id $> id)
            Ident -> op fix (reserved id $> id)
            CustomOp -> op (Infix AssocLeft) (try (delim '|' *> variable) <* delim '|')
            ConsOp -> P.Infix consOp AssocRight
            ProjectOp -> error "not implemented!"

         op :: Fixity -> Parser String -> P.Operator (StateT Position Identity) String (Raw Expr)
         op fix p = case fix of
            Infix assoc -> P.Infix (p <#> \id e e' -> BinaryApp e id e') assoc
            Prefix -> P.Prefix (p <#> \id e -> UnaryPrefixApp id e)
            Postfix -> error "not implemented!"

         consOp :: Parser (Raw Expr -> Raw Expr -> Raw Expr)
         consOp = do
            reservedOperator ":|"
            pure \e e' -> Constr unit (singleton (last cCons)) (e : e' : Nil) Nil

      simpleChain :: Parser (Raw Expr)
      simpleChain = withPos (simple >>= chain)
         where
         chain :: Raw Expr -> Parser (Raw Expr)
         chain e = sameOrIndented *> (project <|> dproject <|> app) <|> pure e
            where
            project :: Parser (Raw Expr)
            project = do
               -- try because '.' can be captured from '..'
               k <- try do
                  delim '.'
                  variable
               chain (Attribute e k)

            dproject :: Parser (Raw Expr)
            dproject = do
               delim '['
               k <- cond
               close ']'
               chain (Subscript e k)

            app :: Parser (Raw Expr)
            app = do
               delim '('
               e' <- case e of
                  Constr a c es Nil -> do
                     args <- commas constrArg
                     pure $ Constr a c (es <> takeLefts args) (takeRights args)
                  _ -> do
                     App e <$> commas cond
               close ')'
               chain e'
               where
               constrArg :: Parser (Raw Expr + Bind (Raw Expr))
               constrArg = defer \_ -> (Right <$> try kwArg) <|> (Left <$> cond)

               kwArg :: Parser (Bind (Raw Expr))
               kwArg = defer \_ -> do
                  x <- variable
                  delim '='
                  v <- cond
                  pure (x ↦ v)

               takeLefts :: forall p q. List (p + q) -> List p
               takeLefts (Left x : xs) = x : takeLefts xs
               takeLefts _ = Nil

               takeRights :: forall p q. List (p + q) -> List q
               takeRights (Right x : xs) = x : takeRights xs
               takeRights (Left _ : xs) = takeRights xs
               takeRights Nil = Nil

      simple :: Parser (Raw Expr)
      simple = context "simple" $
         matrix
            <|> bracketsExpr
            <|> lambda
            <|> dict
            <|> paragraph
            <|> lit
            <|> constr
            <|> var
            <|> parensExpr
            <|> docExpr
               <?> "simple expression"
         where

         lambda :: Parser (Raw Expr)
         lambda = context "lambda" do
            reserved "lambda"
            ps0 <- commas pattern
            delim ':'
            e <- cond
            pure $ Lambda (LambdaClause (ps0 × e))

         var :: Parser (Raw Expr)
         var = variable <#> Var

         constr :: Parser (Raw Expr)
         constr = try do
            prefix <- many (try (variable <* delim '.'))
            c <- constructor
            pure (Constr unit (foldr cons (singleton c) prefix) Nil Nil)

         lit :: Parser (Raw Expr)
         lit = literal <#> Lit unit

         paragraph :: Parser (Raw Expr)
         paragraph = do
            delim "f\"\"\""
            es <- many $ lexeme paragraphElem
            delim "\"\"\""
            pure $ Paragraph es
            where
            paragraphElem :: Parser (Raw ParagraphElem)
            paragraphElem = paragraphToken <|> unquote
               where
               paragraphToken :: Parser (Raw ParagraphElem)
               paragraphToken = do
                  cs <- some paragraphLetter
                  pure $ Token (SCU.fromCharArray cs)

                  where
                  -- TODO: allow escaped `"` and `{`
                  paragraphLetter :: Parser Char
                  paragraphLetter = satisfy $ \c -> (c /= '"' && c /= '{' && not (isSpace (codePointFromChar c)))

               unquote :: Parser (Raw ParagraphElem)
               unquote = defer $ \_ -> do
                  e <- braces (opTree)
                  pure $ Unquote e

         dict :: Parser (Raw Expr)
         dict = context "dict" do
            delim '{'
            kvs <- fields (exprKey <|> varKey) expr
            close '}'
            pure $ Dictionary unit kvs

            where
            exprKey :: Parser (Raw DictEntry)
            exprKey = defer \_ -> brackets cond <#> ExprKey

            varKey :: Parser (Raw DictEntry)
            varKey = variable <#> VarKey unit

         matrix :: Parser (Raw Expr)
         matrix = context "matrix" do
            delim "[|"
            e <- cond
            reserved "for"
            delim '('
            x <- variable
            delim ','
            y <- variable
            delim ')'
            reserved "in"
            e' <- cond
            delim "|]"
            pure $ Matrix unit e (x × y) e'

         bracketsExpr :: Parser (Raw Expr)
         bracketsExpr = context "brackets" do
            delim '['
            choice
               [ do
                    close ']'
                    pure $ ListEmpty unit
               , do
                    e <- cond
                    choice
                       [ context "listNonEmpty" do
                            delim ','
                            rest <- trailingCommas cond
                            close ']'
                            pure $ ListNonEmpty unit e (foldr (Next unit) (End unit) rest)
                       , do
                            close ']'
                            pure $ ListNonEmpty unit e (End unit)
                       , context "listEnum" do
                            delim ".."
                            e' <- cond
                            close ']'
                            pure $ ListEnum e e'

                       , context "listComp" do
                            qs <- many1 $ choice
                               [ context "listCompGuard" do
                                    reserved "if"
                                    e' <- opTree
                                    pure $ ListCompGuard e'
                               , context "listCompDecl" do
                                    reserved "def"
                                    p <- pattern
                                    delim ':'
                                    e' <- opTree
                                    pure $ ListCompDecl (VarDef p Nothing e')
                               , context "listCompGen" do
                                    reserved "for"
                                    p <- pattern
                                    reserved "in"
                                    e' <- opTree
                                    pure $ ListCompGen p e'
                               ]
                            close ']'
                            pure $ ListComp unit e (toList qs)
                       , fail "Expected `]"
                       ]
               , fail "Expected `]` or a list expression after `[`"
               ]

         parensExpr :: Parser (Raw Expr)
         parensExpr = context "parens" do
            delim '('
            choice
               [ do
                    op <- try (operator <* close ')')
                    pure $ Op op
               , do
                    e <- cond
                    choice
                       [ do
                            close ')'
                            pure e
                       , do
                            delim ','
                            e' <- cond
                            close ')'
                            pure $ Constr unit (singleton (last cPair)) (e : e' : Nil) Nil
                       , fail "Expected `)` or `,` after `(expr`"
                       ]
               , fail "Expected `op` or `expr` after `(`"
               ]

         docExpr :: Parser (Raw Expr)
         docExpr = context "doc expr" do
            decorator "doc"
            e <- parens opTree
            e' <- opTree
            pure $ DocExpr e e'

module_ :: Parser (Raw Module)
module_ = do
   is <- many (align import_)
   ss <- many1 (align stmt)
   pure $ Module is (toList ss)

misplacedImport :: forall a. Parser a
misplacedImport = (reserved "import" <|> reserved "from") *> fail "imports must precede statements"

import_ :: Parser Import
import_ = importAll <|> fromImport
   where
   importAll = reserved "import" *> (modPath <#> \q -> Import q Nothing)
   fromImport = do
      reserved "from"
      q <- modPath
      reserved "import"
      xs <- sepBy1 (variable <|> constructor) (delim ',')
      pure $ Import q (Just (toList xs))

modPath :: Parser Name
modPath = sepBy1 variable (delim '.')

importName :: Import -> Name
importName (Import q _) = q

moduleImports :: forall a. Module a -> List Name
moduleImports (Module is _) = importName <$> is

topLevel :: forall a. Parser a -> Parser a
topLevel p = whitespace *> withPos p <* whitespace <* eof

parse :: forall a. Parser a -> String -> Either String a
parse parser input =
   lmap printError $ runIndent $ runParserT input parser
   where
   printError :: ParseError -> String
   printError (ParseError msg (Position { line, column })) =
      "ParseError on line " <> show line <> ", column " <> show column <> ":\n" <> msg

parseProgram :: String -> Either String (Raw Stmt × List Import)
parseProgram src = parse (topLevel programBody) src
   where
   programBody = do
      is <- many (align import_)
      s <- programStmts
      pure (s × is)

parseModule :: String -> Either String (Raw Module × List Name)
parseModule src = parse (topLevel module_) src <#> \m -> m × moduleImports m
