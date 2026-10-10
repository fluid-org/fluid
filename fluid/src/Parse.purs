module Parse where

import Prelude

import Control.Alt ((<|>))
import Control.Lazy (defer)
import Control.Monad.State (StateT)
import Data.Array (reverse, some)
import Data.Bifunctor (lmap)
import Data.CodePoint.Unicode (isSpace)
import Bind (Bind, Name, Var, varAnon, (↦))
import Data.Either (Either(..))
import Data.Foldable (foldl)
import Data.Identity (Identity)
import Data.List (List(..), nub, (:))
import Data.List.NonEmpty (NonEmptyList(..), cons, toList)
import Data.Maybe (Maybe(..), fromMaybe, maybe)
import Data.NonEmpty ((:|))
import Data.String (codePointFromChar)
import Data.String.CodeUnits as SCU
import Data.Traversable (foldr)
import Literal (Literal(..))
import Parse.Number (float, integer)
import Parse.Parser (Parser, align, block, braces, brackets, close, commas, context, delim, fields, lexeme, parens, reserved, reservedOperator, stringLiteral, trailingCommas, variable, whitespace)
import Parsing (ParseError(..), Position(..), consume, fail, runParserT)
import Parsing.Combinators (choice, lookAhead, many, many1, option, optionMaybe, sepBy1, try, (<?>))
import Parsing.Expr (Operator(..)) as P
import Parsing.Expr (OperatorTable, buildExprParser)
import Parsing.Indent (runIndent, sameOrIndented, withPos)
import Parsing.String (eof, satisfy)
import Operator (Operator(..), assoc, binopSymbol, levels, unopSymbol)
import Expr (Binop(..), Pattern(..))
import SExpr (Branch, Clause(..), Expr(..), Import(..), LambdaClause(..), Module(..), Param(..), ParagraphElem(..), Qualifier(..), RecDefs, Stmt(..), TypeExpr(..), VarDef(..), VarDefs)
import Types (Primitive(..)) as T
import Util (MayFail, type (+), type (×), nonEmpty, singleton, (×))

pattern :: Parser Pattern
pattern = defer \_ -> do
   p <- simplePattern
   optionMaybe (reserved "as" *> variable) <#> maybe p (PAs p)

simplePattern :: Parser Pattern
simplePattern = pLit <|> pConstr <|> pVar <|> pRecord <|> pList <|> parensPattern
   where
   pLit :: Parser Pattern
   pLit = literal <#> PLit

   pVar :: Parser Pattern
   pVar = variable <#> \x -> if x == varAnon then PWild else PVar x

   pConstr :: Parser Pattern
   pConstr = defer \_ -> do
      q <- try (qualifiedName <* delim '(')
      args <- commas constrArg
      delim ')'
      pure $ PConstr q (takeLefts args) (takeRights args)
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
   pRecord = defer \_ -> braces (fields stringLiteral pattern) <#> PRecord

   pList :: Parser Pattern
   pList = defer \_ -> brackets (trailingCommas pattern) <#> PList

   parensPattern :: Parser Pattern
   parensPattern = do
      delim '('
      choice
         [ delim ')' $> PTuple Nil
         , do
              p <- pattern
              choice
                 [ delim ')' $> p
                 , do
                      delim ','
                      ps <- trailingCommas pattern
                      delim ')'
                      pure $ PTuple (p : ps)
                 ]
         ]

typeExpr :: Parser TypeExpr
typeExpr = defer \_ -> do
   ψ <- typeAtom
   ψs <- many (reservedOperator "|" *> typeAtom)
   pure (foldl UnionTy ψ ψs)
   where
   typeAtom :: Parser TypeExpr
   typeAtom = defer \_ -> (reserved "None" $> PrimitiveTy T.None) <|> (qualifiedName >>= namedType)

   namedType :: Name -> Parser TypeExpr
   namedType (NonEmptyList (x :| Nil)) = case x of
      "Never" -> pure (PrimitiveTy T.Never)
      "Sized" -> pure (PrimitiveTy T.Sized)
      "Callable" -> brackets (CallableTy <$> brackets (commas typeExpr) <* delim ',' <*> typeExpr)
      "Literal" -> LitTy <$> brackets literal
      "object" -> pure (PrimitiveTy T.Object)
      "bool" -> pure (PrimitiveTy T.Bool)
      "int" -> pure (PrimitiveTy T.Int)
      "float" -> pure (PrimitiveTy T.Float)
      "str" -> pure (PrimitiveTy T.Str)
      "list" -> ListTy <$> brackets typeExpr
      "tuple" -> TupleTy <$> brackets ((delim '(' *> delim ')' $> Nil) <|> commas typeExpr)
      "dict" -> brackets (reserved "str" *> delim ',' *> (DictTy <$> typeExpr))
      _ -> NameTy (singleton x) <$> typeArgs
   namedType q = NameTy q <$> typeArgs

   typeArgs :: Parser (List TypeExpr)
   typeArgs = defer \_ -> option Nil (brackets (commas typeExpr))

typeParams :: Parser (List Var)
typeParams = do
   αs <- option Nil (brackets (commas variable))
   when (nub αs /= αs) $ fail "Duplicate type parameter"
   pure αs

literal :: Parser Literal
literal =
   try (float <#> Float)
      <|> (integer <#> Int)
      <|> (stringLiteral <#> Str)
      <|> (reserved "True" $> Bool true)
      <|> (reserved "False" $> Bool false)
      <|> (reserved "None" $> None)

varDef :: Parser VarDef
varDef = do
   p × ψ <- try do
      p <- pattern
      ψ <- optionMaybe (delim ':' *> typeExpr)
      reservedOperator "="
      pure (p × ψ)
   e <- sameOrIndented *> withPos expr
   pure $ VarDef p ψ e

varDefs :: Parser VarDefs
varDefs = many1 varDef

stmt :: Parser Stmt
stmt = defer \_ -> ifStmt <|> matchStmt <|> defStmt <|> returnStmt <|> (reserved "pass" *> pure Pass) <|> assertStmt <|> misplacedImport <|> (expr <#> ExprStmt)

returnStmt :: Parser Stmt
returnStmt = do
   reserved "return"
   e <- optionMaybe (sameOrIndented *> expr)
   pure $ Return $ fromMaybe (Lit None) e

assertStmt :: Parser Stmt
assertStmt = do
   reserved "assert"
   e <- expr
   msg <- optionMaybe (delim ',' *> expr)
   pure $ Assert e msg

topStmt :: Parser Stmt
topStmt = defer \_ -> typeAliasStmt <|> dataclassStmt <|> stmt

stmts :: Parser Stmt
stmts = defer \_ -> many1 (align stmt) <#> foldr1Seq

-- Top-level programs may omit 'return' on the trailing expression that gives
-- the program its value. Inside functions and other block bodies, 'return'
-- is required.
programStmt :: Parser Stmt
programStmt = defer \_ -> ifStmt <|> matchStmt <|> typeAliasStmt <|> defStmt <|> dataclassStmt <|> returnStmt <|> (reserved "pass" *> pure Pass) <|> assertStmt <|> misplacedImport <|> (Return <$> expr)

programStmts :: Parser Stmt
programStmts = defer \_ -> many1 (align programStmt) <#> foldr1Seq

foldr1Seq :: NonEmptyList Stmt -> Stmt
foldr1Seq (NonEmptyList (s :| ss)) = case ss of
   Nil -> s
   s' : rest -> Seq s (foldr1Seq (NonEmptyList (s' :| rest)))

defStmt :: Parser Stmt
defStmt = defer \_ -> defRecStmt <|> defValStmt
   where
   defRecStmt = defer \_ -> DefRec <$> recDefs
   defValStmt = defer \_ -> Def <$> varDef

ifStmt :: Parser Stmt
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

matchStmt :: Parser Stmt
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

blockBody :: Parser Stmt
blockBody = defer \_ -> block stmts

decorator :: String -> Parser Unit
decorator name = try (delim '@' *> reserved name)

dataclassStmt :: Parser Stmt
dataclassStmt = do
   decorator "dataclass"
   reserved "class"
   c <- variable
   αs <- typeParams
   b <- optionMaybe (parens typeExpr)
   let
      fieldDecl = do
         x <- variable
         delim ':'
         ψ <- typeExpr
         pure (x × ψ)
   xs <- block ((reserved "pass" $> Nil) <|> (toList <$> many1 (align fieldDecl)))
   pure $ Dataclass c αs b xs

typeAliasStmt :: Parser Stmt
typeAliasStmt = do
   x × αs <- try (reserved "type" *> ((×) <$> variable <*> typeParams) <* reservedOperator "=")
   TypeAlias x αs <$> typeExpr

recDefs :: Parser RecDefs
recDefs = many1 recDef
   where
   recDef :: Parser Branch
   recDef = do
      f × αs <- try (reserved "def" *> ((×) <$> variable <*> typeParams) <* delim '(')
      ps <- commas param
      delim ')'
      ψ <- optionMaybe (reservedOperator "->" *> typeExpr)
      s <- blockBody
      pure $ f × Clause (αs × ps × ψ × s)

   param :: Parser Param
   param = Param <$> pattern <*> optionMaybe (delim ':' *> typeExpr)

expr :: Parser Expr
expr = context "expr" $ cond <?> "expression"
   where
   cond :: Parser Expr
   cond = defer \_ -> do
      e1 <- opTree
      option e1 $ try do
         reserved "if"
         e <- opTree
         reserved "else"
         e2 <- expr
         pure $ Cond e1 e e2

   opTree :: Parser Expr
   opTree = context "opTree" (buildExprParser opTable simpleChain) <* consume -- otherwise always `consume: false`
      where

      opTable :: OperatorTable (StateT Position Identity) String Expr
      opTable = reverse levels <#> map toOperator -- tightest first
         where
         toOperator :: Operator -> P.Operator (StateT Position Identity) String Expr
         toOperator op@(Binary b) = P.Infix (symbol b $> \e e' -> BinOp e b e') (assoc op)
         toOperator (Unary u) = P.Prefix (word (unopSymbol u) $> UnOp u)
         toOperator op@AndOp = P.Infix (reserved "and" $> And) (assoc op)
         toOperator op@OrOp = P.Infix (reserved "or" $> Or) (assoc op)
         toOperator op@InfixOp = P.Infix (try (delim '|' *> variable) <* delim '|' <#> \f e e' -> InfixApp e f e') (assoc op)

         symbol :: Binop -> Parser Unit
         symbol In = reserved "in"
         symbol NotIn = try (reserved "not" *> reserved "in")
         symbol b = reservedOperator (binopSymbol b)

         word :: String -> Parser Unit
         word "not" = reserved "not"
         word sym = reservedOperator sym

      simpleChain :: Parser Expr
      simpleChain = withPos (simple >>= chain)
         where
         chain :: Expr -> Parser Expr
         chain e = sameOrIndented *> (project <|> typeApp <|> dproject <|> app Nil) <|> pure e
            where
            project :: Parser Expr
            project = do
               -- try because '.' can be captured from '..'
               k <- try do
                  delim '.'
                  variable
               chain (Attribute e k)

            dproject :: Parser Expr
            dproject = do
               delim '['
               k <- cond
               k' <- optionMaybe (delim ',' *> cond)
               close ']'
               chain (Subscript e (maybe k (\k2 -> Tuple (k : k2 : Nil)) k'))

            -- Type arguments of a constructor call; read back as subscript by checker if head not a class.
            typeApp :: Parser Expr
            typeApp
               | isName e = try (delim '[' *> commas typeExpr <* close ']' <* lookAhead (sameOrIndented *> delim '(')) >>= app
               | otherwise = fail "Expected name before type arguments"

            isName :: Expr -> Boolean
            isName (Var _) = true
            isName (Attribute e' _) = isName e'
            isName _ = false

            app :: List TypeExpr -> Parser Expr
            app ψs = do
               delim '('
               args <- commas arg
               close ')'
               chain (Call e ψs (takeLefts args) (takeRights args))
               where
               arg :: Parser (Expr + Bind Expr)
               arg = defer \_ -> (Right <$> try kwArg) <|> (Left <$> cond)

               kwArg :: Parser (Bind Expr)
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

      simple :: Parser Expr
      simple = context "simple" $
         matrix
            <|> bracketsExpr
            <|> lambda
            <|> dict
            <|> paragraph
            <|> lit
            <|> var
            <|> parensExpr
            <|> docExpr
               <?> "simple expression"
         where

         lambda :: Parser Expr
         lambda = context "lambda" do
            reserved "lambda"
            ps0 <- commas pattern
            delim ':'
            e <- cond
            pure $ Lambda (LambdaClause (ps0 × e))

         var :: Parser Expr
         var = variable <#> Var

         lit :: Parser Expr
         lit = literal <#> Lit

         paragraph :: Parser Expr
         paragraph = do
            delim "f\"\"\""
            es <- many $ lexeme paragraphElem
            delim "\"\"\""
            pure $ Paragraph es
            where
            paragraphElem :: Parser ParagraphElem
            paragraphElem = paragraphToken <|> unquote
               where
               paragraphToken :: Parser ParagraphElem
               paragraphToken = do
                  cs <- some paragraphLetter
                  pure $ Token (SCU.fromCharArray cs)

                  where
                  -- TODO: allow escaped `"` and `{`
                  paragraphLetter :: Parser Char
                  paragraphLetter = satisfy $ \c -> (c /= '"' && c /= '{' && not (isSpace (codePointFromChar c)))

               unquote :: Parser ParagraphElem
               unquote = defer $ \_ -> do
                  e <- braces (opTree)
                  pure $ Unquote e

         dict :: Parser Expr
         dict = context "dict" do
            delim '{'
            choice
               [ do
                    close '}'
                    pure $ Dictionary Nil
               , do
                    k <- key
                    delim ':'
                    e <- expr
                    choice
                       [ context "dictNonEmpty" do
                            delim ','
                            rest <- fields key expr
                            close '}'
                            pure $ Dictionary ((k × e) : rest)
                       , do
                            close '}'
                            pure $ Dictionary ((k × e) : Nil)
                       , context "dictComp" do
                            qs <- qualifiers
                            close '}'
                            pure $ DictComp k e qs
                       , fail "Expected `}`"
                       ]
               , fail "Expected `}` or a dictionary entry after `{`"
               ]

            where
            key :: Parser Expr
            key = defer \_ -> cond

         matrix :: Parser Expr
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
            pure $ Matrix e (x × y) e'

         bracketsExpr :: Parser Expr
         bracketsExpr = context "brackets" do
            delim '['
            choice
               [ do
                    close ']'
                    pure $ List Nil
               , do
                    e <- cond
                    choice
                       [ context "list" do
                            delim ','
                            rest <- trailingCommas cond
                            close ']'
                            pure $ List (e : rest)
                       , do
                            close ']'
                            pure $ List (e : Nil)
                       , context "listComp" do
                            qs <- qualifiers
                            close ']'
                            pure $ ListComp e qs
                       , fail "Expected `]"
                       ]
               , fail "Expected `]` or a list expression after `[`"
               ]

         qualifiers :: Parser (List Qualifier)
         qualifiers = toList <$> many1 (choice [ guard, decl, generator ])
            where
            guard = context "guard" do
               reserved "if"
               e <- opTree
               pure $ Guard e

            decl = context "decl" do
               reserved "def"
               p <- pattern
               delim ':'
               e <- opTree
               pure $ Decl (VarDef p Nothing e)

            generator = context "generator" do
               reserved "for"
               p <- pattern
               reserved "in"
               e <- opTree
               pure $ Generator p e

         parensExpr :: Parser Expr
         parensExpr = context "parens" do
            delim '('
            choice
               [ close ')' $> Tuple Nil
               , do
                    e <- cond
                    choice
                       [ close ')' $> e
                       , do
                            delim ','
                            es <- trailingCommas cond
                            close ')'
                            pure $ Tuple (e : es)
                       , fail "Expected `)` or `,` after `(expr`"
                       ]
               ]

         docExpr :: Parser Expr
         docExpr = context "doc expr" do
            decorator "doc"
            e <- parens opTree
            e' <- opTree
            pure $ DocExpr e e'

module_ :: Parser Module
module_ = do
   ιs <- many (align import_)
   ss <- many (align topStmt)
   pure $ Module ιs ss

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
      xs <- sepBy1 variable (delim ',')
      pure $ Import q (Just (toList xs))

modPath :: Parser Name
modPath = sepBy1 variable (delim '.')

qualifiedName :: Parser Name
qualifiedName = do
   prefix <- many (try (variable <* delim '.'))
   x <- variable
   pure (foldr cons (singleton x) prefix)

importName :: Import -> Name
importName (Import q _) = q

moduleImports :: Module -> List Name
moduleImports (Module ιs _) = importName <$> ιs

topLevel :: forall a. Parser a -> Parser a
topLevel p = whitespace *> withPos p <* whitespace <* eof

parse :: forall a. Parser a -> String -> MayFail a
parse parser input =
   lmap printError $ runIndent $ runParserT input parser
   where
   printError :: ParseError -> String
   printError (ParseError msg (Position { line, column })) =
      "ParseError on line " <> show line <> ", column " <> show column <> ":\n" <> msg

parseProgram :: String -> MayFail (Stmt × List Import)
parseProgram src = parse (topLevel programBody) src
   where
   programBody = do
      ιs <- many (align import_)
      s <- programStmts
      pure (s × ιs)

parseModule :: String -> MayFail (Module × List Name)
parseModule src = parse (topLevel module_) src <#> \m -> m × moduleImports m
