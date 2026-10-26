module Parse where

import Prelude

import Control.Alt ((<|>))
import Control.Lazy (defer)
import Control.Monad.State (StateT)
import Data.Array (reverse, some)
import Data.Bifunctor (lmap)
import Data.CodePoint.Unicode (isSpace)
import Bind (Bind, Name, Var, varAnon, (↦))
import Data.Either (Either(..), isLeft)
import Data.Filterable (partitionMap)
import Data.Foldable (any, foldl)
import Data.Identity (Identity)
import Data.List (List(..), dropWhile, nub, (:))
import Data.List.NonEmpty (NonEmptyList(..), cons, toList)
import Data.Map (lookup)
import Data.Maybe (Maybe(..), maybe)
import Data.NonEmpty ((:|))
import Data.String (codePointFromChar)
import Data.String.CodeUnits as SCU
import Data.Tuple (uncurry)
import Data.Traversable (foldr)
import Literal (Literal(..))
import Parse.Number (float, integer)
import Parse.Parser (Parser, align, block, braces, brackets, close, commas, context, delim, fields, parens, reserved, reservedOperator, stringLiteral, trailingCommas, variable, whitespace)
import Parsing (ParseError(..), Position(..), consume, fail, runParserT)
import Parsing.Combinators (choice, lookAhead, many, many1, notFollowedBy, option, optionMaybe, sepBy1, try, (<?>))
import Parsing.Expr (Operator(..)) as P
import Parsing.Expr (OperatorTable, buildExprParser)
import Parsing.Indent (runIndent, sameOrIndented, withPos)
import Parsing.String (char, eof, satisfy)
import Parsing.String.Basic (skipSpaces)
import Operator (Operator(..), assoc, binopSymbol, comparisons, levels, unopSymbol)
import Expr (Binop(..), Pattern(..))
import SExpr (Branch, Clause(..), Expr(..), Import(..), LambdaClause(..), Module(..), Param(..), ParagraphElem(..), Qualifier(..), Stmt(..), TypeDef(..), TypeExpr(..), VarDef(..), VarDefs)
import Types (Primitive(..), TypeCtr(..), primitiveName, primitives, typeCtrs) as T
import Util (MayFail, type (+), type (×), nonEmpty, singleton, (×))

pattern :: Parser Pattern
pattern = defer \_ -> do
   p <- simplePattern
   optionMaybe (reserved "as" *> variable) <#> maybe p (PAs p)

-- Pattern, or tuple pattern without parentheses
patterns :: Parser Pattern
patterns = do
   p <- pattern
   option p (delim ',' *> (PTuple <<< (p : _) <$> trailingCommas pattern))

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
      uncurry (PConstr q) <$> positionalThenKeyword args
      where
      constrArg :: Parser (Pattern + Bind Pattern)
      constrArg = defer \_ -> (Right <$> try kwArg) <|> (Left <$> pattern)

      kwArg :: Parser (Bind Pattern)
      kwArg = defer \_ -> do
         x <- variable
         delim '='
         p <- pattern
         pure (x ↦ p)

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

-- Split arguments into positional and keyword, rejecting positional after keyword
positionalThenKeyword :: forall a b. List (a + b) -> Parser (List a × List b)
positionalThenKeyword args
   | any isLeft (dropWhile isLeft args) = fail "positional argument follows keyword argument"
   | otherwise = pure (left × right)
        where
        { left, right } = partitionMap identity args

typeExpr :: Parser TypeExpr
typeExpr = defer \_ -> do
   ψ <- typeAtom
   ψs <- many (reservedOperator "|" *> typeAtom)
   pure (foldl UnionTy ψ ψs)
   where
   typeAtom :: Parser TypeExpr
   typeAtom = defer \_ -> (reserved "None" $> PrimitiveTy T.None) <|> (qualifiedName >>= namedType)

   namedType :: Name -> Parser TypeExpr
   namedType (NonEmptyList (x :| Nil))
      | Just π <- lookup x T.primitives = pure (PrimitiveTy π)
      | Just c <- lookup x T.typeCtrs = ctrApp c
   namedType q = NameTy q <$> typeArgs

   ctrApp :: T.TypeCtr -> Parser TypeExpr
   ctrApp T.ListCtr = ListTy <$> brackets typeExpr
   ctrApp T.DictCtr = brackets (reserved (T.primitiveName T.Str) *> delim ',' *> (DictTy <$> typeExpr))
   ctrApp T.TupleCtr = TupleTy <$> brackets ((delim '(' *> delim ')' $> Nil) <|> commas typeExpr)
   ctrApp T.CallableCtr = brackets (CallableTy <$> brackets (commas typeExpr) <* delim ',' <*> typeExpr)
   ctrApp T.TypeTyCtr = TypeTy <$> brackets typeExpr
   ctrApp T.LiteralCtr = brackets literal >>= case _ of
      Float _ -> fail "float in literal type prohibited"
      ℓ -> pure (LitTy ℓ)

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
      p <- patterns
      ψ <- optionMaybe (delim ':' *> typeExpr)
      reservedOperator "="
      pure (p × ψ)
   e <- sameOrIndented *> exprs
   pure $ VarDef p ψ e

varDefs :: Parser VarDefs
varDefs = many1 varDef

stmt :: Parser Stmt
stmt = defer \_ -> ifStmt <|> matchStmt <|> defStmt <|> declareStmt <|> returnStmt <|> (reserved "pass" *> pure Pass) <|> assertStmt <|> misplacedImport <|> (exprs <#> ExprStmt)

declareStmt :: Parser Stmt
declareStmt = do
   x <- try (variable <* delim ':')
   Declare x <$> typeExpr

returnStmt :: Parser Stmt
returnStmt = reserved "return" *> (Return <$> optionMaybe (sameOrIndented *> exprs))

assertStmt :: Parser Stmt
assertStmt = do
   reserved "assert"
   e <- expr
   msg <- optionMaybe (delim ',' *> expr)
   pure $ Assert e msg

topStmt :: Parser Stmt
topStmt = defer \_ -> typeRegion <|> stmt

stmts :: Parser Stmt
stmts = defer \_ -> many1 (align stmt) <#> foldr1Seq

-- Top-level programs may omit 'return' on the trailing expression that gives
-- the program its value. Inside functions and other block bodies, 'return'
-- is required.
programStmt :: Parser Stmt
programStmt = defer \_ -> ifStmt <|> matchStmt <|> typeRegion <|> defStmt <|> declareStmt <|> returnStmt <|> (reserved "pass" *> pure Pass) <|> assertStmt <|> misplacedImport <|> (Return <<< Just <$> exprs)

programStmts :: Parser Stmt
programStmts = defer \_ -> many1 (align programStmt) <#> foldr1Seq

foldr1Seq :: NonEmptyList Stmt -> Stmt
foldr1Seq (NonEmptyList (s :| ss)) = case ss of
   Nil -> s
   s' : rest -> Seq s (foldr1Seq (NonEmptyList (s' :| rest)))

defStmt :: Parser Stmt
defStmt = defer \_ -> (DefRegion <$> defs) <|> (Def <$> varDef)

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
         p <- patterns
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

typeRegion :: Parser Stmt
typeRegion = TypeRegion <$> many1 (typeStmt <|> classDef)

classDef :: Parser TypeDef
classDef = do
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

typeStmt :: Parser TypeDef
typeStmt = do
   x × αs <- try (reserved "type" *> ((×) <$> variable <*> typeParams) <* reservedOperator "=")
   TypeAlias x αs <$> typeExpr

defs :: Parser (NonEmptyList Branch)
defs = many1 defClause
   where
   defClause :: Parser Branch
   defClause = do
      f × αs <- try (reserved "def" *> ((×) <$> variable <*> typeParams) <* delim '(')
      ps <- commas param
      delim ')'
      ψ <- (reservedOperator "->" *> typeExpr) <|> fail "Expected return type annotation"
      s <- blockBody
      pure $ f × Clause (αs × ps × ψ × s)

   param :: Parser Param
   param = Param <$> pattern <*> ((delim ':' *> typeExpr) <|> fail "Expected parameter type annotation")

-- Expression, or tuple without parentheses
exprs :: Parser Expr
exprs = withPos do
   e <- expr
   option e (delim ',' *> (Tuple <<< (e : _) <$> trailingCommas (sameOrIndented *> expr)))

expr :: Parser Expr
expr = context "expr" $ cond <?> "expression"
   where
   cond :: Parser Expr
   cond = defer \_ -> do
      e1 <- opTree
      option e1 do
         sameOrIndented *> reserved "if"
         e <- opTree
         reserved "else"
         e2 <- expr
         pure $ Cond e1 e e2

   opTree :: Parser Expr
   opTree = context "opTree" (buildExprParser opTable simpleChain <* unchained) <* consume -- otherwise always `consume: false`
      where

      unchained :: Parser Unit
      unchained =
         (choice (symbol <$> comparisons) *> fail "chained comparison prohibited")
            <|> ((reserved "and" <|> reserved "or") *> fail "chained boolean operator prohibited")
            <|> pure unit

      symbol :: Binop -> Parser Unit
      symbol In = reserved "in"
      symbol NotIn = try (reserved "not" *> reserved "in")
      symbol BitOr = try (reservedOperator "|" <* notFollowedBy (delim ']')) -- not closing matrix
      symbol b = reservedOperator (binopSymbol b)

      opTable :: OperatorTable (StateT Position Identity) String Expr
      opTable = reverse levels <#> map toOperator -- tightest first
         where
         toOperator :: Operator -> P.Operator (StateT Position Identity) String Expr
         toOperator op@(Binary b) = P.Infix (symbol b $> \e e' -> BinOp e b e') (assoc op)
         toOperator (Unary u) = P.Prefix (word (unopSymbol u) $> UnOp u)
         toOperator op@AndOp = P.Infix (reserved "and" $> And) (assoc op)
         toOperator op@OrOp = P.Infix (reserved "or" $> Or) (assoc op)

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
               positionalThenKeyword args >>= uncurry (Call e ψs) >>> chain
               where
               arg :: Parser (Expr + Bind Expr)
               arg = defer \_ -> (Right <$> try kwArg) <|> (Left <$> cond)

               kwArg :: Parser (Bind Expr)
               kwArg = defer \_ -> do
                  x <- variable
                  delim '='
                  v <- cond
                  pure (x ↦ v)

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

         -- Text between the unquotes keeps its spacing, each run of whitespace as a single space
         paragraph :: Parser Expr
         paragraph = do
            delim "f\"\"\""
            es <- many paragraphElem
            skipSpaces
            delim "\"\"\""
            pure $ Paragraph es
            where
            paragraphElem :: Parser ParagraphElem
            paragraphElem = paragraphToken <|> unquote
               where
               paragraphToken :: Parser ParagraphElem
               paragraphToken = Token <<< SCU.fromCharArray <$> some (paragraphLetter <|> spaces)
                  where
                  -- TODO: allow escaped `"` and `{`
                  paragraphLetter :: Parser Char
                  paragraphLetter = satisfy \c -> c /= '"' && c /= '{' && not (space c)

                  -- Whitespace before the closing quotes isn't text
                  spaces :: Parser Char
                  spaces = ' ' <$ try (some (satisfy space) <* notFollowedBy (delim "\"\"\""))

                  space :: Char -> Boolean
                  space = isSpace <<< codePointFromChar

               unquote :: Parser ParagraphElem
               unquote = defer \_ -> Unquote <$> (delim '{' *> opTree <* char '}')

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
   s <- (many1 (align topStmt) <#> foldr1Seq) <|> pure Pass
   pure $ Module ιs s

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
      "ParseError on line " <> show line <> ", column " <> show column <> ": " <> msg

parseProgram :: String -> MayFail (Stmt × List Import)
parseProgram src = parse (topLevel programBody) src
   where
   programBody = do
      ιs <- many (align import_)
      s <- programStmts
      pure (s × ιs)

parseModule :: String -> MayFail (Module × List Name)
parseModule src = parse (topLevel module_) src <#> \m -> m × moduleImports m
