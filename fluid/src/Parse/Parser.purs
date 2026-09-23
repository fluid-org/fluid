module Parse.Parser where

import Prelude hiding (between)

import Control.Alt ((<|>))
import Control.Monad.Error.Class (catchError, throwError)
import Control.Monad.State.Class (get)
import Control.Monad.State.Trans (put)
import Control.Monad.Trans.Class (lift)
import Data.Array (cons, elem)
import Data.Array as Array
import Data.List.Types (List, NonEmptyList)
import Data.Maybe (Maybe(..))
import Data.String.CodeUnits (take)
import Data.String.CodeUnits as SCU
import Data.Traversable (foldr)
import Parsing (ParseError(..), Position(..), fail, position, region)
import Parsing.Combinators (between, sepBy, sepBy1, sepEndBy, skipMany, try, (<?>))
import Parsing.Combinators.Array (many)
import Parsing.Indent (IndentParser, checkIndent, sameOrIndented, withPos)
import Parsing.String (char, satisfy, string)
import Parsing.String.Basic (alphaNum, letter, lower, upper)
import Parsing.Token (oneOf)
import Util (type (×), (×))

opChars :: Array Char
opChars =
   [ ':'
   , '!'
   , '#'
   , '$'
   , '%'
   , '&'
   , '*'
   , '+'
   , '.'
   , '/'
   , '<'
   , '='
   , '>'
   , '?'
   , '\\'
   , '^'
   , '|'
   , '-'
   , '~'
   ]

type Parser a = IndentParser String a

class Parseable a where
   parse :: a -> Parser a

instance Parseable String where
   parse = string

instance Parseable Char where
   parse = char

keywords :: Array String
keywords = [ "as", "assert", "case", "class", "def", "else", "for", "from", "if", "import", "in", "lambda", "match", "pass", "return" ]

context :: forall a. String -> Parser a -> Parser a
context s p = do
   pos <- position
   region (addContext pos) p
   where
   addContext :: Position -> ParseError -> ParseError
   addContext (Position { line, column }) (ParseError msg pos) =
      ParseError (take 200 (msg <> "\n " <> s <> " on line " <> show line <> ", column " <> show column)) pos

block :: forall a. Parser a -> Parser a
block e = delim ':' *> sameOrIndented *> withPos e

align :: forall a. Parser a -> Parser a
align p = checkIndent *> p

-- Like withPos, but restores the indent reference on failure too.
withPosReset :: forall a. Parser a -> Parser a
withPosReset p = do
   saved <- lift get
   pos <- position
   lift (put pos)
   r <- catchError p \e -> do
      lift (put saved)
      throwError e
   lift (put saved)
   pure r

identifier :: Parser Char -> Parser Char -> Parser String
identifier start letter = lexeme $ do
   c <- start
   cs <- Array.many letter
   pure $ SCU.singleton c <> SCU.fromCharArray cs

unreserved :: Parser String -> Parser String
unreserved p = do
   name <- p
   if name `elem` keywords then fail $ "Reserved identifier: " <> name
   else pure name

variable :: Parser String
variable = unreserved $ identifier (lower <|> char '_') (alphaNum <|> char '_')

constructor :: Parser String
constructor = unreserved $ identifier upper (alphaNum <|> char '_')

reserved :: String -> Parser Unit
reserved expected = try do
   received <- identifier (letter <|> char '_') (alphaNum <|> char '_')
   if expected /= received then fail $ "Expected `" <> expected <> "`, received `" <> received <> "`"
   else pure unit

operator :: Parser String
operator = lexeme $ do
   cs <- Array.some $ oneOf opChars
   pure $ SCU.fromCharArray cs

reservedOperator :: String -> Parser Unit
reservedOperator expected = try do
   received <- operator
   if expected /= received then fail $ "Expected `" <> expected <> "`, received `" <> received <> "`"
   else pure unit

-- shortcut for lexeme throwing away result for primitive parsers
delim :: forall a. Parseable a => a -> Parser Unit
delim a = void $ lexeme $ parse a

-- similar to delim but updates the indentation reference
-- use in combination with withPos - reference should be reset
-- when finished parsing (not handled here)
close :: forall a. Parseable a => a -> Parser Unit
close a = do
   _ <- parse a
   pos <- position
   lift (put pos)
   whitespace

lexeme :: forall a. Parser a -> Parser a
lexeme = (_ <* whitespace)

whitespace :: Parser Unit
whitespace = skipMany (space <|> comment)
   where
   space = void $ oneOf [ ' ', '\t', '\n' ]
   comment = char '#' *> skipMany (satisfy (_ /= '\n'))

braces :: forall a. Parser a -> Parser a
braces = between (delim '{') (delim '}')

brackets :: forall a. Parser a -> Parser a
brackets = between (delim '[') (delim ']')

parens :: forall a. Parser a -> Parser a
parens = between (delim '(') (delim ')')

commas :: forall a. Parser a -> Parser (List a)
commas p = sepBy p (delim ',')

commas1 :: forall a. Parser a -> Parser (NonEmptyList a)
commas1 p = sepBy1 p (delim ',')

trailingCommas :: forall a. Parser a -> Parser (List a)
trailingCommas p = sepEndBy p (delim ',')

fields :: forall k v. Parser k -> Parser v -> Parser (List (k × v))
fields key val = trailingCommas do
   k <- key
   delim ':'
   v <- val
   pure $ k × v

-----------------------------------------------------------
-- String things extracted from "Parsing.Token"
-----------------------------------------------------------
stringLiteral :: Parser String
stringLiteral = lexeme (go <?> "literal string")
   where
   go :: Parser String
   go = do
      maybeChars <- between (char '"') (char '"' <?> "end of string") (many stringChar)
      pure $ SCU.fromCharArray $ foldr folder [] maybeChars

   folder :: Maybe Char -> Array Char -> Array Char
   folder Nothing chars = chars
   folder (Just c) chars = cons c chars

stringChar :: Parser (Maybe Char)
stringChar =
   (Just <$> stringLetter)
      <?> "string character"

stringLetter :: Parser Char
stringLetter = satisfy (\c -> (c /= '"') && (c /= '\\') && (c > '\x1A'))
