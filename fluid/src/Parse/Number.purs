module Parse.Number where

import Prelude hiding (between, when)

import Control.MonadPlus ((<|>))
import Data.Array as Array
import Data.CodePoint.Unicode (hexDigitToInt)
import Data.Foldable (foldl, foldr)
import Data.Int (toNumber)
import Data.Maybe (Maybe(..), fromMaybe, maybe)
import Data.Number (pow)
import Data.String.CodePoints (codePointFromChar)
import Parse.Parser (lexeme)
import Parsing (fail)
import Parsing.Combinators (option, optionMaybe, try, (<?>), (<??>))
import Parsing.Indent (IndentParser)
import Parsing.String (char)
import Parsing.String.Basic (oneOf)
import Parsing.String.Basic as Basic

type Parser a = IndentParser String a

float :: Parser Number
float = lexeme floating <?> "float"

imaginary :: Parser Number
imaginary = lexeme ((try floating <|> (sign <*> (toNumber <$> decimal))) <* oneOf [ 'j', 'J' ]) <?> "imaginary"

integer :: Parser Int
integer = lexeme int <?> "integer"

natural :: Parser Int
natural = lexeme nat <?> "natural"

floating :: Parser Number
floating = do
   f <- fromMaybe identity <$> optionMaybe sign
   x <- decimal >>= fractExponent
   pure $ f x

fractExponent :: Int -> Parser Number
fractExponent n = fractExponent' <|> justExponent
   where
   fractExponent' :: Parser Number
   fractExponent' = do
      fract <- fraction
      expo <- option 1.0 exponent'
      pure $ (toNumber n + fract) * expo

   justExponent :: Parser Number
   justExponent = do
      expo <- exponent'
      pure $ (toNumber n * expo)

fraction :: Parser Number
fraction = "fraction" <??> do
   _ <- char '.'
   digits <- Array.some Basic.digit <?> "fraction"
   maybe (fail "not digit") pure $ foldr op (Just 0.0) digits
   where
   op :: Char -> Maybe Number -> Maybe Number
   op _ Nothing = Nothing
   op d (Just f) = do
      int' <- hexDigitToInt $ codePointFromChar d
      pure $ (f + toNumber int') / 10.0

exponent' :: Parser Number
exponent' = "exponent" <??> do
   _ <- oneOf [ 'e', 'E' ]
   f <- sign
   e <- decimal <?> "exponent"
   pure $ power (f e)
   where
   power :: Int -> Number
   power e
      | e < 0 = 1.0 / power (-e)
      | otherwise = 10.0 `pow` toNumber e

int :: Parser Int
int = do
   f <- lexeme sign
   n <- nat
   pure $ f n

sign :: forall a. (Ring a) => Parser (a -> a)
sign = (char '-' $> negate)
   <|> (char '+' $> identity)
   <|> pure identity

nat :: Parser Int
nat = zeroNumber <|> decimal

zeroNumber :: Parser Int
zeroNumber =
   char '0'
      *> (hexadecimal <|> octal <|> decimal <|> pure 0)
      <?> ""

decimal :: Parser Int
decimal = number 10 Basic.digit

hexadecimal :: Parser Int
hexadecimal = oneOf [ 'x', 'X' ] *> number 16 Basic.hexDigit

octal :: Parser Int
octal = oneOf [ 'o', 'O' ] *> number 8 Basic.octDigit

number :: Int -> Parser Char -> Parser Int
number base baseDigit = do
   digits <- Array.some baseDigit
   maybe (fail "not digits") pure $ foldl folder (Just 0) digits
   where
   folder :: Maybe Int -> Char -> Maybe Int
   folder Nothing _ = Nothing
   folder (Just x) d = ((base * x) + _) <$> hexDigitToInt (codePointFromChar d)
