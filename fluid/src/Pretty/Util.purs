module Pretty.Util where

import Prelude

import Data.List (List(..), (:))
import Pretty.Doc (Doc, indent, inlOrMul, line, stmtOrExpr, text, (<++>), (<+>), (</>))

block :: Doc -> Doc
block d = stmtOrExpr
   (text ":" <> inlOrMul (text " " <> d) (indent (line <> d)))
   (text ":" <+> d <> text ";")

assignment :: Doc -> Doc
assignment d = stmtOrExpr
   (text "=" <> inlOrMul (text " " <> d) (indent (line <> d)))
   (text "=" <+> d <> text ";")

record :: List Doc -> Doc
record ds = inlOrMul
   (text "{" <> sep' (text ", ") ds <> text "}")
   (text "{" <> indent (line <> sep' (text "," <> line) ds) <++> text "}")

enclose :: Doc -> Doc -> Doc -> Doc
enclose l r d = l <> d <> r

parens :: Doc -> Doc
parens = enclose (text "(") (text ")")

braces :: Doc -> Doc
braces = enclose (text "{") (text "}")

brackets :: Doc -> Doc
brackets = enclose (text "[") (text "]")

matrix :: Doc -> Doc
matrix p = text "[|" </> p <> text "|]"

pair :: forall a. (a -> Doc) -> a -> a -> Doc
pair f x y = parens (f x <> text "," <+> f y)

quotes :: Doc -> Doc
quotes = enclose (text "\"") (text "\"")

string :: String -> Doc
string s = quotes (text s)

number :: forall a. Show a => a -> Doc
number s = text (show s)

sep' :: Doc -> List Doc -> Doc
sep' _ Nil = mempty
sep' _ (d : Nil) = d
sep' s (d : ds) = d <> s <> sep' s ds

sep :: List Doc -> Doc
sep Nil = mempty
sep (d : Nil) = d
sep (d : ds) = d <> sep ds

vsep :: List Doc -> Doc
vsep Nil = mempty
vsep (d : Nil) = d
vsep (d : ds) = d <++> vsep ds

hsep :: List Doc -> Doc
hsep Nil = mempty
hsep (d : Nil) = d
hsep (d : ds) = d <+> hsep ds
