module Pretty (PrettyShow(..), class Pretty, compare, pretty, prettyP) where

import Prelude

import Bind (Bind, Var, dottedName, (↦))
import Data.Foldable (intercalate)
import Data.List (List(..), fromFoldable, singleton, (:))
import Data.List.NonEmpty (NonEmptyList(..), last, toList)
import Data.Maybe (Maybe(..), maybe)
import Data.Newtype (class Newtype)
import Data.NonEmpty ((:|))
import Data.Traversable (class Foldable)
import DataType (Ctr, cCons)
import Dict (Dict)
import Expr (Pattern(..))
import Expr as E
import Lattice (class BotOf, class MeetSemilattice, class Neg, botOf, symmetricDiff)
import Expr.Literal as L
import Pretty.Doc (Doc, empty, expr, indent, inlOrMul, line, render, stmt, stmtOrExpr, text, (<++>), (<+>), (</>))
import Pretty.Util (assignment, block, brackets, hsep, matrix, number, pair, parens, record, sep', string, vsep)
import Primitive.Parse (getPrec)
import SExpr (Branch, Case, Clause(..), DictEntry(..), Expr(..), Import(..), LambdaClause(..), ListRest(..), ParagraphElem(..), Qualifier(..), RecDefs, Stmt(..), VarDef(..), VarDefs)
import TypeExpr as T
import Util (type (×), error, isEmpty, (×))
import Util.Map (toUnfoldable)
import Util.Pair (Pair(..))
import Val (BaseVal(..), Fun(..)) as V
import Val (class Ann, class Highlightable, BaseVal, DictRep(..), Env(..), EnvStmt(..), ForeignOp(..), Fun, MatrixRep(..), Val(..), highlightIf)

class Pretty p where
   pretty :: p -> Doc

newtype PrettyShow a = PrettyShow a

derive instance Newtype (PrettyShow a) _

instance Pretty a => Show (PrettyShow a) where
   show (PrettyShow x) = pretty x # render

instance Pretty String where
   pretty = text

class RootOp (e :: Type) where
   rootOp :: e -> Maybe String

instance RootOp Pattern where
   rootOp (PConstr c _ _) | last c == last cCons = Just ":"
   rootOp _ = Nothing

instance Ann a => RootOp (Expr a) where
   rootOp (Constr _ c _ _) | last c == last cCons = Just ":"
   rootOp (BinaryApp _ op _) = Just op
   rootOp (UnaryPrefixApp op _) = Just op
   rootOp _ = Nothing

instance Highlightable a => RootOp (E.Expr a) where
   rootOp (E.Constr _ c _) | c == cCons = Just ":"
   rootOp _ = Nothing

instance Highlightable a => RootOp (Val a) where
   rootOp (Val _ Nothing u) = rootOp u
   rootOp (Val _ (Just _) _) = Nothing

instance Highlightable a => RootOp (BaseVal a) where
   rootOp (V.Constr c _) | c == cCons = Just ":"
   rootOp _ = Nothing

class IsSimple (e :: Type) where
   isSimple :: e -> Boolean

instance Ann a => IsSimple (Expr a) where
   isSimple (BinaryApp _ _ _) = false
   isSimple (UnaryPrefixApp _ _) = false
   isSimple (Constr _ c _ _) | last c == last cCons = false
   isSimple (Lambda _) = false
   isSimple (Cond _ _ _) = false
   isSimple _ = true

instance Highlightable a => IsSimple (E.Expr a) where
   isSimple (E.Constr _ c _) | c == cCons = false
   isSimple (E.Lambda _ _) = false
   isSimple _ = true

instance Highlightable a => IsSimple (Val a) where
   isSimple (Val _ Nothing u) = isSimple u
   isSimple (Val _ (Just _) _) = false

instance Highlightable a => IsSimple (BaseVal a) where
   isSimple _ = true

instance IsSimple Pattern where
   isSimple _ = true

prettySimple :: forall a. IsSimple a => Pretty a => a -> Doc
prettySimple s =
   if isSimple s then pretty s
   else parens (pretty s)

prettyP :: forall a. Pretty a => a -> String
prettyP x = render (pretty x)

operatorApp :: forall a. Ann a => Int -> Expr a -> Doc
operatorApp n (BinaryApp s op s') =
   case getPrec op of
      -1 -> operatorApp customPrec s <+> text "|" <> text op <> text "|" <+> operatorApp customPrec s'
         where
         customPrec = getPrec "|x|"
      n' ->
         if n' <= n then
            parens (operatorApp n' s <+> text op <+> operatorApp n' s')
         else
            operatorApp n' s <+> text op <+> operatorApp n' s'
operatorApp n (UnaryPrefixApp op s) =
   case getPrec op of
      -1 -> error "not implemented!"
      n' ->
         if n' <= n then
            parens (text op <+> operatorApp n' s)
         else
            text op <+> operatorApp n' s
operatorApp _ e = prettySimple e

lambda :: forall a. Ann a => List Pattern -> Stmt a -> Doc
lambda ps s = text "lambda" <+> prettyList ps <> text ":" <+> pretty s

instance Ann a => Pretty (Expr a) where
   pretty (Var x) = text x
   pretty (Op o) = parens $ text o
   pretty (Int α n) = highlightIf α (number n)
   pretty (Float α n) = highlightIf α (number n)
   pretty (Str α str) = highlightIf α (string str)
   pretty (Constr α c Nil Nil) = highlightIf α (text (dottedName c))
   pretty (Constr α c as Nil) = highlightIf α (expr $ prettyConstr (dottedName c) as)
   pretty (Constr α c es xes) =
      highlightIf α (text (dottedName c) <> parens (commas ((pretty <$> es) <> ((\(x ↦ e) -> text x <> text "=" <> pretty e) <$> xes))))
   pretty (Dictionary α Nil) = highlightIf α (text "{}")
   pretty (Dictionary α es) = highlightIf α (expr $ record $ map pretty es)
   pretty (Matrix α e (x × y) e') =
      highlightIf α (expr $ matrix (pretty e <+> text "for" <+> pair text x y <+> text "in" <+> pretty e'))
   pretty (Lambda c) = pretty c
   pretty (Attribute s x) = expr $ prettySimple s <> text "." <> text x
   pretty (ModMember q x) = expr $ text (dottedName q) <> text "." <> text x
   pretty (Subscript e k) = expr $ prettySimple e <> brackets (expr $ pretty k)
   pretty (App s ss) = expr $ prettySimple s <> parens (prettyList ss)
   pretty (BinaryApp s op s') = expr $ operatorApp 0 (BinaryApp s op s')
   pretty (UnaryPrefixApp op s) = expr $ operatorApp 0 (UnaryPrefixApp op s)
   pretty (Cond e1 e e2) =
      expr $ pretty e1 <+> text "if" <+> pretty e <+> text "else" <+> pretty e2

   pretty (ListEmpty α) = highlightIf α (text "[]")
   pretty (ListNonEmpty α e rest) =
      highlightIf α (text "[")
         <> inlOrMul
            (pretty e <> collect rest true)
            (indent (line <> pretty e) <> collect rest false)
      where
      collect :: ListRest a -> Boolean -> Doc
      collect (Next α' e' rest') inline = highlightIf α' (text ",") <> (if inline then text " " <> pretty e' else indent (line <> pretty e')) <> collect rest' inline
      collect (End α') inline = if inline then highlightIf α' (text "]") else line <> highlightIf α' (text "]")

   pretty (ListEnum s s') = brackets $ expr (pretty s <+> text ".." <+> pretty s')
   pretty (ListComp α s qs) = highlightIf α (brackets (expr (pretty s) <+> pretty qs)) -- Qualifier
   pretty (Paragraph p) = pretty p
   pretty (DocExpr p e) = text "@doc" <> parens (pretty p) </> pretty e

instance Ann a => Pretty (List (Qualifier a)) where
   pretty (Cons (ListCompDecl (VarDef v s)) Nil) =
      text "def" <+> pretty v <> text ":" <+> pretty s
   pretty (Cons (ListCompGuard s) Nil) = text "if" <+> pretty s
   pretty (Cons (ListCompGen p s) Nil) = text "for" <+> pretty p <+> text "in" <+> pretty s
   pretty (Cons q qs) = pretty (singleton q) <+> pretty qs
   pretty Nil = empty

instance Ann a => Pretty (NonEmptyList (Case a)) where
   pretty cs = vsep (toList (pretty <$> cs))

instance Ann a => Pretty (Case a) where
   pretty (p × b) = text "case" <+> (pretty p) <> block (pretty b)

instance Pretty Pattern where
   pretty (PInt n) = number n
   pretty (PFloat n) = number n
   pretty (PStr s) = string s
   pretty (PVar x) = text x
   pretty PWild = text "_"
   pretty (PRecord xps) = record $ map pretty xps
   pretty (PConstr c Nil Nil) = text (dottedName c)
   pretty (PConstr c ps Nil) = prettyConstr (dottedName c) ps
   pretty (PConstr c ps xps) =
      text (dottedName c) <> parens (commas ((pretty <$> ps) <> ((\(x ↦ p) -> text x <> text "=" <> pretty p) <$> xps)))
   pretty (PList ps) = brackets (prettyList ps)
   pretty (PAs p x) = pretty p <+> text "as" <+> text x

instance Pretty (String × Pattern) where
   pretty (k × v) = text k <> text ":" <+> pretty v

instance Ann a => Pretty (VarDef a) where
   pretty (VarDef v s) = pretty v <+> assignment (pretty s)

instance Ann a => Pretty (VarDefs a) where
   pretty ds = sep' (stmtOrExpr line (text " ")) (toList (pretty <$> ds))

instance Pretty Import where
   pretty (Import q Nothing) = text "import" <+> text (dottedName q)
   pretty (Import q (Just xs)) =
      text "from" <+> text (dottedName q) <+> text "import" <+> text (intercalate ", " xs)

instance Ann a => Pretty (Stmt a) where
   pretty (Return e) = text "return" <+> pretty e
   pretty (If (NonEmptyList (ss :| sss)) e) =
      vsep (prettyClause "if" ss : (prettyClause "elif" <$> sss))
         <++> maybe mempty (\b -> text "else" <> block (pretty b)) e
      where
      prettyClause w (s × b) = text w <+> expr (pretty s) <> block (pretty b)
   pretty (Match s cs) = text "match" <+> pretty s <> block (pretty cs)
   pretty (Def vd) = pretty vd
   pretty (DefRec xcs) = pretty xcs
   pretty Pass = text "pass"
   pretty (ExprStmt e) = pretty e
   pretty (Assert cond Nothing) = text "assert" <+> pretty cond
   pretty (Assert cond (Just msg)) = text "assert" <+> pretty cond <> text "," <+> pretty msg
   pretty (Seq s1 s2) = pretty s1 <> line <> pretty s2
   pretty (Dataclass c b xs) =
      text "@dataclass" <> line
         <> text "class" <+> text c
         <> maybe mempty (\b' -> text "(" <> text b' <> text ")") b
         <> block body
      where
      body = case xs of
         Nil -> text "pass"
         _ -> vsep ((\(x × ψ) -> text x <> text ":" <+> pretty ψ) <$> xs)

instance Pretty T.TypeExpr where
   pretty (T.Primitive ν) = pretty ν
   pretty (T.List ψ) = text "list" <> brackets (pretty ψ)
   pretty (T.Tuple ψs) = text "tuple" <> brackets (prettyList ψs)
   pretty (T.Dict ψ) = text "dict" <> brackets (text "str," <+> pretty ψ)
   pretty (T.Callable ψs ψ) = text "Callable" <> brackets (brackets (prettyList ψs) <> text "," <+> pretty ψ)
   pretty (T.Literal ℓ) = text "Literal" <> brackets (pretty ℓ)
   pretty (T.ClassName q) = text (dottedName q)
   pretty (T.Union ψ ψ') = pretty ψ <+> text "|" <+> pretty ψ'

instance Pretty T.Primitive where
   pretty T.Object = text "object"
   pretty T.Never = text "Never"
   pretty T.None = text "None"
   pretty T.Bool = text "bool"
   pretty T.Int = text "int"
   pretty T.Float = text "float"
   pretty T.Str = text "str"
   pretty T.Sized = text "Sized"

instance Pretty L.Literal where
   pretty (L.Int n) = number n
   pretty (L.Float n) = number n
   pretty (L.Str s) = string s
   pretty (L.Bool true) = text "True"
   pretty (L.Bool false) = text "False"
   pretty L.None = text "None"

instance Ann a => Pretty (Clause a) where
   pretty (Clause _ (ps × b)) = lambda ps b

instance Ann a => Pretty (LambdaClause a) where
   pretty (LambdaClause (ps × e)) = text "lambda" <+> prettyList ps <> text ":" <+> pretty e

instance Ann a => Pretty (RecDefs a) where
   pretty bs = sep' (stmtOrExpr line (text " ")) (toList (pretty <$> bs))

instance Ann a => Pretty (Branch a) where
   pretty (v × Clause _ (ps × b)) =
      text "def"
         <+> text v
         <> parens (prettyList ps)
         <> block (pretty b)

instance Ann a => Pretty (DictEntry a × Expr a) where
   pretty (k × v) =
      pretty k <> stmt
         ( inlOrMul
              (text ":" <+> pretty v)
              (text ":" <> indent (line <> pretty v))
         )

instance Ann a => Pretty (DictEntry a) where
   pretty (ExprKey k) = brackets (pretty k)
   pretty (VarKey a k) = highlightIf a (text k)

instance Ann a => Pretty (List (ParagraphElem a)) where
   pretty xs = text "f\"\"\"" <> hsep (pretty <$> xs) <> text "\"\"\""

instance Ann a => Pretty (ParagraphElem a) where
   pretty (Token str) = text str
   pretty (Unquote e) = text "{" <> pretty e <> text "}"

prettyConstr :: forall a. RootOp a => IsSimple a => Pretty a => Ctr -> List a -> Doc
prettyConstr "Nil" Nil = text "[]"
prettyConstr "Pair" (x : y : Nil) = pair pretty x y
prettyConstr "Cons" (x : y : Nil) = prettyConsArg x true <+> text ":|" <+> prettyConsArg y false
prettyConstr c Nil = text c
prettyConstr c ps = text c <> parens (prettyList ps)

prettyConsArg :: forall a. RootOp a => IsSimple a => Pretty a => a -> Boolean -> Doc
prettyConsArg e lhs = case rootOp e of
   Nothing -> prettySimple e
   Just op -> if (if lhs then (<=) else (<)) (getPrec op) (getPrec ":") then parens (pretty e) else pretty e

commas :: List Doc -> Doc
commas Nil = empty
commas (d : Nil) = d
commas (d : ds) = d <> text "," <+> commas ds

vcommas :: List Doc -> Doc
vcommas Nil = empty
vcommas (d : Nil) = d
vcommas (d : ds) = d <> text "," <++> vcommas ds

prettyList :: forall f a. Foldable f => Pretty a => f a -> Doc
prettyList xs = commas (pretty <$> fromFoldable xs)

instance Highlightable a => Pretty (Pair (E.Expr a)) where
   pretty (Pair k v) = pretty k <> text ":" <+> pretty v

instance Highlightable a => Pretty (E.Expr a) where
   pretty (E.Var x) = text x
   pretty (E.Op op) = parens (text op)
   pretty (E.Int a n) = highlightIf a (number n)
   pretty (E.Float a n) = highlightIf a (number n)
   pretty (E.Str a str) = highlightIf a (string str)
   pretty (E.Dictionary a ees) = highlightIf a $ record (pretty <$> ees)
   pretty (E.Constr a c es) = highlightIf a (prettyConstr (last c) es)
   pretty (E.Matrix a e1 (i × j) e2) =
      highlightIf a $ matrix (pretty e1 <+> text "for" <+> pair text i j <+> text "in" <+> pretty e2)
   pretty (E.Lambda a o) = highlightIf a (text "lambda") <+> pretty o -- really?
   pretty (E.Attribute e x) = pretty e <> text "." <> text x
   pretty (E.Subscript e x) = pretty e <> brackets (pretty x)
   pretty (E.ModMember q x) = text (dottedName q) <> text "." <> text x
   pretty (E.App e es) = pretty e <> parens (prettyList es)
   pretty (E.Cond e1 e e2) = expr $ pretty e1 <+> text "if" <+> pretty e <+> text "else" <+> pretty e2
   pretty (E.DocExpr p e) = text "@doc" <> parens (pretty p) <+> pretty e

instance Highlightable a => Pretty (E.Stmt a) where
   pretty (E.Return e) = text "return" <+> pretty e
   pretty (E.If (NonEmptyList (b :| bs)) s_opt) =
      vsep (prettyBranch "if" b : (prettyBranch "elif" <$> bs))
         <++> maybe mempty (\s -> text "else" <> block (pretty s)) s_opt
      where
      prettyBranch w (E.Branch e s) = text w <+> expr (pretty e) <> block (pretty s)
   pretty (E.Match e bs) = text "match" <+> pretty e <> block (vsep (toList (prettyCase <$> bs)))
      where
      prettyCase (p × s) = text "case" <+> pretty p <> block (pretty s)
   pretty (E.Assign p e) = pretty p <+> text "=" <+> pretty e
   pretty (E.DefRec (E.RecDefs _ ds)) = text "def" <+> pretty ds
   pretty E.Pass = text "pass"
   pretty (E.ExprStmt e) = pretty e
   pretty (E.Assert e Nothing) = text "assert" <+> pretty e
   pretty (E.Assert e (Just e')) = text "assert" <+> pretty e <> text "," <+> pretty e'
   pretty (E.Seq s1 s2) = pretty s1 <++> pretty s2

instance Highlightable a => Pretty (E.Def a) where
   pretty (E.Def xs s) = parens (commas (text <$> xs)) <> text "->" <> pretty s

instance Highlightable a => Pretty (Dict (E.Def a)) where
   pretty ds = go (toUnfoldable ds)
      where
      go :: List (Var × E.Def a) -> Doc
      go Nil = empty
      go (xd : Nil) = pretty xd
      go (xd : xds) = (go xds <+> text ";") <+> (pretty xd)

instance Highlightable a => Pretty (Env a) where
   pretty (Env ρ) = brackets $ go (toUnfoldable ρ)
      where
      go :: List (Var × Val a) -> Doc
      go Nil = empty
      go ((x × v) : rest) =
         (text x <+> text "->" <+> pretty v <+> text ",") <++> go rest

instance Highlightable a => Pretty (EnvStmt a) where
   pretty (EnvStmt ρ s) = (pretty ρ) <++> (pretty s)

instance Highlightable a => Pretty (Bind (E.Def a)) where
   pretty (x ↦ d) = pretty x <> pretty ":" <+> pretty d

instance Highlightable a => Pretty (Val a) where
   pretty (Val a Nothing u) = highlightIf a (pretty u)
   pretty (Val a (Just v') u) = text "@doc" <> parens (pretty v') <+> highlightIf a (pretty u)

instance Highlightable a => Pretty (Var × (a × Val a)) where
   pretty (k × (a × v)) = highlightIf a (pretty k) <> text ":" <+> pretty v -- ???

instance Highlightable a => Pretty (BaseVal a) where
   pretty (V.Int n) = number n
   pretty (V.Float n) = number n
   pretty (V.Str str) = string str
   pretty (V.Dictionary (DictRep svs))
      | isEmpty svs = text "{}"
      | otherwise = record (pretty <$> (toUnfoldable svs))
   pretty (V.Constr c vs) = prettyConstr (last c) vs
   pretty (V.Matrix (MatrixRep (vss × _ × _))) = vcommas $ fromFoldable (prettyList <$> vss) -- ???
   pretty (V.Fun phi) = pretty phi

instance Highlightable a => Pretty (Fun a) where
   pretty (V.Closure _ _ _) = text "cl"
   pretty (V.Prim phi) = pretty phi
   pretty (V.Type c) = text (last c)
   pretty (V.Partial phi vs) = pretty phi <> parens (prettyList vs)

instance Pretty ForeignOp where
   pretty (ForeignOp (s × _)) = pretty s

compare :: forall a. BotOf a a => Neg a => MeetSemilattice a => Eq a => Pretty a => String -> String -> a -> a -> String × String
compare op1 op2 x y =
   let
      x_minus_y × y_minus_x = symmetricDiff x y
      left = if x_minus_y == botOf x then "" else op1 <> " but not " <> op2 <> ":\n" <> prettyP x_minus_y
      right = if y_minus_x == botOf x then "" else op2 <> " but not " <> op1 <> ":\n" <> prettyP y_minus_x
   in
      left × right
