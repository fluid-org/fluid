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
import DataType (Ctr)
import Dict (Dict)
import Expr (Pattern(..))
import Expr as E
import Lattice (class BotOf, class MeetSemilattice, class Neg, botOf, symmetricDiff)
import Literal (Literal(..))
import Pretty.Doc (Doc, empty, expr, indent, inlOrMul, line, render, stmt, stmtOrExpr, text, (<++>), (<+>), (</>))
import Pretty.Util (assignment, block, braces, brackets, hsep, matrix, number, pair, parens, record, sep', string, vsep)
import Operator (Operator(..), binopSymbol, prec, unopSymbol)
import SExpr (Branch, Case, Clause(..), Expr(..), Import(..), LambdaClause(..), Param(..), ParagraphElem(..), Qualifier(..), RecDefs, Stmt(..), VarDef(..), VarDefs)
import Type as T
import Util (type (×), isEmpty, (×))
import Util.Map (toUnfoldable)
import Util.Pair (Pair(..))
import Val (BaseVal(..), Fun(..)) as V
import Val (class Highlightable, BaseVal, DictRep(..), Env(..), ForeignOp(..), Fun, MatrixRep(..), Val(..), ValWithDoc(..), EnvWithDocs(..), highlightIf)

class Pretty p where
   pretty :: p -> Doc

newtype PrettyShow a = PrettyShow a

derive instance Newtype (PrettyShow a) _

instance Pretty a => Show (PrettyShow a) where
   show (PrettyShow x) = pretty x # render

instance Pretty String where
   pretty = text

class RootOp (e :: Type) where
   rootOp :: e -> Maybe Operator

instance RootOp Pattern where
   rootOp _ = Nothing

instance RootOp Expr where
   rootOp (BinOp _ op _) = Just (Binary op)
   rootOp (UnOp op _) = Just (Unary op)
   rootOp (And _ _) = Just AndOp
   rootOp (Or _ _) = Just OrOp
   rootOp (InfixApp _ _ _) = Just InfixOp
   rootOp _ = Nothing

instance RootOp E.Expr where
   rootOp _ = Nothing

instance Highlightable a => RootOp (Val a) where
   rootOp (Val _ u) = rootOp u

instance Highlightable a => RootOp (BaseVal a) where
   rootOp _ = Nothing

class IsSimple (e :: Type) where
   isSimple :: e -> Boolean

instance IsSimple Expr where
   isSimple (BinOp _ _ _) = false
   isSimple (UnOp _ _) = false
   isSimple (And _ _) = false
   isSimple (Or _ _) = false
   isSimple (InfixApp _ _ _) = false
   isSimple (Lambda _) = false
   isSimple (Cond _ _ _) = false
   isSimple _ = true

instance IsSimple E.Expr where
   isSimple (E.Lambda _) = false
   isSimple _ = true

instance Highlightable a => IsSimple (Val a) where
   isSimple (Val _ u) = isSimple u

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

operatorApp :: Int -> Expr -> Doc
operatorApp n (BinOp s op s') = infixApp n (Binary op) s (text (binopSymbol op)) s'
operatorApp n (And s s') = infixApp n AndOp s (text "and") s'
operatorApp n (Or s s') = infixApp n OrOp s (text "or") s'
operatorApp n (InfixApp s f s') = infixApp n InfixOp s (text "|" <> text f <> text "|") s'
operatorApp n (UnOp op s) =
   if n' <= n then parens (text (unopSymbol op) <+> operatorApp n' s)
   else text (unopSymbol op) <+> operatorApp n' s
   where
   n' = prec (Unary op)
operatorApp _ e = prettySimple e

-- Conditional or lambda in a qualifier needs parentheses
prettyQualifierExpr :: Expr -> Doc
prettyQualifierExpr s@(Cond _ _ _) = parens (pretty s)
prettyQualifierExpr s@(Lambda _) = parens (pretty s)
prettyQualifierExpr s = pretty s

infixApp :: Int -> Operator -> Expr -> Doc -> Expr -> Doc
infixApp n op s sym s' =
   if n' <= n then parens (operatorApp n' s <+> sym <+> operatorApp n' s')
   else operatorApp n' s <+> sym <+> operatorApp n' s'
   where
   n' = prec op

instance Pretty Expr where
   pretty (Var x) = text x
   pretty (Lit ℓ) = pretty ℓ
   pretty (Call e es xes) =
      expr $ prettySimple e <> parens (commas ((pretty <$> es) <> ((\(x ↦ e') -> text x <> text "=" <> pretty e') <$> xes)))
   pretty (Dictionary Nil) = text "{}"
   pretty (Dictionary es) = expr $ record $ map pretty es
   pretty (Matrix e (x × y) e') =
      expr $ matrix (pretty e <+> text "for" <+> pair text x y <+> text "in" <+> pretty e')
   pretty (Lambda c) = pretty c
   pretty (Attribute s x) = expr $ prettySimple s <> text "." <> text x
   pretty (Subscript e (Tuple ks)) = expr $ prettySimple e <> brackets (expr $ prettyList ks)
   pretty (Subscript e k) = expr $ prettySimple e <> brackets (expr $ pretty k)
   pretty e@(BinOp _ _ _) = expr $ operatorApp 0 e
   pretty e@(UnOp _ _) = expr $ operatorApp 0 e
   pretty e@(And _ _) = expr $ operatorApp 0 e
   pretty e@(Or _ _) = expr $ operatorApp 0 e
   pretty e@(InfixApp _ _ _) = expr $ operatorApp 0 e
   pretty (Cond e1 e e2) =
      expr $ pretty e1 <+> text "if" <+> pretty e <+> text "else" <+> pretty e2

   pretty (List Nil) = text "[]"
   pretty (List es) =
      text "[" <> inlOrMul (commas ds) (indent (line <> vcommas ds) <> line) <> text "]"
      where
      ds = pretty <$> es
   pretty (Tuple es) = tuple (pretty <$> es)

   pretty (ListComp s qs) = brackets (expr (pretty s) <+> pretty qs)
   pretty (DictComp k s qs) = braces (pretty k <> text ":" <+> expr (pretty s) <+> pretty qs)
   pretty (Paragraph p) = pretty p
   pretty (DocExpr p e) = text "@doc" <> parens (pretty p) </> pretty e

instance Pretty (List Qualifier) where
   pretty (Cons (Decl (VarDef v _ s)) Nil) =
      text "def" <+> pretty v <> text ":" <+> pretty s
   pretty (Cons (Guard s) Nil) = text "if" <+> prettyQualifierExpr s
   pretty (Cons (Generator p s) Nil) = text "for" <+> pretty p <+> text "in" <+> prettyQualifierExpr s
   pretty (Cons q qs) = pretty (singleton q) <+> pretty qs
   pretty Nil = empty

instance Pretty (NonEmptyList Case) where
   pretty cs = vsep (toList (pretty <$> cs))

instance Pretty Case where
   pretty (p × b) = text "case" <+> (pretty p) <> block (pretty b)

instance Pretty Pattern where
   pretty (PLit ℓ) = pretty ℓ
   pretty (PVar x) = text x
   pretty PWild = text "_"
   pretty (PRecord xps) = record $ map pretty xps
   pretty (PConstr c ps Nil) = prettyConstr (dottedName c) ps
   pretty (PConstr c ps xps) =
      text (dottedName c) <> parens (commas ((pretty <$> ps) <> ((\(x ↦ p) -> text x <> text "=" <> pretty p) <$> xps)))
   pretty (PList ps) = brackets (prettyList ps)
   pretty (PTuple ps) = tuple (pretty <$> ps)
   pretty (PAs p x) = pretty p <+> text "as" <+> text x

instance Pretty (String × Pattern) where
   pretty (k × v) = string k <> text ":" <+> pretty v

instance Pretty VarDef where
   pretty (VarDef v ψ s) = pretty v <> annot ψ <+> assignment (pretty s)

instance Pretty VarDefs where
   pretty ds = sep' (stmtOrExpr line (text " ")) (toList (pretty <$> ds))

instance Pretty Import where
   pretty (Import q Nothing) = text "import" <+> text (dottedName q)
   pretty (Import q (Just xs)) =
      text "from" <+> text (dottedName q) <+> text "import" <+> text (intercalate ", " xs)

instance Pretty Stmt where
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

instance Pretty c => Pretty (T.TypeExpr c) where
   pretty (T.Primitive ν) = pretty ν
   pretty (T.List ψ) = text "list" <> brackets (pretty ψ)
   pretty (T.Tuple ψs) = text "tuple" <> brackets (prettyList ψs)
   pretty (T.Dict ψ) = text "dict" <> brackets (text "str," <+> pretty ψ)
   pretty (T.Callable ψs ψ) = text "Callable" <> brackets (brackets (prettyList ψs) <> text "," <+> pretty ψ)
   pretty (T.Lit ℓ) = text "Literal" <> brackets (pretty ℓ)
   pretty (T.ClassName c) = pretty c
   pretty (T.Union ψ ψ') = pretty ψ <+> text "|" <+> pretty ψ'

instance Pretty T.Class where
   pretty (T.Class q) = text "~" <> text (dottedName q)

instance Pretty (NonEmptyList String) where
   pretty = text <<< dottedName

instance Pretty T.Primitive where
   pretty = text <<< T.primitiveName

instance Pretty Literal where
   pretty (Int n) = number n
   pretty (Float n) = number n
   pretty (Str s) = string s
   pretty (Bool true) = text "True"
   pretty (Bool false) = text "False"
   pretty None = text "None"

instance Pretty Clause where
   pretty (Clause (ps × ψ × s)) = parens (prettyList ps) <> returnAnnot ψ <> block (pretty s)

instance Pretty Param where
   pretty (Param p ψ) = pretty p <> annot ψ

annot :: forall c. Pretty c => Maybe (T.TypeExpr c) -> Doc
annot = maybe mempty \ψ -> text ":" <+> pretty ψ

returnAnnot :: forall c. Pretty c => Maybe (T.TypeExpr c) -> Doc
returnAnnot = maybe mempty \ψ -> text " ->" <+> pretty ψ

instance Pretty LambdaClause where
   pretty (LambdaClause (ps × e)) = text "lambda" <+> prettyList ps <> text ":" <+> pretty e

instance Pretty RecDefs where
   pretty bs = sep' (stmtOrExpr line (text " ")) (toList (pretty <$> bs))

instance Pretty Branch where
   pretty (f × clause) = text "def" <+> text f <> pretty clause

instance Pretty (Expr × Expr) where
   pretty (k × v) =
      pretty k <> stmt
         ( inlOrMul
              (text ":" <+> pretty v)
              (text ":" <> indent (line <> pretty v))
         )

instance Pretty (List ParagraphElem) where
   pretty xs = text "f\"\"\"" <> hsep (pretty <$> xs) <> text "\"\"\""

instance Pretty ParagraphElem where
   pretty (Token str) = text str
   pretty (Unquote e) = text "{" <> pretty e <> text "}"

prettyConstr :: forall a. RootOp a => IsSimple a => Pretty a => Ctr -> List a -> Doc
prettyConstr c ps = text c <> parens (prettyList ps)

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

-- Comma after single element distinguishes tuple from parenthesised expression.
tuple :: List Doc -> Doc
tuple (d : Nil) = parens (d <> text ",")
tuple ds = parens (commas ds)

instance Pretty (Pair E.Expr) where
   pretty (Pair k v) = pretty k <> text ":" <+> pretty v

instance Pretty E.Expr where
   pretty (E.Var x) = text x
   pretty (E.Lit ℓ) = pretty ℓ
   pretty (E.Dictionary ees) = record (pretty <$> ees)
   pretty (E.Constr c es) = prettyConstr (last c) es
   pretty (E.List es) = brackets (prettyList es)
   pretty (E.Tuple es) = tuple (pretty <$> es)
   pretty (E.Matrix e1 (i × j) e2) =
      matrix (pretty e1 <+> text "for" <+> pair text i j <+> text "in" <+> pretty e2)
   pretty (E.Lambda o) = text "lambda" <+> pretty o -- really?
   pretty (E.Attribute e x) = pretty e <> text "." <> text x
   pretty (E.Subscript e x) = pretty e <> brackets (pretty x)
   pretty (E.ModMember q x) = text (dottedName q) <> text "." <> text x
   pretty (E.App e es) = pretty e <> parens (prettyList es)
   pretty (E.BinOp e op e') = expr $ pretty e <+> text (binopSymbol op) <+> pretty e'
   pretty (E.UnOp op e) = expr $ text (unopSymbol op) <+> pretty e
   pretty (E.And e e') = expr $ pretty e <+> text "and" <+> pretty e'
   pretty (E.Or e e') = expr $ pretty e <+> text "or" <+> pretty e'
   pretty (E.Cond e1 e e2) = expr $ pretty e1 <+> text "if" <+> pretty e <+> text "else" <+> pretty e2
   pretty (E.ListComp e gs) = brackets (expr (pretty e) <+> hsep (pretty <$> gs))
   pretty (E.DictComp e e' gs) = braces (pretty e <> text ":" <+> expr (pretty e') <+> hsep (pretty <$> gs))
   pretty (E.DocExpr p e) = text "@doc" <> parens (pretty p) <+> pretty e

instance Pretty E.Qualifier where
   pretty (E.Guard e) = text "if" <+> pretty e
   pretty (E.Generator p e) = text "for" <+> pretty p <+> text "in" <+> pretty e
   pretty (E.Decl p e) = text "def" <+> pretty p <> text ":" <+> pretty e

instance Pretty E.Stmt where
   pretty (E.Return e) = text "return" <+> pretty e
   pretty (E.If (NonEmptyList (b :| bs)) s_opt) =
      vsep (prettyBranch "if" b : (prettyBranch "elif" <$> bs))
         <++> maybe mempty (\s -> text "else" <> block (pretty s)) s_opt
      where
      prettyBranch w (E.Branch e s) = text w <+> expr (pretty e) <> block (pretty s)
   pretty (E.Match e bs) = text "match" <+> pretty e <> block (vsep (toList (prettyCase <$> bs)))
      where
      prettyCase (p × s) = text "case" <+> pretty p <> block (pretty s)
   pretty (E.Assign p ψ e) = pretty p <> annot ψ <+> text "=" <+> pretty e
   pretty (E.DefRec (E.RecDefs ds)) = text "def" <+> pretty ds
   pretty E.Pass = text "pass"
   pretty (E.ExprStmt e) = pretty e
   pretty (E.Assert e Nothing) = text "assert" <+> pretty e
   pretty (E.Assert e (Just e')) = text "assert" <+> pretty e <> text "," <+> pretty e'
   pretty (E.Seq s1 s2) = pretty s1 <++> pretty s2

instance Pretty E.Def where
   pretty (E.Def xs ψ s) = parens (prettyList xs) <> returnAnnot ψ <> text "->" <> pretty s

instance Pretty E.Param where
   pretty (E.Param x ψ) = text x <> annot ψ

instance Pretty (Dict E.Def) where
   pretty ds = go (toUnfoldable ds)
      where
      go :: List (Var × E.Def) -> Doc
      go Nil = empty
      go (xd : Nil) = pretty xd
      go (xd : xds) = (go xds <+> text ";") <+> (pretty xd)

instance Highlightable a => Pretty (Env a) where
   pretty (Env ρ) = prettyEnv ρ

instance Highlightable a => Pretty (EnvWithDocs a) where
   pretty (EnvWithDocs ρ) = prettyEnv ρ

prettyEnv :: forall v. Pretty v => Dict v -> Doc
prettyEnv ρ = brackets $ go (toUnfoldable ρ)
   where
   go :: List (Var × v) -> Doc
   go Nil = empty
   go ((x × v) : rest) =
      (text x <+> text "->" <+> pretty v <+> text ",") <++> go rest

instance Pretty (Bind E.Def) where
   pretty (x ↦ d) = pretty x <> pretty ":" <+> pretty d

instance Highlightable a => Pretty (Val a) where
   pretty (Val a u) = highlightIf a (pretty u)

instance Highlightable a => Pretty (ValWithDoc a) where
   pretty (ValWithDoc { val: v, doc: Nothing }) = pretty v
   pretty (ValWithDoc { val: v, doc: Just d }) = text "@doc" <> parens (pretty d) <+> pretty v

instance Highlightable a => Pretty (Var × (a × Val a)) where
   pretty (k × (a × v)) = highlightIf a (string k) <> text ":" <+> pretty v

instance Highlightable a => Pretty (BaseVal a) where
   pretty (V.Lit ℓ) = pretty ℓ
   pretty (V.Dictionary (DictRep svs))
      | isEmpty svs = text "{}"
      | otherwise = record (pretty <$> (toUnfoldable svs))
   pretty (V.Constr c vs) = prettyConstr (last c) vs
   pretty (V.List vs) = brackets (prettyList vs)
   pretty (V.Tuple vs) = tuple (pretty <$> fromFoldable vs)
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
