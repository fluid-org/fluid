module Eval where

import Prelude hiding (absurd, apply)

import Bind (dottedName, prefixOf, varAnon, varThis)
import Control.Alt ((<|>))
import Control.Apply (lift2)
import Control.Monad.Error.Class (class MonadError)
import Control.Monad.State (class MonadState, runStateT)
import Data.Array as A
import Data.Either (either)
import Data.Foldable (elem, fold, foldM, foldl, sum)
import Data.Functor.Compose (Compose(..))
import Data.Functor.Product (Product(..), product)
import Data.Identity (Identity(..))
import Data.FunctorWithIndex (mapWithIndex)
import Data.List (List(..), drop, elemIndex, length, take, zip, (:))
import Data.List as L
import Data.List.NonEmpty (head, last, snoc, unsnoc)
import Data.List.NonEmpty (fromList, toList) as NEL
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe, maybe)
import Data.Profunctor.Strong (first, second)
import Data.Set (Set)
import Data.Set as Set
import Data.Traversable (for, sequence, traverse)
import Data.Tuple (fst, snd, uncurry)
import Classes (class HasClasses, ClassTable, ancestors, arity, askClasses, checkArity, fieldNames)
import Dict (Dict)
import Dict (fromFoldable) as D
import Effect.Exception (Error)
import Expr (Branch(..), Def(..), Expr(..), Import(..), Module(..), Pattern(..), Qualifier(..), Stmt(..), assigns, fv, statements)
import File (class MonadLoad, withClasses)
import DepGraph (DepGraph, Deriv, VisibleGraph, at, attachDoc, materialise, newVertex)
import Lattice (class DepSemiring, DepKind, Raw, ctrlWeight)
import Literal (Literal(..), eqLiteral)
import Module.Defs (ModuleName, implicit, submods)
import Operator (binopSymbol, unopSymbol)
import Pretty (prettyP)
import Types (Type(..)) as T
import Primitive (binop, binopRel, boolean, concatLists, dropα, int, string, typeMismatch, unop, unopRel, unpack, unpack')
import Util (type (×), Endo, absurd, check, definitely', definitelyRight, error, orElse, orThrow, quoted, singleton, throw, withMsg, (×))
import Util.Map (get, lookup, lookup', mapWithKey, maplet, restrict, unionWith_never, (<+>))
import Util.Pair (Pair(..))
import Util.Set (empty, (∪))
import Val (BaseVal(..), Fun(..), Label(Assigns), dictEntry, value) as V
import Val (class HasModuleStore, class MonadEval, BaseVal, Ctrl, ModuleState(..), loadedEnv, DictRep(..), Env(..), ForeignOp(..), ForeignOp'(..), GVal, Label(Value), MatrixRep(..), Val(..), Weight, binding, closureEnv, constant, construct, constructWith, ctrlPosition, deliver, dictionary, field, forDefs, fun, gval, element, elementCount, lengthDep, matrixElement, modifyModuleStore, moduleStore, partialArg, partialFun, root, toDict, valAt, via, viaAll)

type Inputs s = { ctrl :: Ctrl s, env :: Dict (GVal s) }

newValue :: forall m s. MonadState (DepGraph Label s) m => GVal s -> m (Deriv × Raw Val)
newValue { val: v, inEdges } = newVertex (Value v) (Value <$> inEdges) <#> (_ × v)

-- Allocate vertex with bindings ρ and control position ctrl as label; returned ρ and ctrl depend on the vertex
newAssigns
   :: forall m s
    . MonadState (DepGraph Label s) m
   => Dict (GVal s)
   -> Maybe (Ctrl s)
   -> m (Dict (GVal s) × Maybe (Ctrl s))
newAssigns ρ ctrl = newVertex label inEdges <#> \p ->
   mapWithKey (\x v -> v { inEdges = binding x <$> at p }) ρ × (ctrl $> (ctrlPosition <$> at p))
   where
   label = V.Assigns (void ctrl) (Env (_.val <$> ρ))
   inEdges = lift2 V.Assigns (sequence ctrl) (Env <$> traverse _.inEdges ρ)

-- Inputs after a statement which introduces ρ and ctrl
after :: forall s. Inputs s -> Dict (GVal s) -> Maybe (Ctrl s) -> Inputs s
after inputs ρ ctrl = { env: inputs.env <+> ρ, ctrl: fromMaybe inputs.ctrl ctrl }

-- Returned value, or the bindings and control position introduced
data Result s = Returns (Deriv × Raw Val) | Assigns (Dict (GVal s)) (Maybe (Ctrl s))

asReturns :: forall s. Result s -> Deriv × Raw Val
asReturns (Returns r) = r
asReturns (Assigns _ _) = error "Returns expected"

asAssigns :: forall s. Result s -> Dict (GVal s) × Maybe (Ctrl s)
asAssigns (Assigns ρ ctrl) = ρ × ctrl
asAssigns (Returns _) = error "Assigns expected"

-- Result r of a statement evaluated after ρ and ctrl are introduced
override :: forall s. Dict (GVal s) -> Maybe (Ctrl s) -> Result s -> Result s
override ρ ctrl (Assigns ρ' ctrl') = Assigns (ρ <+> ρ') (ctrl' <|> ctrl)
override _ _ r = r

-- Variables bound if the pattern matches the value, with the dependence of each inspected position.
matches :: forall s. ClassTable -> GVal s -> Pattern -> Maybe (Dict (GVal s)) × List (Ctrl s)
matches _ v (PVar x)
   | x == varAnon = Just empty × Nil
   | otherwise = Just (maplet x v) × Nil
matches _ _ PWild = Just empty × Nil
matches classes v (PAs p x) = first (map (_ `unionWith_never` maplet x v)) (matches classes v p)
matches classes v@{ val: Val _ u } p = second (via root v : _) case u, p of
   V.Lit ℓ', PLit ℓ | eqLiteral ℓ ℓ' -> Just empty × Nil
   V.Obj c' xvs, PConstr c ps Nil
      | c `elem` ancestors classes c' ->
           matchesMany classes
              (mapWithIndex (\i (_ × val) -> { val, inEdges: via (field i) v }) (take (length ps) xvs))
              ps
   V.Dictionary (DictRep xvs), PRecord xps ->
      case traverse (\(x × p') -> lookup x xvs <#> \(_ × val) -> x × { val, inEdges: via (V.dictEntry x >>> snd) v } × p') xps of
         Just kvs -> second ((kvs <#> \(x × _) -> via (V.dictEntry x >>> fst) v) <> _)
            (matchesMany classes (fst <<< snd <$> kvs) (snd <<< snd <$> kvs))
         Nothing -> Nothing × Nil
   V.List vs, PList ps | A.length vs == length ps -> matchesElements vs ps
   V.Tuple vs, PTuple ps | A.length vs == length ps -> matchesElements vs ps
   _, _ -> Nothing × Nil
   where
   matchesElements vs ps = matchesMany classes (mapWithIndex (\i val -> { val, inEdges: via (element i) v }) (L.fromFoldable vs)) ps

matchesMany :: forall s. ClassTable -> List (GVal s) -> List Pattern -> Maybe (Dict (GVal s)) × List (Ctrl s)
matchesMany _ Nil Nil = Just empty × Nil
matchesMany classes (v : vs) (p : ps) = case matches classes v p of
   Nothing × ctrls -> Nothing × ctrls
   Just ρ × ctrls -> case matchesMany classes vs ps of
      Nothing × ctrls' -> Nothing × (ctrls <> ctrls')
      Just ρ' × ctrls' -> Just (ρ `unionWith_never` ρ') × (ctrls <> ctrls')
matchesMany _ _ _ = error absurd

-- Bindings of the first matching case, with the control position introduced if the cases tried inspect any
-- position
dispatch :: forall s b. Semiring s => ClassTable -> List (Pattern × b) -> GVal s -> Maybe (Dict (GVal s) × b) × Maybe (Ctrl s)
dispatch classes cases v = second introduced (go cases)
   where
   go :: List (Pattern × b) -> Maybe (Dict (GVal s) × b) × List (Ctrl s)
   go Nil = Nothing × Nil
   go ((p × b) : cases') = case matches classes v p of
      Just ρ × ctrls -> Just (ρ × b) × ctrls
      Nothing × ctrls -> second (ctrls <> _) (go cases')

   introduced :: List (Ctrl s) -> Maybe (Ctrl s)
   introduced Nil = Nothing
   introduced ctrls = Just (fold ctrls)

-- dispatch on a single pattern, which must match.
destructure :: forall m s. MonadError Error m => Semiring s => ClassTable -> Pattern -> GVal s -> m (Dict (GVal s) × Maybe (Ctrl s))
destructure classes p v = case dispatch classes (singleton (p × unit)) v of
   Just (ρ × _) × ctrl -> pure (ρ × ctrl)
   Nothing × _ -> throw ("Pattern mismatch: " <> prettyP v.val <> " does not match " <> prettyP p)

closure :: forall s. Semiring s => Dict (GVal s) -> Dict Def -> Def -> GVal s
closure ρ ds d = { val: clo (_.val <$> ρ), inEdges: viaAll clo ρ }
   where
   clo :: forall a. Semiring a => Dict (Val a) -> Val a
   clo ρ' = Val zero (V.Fun (V.Closure (Env ρ') ds d))

closeDefs :: forall s. DepSemiring s => Inputs s -> Dict Def -> Dict (GVal s)
closeDefs inputs ds = ds <#> \d ->
   let
      ds' = ds `forDefs` d
   in
      construct inputs.ctrl (closure (restrict (fv ds' ∪ fv d) inputs.env) ds' d)

-- ======================
-- Evaluation
-- ======================

-- Evaluator specialised to its class dictionaries once per use
eval
   :: forall m s
    . MonadEval s m
   => { stmt :: Inputs s -> Stmt -> m (Result s)
      , program :: Inputs s -> Stmt -> m (Deriv × Raw Val)
      }
eval = { stmt, program }
   where
   expr :: Inputs s -> Expr -> m (Deriv × Raw Val)
   expr inputs e'@(DocExpr e _) = do
      r <- value inputs e' >>= newValue
      doc <- expr (inputs { env = inputs.env <+> maplet varThis (gval r) }) e
      attachDoc (fst r) (fst doc) $> r
   expr inputs e = value inputs e >>= newValue

   -- Value of an expression in terms of inputs and the vertices of the premises
   value :: Inputs s -> Expr -> m (GVal s)
   value inputs = case _ of
      Var x -> pure (deliver inputs.ctrl (get x inputs.env))
      Lit ℓ -> pure (construct inputs.ctrl (constant (Val unit (V.Lit ℓ))))
      Dictionary ees -> dictionary inputs.ctrl <$> for ees \(Pair e e') -> dictEntry inputs e e'
      DictComp e e' gs -> qualifiers entry inputs gs <#> \v -> { val: toDict v.val, inEdges: via toDict v }
         where
         entry inputs' = dictEntry inputs' e e' <#> \(_ × k × v) -> singletonList inputs' (tuple k v)
      List es -> constructWith inputs.ctrl (A.fromFoldable >>> V.List) <$> traverse (expr inputs >>> map gval) es
      Tuple es -> constructWith inputs.ctrl (A.fromFoldable >>> V.Tuple) <$> traverse (expr inputs >>> map gval) es
      ListComp e gs -> qualifiers (\inputs' -> expr inputs' e <#> (gval >>> singletonList inputs')) inputs gs
      Constr c es -> do
         classes <- askClasses
         checkArity c (length es) classes
         constructWith inputs.ctrl (V.Obj c <<< zip (fieldNames classes c)) <$>
            traverse (expr inputs >>> map gval) es
      Matrix e (x × y) e' -> do
         dims <- gval <$> expr inputs e'
         i' × j' <- case dims.val of
            Val _ (V.Tuple [ Val _ (V.Lit (Int i')), Val _ (V.Lit (Int j')) ]) -> pure (i' × j')
            Val _ u -> throw (typeMismatch u "pair of int")
         check
            (i' × j' >= 1 × 1)
            ("array must be at least (" <> show (1 × 1) <> "); got (" <> show (i' × j') <> ")")
         vss <- for (A.range 0 (i' - 1)) \i -> for (A.range 0 (j' - 1)) \j -> do
            let ρ' = maplet x (index dims 0 i) `unionWith_never` maplet y (index dims 1 j)
            gval <$> expr (inputs { env = inputs.env <+> ρ' }) e
         pure (constructWith inputs.ctrl mat (product (Compose vss) (Identity dims)))
         where
         index :: GVal s -> Int -> Int -> GVal s
         index dims k n =
            { val: Val unit (V.Lit (Int n))
            , inEdges: via (\p -> Val (ctrlWeight * root (element k p)) (V.Lit (Int n))) dims
            }

         mat :: forall a. Product (Compose Array Array) Identity (Val a) -> BaseVal a
         mat (Product (Compose vss × Identity p)) = V.Matrix (MatrixRep (vss × element 0 p × element 1 p))
      Lambda d -> pure (construct inputs.ctrl (closure (restrict (fv d) inputs.env) empty d))
      Type τ -> pure (construct inputs.ctrl (constant (Val unit (V.Fun (V.Type τ)))))
      Attribute e x -> do
         v <- gval <$> expr inputs e
         case v.val of
            Val _ (V.Obj c xvs) -> do
               i <- elemIndex x (fst <$> xvs) # orElse (quoted (dottedName c) <> " has no field " <> quoted x)
               pure (deliver (inputs.ctrl <> via root v) { val: field i v.val, inEdges: via (field i) v })
            _ -> throw $ "Found " <> prettyP v.val <> ", expected object"
      Subscript e e' -> do
         v@{ val: Val _ u } <- gval <$> expr inputs e
         v'@{ val: Val _ u' } <- gval <$> expr inputs e'
         case u, u' of
            V.Dictionary (DictRep d), V.Lit (Str s) -> do
               _ <- withMsg "Dict lookup" $ lookup s d # orElse ("Key \"" <> s <> "\" not found")
               subscript v v' (V.dictEntry s >>> snd) (via root v <> via (V.dictEntry s >>> fst) v)
            V.Dictionary _, _ -> throw $ "Found " <> prettyP v'.val <> ", expected str"
            _, V.Lit (Int i) | Just n <- elementCount v.val -> do
               let i' = if i < 0 then n + i else i
               unless (0 <= i' && i' < n) $ throw ("Index " <> show i <> " out of range")
               subscript v v' (element i') (via root v)
            V.List _, _ -> throw $ "Found " <> prettyP v'.val <> ", expected int"
            V.Tuple _, _ -> throw $ "Found " <> prettyP v'.val <> ", expected int"
            V.Lit (Str _), _ -> throw $ "Found " <> prettyP v'.val <> ", expected int"
            V.Matrix (MatrixRep (_ × m × n)), V.Tuple [ Val _ (V.Lit (Int i)), Val _ (V.Lit (Int j)) ] -> do
               unless (0 <= i && i < dropα (unpack' int m) && 0 <= j && j < dropα (unpack' int n)) $ throw ("Index (" <> show i <> ", " <> show j <> ") out of range")
               subscript v v' (matrixElement i j) (via root v)
            V.Matrix _, _ -> throw $ "Found " <> prettyP v'.val <> ", expected pair of int"
            _, _ -> throw $ "Found " <> prettyP v.val <> ", expected list, tuple, str, dict or matrix"
         where
         subscript :: GVal s -> GVal s -> (forall a. Endo (Val a)) -> Ctrl s -> m (GVal s)
         subscript v v' proj ctrl =
            pure (deliver (inputs.ctrl <> ctrl <> via sum v') { val: proj v.val, inEdges: via proj v })
      ModMember q x -> do
         { modules } <- moduleStore
         deliver inputs.ctrl <$> withMsg "Module member" (lookup' x (definitely' (loadedEnv (get q modules))))
      App e es -> do
         f <- gval <$> expr inputs e
         vs <- traverse (expr inputs >>> map gval) es
         withMsg ("In " <> funName e) $ apply inputs.ctrl f vs
      BinOp e op e' -> do
         v <- gval <$> expr inputs e
         v' <- gval <$> expr inputs e'
         u <- withMsg ("In " <> binopSymbol op) $ orThrow (binop op v.val v'.val) <#> fst
         pure $ deliver inputs.ctrl
            { val: Val unit u, inEdges: lift2 (\x y -> definitelyRight (binopRel op x y)) v.inEdges v'.inEdges }
      UnOp op e -> do
         v <- gval <$> expr inputs e
         u <- withMsg ("In " <> unopSymbol op) $ orThrow (unop op v.val) <#> fst
         pure (deliver inputs.ctrl { val: Val unit u, inEdges: via (unopRel op >>> definitelyRight) v })
      And e e' -> do
         { holds, ctrl, value: v } <- condition inputs e
         if holds then gval <$> expr (inputs { ctrl = ctrl }) e' else pure v
      Or e e' -> do
         { holds, ctrl, value: v } <- condition inputs e
         if holds then pure v else gval <$> expr (inputs { ctrl = ctrl }) e'
      Cond e1 e e2 -> do
         { holds, ctrl } <- condition inputs e
         gval <$> expr (inputs { ctrl = ctrl }) (if holds then e1 else e2)
      DocExpr _ e -> gval <$> expr inputs e

   dictEntry :: Inputs s -> Expr -> Expr -> m (String × GVal s × GVal s)
   dictEntry inputs' e e' = do
      k <- expr inputs' e
      s <- orThrow (unpack string (snd k)) <#> fst
      u <- expr inputs' e'
      pure (s × gval k × gval u)

   funName :: Expr -> String
   funName (Var x) = quoted x
   funName (App e _) = funName e
   funName _ = "unknown"

   -- Evaluate e as a Boolean, taking the root of the resulting value as control input for later evaluation
   condition :: Inputs s -> Expr -> m { holds :: Boolean, ctrl :: Ctrl s, value :: GVal s }
   condition inputs e = do
      v <- gval <$> expr inputs e
      holds × _ <- orThrow (unpack boolean v.val)
      pure { holds, ctrl: via root v, value: v }

   singletonList :: Inputs s -> GVal s -> GVal s
   singletonList inputs v = constructWith inputs.ctrl (A.fromFoldable >>> V.List) (v : Nil)

   tuple :: GVal s -> GVal s -> GVal s
   tuple k v = constructWith mempty (A.fromFoldable >>> V.Tuple) (k : v : Nil)

   -- Evaluate qualifiers and then body to list of elements; body gives one-element list
   qualifiers :: (Inputs s -> m (GVal s)) -> Inputs s -> List Qualifier -> m (GVal s)
   qualifiers body inputs gs = gval <$> (elements gs >>= newValue)
      where
      -- List of elements in terms of the vertices of the premises
      elements :: List Qualifier -> m (GVal s)
      elements Nil = body inputs
      elements (Guard e : gs') = do
         { holds, ctrl } <- condition inputs e
         if holds then qualifiers body (inputs { ctrl = ctrl }) gs'
         else pure (construct ctrl (constant (Val unit (V.List []))))
      elements (Generator p e : gs') = do
         v <- gval <$> expr inputs e
         n <- case elementCount v.val of
            Just n -> pure n
            Nothing -> throw ("Found " <> prettyP v.val <> ", expected list, tuple, str or dict")
         classes <- askClasses
         vs × ctrl <- fold <$> for (L.take n (L.range 0 n)) \i -> do
            let u = { val: element i v.val, inEdges: via (element i) v }
            case dispatch classes (singleton (p × unit)) u of
               Nothing × ctrl -> pure (Nil × fold ctrl)
               Just (ρ' × _) × ctrl ->
                  qualifiers body (inputs { env = inputs.env <+> ρ', ctrl = via lengthDep v <> fold ctrl }) gs'
                     <#> \v' -> singleton v' × mempty
         pure (construct (via lengthDep v <> ctrl) { val: concatLists (_.val <$> vs), inEdges: viaAll concatLists vs })
      elements (Decl p e : gs') = do
         v <- gval <$> expr inputs e
         classes <- askClasses
         ρ' × ctrl <- destructure classes p v
         qualifiers body (after inputs ρ' ctrl) gs'

   stmt :: Inputs s -> Stmt -> m (Result s)
   stmt inputs s = result inputs s >>= case _ of
      Returns r -> Returns <$> newValue (gval r)
      Assigns ρ ctrl -> uncurry Assigns <$> newAssigns ρ ctrl

   -- Result of a statement in terms of inputs and the vertices of the premises
   result :: Inputs s -> Stmt -> m (Result s)
   result inputs = case _ of
      Return e -> Returns <$> expr inputs e
      If bs s_opt -> go (NEL.toList bs) inputs.ctrl
         where
         go Nil ctrl = maybe (pure (Assigns empty (Just ctrl))) (branch ctrl) s_opt
         go (Branch e s' : bs') ctrl = do
            { holds, ctrl: ctrl' } <- condition (inputs { ctrl = ctrl }) e
            if holds then branch ctrl' s' else go bs' ctrl'

         branch ctrl s' = override empty (Just ctrl) <$> stmt (inputs { ctrl = ctrl }) s'
      Match e bs -> do
         v <- gval <$> expr inputs e
         classes <- askClasses
         case dispatch classes (NEL.toList bs) v of
            Nothing × ctrl -> pure (Assigns empty ctrl)
            Just (ρ' × s') × ctrl -> override ρ' ctrl <$> stmt (after inputs ρ' ctrl) s'
      Declare _ -> pure (Assigns empty Nothing)
      Assign p e -> do
         v <- gval <$> expr inputs e
         classes <- askClasses
         uncurry Assigns <$> destructure classes p v
      DefRegion ds -> pure (Assigns (closeDefs inputs ds) Nothing)
      Pass -> pure (Assigns empty Nothing)
      ExprStmt e -> expr inputs e $> Assigns empty Nothing
      Assert e e_opt -> do
         { holds, ctrl } <- condition inputs e
         if holds then pure (Assigns empty (Just ctrl))
         else case e_opt of
            Nothing -> throw "AssertionError"
            Just e' -> do
               _ × Val _ u <- expr (inputs { ctrl = ctrl }) e'
               throw ("AssertionError: " <> either (\_ -> prettyP u) identity (string.unpack u))
      Dataclass c -> do
         let v = construct inputs.ctrl (constant (Val unit (V.Fun (V.Type (T.ClassTy c Nil)))))
         pure (Assigns (maplet (last c) v) Nothing)
      TypeAlias x αs τ -> do
         let v = construct inputs.ctrl (constant (Val unit (V.TypeAlias αs τ)))
         pure (Assigns (maplet x v) Nothing)
      s@(Seq _ _) -> block inputs empty Nothing (NEL.toList (statements s))

   -- Result of statements in sequence under a single rule; ρ and ctrl are introduced by earlier statements
   block :: Inputs s -> Dict (GVal s) -> Maybe (Ctrl s) -> List Stmt -> m (Result s)
   block _ ρ ctrl Nil = pure (Assigns ρ ctrl)
   block inputs ρ ctrl (s : ss) = stmt inputs s >>= case _ of
      Returns r -> pure (Returns r)
      Assigns ρ' ctrl' -> block (after inputs ρ' ctrl') (ρ <+> ρ') (ctrl' <|> ctrl) ss

   -- Evaluate top-level program at a new vertex; return vertex of final expression as output
   program :: Inputs s -> Stmt -> m (Deriv × Raw Val)
   program inputs s = output (unsnoc (statements s)) >>= \r -> newValue (gval r) $> r
      where
      output { init, last: ExprStmt e } =
         asAssigns <$> block inputs empty Nothing init >>= uncurry newAssigns >>= \(ρ × ctrl) ->
            expr (after inputs ρ ctrl) e
      output _ = error absurd

   -- Apply f to vs at a new vertex
   application :: Ctrl s -> GVal s -> List (GVal s) -> m (GVal s)
   application ctrl f vs = gval <$> (apply ctrl f vs >>= newValue)

   -- Apply f to vs, partially if vs is shorter than the arity of f; apply the result to any arguments beyond
   -- the arity
   apply :: Ctrl s -> GVal s -> List (GVal s) -> m (GVal s)
   apply ctrl f@{ val: Val _ u } vs = case u of
      V.Fun (V.Partial φ us) ->
         apply ctrl { val: Val unit (V.Fun φ), inEdges: via partialFun f }
            (mapWithIndex (\i val -> { val, inEdges: via (partialArg i) f }) us <> vs)
      V.Fun φ -> do
         n <- arity'
         let k = length vs
         if k < n then pure (construct ctrl (partial unit))
         else if k == n then call φ vs
         else application ctrl f (take n vs) >>= \v -> apply ctrl v (drop n vs)
         where
         arity' :: m Int
         arity' = case φ of
            V.Closure _ _ (Def xs _) -> pure (length xs)
            V.Prim (ForeignOp (_ × ForeignOp' φ')) -> pure φ'.arity
            V.Type (T.ClassTy c _) -> askClasses >>= arity c
            V.Type τ -> throw ("Not callable: " <> prettyP τ)
            V.Partial _ _ -> error absurd

         -- Partial application, with root and function part dependent on the function value, and stored
         -- arguments dependent on the argument values
         partial :: Unit -> GVal s
         partial _ =
            { val: Val unit (V.Fun (V.Partial φ (_.val <$> vs)))
            , inEdges: lift2 (\x us -> Val (root x) (V.Fun (V.Partial (fun x) us))) f.inEdges (traverse _.inEdges vs)
            }
      _ -> throw $ "Found " <> prettyP f.val <> ", expected function"
      where
      -- Apply φ to vs', taking the root of the function value as control input
      call :: V.Fun Unit -> List (GVal s) -> m (GVal s)
      call φ vs' = case φ of
         V.Closure (Env ρ1) ds (Def xs s) -> do
            let
               ρ1' = mapWithKey (\y val -> { val, inEdges: via (closureEnv >>> get y) f }) ρ1
               ρ2 = closeDefs { ctrl: ctrl', env: ρ1' } ds
               ρ3 = foldl (\ρ (x × v) -> if x == varAnon then ρ else ρ `unionWith_never` maplet x v) empty (zip xs vs')
            gval <<< asReturns <$> stmt { ctrl: ctrl', env: ρ1' <+> ρ2 <+> ρ3 } s
         V.Prim (ForeignOp (_ × ForeignOp' { depOp })) -> depOp (application ctrl') ctrl' vs'
         V.Type (T.ClassTy c _) ->
            askClasses <#> \classes -> constructWith ctrl' (V.Obj c <<< zip (fieldNames classes c)) vs'
         V.Type _ -> error absurd
         V.Partial _ _ -> error absurd
         where
         ctrl' = via root f

-- Evaluate module q at a new vertex; bindings of body override module value of each submodule
evalModule
   :: forall m s
    . MonadEval s m
   => Dict (GVal s)
   -> ModuleName
   -> Module
   -> m (Dict (GVal s))
evalModule ρ0 q (Module ιs s) = do
   ρ <- foldM (evalImport q) ρ0 ιs
   { modules } <- moduleStore
   ρ' × _ <- asAssigns <$> eval.stmt { ctrl: mempty, env: ρ } s
   fst <$> newAssigns (subMods modules <+> unbound <+> ρ') Nothing
   where
   subMods modules = moduleVal <$> D.fromFoldable (submods (Map.keys modules) q)
   unbound = D.fromFoldable (L.fromFoldable (assigns s) <#> (_ × constant (Val unit V.Unbound)))

-- Bind imported members, and names of imported modules to module values.
evalImport
   :: forall m s
    . MonadEval s m
   => ModuleName
   -> Dict (GVal s)
   -> Import
   -> m (Dict (GVal s))
evalImport enclosing ρ = case _ of
   Import q Nothing -> do
      _ <- load q
      loadAncestors Nothing q
      pure (ρ <+> maplet (head q) (moduleVal (pure (head q))))
   Import q (Just xs) -> do
      ρ_q <- load q
      loadAncestors (Just enclosing) q
      importsFrom q ρ_q ρ xs
   where
   loadAncestors bound q = case NEL.fromList (unsnoc q).init of
      Nothing -> pure unit
      Just q'
         | maybe false (q' `prefixOf` _) bound -> pure unit
         | otherwise -> void (load q') *> loadAncestors bound q'

   importsFrom q ρ_q = foldM step
      where
      step ρ' x = do
         { modules } <- moduleStore
         when (Map.member (snoc q x) modules) (void (load (snoc q x)))
         pure (ρ' <+> maplet x (get x ρ_q))

moduleVal :: forall s. Semiring s => ModuleName -> GVal s
moduleVal q = constant (Val unit (V.Module q))

-- Members of the implicit modules loaded so far.
implicitMembers :: forall m s. HasModuleStore s m => m (Dict (GVal s))
implicitMembers = moduleStore <#> \{ modules } ->
   foldl (\ρ q -> ρ <+> fromMaybe empty (Map.lookup q modules >>= loadedEnv)) empty implicit

load
   :: forall m s
    . MonadEval s m
   => ModuleName
   -> m (Dict (GVal s))
load q = do
   { modules } <- moduleStore
   case Map.lookup q modules of
      Just (Loaded ρ_q) -> pure ρ_q
      Just (Parsed body) -> do
         ρ0 <- implicitMembers
         evalModule ρ0 q body >>= loaded
      Nothing -> loaded empty
   where
   loaded ρ_q = modifyModuleStore (\s -> s { modules = Map.insert q (Loaded ρ_q) s.modules }) $> ρ_q

type Eval =
   { g :: DepGraph Label Weight
   , out :: Deriv
   }

visible :: Eval -> Set Deriv
visible { g, out } = Map.keys g.docs ∪ Set.fromFoldable (Map.values g.docs) ∪ singleton out

-- Graph of the visible vertices, which are labelled by values
visibleGraph :: Eval -> VisibleGraph Val DepKind
visibleGraph r = graph { vals = V.value <$> graph.vals }
   where
   graph = materialise r.g (visible r)

-- Vertices documented with the name x.
documentedAs :: forall s. DepGraph Label s -> String -> Array Deriv
documentedAs g x = A.fromFoldable (Map.keys (Map.filter (\d -> valAt g d == Val unit (V.Lit (Str x))) g.docs))

evalProgram
   :: forall m
    . HasClasses m
   => HasModuleStore Weight m
   => MonadLoad m
   => Dict (GVal Weight) -- top-level environment
   -> ClassTable
   -> Stmt
   -> m Eval
evalProgram inputs classes s =
   withClasses classes do
      { depGraph } <- moduleStore
      out × g <- flip runStateT depGraph (fst <$> eval.program { ctrl: mempty, env: inputs } s)
      pure { g, out }
