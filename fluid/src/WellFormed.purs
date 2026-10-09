module WellFormed where

import Prelude hiding (absurd)

import Bind (Bind, Name, Var, dottedName, prefixOf, properPrefixOf, varThis, (↦))
import Control.Monad.Error.Class (throwError)
import Control.Monad.Reader (ReaderT, ask, mapReaderT, runReaderT)
import Control.Monad.State (StateT, get, mapStateT, modify_, runStateT)
import Control.Monad.Trans.Class (lift)
import Data.Bifunctor (lmap)
import Data.Either (Either, hush)
import Control.MonadPlus (guard)
import Data.Foldable (all, and, elem, find, foldM, foldl, foldr, for_, intercalate)
import Data.Function (on)
import Data.FoldableWithIndex (forWithIndex_)
import Data.FunctorWithIndex (mapWithIndex)
import Data.TraversableWithIndex (forWithIndex)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe, maybe)
import Data.List (List(..), drop, length, mapMaybe, nub, null, sort, transpose, zipWith, (:))
import Data.Foldable (lookup) as F
import ModuleGraph (ModuleName, implicitFor, submodules)
import Data.List.NonEmpty (NonEmptyList(..), snoc, unsnoc)
import Data.NonEmpty ((:|))
import Data.List.NonEmpty as NEL
import Data.Semigroup.Foldable (foldl1)
import Data.Set (Set, unions)
import Data.Set as Set
import Data.Traversable (for, traverse)
import Data.Tuple (fst, snd)
import DataType (cParagraph, cRange)
import DefiniteAssignment (ClassEntry, VarCxt, Entry(..), Cxt, WfResult(..), ancestors, classFor, classOf, extendCxt, extendCxtWith, fieldMap, fields, mergeRes, overrideRes, resolveName)
import Dict as D
import Util.Map (constMap)
import Expr (bv, fv)
import Expr (Pattern(..)) as S
import Expr (Branch(..), Def(..), Expr(..), Import(..), Module(..), Qualifier(..), RecDefs(..), Stmt(..)) as E
import Literal (Literal(..))
import SExpr (Clause(..), Expr(..), Import(..), LambdaClause(..), Module(..), Param(..), ParagraphElem(..), Qualifier(..), Stmt(..), TypeExpr(..), VarDef(..), assigns) as S
import Types as T
import Util (MayFail, type (×), absurd, checkDistinct, definitely', error, nonEmpty, singleton, (×), (∩))
import Util.Pair (Pair(..))
import Util.Set ((\\), (∪))

-- Predefined modules and program (under __main__) have no body
type CheckedModule = { cxt :: Cxt, mod :: Maybe E.Module }

-- Modules checked so far, over parsed modules.
type CheckM = StateT (Map.Map ModuleName CheckedModule) (ReaderT (Map.Map ModuleName S.Module) (Either String))

runCheckM :: forall a. CheckM a -> Map.Map ModuleName S.Module -> Map.Map ModuleName Cxt -> MayFail (a × Map.Map ModuleName CheckedModule)
runCheckM m mods predefined = runReaderT (runStateT m (predefined <#> \cxt -> { cxt, mod: Nothing })) mods

checkProgram :: List S.Import -> S.Stmt -> CheckM E.Stmt
checkProgram imports s = do
   _ × cxt_imp <- checkImports mainModule imports
   -- Unlike a module (checkStatements), the program may return: a top-level return yields
   -- its result value. The spec forbids this, treating __main__ as a module; Fluid does not.
   decls × _ × s' <- lift (lift (wellFormedTop mainModule (Map.insert "__name__" (VarStatus true) cxt_imp) s))
   modify_ (Map.insert mainModule { cxt: decls, mod: Nothing })
   pure s'

-- Member context of module q, checked on demand as its import is checked; memoised. The recursion has no
-- cycle guard; it terminates because the dependency graph is acyclic.
checkModule :: ModuleName -> CheckM Cxt
checkModule q = get >>= \checked -> case Map.lookup q checked of
   Just { cxt } -> pure cxt
   Nothing -> mapStateT (mapReaderT (lmap (_ <> "\nChecking module " <> dottedName q))) do
      mods <- lift ask
      mod@(S.Module is _) <- maybe (throwError ("Module not parsed: " <> dottedName q)) pure (Map.lookup q mods)
      importCxt × cxt_imp <- checkImports q is
      δ × mod' <- lift (lift (checkStatements q cxt_imp mod))
      let subs = Mod <$> Map.fromFoldable (submodules (Map.keys mods) q)
      let clash = (Map.keys importCxt ∪ Map.keys δ) ∩ Map.keys subs
      when (not Set.isEmpty clash)
         $ throwError
         $ "Submodule name clash in module " <> dottedName q <> ": " <> intercalate ", " (Set.toUnfoldable clash :: List Var)
      let cxt = subs `Map.union` δ
      modify_ (Map.insert q { cxt, mod: Just mod' })
      pure cxt

checkImports :: ModuleName -> List S.Import -> CheckM (Cxt × Cxt)
checkImports enclosing is = do
   implicitCxt <- foldM (\acc q -> (acc `Map.union` _) <$> checkModule q) Map.empty (implicitFor enclosing)
   importCxt <- foldM (\acc i -> (acc `extendCxtWith` _) <$> importBindings enclosing i) Map.empty is
   pure (importCxt × (implicitCxt `extendCxtWith` importCxt))

-- Bindings contributed by one import of the enclosing module.
importBindings :: ModuleName -> S.Import -> CheckM Cxt
importBindings enclosing (S.Import q Nothing) = do
   when (enclosing `properPrefixOf` q)
      $ throwError
      $ "Module " <> dottedName enclosing <> " cannot import its own descendant " <> dottedName q
   θ <- ModChecked q <$> checkModule q
   Map.singleton (NEL.head q) <$> checksTo Nothing q θ
importBindings enclosing (S.Import q (Just xs)) = do
   cxt <- checkModule q
   _ <- checksTo (Just enclosing) q (ModChecked q cxt) -- checks q's ancestors; contributes no bindings
   importedMembers q cxt xs

-- Wrap the reference for module q in checked references for its proper
-- prefixes, checking each; prefixes of the bound (the enclosing module,
-- for a from-import) are exempt.
checksTo :: Maybe ModuleName -> ModuleName -> Entry -> CheckM Entry
checksTo bound q θ = case NEL.fromList init of
   Nothing -> pure θ
   Just q'
      | maybe false (q' `prefixOf` _) bound -> pure θ
      | otherwise -> do
           cxt <- checkModule q'
           checksTo bound q' (ModChecked q' (cxt `extendCxtWith` Map.singleton x θ))
   where
   { init, last: x } = unsnoc q

-- Bindings for names imported from module q with member context cxt.
importedMembers :: ModuleName -> Cxt -> List Var -> CheckM Cxt
importedMembers _ _ Nil = pure Map.empty
importedMembers q cxt (x : xs) = do
   othersCxt <- importedMembers q cxt xs
   case Map.lookup x cxt of
      Just (Mod q') -> checkModule q' <#> \cxt' -> Map.insert x (ModChecked q' cxt') othersCxt
      Just (VarStatus false) -> throwError $ "Not definitely assigned: " <> x
      Just θ -> pure (Map.insert x θ othersCxt)
      Nothing -> throwError $ "Cannot import name " <> x <> " from module " <> dottedName q

checkStatements :: Name -> Cxt -> S.Module -> MayFail (Cxt × E.Module)
checkStatements q cxt_imp (S.Module imports ss) =
   case foldr (\s acc -> Just (maybe s (S.Seq s) acc)) Nothing ss of
      Nothing -> pure (Map.singleton "__name__" (VarStatus true) × E.Module imports' Nil)
      Just s -> do
         decls × r × s' <- wellFormedTop q (Map.insert "__name__" (VarStatus true) cxt_imp) s
         case r of
            Returns -> throwError "Module body cannot return"
            Assigns δ ->
               pure (Map.insert "__name__" (VarStatus true) (Map.union decls (VarStatus <$> δ)) × E.Module imports' (unSeq s'))
   where
   imports' = imports <#> \(S.Import q' xs) -> E.Import q' xs
   unSeq (E.Seq s1 s2) = s1 : unSeq s2
   unSeq s = s : Nil

mainModule :: Name
mainModule = pure "__main__"

typeDecls :: S.Stmt -> Set Var
typeDecls (S.Dataclass c _ _ _) = Set.singleton c
typeDecls (S.TypeAlias x _ _) = Set.singleton x
typeDecls (S.Seq s1 s2) = typeDecls s1 ∪ typeDecls s2
typeDecls _ = Set.empty

-- Variables of enclosing scopes read within closures.
class Captures a where
   captures :: a -> Set Var

instance Captures S.Stmt where
   captures S.Pass = Set.empty
   captures (S.Def (S.VarDef _ _ e)) = captures e
   captures (S.ExprStmt e) = captures e
   captures (S.Assert e e') = captures e ∪ maybe Set.empty captures e'
   captures (S.Return e) = captures e
   captures (S.If es s) =
      unions ((\(e × s') -> captures e ∪ captures s') <$> es) ∪ maybe Set.empty captures s
   captures (S.Match e ps) =
      captures e ∪ unions ((\(_ × s) -> captures s) <$> ps)
   captures (S.DefRec ds) = unions ((fv <<< snd) <$> ds) \\ unions (Set.singleton <<< fst <$> ds)
   captures (S.Seq s1 s2) = captures s1 ∪ captures s2
   captures (S.Dataclass _ _ _ _) = Set.empty
   captures (S.TypeAlias _ _ _) = Set.empty

instance Captures S.Expr where
   captures (S.Var _) = Set.empty
   captures (S.Lit _) = Set.empty
   captures (S.Call e _ es xes) = captures e ∪ unions (captures <$> es) ∪ unions ((captures <<< snd) <$> xes)
   captures (S.Dictionary es) =
      unions ((\(k × v) -> captures k ∪ captures v) <$> es)
   captures (S.Matrix e (x × y) e') =
      (captures e \\ (Set.singleton x ∪ Set.singleton y)) ∪ captures e'
   captures (S.Lambda (S.LambdaClause (ps × e))) =
      fv e \\ unions (bv <$> ps)
   captures (S.Attribute e _) = captures e
   captures (S.Subscript e e') = captures e ∪ captures e'
   captures (S.BinOp e _ e') = captures e ∪ captures e'
   captures (S.UnOp _ e) = captures e
   captures (S.And e e') = captures e ∪ captures e'
   captures (S.Or e e') = captures e ∪ captures e'
   captures (S.InfixApp e _ e') = captures e ∪ captures e'
   captures (S.Cond e1 e e2) = captures e1 ∪ captures e ∪ captures e2
   captures (S.Paragraph es) = unions (capturesPe <$> es)
      where
      capturesPe (S.Token _) = Set.empty
      capturesPe (S.Unquote e) = captures e
   captures (S.List es) = unions (captures <$> es)
   captures (S.Tuple es) = unions (captures <$> es)
   captures (S.ListComp e gs) = captures gs ∪ (captures e \\ bv gs)
   captures (S.DictComp k e gs) = captures gs ∪ ((captures k ∪ captures e) \\ bv gs)
   captures (S.DocExpr e e') = (captures e \\ Set.singleton varThis) ∪ captures e'

instance Captures (List S.Qualifier) where
   captures Nil = Set.empty
   captures (S.Guard e : gs) = captures e ∪ captures gs
   captures (S.Generator p e : gs) = captures e ∪ (captures gs \\ bv p)
   captures (S.Decl (S.VarDef p _ e) : gs) = captures e ∪ (captures gs \\ bv p)

-- Translation into core, with the variables assigned or a return.
class WellFormed a b | a -> b where
   wellFormed :: Cxt -> a -> MayFail b

instance WellFormed S.Stmt (WfResult VarCxt × E.Stmt) where
   wellFormed _ S.Pass = pure (Assigns Map.empty × E.Pass)
   wellFormed cxt (S.Return e) = (Returns × _) <<< E.Return <$> wellFormed cxt e
   wellFormed cxt (S.ExprStmt e) = (Assigns Map.empty × _) <<< E.ExprStmt <$> wellFormed cxt e
   wellFormed cxt (S.Assert e e') =
      (Assigns Map.empty × _) <$> (E.Assert <$> wellFormed cxt e <*> traverse (wellFormed cxt) e')
   wellFormed cxt (S.Def (S.VarDef p ψ e)) = do
      let xs = bv p
      for_ (Set.toUnfoldable (xs ∩ captures e) :: Array Var) \x ->
         throwError $ "Variable captured by its own definition: " <> x
      e' <- wellFormed cxt e
      p' <- wellFormed cxt p
      for_ ψ (resolveType cxt)
      pure (Assigns (constMap true xs) × E.Assign p' e')
   wellFormed cxt (S.DefRec ds) = do
      let fs = unions (Set.singleton <<< fst <$> ds)
      let cxt' = cxt `extendCxt` constMap true fs
      let groups = NEL.groupBy (eq `on` fst) ds
      checkDistinct ("Non-contiguous clauses for: " <> _) (NEL.toList (fst <<< NEL.head <$> groups))
      defs <- for groups \group -> do
         void $ wellFormedPatterns cxt' (group <#> \(_ × S.Clause (_ × ps × _)) -> S.PList (ps <#> \(S.Param p _) -> p))
         cs <- for group \(_ × S.Clause (αs × ps × ψ × s)) -> do
            let xs = unions (bv <$> ps)
            let ys = S.assigns s \\ xs
            let cxt_α = cxt' `withTypeParams` αs
            let cxt'' = cxt_α `extendCxt` constMap true xs `extendCxt` constMap false ys
            ps' <- traverse (\(S.Param p ψ') -> (×) <$> wellFormed cxt' p <*> traverse (resolveType cxt_α) ψ') ps
            τ <- traverse (resolveType cxt_α) ψ
            r × s' <- wellFormed cxt'' s
            pure (ps' × τ × close r s')
         (fst (NEL.head group) ↦ _) <$> clauses cs
      pure (Assigns (constMap true fs) × E.DefRec (E.RecDefs (D.fromFoldable defs)))
      where
      -- Body that may fall through returns None
      close Returns s = s
      close (Assigns _) s = E.Seq s (E.Return (E.Lit None))
   wellFormed cxt (S.Seq s1 s2) = do
      r1 × s1' <- wellFormed cxt s1
      case r1 of
         Returns -> throwError "Unreachable statement"
         Assigns δ -> do
            for_ (Set.toUnfoldable (captures s1 ∩ S.assigns s2) :: Array Var) \x ->
               throwError $ "Captured variable reassigned: " <> x
            r2 × s2' <- wellFormed (cxt `extendCxt` δ) s2
            pure (overrideRes r1 r2 × E.Seq s1' s2')
   wellFormed cxt (S.If es elseBranch) = do
      es' <- for es \(e × s) -> do
         e' <- wellFormed cxt e
         r × s' <- wellFormed cxt s
         pure (r × E.Branch e' s')
      rElse × elseBranch' <- case elseBranch of
         Just s -> map Just <$> wellFormed cxt s
         Nothing -> pure (Assigns Map.empty × Nothing)
      pure (foldl1 mergeRes (NEL.cons rElse (fst <$> es')) × E.If (snd <$> es') elseBranch')
   wellFormed cxt (S.Match e bs) = do
      e' <- wellFormed cxt e
      ps' <- wellFormedPatterns cxt (fst <$> bs)
      bs' <- for (NEL.zip ps' bs) \(p' × (p × s)) -> do
         let xs = bv p
         r × s' <- wellFormed (cxt `extendCxt` constMap true xs) s
         pure (overrideRes (Assigns (constMap true xs)) r × (p' × s'))
      pure (foldl1 mergeRes ((fst <$> bs') `snoc` rFall) × E.Match e' (snd <$> bs'))
      where
      rFall = case fst (NEL.last bs) of
         S.PVar _ -> Returns
         S.PWild -> Returns
         _ -> Assigns Map.empty
   wellFormed _ (S.Dataclass _ _ _ _) = error absurd
   wellFormed _ (S.TypeAlias _ _ _) = error absurd

wellFormedTop :: Name -> Cxt -> S.Stmt -> MayFail (Cxt × WfResult VarCxt × E.Stmt)
wellFormedTop q cxt (S.Dataclass c αs b xψs) = do
   predefName cxt "dataclass"
   let cxt_α = cxt `withTypeParams` αs
   let xs = fst <$> xψs
   when (length (nub xs) /= length xs) $ throwError $ "Duplicate field names in class: " <> c
   for_ xψs (resolveType cxt_α <<< snd)
   base <- for b \ψ -> case ψ of
      S.NameTy (NonEmptyList (base :| Nil)) _ -> do
         cls <- maybe (throwError $ "Base of class " <> c <> " is not a class: " <> base) pure (classFor cxt base)
         when (cls.name /= snoc q base) $ throwError $ "Cannot extend imported class: " <> base
         void $ resolveType cxt_α ψ
         let clash = Set.fromFoldable xs ∩ Set.fromFoldable (fields cls)
         when (not Set.isEmpty clash)
            $ throwError
            $ "Class " <> c <> " redeclares inherited field(s): "
                 <> show (Set.toUnfoldable clash :: List Var)
         pure base
      S.NameTy base _ -> throwError $ "Cannot extend imported class: " <> dottedName base
      _ -> throwError $ "Base of class " <> c <> " is not a class"
   let cls = { cxt, name: snoc q c, typeParams: αs, base, fields: xs }
   pure (Map.singleton c (Class cls) × Assigns Map.empty × E.Dataclass (snoc q c))
wellFormedTop _ cxt (S.TypeAlias x αs ψ) = do
   τ <- resolveType (cxt `withTypeParams` αs) ψ
   pure (Map.singleton x (TypeAlias αs τ) × Assigns Map.empty × E.TypeAlias x αs τ)
wellFormedTop q cxt (S.Seq t1 t2) = do
   decls1 × r1 × t1' <- wellFormedTop q cxt t1
   case r1 of
      Returns -> throwError "Unreachable statement"
      Assigns δ -> do
         for_ (Set.toUnfoldable (captures t1 ∩ S.assigns t2) :: Array Var) \x ->
            throwError $ "Captured variable reassigned: " <> x
         for_ (Map.toUnfoldable (Map.filterKeys (_ `Set.member` S.assigns t2) decls1) :: Array (Var × Entry)) \(x × θ) ->
            throwError $ (if x `Set.member` typeDecls t2 then duplicate θ else reassigned θ) <> x
         decls2 × r2 × t2' <- wellFormedTop q (Map.union decls1 (cxt `extendCxt` δ)) t2
         pure (Map.union decls2 decls1 × overrideRes r1 r2 × E.Seq t1' t2')
   where
   duplicate (TypeAlias _ _) = "Duplicate type alias declaration: "
   duplicate _ = "Duplicate class declaration: "
   reassigned (TypeAlias _ _) = "Type alias name reassigned: "
   reassigned _ = "Class name reassigned: "
wellFormedTop _ cxt s = do
   r × s' <- wellFormed cxt s
   pure (Map.empty × r × s')

withTypeParams :: Cxt -> List Var -> Cxt
withTypeParams cxt αs = Map.union (constMap TypeVar (Set.fromFoldable αs)) cxt

resolveType :: Cxt -> S.TypeExpr -> MayFail T.Type
resolveType cxt (S.PrimitiveTy ν) = T.PrimitiveTy ν <$ predefName cxt (T.primitiveName ν)
resolveType cxt (S.NameTy q ψs) = do
   τs <- traverse (resolveType cxt) ψs
   case resolveName cxt q of
      Just TypeVar | null ψs -> pure (T.VarTy (dottedName q))
      Just (TypeAlias αs τ) -> do
         when (length τs /= length αs) $ throwError $ arity "Type alias" αs τs
         pure (T.subst τs αs τ)
      Just (Class cls) -> do
         when (length τs /= length cls.typeParams) $ throwError $ arity "Class" cls.typeParams τs
         pure (T.ClassTy cls.name τs)
      Nothing -> throwError $ "Unbound name: " <> dottedName q
      _ -> throwError $ "Not a class: " <> dottedName q
   where
   arity what αs τs =
      what <> " " <> dottedName q <> " expects " <> show (length αs) <> " type argument(s); got " <> show (length τs)
resolveType cxt (S.LitTy ℓ) = T.LitTy ℓ <$ predefName cxt "Literal"
resolveType cxt (S.ListTy ψ) = predefName cxt "list" *> (T.ListTy <$> resolveType cxt ψ)
resolveType cxt (S.DictTy ψ) = predefName cxt "dict" *> predefName cxt "str" *> (T.DictTy <$> resolveType cxt ψ)
resolveType cxt (S.TupleTy ψs) = predefName cxt "tuple" *> (T.TupleTy <$> traverse (resolveType cxt) ψs)
resolveType cxt (S.CallableTy ψs ψ) =
   predefName cxt "Callable" *> (T.CallableTy <$> traverse (resolveType cxt) ψs <*> resolveType cxt ψ)
resolveType cxt (S.UnionTy ψ ψ') = T.UnionTy <$> resolveType cxt ψ <*> resolveType cxt ψ'

instance WellFormed S.Expr E.Expr where
   wellFormed cxt (S.Var x) = E.Var x <$ var cxt x
   wellFormed _ (S.Lit ℓ) = pure (E.Lit ℓ)
   wellFormed cxt (S.Call e ψs es xes) = case asName e >>= \c -> (c × _) <$> resolveName cxt c of
      Just (c × Class cls) -> do
         for_ (NEL.fromList ψs) \_ -> resolveType cxt (S.NameTy c ψs)
         let fs = fields cls
         when (null xes && length es /= length fs)
            $ throwError
            $ dottedName c <> " expects " <> show (length fs) <> " argument(s); got " <> show (length es)
         xes' <- if null xes then pure Nil else positionaliseKw cls c (length es) xes
         E.Constr cls.name <$> traverse (wellFormed cxt) (es <> xes')
      _ -> case NEL.fromList ψs of
         Nothing -> do
            when (not (null xes)) $ throwError "Keyword arguments in function call"
            E.App <$> wellFormed cxt e <*> traverse (wellFormed cxt) es
         Just ψs' -> do
            i <- traverse asIndex ψs'
            wellFormed cxt (S.Call (S.Subscript e (indexExpr i)) Nil es xes)
      where
      asIndex (S.NameTy q Nil) = pure (nameExpr q)
      asIndex _ = throwError $ "Type arguments for non-class: " <> maybe "expression" dottedName (asName e)

      indexExpr (NonEmptyList (i :| Nil)) = i
      indexExpr is = S.Tuple (NEL.toList is)

      nameExpr q = foldl S.Attribute (S.Var (NEL.head q)) (NEL.tail q)
   wellFormed cxt (S.BinOp e op e') = E.BinOp <$> wellFormed cxt e <@> op <*> wellFormed cxt e'
   wellFormed cxt (S.UnOp op e) = E.UnOp op <$> wellFormed cxt e
   wellFormed cxt (S.And e e') = E.And <$> wellFormed cxt e <*> wellFormed cxt e'
   wellFormed cxt (S.Or e e') = E.Or <$> wellFormed cxt e <*> wellFormed cxt e'
   wellFormed cxt (S.InfixApp e f e') = do
      var cxt f
      E.App (E.Var f) <$> traverse (wellFormed cxt) (e : e' : Nil)
   wellFormed cxt (S.Cond e1 e e2) = E.Cond <$> wellFormed cxt e1 <*> wellFormed cxt e <*> wellFormed cxt e2
   wellFormed cxt (S.Attribute e y) = case resolveName cxt =<< asName e of
      Just (ModChecked q cxt') -> do
         when (not (Map.member y cxt'))
            $ throwError
            $ "module " <> dottedName q <> " has no member " <> y
         var cxt' y
         pure (E.ModMember q y)
      _ -> flip E.Attribute y <$> wellFormed cxt e
   wellFormed cxt (S.Subscript e e') = E.Subscript <$> wellFormed cxt e <*> wellFormed cxt e'
   wellFormed cxt (S.Matrix e1 (x × y) e2) =
      (\e2' e1' -> E.Matrix e1' (x × y) e2') <$> wellFormed cxt e2 <*> wellFormed
         (cxt `extendCxt` constMap true (Set.singleton x ∪ Set.singleton y))
         e1
   wellFormed cxt (S.Lambda (S.LambdaClause (ps × e))) = do
      ps' <- traverse (wellFormed cxt) ps
      e' <- wellFormed (cxt `extendCxt` constMap true (unions (bv <$> ps))) e
      E.Lambda <$> clauses (NEL.singleton ((ps' <#> (_ × Nothing)) × Nothing × E.Return e'))
   wellFormed cxt (S.Dictionary kvs) =
      E.Dictionary <$> traverse (\(k × v) -> Pair <$> wellFormed cxt k <*> wellFormed cxt v) kvs
   wellFormed cxt (S.Paragraph elems) =
      E.Constr cParagraph <<< (_ : Nil) <<< E.List <$> traverse pe elems
      where
      pe (S.Unquote e) = wellFormed cxt e
      pe (S.Token str) = pure (E.Lit (Str str))
   wellFormed cxt (S.List es) = E.List <$> traverse (wellFormed cxt) es
   wellFormed cxt (S.Tuple es) = E.Tuple <$> traverse (wellFormed cxt) es
   wellFormed cxt (S.ListComp e gs) =
      (\(e' × gs') -> E.ListComp e' gs') <$> wellFormedQualifiers cxt gs (\cxt' -> wellFormed cxt' e)
   wellFormed cxt (S.DictComp k e gs) =
      (\((k' × e') × gs') -> E.DictComp k' e' gs') <$> wellFormedQualifiers cxt gs \cxt' ->
         (×) <$> wellFormed cxt' k <*> wellFormed cxt' e
   wellFormed cxt (S.DocExpr e e') =
      E.DocExpr <$> wellFormed (cxt `extendCxt` constMap true (Set.singleton varThis)) e <*> wellFormed cxt e'

asName :: S.Expr -> Maybe Name
asName (S.Var x) = Just (singleton x)
asName (S.Attribute e y) = asName e <#> (_ <> singleton y)
asName _ = Nothing

wellFormedQualifiers
   :: forall b
    . Cxt
   -> List S.Qualifier
   -> (Cxt -> MayFail b)
   -> MayFail (b × List E.Qualifier)
wellFormedQualifiers cxt Nil body = (_ × Nil) <$> body cxt
wellFormedQualifiers cxt (g : gs) body = case g of
   S.Guard e -> do
      e' <- wellFormed cxt e
      map (E.Guard e' : _) <$> wellFormedQualifiers cxt gs body
   S.Generator p e -> do
      e' <- wellFormed cxt e
      p' <- wellFormed cxt p
      map (E.Generator p' e' : _) <$> wellFormedQualifiers (cxt `extendCxt` constMap true (bv p)) gs body
   S.Decl (S.VarDef p ψ e) -> do
      for_ ψ (resolveType cxt)
      e' <- wellFormed cxt e
      p' <- wellFormed cxt p
      map (E.Decl p' e' : _) <$> wellFormedQualifiers (cxt `extendCxt` constMap true (bv p)) gs body

-- Keyword arguments in field order; must cover fields after first n exactly.
positionaliseKw :: forall b. ClassEntry -> Name -> Int -> List (Bind b) -> MayFail (List b)
positionaliseKw cls c n xbs = do
   let remaining = drop n (fields cls)
   let provided = fst <$> xbs
   when (sort provided /= sort remaining) $ throwError $
      "Class " <> NEL.last c <> " keyword fields mismatch: expected " <> show remaining <> ", got " <> show provided
   pure $ remaining <#> \f -> definitely' (snd <$> find (\(k ↦ _) -> k == f) xbs)

-- Parameter names for desugared functions, kept apart from source identifiers by the leading $.
param :: Int -> Var
param i = "$" <> show i

-- Clauses over k parameters as a function of k parameters. A parameter column that is the same variable in
-- every clause is a parameter of that name; the remaining columns are matched together, as nested pairs when
-- there are several.
clauses :: NEL.NonEmptyList (List (S.Pattern × Maybe T.Type) × Maybe T.Type × E.Stmt) -> MayFail E.Def
clauses cs = do
   let n = length (fst (NEL.head cs)) :: Int
   for_ cs \(ps × _) ->
      when (length ps /= n) $ throwError "Clauses differ in number of parameters"
   for_ (transpose (NEL.toList (cs <#> \(ps × _) -> snd <$> ps))) (agree "parameter annotations" <<< nonEmpty)
   agree "return annotation" (cs <#> \(_ × ψ × _) -> ψ)
   let
      columns = transpose (NEL.toList (cs <#> \(ps × _) -> fst <$> ps))
      named = columns # mapWithIndex \i ps -> case sharedVar ps of
         Just x -> x × Nothing
         Nothing -> param (i + 1) × Just ps
      matched = named # mapMaybe \(x × ps_opt) -> (x × _) <$> ps_opt
      ss = cs <#> \(_ × _ × s) -> s
      body = case matched of
         Nil -> NEL.head ss
         (x × ps) : Nil -> E.Match (E.Var x) (NEL.zip (nonEmpty ps) ss)
         _ -> E.Match (E.Tuple (E.Var <<< fst <$> matched)) (NEL.zipWith (\ps s -> S.PTuple ps × s) (nonEmpty (transpose (snd <$> matched))) ss)
   pure (E.Def (fst <$> named) body)
   where
   sharedVar :: List S.Pattern -> Maybe Var
   sharedVar (S.PVar x : ps) | all (_ == S.PVar x) ps = Just x
   sharedVar _ = Nothing

   agree :: String -> NEL.NonEmptyList (Maybe T.Type) -> MayFail Unit
   agree what ψs =
      unless (all (\ψ -> ψ == Nothing || ψ == NEL.head ψs) (NEL.tail ψs)) $ throwError ("Clauses differ in " <> what)

var :: Cxt -> Var -> MayFail Unit
var cxt x = case Map.lookup x cxt of
   Just (VarStatus true) -> pure unit
   Just (VarStatus false) -> throwError $ "Not definitely assigned: " <> x
   Just (Mod q) -> throwError $ "module " <> dottedName q <> " is not a value"
   Just (ModChecked q _) -> throwError $ "module " <> dottedName q <> " is not a value"
   Just (Class _) -> throwError $ "class " <> x <> " is not a value"
   Just TypeVar -> throwError $ "type parameter " <> x <> " is not a value"
   Just (TypeAlias _ _) -> throwError $ "type alias " <> x <> " is not a value"
   Just PredefName -> throwError $ "predefined name " <> x <> " is not a value"
   Nothing -> throwError $ "Unbound name: " <> x

predefName :: Cxt -> Var -> MayFail Unit
predefName cxt x = case Map.lookup x cxt of
   Just PredefName -> pure unit
   _ -> throwError $ "Not bound as a predefined name: " <> x

-- Case patterns well-formed as a list: each well-formed, and none subsumed by an earlier one.
wellFormedPatterns :: Cxt -> NEL.NonEmptyList S.Pattern -> MayFail (NEL.NonEmptyList S.Pattern)
wellFormedPatterns cxt ps = forWithIndex ps \i p -> do
   forWithIndex_ (drop (i + 1) (NEL.toList ps)) \j p' ->
      when (subsumed cxt p' p) $ throwError $ "case " <> show (i + j + 2) <> " is unreachable"
   wellFormed cxt p

instance WellFormed S.Pattern S.Pattern where
   wellFormed cxt (S.PConstr c ps xps) = do
      cls <- classOf cxt c
      when (cls.name == cRange) $ throwError "range not permitted in a constructor pattern"
      let fs = fields cls
      when (null xps && length ps /= length fs)
         $ throwError
         $ dottedName c <> " expects " <> show (length fs) <> " argument(s); got " <> show (length ps)
      distinctVars (ps <> (snd <$> xps))
      xps' <- if null xps then pure Nil else positionaliseKw cls c (length ps) xps
      S.PConstr cls.name <$> traverse (wellFormed cxt) (ps <> xps') <@> Nil
   wellFormed cxt (S.PRecord xps) = do
      checkDistinct ("Duplicate key in pattern: " <> _) (fst <$> xps)
      distinctVars (snd <$> xps)
      S.PRecord <$> traverse (traverse (wellFormed cxt)) xps
   wellFormed cxt (S.PList ps) = do
      distinctVars ps
      S.PList <$> traverse (wellFormed cxt) ps
   wellFormed cxt (S.PTuple ps) = do
      distinctVars ps
      S.PTuple <$> traverse (wellFormed cxt) ps
   wellFormed cxt (S.PAs p x) = do
      distinctVars (p : S.PVar x : Nil)
      S.PAs <$> wellFormed cxt p <@> x
   wellFormed _ p = pure p

distinctVars :: List S.Pattern -> MayFail Unit
distinctVars ps = checkDistinct ("Duplicate variable in pattern: " <> _) (ps >>= Set.toUnfoldable <<< bv)

subsumed :: Cxt -> S.Pattern -> S.Pattern -> Boolean
subsumed _ _ (S.PVar _) = true
subsumed _ _ S.PWild = true
subsumed cxt (S.PAs p _) p' = subsumed cxt p p'
subsumed cxt p (S.PAs p' _) = subsumed cxt p p'
subsumed _ (S.PLit ℓ) (S.PLit ℓ') = ℓ == ℓ'
subsumed cxt (S.PRecord xps) (S.PRecord xps') =
   all (\(x × p') -> maybe false (\p -> subsumed cxt p p') (F.lookup x xps)) xps'
subsumed cxt (S.PList ps) (S.PList ps') = length ps == length ps' && and (zipWith (subsumed cxt) ps ps')
subsumed cxt (S.PTuple ps) (S.PTuple ps') = length ps == length ps' && and (zipWith (subsumed cxt) ps ps')
subsumed cxt (S.PConstr c ps xps) (S.PConstr c' ps' xps') = fromMaybe false do
   cls <- hush (classOf cxt c)
   cls' <- hush (classOf cxt c')
   guard (cls'.name `elem` ancestors cls)
   pure $ all (\x -> fromMaybe false (subsumed cxt <$> fieldMap cls ps xps x <*> fieldMap cls' ps' xps' x)) (fields cls')
subsumed _ _ _ = false

