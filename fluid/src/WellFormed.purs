module WellFormed where

import Prelude

import Bind (Bind, Name, Var, dottedName, prefixOf, properPrefixOf, varThis, (↦))
import Control.Monad.Error.Class (throwError)
import Control.Monad.Reader (ReaderT, ask, mapReaderT, runReaderT)
import Control.Monad.State (StateT, get, mapStateT, modify_, runStateT)
import Control.Monad.Trans.Class (lift)
import Data.Bifunctor (lmap)
import Data.Either (Either, hush)
import Control.MonadPlus (guard)
import Data.Foldable (all, and, elem, find, foldM, foldr, for_, intercalate)
import Data.Function (on)
import Data.FoldableWithIndex (forWithIndex_)
import Data.FunctorWithIndex (mapWithIndex)
import Data.TraversableWithIndex (forWithIndex)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe, maybe)
import Data.List (List(..), drop, length, mapMaybe, nub, null, sort, transpose, zipWith, (:))
import Data.Foldable (lookup) as F
import ModuleGraph (ModuleName, implicitFor)
import Data.List.NonEmpty as NEL
import Data.Semigroup.Foldable (foldl1, foldr1)
import Data.Set (Set, unions)
import Data.Set as Set
import Data.Traversable (for, traverse)
import Data.Tuple (fst, snd)
import DataType (cPair, cParagraph)
import DefiniteAssignment (ClassEntry, VarCxt, Entry(..), Cxt, WfResult(..), ancestors, classFor, className, classOf, erase, extendCxt, extendCxtWith, fieldMap, fields, mergeRes, overrideRes, resolveName)
import Dict as D
import Util.Map (constMap)
import Expr (bv, fv)
import Expr (Pattern(..)) as S
import Expr (Branch(..), Def(..), Expr(..), Import(..), Module(..), Param(..), Qualifier(..), RecDefs(..), Stmt(..)) as E
import Literal (Literal(..))
import SExpr (Clause(..), Expr(..), Import(..), LambdaClause(..), Module(..), Param(..), ParagraphElem(..), Qualifier(..), Stmt(..), VarDef(..)) as S
import Type as T
import Util (type (×), checkDistinct, definitely, nonEmpty, singleton, whenever, (×), (∩))
import Util.Pair (Pair(..))
import Util.Set ((\\), (∪))

-- Predefined modules and program (under __main__) have no body
type LoadedModule = { cxt :: Cxt, mod :: Maybe E.Module }

-- Modules loaded so far, over parsed modules.
type LoadM = StateT (Map.Map ModuleName LoadedModule) (ReaderT (Map.Map ModuleName S.Module) (Either String))

runLoadM :: forall a. LoadM a -> Map.Map ModuleName S.Module -> Map.Map ModuleName Cxt -> Either String (a × Map.Map ModuleName LoadedModule)
runLoadM m mods predefined = runReaderT (runStateT m (predefined <#> \cxt -> { cxt, mod: Nothing })) mods

checkProgram :: List S.Import -> S.Stmt -> LoadM (VarCxt × E.Stmt)
checkProgram imports s = do
   _ × cxt_imp <- checkImports mainModule imports
   -- Unlike a module (checkStatements), the program may return: a top-level return yields
   -- its result value. The spec forbids this, treating __main__ as a module; Fluid does not.
   decls × _ × s' <- lift (lift (wellFormedTop mainModule (Map.insert "__name__" (VarStatus true) cxt_imp) s))
   modify_ (Map.insert mainModule { cxt: Class <$> decls, mod: Nothing })
   pure (Map.insert "__name__" true (erase cxt_imp) × s')

-- Member context of module q, loaded on demand as its import is checked; memoised. The recursion has no
-- cycle guard; it terminates because the dependency graph is acyclic.
loadModule :: ModuleName -> LoadM Cxt
loadModule q = get >>= \loaded -> case Map.lookup q loaded of
   Just { cxt } -> pure cxt
   Nothing -> mapStateT (mapReaderT (lmap (_ <> "\nChecking module " <> dottedName q))) do
      mods <- lift ask
      mod@(S.Module is _) <- maybe (throwError ("Module not parsed: " <> dottedName q)) pure (Map.lookup q mods)
      importCxt × cxt_imp <- checkImports q is
      δ × mod' <- lift (lift (checkStatements q cxt_imp mod))
      let subs = submodules (Map.keys mods) q
      let clash = (Map.keys importCxt ∪ Map.keys δ) ∩ Map.keys subs
      when (not Set.isEmpty clash)
         $ throwError
         $ "Submodule name clash in module " <> dottedName q <> ": " <> intercalate ", " (Set.toUnfoldable clash :: List Var)
      let cxt = subs `Map.union` δ
      modify_ (Map.insert q { cxt, mod: Just mod' })
      pure cxt

checkImports :: ModuleName -> List S.Import -> LoadM (Cxt × Cxt)
checkImports enclosing is = do
   implicitCxt <- foldM (\acc q -> (acc `Map.union` _) <$> loadModule q) Map.empty (implicitFor enclosing)
   importCxt <- foldM (\acc i -> (acc `extendCxtWith` _) <$> importBindings enclosing i) Map.empty is
   pure (importCxt × (implicitCxt `extendCxtWith` importCxt))

-- Bindings contributed by one import of the enclosing module.
importBindings :: ModuleName -> S.Import -> LoadM Cxt
importBindings enclosing (S.Import q Nothing) = do
   when (enclosing `properPrefixOf` q)
      $ throwError
      $ "Module " <> dottedName enclosing <> " cannot import its own descendant " <> dottedName q
   θ <- ModLoaded q <$> loadModule q
   Map.singleton (NEL.head q) <$> loadsTo Nothing q θ
importBindings enclosing (S.Import q (Just xs)) = do
   cxt <- loadModule q
   _ <- loadsTo (Just enclosing) q (ModLoaded q cxt) -- loads q's ancestors; contributes no bindings
   importedMembers q cxt xs

-- Wrap the reference for module q in loaded references for its proper
-- prefixes, loading each; prefixes of the bound (the enclosing module,
-- for a from-import) are exempt.
loadsTo :: Maybe ModuleName -> ModuleName -> Entry -> LoadM Entry
loadsTo bound q θ = case NEL.fromList init of
   Nothing -> pure θ
   Just q'
      | maybe false (q' `prefixOf` _) bound -> pure θ
      | otherwise -> do
           cxt <- loadModule q'
           loadsTo bound q' (ModLoaded q' (cxt `extendCxtWith` Map.singleton x θ))
   where
   { init, last: x } = NEL.unsnoc q

-- Bindings for names imported from module q with member context cxt.
importedMembers :: ModuleName -> Cxt -> List Var -> LoadM Cxt
importedMembers _ _ Nil = pure Map.empty
importedMembers q cxt (x : xs) = do
   othersCxt <- importedMembers q cxt xs
   case Map.lookup x cxt of
      Just (Mod q') -> loadModule q' <#> \cxt' -> Map.insert x (ModLoaded q' cxt') othersCxt
      Just (VarStatus false) -> throwError $ "Not definitely assigned: " <> x
      Just θ -> pure (Map.insert x θ othersCxt)
      Nothing -> throwError $ "Cannot import name " <> x <> " from module " <> dottedName q

-- Stubs for the immediate submodules of q in the module table.
submodules :: Set ModuleName -> ModuleName -> Cxt
submodules modules q = Map.fromFoldable (mapMaybe sub (Set.toUnfoldable modules))
   where
   sub m = let { init, last: x } = NEL.unsnoc m in whenever (NEL.fromList init == Just q) (x × Mod m)

checkStatements :: Name -> Cxt -> S.Module -> Either String (Cxt × E.Module)
checkStatements q cxt_imp (S.Module imports ss) =
   case foldr (\s acc -> Just (maybe s (S.Seq s) acc)) Nothing ss of
      Nothing -> pure (Map.singleton "__name__" (VarStatus true) × E.Module imports' Nil)
      Just s -> do
         decls × r × s' <- wellFormedTop q (Map.insert "__name__" (VarStatus true) cxt_imp) s
         case r of
            Returns -> throwError "Module body cannot return"
            Assigns δ ->
               pure (Map.insert "__name__" (VarStatus true) (Map.union (Class <$> decls) (VarStatus <$> δ)) × E.Module imports' (unSeq s'))
   where
   imports' = imports <#> \(S.Import q' xs) -> E.Import q' xs
   unSeq (E.Seq s1 s2) = s1 : unSeq s2
   unSeq s = s : Nil

mainModule :: Name
mainModule = pure "__main__"

assigns :: S.Stmt -> Set Var
assigns S.Pass = Set.empty
assigns (S.Def (S.VarDef p _ _)) = bv p
assigns (S.ExprStmt _) = Set.empty
assigns (S.Assert _ _) = Set.empty
assigns (S.Return _) = Set.empty
assigns (S.If es s) = unions (assigns <$> (snd <$> es)) ∪ maybe Set.empty assigns s
assigns (S.Match _ ps) = unions (assigns <$> (snd <$> ps))
assigns (S.DefRec ds) = unions (Set.singleton <<< fst <$> ds)
assigns (S.Seq s1 s2) = assigns s1 ∪ assigns s2
assigns (S.Dataclass c _ _) = Set.singleton c

classDecls :: S.Stmt -> Set Var
classDecls (S.Dataclass c _ _) = Set.singleton c
classDecls (S.Seq s1 s2) = classDecls s1 ∪ classDecls s2
classDecls _ = Set.empty

captures :: S.Stmt -> Set Var
captures S.Pass = Set.empty
captures (S.Def (S.VarDef _ _ e)) = capturesE e
captures (S.ExprStmt e) = capturesE e
captures (S.Assert e e') = capturesE e ∪ maybe Set.empty capturesE e'
captures (S.Return e) = capturesE e
captures (S.If es s) =
   unions ((\(e × s') -> capturesE e ∪ captures s') <$> es) ∪ maybe Set.empty captures s
captures (S.Match e ps) =
   capturesE e ∪ unions ((\(_ × s) -> captures s) <$> ps)
captures (S.DefRec ds) =
   (unions (clauseCaptures <$> ds)) \\ unions (Set.singleton <<< fst <$> ds)
   where
   clauseCaptures (_ × S.Clause (ps × _ × s)) =
      (fv s \\ unions (bv <$> ps)) \\ assigns s
captures (S.Seq s1 s2) = captures s1 ∪ captures s2
captures (S.Dataclass _ _ _) = Set.empty

capturesE :: S.Expr -> Set Var
capturesE (S.Var _) = Set.empty
capturesE (S.Lit _) = Set.empty
capturesE (S.Call e es xes) = capturesE e ∪ unions (capturesE <$> es) ∪ unions ((capturesE <<< snd) <$> xes)
capturesE (S.Dictionary es) =
   unions ((\(k × v) -> capturesE k ∪ capturesE v) <$> es)
capturesE (S.Matrix e (x × y) e') =
   (capturesE e \\ (Set.singleton x ∪ Set.singleton y)) ∪ capturesE e'
capturesE (S.Lambda (S.LambdaClause (ps × e))) =
   fv e \\ unions (bv <$> ps)
capturesE (S.Attribute e _) = capturesE e
capturesE (S.Subscript e e') = capturesE e ∪ capturesE e'
capturesE (S.BinOp e _ e') = capturesE e ∪ capturesE e'
capturesE (S.UnOp _ e) = capturesE e
capturesE (S.And e e') = capturesE e ∪ capturesE e'
capturesE (S.Or e e') = capturesE e ∪ capturesE e'
capturesE (S.InfixApp e _ e') = capturesE e ∪ capturesE e'
capturesE (S.Cond e1 e e2) = capturesE e1 ∪ capturesE e ∪ capturesE e2
capturesE (S.Paragraph es) = unions (capturesPe <$> es)
   where
   capturesPe (S.Token _) = Set.empty
   capturesPe (S.Unquote e) = capturesE e
capturesE (S.List es) = Set.unions (capturesE <$> es)
capturesE (S.ListComp e gs) = capturesQualifiers gs ∪ (capturesE e \\ bv gs)
capturesE (S.DictComp k e gs) = capturesQualifiers gs ∪ ((capturesE k ∪ capturesE e) \\ bv gs)
capturesE (S.DocExpr e e') = (capturesE e \\ Set.singleton varThis) ∪ capturesE e'

capturesQualifiers :: List S.Qualifier -> Set Var
capturesQualifiers Nil = Set.empty
capturesQualifiers (S.Guard e : gs) = capturesE e ∪ capturesQualifiers gs
capturesQualifiers (S.Generator p e : gs) = capturesE e ∪ (capturesQualifiers gs \\ bv p)
capturesQualifiers (S.Decl (S.VarDef p _ e) : gs) = capturesE e ∪ (capturesQualifiers gs \\ bv p)

wellFormed :: Name -> Cxt -> S.Stmt -> Either String (WfResult VarCxt × E.Stmt)
wellFormed _ _ S.Pass = pure (Assigns Map.empty × E.Pass)
wellFormed _ cxt (S.Return e) = (Returns × _) <<< E.Return <$> wellFormedExpr cxt e
wellFormed _ cxt (S.ExprStmt e) = (Assigns Map.empty × _) <<< E.ExprStmt <$> wellFormedExpr cxt e
wellFormed _ cxt (S.Assert e e') =
   (Assigns Map.empty × _) <$> (E.Assert <$> wellFormedExpr cxt e <*> traverse (wellFormedExpr cxt) e')
wellFormed _ cxt (S.Def (S.VarDef p ψ e)) = do
   let xs = bv p
   for_ (Set.toUnfoldable (xs `Set.intersection` capturesE e) :: Array Var) \x ->
      throwError $ "Variable captured by its own definition: " <> x
   e' <- wellFormedExpr cxt e
   p' <- wellFormedPattern cxt p
   τ <- traverse (resolveType cxt) ψ
   pure (Assigns (constMap true xs) × E.Assign p' τ e')
wellFormed q cxt (S.DefRec ds) = do
   let fs = unions (Set.singleton <<< fst <$> ds)
   let cxt' = cxt `extendCxt` constMap true fs
   let groups = NEL.groupBy (eq `on` fst) ds
   checkDistinct ("Non-contiguous clauses for: " <> _) (NEL.toList (fst <<< NEL.head <$> groups))
   defs <- for groups \group -> do
      void $ wellFormedPatterns cxt' (group <#> \(_ × S.Clause (ps × _)) -> S.PList (ps <#> \(S.Param p _) -> p))
      cs <- for group \(_ × S.Clause (ps × ψ × s)) -> do
         let xs = unions (bv <$> ps)
         let ys = assigns s \\ xs
         let cxt'' = cxt' `extendCxt` constMap true xs `extendCxt` constMap false ys
         ps' <- traverse (\(S.Param p ψ') -> (×) <$> wellFormedPattern cxt' p <*> traverse (resolveType cxt') ψ') ps
         τ <- traverse (resolveType cxt') ψ
         r × s' <- wellFormed q cxt'' s
         pure (ps' × τ × close r s')
      (fst (NEL.head group) ↦ _) <$> clauses cs
   pure (Assigns (constMap true fs) × E.DefRec (E.RecDefs (D.fromFoldable defs)))
   where
   -- Body that may fall through returns None
   close Returns s = s
   close (Assigns _) s = E.Seq s (E.Return (E.Lit None))
wellFormed q cxt (S.Seq s1 s2) = do
   r1 × s1' <- wellFormed q cxt s1
   case r1 of
      Returns -> throwError "Unreachable statement"
      Assigns δ -> do
         for_ (Set.toUnfoldable (captures s1 `Set.intersection` assigns s2) :: Array Var) \x ->
            throwError $ "Captured variable reassigned: " <> x
         r2 × s2' <- wellFormed q (cxt `extendCxt` δ) s2
         pure (overrideRes r1 r2 × E.Seq s1' s2')
wellFormed q cxt (S.If es elseBranch) = do
   es' <- for es \(e × s) -> do
      e' <- wellFormedExpr cxt e
      r × s' <- wellFormed q cxt s
      pure (r × E.Branch e' s')
   rElse × elseBranch' <- case elseBranch of
      Just s -> map Just <$> wellFormed q cxt s
      Nothing -> pure (Assigns Map.empty × Nothing)
   pure (foldl1 mergeRes (NEL.cons rElse (fst <$> es')) × E.If (snd <$> es') elseBranch')
wellFormed q cxt (S.Match e bs) = do
   e' <- wellFormedExpr cxt e
   ps' <- wellFormedPatterns cxt (fst <$> bs)
   bs' <- for (NEL.zip ps' bs) \(p' × (p × s)) -> do
      let xs = bv p
      r × s' <- wellFormed q (cxt `extendCxt` constMap true xs) s
      pure (overrideRes (Assigns (constMap true xs)) r × (p' × s'))
   pure (foldl1 mergeRes ((fst <$> bs') `NEL.snoc` rFall) × E.Match e' (snd <$> bs'))
   where
   rFall = case fst (NEL.last bs) of
      S.PVar _ -> Returns
      S.PWild -> Returns
      _ -> Assigns Map.empty
wellFormed _ _ (S.Dataclass c _ _) = throwError $ "Class declaration not at top level: " <> c

wellFormedTop :: Name -> Cxt -> S.Stmt -> Either String (Map.Map Var ClassEntry × WfResult VarCxt × E.Stmt)
wellFormedTop q cxt (S.Dataclass c b xψs) = do
   predefName cxt "dataclass"
   let xs = fst <$> xψs
   when (length (nub xs) /= length xs) $ throwError $ "Duplicate field names in class: " <> c
   for_ xψs (resolveType cxt <<< snd)
   case b of
      Nothing -> pure unit
      Just base -> do
         cls <- maybe (throwError $ "Unknown class: " <> base) pure (classFor cxt base)
         when (cls.name /= NEL.snoc q base) $ throwError $ "Cannot extend imported class: " <> base
         let clash = Set.intersection (Set.fromFoldable xs) (Set.fromFoldable (fields cls))
         when (not Set.isEmpty clash)
            $ throwError
            $ "Class " <> c <> " redeclares inherited field(s): "
                 <> show (Set.toUnfoldable clash :: List Var)
   pure (Map.singleton c { cxt, name: NEL.snoc q c, base: b, fields: xs } × Assigns Map.empty × E.Pass)
wellFormedTop q cxt (S.Seq t1 t2) = do
   decls1 × r1 × t1' <- wellFormedTop q cxt t1
   case r1 of
      Returns -> throwError "Unreachable statement"
      Assigns δ -> do
         for_ (Set.toUnfoldable (captures t1 `Set.intersection` assigns t2) :: Array Var) \x ->
            throwError $ "Captured variable reassigned: " <> x
         for_ (Set.toUnfoldable (Map.keys decls1 `Set.intersection` assigns t2) :: Array Var) \c ->
            throwError $ (if c `Set.member` classDecls t2 then "Duplicate class declaration: " else "Class name reassigned: ") <> c
         decls2 × r2 × t2' <- wellFormedTop q (Map.union (Class <$> decls1) (cxt `extendCxt` δ)) t2
         pure (Map.union decls2 decls1 × overrideRes r1 r2 × E.Seq t1' t2')
wellFormedTop q cxt s = do
   r × s' <- wellFormed q cxt s
   pure (Map.empty × r × s')

resolveType :: Cxt -> T.TypeExpr Name -> Either String T.Type
resolveType cxt (T.Primitive ν) = T.Primitive ν <$ predefName cxt (T.primitiveName ν)
resolveType cxt (T.ClassName q) = T.ClassName <<< T.Class <$> className cxt q
resolveType cxt (T.Lit ℓ) = T.Lit ℓ <$ predefName cxt "Literal"
resolveType cxt (T.List ψ) = predefName cxt "list" *> (T.List <$> resolveType cxt ψ)
resolveType cxt (T.Dict ψ) = predefName cxt "dict" *> predefName cxt "str" *> (T.Dict <$> resolveType cxt ψ)
resolveType cxt (T.Tuple ψs) = predefName cxt "tuple" *> (T.Tuple <$> traverse (resolveType cxt) ψs)
resolveType cxt (T.Callable ψs ψ) =
   predefName cxt "Callable" *> (T.Callable <$> traverse (resolveType cxt) ψs <*> resolveType cxt ψ)
resolveType cxt (T.Union ψ ψ') = T.Union <$> resolveType cxt ψ <*> resolveType cxt ψ'

wellFormedExpr :: Cxt -> S.Expr -> Either String E.Expr
wellFormedExpr cxt (S.Var x) = E.Var x <$ var cxt x
wellFormedExpr _ (S.Lit ℓ) = pure (E.Lit ℓ)
wellFormedExpr cxt (S.Call e es xes) = case asName e >>= \c -> (c × _) <$> resolveName cxt c of
   Just (c × Class cls) -> do
      let fs = fields cls
      when (null xes && length es /= length fs)
         $ throwError
         $ dottedName c <> " expects " <> show (length fs) <> " argument(s); got " <> show (length es)
      xes' <- if null xes then pure Nil else positionaliseKw cls c (length es) xes
      E.Constr cls.name <$> traverse (wellFormedExpr cxt) (es <> xes')
   _ -> do
      when (not (null xes)) $ throwError "Keyword arguments in function call"
      E.App <$> wellFormedExpr cxt e <*> traverse (wellFormedExpr cxt) es
wellFormedExpr cxt (S.BinOp e op e') = E.BinOp <$> wellFormedExpr cxt e <@> op <*> wellFormedExpr cxt e'
wellFormedExpr cxt (S.UnOp op e) = E.UnOp op <$> wellFormedExpr cxt e
wellFormedExpr cxt (S.And e e') = E.And <$> wellFormedExpr cxt e <*> wellFormedExpr cxt e'
wellFormedExpr cxt (S.Or e e') = E.Or <$> wellFormedExpr cxt e <*> wellFormedExpr cxt e'
wellFormedExpr cxt (S.InfixApp e f e') = do
   var cxt f
   E.App (E.Var f) <$> traverse (wellFormedExpr cxt) (e : e' : Nil)
wellFormedExpr cxt (S.Cond e1 e e2) = E.Cond <$> wellFormedExpr cxt e1 <*> wellFormedExpr cxt e <*> wellFormedExpr cxt e2
wellFormedExpr cxt (S.Attribute e y) = case resolveName cxt =<< asName e of
   Just (ModLoaded q cxt') -> do
      when (not (Map.member y cxt'))
         $ throwError
         $ "module " <> dottedName q <> " has no member " <> y
      pure (E.ModMember q y)
   _ -> flip E.Attribute y <$> wellFormedExpr cxt e
wellFormedExpr cxt (S.Subscript e e') = E.Subscript <$> wellFormedExpr cxt e <*> wellFormedExpr cxt e'
wellFormedExpr cxt (S.Matrix e1 (x × y) e2) =
   (\e2' e1' -> E.Matrix e1' (x × y) e2') <$> wellFormedExpr cxt e2 <*> wellFormedExpr
      (cxt `extendCxt` constMap true (Set.singleton x ∪ Set.singleton y))
      e1
wellFormedExpr cxt (S.Lambda (S.LambdaClause (ps × e))) = do
   ps' <- traverse (wellFormedPattern cxt) ps
   e' <- wellFormedExpr (cxt `extendCxt` constMap true (unions (bv <$> ps))) e
   E.Lambda <$> clauses (NEL.singleton ((ps' <#> (_ × Nothing)) × Nothing × E.Return e'))
wellFormedExpr cxt (S.Dictionary kvs) =
   E.Dictionary <$> traverse (\(k × v) -> Pair <$> wellFormedExpr cxt k <*> wellFormedExpr cxt v) kvs
wellFormedExpr cxt (S.Paragraph elems) =
   E.Constr cParagraph <<< (_ : Nil) <<< E.List <$> traverse pe elems
   where
   pe (S.Unquote e) = wellFormedExpr cxt e
   pe (S.Token str) = pure (E.Lit (Str str))
wellFormedExpr cxt (S.List es) = E.List <$> traverse (wellFormedExpr cxt) es
wellFormedExpr cxt (S.ListComp e gs) =
   (\(e' × gs') -> E.ListComp e' gs') <$> wellFormedQualifiers cxt gs (\cxt' -> wellFormedExpr cxt' e)
wellFormedExpr cxt (S.DictComp k e gs) =
   (\((k' × e') × gs') -> E.DictComp k' e' gs') <$> wellFormedQualifiers cxt gs \cxt' ->
      (×) <$> wellFormedExpr cxt' k <*> wellFormedExpr cxt' e
wellFormedExpr cxt (S.DocExpr e e') =
   E.DocExpr <$> wellFormedExpr (cxt `extendCxt` constMap true (Set.singleton varThis)) e <*> wellFormedExpr cxt e'

asName :: S.Expr -> Maybe Name
asName (S.Var x) = Just (singleton x)
asName (S.Attribute e y) = asName e <#> (_ <> singleton y)
asName _ = Nothing

wellFormedQualifiers
   :: forall b
    . Cxt
   -> List S.Qualifier
   -> (Cxt -> Either String b)
   -> Either String (b × List E.Qualifier)
wellFormedQualifiers cxt Nil body = (_ × Nil) <$> body cxt
wellFormedQualifiers cxt (g : gs) body = case g of
   S.Guard e -> do
      e' <- wellFormedExpr cxt e
      map (E.Guard e' : _) <$> wellFormedQualifiers cxt gs body
   S.Generator p e -> do
      e' <- wellFormedExpr cxt e
      p' <- wellFormedPattern cxt p
      map (E.Generator p' e' : _) <$> wellFormedQualifiers (cxt `extendCxt` constMap true (bv p)) gs body
   S.Decl (S.VarDef p ψ e) -> do
      for_ ψ (resolveType cxt)
      e' <- wellFormedExpr cxt e
      p' <- wellFormedPattern cxt p
      map (E.Decl p' e' : _) <$> wellFormedQualifiers (cxt `extendCxt` constMap true (bv p)) gs body

-- Keyword arguments in field order; must cover fields after first n exactly.
positionaliseKw :: forall b. ClassEntry -> Name -> Int -> List (Bind b) -> Either String (List b)
positionaliseKw cls c n xbs = do
   let remaining = drop n (fields cls)
   let provided = fst <$> xbs
   when (sort provided /= sort remaining) $ throwError $
      "Class " <> NEL.last c <> " keyword fields mismatch: expected " <> show remaining <> ", got " <> show provided
   pure $ remaining <#> \f -> definitely "keyword argument for field" (snd <$> find (\(k ↦ _) -> k == f) xbs)

-- Parameter names for desugared functions, kept apart from source identifiers by the leading $.
param :: Int -> Var
param i = "$" <> show i

-- Clauses over k parameters as a function of k parameters. A parameter column that is the same variable in
-- every clause is a parameter of that name; the remaining columns are matched together, as nested pairs when
-- there are several.
clauses :: NEL.NonEmptyList (List (S.Pattern × Maybe T.Type) × Maybe T.Type × E.Stmt) -> Either String E.Def
clauses cs = do
   let n = length (fst (NEL.head cs)) :: Int
   for_ cs \(ps × _) ->
      when (length ps /= n) $ throwError "Clauses differ in number of parameters"
   ψs <- traverse (signature "parameter annotations" <<< nonEmpty) (transpose (NEL.toList (cs <#> \(ps × _) -> snd <$> ps)))
   ψ <- signature "return annotation" (cs <#> \(_ × ψ × _) -> ψ)
   let
      columns = transpose (NEL.toList (cs <#> \(ps × _) -> fst <$> ps))
      named = columns # mapWithIndex \i ps -> case sharedVar ps of
         Just x -> x × Nothing
         Nothing -> param (i + 1) × Just ps
      matched = named # mapMaybe \(x × ps_opt) -> (x × _) <$> ps_opt
      ss = cs <#> \(_ × _ × s) -> s
      body = case matched of
         Nil -> NEL.head ss
         _ ->
            let
               e = foldr1 (\e1 e2 -> E.Constr cPair (e1 : e2 : Nil)) (E.Var <<< fst <$> nonEmpty matched)
               bs = NEL.zipWith (\ps s -> foldr1 (\p p' -> S.PConstr cPair (p : p' : Nil) Nil) (nonEmpty ps) × s)
                  (nonEmpty (transpose (snd <$> matched)))
                  ss
            in
               E.Match e bs
   pure (E.Def (zipWith E.Param (fst <$> named) ψs) ψ body)
   where
   sharedVar :: List S.Pattern -> Maybe Var
   sharedVar (S.PVar x : ps) | all (_ == S.PVar x) ps = Just x
   sharedVar _ = Nothing

   signature :: String -> NEL.NonEmptyList (Maybe T.Type) -> Either String (Maybe T.Type)
   signature what ψs
      | all (\ψ -> ψ == Nothing || ψ == NEL.head ψs) (NEL.tail ψs) = pure (NEL.head ψs)
      | otherwise = throwError ("Clauses differ in " <> what)

var :: Cxt -> Var -> Either String Unit
var cxt x = case Map.lookup x cxt of
   Just (VarStatus true) -> pure unit
   Just (VarStatus false) -> throwError $ "Not definitely assigned: " <> x
   Just (Mod q) -> throwError $ "module " <> dottedName q <> " is not a value"
   Just (ModLoaded q _) -> throwError $ "module " <> dottedName q <> " is not a value"
   Just (Class _) -> throwError $ "class " <> x <> " is not a value"
   Just PredefName -> throwError $ "predefined name " <> x <> " is not a value"
   Nothing -> throwError $ "Unbound name: " <> x

predefName :: Cxt -> Var -> Either String Unit
predefName cxt x = case Map.lookup x cxt of
   Just PredefName -> pure unit
   _ -> throwError $ "Not bound as a predefined name: " <> x

-- Case patterns well-formed as a list: each well-formed, and none subsumed by an earlier one.
wellFormedPatterns :: Cxt -> NEL.NonEmptyList S.Pattern -> Either String (NEL.NonEmptyList S.Pattern)
wellFormedPatterns cxt ps = forWithIndex ps \i p -> do
   forWithIndex_ (drop (i + 1) (NEL.toList ps)) \j p' ->
      when (subsumed cxt p' p) $ throwError $ "case " <> show (i + j + 2) <> " is unreachable"
   wellFormedPattern cxt p

wellFormedPattern :: Cxt -> S.Pattern -> Either String S.Pattern
wellFormedPattern cxt (S.PConstr c ps xps) = do
   cls <- classOf cxt c
   let fs = fields cls
   when (null xps && length ps /= length fs)
      $ throwError
      $ dottedName c <> " expects " <> show (length fs) <> " argument(s); got " <> show (length ps)
   distinctVars (ps <> (snd <$> xps))
   xps' <- if null xps then pure Nil else positionaliseKw cls c (length ps) xps
   S.PConstr cls.name <$> traverse (wellFormedPattern cxt) (ps <> xps') <@> Nil
wellFormedPattern cxt (S.PRecord xps) = do
   checkDistinct ("Duplicate key in pattern: " <> _) (fst <$> xps)
   distinctVars (snd <$> xps)
   S.PRecord <$> traverse (traverse (wellFormedPattern cxt)) xps
wellFormedPattern cxt (S.PList ps) = do
   distinctVars ps
   S.PList <$> traverse (wellFormedPattern cxt) ps
wellFormedPattern cxt (S.PAs p x) = do
   distinctVars (p : S.PVar x : Nil)
   S.PAs <$> wellFormedPattern cxt p <@> x
wellFormedPattern _ p = pure p

distinctVars :: List S.Pattern -> Either String Unit
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
subsumed cxt (S.PConstr c ps xps) (S.PConstr c' ps' xps') = fromMaybe false do
   cls <- hush (classOf cxt c)
   cls' <- hush (classOf cxt c')
   guard (cls'.name `elem` ancestors cls)
   pure $ all (\x -> fromMaybe false (subsumed cxt <$> fieldMap cls ps xps x <*> fieldMap cls' ps' xps' x)) (fields cls')
subsumed _ _ _ = false

