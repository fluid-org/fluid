module WellFormed where

import Prelude

import Bind (Name, Var, dottedName, prefixOf, properPrefixOf)
import Control.Monad.Error.Class (throwError)
import Control.Monad.State (StateT, get, mapStateT, modify_, runStateT)
import Control.Monad.Trans.Class (lift)
import Data.Bifunctor (lmap)
import Data.Either (Either, hush)
import Control.MonadPlus (guard)
import Data.Foldable (all, elem, foldM, foldr, for_, intercalate, traverse_)
import Data.Function (on)
import Data.FoldableWithIndex (forWithIndex_)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe, maybe)
import Data.List (List(..), length, mapMaybe, nub, zip, (:))
import Data.Foldable (lookup) as F
import DataType (cCons, cNil)
import ModuleGraph (ModuleName, builtins, predefinedDeps)
import Data.List.NonEmpty as NEL
import Data.Semigroup.Foldable (foldl1)
import Data.Set (Set, unions)
import Data.Set as Set
import Data.Traversable (traverse)
import Data.Tuple (fst, snd)
import DefiniteAssignment (ClassEntry, VarCxt, Entry(..), Cxt, WfResult(..), classFor, erase, extendCxt, extendCxtWith, fields, mergeRes, overrideRes)
import Util.Map (constMap)
import Expr (bv, fv)
import Expr (Pattern(..)) as S
import Lattice (Raw)
import SExpr (Clause(..), DictEntry(..), Expr(..), Import(..), LambdaClause(..), ListRest(..), Module(..), ParagraphElem(..), Qualifier(..), Stmt(..), VarDef(..)) as S
import Util (type (×), firstDuplicate, singleton, whenever, (×), (∩))
import Util.Set ((\\), (∪))

-- Member context of a loaded module and its checked body. The program is
-- recorded too, under __main__, with no body: it is checked separately and
-- may return, so it has no S.Module. The table memoises the load judgement.
type LoadedModule = { cxt :: Cxt, mod :: Maybe (S.Module (WfResult VarCxt)) }

type LoadM = StateT (Map.Map ModuleName LoadedModule) (Either String)

-- Load each module on demand as its import is checked. The recursion has no
-- cycle guard; it terminates because the dependency graph is acyclic.
checkProgram
   :: Map.Map ModuleName (Raw S.Module)
   -> Cxt
   -> List S.Import
   -> Raw S.Stmt
   -> Either String { cxt :: VarCxt, s :: S.Stmt (WfResult VarCxt), loaded :: Map.Map ModuleName LoadedModule }
checkProgram mods nativeBuiltins imports s =
   runStateT program Map.empty <#> \((cxt × s') × loaded) -> { cxt, s: s', loaded }
   where
   program :: LoadM (VarCxt × S.Stmt (WfResult VarCxt))
   program = do
      _ × cxt_imp <- checkImports mainModule imports
      -- Unlike a module (checkStatements), the program may return: a top-level return yields
      -- its result value. The spec forbids this, treating __main__ as a module; Fluid does not.
      _ × s' <- lift (wellFormed mainModule (Map.insert "__name__" (VarStatus true) cxt_imp) s)
      λ <- lift (classes mainModule s)
      modify_ (Map.insert mainModule { cxt: Class <$> λ, mod: Nothing })
      pure (Map.insert "__name__" true (erase cxt_imp) × s')

   -- Member context of module q; memoised.
   loadModule :: ModuleName -> LoadM Cxt
   loadModule q = get >>= \loaded -> case Map.lookup q loaded of
      Just { cxt } -> pure cxt
      Nothing -> mapStateT (lmap (_ <> "\nChecking module " <> dottedName q)) do
         mod@(S.Module is _) <- maybe (throwError ("Module not parsed: " <> dottedName q)) pure (Map.lookup q mods)
         importCxt × cxt_imp <- checkImports q is
         δ × mod' <- lift (checkStatements q cxt_imp mod)
         λ <- lift (classesOfModule q mod)
         let subs = submodules (Map.keys mods) q
         let clash = (Map.keys importCxt ∪ Map.keys δ ∪ Map.keys λ) ∩ Map.keys subs
         when (not Set.isEmpty clash)
            $ throwError
            $ "Submodule name clash in module " <> dottedName q <> ": " <> intercalate ", " (Set.toUnfoldable clash :: List Var)
         when (q == builtins) do
            let nativeClash = Map.keys nativeBuiltins ∩ (Map.keys δ ∪ Map.keys λ ∪ Map.keys subs)
            when (not (Set.isEmpty nativeClash))
               $ throwError
               $ "builtins' primitives clash with its source members: " <> intercalate ", " (Set.toUnfoldable nativeClash :: List Var)
         let
            cxt = (if q == builtins then nativeBuiltins else Map.empty) `Map.union` subs `Map.union` (Class <$> λ) `Map.union`
               (VarStatus <$> δ)
         modify_ (Map.insert q { cxt, mod: Just mod' })
         pure cxt

   checkImports :: ModuleName -> List S.Import -> LoadM (Cxt × Cxt)
   checkImports enclosing is = do
      predefinedCxt <- foldM (\acc q -> (acc `Map.union` _) <$> loadModule q) Map.empty (predefinedDeps enclosing)
      importCxt <- foldM (\acc i -> (acc `extendCxtWith` _) <$> importBindings enclosing i) Map.empty is
      pure (importCxt × (predefinedCxt `extendCxtWith` importCxt))

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

classesOfModule :: forall a. Name -> S.Module a -> Either String (Map.Map Var ClassEntry)
classesOfModule q (S.Module _ ss) =
   case foldr (\s acc -> Just (maybe s (S.Seq s) acc)) Nothing ss of
      Nothing -> pure Map.empty
      Just s -> classes q s

checkStatements :: Name -> Cxt -> Raw S.Module -> Either String (VarCxt × S.Module (WfResult VarCxt))
checkStatements q cxt_imp (S.Module imports ss) =
   case foldr (\s acc -> Just (maybe s (S.Seq s) acc)) Nothing ss of
      Nothing -> pure (Map.singleton "__name__" true × S.Module imports Nil)
      Just s -> do
         r × s' <- wellFormed q (Map.insert "__name__" (VarStatus true) cxt_imp) s
         case r of
            Returns -> throwError "Module body cannot return"
            Assigns δ -> pure (Map.insert "__name__" true δ × S.Module imports (unSeq s'))
   where
   unSeq (S.Seq s1 s2) = s1 : unSeq s2
   unSeq s = s : Nil

-- Entry program's module (spec entry point E; its __name__ is "__main__").
mainModule :: Name
mainModule = pure "__main__"

classes :: forall a. Name -> S.Stmt a -> Either String (Map.Map Var ClassEntry)
classes q = go Map.empty
   where
   go acc (S.Dataclass c b xs)
      | Map.member c acc = throwError $ "Duplicate class declaration: " <> c
      | otherwise = pure (Map.insert c { cxt: Class <$> acc, name: NEL.snoc q c, base: b, fields: xs } acc)
   go acc (S.Seq s1 s2) = go acc s1 >>= \acc' -> go acc' s2
   go acc _ = pure acc

assigns :: forall a. S.Stmt a -> Set Var
assigns S.Pass = Set.empty
assigns (S.Def (S.VarDef p _)) = bv p
assigns (S.ExprStmt _) = Set.empty
assigns (S.Assert _ _) = Set.empty
assigns (S.Return _) = Set.empty
assigns (S.If es s) = unions (assigns <$> (snd <$> es)) ∪ maybe Set.empty assigns s
assigns (S.Match _ ps) = unions (assigns <$> (snd <$> ps))
assigns (S.DefRec ds) = unions (Set.singleton <<< fst <$> ds)
assigns (S.Seq s1 s2) = assigns s1 ∪ assigns s2
assigns (S.Dataclass c _ _) = Set.singleton c

captures :: forall a. S.Stmt a -> Set Var
captures S.Pass = Set.empty
captures (S.Def (S.VarDef _ e)) = capturesE e
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
   clauseCaptures (_ × S.Clause _ (ps × s)) =
      (fv s \\ unions (bv <$> ps)) \\ assigns s
captures (S.Seq s1 s2) = captures s1 ∪ captures s2
captures (S.Dataclass _ _ _) = Set.empty

capturesE :: forall a. S.Expr a -> Set Var
capturesE (S.Var _) = Set.empty
capturesE (S.Op _) = Set.empty
capturesE (S.Int _ _) = Set.empty
capturesE (S.Float _ _) = Set.empty
capturesE (S.Str _ _) = Set.empty
capturesE (S.Constr _ _ es xes) = unions (capturesE <$> es) ∪ unions ((capturesE <<< snd) <$> xes)
capturesE (S.Dictionary _ es) =
   unions ((\(k × v) -> capturesEntry k ∪ capturesE v) <$> es)
   where
   capturesEntry (S.ExprKey e) = capturesE e
   capturesEntry (S.VarKey _ _) = Set.empty
capturesE (S.Matrix _ e (x × y) e') =
   (capturesE e \\ (Set.singleton x ∪ Set.singleton y)) ∪ capturesE e'
capturesE (S.Lambda (S.LambdaClause (ps × e))) =
   fv e \\ unions (bv <$> ps)
capturesE (S.Attribute e _) = capturesE e
capturesE (S.ModMember _ _) = Set.empty
capturesE (S.Subscript e e') = capturesE e ∪ capturesE e'
capturesE (S.App e es) = capturesE e ∪ unions (capturesE <$> es)
capturesE (S.BinaryApp e _ e') = capturesE e ∪ capturesE e'
capturesE (S.UnaryPrefixApp _ e) = capturesE e
capturesE (S.Ternary e e1 e2) = capturesE e ∪ capturesE e1 ∪ capturesE e2
capturesE (S.Paragraph es) = unions (capturesPe <$> es)
   where
   capturesPe (S.Token _) = Set.empty
   capturesPe (S.Unquote e) = capturesE e
capturesE (S.ListEmpty _) = Set.empty
capturesE (S.ListNonEmpty _ e l) = capturesE e ∪ capturesEListRest l
   where
   capturesEListRest (S.End _) = Set.empty
   capturesEListRest (S.Next _ e' l') = capturesE e' ∪ capturesEListRest l'
capturesE (S.ListEnum e1 e2) = capturesE e1 ∪ capturesE e2
capturesE (S.ListComp _ e _) = capturesE e
capturesE (S.DocExpr e e') = capturesE e ∪ capturesE e'

wellFormed :: forall a. Name -> Cxt -> S.Stmt a -> Either String (WfResult VarCxt × S.Stmt (WfResult VarCxt))
wellFormed _ _ S.Pass = pure (Assigns Map.empty × S.Pass)
wellFormed _ cxt (S.Return e) = do
   e' <- wellFormedExpr cxt e
   pure (Returns × S.Return (Assigns Map.empty <$ e'))
wellFormed _ cxt (S.ExprStmt e) = do
   e' <- wellFormedExpr cxt e
   pure (Assigns Map.empty × S.ExprStmt (Assigns Map.empty <$ e'))
wellFormed _ cxt (S.Assert e e') = do
   e1 <- wellFormedExpr cxt e
   e2 <- traverse (wellFormedExpr cxt) e'
   pure (Assigns Map.empty × S.Assert (Assigns Map.empty <$ e1) ((Assigns Map.empty <$ _) <$> e2))
wellFormed _ cxt (S.Def (S.VarDef p e)) = do
   let xs = bv p
   for_ (Set.toUnfoldable (xs `Set.intersection` capturesE e) :: Array Var) \x ->
      throwError $ "Variable captured by its own definition: " <> x
   e' <- wellFormedExpr cxt e
   p' <- qualifyPattern cxt p
   pure (Assigns (constMap true xs) × S.Def (S.VarDef p' (Assigns Map.empty <$ e')))
wellFormed q cxt (S.DefRec ds) = do
   let fs = unions (Set.singleton <<< fst <$> ds)
   let cxt' = cxt `extendCxt` constMap true fs
   for_ (NEL.groupBy (eq `on` fst) ds) \clauses ->
      wellFormedPatterns cxt' (clauses <#> \(_ × S.Clause _ (ps × _)) -> S.PList ps)
   ds' <- traverse
      ( \(x × S.Clause _ (ps × s)) -> do
           let xs = unions (bv <$> ps)
           let ys = assigns s \\ xs
           let cxt'' = cxt' `extendCxt` constMap true xs `extendCxt` constMap false ys
           ps' <- traverse (qualifyPattern cxt') ps
           r × s' <- wellFormed q cxt'' s
           pure (x × S.Clause r (ps' × s'))
      )
      ds
   pure (Assigns (constMap true fs) × S.DefRec ds')
wellFormed q cxt (S.Seq s1 s2) = do
   r1 × s1' <- wellFormed q cxt s1
   case r1 of
      Returns -> throwError "Unreachable statement"
      Assigns δ -> do
         for_ (Set.toUnfoldable (captures s1 `Set.intersection` assigns s2) :: Array Var) \x ->
            throwError $ "Captured variable reassigned: " <> x
         λ1 <- classes q s1
         let cxt' = Map.union (Class <$> (λ1 <#> _ { cxt = cxt })) (cxt `extendCxt` δ)
         r2 × s2' <- wellFormed q cxt' s2
         pure (overrideRes r1 r2 × S.Seq s1' s2')
wellFormed q cxt (S.If es elseBranch) = do
   es' <- traverse
      ( \(e × s) -> do
           e' <- wellFormedExpr cxt e
           r × s' <- wellFormed q cxt s
           pure (r × ((Assigns Map.empty <$ e') × s'))
      )
      es
   rElse × elseBranch' <- case elseBranch of
      Just s -> map Just <$> wellFormed q cxt s
      Nothing -> pure (Assigns Map.empty × Nothing)
   pure (foldl1 mergeRes (NEL.cons rElse (fst <$> es')) × S.If (snd <$> es') elseBranch')
wellFormed q cxt (S.Match e ps) = do
   e' <- wellFormedExpr cxt e
   wellFormedPatterns cxt (fst <$> ps)
   ps' <- traverse
      ( \(p × s) -> do
           let xs = bv p
           p' <- qualifyPattern cxt p
           r × s' <- wellFormed q (cxt `extendCxt` constMap true xs) s
           pure (overrideRes (Assigns (constMap true xs)) r × (p' × s'))
      )
      ps
   pure (foldl1 mergeRes ((fst <$> ps') `NEL.snoc` rFall) × S.Match (Assigns Map.empty <$ e') (snd <$> ps'))
   where
   rFall = case fst (NEL.last ps) of
      S.PVar _ -> Returns
      S.PWild -> Returns
      _ -> Assigns Map.empty
wellFormed q cxt (S.Dataclass c b xs) = do
   when (length (nub xs) /= length xs) $ throwError $ "Duplicate field names in class: " <> c
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
   pure (Assigns Map.empty × S.Dataclass c b xs)

asName :: forall a. S.Expr a -> Maybe Name
asName (S.Var x) = Just (singleton x)
asName (S.Attribute e y) = asName e <#> (_ <> singleton y)
asName _ = Nothing

classOf :: Cxt -> Name -> Either String ClassEntry
classOf cxt c = case resolveName cxt c of
   Just (Class cls) -> pure cls
   _ -> throwError $ "Unknown dataclass: " <> dottedName c

resolveName :: Cxt -> Name -> Maybe Entry
resolveName cxt name = case NEL.fromList init of
   Nothing -> simpleEntry cxt x
   Just q -> case resolveName cxt q of
      Just (ModLoaded _ cxt') -> simpleEntry cxt' x
      _ -> Nothing
   where
   { init, last: x } = NEL.unsnoc name
   simpleEntry g y = case Map.lookup y g of
      Just e@(VarStatus true) -> Just e
      Just e@(ModLoaded _ _) -> Just e
      Just e@(Class _) -> Just e
      _ -> Nothing

-- Validate an expression; rewrite constructor names to fully-qualified form and
-- module projections to ModMember.
wellFormedExpr :: forall a. Cxt -> S.Expr a -> Either String (S.Expr a)
wellFormedExpr = wf
   where
   wf :: Cxt -> S.Expr a -> Either String (S.Expr a)
   wf cxt e@(S.Var x) = e <$ var cxt x
   wf cxt e@(S.Op op) = e <$ var cxt op
   wf _ e@(S.Int _ _) = pure e
   wf _ e@(S.Float _ _) = pure e
   wf _ e@(S.Str _ _) = pure e
   wf cxt (S.Constr α c es Nil) = do
      cls <- classOf cxt c
      let fs = fields cls
      when (length es /= length fs)
         $ throwError
         $ dottedName c <> " expects " <> show (length fs) <> " argument(s); got " <> show (length es)
      (\es' -> S.Constr α (qualified cls c) es' Nil) <$> traverse (wf cxt) es
   wf cxt (S.Constr α c es xes) = do
      cls <- classOf cxt c
      S.Constr α (qualified cls c) <$> traverse (wf cxt) es <*> traverse (\(x × e) -> (x × _) <$> wf cxt e) xes
   wf cxt (S.App e es) = S.App <$> wf cxt e <*> traverse (wf cxt) es
   wf cxt (S.BinaryApp e op e') = S.BinaryApp <$> wf cxt e <*> (op <$ var cxt op) <*> wf cxt e'
   wf cxt (S.UnaryPrefixApp op e) = var cxt op *> (S.UnaryPrefixApp op <$> wf cxt e)
   wf cxt (S.Ternary c e e') = S.Ternary <$> wf cxt c <*> wf cxt e <*> wf cxt e'
   wf cxt (S.Attribute e y) = case resolveName cxt =<< asName e of
      Just (ModLoaded q cxt') -> do
         when (not (Map.member y cxt'))
            $ throwError
            $ "module " <> dottedName q <> " has no member " <> y
         pure (S.ModMember q y)
      _ -> flip S.Attribute y <$> wf cxt e
   wf _ e@(S.ModMember _ _) = pure e
   wf cxt (S.Subscript e e') = S.Subscript <$> wf cxt e <*> wf cxt e'
   wf cxt (S.Matrix α body (x × y) source) =
      (\source' body' -> S.Matrix α body' (x × y) source') <$> wf cxt source <*> wf
         (cxt `extendCxt` constMap true (Set.singleton x ∪ Set.singleton y))
         body
   wf cxt (S.Lambda (S.LambdaClause (ps × e))) = do
      ps' <- traverse (qualifyPattern cxt) ps
      e' <- wf (cxt `extendCxt` constMap true (unions (bv <$> ps))) e
      pure (S.Lambda (S.LambdaClause (ps' × e')))
   wf cxt (S.Dictionary α kvs) = S.Dictionary α <$> traverse (\(k × v) -> (×) <$> dictKey k <*> wf cxt v) kvs
      where
      dictKey (S.ExprKey e) = S.ExprKey <$> wf cxt e
      dictKey k@(S.VarKey _ _) = pure k
   wf cxt (S.Paragraph elems) = S.Paragraph <$> traverse pe elems
      where
      pe (S.Unquote e) = S.Unquote <$> wf cxt e
      pe t@(S.Token _) = pure t
   wf _ e@(S.ListEmpty _) = pure e
   wf cxt (S.ListNonEmpty α e l) = S.ListNonEmpty α <$> wf cxt e <*> listRest l
      where
      listRest l'@(S.End _) = pure l'
      listRest (S.Next α' e' l') = S.Next α' <$> wf cxt e' <*> listRest l'
   wf cxt (S.ListEnum e e') = S.ListEnum <$> wf cxt e <*> wf cxt e'
   wf cxt (S.ListComp α e quals) = (\(e' × quals') -> S.ListComp α e' quals') <$> qualifiers cxt quals
      where
      qualifiers cxt' Nil = (_ × Nil) <$> wf cxt' e
      qualifiers cxt' (q : qs) = case q of
         S.ListCompGuard cond -> do
            cond' <- wf cxt' cond
            map (S.ListCompGuard cond' : _) <$> qualifiers cxt' qs
         S.ListCompGen p src -> do
            src' <- wf cxt' src
            p' <- qualifyPattern cxt' p
            map (S.ListCompGen p' src' : _) <$> qualifiers (cxt' `extendCxt` constMap true (bv p)) qs
         S.ListCompDecl (S.VarDef p src) -> do
            src' <- wf cxt' src
            p' <- qualifyPattern cxt' p
            map (S.ListCompDecl (S.VarDef p' src') : _) <$> qualifiers (cxt' `extendCxt` constMap true (bv p)) qs
   wf cxt (S.DocExpr e e') = S.DocExpr <$> wf cxt e <*> wf cxt e'

   qualified cls _ = cls.name

var :: Cxt -> Var -> Either String Unit
var cxt x = case Map.lookup x cxt of
   Just (VarStatus true) -> pure unit
   Just (VarStatus false) -> throwError $ "Not definitely assigned: " <> x
   Just (Mod q) -> throwError $ "module " <> dottedName q <> " is not a value"
   Just (ModLoaded q _) -> throwError $ "module " <> dottedName q <> " is not a value"
   Just (Class _) -> throwError $ "class " <> x <> " is not a value"
   Nothing -> throwError $ "Unbound name: " <> x

-- Case patterns well-formed as a list: each well-formed, and none subsumed by an earlier one.
wellFormedPatterns :: Cxt -> NEL.NonEmptyList S.Pattern -> Either String Unit
wellFormedPatterns cxt = go 1 <<< NEL.toList
   where
   go :: Int -> List S.Pattern -> Either String Unit
   go _ Nil = pure unit
   go i (p : ps) = do
      wellFormedPattern p
      forWithIndex_ ps \j p' ->
         when (subsumed cxt p' p) $ throwError $ "case " <> show (i + j + 1) <> " is unreachable"
      go (i + 1) ps

-- Sub-patterns well-formed, with pairwise disjoint variables; dictionary keys distinct.
wellFormedPattern :: S.Pattern -> Either String Unit
wellFormedPattern p = do
   case p of
      S.PRecord xps -> for_ (firstDuplicate (fst <$> xps)) \w -> throwError $ "Duplicate key in pattern: " <> w
      _ -> pure unit
   traverse_ wellFormedPattern ps
   for_ (firstDuplicate (ps >>= Set.toUnfoldable <<< bv)) \x -> throwError $ "Duplicate variable in pattern: " <> x
   where
   ps = case p of
      S.PConstr _ ps' xps -> ps' <> (snd <$> xps)
      S.PRecord xps -> snd <$> xps
      S.PList ps' -> ps'
      S.PAs p' x -> p' : S.PVar x : Nil
      _ -> Nil

-- p subsumed by p': every value p matches, p' matches. List patterns as Nil and Cons patterns.
subsumed :: Cxt -> S.Pattern -> S.Pattern -> Boolean
subsumed _ _ (S.PVar _) = true
subsumed _ _ S.PWild = true
subsumed cxt (S.PAs p _) p' = subsumed cxt p p'
subsumed cxt p (S.PAs p' _) = subsumed cxt p p'
subsumed _ (S.PInt n) (S.PInt n') = n == n'
subsumed _ (S.PFloat x) (S.PFloat x') = x == x'
subsumed _ (S.PStr s) (S.PStr s') = s == s'
subsumed cxt (S.PRecord xps) (S.PRecord uqs) =
   all (\(u × q) -> maybe false (\p -> subsumed cxt p q) (F.lookup u xps)) uqs
subsumed cxt p p' = case asConstr p, asConstr p' of
   Just (c × ps × xps), Just (c' × qs × xqs) -> fromMaybe false do
      cls <- hush (classOf cxt c)
      cls' <- hush (classOf cxt c')
      guard (cls'.name `elem` ancestors cls)
      fm <- fieldMap cls ps xps
      fm' <- fieldMap cls' qs xqs
      pure $ all (\x -> fromMaybe false (subsumed cxt <$> Map.lookup x fm <*> Map.lookup x fm')) (fields cls')
   _, _ -> false
   where
   ancestors :: ClassEntry -> List Name
   ancestors cls = cls.name : maybe Nil ancestors (cls.base >>= classFor cls.cxt)

   -- Field to sub-pattern, positional then keyword; undefined if the arguments don't fit the class.
   fieldMap :: ClassEntry -> List S.Pattern -> List (Var × S.Pattern) -> Maybe (Map.Map Var S.Pattern)
   fieldMap cls ps xps = do
      let fs = fields cls
      guard (length ps <= length fs)
      let positional = Map.fromFoldable (zip fs ps)
      foldM (\m (x × q) -> whenever (x `elem` fs && not (Map.member x m)) (Map.insert x q m)) positional xps

-- Constructor view of a pattern, with list patterns as Nil and Cons.
asConstr :: S.Pattern -> Maybe (Name × List S.Pattern × List (Var × S.Pattern))
asConstr (S.PConstr c ps xps) = Just (c × ps × xps)
asConstr (S.PList Nil) = Just (singleton (NEL.last cNil) × Nil × Nil)
asConstr (S.PList (p : ps)) = Just (singleton (NEL.last cCons) × (p : S.PList ps : Nil) × Nil)
asConstr _ = Nothing

qualifyPattern :: Cxt -> S.Pattern -> Either String S.Pattern
qualifyPattern cxt = qualify
   where
   qualify (S.PConstr c ps xps) = do
      fqn <- fqnOf c
      S.PConstr fqn <$> traverse qualify ps <*> traverse (traverse qualify) xps
   qualify (S.PRecord xps) = S.PRecord <$> traverse (traverse qualify) xps
   qualify (S.PList ps) = S.PList <$> traverse qualify ps
   qualify (S.PAs p x) = S.PAs <$> qualify p <@> x
   qualify p = pure p
   fqnOf c = _.name <$> classOf cxt c

