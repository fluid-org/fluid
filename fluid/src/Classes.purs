module Classes where

import Prelude hiding (absurd, join)
import Prim hiding (Type)

import Bind (Name, Var)
import Control.Alt ((<|>))
import Control.Monad.Error.Class (class MonadError)
import Control.Monad.Except.Trans (ExceptT)
import Control.Monad.Reader.Trans (ReaderT)
import Control.Monad.State.Trans (StateT)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Writer.Trans (WriterT)
import Data.Bifunctor (rmap)
import Data.Foldable (all, and, any, foldl, foldr, lookup) as F
import Data.List (List(..), elem, elemIndex, filter, filterM, index, length, nubEq, null, zipWith, (:))
import Data.List.NonEmpty (last) as NE
import Data.Map (Map, empty, singleton, unionWith)
import Data.Maybe (Maybe(..), maybe)
import Data.Set as Set
import Data.Traversable (sequence)
import Data.Tuple (fst)
import Effect.Exception (Error)
import Types (Primitive(..), Type(..), baseType, fv, subst, subterms)
import Types.Defs (cRange, int, never, object, str)
import Util (type (×), absurd, error, quoted, throw, (×), (∩))
import Util.Map (get, lookup)

type Ctr = String -- newtype would require more general Dict keys

type ClassEntry =
   { typeParams :: List Var
   , fields :: List (Var × Type) -- declared fields, distinct
   , base :: Maybe (Name × List Type)
   }

type ClassTable = Map Name ClassEntry

fields :: ClassTable -> Name -> List (Var × Type)
fields classes c = case def.base of
   Nothing -> def.fields
   Just (d × σs) -> (rmap (subst σs (get d classes).typeParams) <$> fields classes d) <> def.fields
   where
   def = get c classes

fieldNames :: ClassTable -> Name -> List Var
fieldNames classes c = fst <$> fields classes c

ancestors :: ClassTable -> Name -> List Name
ancestors classes c = c : maybe Nil (ancestors classes <<< fst) (get c classes).base

base :: ClassTable -> Name -> Maybe Type
base classes c = (get c classes).base <#> \(d × σs) -> ClassTy d σs

ancestorArgs :: ClassTable -> Name -> List Type -> Name -> List Type
ancestorArgs classes c τs d
   | c == d = τs
   | Just (ClassTy c' σs) <- subst τs (get c classes).typeParams <$> base classes c = ancestorArgs classes c' σs d
   | otherwise = error absurd

fieldsAt :: ClassTable -> Name -> List Type -> List (Var × Type)
fieldsAt classes c τs = rmap (subst τs (get c classes).typeParams) <$> fields classes c

data Instance = Instance (List Type) | Undetermined

instanceAt :: ClassTable -> Name -> Type -> Maybe Instance
instanceAt classes c τ = instanceAbove classes c τ <|> instanceBelow classes c τ

instanceAbove :: ClassTable -> Name -> Type -> Maybe Instance
instanceAbove classes c (ClassTy d τs) | c `elem` ancestors classes d = Just (Instance (ancestorArgs classes d τs c))
instanceAbove classes c (PrimitiveTy Never) = Just (monomorphic classes c)
instanceAbove _ _ _ = Nothing

-- Instance of c below τ; undetermined if instantiations below τ are not all equivalent
instanceBelow :: ClassTable -> Name -> Type -> Maybe Instance
instanceBelow classes c (ClassTy d σs) | d `elem` ancestors classes c =
   case filter solves candidates of
      Nil -> Nothing
      τs : τss
         | F.all (F.and <<< zipWith (equiv classes) τs) τss -> Just (Instance τs)
         | otherwise -> Just Undetermined
   where
   αs = (get c classes).typeParams
   ρs = ancestorArgs classes c (VarTy <$> αs) d
   atoms = nubEq (object : (σs >>= subterms))
   candidates = sequence (αs <#> \_ -> joins classes <$> subsets atoms)
   solves τs = F.and (zipWith (\ρ σ -> equiv classes (subst τs αs ρ) σ) ρs σs)
instanceBelow classes c (PrimitiveTy Object) = Just (monomorphic classes c)
instanceBelow _ _ _ = Nothing

-- Instance of c at object or Never, determined only if c has no type parameters
monomorphic :: ClassTable -> Name -> Instance
monomorphic classes c = if null (get c classes).typeParams then Instance Nil else Undetermined

subsets :: forall a. List a -> List (List a)
subsets = filterM (const (false : true : Nil))

class TypeArgs a where
   typeArgs :: ClassTable -> List Var -> a -> a -> Map Var Type

instance TypeArgs Type where
   typeArgs _ αs (VarTy α) τ | α `elem` αs = singleton α (baseType τ)
   typeArgs classes αs σ (UnionTy τ τ') = join classes (typeArgs classes αs σ τ) (typeArgs classes αs σ τ')
   typeArgs classes αs (ListTy σ) (ListTy τ) = typeArgs classes αs σ τ
   typeArgs classes αs (DictTy σ) (DictTy τ) = typeArgs classes αs σ τ
   typeArgs classes αs (TupleTy σs) (TupleTy τs) = typeArgs classes αs σs τs
   typeArgs classes αs (CallableTy σs σ) (CallableTy τs τ) = typeArgs classes αs (σ : σs) (τ : τs)
   typeArgs classes αs (TypeTy σ) (TypeTy τ) = typeArgs classes αs σ τ
   typeArgs classes αs (ClassTy c σs) τ = case instanceAt classes c τ of
      Just (Instance τs) -> typeArgs classes αs σs τs
      _ -> empty
   typeArgs classes αs (UnionTy σ σ') τ
      | F.any (\σ'' -> Set.isEmpty (fv σ'' ∩ Set.fromFoldable αs) && subtype classes τ σ'') [ σ, σ' ] = empty
      | otherwise = join classes (typeArgs classes αs σ τ) (typeArgs classes αs σ' τ)
   typeArgs _ _ _ _ = empty

instance TypeArgs a => TypeArgs (List a) where
   typeArgs classes αs σs τs = F.foldl (join classes) empty (zipWith (typeArgs classes αs) σs τs)

elemType :: ClassTable -> Type -> Maybe Type
elemType _ τ | baseType τ == str = Just str
elemType _ (ListTy σ) = Just σ
elemType _ (DictTy _) = Just str
elemType _ (ClassTy c Nil) | c == cRange = Just int
elemType classes (TupleTy τs) = Just (joins classes (baseType <$> τs))
elemType classes (UnionTy σ τ) = join classes <$> elemType classes σ <*> elemType classes τ
elemType _ _ = Nothing

fieldMap :: forall a. ClassTable -> Name -> List a -> List (Var × a) -> Var -> Maybe a
fieldMap classes c xs xys x = case elemIndex x (fst <$> fields classes c) of
   Just i | i < length xs -> index xs i
   _ -> F.lookup x xys

class HasClasses m where
   askClasses :: m ClassTable

instance (Monad m, HasClasses m) => HasClasses (StateT s m) where
   askClasses = lift askClasses

instance (Monad m, HasClasses m) => HasClasses (ReaderT r m) where
   askClasses = lift askClasses

instance (Monad m, HasClasses m) => HasClasses (ExceptT e m) where
   askClasses = lift askClasses

instance (Monad m, HasClasses m, Monoid w) => HasClasses (WriterT w m) where
   askClasses = lift askClasses

arity :: forall m. MonadError Error m => Name -> ClassTable -> m Int
arity c classes = case lookup c classes of
   Nothing -> throw $ "Unknown dataclass: " <> quoted (NE.last c)
   Just _ -> pure (length (fields classes c))

checkArity :: forall m. MonadError Error m => Name -> Int -> ClassTable -> m Unit
checkArity c n classes = do
   n' <- arity c classes
   when (n' /= n) $ throw $ quoted (NE.last c) <> " arity " <> show n' <> "; got " <> show n

subtype :: ClassTable -> Type -> Type -> Boolean
subtype classes σ τ
   | σ == τ = true
   | otherwise =
        case σ, τ of
           UnionTy σ1 σ2, _ -> subtype classes σ1 τ && subtype classes σ2 τ
           _, UnionTy τ1 τ2 -> subtype classes σ τ1 || subtype classes σ τ2
           PrimitiveTy Never, _ -> true
           _, PrimitiveTy Object -> true
           PrimitiveTy Int, PrimitiveTy Float -> true
           LitTy _, _ -> subtype classes (baseType σ) τ
           ClassTy c σs, ClassTy d τs | c == d -> F.and (zipWith (equiv classes) σs τs)
           ClassTy c σs, _ | Just σ' <- base classes c -> subtype classes (subst σs (get c classes).typeParams σ') τ
           _, PrimitiveTy Sized -> sized σ
           ListTy σ', ListTy τ' -> equiv classes σ' τ'
           DictTy σ', DictTy τ' -> equiv classes σ' τ'
           TypeTy σ', TypeTy τ' -> subtype classes σ' τ'
           TupleTy σs, TupleTy τs -> length σs == length τs && F.and (zipWith (subtype classes) σs τs)
           CallableTy σs σ', CallableTy τs τ' ->
              length σs == length τs && F.and (zipWith (subtype classes) τs σs) && subtype classes σ' τ'
           _, _ -> false
        where
        sized (ListTy _) = true
        sized (DictTy _) = true
        sized (PrimitiveTy Str) = true
        sized (TupleTy _) = true
        sized (ClassTy c Nil) = c == cRange
        sized _ = false

equiv :: ClassTable -> Type -> Type -> Boolean
equiv classes σ τ = subtype classes σ τ && subtype classes τ σ

comparable :: ClassTable -> Type -> Type -> Boolean
comparable classes σ τ = subtype classes σ τ || subtype classes τ σ

class Join a where
   join :: ClassTable -> a -> a -> a

instance Join Type where
   join classes σ τ
      | subtype classes σ τ = τ
      | subtype classes τ σ = σ
      | otherwise = UnionTy σ τ

instance (Ord k, Join a) => Join (Map k a) where
   join classes = unionWith (join classes)

joins :: ClassTable -> List Type -> Type
joins classes = F.foldr (join classes) never

meet :: ClassTable -> Type -> Type -> Type
meet classes σ τ
   | subtype classes σ τ = σ
   | subtype classes τ σ = τ
   | otherwise =
        case σ, τ of
           UnionTy σ1 σ2, _ -> join classes (meet classes σ1 τ) (meet classes σ2 τ)
           _, UnionTy τ1 τ2 -> join classes (meet classes σ τ1) (meet classes σ τ2)
           CallableTy σs σ', CallableTy τs τ' | length σs == length τs ->
              CallableTy (zipWith (join classes) σs τs) (meet classes σ' τ')
           TupleTy σs, TupleTy τs | length σs == length τs -> TupleTy (zipWith (meet classes) σs τs)
           _, _ -> never
