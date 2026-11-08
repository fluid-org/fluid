module Rules where

import Prelude

import Bind (Name, Var)
import Data.Foldable (class Foldable, foldMap)
import Data.List (List(..), (:))
import Data.Maybe (Maybe(..))
import Data.Traversable (class Traversable)
import Expr (Binop, Def, Expr, Qualifier, Unop)
import Literal (Literal)
import Util.Pair (Pair(..))


data Rule v a
   = Variable Var
   | Literal Literal
   | Binary Binop a a
   | Unary Unop a
   | AndShort a Expr
   | AndFull a a
   | OrShort a Expr
   | OrFull a a
   | CondTrue a a Expr
   | CondFalse a Expr a
   | ListLiteral (List a)
   | TupleLiteral (List a)
   --key/value premises in source order
   | DictLiteral (List (Pair a))
   --retain source key, value exprs and qualifiers list
   | DictComp Expr Expr (List Qualifier) (QualifierRun a (Pair a))
   --retain source syntax in case some bodies or qualifier suffixes never ran
   | ListComp Expr (List Qualifier) (QualifierRun a a)
   | Lambda Def
   | Application a (List a) a --function closure, args, callee
   | PartialApplication a (List a)
   | PrimitiveOp String a (List a)
   | ObjectConstructor Name (List a)
   | Subscript a a
   | Attribute Var a
   | ValueLeaf v

--comprehensions execute in two phases:
--1. qualifiers evaluate generator sources, guards and decls, producing a tree QualifierRun Deriv (Inputs s)
--        where type Inputs s = { ctrl :: Ctrl s, env :: Dict (GVal s) }
--2. evaluate the source body at each Yield, replacing each Inputs s with a Deriv

--q marks qualifier expression premises; b marks successful body positions
--Nothing means the generator pattern did not match

data QualifierRun q b
   = GeneratorRun q (List (Maybe (QualifierRun q b)))
   | GuardPassed q (QualifierRun q b)
   | GuardFailed q
   | DeclRun q (QualifierRun q b)
   | Yield b

--with q fixed, ordinary traversal visits only the body positions
derive instance Functor (QualifierRun q)
derive instance Foldable (QualifierRun q)
derive instance Traversable (QualifierRun q)


premises :: forall v a. Rule v a -> List a
premises = case _ of
   Variable _ -> Nil
   Literal _ -> Nil
   Binary _ left right -> left : right : Nil
   Unary _ operand -> operand : Nil
   AndShort left _ -> left : Nil
   AndFull left right -> left : right : Nil
   OrShort left _ -> left : Nil
   OrFull left right -> left : right : Nil
   CondTrue condition chosen _ -> condition : chosen : Nil
   CondFalse condition _ chosen -> condition : chosen : Nil
   ListLiteral children -> children
   TupleLiteral children -> children
   DictLiteral entries -> foldMap (\(Pair k v) -> k : v : Nil) entries
   DictComp _ _ _ run -> compQualifierPremises run <> foldMap (\(Pair key value) -> key : value : Nil) (compBodyPremises run)
   ListComp _ _ run -> compQualifierPremises run <> compBodyPremises run
   Lambda _ -> Nil
   Application fun args callee -> fun : (args <> (callee : Nil))
   PartialApplication fun args -> fun : args
   PrimitiveOp _ fun args -> fun : args
   ObjectConstructor _ args -> args
   Subscript container index -> container : index : Nil
   Attribute _ receiver -> receiver : Nil
   ValueLeaf _ -> Nil

--TWO PHASE LISTCOMP COLLECION TO MAINTAIN EXECUTION ORDER

--phase 1: collect generator-source and guard references, skipping bodies
compQualifierPremises :: forall q b. QualifierRun q b -> List q
compQualifierPremises = case _ of
   GeneratorRun source branches -> source : foldMap branchPremises branches
   GuardPassed condition rest -> condition : compQualifierPremises rest
   GuardFailed condition -> condition : Nil
   DeclRun value rest -> value : compQualifierPremises rest
   Yield _ -> Nil
   where
   branchPremises :: Maybe (QualifierRun q b) -> List q
   branchPremises Nothing = Nil
   branchPremises (Just run) = compQualifierPremises run

--phase 2: collect successful bodies, skipping qualifiers
compBodyPremises :: forall q b. QualifierRun q b -> List b
compBodyPremises = case _ of
   GeneratorRun _ branches -> foldMap branchPremises branches
   GuardPassed _ rest -> compBodyPremises rest
   GuardFailed _ -> Nil
   DeclRun _ rest -> compBodyPremises rest
   Yield body -> body : Nil
   where
   branchPremises :: Maybe (QualifierRun q b) -> List b
   branchPremises Nothing = Nil
   branchPremises (Just run) = compBodyPremises run


valueRule :: forall v a. v -> Rule v a
valueRule = ValueLeaf
