{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveDataTypeable #-}
module OdLang.Type.Solver where

import Control.Applicative
import Control.Monad
import Control.Monad.State
import Data.Bifunctor
import Data.Bifoldable
import Data.Bitraversable
import Data.Bifunctor.TH
import Data.Data
import Data.Function
import Data.Functor.Classes
import Data.Eq.Deriving
import Data.Either
import Data.IntMap qualified as M
import Data.List
import Data.Maybe
import Text.Show.Deriving

import Debug.Trace

type Pred = String

data Inc var = B Int | F var deriving (Eq, Show, Typeable, Data)

deriving instance Functor Inc
deriving instance Foldable Inc
deriving instance Traversable Inc

type Scope term var = term (Inc var)

data TypeF scope ty where
  TAbsF :: scope -> TypeF scope ty
  (:->>) :: ty -> ty -> TypeF scope ty
  TAppF :: ty -> [ty] -> TypeF scope ty
  TUnitF :: TypeF scope ty

infixr 6 :->>

deriving instance Typeable TypeF
deriving instance (Data scope, Data ty) => Data (TypeF scope ty)
deriving instance (Eq b, Eq a) => Eq (TypeF b a)
deriving instance (Show b, Show a) => Show (TypeF b a)
deriving instance Functor (TypeF b)
deriving instance Foldable (TypeF b)
deriving instance Traversable (TypeF b)
$(deriveBifunctor ''TypeF)
$(deriveBifoldable ''TypeF)
$(deriveBitraversable ''TypeF)
instance Show a => Show1 (TypeF a) where liftShowsPrec = $(makeLiftShowsPrec ''TypeF)
instance Show2 TypeF where liftShowsPrec2 = $(makeLiftShowsPrec2 ''TypeF)
instance Eq a => Eq1 (TypeF a) where liftEq = $(makeLiftEq ''TypeF)
instance Eq2 TypeF where liftEq2 = $(makeLiftEq2 ''TypeF)

data Free term var
  = Pure var
  | Free (FreeS term var)

type FreeS term var = term (Scope (Free term) var) (Free term var)

deriving instance (Show var, Show2 term) => Show (Free term var)
deriving instance (Eq var, Eq2 term) => Eq (Free term var)
deriving instance Typeable Free
deriving instance (Typeable term, Data var, forall a b . (Data a, Data b) => Data (term a b)) => Data (Free term var)

instance Bifunctor term => Functor (Free term) where
  fmap = liftM

instance Bifunctor term => Applicative (Free term) where
  (<*>) = ap
  pure = return

instance Bifunctor term => Monad (Free term) where
  return = Pure
  Pure v >>= f = f v
  Free t >>= f = Free (bimap (>>= traverse f) (>>= f) t)

instance Bifoldable term => Foldable (Free term) where
  foldMap f (Pure v) = f v
  foldMap f (Free t) = bifoldMap (foldMap $ foldMap f) (foldMap f) t

instance Bitraversable term => Traversable (Free term) where
  traverse f (Pure v) = Pure <$> f v
  traverse f (Free t) = Free <$> bitraverse (traverse $ traverse f) (traverse f) t

type Type = Free TypeF

pattern TVar i = Pure i
pattern TAbs t = Free (TAbsF t)
pattern a :-> b = Free (a :->> b)
pattern TApp a b = Free (TAppF a b)
pattern TUnit = Free TUnitF

infixr 6 :->

data Constraint f var where
  CEq :: Free f var -> Free f var -> Constraint f var
  CPred :: Pred -> [Free f var] -> Constraint f var
  CImpl :: [Scope (Constraint f) var]
        -> Scope (Constraint f) var
        -> Constraint f var

deriving instance (Show var, Show2 f) => Show (Constraint f var)
deriving instance Bifunctor f => Functor (Constraint f)
deriving instance Bifoldable f => Foldable (Constraint f)
deriving instance Bitraversable f => Traversable (Constraint f)

substitute :: Bifunctor f => (var -> Free f var') -> Constraint f var -> Constraint f var'
substitute s (CEq t1 t2) = (t1 >>= s) `CEq` (t2 >>= s)
substitute s (CPred p t) = CPred p $ map (>>= s) t
substitute s (CImpl a c) =
  CImpl (map (substitute (traverse s)) a) (substitute (traverse s) c)

weaken :: Functor f => f var -> Scope f var
weaken = fmap F

contract :: Traversable f => Scope f var -> Maybe (f var)
contract = traverse \case
  B _ -> Nothing
  F v -> Just v

sameConstr :: Data a => a -> a -> Bool
sameConstr = (==) `on` toConstr

unroll :: (Bifoldable f)
       => FreeS f var
       -> [Either (Scope (Free f) var) (Free f var)]
unroll = bifoldr (\s l -> Left s : l) (\f l -> Right f : l) []

matches :: forall f var .
        ( forall v . Data v => Data (FreeS f v)
        , forall v . Eq v => Eq (Free f v)
        , Eq2 f
        , Bifunctor f, Bifoldable f, Bitraversable f
        , Eq var, Data var)
        => [Free f var] -> [Scope (Free f) var]
        -> Maybe (Inc var -> Free f var)
matches a b = fmap sub $ join $ fmap sequence $ combineList $ zipWith (matches' lvl) a b
  where
    matches' :: (Eq var', Data var') => (Inc var' -> Maybe Int) -> Free f var' -> Scope (Free f) var'
             -> Maybe (M.IntMap (Maybe (Free f var')))
    matches' lvl t (Pure (lvl -> Just i)) = Just $ M.singleton i (Just t)
    matches' lvl (Free t1) (Free t2)
      | toConstr t1 == toConstr t2 =
        let (s1, f1) = partitionEithers $ unroll t1
            (s2, f2) = partitionEithers $ unroll t2
            lvl' (F v) = lvl v
            lvl' _ = Nothing
         in combineList $ (fmap (fmap (>>= contract)) <$> zipWith (matches' lvl') s1 s2) ++ zipWith (matches' lvl) f1 f2
      | otherwise = Nothing
    matches' _ _ _ = Nothing

    lvl :: Inc var -> Maybe Int
    lvl (B i) = Just i
    lvl _ = Nothing

    combine :: Eq var' => M.IntMap (Maybe (Free f var')) -> M.IntMap (Maybe (Free f var'))
            -> M.IntMap (Maybe (Free f var'))
    combine = M.mergeWithKey (\_ a b -> if a == b then Just a else Just Nothing) id id

    combineList :: Eq var' => [Maybe (M.IntMap (Maybe (Free f var')))]
                -> Maybe (M.IntMap (Maybe (Free f var')))
    combineList = foldl' (liftM2 combine) (Just M.empty)

    sub m = \case
      B i -> m M.! i
      F v -> pure v

solve :: forall f var .
      ( forall v . Data v => Data (FreeS f v)
      , forall v . Eq v => Eq (Free f v)
      , Eq2 f, Show2 f
      , Bifunctor f, Bifoldable f, Bitraversable f
      , Eq var, Show var
      , Data var)
      => [Constraint f var] -> [Constraint f var]
      -> [Constraint f var]
solve assume consts = evalState (go assume consts []) False
  where
    subst x t i = if i == x then t else pure i

    genConstraints lhs rhs = zipWith constr (unroll lhs) (unroll rhs)

    constr (Left t1) (Left t2) = CImpl [] (CEq t1 t2)
    constr (Right t1) (Right t2) = CEq t1 t2

    go :: [Constraint f var] -> [Constraint f var] -> [Constraint f var]
       -> State Bool [Constraint f var]
    go assume [] cs = do
      continue <- get
      if continue
        then do
          put False
          go assume (reverse cs) []
        else
          pure cs

    go assume (c:cs) r =
      trace ("assumptions = " ++ show assume ++ "\nconstraints = " ++ show (reverse r ++ (c:cs))) $
      case c of
        CEq t1 t2 | t1 == t2 -> put True >> go assume cs r
        CEq (Pure a) t -> put True >> go assume (map (substitute (subst a t)) cs) (map (substitute (subst a t)) r)
        CEq t (Pure a) -> put True >> go assume (map (substitute (subst a t)) cs) (map (substitute (subst a t)) r)
        CEq (Free f1) (Free f2) | sameConstr f1 f2 -> put True >> go assume (genConstraints f1 f2 ++ cs) r
        CEq _ _ -> go assume cs (c:r)

        CPred p ts ->
          case [a | a@(CPred p' ts') <- assume
               , and $ zipWith (==) ts ts'
               , p == p', length ts == length ts'] of
            [_] -> put True >> go assume cs r
            _:_  -> error "Ambiguous assumptions"
            [] ->
              case [map (substitute m) a
                   | a `CImpl` (CPred p' ts') <- assume
                   , m <- maybeToList $ matches ts ts'
                   , p == p', length ts == length ts'] of
                [a] -> put True >> go assume (a ++ cs) r
                _:_ -> error "Ambiguous assumptions"
                [] -> go assume cs (c:r)

        CImpl a c -> let Just res = traverse contract $ solve (map weaken assume ++ a) [c]
                      in put True >> go assume (res ++ cs) r
