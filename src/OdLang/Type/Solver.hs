{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveDataTypeable #-}
module OdLang.Type.Solver where

import Control.Applicative
import Control.Monad
import Control.Monad.State
import Data.Bifunctor
import Data.Bifoldable
import Data.Bitraversable
import Data.Kind qualified as K
import Data.Function
import Data.Functor.Classes
import Data.Either
import Data.IntMap qualified as M
import Data.List (foldl')
import Data.Maybe
import Data.Void
import Language.Haskell.TH qualified as TH
import Language.Haskell.TH.Syntax qualified as TH

import OdLang.Type.Free

class Equational (t :: K.Type -> K.Type -> K.Type) where
  equal :: FreeS t var -> FreeS t var -> Maybe [Constraint t var]
  sameConstr :: FreeS t var -> FreeS t var' -> Bool

defaultEqual :: (Bitraversable t, Equational t)
             => FreeS t var -> FreeS t var -> Maybe [Constraint t var]
defaultEqual a b =
  if sameConstr a b
     then Just $ let (s1, t1) = partitionEithers $ unroll a
                     (s2, t2) = partitionEithers $ unroll b
                     sc a b = CImpl [] [CEq (withSkolems a) (withSkolems b)]
                     ty a b = CEq a b
                  in zipWith sc s1 s2 ++ zipWith ty t1 t2
     else Nothing

makeSameConstr :: TH.Name -> TH.Q TH.Exp
makeSameConstr name = do
  TH.TyConI (TH.DataD _ _ _ _ constrs _) <- TH.reify name
  let pats = concatMap f constrs
  [| \a b -> $(TH.caseE [| (a, b) |] (pats ++ [catchAll])) |]
    where
      f = \case
          TH.NormalC n _ -> [TH.match [p| ($(p), $(p)) |] (TH.NormalB <$> [| True |]) []]
            where p = TH.recP n []
          TH.InfixC _ n _ -> [TH.match [p| ($(p), $(p)) |] (TH.NormalB <$> [| True |]) []]
            where p = TH.infixP TH.wildP n TH.wildP
          TH.GadtC ns _ _ -> [ TH.match [p| ($(p), $(p)) |] (TH.NormalB <$> [| True |]) []
                             | n <- ns, let p = TH.recP n []]
          TH.ForallC _ _ con -> f con
          con -> fail ("makeSameConstr not implemented for constructors like " ++ TH.pprint con)
      catchAll = TH.match [p| _ |] (TH.NormalB <$> [| False |]) []

type Pred = String

newtype Skolem = Skolem Int deriving (Eq, Show)

type SkInc var = Either Skolem (Inc var)

type Skope term var = term (SkInc var)

data Constraint f var where
  CEq :: Free f var -> Free f var -> Constraint f var
  CPred :: Pred -> [Free f var] -> Constraint f var
  CImpl :: [Constraint f (Either Skolem var)]
        -> [Skope (Constraint f) var]
        -> Constraint f var

deriving instance (Show var, forall var . Show var => Show (Free f var)) => Show (Constraint f var)
deriving instance (Eq var, forall var . Eq var => Eq (Free f var)) => Eq (Constraint f var)
deriving instance Bifunctor f => Functor (Constraint f)
deriving instance Bifoldable f => Foldable (Constraint f)
deriving instance Bitraversable f => Traversable (Constraint f)

substitute :: Bifunctor f => (var -> Free f var') -> Constraint f var -> Constraint f var'
substitute s (CEq t1 t2) = (t1 >>= s) `CEq` (t2 >>= s)
substitute s (CPred p t) = CPred p $ map (>>= s) t
substitute s (CImpl a c) =
  CImpl (map (substitute (traverse s)) a)
        (map (substitute (traverse $ traverse s)) c)

weaken :: Functor f => f var -> Skope f var
weaken = fmap (Right . F)

contract :: Traversable f => Skope f var -> Maybe (f var)
contract = sequence . fmap \case
  Left _ -> Nothing
  Right (B _) -> Nothing
  Right (F v) -> Just v

contractT :: Traversable f => Scope f var -> Maybe (f var)
contractT = sequence . fmap \case
  B _ -> Nothing
  F v -> Just v

unroll :: Bifoldable f
       => FreeS f var
       -> [Either (Scope (Free f) var) (Free f var)]
unroll = bifoldr (\s l -> Left s : l) (\f l -> Right f : l) []

matches :: forall f var .
        ( forall v . Eq v => Eq (Free f v)
        , Bitraversable f, Equational f
        , Eq var)
        => [Free f var] -> [Free f (Either Skolem var)]
        -> Maybe (Either Skolem var -> Free f var)
matches a b = fmap sub $ join $ fmap sequence $ combineList $ zipWith (matches' lvl0) a b
  where
    matches' :: Eq var' => (var'' -> Either Int var') -> Free f var' -> Free f var''
             -> Maybe (M.IntMap (Maybe (Free f var')))
    matches' lvl t (Pure (lvl -> Left i)) = Just $ M.singleton i (Just t)
    matches' lvl (Pure v1) (Pure (lvl -> Right v2))
      | v1 == v2 = Just M.empty
    matches' lvl (Free t1) (Free t2)
      | sameConstr t1 t2 =
        let (s1, f1) = partitionEithers $ unroll t1
            (s2, f2) = partitionEithers $ unroll t2
            lvl' (F v) = second F $ lvl v
            lvl' (B i) = Right $ B i
            terms = zipWith (matches' lvl) f1 f2
            scopeds = zipWith (matches' lvl') s1 s2
         in combineList $ (fmap (fmap (>>= contractT)) <$> scopeds) ++ terms
    matches' _ _ _ = Nothing

    lvl0 :: Either Skolem var -> Either Int var
    lvl0 = first \case {Skolem i -> i}

    combine :: Eq var' => M.IntMap (Maybe (Free f var')) -> M.IntMap (Maybe (Free f var'))
            -> M.IntMap (Maybe (Free f var'))
    combine = M.mergeWithKey (\_ a b -> if a == b then Just a else Just Nothing) id id

    combineList :: Eq var' => [Maybe (M.IntMap (Maybe (Free f var')))]
                -> Maybe (M.IntMap (Maybe (Free f var')))
    combineList = foldl' (liftM2 combine) (Just M.empty)

    sub m = \case
      Left (Skolem i) -> m M.! i
      Right v -> pure v

ensureAssumption :: Bitraversable f => Skope (Constraint f) var -> Maybe (Constraint f (Either Skolem var))
ensureAssumption = sequence . fmap \case
                     Left sk -> Just $ Left sk
                     Right (F v) -> Just $ Right v
                     Right (B _) -> Nothing

fromAssumption :: Bifunctor f => Constraint f (Either Skolem var) -> Skope (Constraint f) var
fromAssumption = fmap (fmap F)

withSkolems :: Bifunctor f => Scope (Free f) var -> Skope (Free f) var
withSkolems = fmap \case
  B i -> Left $ Skolem i
  v   -> Right v

class Variable var where
  isUni :: var -> Bool
  isSkolem :: var -> Bool
  level :: var -> Int

instance Variable Void where
  isUni = absurd
  isSkolem = absurd
  level = absurd

instance Variable String where
  isUni = const False
  isSkolem = const False
  level = const 0

instance Variable var => Variable (Inc var) where
  isUni (B _) = True
  isUni (F v) = isUni v

  isSkolem (B _) = False
  isSkolem (F v) = isSkolem v

  level (B _) = 0
  level (F v) = 1 + level v

instance Variable var => Variable (Either Skolem var) where
  isUni (Left _) = False
  isUni (Right v) = isUni v

  isSkolem (Left _) = True
  isSkolem (Right v) = isSkolem v

  level (Left _) = 0
  level (Right v) = level v

solve :: forall f var .
      ( forall v . Eq v => Eq (Free f v)
      , forall v . Show v => Show (Free f v)
      , Eq2 f, Bitraversable f, Equational f
      , Eq var, Show var, Variable var)
      => [Constraint f var] -> [Constraint f var]
      -> [Constraint f var]
solve assume consts = evalState (go assume consts []) False
  where
    subst x t i = if i == x then t else pure i

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
      case c of
        CEq t1 t2 |  CEq t1 t2 `elem` assume
                  || CEq t2 t1 `elem` assume -> go assume cs r

        CEq t1 t2 | t1 == t2 -> go assume cs r
        CEq (Pure a) t | isUni a && level a <= maximum (fmap level t) && all (/= a) t
          -> put True >> go assume (map (substitute (subst a t)) cs) (map (substitute (subst a t)) r)
        CEq t (Pure a) | isUni a && level a <= maximum (fmap level t) && all (/= a) t
          -> put True >> go assume (map (substitute (subst a t)) cs) (map (substitute (subst a t)) r)
        CEq (Free f1) (Free f2) | Just cs' <- equal f1 f2 -> put True >> go assume (cs' ++ cs) r
        CEq _ _ -> go assume cs (c:r)

        CPred p ts ->
          case [a | a@(CPred p' ts') <- assume
               , and $ zipWith (==) ts ts'
               , p == p', length ts == length ts'] of
            [_] -> go assume cs r
            _:_  -> error "Ambiguous assumptions"
            [] ->
              case [map (substitute m) a
                   | a `CImpl` [ensureAssumption -> Just (CPred p' ts')] <- assume
                   , m <- maybeToList $ matches ts ts'
                   , p == p', length ts == length ts'] of
                [a] -> put True >> go assume (a ++ cs) r
                _:_ -> error "Ambiguous assumptions"
                [] -> go assume cs (c:r)

        CImpl _ [] -> go assume cs r
        CImpl a w ->
          do
            let res = solve (map weaken assume ++ (map fromAssumption a)) w
            when (res /= w) $ put True
            go assume cs (CImpl a res : r)
