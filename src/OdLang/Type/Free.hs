module OdLang.Type.Free where

import Control.Monad
import Data.Bifunctor
import Data.Bifoldable
import Data.Bitraversable
import Data.Functor.Classes

data Inc var = B Int | F var deriving (Eq, Show)

deriving instance Functor Inc
deriving instance Foldable Inc
deriving instance Traversable Inc

type Scope term var = term (Inc var)

data Free term var
  = Pure var
  | Free (FreeS term var)

type FreeS term var = term (Scope (Free term) var) (Free term var)

instance Bifunctor term => Functor (Free term) where
  fmap = liftM

instance Bifunctor term => Applicative (Free term) where
  (<*>) = ap
  pure = Pure

instance Bifunctor term => Monad (Free term) where
  return = pure
  Pure v >>= f = f v
  Free t >>= f = Free (bimap (>>= traverse f) (>>= f) t)

instance Bifoldable term => Foldable (Free term) where
  foldMap f (Pure v) = f v
  foldMap f (Free t) = bifoldMap (foldMap $ foldMap f) (foldMap f) t

instance Bitraversable term => Traversable (Free term) where
  traverse f (Pure v) = Pure <$> f v
  traverse f (Free t) = Free <$> bitraverse (traverse $ traverse f) (traverse f) t

deriving instance (Eq2 term, Eq var) => Eq (Free term var)
deriving instance (Show2 term, Show var) => Show (Free term var)
