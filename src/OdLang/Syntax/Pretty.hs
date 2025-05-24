{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module OdLang.Syntax.Pretty where

import Control.Monad.State
import Prettyprinter

class PrettyPrec a where
  prettyPrec :: Int -> a -> Doc ann

fromPrettyPrec :: PrettyPrec a => a -> Doc ann
fromPrettyPrec a = prettyPrec 0 a

parensIf :: Bool -> Doc ann -> Doc ann
parensIf True = parens
parensIf False = id

newtype GenName a = GenName (State Int a)
  deriving (Functor, Applicative, Monad)

runGenName :: GenName a -> a
runGenName (GenName r) = evalState r 0

genName :: GenName String
genName = do
  i <- GenName get
  GenName $ modify (+1)
  pure $ "x" ++ show @Int i
