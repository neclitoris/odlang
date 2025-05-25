{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-missing-pattern-synonym-signatures -Wno-name-shadowing #-}
module OdLang.Core.Type where

import Data.Bifunctor
import Data.Bifunctor.TH
import Data.Functor.Classes
import Data.Eq.Deriving
import Control.Monad
import Text.Show.Deriving
import Prettyprinter

import OdLang.Syntax.Pretty
import OdLang.Type.Free
import OdLang.Type.Solver

data KindF sc ty = KData | KMult | KType
                 | ty :!->: ty
                 | ty :!*: ty
                 | KRow ty

type Kind = Free KindF

data TypeF sc ty where
  TAbsF :: sc -> TypeF sc ty
  TAppF :: ty -> ty -> TypeF sc ty
  TProdF :: ty -> ty -> TypeF sc ty
  TProjF :: Bool -> ty -> TypeF sc ty
  TFixF :: sc -> TypeF sc ty

  TRowEF :: TypeF sc ty
  TRowExtF :: String -> ty -> ty -> TypeF sc ty
  TRowMapF :: ty -> ty -> TypeF sc ty
  TRowInfF :: ty -> TypeF sc ty
  TRowSupF :: ty -> TypeF sc ty

  TDataF :: ty -> TypeF sc ty
  (:!->) :: ty -> ty -> TypeF sc ty
  TDataAbsF :: sc -> TypeF sc ty
  TRecordF, TPaletteF, TUnionF :: ty -> TypeF sc ty

  TMultF :: ty -> TypeF sc ty
  TMultLinF, TMultAffF, TMultRelF, TMultUnresF :: TypeF sc ty
  (:!/\), (:!\/) :: ty -> ty -> TypeF sc ty
  TTyConF :: ty -> ty -> TypeF sc ty

infixl 6 :!/\
infixl 5 :!\/
infixr 0 :!->

type Type = Free TypeF

pattern TVar v = Pure v
pattern TAbs t = Free (TAbsF t)
pattern TApp f t = Free (TAppF f t)
pattern TProd t1 t2 = Free (TProdF t1 t2)
pattern TProj b t = Free (TProjF b t)
pattern TFix t = Free (TFixF t)

pattern TRowE = Free TRowEF
pattern TRowExt n t1 t2 = Free (TRowExtF n t1 t2)
pattern TRowMap f t = Free (TRowMapF f t)
pattern TRowInf t = Free (TRowInfF t)
pattern TRowSup t = Free (TRowSupF t)

pattern TData t = Free (TDataF t)
pattern t1 :-> t2 = Free (t1 :!-> t2)
pattern TDataAbs t = Free (TDataAbsF t)
pattern TRecord t = Free (TRecordF t)
pattern TPalette t = Free (TPaletteF t)
pattern TUnion t = Free (TUnionF t)

pattern TMult t = Free (TMultF t)
pattern TMultLin = Free TMultLinF
pattern TMultAff = Free TMultAffF
pattern TMultRel = Free TMultRelF
pattern TMultUnres = Free TMultUnresF
pattern t1 :/\ t2 = Free (t1 :!/\ t2)
pattern t1 :\/ t2 = Free (t1 :!\/ t2)
pattern TTyCon t1 t2 = Free (TTyConF t1 t2)

infixl 6 :/\
infixl 5 :\/
infixr 0 :->

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

instance Pretty var => PrettyPrec (Free TypeF var) where
  prettyPrec p x = runGenName $ prettyPrec' p (fmap pretty x)
    where
      prettyPrec' :: Int -> Free TypeF (Doc ann) -> GenName (Doc ann)
      prettyPrec' p = \case
        TVar v -> pure $ v
        TAbs t -> do
          name <- genName
          let t' = \case { B 0 -> pretty name; F v -> v} <$> t
          tdoc <- prettyPrec' 0 t'
          pure $ parensIf (p > 0) $ ("Λ" <+> pretty name <> ". ") <> tdoc
        TApp f x ->
          parensIf (p > 10) <$> liftM2 (<+>) (prettyPrec' 10 f) (prettyPrec' 11 x)
        TProd a b -> tupled <$> sequence [prettyPrec' 0 a, prettyPrec' 0 b]
        TProj b e -> (("π_" <> if b then "1" else "0") <+>) <$> prettyPrec' 11 e
        TFix t -> do
          name <- genName
          let t' = \case { B 0 -> pretty name; F v -> v} <$> t
          tdoc <- prettyPrec' 0 t'
          pure $ parensIf (p > 0) $ ("μ" <+> pretty name <> ".") <> tdoc
        a :-> b -> parensIf (p > 1) . hsep <$> sequence [prettyPrec' 2 a, pure "->", prettyPrec' 1 b]

instance Pretty var => Pretty (Free TypeF var) where
  pretty = fromPrettyPrec

apply :: Type (Inc var) -> Type var -> Type var
apply f x = f >>= s
  where
    s = \case
      B 0 -> x
      F v -> pure v

unfoldMu :: Type (Inc var) -> Type var
unfoldMu f = apply f (TFix f)

eval :: Type var -> Type var
eval = \case
  Pure v -> Pure v
  Free f -> evalF $ bimap eval eval f

evalF :: FreeS TypeF var -> Type var
evalF = eval' True
  where
    -- beta reduce
    eval' _ (TAppF (TAbs t) u) = apply t u
    -- evaluate meet
    eval' _ (TMultLin :!/\ _) = TMultLin
    eval' _ (TMultUnres :!/\ a) = a
    eval' _ (TMultAff :!/\ TMultRel) = TMultLin
    eval' True (a :!/\ b) = eval' False (b :!/\ a)
    -- evaluate join
    eval' _ (TMultLin :!\/ a) = a
    eval' _ (TMultUnres :!\/ _) = TMultUnres
    eval' _ (TMultAff :!\/ TMultRel) = TMultUnres
    eval' True (a :!\/ b) = eval' False (b :!\/ a)
    -- can't recurse anymore
    eval' True e = Free e
    eval' False e = Free e

floatKey :: String -> Type var -> Type var
floatKey = floatKey' id
  where
    floatKey' f k (eval -> TRowExt n t r)
      | k == n = TRowExt n t (f r)
      | otherwise = floatKey' (f . TRowExt n t) k r
    floatKey' f _ t = f t

instance Equational TypeF where
  equal a b = equal' True (eval (Free a)) (eval (Free b))
    where
      -- Unfold
      equal' _ (TFix t1) (TFix t2) =
        Just [CImpl [fmap Right (TFix t1) `CEq` fmap Right (TFix t2)]
                    [weaken (unfoldMu t1) `CEq` weaken (unfoldMu t2)]]
      equal' _ (TFix t1) t2 =
        Just [CEq (unfoldMu t1) t2]
      -- MapEmpty
      equal' _ (TRowMap _ TRowE) t = Just [CEq TRowE t]
      -- MapExt
      equal' _ (TRowMap f (TRowExt n t r)) u =
        Just [CEq (TRowExt n (TApp f t) (TRowMap f r)) u]
      -- ProjRed
      equal' _ (TProj False (TProd t _)) u = Just [CEq t u]
      equal' _ (TProj True  (TProd _ t)) u = Just [CEq t u]
      -- DataType
      equal' _ (TData (TTyCon t _)) u = Just [CEq t u]
      -- MultType
      equal' _ (TMult (TTyCon _ t)) u = Just [CEq t u]
      -- TypeExt
      equal' _ (TTyCon (TData t1) (TMult t2)) u | t1 == t2 = Just [CEq t1 u]
      -- Row equality
      equal' _ a@(TRowExt n1 t1 r1) b@(TRowExt n2 t2 r2)
        | TRowExt n3 t3 r3 <- floatKey n1 b, n1 == n3 = Just [CEq t1 t3, CEq r1 r3]
        | TRowExt n3 t3 r3 <- floatKey n2 a, n2 == n3 = Just [CEq t2 t3, CEq r2 r3]

      equal' True a b = equal' False b a
      equal' False (Free a) (Free b) = defaultEqual a b
      equal' False a' b'
        | Free a == a' && Free b == b' = Nothing
        | otherwise = Just [CEq a' b']

  sameConstr = $(makeSameConstr ''TypeF)
