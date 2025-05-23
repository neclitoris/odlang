{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-missing-pattern-synonym-signatures #-}
module OdLang.Core.Type where

import Data.Bifunctor.TH
import Data.Functor.Classes
import Data.Eq.Deriving
import Control.Monad.Reader
import Text.Show.Deriving
import Prettyprinter
import Prettyprinter.Render.String

import OdLang.Type.Free
import OdLang.Type.Solver

data Kind = KData | KMult | KType
          | Kind :->: Kind
          | Kind :*: Kind
          | KRow Kind

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
  (:->>) :: ty -> ty -> TypeF sc ty
  TDataAbsF :: sc -> TypeF sc ty
  TRecordF, TPaletteF, TUnionF :: ty -> TypeF sc ty

  TMultF :: ty -> TypeF sc ty
  TMultLinF, TMultAffF, TMultRelF, TMultUnresF :: TypeF sc ty
  TMultMeetF, TMultJoinF :: ty -> ty -> TypeF sc ty
  TTyConF :: ty -> ty -> TypeF sc ty

infixr 6 :->>

type Type var = Free TypeF var

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
pattern t1 :-> t2 = Free (t1 :->> t2)
pattern TDataAbs t = Free (TDataAbsF t)
pattern TRecord t = Free (TRecordF t)
pattern TPalette t = Free (TPaletteF t)
pattern TUnion t = Free (TUnionF t)

pattern TMult t = Free (TMultF t)
pattern TMultLin = Free TMultLinF
pattern TMultAff = Free TMultAffF
pattern TMultRel = Free TMultRelF
pattern TMultUnres = Free TMultUnresF
pattern TMultMeet t1 t2 = Free (TMultMeetF t1 t2)
pattern TMultJoin t1 t2 = Free (TMultJoinF t1 t2)
pattern TTyCon t1 t2 = Free (TTyConF t1 t2)

infixr 6 :->

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
deriving instance Eq var => Eq (Free TypeF var)

-- instance Show var => Pretty (Free TypeF var) where
  -- pretty x = parens $ runReader (pretty' (fmap viaShow x)) 0
    -- where
      -- pretty' :: forall ann. Free TypeF (Doc ann) -> Reader Int (Doc ann)
      -- pretty' (TVar v) = pure $ v
      -- pretty' (TApp a b) = do
        -- a' <- pretty' a
        -- b' <- pretty' b
        -- pure $ parens a' <+> parens b'
      -- pretty' (a :-> b) = do
        -- a' <- pretty' a
        -- b' <- pretty' b
        -- pure $ a' <+> "->" <+> b'
      -- pretty' (TFix f) = do
        -- name <- reader $ ("x" <>) . viaShow
        -- let s :: Inc (Doc ann) -> Free TypeF (Doc ann)
            -- s = \case { B 0 -> TVar name; F v -> TVar v }
        -- body <- local (+1) (pretty' (f >>= s))
        -- pure $ "μ" <+> name <> "." <+> body
      -- pretty' _ = error "bruh"
--
-- instance Show var => Show (Free TypeF var) where
  -- showsPrec _ = renderShowS . layoutPretty defaultLayoutOptions . pretty

deriving instance Show var => Show (Free TypeF var)

unfoldMu :: Free TypeF (Inc var) -> Free TypeF var
unfoldMu f = f >>= s
  where
    s = \case
      B 0 -> TFix f
      F v -> pure v

$(pure [])

instance Equational TypeF where
  equal (TFixF t1) (TFixF t2) =
    Just $ [CImpl [fmap Right (TFix t1) `CEq` fmap Right (TFix t2)]
                  [weaken (unfoldMu t1) `CEq` weaken (unfoldMu t2)]]
  equal (TFixF t1) t2 =
    Just $ [CEq (unfoldMu t1) (Free t2)]
  equal t1 t2@(TFixF _) = equal t2 t1

  equal (TAppF (TAbs t) u) v =
    Just $ [CEq (t >>= s) (Free v)]
      where
        s = \case { B 0 -> u; F v -> pure v }
  equal t u@(TAppF (TAbs _) _) = equal u t
  equal a b = defaultEqual a b
  sameConstr = $(makeSameConstr ''TypeF)
