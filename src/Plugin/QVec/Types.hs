{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}

module Plugin.QVec.Types (
  -- *
  Env (..),
  Decls (..),
  DeclsCoords (..),
  InitEnv (..),
  -- *
  QVec (..),
  mkQVec,
  minusQVec,
  negateQVec,
  scaleQVec,
  singletonQVec,
  varQVec,
  -- *
  FunApp (..),
  FunArg (..),
  funAppTyConArgs,
  funAppType,
  funArgType,
  -- *
  Tree (..),
  prjTree,
  qVecTree,
  treeType,
  -- *
  FunEq (..),
  TyEq (..),
  funeqType,
  prjFunEq,
  prjTyEq,
  -- *
  FunEqCoords (..),
  funeqCoordsType,
  prjFunEqCoords,
  -- *
  Result (..),
  emitCt,
  nullResult,
  solveGiven,
  solveDerived,
  solveWanted,
  -- *
  NDVar (..),
  NDXi (..),
  balance,
  dropKind,
  foldForM,
  foldMapM,
  mwhen,
  munless,
  orElse,
  partitionPosNeg,
  plusMap,
  -- *
  antiSwapMasquerade,
  ridiculousTcLevel,
  ) where

import           Control.Applicative ((<|>))
import           Control.Monad (guard)
import           Data.Foldable (fold)
import           Data.IORef (IORef)
import           Data.Map (Map)
import qualified Data.Map as Map
import           GHC.Natural (Natural)
import           GHC.Real (Ratio (..), numerator, denominator)

import           GhcPlugins ((<+>), parens, ppr, text)
import qualified GhcPlugins
import qualified TcEvidence
import           TcRnTypes (Xi)
import qualified TcRnTypes
import           TcType (TcKind, TcLevel, TcTyVar)
import qualified TcType
import           TyCon (TyCon)
import           Unique (getUnique, nonDetCmpUnique)
import           VarEnv
import           VarSet

data Env = MkEnv
    {
      envDecls :: !Decls
    ,
      envDeclsCoords :: !DeclsCoords
    ,
      envDynFlags :: !GhcPlugins.DynFlags
    ,
      -- | How any times the plugin has been invoked

      envInvocationCount :: !(IORef Int)
    ,
      envLevel :: !TcLevel
    }

-- | Fields of 'Env' that can be set during 'tcPluginInit'

data InitEnv = MkInitEnv
    {
      ieDecls :: !Decls
    ,
      ieDeclsCoords :: !DeclsCoords
    ,
      ieInvocationCount :: !(IORef Int)
    }

data Decls = MkDecls
    {
      dBv1 :: !TyCon
    ,
      dBvN :: !TyCon
    ,
      dBvQ :: !TyCon
    ,
      -- | 'Data.QVec.:-'

      dDecr :: !TyCon
    ,
      -- | 'Data.QVec.:+'

      dIncr :: !TyCon
    ,
      dInv :: !TyCon
    ,
      -- | 'Data.QVec.:-:'

      dMnus :: !TyCon
    ,
      dNil :: !TyCon
    ,
      -- | 'Data.QVec.:+:'

      dPlus :: !TyCon
    ,
      dQVec :: !TyCon
    ,
      dScQ :: !TyCon
    ,
      dScN :: !TyCon
    }

data DeclsCoords = MkDeclsCoords
    {
      dCoords :: !TyCon
    ,
      dConsCoords :: !TyCon
    ,
      dNeg :: !TyCon
    ,
      dNilCoords :: !TyCon
    ,
      dPos :: !TyCon
    ,
      dToCoords :: !TyCon
    }
{------------------------------------------------------------------------------
    Syntactic form
------------------------------------------------------------------------------}

-- | Exact representation of a type family application (excluding kind
-- argument)

data FunApp f =
      FunAppBvN !Natural !Xi
    |
      FunAppBvQ !Natural !Natural !Xi
    |
      FunAppDecr (f TcTyVar) !Xi
    |
      FunAppIncr (f TcTyVar) !Xi
    |
      FunAppInv (f TcTyVar)
    |
      FunAppMnus (f TcTyVar) (f TcTyVar)
    |
      FunAppPlus (f TcTyVar) (f TcTyVar)
    |
      FunAppScN !Natural (f TcTyVar)
    |
      FunAppScQ !Natural !Natural (f TcTyVar)

instance Eq (f TcTyVar) => Eq (FunApp f) where
  FunAppBvN ln    le == FunAppBvN rn    re = ln == rn && GhcPlugins.eqType le re
  FunAppBvQ ln ld le == FunAppBvQ rn rd re = ln == rn && ld == rd && GhcPlugins.eqType le re
  FunAppDecr lv le   == FunAppDecr rv re   = lv == rv && GhcPlugins.eqType le re
  FunAppIncr lv le   == FunAppIncr rv re   = lv == rv && GhcPlugins.eqType le re
  FunAppInv lv       == FunAppInv rv       = lv == rv
  FunAppMnus lv1 lv2 == FunAppMnus rv1 rv2 = lv1 == rv1 && lv2 == rv2
  FunAppPlus lv1 lv2 == FunAppPlus rv1 rv2 = lv1 == rv1 && lv2 == rv2
  FunAppScN ln    lv == FunAppScN rn    rv = ln == rn && lv == rv
  FunAppScQ ln ld lv == FunAppScQ rn rd rv = ln == rn && ld == rd && lv == rv
  _                  == _                  = False

traverseFunApp ::
    Applicative i =>
    (f TcTyVar -> i (g TcTyVar)) {- ^ apply to left arguments -} ->
    (f TcTyVar -> i (g TcTyVar)) {- ^ apply to right arguments -} ->
    FunApp f -> i (FunApp g)
traverseFunApp l r = \case
    FunAppBvN n   e  -> pure $ FunAppBvN n   e
    FunAppBvQ n d e  -> pure $ FunAppBvQ n d e
    FunAppDecr v e   -> FunAppDecr <$> l v <*> pure e
    FunAppIncr v e   -> FunAppIncr <$> l v <*> pure e
    FunAppInv v      -> FunAppInv <$> l v
    FunAppMnus v1 v2 -> FunAppMnus <$> l v1 <*> r v2
    FunAppPlus v1 v2 -> FunAppPlus <$> l v1 <*> r v2
    FunAppScN n   v  -> FunAppScN n   <$> r v
    FunAppScQ n d v  -> FunAppScQ n d <$> r v

-- | Exact representation of a vector argument of a type family
-- application (excluding kind argument)

data FunArg v =
      FunArgBv1 !Xi
    |
      FunArgNil
    |
      FunArgVar !v
  deriving (Foldable, Functor, Traversable)


instance GhcPlugins.Outputable (f TcTyVar) => GhcPlugins.Outputable (FunApp f) where
  ppr = \case
      FunAppBvN n   e  -> text "BvN" <+> nat n           <+> ppr e
      FunAppBvQ n d e  -> text "BvQ" <+> nat n <+> nat d <+> ppr e
      FunAppDecr v e   -> parens (ppr v) <+> text ":-" <+> ppr e
      FunAppIncr v e   -> parens (ppr v) <+> text ":+" <+> ppr e
      FunAppInv v      -> text "Inv" <+> ppr v
      FunAppMnus v1 v2 -> parens (ppr v1) <+> text ":-:" <+> parens (ppr v2)
      FunAppPlus v1 v2 -> parens (ppr v1) <+> text ":+:" <+> parens (ppr v2)
      FunAppScN n   v  -> text "ScN" <+> nat n           <+> ppr v
      FunAppScQ n d v  -> text "ScQ" <+> nat n <+> nat d <+> ppr v
    where
      nat n = ppr (fromIntegral n :: Integer)

instance GhcPlugins.Outputable v => GhcPlugins.Outputable (FunArg v) where
  ppr = \case
      FunArgBv1 e -> text "Bv1" <+> ppr e
      FunArgNil   -> text "Nil"
      FunArgVar v -> ppr v

funAppType ::
  Env ->
  TcKind ->
  (Env -> TcKind -> f TcTyVar -> Xi) ->
  FunApp f ->
  Xi
funAppType env k raw_arg fa =
    GhcPlugins.mkTyConApp tycon args
  where
    (tycon, args) = funAppTyConArgs env k raw_arg fa

funAppTyConArgs ::
  Env ->
  TcKind ->
  (Env -> TcKind -> f TcTyVar -> Xi) ->
  FunApp f ->
  (TyCon, [Xi])
funAppTyConArgs env@MkEnv{..} k raw_arg = \case
    FunAppBvN n   e  -> tycon dBvN [k, nat n, e]
    FunAppBvQ n d e  -> tycon dBvQ [k, nat n, nat d, e]
    FunAppDecr v e   -> tycon dDecr [k, arg v, e]
    FunAppIncr v e   -> tycon dIncr [k, arg v, e]
    FunAppInv v      -> tycon dInv [k, arg v]
    FunAppMnus v1 v2 -> tycon dMnus [k, arg v1, arg v2]
    FunAppPlus v1 v2 -> tycon dPlus [k, arg v1, arg v2]
    FunAppScN n   v  -> tycon dScN [k, nat n, arg v]
    FunAppScQ n d v  -> tycon dScQ [k, nat n, nat d, arg v]
  where
    MkDecls{..} = envDecls

    arg = raw_arg env k
    nat = GhcPlugins.mkNumLitTy . fromIntegral
    tycon = (,)

funArgType ::
  Env ->
  TcKind ->
  FunArg TcTyVar ->
  Xi
funArgType MkEnv{..} k = \case
    FunArgBv1 e -> tycon dBv1 [k, e]
    FunArgNil   -> tycon dNil [k]
    FunArgVar v -> tyvar v
  where
    MkDecls{..} = envDecls

    tycon = GhcPlugins.mkTyConApp
    tyvar = GhcPlugins.mkTyVarTy

data Tree v =
      TreeBv1 !Xi
    |
      TreeFun (FunApp Tree)
    |
      TreeNil
    |
      TreeVar !v

instance Eq v => Eq (Tree v) where
  TreeBv1 le   == TreeBv1 re   = GhcPlugins.eqType le re
  TreeFun lfat == TreeFun rfat = lfat == rfat
  TreeNil      == TreeNil      = True
  TreeVar lv   == TreeVar rv   = lv == rv
  _            == _            = False

instance GhcPlugins.Outputable v => GhcPlugins.Outputable (Tree v) where
  ppr = \case
      TreeBv1 e   -> ppr e
      TreeFun fat -> ppr fat
      TreeNil     -> text "Nil"
      TreeVar v   -> ppr v

treeType :: Env -> TcKind -> Tree TcTyVar -> Xi
treeType env k = \case
    TreeBv1 e -> funArg $ FunArgBv1 e
    TreeFun t -> funAppType env k treeType t
    TreeNil   -> funArg FunArgNil
    TreeVar v -> funArg $ FunArgVar v
  where
    funArg = funArgType env k

-- | Parse without recursing into left-arguments, since in canonical
-- form, those are already uninterpretable

prjTree ::
  Env ->
  VarEnv FunEq ->
  TcTyVar ->
  Maybe (TcKind, Tree TcTyVar)
prjTree env funeqs = \v -> do
    k <- getQVec_maybe env $ kind v
    (,) k <$> go emptyVarSet v
  where
    MkEnv{..} = env
    MkDecls{..} = envDecls

    go acc v0 = do
      -- check for infinite types
      guard $ not $ elemVarSet v0 acc

      let funArg = \case
              FunArgBv1 e -> pure $ TreeBv1 e
              FunArgNil   -> pure TreeNil
              FunArgVar v -> go (extendVarSet acc v0) v

      case lookupVarEnv funeqs v0 of
        Nothing -> pure $ TreeVar v0
        Just MkFunEq{..} -> TreeFun <$> traverseFunApp funArg funArg fe_lhs

    kind = GhcPlugins.tyVarKind

{------------------------------------------------------------------------------
    QVec canonical form
------------------------------------------------------------------------------}

-- | We intentionally use an 'Ord' instance that depends on uniques
--
-- TODO explain the assumptions about why this is safe

newtype NDXi = MkNDXi{ndXi :: Xi}

instance Eq NDXi where
  MkNDXi l == MkNDXi r = GhcPlugins.eqType l r

instance Ord NDXi where
  compare (MkNDXi l) (MkNDXi r) = GhcPlugins.nonDetCmpType l r

instance GhcPlugins.Outputable NDXi where
  ppr (MkNDXi t) = ppr t

newtype NDVar = MkNDVar TcTyVar
  deriving (Eq)

instance GhcPlugins.Outputable NDVar where
  ppr (MkNDVar v) = ppr v

instance Ord NDVar where
  compare (MkNDVar l) (MkNDVar r) =
      nonDetCmpUnique (getUnique l) (getUnique r)

-- | The canonical form of an 'Data.QVec.QVec'

data QVec =
    -- | Counts 'Data.QVec.QVec' tyvars and counts for basis elements
    --
    -- The 'Data.QVec.:+:' and 'Data.QVec.:-:'s, and the
    -- 'Data.QVec.:+'s and 'Data.QVec.:-'s.
    --
    -- INVARIANT: Every 'Int' is non-zero.

    MkQVec
      !(Map NDVar Rational)
      !(Map NDXi Rational)
  deriving (Eq, Ord)

instance Monoid QVec where
  mempty = MkQVec Map.empty Map.empty

instance Semigroup QVec where
  MkQVec lvs lbs <> MkQVec rvs rbs =
      MkQVec (plusMap lvs rvs) (plusMap lbs rbs)

instance GhcPlugins.Outputable QVec where
  ppr = ppr . qVecCanSum

scaleQVec :: Rational -> QVec -> QVec
scaleQVec i (MkQVec vs bs) =
    MkQVec (fmap (* i) vs) (fmap (* i) bs)

negateQVec :: QVec -> QVec
negateQVec (MkQVec vs bs) =
    MkQVec (fmap negate vs) (fmap negate bs)

minusQVec :: QVec -> QVec -> QVec
minusQVec l r = l <> negateQVec r

singletonQVec :: Xi -> QVec
singletonQVec t = MkQVec Map.empty (Map.singleton (MkNDXi t) 1)

varQVec :: TcTyVar -> QVec
varQVec v = MkQVec (Map.singleton (MkNDVar v) 1) Map.empty

qVecTree :: QVec -> Tree TcTyVar
qVecTree zm = canSumTree (qVecCanSum zm)

-- | Render an 'QVecCan' via the "Data.QVec" operators
--
-- First @:+:@s, then @:-:@s, then @:+@s, then @:-@s. If there are no
-- @:+:@s, then start with @Nil@.
--
-- e.g. @x :+: y :+ b :- a@
--
-- e.g. @Nil :-: y@
--
-- e.g. @x :+ b :+ c :- a@

qVecCanSum :: QVec -> CanSum
qVecCanSum (MkQVec vs bs) =
    CanSum
      (Map.toAscList ps ++ map (fmap negate) (Map.toAscList ms))
      (Map.toAscList is ++ map (fmap negate) (Map.toAscList ds))
  where
    (ps, ms) = partitionPosNeg vs
    (is, ds) = partitionPosNeg bs

-- | Canonicalized linear combination
--
-- INVARIANT each list is sorted with positives first
--
-- INVARIANT every 'Rational' is finite and non-zero

data CanSum = CanSum [(NDVar, Rational)] [(NDXi, Rational)]
  deriving (Eq)

instance GhcPlugins.Outputable CanSum where
  ppr (CanSum vs es) = text "CanSum"
      <+> ppr [ (v, n, d) | (MkNDVar v, n :% d) <- vs ]
      <+> ppr [ (e, n, d) | (MkNDXi  e, n :% d) <- es ]

canSumTree :: CanSum -> Tree TcTyVar
canSumTree (CanSum vs es) = case map injV vs ++ map injE es of
    []         -> TreeNil
    term:terms -> foldl snoc (leftmost term) terms
  where
    injV (v, q) = (Left v, q)
    injE (e, q) = (Right e, q)

    leftmost :: (Either NDVar NDXi, Rational) -> Tree TcTyVar
    leftmost (x, q)
        | q < 0     = TreeFun $ FunAppInv $ leftmost (x, negate q)
        | otherwise = snoc2 (x, q)

    snoc :: Tree TcTyVar -> (Either NDVar NDXi, Rational) -> Tree TcTyVar
    snoc acc (x, q) = TreeFun $ case x of
        Right (MkNDXi e)
            | q == -1   -> FunAppDecr acc e
            | q == 1    -> FunAppIncr acc e
        _               -> acc `op` snoc2 (x, q)
      where
        op = if q < 0 then FunAppMnus else FunAppPlus

    snoc2 :: (Either NDVar NDXi, Rational) -> Tree TcTyVar
    snoc2 (x, raw_q) = pick $ case x of
        Left (MkNDVar v) -> (TreeVar v, FunAppScN n (TreeVar v), FunAppScQ n d (TreeVar v))
        Right (MkNDXi e) -> (TreeBv1 e, FunAppBvN n e, FunAppBvQ n d e)
      where
        q = abs raw_q
        n = fromInteger $ numerator q
        d = fromInteger $ denominator q

        pick (one, nat, rat)
          | 1 == q    = one
          | 1 == d    = TreeFun nat
          | otherwise = TreeFun rat

{------------------------------------------------------------------------------
    Isolated canonical constraints
------------------------------------------------------------------------------}

-- | A funeq that potentially interests us because it uses the
-- "Data.QVec" signature

data FunEq = MkFunEq
    {
      fe_ct :: TcRnTypes.Ct
    ,
      fe_ev :: TcRnTypes.CtEvidence
    ,
      fe_rhs :: TcTyVar
    ,
      fe_kind :: TcKind
    ,
      fe_lhs :: FunApp FunArg
    }

instance GhcPlugins.Outputable FunEq where
  ppr MkFunEq{..} = text "FunEq" <+> ppr fe_ev <+> text "is" <+> ppr fe_kind <+> ppr fe_rhs <+> ppr fe_lhs

-- | 'Just' if it's a 'TcRnTypes.CFunEqCan' mapping to an application
-- of the "Data.QVec" operators where each 'Data.QVec.QVec'
-- argument is either 'Data.QVec.Nil' or another
-- 'Data.QVec.QVec' tyvar

prjFunEq :: Env -> TcRnTypes.Ct -> Maybe FunEq
prjFunEq env ct = do
    TcRnTypes.CFunEqCan{..} <- pure ct

    let fe_ct = ct
        fe_ev = cc_ev
        fe_rhs = cc_fsk

    (fe_kind, fe_lhs) <- prjFunAppTyConArgs env (cc_fun, cc_tyargs)

    pure MkFunEq{..}

prjFunAppTyConArgs :: Env -> (TyCon, [Xi]) -> Maybe (TcKind, FunApp FunArg)
prjFunAppTyConArgs env@MkEnv{..} (tc, args) =
        (do
          guard $ tc == dBvN
          [k, n, e] <- pure args
          n' <- nat n
          pure (k, FunAppBvN n' e))
    <|> (do
          guard $ tc == dBvQ
          [k, n, d, e] <- pure args
          n' <- nat n
          d' <- nat d
          pure (k, FunAppBvQ n' d' e))
    <|> (do
          guard $ tc == dDecr
          [k, v, e] <- pure args
          arg <- funArg v
          pure (k, FunAppDecr arg e))
    <|> (do
          guard $ tc == dIncr
          [k, v, e] <- pure args
          arg <- funArg v
          pure (k, FunAppIncr arg e))
    <|> (do
          guard $ tc == dInv
          [k, v] <- pure args
          arg <- funArg v
          pure (k, FunAppInv arg))
    <|> (do
          guard $ tc == dMnus
          [k, v1, v2] <- pure args
          arg1 <- funArg v1
          arg2 <- funArg v2
          pure (k, FunAppMnus arg1 arg2))
    <|> (do
          guard $ tc == dPlus
          [k, v1, v2] <- pure args
          arg1 <- funArg v1
          arg2 <- funArg v2
          pure (k, FunAppPlus arg1 arg2))
    <|> (do
          guard $ tc == dScN
          [k, n, v] <- pure args
          n' <- nat n
          arg <- funArg v
          pure (k, FunAppScN n' arg))
    <|> (do
          guard $ tc == dScQ
          [k, n, d, v] <- pure args
          n' <- nat n
          d' <- nat d
          arg <- funArg v
          pure (k, FunAppScQ n' d' arg))
  where
    MkDecls{..} = envDecls

    funArg t = snd <$> prjFunArg env t
    nat = fmap fromInteger . GhcPlugins.isNumLitTy

prjFunArg :: Env -> Xi -> Maybe (TcKind, FunArg TcTyVar)
prjFunArg env@MkEnv{..} t =
        (do
          (tc, [k, e]) <- tycon t
          guard $ tc == dBv1
          pure (k, FunArgBv1 e))
    <|> (do
          (tc, [k]) <- tycon t
          guard $ tc == dNil
          pure (k, FunArgNil))
    <|> (do
          v <- tyvar t
          -- TODO should 'Nothing' be a panic here?
          k <- getQVec_maybe env $ GhcPlugins.tyVarKind v
          pure (k, FunArgVar v))
  where
    MkDecls{..} = envDecls

    tyvar = GhcPlugins.getTyVar_maybe
    tycon = GhcPlugins.splitTyConApp_maybe

-- | The LHS as a type

funeqType :: Env -> FunEq -> Xi
funeqType env MkFunEq{..} =
    funAppType env fe_kind funArgType fe_lhs

-- | A tyeq that potentially interests us because it involves the
-- "Data.QVec" signature

data TyEq = MkTyEq
    {
      te_ct :: TcRnTypes.Ct
    ,
      te_ev :: TcRnTypes.CtEvidence
    ,
      te_kind :: TcKind
    ,
      te_lhs :: TcTyVar
    ,
      -- | 'Nothing' means 'Data.QVec.Nil'

      te_rhs :: FunArg TcTyVar
    }

instance GhcPlugins.Outputable TyEq where
  ppr MkTyEq{..} = text "TyEq" <+> ppr te_ev <+> text "is" <+> ppr te_kind <+> ppr te_lhs <+> ppr te_rhs

-- | 'Just' if it's a 'TcRnTypes.CTyEqCan' mapping to
-- 'Data.QVec.Nil' or another 'Data.QVec.QVec' tyvar

prjTyEq :: Env -> TcRnTypes.Ct -> Maybe TyEq
prjTyEq env ct = do
    TcRnTypes.CTyEqCan{..} <- pure ct

    let te_ct = ct
        te_ev = cc_ev
        te_lhs = unAntiSwapMasquerade cc_tyvar

    (te_kind, te_rhs) <- prjFunArg env cc_rhs

    pure MkTyEq{..}

-- | A funeq that potentially interests us because it involves a
-- "Data.QVec" conversion

data FunEqCoords = MkFunEqCoords
    {
      fec_ct :: TcRnTypes.Ct
    ,
      fec_ev :: TcRnTypes.CtEvidence
    ,
      fec_rhs :: TcTyVar
    ,
      fec_kind :: TcKind
    ,
      fec_lhs :: FunArg TcTyVar
    }

instance GhcPlugins.Outputable FunEqCoords where
  ppr MkFunEqCoords{..} = text "FunEqCoords" <+> ppr fec_ev <+> text "is" <+> ppr fec_kind <+> ppr fec_rhs <+> ppr fec_lhs

prjFunEqCoords :: Env -> TcRnTypes.Ct -> Maybe FunEqCoords
prjFunEqCoords env ct = do
    TcRnTypes.CFunEqCan{..} <- pure ct

    let fec_ct = ct
        fec_ev = cc_ev
        fec_rhs = cc_fsk

    (fec_kind, fec_lhs) <- prjFunAppCoordsTyConArgs env (cc_fun, cc_tyargs)

    pure MkFunEqCoords{..}

prjFunAppCoordsTyConArgs :: Env -> (TyCon, [Xi]) -> Maybe (TcKind, FunArg TcTyVar)
prjFunAppCoordsTyConArgs env@MkEnv{..} (tc, args) =
        (do
          guard $ tc == dToCoords
          [k, t] <- pure args
          (_k, t') <- prjFunArg env t
          pure (k, t'))
  where
    MkDeclsCoords{..} = envDeclsCoords

-- | The LHS as a type

funeqCoordsType :: Env -> FunEqCoords -> Xi
funeqCoordsType env@MkEnv{..} MkFunEqCoords{..} =
    tycon dToCoords [fec_kind, funArgType env fec_kind fec_lhs]
  where
    MkDeclsCoords{..} = envDeclsCoords

    tycon = GhcPlugins.mkTyConApp

{------------------------------------------------------------------------------
    Parsing QVec
------------------------------------------------------------------------------}

-- | 'Just' if the kind is an applicaton of 'Data.QVec.QVec'

getQVec_maybe :: Env -> TcKind -> Maybe TcKind
getQVec_maybe MkEnv{..} v = do
    (tc, [k]) <- GhcPlugins.splitTyConApp_maybe v
    guard $ tc == dQVec
    pure k
  where
    MkDecls{..} = envDecls

-- | 'Just' if the var's kind is an applicaton of 'Data.QVec.QVec'

mkQVec ::
  Env ->
  VarEnv FunEq ->
  VarEnv TyEq ->
  TcTyVar ->
  Maybe (TcKind, QVec)
mkQVec env funeqs tyeqs = \v -> do
    k <- getQVec_maybe env $ GhcPlugins.tyVarKind v
    (,) k <$> go emptyVarSet v
  where
    go acc v0 = do
      -- check for infinite types
      guard $ not $ elemVarSet v0 acc

      let funArg = \case
              FunArgBv1 e -> pure $ singletonQVec e
              FunArgNil   -> pure mempty
              FunArgVar v -> go (extendVarSet acc v0) v

      let funApp = \case
              FunAppBvN n   e  -> pure $
                scaleQVec (fromIntegral n) $
                singletonQVec e
              FunAppBvQ n d e  -> pure $
                scaleQVec (fromIntegral n / fromIntegral d) $
                singletonQVec e
              FunAppDecr v e   ->
                (`minusQVec` singletonQVec e) <$> funArg v
              FunAppIncr v e   ->
                (<> singletonQVec e) <$> funArg v
              FunAppInv v           -> negateQVec <$> funArg v
              FunAppMnus v1 v2 -> minusQVec <$> funArg v1 <*> funArg v2
              FunAppPlus v1 v2 -> (<>)        <$> funArg v1 <*> funArg v2
              FunAppScN n   v  ->
                scaleQVec (fromIntegral n) <$>
                funArg v
              FunAppScQ n d v  ->
                scaleQVec (fromIntegral n / fromIntegral d) <$>
                funArg v

      case (lookupVarEnv funeqs v0, lookupVarEnv tyeqs v0) of
        (Just MkFunEq{..}, _)      -> funApp fe_lhs
        (Nothing, Just MkTyEq{..}) -> funArg te_rhs
        (Nothing, Nothing)         -> pure $ varQVec v0

newtype Result = Result{tcPluginResult :: TcRnTypes.TcPluginResult}

instance Monoid Result where
  mempty = Result $ TcRnTypes.TcPluginOk [] []

instance Semigroup Result where
  Result l <> Result r = Result $ case (l, r) of
      (TcRnTypes.TcPluginOk lold lnew, TcRnTypes.TcPluginOk rold rnew) ->
          TcRnTypes.TcPluginOk (lold ++ rold) (lnew ++ rnew)
      (TcRnTypes.TcPluginContradiction l', TcRnTypes.TcPluginContradiction r') ->
          TcRnTypes.TcPluginContradiction (l' ++ r')
      (TcRnTypes.TcPluginContradiction x, _) -> TcRnTypes.TcPluginContradiction x
      (_, TcRnTypes.TcPluginContradiction x) -> TcRnTypes.TcPluginContradiction x

instance GhcPlugins.Outputable Result where
  ppr (Result x) = case x of
      TcRnTypes.TcPluginContradiction cts ->
          text "TcPluginContradiction" <+> ppr cts
      TcRnTypes.TcPluginOk [] []   -> text "TcPluginOk [] []"
      TcRnTypes.TcPluginOk old new ->
          text "TcPluginOk" <+> (ppr old GhcPlugins.$$ ppr new)

nullResult :: Result -> Bool
nullResult = \case
    Result (TcRnTypes.TcPluginOk [] []) -> True
    _ -> False

emitCt :: TcRnTypes.Ct -> Result
emitCt ct = Result $ TcRnTypes.TcPluginOk [] [ct]

solveGiven :: TcRnTypes.Ct -> Result
solveGiven ct = Result $ TcRnTypes.TcPluginOk [(ev, ct)] []
  where
    -- this argument is ignored for Givens
    --
    -- The interface suggests to just use a given's own evidence here.
    ev = TcRnTypes.ctEvTerm $ TcRnTypes.cc_ev ct

solveDerived :: TcEvidence.EvTerm -> TcRnTypes.Ct -> Result
solveDerived ev ct = Result $ TcRnTypes.TcPluginOk [(ev, ct)] []

solveWanted :: TcEvidence.EvTerm -> TcRnTypes.Ct -> Result
solveWanted ev ct = Result $ TcRnTypes.TcPluginOk [(ev, ct)] []

{------------------------------------------------------------------------------
    Miscellany
------------------------------------------------------------------------------}

plusMap :: (Ord k, Eq a, Num a) => Map k a -> Map k a -> Map k a
plusMap l r = Map.filter (/= 0) $ Map.unionWith (+) l r

partitionPosNeg :: (Ord k, Ord a, Num a) => Map k a -> (Map k a, Map k a)
partitionPosNeg = fmap (fmap abs) . Map.partition (> 0)

orElse :: Monad m => m Result -> m Result -> m Result
orElse m n = do
    x <- m
    if nullResult x then n else pure x

foldForM :: (Traversable t, Monad m, Monoid b) => t a -> (a -> m b) -> m b
foldForM = flip foldMapM

foldMapM :: (Traversable t, Monad m, Monoid b) => (a -> m b) -> t a -> m b
foldMapM f x = fmap fold $ traverse f x

mwhen :: (Applicative m, Monoid a) => Bool -> m a -> m a
mwhen b m = if b then m else pure mempty

munless :: (Applicative m, Monoid a) => Bool -> m a -> m a
munless = mwhen . not

dropKind :: (TcKind, a) -> a
dropKind (_k, x) = x

-- | A 'TcType.TcLevel' depth no reasonable program will ever reach

ridiculousTcLevel :: Int
ridiculousTcLevel = 1000000

-- | Hackily change a tyvar's details so that it will definitely stay
-- on the LHS of a CTyEqCan.
--
-- Sometimes we emit a type equality that crucially must not be
-- flipped, even though GHC will immediately flip it. This function
-- lets us prevent GHC from doing so.

antiSwapMasquerade :: TcTyVar -> TcTyVar
antiSwapMasquerade v0 = case GhcPlugins.tcTyVarDetails v0 of

    TcType.MetaTv{} -> v0

    TcType.SkolemTv (TcType.TcLevel lvl) flag ->
        GhcPlugins.setTcTyVarDetails v0 $
        TcType.SkolemTv (TcType.TcLevel (lvl + ridiculousTcLevel)) flag

    TcType.RuntimeUnk{} -> v0

unAntiSwapMasquerade :: TcTyVar -> TcTyVar
unAntiSwapMasquerade v0 = case GhcPlugins.tcTyVarDetails v0 of
    TcType.MetaTv{} -> v0

    TcType.SkolemTv (TcType.TcLevel lvl) flag
        | lvl > ridiculousTcLevel ->
        GhcPlugins.setTcTyVarDetails v0 $
        TcType.SkolemTv (TcType.TcLevel (lvl - ridiculousTcLevel)) flag

        | otherwise -> v0

    TcType.RuntimeUnk{} -> v0

data Balance a =
      Balanced [a] (Map a Rational)
    |
      Imbalanced

balance ::
    forall l r.
    (Ord l, Ord r) =>
    (l -> r -> Bool) {- ^ apart -} ->
    Map l Rational -> Map r Rational ->
    Maybe [(l, r)] {- ^ derived equalities or else imbalanced -}
balance aptLR = outer
  where
    -- 'Nothing' means contradiction
    outer ::
        Map l Rational -> Map r Rational ->
        Maybe [(l, r)]
    outer ls0 rs0 = do
        (ls1, rs1, a1) <- inner aptLR one ls0 (Map.toList rs0)
        (rs2, ls2, a2) <- inner (flip aptLR) (flip one) rs1 (Map.toList ls1)
        if null a1 && null a2 then pure [] else
          (<>) (a1 <> a2) <$> outer ls2 rs2
      where
        one l r = [(l, r)]

    -- 'Nothing' means contradiction
    inner ::
        (Ord x, Ord y, Monoid a) =>
        (x -> y -> Bool) ->
        (x -> y -> a) ->
        Map x Rational -> [(y, Rational)] ->
        Maybe (Map x Rational, Map y Rational, a)
    inner apt mk !ls = \case
        [] -> pure (ls, Map.empty, mempty)

        ri@(r, i) : ris -> case consumes apt ls ri of
            Nothing -> do
                (ls', rs', a) <- inner apt mk ls ris
                pure (ls', Map.insert r i rs', a)
            Just (Balanced matches ls1) -> do
                (ls2, rs', a) <- inner apt mk ls1 ris
                pure (ls2, rs', a <> mconcat [ mk match r | match <- matches ])
            Just Imbalanced ->
                Nothing

    -- 'Nothing' means noncommital
    consumes ::
        (Ord x, Ord y) =>
        (x -> y -> Bool) ->
        Map x Rational -> (y, Rational) ->
        Maybe (Balance x)
    consumes apt ls (r, i) = case compare i tot of
        EQ -> Just $ Balanced (Map.keys ls') $ ls `plusMap` fmap negate ls'
        -- not yet sure which it must match with
        LT -> Nothing
        -- impossible
        GT -> Just Imbalanced
      where
        tot = sum ls'
        ls' = Map.filterWithKey (\l _ -> not $ apt l r) ls
