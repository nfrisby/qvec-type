{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}

-- | Wrappers around the GHC API.

module GHCAPI (module GHCAPI) where

import qualified Coercion
import qualified Finder
import qualified GhcPlugins
import           Outputable (ppr)
import qualified Outputable
import           Panic (panicDoc)
import qualified TcEvidence
import qualified TcPluginM
import qualified TcRnMonad
import           TcRnTypes (Ct, CtEvidence)
import qualified TcRnTypes
import qualified TyCoRep
import qualified TyCon
import           TcType (TcType)
import qualified TcType
import           TcUnify (canSolveByUnification)

import           Plugin.QVec.Types

lookupModule :: String -> TcPluginM.TcPluginM GhcPlugins.Module
lookupModule s = do
    let mod_nm = GhcPlugins.mkModuleName s
        lu = TcPluginM.findImportedModule mod_nm
    lu (Just $ GhcPlugins.fsLit "this") >>= \case
      Finder.Found _ m -> pure m
      _ -> lu Nothing >>= \case
          Finder.Found _ m -> pure m
          _ -> panicDoc "Plugin.QVec initialization could not find Module " $
               ppr mod_nm

lookupTC :: GhcPlugins.Module -> String -> TcPluginM.TcPluginM GhcPlugins.TyCon
lookupTC modul s =
    TcPluginM.lookupOrig modul (GhcPlugins.mkTcOcc s) >>=
    TcPluginM.tcLookupTyCon

lookupDC :: GhcPlugins.TyCon -> String -> TcPluginM.TcPluginM GhcPlugins.DataCon
lookupDC tc s = case dcs of
      [d] -> pure d
      _ -> panicDoc "Plugin.QVec initialization could not find DataCon " (ppr s)
  where
    dcs =
        [ dc
        | dc <- TyCon.tyConDataCons tc
        , GhcPlugins.fsLit s ==
            GhcPlugins.occNameFS (GhcPlugins.occName (GhcPlugins.dataConName dc))
        ]

putSDoc :: Env -> Outputable.SDoc -> TcRnTypes.TcPluginM ()
putSDoc env =
    TcPluginM.tcPluginIO . putStrLn . Outputable.showSDocDump envDynFlags
  where
    MkEnv{..} = env

-- | Plugin equality axiom

pluginCo :: TcType -> TcType -> TyCoRep.Coercion
pluginCo lhs rhs =
    Coercion.mkUnivCo (TyCoRep.PluginProv "qvec-types") TyCon.Nominal lhs rhs

emitNewDerivedEq ::
    TcRnTypes.CtLoc -> TcType -> TcType -> TcRnTypes.TcPluginM Result
emitNewDerivedEq loc lhs rhs = do
    ctev <- TcPluginM.newDerived loc
      (GhcPlugins.mkPrimEqPredRole TyCon.Nominal lhs rhs)
    pure $ emitCt $ TcRnTypes.mkNonCanonical ctev

-- | Check if GHC's constraint solver will certainly solve the given
-- assignment by actually writing to the tyvar
--
-- Suppose we determine that the current constraints imply some new
-- constraint. If we simply emit that new constraint as a new Given or
-- as a new Derived, then we run the risk of causing constraint
-- simplification to diverge. It is only safe to emit a new constraint
-- if we're certain that its existence will (eventually) prevent later
-- invocations of the plugin from emitting an equivalent constraint.
--
-- This function in particular checks if a new equality @v ~ ty@ will
-- cause GHC to unify @v@.

_usefulAssignment :: Env -> TcType.TcTyVar -> TcType -> Bool
_usefulAssignment MkEnv{..} v ty = canSolveByUnification envLevel v ty

emitNewGivenEq ::
    Ct -> TcType -> TcType -> TcRnTypes.TcPluginM Result
emitNewGivenEq ct lhs rhs = do
    new_ev <- deriveGivenEv ct lhs rhs
    pure $ emitCt $ TcRnTypes.mkNonCanonical new_ev

replaceGivenEq ::
    Ct -> TcType -> TcType -> TcRnTypes.TcPluginM Result
replaceGivenEq ct lhs rhs = do
    new_ev <- deriveGivenEv ct lhs rhs
    let new_ct = TcRnTypes.mkNonCanonical new_ev
    pure $ solveGiven ct <> emitCt new_ct

replaceGivenFunEq ::
    Env -> FunEq -> FunApp Tree -> TcRnTypes.TcPluginM Result
replaceGivenFunEq env MkFunEq{..} fat =
    replaceFunEq deriveGivenEv solve fe_ct fe_rhs
      (funAppTyConArgs env fe_kind treeType fat)
  where
    solve _new_ev = solveGiven fe_ct

replaceGivenFunEqFixCoord ::
    Env -> FunEqFixCoord -> (Integer, Integer, TcRnTypes.Xi, QVec) ->
    TcRnTypes.TcPluginM Result
replaceGivenFunEqFixCoord env MkFunEqFixCoord{..} args =
    replaceFunEq deriveGivenEv solve fefc_ct fefc_rhs
      (fixCoordTyConArgs env fefc_kind (cnv args))
  where
    solve _new_ev = solveGiven fefc_ct
    cnv (n, d, e0, zm) = (n, d, e0, treeType env fefc_kind (qVecTree zm))

deriveGivenEv ::
    Ct -> TcType -> TcType ->
    TcRnTypes.TcPluginM CtEvidence
deriveGivenEv ct lhs rhs = do
{- TODO how to keep the old covar alive?
    let new_pty :: TyCoRep.PredType
        new_pty = GhcPlugins.mkPrimEqPredRole TyCon.Nominal lhs rhs

        old_pty :: TyCoRep.PredType
        old_pty = TcRnTypes.ctPred ct

    -- set the new coercion to seq old_co fiat_co
    let evex :: TcEvidence.EvExpr
        evex =
            GhcPlugins.Case scrut bndr new_pty $
            (\x -> [(GhcPlugins.DEFAULT,[],x)]) $
            GhcPlugins.Coercion $
            pluginCo lhs rhs
          where
            scrut = TcRnTypes.ctEvExpr (TcRnTypes.cc_ev ct)
            bndr = GhcPlugins.mkWildValBinder old_pty
-}
    TcPluginM.newGiven
      (TcRnTypes.bumpCtLocDepth (TcRnTypes.ctLoc ct))
      (GhcPlugins.mkPrimEqPredRole TyCon.Nominal lhs rhs)
      (GhcPlugins.Coercion $ pluginCo lhs rhs)

replaceWantedFunEq ::
    Env -> FunEq -> FunApp Tree -> TcRnTypes.TcPluginM Result
replaceWantedFunEq env funeq@MkFunEq{..} fat =
    replaceFunEq deriveWantedEv solve fe_ct fe_rhs
      (funAppTyConArgs env fe_kind treeType fat)
  where
    solve new_ev = solveWantedEq fe_ct
        (funeqType env funeq)
        -- we use the unflattened type instead of the fmv itself,
        -- since we are intentionally updating its definition
        (funAppType env fe_kind treeType fat)
        new_ev

replaceWantedFunEqFixCoord ::
    Env -> FunEqFixCoord -> (Integer, Integer, TcRnTypes.Xi, QVec) -> TcRnTypes.TcPluginM Result
replaceWantedFunEqFixCoord env MkFunEqFixCoord{..} args =
    replaceFunEq deriveWantedEv solve fefc_ct fefc_rhs tcargs
  where
    tcargs = fixCoordTyConArgs env fefc_kind (cnv1 args)
    cnv1 (n, d, e0, zm) = (n, d, e0, treeType env fefc_kind (qVecTree zm))
    cnv2 (n, d, e0, fa) =
        (toInteger n, toInteger d, e0, funArgType env fefc_kind fa)

    solve new_ev = solveWantedEq fefc_ct
        (fixCoordType env fefc_kind (cnv2 fefc_lhs))
        -- we use the unflattened type instead of the fmv itself,
        -- since we are intentionally updating its definition
        (GhcPlugins.mkTyConApp `uncurry` tcargs)
        new_ev

replaceWantedEq ::
    Ct ->
    TcType -> TcType ->
    TcType -> TcType ->
    TcRnTypes.TcPluginM Result
replaceWantedEq ct old_lhs old_rhs lhs rhs = do
    new_ev <- deriveWantedEv ct lhs rhs
    pure $
      solveWantedEq ct old_lhs old_rhs new_ev <>
      emitCt (TcRnTypes.mkNonCanonical new_ev)

solveWantedEq :: Ct -> TcType -> TcType -> CtEvidence -> Result
solveWantedEq old_ct old_lhs old_rhs _new_ev =
{- TODO how to keep the old covar alive?

    -- set the old coercion to seq new_co fiat_co
    old_ev :: TcEvidence.EvTerm
    old_ev =
        TcEvidence.EvExpr $
        GhcPlugins.Case scrut bndr old_pty $
        (\x -> [(GhcPlugins.DEFAULT,[],x)]) $
        GhcPlugins.Coercion $
        pluginCo lhs rhs
      where
        scrut = TcRnTypes.ctEvExpr new_ev
        bndr = GhcPlugins.mkWildValBinder new_pty
-}

    solveWanted old_ev old_ct
  where
    -- set the old coercion to a fiat_co
    old_ev :: TcEvidence.EvTerm
    old_ev =
        TcEvidence.EvExpr $
        GhcPlugins.Coercion $
        pluginCo old_lhs old_rhs

deriveWantedEv ::
    Ct ->
    TcType -> TcType ->
    TcRnTypes.TcPluginM CtEvidence
deriveWantedEv ct lhs rhs = do
    TcPluginM.newWanted
      (TcRnTypes.bumpCtLocDepth (TcRnTypes.ctLoc ct))
      (GhcPlugins.mkPrimEqPred lhs rhs)

replaceFunEq ::
    ( Ct -> TcType -> TcType ->
      TcRnTypes.TcPluginM CtEvidence
    ) {- ^ create the new evidence -} ->
    ( CtEvidence -> Result
    ) {- ^ solve the old constraint from the new evidence -} ->
    Ct -> TcType.TcTyVar -> (TyCon.TyCon, [TcRnTypes.Xi]) ->
    TcRnTypes.TcPluginM Result
replaceFunEq deriveEv solve ct tv (tc, args) = do
    new_ev <- let
      lhs = GhcPlugins.mkTyConApp tc args
      rhs = GhcPlugins.mkTyVarTy tv
      in
      deriveEv ct lhs rhs

    -- If we just use 'TcRnTypes.mkNonCanonical' here, then GHC first
    -- flattens the LHS to create a fresh flatvar, and then introduces
    -- a CTyEqCan. So the original flatvar occurs at least in that new
    -- CTyEqCan but doesn't have its own CFunEqCan.
    --
    -- GHC doesn't fail in that situation (ie it handles such
    -- \"alias\" flatvars0, but it is needless noise, so we do this
    -- instead. GHC still recanonicalizes this CFunEqCan, but without
    -- creating a fresh flatvar that's equivalent to the previous one.
    let new_ct = TcRnTypes.CFunEqCan {
              cc_ev = new_ev
            ,
              cc_fun = tc
            ,
              -- these likely aren't flat, but the GHC canonicalizer
              -- will rectify that right away
              cc_tyargs = args
            ,
              cc_fsk = tv
            }

    pure $ solve new_ev <> emitCt new_ct
