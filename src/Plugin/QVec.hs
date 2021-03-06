{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}

module Plugin.QVec (
  plugin,
  tcPlugin,
  ) where

import           Control.Monad (foldM, guard)
import           Data.Either (partitionEithers)
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.IORef
import           Data.List (intersperse, subsequences)
import           Data.List.NonEmpty (NonEmpty, nonEmpty)
import qualified Data.List.NonEmpty as NE
import           Data.Maybe (maybeToList)
import qualified Data.Set as Set
import           GHC.Real (denominator, numerator)

import qualified GhcPlugins
import           Outputable (($$), (<+>), ppr, text)
import qualified TcPluginM
import qualified TcRnMonad
import           TcRnTypes (Ct, Xi)
import qualified TcRnTypes
import           TcType (TcKind, TcTyVar, TcType)
import           VarEnv
import           VarSet
import qualified Unify
import           UniqSet

import           GHCAPI
import           GHCAPI.DetCmpType (detCmpType)
import           Plugin.QVec.Types

-- | 'tcPlugin' with 'GhcPlugins.purePlugin' set

plugin :: GhcPlugins.Plugin
plugin = GhcPlugins.defaultPlugin
    {
      GhcPlugins.pluginRecompile = GhcPlugins.purePlugin
    ,
      GhcPlugins.tcPlugin = \_opts -> pure tcPlugin
    }

-- | A typechecker plugin for "Data.QVec"

tcPlugin :: TcRnTypes.TcPlugin
tcPlugin = TcRnTypes.TcPlugin
    {
      tcPluginInit
    ,
      tcPluginSolve
    ,
      tcPluginStop
    }

tcPluginInit :: TcPluginM.TcPluginM InitEnv
tcPluginInit = do
    modul <- lookupModule "Data.QVec"
    let luTC = lookupTC modul

    ieDecls <- do
      dQVec <- luTC "QVec"
      let luDC s = GhcPlugins.promoteDataCon <$> lookupDC dQVec s

      dBv1  <- luDC "Bv1"
      dBvN  <- luTC "BvN"
      dBvQ  <- luTC "BvQ"
      dDecr <- luTC ":-"
      dIncr <- luTC ":+"
      dInv  <- luTC "Inv"
      dMnus <- luTC ":-:"
      dNil  <- luDC "Nil"
      dPlus <- luTC ":+:"
      dScN  <- luTC "ScN"
      dScQ  <- luTC "ScQ"

      pure MkDecls{..}

    ieDeclsCoords <- do
      dCoords <- luTC "Coords"
      let luDC s = GhcPlugins.promoteDataCon <$> lookupDC dCoords s

      dConsCoords <- luDC "ConsCoords"
      dNilCoords <- luDC "NilCoords"
      dToCoords <- luTC "ToCoords"

      dSign <- luTC "Sign"
      let luSignDC s = GhcPlugins.promoteDataCon <$> lookupDC dSign s

      dNeg <- luSignDC "Neg"
      dPos <- luSignDC "Pos"

      pure MkDeclsCoords{..}

    ieDeclsFixCoord <- do
      dProved <- luTC "Proved"
      let luDC s = GhcPlugins.promoteDataCon <$> lookupDC dProved s

      dFixCoord <- luTC "FixCoord"
      dMkProved <- luDC "MkProved"

      pure MkDeclsFixCoord{..}

    ieInvocationCount <- TcPluginM.tcPluginIO $ newIORef 0

    pure MkInitEnv{..}

tcPluginSolve ::
    InitEnv ->
    [Ct] -> [Ct] -> [Ct] ->
    TcPluginM.TcPluginM TcRnTypes.TcPluginResult
tcPluginSolve MkInitEnv{..} gs ds ws = do
    envDynFlags <- TcRnTypes.unsafeTcPluginTcM GhcPlugins.getDynFlags
    envLevel <- TcRnTypes.unsafeTcPluginTcM TcRnMonad.getTcLevel
    let envDecls = ieDecls
        envDeclsCoords = ieDeclsCoords
        envDeclsFixCoord = ieDeclsFixCoord
        envInvocationCount = ieInvocationCount
    pluginSolve MkEnv{..} gs ds ws

pluginSolve ::
    Env ->
    [Ct] -> [Ct] -> [Ct] ->
    TcPluginM.TcPluginM TcRnTypes.TcPluginResult
pluginSolve env gs ds ws = do
    let MkEnv{..} = env

    -- show banner
    c <- TcPluginM.tcPluginIO $ do
      x <- readIORef envInvocationCount
      let c = succ x
      writeIORef envInvocationCount $! c
      pure c
    id $
      putSDoc env $
      text $ "========== Plugin Invocation #" <> show c <> " =========="
    putSDoc env $ ppr envLevel
      

    -- show constraints
    id $
      mapM_ (putSDoc env) $
      intersperse (text "---") $
      map ppr $
      filter (not . null) $
      [gs, ds, ws]

    let (gFuneqs, gFuneqsFixCoord, gOthers) = (funeqs, funeqsFixCoord, others)
          where
            Cts{funeqs, funeqsFixCoord, others} = partitionCts env gs
    let (wFuneqs, wFuneqsFixCoord, wOthers) = (funeqs, funeqsFixCoord, others)
          where
            Cts{funeqs, funeqsFixCoord, others} = partitionCts env (ds ++ ws)
        allFuneqs = gFuneqs `plusVarEnv` wFuneqs

    let gFceqEnv = MkFixCoordEqEnv
            {
              fceqFlavor = Given
            ,
              fceqImprove = emitNewGivenEq
            ,
              fceqReplaceEq = \ct _old_lhs _old_rhs lhs rhs ->
                replaceGivenEq ct lhs rhs
            ,
              fceqReplaceFunEq = replaceGivenFunEqFixCoord env
            ,
              fceqSigmas0 = Map.empty
            }

    let gTyEqEnv = MkTyEqEnv
            {
              tyeqFlavor = Given
            ,
              tyeqImprove = emitNewGivenEq
            ,
              tyeqReplace = \ct _old_lhs _old_rhs lhs rhs ->
                replaceGivenEq ct lhs rhs
            }

    let wTyEqEnv = MkTyEqEnv
            {
              tyeqFlavor = Wanted
            ,
              tyeqImprove = \ct lhs rhs ->
                emitNewDerivedEq
                  (TcRnTypes.bumpCtLocDepth $ TcRnTypes.ctLoc ct)
                  lhs rhs
            ,
              tyeqReplace = replaceWantedEq
            }

    let wFceqEnv sigmas0 = MkFixCoordEqEnv
            {
              fceqFlavor = Wanted
            ,
              fceqImprove = \ct lhs rhs -> do
                emitNewDerivedEq
                  (TcRnTypes.bumpCtLocDepth $ TcRnTypes.ctLoc ct)
                  lhs rhs
            ,
              fceqReplaceEq = replaceWantedEq
            ,
              fceqReplaceFunEq = replaceWantedFunEqFixCoord env
            ,
              fceqSigmas0 = sigmas0
            }

    res <- runPipeline $
      Stage (canonicalizeFsks env gs) $
      Stage (simplifyEqualities improveEquality1                   gTyEqEnv env gFuneqs gs) $
      Bind  (simplifyFixCoords gFceqEnv env gFuneqs gFuneqsFixCoord gOthers) $ \gSigmasFixCoord ->
      Stage (simplifyEqualities (improveEquality2 gSigmasFixCoord) gTyEqEnv env gFuneqs gs) $

      Stage (canonicalizeFmvs env allFuneqs ds ws) $
        -- TODO ^^^ handle Derived FunEqs!
      Stage (simplifyEqualities improveEquality1                   wTyEqEnv env allFuneqs ws) $
      Bind  (simplifyFixCoords (wFceqEnv gSigmasFixCoord) env allFuneqs wFuneqsFixCoord wOthers) $ \wSigmasFixCoord ->
        -- TODO ^^^ what if we have ([W] fsk ~ MkProved, [G] FixCoords
        -- ... ~ fsk)? How would we update the *Given* FunEq?
        -- 'simplifyFixCoords' currently just ignores such a @~@ since
        -- we only pass @wFunEqsFixCoord@.
      Stage (simplifyEqualities (improveEquality2 wSigmasFixCoord) wTyEqEnv env allFuneqs ws) $

      Stage (reduceToCoords env allFuneqs ws) $

      Done

    putSDoc env $ ppr res
    pure (tcPluginResult res)

tcPluginStop :: InitEnv -> TcPluginM.TcPluginM ()
tcPluginStop _initEnv = pure ()

data Pipeline =
      Done
    |
      Stage (TcPluginM.TcPluginM Result) Pipeline
    |
      forall a. Bind (TcPluginM.TcPluginM (a, Result)) (a -> Pipeline)

runPipeline :: Pipeline -> TcPluginM.TcPluginM Result
runPipeline = go
  where
    -- TODO should we keep going in order to find contradictions ASAP?
    go = \case
        Done      -> pure mempty
        Stage m k -> do
          r <- m
          if nullResult r then go k else pure r
        Bind m k -> do
          (a, r) <- m
          if nullResult r then go (k a) else pure r

{------------------------------------------------------------------------------
    Simplifying givens
------------------------------------------------------------------------------}

canonicalizeFsks ::
    Env ->
    [Ct] ->
    TcPluginM.TcPluginM Result
canonicalizeFsks env gs = do
    putSDoc env $ text "----- Canonicalizing fsks -----"

    let Cts{funeqs,tyeqs} = partitionCts env gs

    do
      putSDoc env $ ppr (GhcPlugins.nonDetEltsUFM funeqs)
      putSDoc env $ text "---"
      putSDoc env $ ppr (GhcPlugins.nonDetEltsUFM tyeqs)
      putSDoc env $ text "---"

    -- simplify all of the CFunEqs
    do
      foldForM (GhcPlugins.nonDetEltsUFM funeqs) $ \funeq -> do
        let MkFunEq{..} = funeq

        let mbUpdate :: Maybe (QVec, Tree TcTyVar)
            mbUpdate = mkFunEqUpdate env funeqs funeq

        foldForM mbUpdate $ \(zm, tree) -> do
          id $
            putSDoc env $
            text "Canonicalizing fsk" <+> ppr (fe_rhs, fe_kind, zm, tree, dropKind <$> prjTree env funeqs fe_rhs)

          case mkFunEqUpdateCases env fe_kind tree of
            Left t -> do
                -- this fsk canonicalizes to something that's not a
                -- type family application, so we emit a Given fsk ~ T
                -- (CTyEqCan) and also *solve the CFunEq*
                --
                -- ASSUMPTION Such a Given CTyEqCan will always
                -- rewrite all occurrences of the fsk, so it's
                -- harmless to discard the CFunEq in this way.

                -- TODO should we indirect through a new CTyEqCan when
                -- @t@ is a tyvar? Else the new tyvar could be an fsk
                -- that ends up written to the old fsk. That seems
                -- somewhat sloppy but might not be problematic.

                replaceGivenEq fe_ct (GhcPlugins.mkTyVarTy fe_rhs) t

            Right fat -> do
                -- we are replacing this CFunEq with a new CFunEq
                --
                -- This approach is adapted from
                -- TcInteract.shortCutReduction.

                -- the new Given: @lhs ~ fsk (CFunEq)@
                replaceGivenFunEq env funeq fat

{------------------------------------------------------------------------------
    Simplifying wanteds
------------------------------------------------------------------------------}

canonicalizeFmvs :: Env -> VarEnv FunEq -> [Ct] -> [Ct] -> TcPluginM.TcPluginM Result
canonicalizeFmvs env allFuneqs ds ws = do
    putSDoc env $ text "----- Canonicalizing fmvs -----"

    let Cts{funeqs,nonFuneqs,tyeqs} = partitionCts env ws

    do
      putSDoc env $ ppr (GhcPlugins.nonDetEltsUFM funeqs)
      putSDoc env $ text "---"
      putSDoc env $ ppr (GhcPlugins.nonDetEltsUFM tyeqs)
      putSDoc env $ text "---"

    -- simplify the CFunEqs for any fmvs that occur in non-CFunEq
    -- constraints and would currently unflatten to non-canonical
    -- QVec syntactic forms
    do
      let fvs :: VarSet
          fvs =
              GhcPlugins.tyCoVarsOfTypes $
              map TcRnTypes.ctPred (nonFuneqs ++ ds)
      foldForM (nonDetEltsUniqSet fvs) $ \v -> do
        let mbUpdate :: Maybe (FunEq, (QVec, Tree TcTyVar))
            mbUpdate = do
                funeq <- lookupVarEnv funeqs v
                (,) funeq <$> mkFunEqUpdate env allFuneqs funeq

        foldForM mbUpdate $ \(funeq, (zm, tree)) -> do
          let MkFunEq{..} = funeq

          id $
            putSDoc env $
            text "Canonicalizing fmv" <+> ppr (v, fe_kind, zm, tree, dropKind <$> prjTree env allFuneqs v)

          case mkFunEqUpdateCases env fe_kind tree of
            Left t -> do
                -- this fmv canonicalizes to something that's not a
                -- type family application, so we emit a Derived fmv ~
                -- T (CTyEqCan) and also *solve the CFunEq*
                --
                -- ASSUMPTION Such a Derived CTyEqCan will always
                -- rewrite all occurrences of the fmv, so it's
                -- harmless to discard the CFunEq in this way.

                -- TODO should we indirect through a new CTyEqCan when
                -- @t@ is a tyvar? Else the new tyvar could be an fmv
                -- that ends up written to the old fmv. That seems
                -- somewhat sloppy but might not be problematic.

                replaceWantedEq fe_ct
                  (funeqType env funeq) (GhcPlugins.mkTyVarTy fe_rhs)
                  (GhcPlugins.mkTyVarTy fe_rhs) t

            Right fat -> do
                -- we are replacing this CFunEq with a new CFunEq
                --
                -- This approach is adapted from
                -- TcInteract.shortCutReduction.

                -- the new Wanted: @lhs ~ fmv (CFunEq)@
                replaceWantedFunEq env funeq fat

-- | Reduce 'Data.QVec.ToCoords' applications when all the non-zero
-- vector indices can be sorted by 'detCmpType'

reduceToCoords :: Env -> VarEnv FunEq -> [Ct] -> TcPluginM.TcPluginM Result
reduceToCoords env funeqs ws = do
    putSDoc env $ text $ "----- Reducing coords -----"

    let Cts{funeqsCoords} = partitionCts env ws
    
    foldForM (GhcPlugins.nonDetEltsUFM funeqsCoords) $ \funeqCoords -> do
      let MkFunEqCoords{..} = funeqCoords

          mbCoords :: Maybe [(Xi, Rational)]
          mbCoords = (>>= sortBs) $ case fec_lhs of
              FunArgBv1 e -> Just $ singletonQVec e
              FunArgNil   -> Just mempty
              FunArgVar v -> dropKind <$> mkQVec env funeqs emptyVarEnv v

          sortBs :: QVec -> Maybe [(Xi, Rational)]
          sortBs (MkQVec vs bs) = do
              guard $ null vs
              foldM (flip insert) []
                [ (e, q) | (MkNDXi e, q) <- Map.toList bs ]
            where
              -- INVARIANT second argument is deterministically sorted
              insert ::
                  (Xi, Rational) -> [(Xi, Rational)] -> Maybe [(Xi, Rational)]
              insert new = \case
                []       -> Just [new]
                old:olds -> detCmpType (fst new) (fst old) >>= \case
                    LT -> Just $ new : old : olds
                    EQ -> error "impossible!"
                    GT -> (old :) <$> insert new olds

      putSDoc env $ ppr fec_lhs
      case mbCoords of
        Nothing     -> pure mempty
        Just coords -> do
            putSDoc env $
              ppr [ (t, numerator q, denominator q) | (t, q) <- coords ]

            let rhs = foldr cons nil coords
                nil = tycon dNilCoords [fec_kind]
                cons (e, q) acc =
                    tycon dConsCoords [fec_kind, sign, n, d, e, acc]
                  where
                    sign = GhcPlugins.mkTyConTy $ if q < 0 then dNeg else dPos
                    n = nat $ abs $ numerator q
                    d = nat $ abs $ denominator q

            let tv = GhcPlugins.mkTyVarTy fec_rhs
            replaceWantedEq fec_ct
              (funeqCoordsType env funeqCoords) tv
              tv rhs
  where
    MkEnv{..} = env
    MkDeclsCoords{..} = envDeclsCoords

    nat = GhcPlugins.mkNumLitTy . fromIntegral
    tycon = GhcPlugins.mkTyConApp


{------------------------------------------------------------------------------
    Canonicalizing and interacting FixCoord equalities
------------------------------------------------------------------------------}

data FixCoordEqEnv = MkFixCoordEqEnv
    {
      fceqFlavor :: Flavor
    ,
      fceqImprove :: Ct -> TcType -> TcType -> TcPluginM.TcPluginM Result
    ,
      fceqReplaceEq ::
        Ct ->
        TcType -> TcType ->
        TcType -> TcType ->
        TcPluginM.TcPluginM Result
    ,
      fceqReplaceFunEq ::
        FunEqFixCoord ->
        (Integer, Integer, Xi, QVec) ->
        TcPluginM.TcPluginM Result
    ,
      fceqSigmas0 :: Map NDXi (VarEnv QVec)
    }

data Acc_simplifyFixCoords = MkAcc_simplifyFixCoords

  !(Map NDXi (VarEnv QVec))

  -- ^ the work-in-progress substitutions

  ![(Ct, FunEqFixCoord, QVec, Bool)]

  -- ^ the work-in-progress equality constraints
  --
  -- The 'Ct' is a 'TcRnTypes.CTyEqCan' where the LHS is an
  -- application of 'Data.QVec.FixCoord' (hence the 'FunEqFixCoord')
  -- and the RHS is 'Data.QVec.MkProved'.
  --
  -- The 'QVec' already includes all 'FunEqFixCoord' arguments: it is
  -- the vector minus the scaled basis vector.
  --
  -- The 'Bool' indicates whether the underlying 'TcRnTypes.CFunEqCan'
  -- needs to be updated; see the @inner@ loop for details.

simplifyFixCoords ::
    FixCoordEqEnv -> Env -> VarEnv FunEq -> VarEnv FunEqFixCoord -> [Ct] ->
    TcPluginM.TcPluginM (Map NDXi (VarEnv QVec), Result)
simplifyFixCoords fceqEnv env funeqs funeqsFixCoord others = do
    putSDoc env $ text $ "----- Simplifying " <> show fceqFlavor <> " FixCoord eqs -----"

    let eqs =
            [ (ct, funeq, zm, False)
            | ct@TcRnTypes.CTyEqCan{..} <- others
            , (funeq, zm) <- maybeToList $ do
                guard $ cc_rhs `GhcPlugins.eqType` mkProved
                funeq@MkFunEqFixCoord{..} <- lookupVarEnv funeqsFixCoord cc_tyvar
                let (n, d, e0, t) = fefc_lhs
                    constant =
                        scaleQVec (fromIntegral n / fromIntegral d) $
                        singletonQVec e0
                zm <- case t of
                  FunArgBv1 e -> pure $ singletonQVec e
                  FunArgNil   -> pure mempty
                  FunArgVar v -> dropKind <$> mkQVec env funeqs emptyVarEnv v
                pure (funeq, zm `minusQVec` constant)
            ]

    putSDoc env $ ppr eqs

    putSDoc env $ text "---"

    work eqs
  where
    MkFixCoordEqEnv{..} = fceqEnv
    MkEnv{..} = env
    MkDeclsFixCoord{..} = envDeclsFixCoord

    mkProved = GhcPlugins.mkTyConTy dMkProved

    emptyAcc = MkAcc_simplifyFixCoords fceqSigmas0 []

    -- We only do one pass for these reasons:
    --
    -- 0) It's simpler.
    --
    -- 1) We don't want to derive too many improvement equalities at
    --    once, since that can lead to error messages as unhelpful as
    --    @True is not False@.
    --
    -- 2) We intend to eventually generate useful coercions. When one
    --    FixCoord constraint's substitution applies to another
    --    FixCoord constraint, we'll need to record that in the
    --    corresponding coercion. Doing so incrementally will be
    --    easiest if we use the 'Result' to generate the new
    --    constraint right away. (Ultimately, this provides sharing in
    --    the evterms.)
    --
    -- 3) When one Derived or Wanted-Derived FixCoord constraint's
    --    substitution applies to a (different) Wanted-Derived
    --    FixCoord constraint, we'll need to split the latter into its
    --    Wanted and shadow Derived, since Wanteds are not allowed to
    --    (directly) simplify Wanteds. (Such indirect rewriting is the
    --    raison d'être of Derived constraints, since it might reveal
    --    some necessary unifications that then let us simplify/solve
    --    the Wanteds.) This is also simplest via an ASAP 'Result'.
    --
    -- Reasons 2 and 3 wouldn't be a concern if the plugin didn't
    -- handle constraint-constraint interactions. Specifically, we
    -- wouldn't have to do this if not for FixCoord constraints, since
    -- the other constraints that interact are all proper @~@
    -- equalities that GHC's own solver already correctly handles.
    work eqs = do
        -- emit updated constraints or else derived constraints that
        -- will simplify at least one constraint
        r <- firstResultForM inert_eqs $ \(ct, funeq, zm, eqflag) -> do
          putSDoc env $ text "Simplifying" $$ ppr ct $$ ppr funeq $$ ppr zm

          let MkFunEqFixCoord{..} = funeq
              (n, d, e0, fa) = fefc_lhs

          case checkFixCoord env e0 zm of

            FixCoordDecided dec
                | dec -> do
                putSDoc env $ text "Tautology"
                let lhs' =
                        ( toInteger n, toInteger d
                        , e0
                        , funArgType env fefc_kind fa
                        )
                fceqReplaceEq fefc_ct
                  (fixCoordType env fefc_kind lhs')
                  (GhcPlugins.mkTyVarTy fefc_rhs)
                  (GhcPlugins.mkTyVarTy fefc_rhs) mkProved

                | otherwise -> do
                putSDoc env $ text "Contradiction"
                pure $ Result $ TcRnTypes.TcPluginContradiction [ct]

            FixCoordImprovable deqs -> do
                -- TODO simultaneously emitting several derived
                -- equalities for this FixCoord) can lead to
                -- terrible type errors
                putSDoc env $ text "Deriving" <+> ppr (e0, NE.toList deqs)
                foldForM deqs $ \(MkNDXi ei) -> fceqImprove ct e0 ei

            FixCoordStuck n' d' zm' -> do
                -- no actionable conclusion ...
                mwhen eqflag $ do   -- .. but otherwise simplified
                  putSDoc env $ text "Simpler"
                  fceqReplaceFunEq funeq (n', d', e0, zm')

        pure (sigmas, r)
      where
        MkAcc_simplifyFixCoords sigmas inert_eqs =
            foldl snoc emptyAcc eqs

    snoc ::
        Acc_simplifyFixCoords ->
        (Ct, FunEqFixCoord, QVec, Bool) ->
        Acc_simplifyFixCoords
    snoc acc eq = acc'
      where
        MkAcc_simplifyFixCoords sigmas inert_eqs = acc
        (ct, funeq@MkFunEqFixCoord{..}, zm0, eqflag) = eq
        (n, d, e0, _t) = fefc_lhs

        sigma = Map.findWithDefault emptyVarEnv (MkNDXi e0) sigmas
        (hits1, zm1) = substQVec sigma zm0
        hit1 = not $ isEmptyVarSet hits1

        (hits2, zm2) = projectQVec e0 zm1
        hit2 = not $ null hits2

        hit3 = q /= negate (fromIntegral n / fromIntegral d)
          where
            (q, _zm3) = popQVec e0 zm1

        eqflag' =
            eqflag
            || hit1   -- a variable occurrence was eliminated

            || hit2   -- an apart basis vector was eliminated

            || hit3   -- the focused basis vector needs to be
                      -- consolidated into the 'FunEqFixCoord'
                      -- argument

        sigma' = case interpretQVec zm2 of
            Nothing       -> sigma
            Just (v, rhs) -> extendVarEnv sigma v rhs

        acc' = MkAcc_simplifyFixCoords
            (if isEmptyVarEnv sigma' || Wanted == fceqFlavor then sigmas else   -- TODO split WDs
             Map.insert (MkNDXi e0) sigma' sigmas)
            ((ct, funeq, zm2, eqflag') : inert_eqs)

-- | A status about a 'Data.QVec.FixCoord' constraint

data FixCoordStatus =
      FixCoordDecided Bool
    |
      FixCoordImprovable (NonEmpty NDXi)

      -- ^ any solution will require these arguments are each
      -- equivalent to the index argument of the 'Data.QVec.FixCoord'

    |
      FixCoordStuck Integer Integer QVec

      -- ^ the 'Data.QVec.FixCoord' arguments

checkFixCoord ::
    Env -> Xi {- ^ the @e0@ -} ->
    QVec {- ^ the entire equality, including the focused constant -} ->
    FixCoordStatus
checkFixCoord env e0 zm

    -- Recall that zm includes the (-n / d * e0) summand.

    | mempty == zm = FixCoordDecided True

    -- 4) If there are no satisfiable possibilities,
    --    Contradiction.

    | null vs && null sats = FixCoordDecided False

    -- TODO currently do not claim contradictions unless
    -- vs is empty. However, if all the remaining vs have
    -- corresponding BitCoords constraints, then that
    -- bounds what they could possibly contribute, which
    -- means we might be able to find more contradictions

    -- 5) If the i-th bit is set in every satisfiable
    --    possibility, emit a constraint e0 ~ ei.

    | null vs, Just xs <- nonEmpty deqs = FixCoordImprovable xs

    -- TODO
    --
    -- 6) If the i-th bit is clear in every satisfiable
    --    possibility, emit a constraint e0 /~ ei.

 -- null vs && not (null dneqs) -> ...

    | otherwise = FixCoordStuck n' d' zm'
  where
    MkEnv{..} = env
    MkDeclsFixCoord{..} = envDeclsFixCoord

    -- TODO for total completeness, we should technically have another
    -- stage in the plugin pipeline which applies the sigmas to any
    -- FunEqFixCoord, even if that FunEqFixCoord doesn't occur in a
    -- CTyEqCan with a MkProved RHS. I haven't done that yet, because
    -- I don't anticipate it ever being useful. However, if we were to
    -- do that, then this computation of @(n', d', zm')@ likely
    -- belongs there, to be re-used here.

    -- separate the 'QVec' into the arguments of the 'FunEqFixCoord'
    --
    -- > 0 ~ zm
    -- >   iff
    -- > -q_e ~ zm_less_e
    -- >   iff
    -- > n'/d' e ~ zm_less_e
    (n', d', zm') = case compare n1 0 of

        LT -> (negate n1, d1, negateQVec zm_less_e)

        EQ -> (0, 1, zm_less_e)
          -- TODO when to negateQVec in this EQ case? The inversion or
          -- lack thereof might prevent a G from matching a W...
          --
          -- TODO Once we're inverting here, we should also figure out
          -- how to set @eqflag@ when inversion is necessary (ie add
          -- this as @hit4@).

        GT -> (n1, d1, zm_less_e)

      where
        n1 = numerator q1; d1 = denominator q1

        -- -q_e ~ zm_less_e   iff   q1 ~ zm_less_e
        q1 = negate q_e

        -- 0 ~ zm   iff   -q_e ~ zm_less_e
        (q_e, zm_less_e) = popQVec e0 zm
            
    -- Note that @n'@ and @d'@ might be the same as @_n@ and @_d@, but
    -- if so then some other part of the constraint must have changed,
    -- since @eqflag@ is set.

    -- Basic plan for @FixCoord n d e0 (q1 e1 + q2 e2 + ... + qn en)@,
    -- where @e0@ and @ei@ are neither manifestly equal nor manifestly
    -- apart.
    MkQVec vs es = zm'

    -- 1) Explore all 2^n possibilities. Each bit indicates whether
    --    the element type ends up being equivalent to or apart from
    --    e0.
    posss = subsequences (Map.toList es)

    -- 2) Within each possibility, invoke the pure unifier to
    --    determine if the possibility is feasible. It should either
    --    fail (infeasible) or provide an mgu (feasible).

    --    NOTE The possibility with n-many 0s is always feasible
    --    (recall n may itself be 0).

    --    Unify. (I2) says: If (unify t1 t2) = MaybeApart theta and if
    --    some phi exists such that phi(t1) ~ phi(t2), then phi
    --    extends theta.

    --    So MaybeApart indicates a possibility might actually be
    --    infeasible.

    --    TODO how to properly handle each flavor of tyvar?

    --    TODO need to zonk first?

    -- 3) If a feasible possibility's coefficients add up to n / d,
    --    then it's a satisfiable possibility. Feasible possibilities
    --    that don't add up and the unfeasible possibilities are
    --    lumped together as the unsatisfiable possibilities.
    sats =
        [ (mgu, Set.fromList (map fst poss))
        | poss <- posss
        , fromIntegral n' / fromIntegral d' == sum (map snd poss)
        , let poss' = [ ei | (MkNDXi ei, _q) <- poss ]
        , mgu <- case unifyTypes (zip poss' (e0 : tail poss')) of
            Unify.Unifiable mgu -> [mgu]
            _                   -> []
            -- TODO what about Unify.MaybeApart?
        ]

    -- see item 5)
    deqs =
        [ ei
        | (ei, _) <- Map.toList es
        , all (Set.member ei . snd) sats
        ]

{------------------------------------------------------------------------------
    Shared logic
------------------------------------------------------------------------------}

data Flavor = Given | Wanted
  deriving (Eq, Show)

instance GhcPlugins.Outputable Flavor where
  ppr = text . show

mkFunEqUpdateCases ::
    Env -> TcKind -> Tree TcTyVar -> Either TcType (FunApp Tree)
mkFunEqUpdateCases env k tree = case tree of
    TreeBv1{}   -> t
    TreeNil{}   -> t
    TreeFun fat -> Right fat
    TreeVar{}   -> t
  where
    t = Left $ treeType env k tree

mkFunEqUpdate ::
    Env -> VarEnv FunEq -> FunEq -> Maybe (QVec, Tree TcTyVar)
mkFunEqUpdate env funeqs MkFunEq{..} = do
    zm <- dropKind <$> mkQVec env funeqs emptyVarEnv fe_rhs

    let -- what we want the flatvar to unflatten to
        new_tree = qVecTree zm
        -- what the flatvar currently unflattens to
        mb_old_tree = dropKind <$> prjTree env funeqs fe_rhs

    -- only update if we want the unflattening to change
    guard $ Just new_tree /= mb_old_tree

    pure (zm, new_tree)

data TyEqEnv = MkTyEqEnv
    {
      tyeqFlavor :: Flavor
    ,
      tyeqImprove :: Ct -> TcType -> TcType -> TcPluginM.TcPluginM Result
    ,
      tyeqReplace ::
        Ct ->
        TcType -> TcType ->
        TcType -> TcType ->
        TcPluginM.TcPluginM Result
    }

-- | Try to derive equivalences from TyEqs

simplifyEqualities ::
    (TyEqEnv -> Env -> TyEq -> QVec -> TcPluginM.TcPluginM Result) ->
    TyEqEnv -> Env -> VarEnv FunEq -> [Ct] -> TcPluginM.TcPluginM Result
simplifyEqualities improve tyeqEnv env funeqs ws = do
    let MkTyEqEnv{tyeqFlavor} = tyeqEnv

    putSDoc env $ text $ "----- Simplifying " <> show tyeqFlavor <> " eqs -----"

    let Cts{tyeqs} = partitionCts env ws

    foldForM (GhcPlugins.nonDetEltsUFM tyeqs) $ \tyeq -> do
      let MkTyEq{..} = tyeq

          mbQVec :: Maybe QVec
          mbQVec = do
              l <- dropKind <$> mkQVec env funeqs emptyVarEnv te_lhs
              r <- case te_rhs of
                FunArgBv1 e  -> pure $ singletonQVec e
                FunArgNil    -> pure mempty
                FunArgVar v  -> dropKind <$> mkQVec env funeqs emptyVarEnv v
              pure $ minusQVec l r `max` minusQVec r l

      foldForM mbQVec $ \zm -> do
        putSDoc env $ ppr (qVecTree zm)
        improve tyeqEnv env tyeq zm
         
-- | Improve equalities that have vector variables
--
-- Sort the vector variables by ascending absolute multiplicity (and
-- then by @'Ord' 'NDVar'@), and then select the first that is minimal
-- w.r.t 'swapOverTyVars'. Rearrange the equality to be a definition
-- of that variable.
--
-- E.G. @(x :+: y :+: y) ~ z :+ b@ yields @x ~ (z :-: y :-: y :+ b)@,
-- presuming that @x@ precedes @z@ in the @'Ord' 'NDVar'@.
--
-- TODO Favor multiplicities that result in more unitary/integer
-- coefficients?

improveEquality1 ::
    TyEqEnv -> Env -> TyEq -> QVec -> TcPluginM.TcPluginM Result
improveEquality1 MkTyEqEnv{..} env MkTyEq{..} zm@(MkQVec vs _bs) =
    munless (null vs) $
    foldForM (interpretQVec zm) $ \(v, zm') ->
      if v == te_lhs
      then pure mempty
      else do
        let rhs_tree = qVecTree zm'
        let v' = case rhs_tree of
                TreeNil{} -> v
                TreeBv1{} -> v
                TreeFun{} -> antiSwapMasquerade v
                TreeVar{} -> v
        putSDoc env $ text "Rearrange" <+> ppr v' <+> ppr rhs_tree <+> ppr zm
        tyeqReplace te_ct
          (GhcPlugins.mkTyVarTy te_lhs)
          (funArgType env te_kind te_rhs)
          (GhcPlugins.mkTyVarTy v')
          (treeType env te_kind rhs_tree)
  where
    MkEnv{..} = env

-- | Improve equalities that do not have vector variables
--
-- E.G. @(Nil :+ [x] :+ b) ~ (Nil :+ y :+ Maybe a)@ yields @[x] ~ y@
-- and @b ~ Maybe a@.

improveEquality2 ::
    Map NDXi (VarEnv QVec) {- the 'Data.QVec.FixCoord' subst -} ->
    TyEqEnv -> Env -> TyEq -> QVec ->
    TcPluginM.TcPluginM Result
improveEquality2 sigmas MkTyEqEnv{..} env MkTyEq{..} zm0@(MkQVec _ bs0) =
    firstResultForM (Map.keys bs0) $ \(MkNDXi e0) ->
      let sigma = Map.findWithDefault emptyVarEnv (MkNDXi e0) sigmas
          (_, zm1@(MkQVec vs bs)) = substQVec sigma zm0
      in
      mwhen (null vs) $
      if 0 /= sum bs then pure contra else   -- TODO unnecessary check?
      case checkFixCoord env e0 zm1 of
        FixCoordDecided dec     -> munless dec $ pure contra
        FixCoordImprovable deqs -> foldForM deqs $ \(MkNDXi e) -> do
          putSDoc env $
            text "Derived basis equivalence" <+> ppr e0 <+> ppr e
          tyeqImprove te_ct e0 e
        FixCoordStuck{}         -> pure mempty
  where
    contra = Result $ TcRnTypes.TcPluginContradiction [te_ct]

{------------------------------------------------------------------------------
    Partitions constraints
------------------------------------------------------------------------------}

data Cts = Cts
    {
      funeqs :: VarEnv FunEq
    ,
      -- | May contain 'TcRnTypes.CFunEqCan's but not 'FunEq's

      nonFuneqs :: [Ct]
    ,
      funeqsCoords :: VarEnv FunEqCoords
    ,
      funeqsFixCoord :: VarEnv FunEqFixCoord
    ,
      tyeqs :: VarEnv TyEq
    ,
      -- | May contain 'TcRnTypes.CFunEqCan's and 'TcRnTypes.CTyEqCan's
      -- but neither 'FunEq's nor 'TyEq's

      others :: [Ct]
    }

partitionCts :: Env -> [Ct] -> Cts
partitionCts env cts = Cts{..}
  where
    funeqs :: VarEnv FunEq
    funeqs =
        mkVarEnv [ (fe_rhs, funeq) | funeq@MkFunEq{..} <- funeqsL ]

    funeqsCoords :: VarEnv FunEqCoords
    funeqsCoords =
        mkVarEnv
          [ (fec_rhs, funeq) | funeq@MkFunEqCoords{..} <- funeqsCoordsL ]

    funeqsFixCoord :: VarEnv FunEqFixCoord
    funeqsFixCoord =
        mkVarEnv
          [ (fefc_rhs, funeq) | funeq@MkFunEqFixCoord{..} <- funeqsFixCoordL ]

    tyeqs :: VarEnv TyEq
    tyeqs =
        mkVarEnv [ (te_lhs, tyeq) | tyeq@MkTyEq{..} <- tyeqsL ]

    funeqsL :: [FunEq]
    funeqsCoordsL :: [FunEqCoords]
    tyeqsL :: [TyEq]
    nonFuneqs :: [Ct]
    others :: [Ct]
    (funeqsL, nonFuneqs) = partitionEithers
        [ maybe (Right ct) Left $ prjFunEq env ct | ct <- cts]
    funeqsCoordsL =
        [ funeq | ct <- cts, funeq <- maybeToList (prjFunEqCoords env ct) ]
    funeqsFixCoordL =
        [ funeq | ct <- cts, funeq <- maybeToList (prjFunEqFixCoord env ct) ]
    (tyeqsL, others) = partitionEithers
        [ maybe (Right ct) Left $ prjTyEq env ct | ct <- nonFuneqs]
