# Next Session: F3 package for `ClusterCorrelatorBound`

## Current Front

The active Clay-critical front is no longer L2.6 / Peter-Weyl.  The
consumer-driven target is:

    ClusterCorrelatorBound N_c r C_clust

The preferred single-object F3 frontier is now:

    ShiftedF3MayerCountPackage N_c wab

in `YangMills/ClayCore/ClusterRpowBridge.lean`.

Supplying this one package yields, oracle-clean:

    ClusterCorrelatorBound
    ClayWitnessHyp
    ClayYangMillsMassGap
    ClayConnectedCorrDecay
    ClayYangMillsTheorem

## Exact Remaining Package

For a fixed `wab : WilsonPolymerActivityBound N_c`, construct:

    structure ShiftedF3MayerCountPackage
        (N_c : Nat) [NeZero N_c] (wab : WilsonPolymerActivityBound N_c)

with fields:

1. constants `C_conn`, `A₀`, positivity proofs `hC`, `hA`, and `dim`;
2. `ConnectedCardDecayMayerData N_c wab.r A₀ wab.hr_pos.le hA.le`;
3. `ShiftedConnectingClusterCountBound C_conn dim`.

## Two Mathematical Subtargets

### F3-Mayer

Produce `ConnectedCardDecayMayerData`.

This means:

- raw truncated activity `K`;
- connected-cardinality decay:

      |K β F p q Y| ≤
        if p ∈ Y ∧ q ∈ Y ∧ PolymerConnected Y
          then A₀ * wab.r ^ Y.card else 0

- Mayer/Ursell identity:

      wilsonConnectedCorr ... β F p q =
        (TruncatedActivities.ofConnectedCardDecay ...).connectingSum p q

### F3-Count

Produce `ShiftedConnectingClusterCountBound C_conn dim`:

    # {Y | p ∈ Y ∧ q ∈ Y ∧ PolymerConnected Y ∧
          Y.card = n + ⌈siteLatticeDist p.site q.site⌉₊}
      ≤ C_conn * (n+1)^dim

under the existing hypotheses

    n ∈ Finset.range (Fintype.card (ConcretePlaquette d L) + 1)
    1 ≤ siteLatticeDist p.site q.site

## Preferred Build Checks

After any edit:

    lake build YangMills.ClayCore.ClusterRpowBridge

Key oracle canaries:

    #print axioms clusterCorrelatorBound_of_shiftedF3MayerCountPackage
    #print axioms clayWitnessHyp_of_shiftedF3MayerCountPackage
    #print axioms clayMassGap_of_shiftedF3MayerCountPackage
    #print axioms clayConnectedCorrDecay_of_shiftedF3MayerCountPackage
    #print axioms clay_theorem_of_shiftedF3MayerCountPackage
    #print axioms clayMassGap_of_shiftedF3MayerCountPackage_mass_eq
    #print axioms clayMassGap_of_shiftedF3MayerCountPackage_prefactor_eq

Expected oracle:

    [propext, Classical.choice, Quot.sound]

## Rules

- No `sorry`.
- No new axioms.
- Do not move bars unless a named frontier entry is actually retired.
- Keep `ClayYangMillsTheorem` as a downstream projection only; primary audit
  endpoints are `ClusterCorrelatorBound`, `ClayYangMillsMassGap`, and
  `ClayConnectedCorrDecay`.
- Do not commit `.lake/config/[anonymous]/lakefile.olean.trace`.
