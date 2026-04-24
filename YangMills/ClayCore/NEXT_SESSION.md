# Next Session: F3 package for `ClusterCorrelatorBound`

## Current Front

The active Clay-critical front is no longer L2.6 / Peter-Weyl.  The
consumer-driven target is:

    ClusterCorrelatorBound N_c r C_clust

The preferred single-object F3 frontier is:

    ShiftedF3MayerCountPackage N_c wab

in `YangMills/ClayCore/ClusterRpowBridge.lean`.

It can be supplied directly, or mechanically assembled from the two independent
frontier halves:

    mayer : ShiftedF3MayerPackage N_c wab
    count : ShiftedF3CountPackage

Supplying either the single package or both halves yields, oracle-clean:

    ClusterCorrelatorBound
    ClayWitnessHyp
    ClayYangMillsMassGap
    ClayConnectedCorrDecay
    ClayYangMillsTheorem

The single package now also exposes its finite-volume consumers directly:

    ShiftedF3MayerCountPackage.toTruncatedActivities
    ShiftedF3MayerCountPackage.wilsonConnectedCorr_eq_toTruncatedActivities_connectingSum
    ShiftedF3MayerCountPackage.apply_count

so downstream code no longer needs to project through `mayerPackage` /
`countPackage` just to obtain the activity, Mayer identity, or bucket-count
inequality.

The small-β terminal form is now named directly in
`YangMills/ClayCore/ZeroMeanCancellation.lean`:

    WilsonUniformRpowBound N_c β C → ClayYangMillsMassGap N_c
    WilsonUniformRpowBound N_c β C → ClayConnectedCorrDecay N_c

Both projections preserve the expected constants:

    mass      = kpParameter β
    prefactor = C

So the remaining terminal analytic target is sharply localized: prove
`WilsonUniformRpowBound N_c β C` from the F3/Mayer package or its preferred
subpackages.

## Exact Remaining Packages

For a fixed `wab : WilsonPolymerActivityBound N_c`, construct:

    structure ShiftedF3MayerPackage
        (N_c : Nat) [NeZero N_c] (wab : WilsonPolymerActivityBound N_c)

with fields:

1. constant `A₀` and positivity proof `hA`;
2. `ConnectedCardDecayMayerData N_c wab.r A₀ wab.hr_pos.le hA.le`.

Separately construct:

    structure ShiftedF3CountPackage

with fields:

1. constants `C_conn`, positivity proof `hC`, and `dim`;
2. `ShiftedConnectingClusterCountBound C_conn dim`.

These combine by:

    ShiftedF3MayerCountPackage.ofSubpackages mayer count

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
        (data.toTruncatedActivities β F p q).connectingSum p q

At package level this is available as:

      ShiftedF3MayerPackage.wilsonConnectedCorr_eq_toTruncatedActivities_connectingSum
      ShiftedF3MayerCountPackage.wilsonConnectedCorr_eq_toTruncatedActivities_connectingSum

What is already closed at the single-plaquette layer:

    singlePlaquetteZ_pos
    plaquetteFluctuationNorm_integrable
    plaquetteFluctuationNorm_mean_zero
    plaquetteFluctuationNorm_zero_beta

These prove the normalized one-plaquette fluctuation is integrable, mean-zero,
and trivial at `β = 0`.  The remaining F3-Mayer work is the product-measure /
polymer lift to `ConnectedCardDecayMayerData`, not the one-plaquette
normalization identity.

The small-β terminal wrapper now consumes the named uniform frontier:

    WilsonUniformRpowBound N_c β C

This is stronger than the looser `WilsonLinkIndependence` predicate, whose
constant is existential per call-site.  The useful Clay-chain input is the
uniform rpow bound.  Supplying it now gives the authentic endpoint

    clayMassGap_small_beta_of_uniformRpow : ClayYangMillsMassGap N_c

with mass `kpParameter β` and prefactor `C`; the weak theorem is just the
projection from that mass-gap object.

### F3-Count

Produce `ShiftedConnectingClusterCountBound C_conn dim`:

    # {Y | p ∈ Y ∧ q ∈ Y ∧ PolymerConnected Y ∧
          Y.card = n + ⌈siteLatticeDist p.site q.site⌉₊}
      ≤ C_conn * (n+1)^dim

under the existing hypotheses

    n ∈ Finset.range (Fintype.card (ConcretePlaquette d L) + 1)
    1 ≤ siteLatticeDist p.site q.site

What is already closed locally:

    shiftedConnectingClusterCountBoundAt_finite
    ShiftedF3CountPackageAt.finite
    ShiftedConnectingClusterCountBound.toAt
    ShiftedF3CountPackage.toAt
    ShiftedF3CountPackage.ofBound
    ShiftedF3CountPackage.apply
    ShiftedF3MayerCountPackage.apply_count

proves the fixed-`d`, fixed-`L` finite-volume version with
`C_conn = Fintype.card (Finset (ConcretePlaquette d L)) + 1` and `dim = 0`.
The remaining F3-count work is the uniform lattice-animal estimate
`ShiftedConnectingClusterCountBound`, not mere finiteness.  A proved global
count package now projects mechanically to every local finite-volume package.

## Preferred Build Checks

After any edit:

    lake build YangMills.ClayCore.ClusterRpowBridge

Key oracle canaries:

    #print axioms clusterCorrelatorBound_of_shiftedF3Subpackages
    #print axioms clayWitnessHyp_of_shiftedF3Subpackages
    #print axioms clayMassGap_of_shiftedF3Subpackages
    #print axioms clayConnectedCorrDecay_of_shiftedF3Subpackages
    #print axioms clay_theorem_of_shiftedF3Subpackages
    #print axioms clusterCorrelatorBound_of_shiftedF3MayerCountPackage
    #print axioms clayWitnessHyp_of_shiftedF3MayerCountPackage
    #print axioms clayMassGap_of_shiftedF3MayerCountPackage
    #print axioms clayConnectedCorrDecay_of_shiftedF3MayerCountPackage
    #print axioms clay_theorem_of_shiftedF3MayerCountPackage
    #print axioms clayMassGap_of_shiftedF3MayerCountPackage_mass_eq
    #print axioms clayMassGap_of_shiftedF3MayerCountPackage_prefactor_eq
    #print axioms ShiftedF3MayerCountPackage.toTruncatedActivities
    #print axioms ShiftedF3MayerCountPackage.wilsonConnectedCorr_eq_toTruncatedActivities_connectingSum
    #print axioms ShiftedF3MayerCountPackage.apply_count
    #print axioms shiftedConnectingClusterCountBoundAt_finite
    #print axioms ShiftedF3CountPackageAt.finite
    #print axioms ShiftedConnectingClusterCountBound.toAt
    #print axioms ShiftedF3CountPackage.toAt
    #print axioms ShiftedF3CountPackage.ofBound
    #print axioms ShiftedF3CountPackage.apply
    #print axioms WilsonUniformRpowBound.apply
    #print axioms plaquetteFluctuationNorm_mean_zero
    #print axioms yang_mills_final_small_beta_of_uniformRpow
    #print axioms clayMassGap_small_beta_of_uniformRpow
    #print axioms clayMassGap_small_beta_of_uniformRpow_mass_eq
    #print axioms clayMassGap_small_beta_of_uniformRpow_prefactor_eq

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
