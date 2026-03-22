
# AXIOM FRONTIER — THE ERIKSSON PROGRAMME

## Snapshot

* Version: v0.9.31
* Main theorem-side semantic note: `rg_increment_decay_P81` is discharged under current zero-map semantics
* Preferred public P91 lane: corrected multiplicative window `β · (3 · b₀) < 2`
* Remaining main-file `sorry`s: 3
* Status of those 3 `sorry`s: deprecated artifacts on the old P91 route

## Remaining main-file `sorry`s

| File                                                         | Name                                     | Status              |
| ------------------------------------------------------------ | ---------------------------------------- | ------------------- |
| `YangMills/ClayCore/BalabanRG/BalabanCouplingRecursion.lean` | `asymptotic_freedom_implies_beta_growth` | legacy / deprecated |
| `YangMills/ClayCore/BalabanRG/P91DenominatorControl.lean`    | `denominator_pos`                        | legacy / deprecated |
| `YangMills/ClayCore/BalabanRG/P91OnestepDriftSkeleton.lean`  | `uniform_drift_lower_bound_P91`          | legacy / deprecated |

## Active theorem-side public surface

* `P91CorrectedWindowPublicShim.lean`
* `P91UniformDriftWindowDirect.lean`
* `P91CorrectedWindowConsumerPacket.lean`

These are the files intended to carry the corrected P91 public API.

## Semantic frontier

The decisive live mathematical frontier is not the old P91 route anymore. It is:

1. replace `RGBlockingMap := 0` by the explicit Bałaban blocking map,
2. re-prove the P80/P81 contraction corridor with nontrivial RG dynamics,
3. keep the corrected multiplicative-window P91 lane as the coupling interface.

## Audit note

The legacy P91 route is formally certified as too weak by
`YangMills/ClayCore/BalabanRG/P91LegacyRouteCounterexample.lean`.
