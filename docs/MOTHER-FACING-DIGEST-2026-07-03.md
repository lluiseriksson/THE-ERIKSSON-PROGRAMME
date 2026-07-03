# Mother-Facing Interface Digest - 2026-07-03

This digest is an agent handoff, not a mathematical claim.  It records the
current small set of source-facing interfaces that another repo, dashboard, or
agent can consume without changing the theorem boundary.

## Public state checked

- Repository: `lluiseriksson/THE-ERIKSSON-PROGRAMME`
- Default branch: `main`
- Public HEAD checked: `48da3efe6a26af953d33f24c4e5170799eae3e26`
- Latest main CI observed: green, `CI - Epistemic Honesty Enforcement`,
  run `28676354167`
- Latest Pages deployment observed: green, run `28676353821`
- Open PRs observed: none
- Open issues with labels `agent-task`, `blocked`, or `interface-change`:
  none

## Safe consumer interfaces

### Eq. (2.31) source-side gap-cube candidate

- File: `YangMills/RG/BalabanCMP116Eq231.lean`
- Names:
  - `YangMills.RG.cmp116Eq231GapCubesOfY0cStarInteriorBoundary`
  - `YangMills.RG.cmp116Eq231_mem_gapCubesOfY0cStarInteriorBoundary`
  - `YangMills.RG.cmp116Eq231_y0cStarInteriorBoundary_to_gapCubes_of_source`
  - `YangMills.RG.CMP116Eq231PositiveTailOwnershipSource.of_y0cStarInteriorBoundary`
- How to consume: use these as the narrow target for the corrected
  `Y0^{c,*}` / interior / boundary-disjoint route.  They are useful for agents
  trying to connect the source P-family carrier to the existing `gapCubes`
  consumers.
- Hypothesis still live: the primary-source theorem proving that encoded
  P-bonds in `Y0^{c,*}`, interior to `Z0`, and boundary-disjoint have first
  coordinate in `gapCubes`.
- Do not claim: this does not prove the endpoint/base dictionary, the full
  source admissibility equivalence, or the downstream `PBondBoundary`.

### Raw activity decomposition landing pad

- File: `YangMills/RG/YMActivityBudgetUV.lean`
- Names:
  - `YangMills.RG.YMActivityErrorBudget.RawYMActivityDecomposition`
  - `YangMills.RG.YMActivityErrorBudget.RawYMActivityDecomposition.of_components`
  - `YangMills.RG.YMActivityErrorBudget.RawYMActivityDecomposition.of_sum_components_profile`
  - `YangMills.RG.YMActivityErrorBudget.RawYMActivityDecomposition.rawYMActivityDecay`
  - `YangMills.RG.YMActivityErrorBudget.RawYMActivityDecomposition.singleScaleUVDecay_of_tsum_fintype`
  - `YangMills.RG.YMActivityErrorBudget.RawYMActivityDecomposition.singleScaleUVDecay_of_tsum_fintype_sizeCount`
  - `YangMills.RG.YMActivityErrorBudget.RawYMActivityDecomposition.lattice_mass_gap_marginal_of_tsum_fintype`
  - `YangMills.RG.YMActivityErrorBudget.RawYMActivityDecomposition.lattice_mass_gap_marginal_of_tsum_fintype_sizeCount`
- How to consume: provide a finite carrier, an exact scalar identity, the
  source-shaped activity term, and the covariance/dictionary/support/Jacobian
  defect estimates.  The interface discharges finite summability and connects
  the package to the existing single-scale and marginal UV consumers.
- Hypotheses still live: all component estimates, source termwise
  identification, metric-to-weight comparison, and source proof of the actual
  Yang-Mills raw activity bound.
- Do not claim: this is bookkeeping and composition only; it does not prove
  `hRpoly`, the Balaban/Dimock activity estimate, or a continuum theorem.

### Gaussian pushforward source normalization

- File: `YangMills/RG/PhysicalGaugeCMP116ActivityConstruction.lean`
- Names:
  - `PhysicalGaugeCMP116Dictionary.CMP116GaussianCoordinateMapSource`
  - `PhysicalGaugeCMP116Dictionary.CMP116GaussianPhysicalLawSource`
  - `PhysicalGaugeCMP116Dictionary.CMP116GaussianNormalizedPushforwardSource`
  - `PhysicalGaugeCMP116Dictionary.CMP116GaussianPushforwardNormalization`
  - `PhysicalGaugeCMP116Dictionary.CMP116GaussianPushforwardNormalization.of_sourceRecords`
  - `PhysicalGaugeCMP116Dictionary.CMP116GaussianPushforwardNormalization.of_dictionaryRootMap`
  - `PhysicalGaugeCMP116Dictionary.CMP116GaussianPushforwardNormalization.gaussian_pushforward`
- How to consume: split the CMP116 Gaussian normalization into coordinate-map,
  physical-law, and normalized-pushforward records, then feed
  `CMP116GaussianPushforwardNormalization` to localized/raw/scale-family
  consumers.
- Hypotheses still live: the independently specified CMP116 determinant,
  Jacobian, covariance, Hessian, and source Gaussian normalization facts.
- Do not claim: `of_dictionaryRootMap` closes only the definitional convention
  where the downstream physical Gaussian law is defined as the pushforward of
  the dictionary/root map.

## Source-db commands for the next agent

Run these before opening broad source windows:

```powershell
python scripts\source_citations.py blockers
python scripts\source_db.py blockers
python scripts\source_db.py frontier --term eq231 --status lean_linked --limit 8
python scripts\source_db.py frontier --term Cammarota
python scripts\source_db.py head-refs
```

Current high-payoff blockers surfaced by those commands:

- `cammarota.cmp85.polymer-mayer-source-target`: exact theorem, constants,
  hypotheses, and Balaban D-family dictionary still missing.
- `cmp116.eq231.p-family-carrier-source-target`: exact P-family membership and
  eligible bond carrier theorem still missing.
- `cmp109.bond-convention.positive-oriented`: orientation convention still
  needs exact source confirmation for the Eq. (2.31) P-family route.
- `cmp116.lemma3.window.2.14-2.38`: termwise H(Z) summation and D/P/Z0/Z0'
  dictionaries remain OCR/source-corrupted.

## Acceptance boundary

This digest is satisfied if:

1. The file stays documentation-only.
2. `python scripts/check_consistency.py` passes.
3. `python scripts/validate_dashboard.py` passes.
4. No new `sorry`, `axiom`, `admit`, or source theorem claim is introduced.

