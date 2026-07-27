# Surface Theorem — external audit handoff (2026-07-27)

This page is the stable entry point for an independent reviewer while the
closure campaign continues.

## Public review targets

- Branch:
  <https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/tree/codex/maintenance-baseline>
- Diff against `main`:
  <https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/compare/main...codex/maintenance-baseline>
- Closure board:
  <https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/blob/codex/maintenance-baseline/docs/SURFACE-CLOSURE-GATES.md>
- Current status:
  <https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/blob/codex/maintenance-baseline/docs/SURFACE-STATUS-20260725-CODEX.md>
- Moving-seam audit correction:
  <https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/blob/codex/maintenance-baseline/docs/INCIDENT-G2-AUDIT-BETA-HI-20260727.md>
- Exact-union audit correction:
  <https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/blob/codex/maintenance-baseline/docs/INCIDENT-G2-AUDIT-OVERLAP-UNION-20260727.md>
- Gap-repair preregistration:
  <https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/blob/codex/maintenance-baseline/docs/SURFACE-G2-CWIN3P2-RESCUE300-GAP81-86-PREREG-20260727.md>
- Authoritative relay auditor:
  <https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/blob/codex/maintenance-baseline/scripts/audit_surface_g2_relay_admissibility.py>
- Regression for the `beta_hi` seam:
  <https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/blob/codex/maintenance-baseline/tests/test_surface_g2_relay_admissibility.py>
- Candidate-union auditor:
  <https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/blob/codex/maintenance-baseline/scripts/audit_surface_scaled_bulk_candidate_beta_union.py>
- Manuscript source:
  <https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/blob/codex/maintenance-baseline/papers/surface-complete/surface_theorem_complete.tex>
- K2 direct joint-remainder relay:
  <https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/blob/codex/maintenance-baseline/docs/SURFACE-K2-DIRECT-JOINT-RELAY-20260727.md>
- K2 relay algebra audit:
  <https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/blob/codex/maintenance-baseline/scripts/verify_surface_k2_direct_joint_relay.py>
- Finite-beta role relay:
  <https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/blob/codex/maintenance-baseline/docs/SURFACE-FINITE-ROLE-RELAY-20260727.md>
- Finite-beta executable role audit:
  <https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/blob/codex/maintenance-baseline/scripts/audit_surface_finite_role_relay.py>
- K4 global-judge incident:
  <https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/blob/codex/maintenance-baseline/docs/SURFACE-K4-GLOBAL-JUDGE-AUDIT-20260727.md>
- K4 executable global-judge audit:
  <https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/blob/codex/maintenance-baseline/scripts/audit_surface_k4_global_judge.py>
- High-beta G5 lambda-two result:
  <https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/blob/codex/maintenance-baseline/docs/SURFACE-HIGH-BETA-G5-LAMBDA2-RESULT-20260727.md>
- High-beta G5 production/replay validator:
  <https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/blob/codex/maintenance-baseline/scripts/validate_surface_high_beta_g5_lambda2.py>
- Corrected three-block bilinear contract:
  <https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/blob/codex/maintenance-baseline/docs/SURFACE-HIGH-BETA-BILINEAR-RESIDUAL-CONTRACT-20260727.md>
- Exact third-block algebra:
  <https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/blob/codex/maintenance-baseline/scripts/verify_surface_three_block_decomposition.py>
- Certified rest perturbation:
  <https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/blob/codex/maintenance-baseline/scripts/verify_surface_high_beta_rest_perturbation_bound.py>

## Current interpretation

The candidate beta archive reaches `1000/9`.
After correcting the moving-seam check from `beta_lo` to `beta_hi`, the
authoritative audit exposed the old gap `[81,86]`.  All twenty preregistered
rescue-300 units now cover `[81,86]` with independent production/replay
pairs.  The corrected exact-union audit reports one component
`[20,1000/9]`, no rational gaps, and a complete adjacent canonical subcover.
Raw archive adjacency is false only because valid historical boxes overlap.

The separate role audit now combines that union with Theorem A, the exact
direct-sign identity, certified G4 on the left, and certified G5 on the
right.  It proves `E'<0` on the complete finite range
`20<=beta<=1000/9`, `0<t<pi`.  This finite-range promotion does **not**
promote K2, the high-beta half-line, K4, S1'''/S2''', G6, or the manuscript.
The `DO_NOT_SUBMIT` banner and unresolved slots remain deliberate.

The K2 audit has also isolated a manuscript-role correction.  The regular K2
certificate controls the assembled joint remainder `Y=beta*X_main`; it does
not identify or bound the older separately named tail `tau`.  The exact
replacement relay is now executable and shows that the certified joint bound
implies the displayed main-saddle extraction bound with a strictly smaller
budget.  No gate changes until the K2/G5/mirror domain-role audit passes.

The high-beta non-bilinear term is now closed independently.  The exact
algebra audit and a 160-bit Arb sweep prove the stronger bound
`<Phi>-(19/20)<D>>0`, hence `<Phi>/<D>>19/20`, throughout
`beta>=1000/9`, `0<t<=pi-3/(2beta)`.  The executable witness is
`scripts/certify_surface_high_beta_q_half.py`, its short transcript is
`scripts/surface_high_beta_q_half_transcript_20260727.txt`, and the derivation
is recorded in `docs/SURFACE-HIGH-BETA-Q-HALF-20260727.md`.  This does not
silently promote the theorem: the remaining high-beta obligation is the
lower bound on the full-minus-main bilinear correction.

The bilinear correction now has a corrected exact three-block contract.
The first assembly combines only the main and mirror squares and retains
their ratio cancellations.  A second independently checked identity adds
the rest; the existing Abel-layer mass bound proves its total adverse
contribution is below `4.489e-6` uniformly on the high-beta half-line.
This correction explicitly retracts the earlier abbreviation
`main+mirror=full`, which omitted the rest.  In the far zone the pure-mirror
perturbation is below `1e-30`; the remaining analytic obligation is confined
to the two principal-square ratio signs in the near interior.

The direct right-edge G5 campaign has also closed the adjacent strip
`delta in [0,9/1000]`, `lambda in [3/2,2]`: 225/225 cells pass, the
production and replay rows are exactly equal, and the worst `H` lower
endpoint is `0.0200479966588318...`.  This is a genuine strip certificate,
not yet a promotion of the remaining high-beta interior or the final seal.

The historical K4 lane has now been audited against its literal additive
judge.  Summing the 39 current positive-band contributions makes four of
seven S1''' rows exceed one; a separate committed t-box transcript also
printed `PASS` with two local fractions above one.  The tracked t-box emitter
now derives its verdict and exit status from the actual finite `<1`
predicate.  K4 remains unpromoted, its positive-delta union is disjoint from
`delta<=9/1000`, and none of this evidence is used for the live high-beta
bilinear judge.

## Reproduction

```powershell
git clone https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME
Set-Location THE-ERIKSSON-PROGRAMME
git checkout codex/maintenance-baseline
python -m pytest -q tests/test_surface_g2_relay_admissibility.py
python scripts/audit_surface_g2_relay_admissibility.py
python scripts/audit_surface_scaled_bulk_candidate_beta_union.py
python scripts/audit_surface_finite_role_relay.py
python scripts/verify_surface_k2_direct_joint_relay.py
python scripts/audit_surface_k4_global_judge.py
python scripts/validate_surface_high_beta_g5_lambda2.py
python scripts/verify_surface_three_block_decomposition.py
python scripts/verify_surface_high_beta_rest_perturbation_bound.py
python scripts/validate_surface_closure.py
python scripts/audit_surface_final_seal.py
```

The final-seal audit is expected to remain red until the mathematical gates
and manuscript slots are genuinely closed.  A green candidate-union audit is
not evidence of final closure.

## Scope discipline

Review the committed branch, not the local working tree.  The working tree
contains a large amount of historical and unrelated material that is not part
of this handoff.  Every accepted rescue unit has a scoped manifest and exact
production/replay transcript pair; pending local computations are pushed only
after replay and validation pass.
