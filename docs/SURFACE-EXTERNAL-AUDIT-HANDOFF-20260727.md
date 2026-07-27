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
