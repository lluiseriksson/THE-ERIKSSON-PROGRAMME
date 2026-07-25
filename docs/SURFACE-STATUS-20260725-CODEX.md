# Surface theorem status — Codex audit, 2026-07-25

This is a read-only status record; it does not promote any candidate evidence.

## Independently reproduced

- `audit_surface_g2_direct_sign_candidate_union.py`: the quarantined candidate
  union is continuous from `beta=20` through `1635/16`; the remaining candidate
  gap is `[1635/16,1000/9]`. The authoritative relay remains
  `RELAY_LEMMA_UNPROVED`.
- `audit_surface_h_tail_cauchy_budget.py`: the required complex supremum is
  still `M_SUPREMUM UNSUPPLIED`; the required threshold is
  `0.002763129991...`.
- `audit_surface_remainder_k4_positive_current_regen.py`: 39 local units and
  89,856 cells pass production/replay byte equality, explicitly candidate-only.
- `audit_surface_remainder_k4_centered_lower_current_regen.py`: 6 local units
  and 55,296 cells pass, explicitly candidate-only.
- `audit_surface_remainder_k4_tbox_current_regen.py`: 15 local units and
  34,560 cells pass, explicitly candidate-only.
- The K4 crude-ball reach diagnostic gives `M_nuD_crude ~= 7.5e321`, so it is
  many orders of magnitude above the registered Cauchy budget and cannot close
  `(H_tail)`.
- The closure-gate tests pass (`9 passed`), but this only verifies that the
  repository refuses premature promotion.

## Seal state

`audit_surface_final_seal.py` remains blocked by the `DO_NOT_SUBMIT` banner,
`G2=BLOCKED`, `G6=BLOCKED`, pending relay language, and an unresolved `[SLOT]`.
The definitive theorem and paper must therefore not be advertised as complete.

