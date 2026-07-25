# Surface theorem status — Codex audit, 2026-07-25

This is a read-only status record; it does not promote any candidate evidence.

## Independently reproduced

- `audit_surface_g2_relay_admissibility.py`: after fresh terminal production
  and replay, the direct-sign union is continuous from `beta=20` through
  `3313/32`. The remaining authoritative gap is exactly
  `[3313/32,1000/9]`; the relay remains `RELAY_LEMMA_UNPROVED`.
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

## New bounded probe

`probe_surface_h_tail_cauchy_majorant.py` and its two tests reproduce the
registered Cauchy geometry. With `rho=7/100` and `delta_max=1/15`, the exact
geometric multiplier is `16.4540494958...`; therefore the normalized complex
circle supremum would have to satisfy `M < 0.0001680` (the pre-multiplier
`C_4` budget is `<0.0027632`). The finite-order raw bilinear majorant is
`2.5903529741e-12`, but it is unnormalised and still lacks both the omitted
coefficient tail and a joint complex denominator floor. The probe ends with
`NO_H_TAIL_PROMOTION`; it is a diagnostic, not a closure claim.

The new terminal manifests are
`surface-scaled-bulk-cwin3p2-mid24-terminal-20260725.json` (34 units,
7,711 t-rows, `[241/4,275/4]`) and
`surface-scaled-bulk-cwin3p2-post1635-terminal-20260725.json` (five rescue-300
units, 1,848 t-rows, `[1635/16,3313/32]`). All are direct-sign evidence only and
explicitly make no H-tail/G2/G6 promotion. The authoritative audit now sees
475 admissible units and one remaining beta gap, `[3313/32,1000/9]`.

## Seal state

`audit_surface_final_seal.py` remains blocked by the `DO_NOT_SUBMIT` banner,
`G2=BLOCKED`, `G6=BLOCKED`, pending relay language, and an unresolved `[SLOT]`.
The definitive theorem and paper must therefore not be advertised as complete.
