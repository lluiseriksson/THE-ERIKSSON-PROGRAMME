# Colab Lean verification record — audit 49, optimal-domain completion

This is an execution record for the source offered to external review, not a
terminal self-certification.

- Date: 2026-08-04
- Visible signed-in account: `lluiseriksson@gmail.com`
- Runtime: Google Colab Pro+, CPU, high-memory; no GPU
- Runtime opened: approximately 20:07 CEST
- Runtime disconnected and deleted: 20:38 CEST
- Elapsed wall time: 31 minutes
- Other active owner sessions: three, left untouched
- Local Windows: no Lean, Lake, oracle, or sustained computation
- Toolchain: Lean `v4.29.0-rc6`
- Mathlib: `07642720480157414db592fa85b626dafb71355b`

Commands and results:

1. `lake build AmosClosure.BesselNegative`
   - success, 8163 jobs; `.olean` materialized
2. `lake build AmosClosure.FractionalOrderOptimal`
   - success, 8167 jobs; `.olean` materialized
3. `lake build AmosClosure`
   - success, 8178 jobs; integrated root `.olean` materialized
4. `lake env lean AmosClosure/Oracle.lean`
   - success; all historical and twelve new registrations printed only
     `[propext, Classical.choice, Quot.sound]`

New registered declarations:

- `summable_besselRealTerm_gt_neg_one`
- `besselIReal_pos_gt_neg_one`
- `besselIReal_recurrence_gt_neg_one`
- `besselIReal_hasDerivAt_gt_neg_one`
- `besselRatioReal_hasDerivAt_gt_neg_one`
- `fractionalBarrierGap_hasDerivAt_ode`
- `besselRatioReal_strictAnti_order`
- `besselRatioReal_fractional_upper_gt_neg_one_of_pos_sum`
- `besselRatioReal_fractional_upper_gt_neg_one_of_sum_eq_zero`
- `exists_fractional_upper_failure_of_sum_neg`
- `besselRatioReal_fractional_upper_all_iff`
- `besselRatioReal_fractional_two_sided`

The notebook tab was closed immediately after deleting the current runtime to
prevent automatic reconnection. No Claude Code, Opus 5, or Fable 5 invocation
was made because a visible `masterythief@gmail.com` session could not be
confirmed.
