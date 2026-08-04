# Colab Lean verification record — audit 49

This record documents the remote verification of the exact local source later
included in the final frozen body.  It is an execution record, not a terminal
independent certification.

- Date: 2026-08-04
- Visible signed-in account: `lluiseriksson@gmail.com`
- Runtime: Google Colab Pro+, CPU, high-memory; no GPU
- Runtime opened: 2026-08-04 15:42:40 UTC (17:42:40 CEST)
- Runtime disconnected and deleted: 2026-08-04 16:01:33 UTC (18:01:33 CEST)
- Elapsed wall time: 18 min 53 s
- Local Windows policy: no Lean, Lake, oracle, or sustained computation was run
  locally

Commands and results:

1. `lake build AmosClosure.AmosBarrierReal`
   - success, 8164 jobs
2. `lake env lean AmosClosure/FractionalOrder.lean`
   - success, no diagnostics
3. `lake build AmosClosure.FractionalOrder`
   - success, 8165 jobs; `.olean` materialized
4. `lake env lean Oracle49.lean`
   - success
   - each of the five audited declarations printed only
     `[propext, Classical.choice, Quot.sound]`

Audited declarations:

- `fractionalBarrierGap_hasDerivAt`
- `fractionalBarrierGap_hasDerivAt_of_touch`
- `fractionalBarrierGap_seed`
- `besselRatioReal_fractional_upper`
- `besselIReal_logDeriv_fractional_lt`

The transient notebook/runtime was closed after the checks.  No Claude Code,
Opus 5, or Fable 5 invocation was made.
