# Generated point-source Green v2 — cold FAIL at central pair

The retained Colab Pro+ CPU runtime validated exact source checkpoint
`bd89724bbb926da4af507690773f32a84a657ccf` with the official Lean
`v4.29.0-rc6` toolchain and the pinned Mathlib checkout.

The stop-on-first-error queue recorded:

- `point_source_inverse_uniqueness_focal`: exit `0`, `5932.301 s`;
- `point_source_inverse_uniqueness_audit`: exit `0`, `14.360 s`;
- `central_average_pair_nonvanishing_focal`: exit `1`, `46.367 s`.

The first real compiler error is at
`BalabanCMP99SourceFlatQprimePhysicalCentralAveragePairNonvanishing.lean:129:2`:
the proof constructed nonvanishing of the real square before coercion,
`↑(‖A‖ ^ 2) ≠ 0`, while the goal was the square after coercion,
`(↑‖A‖ : ℂ) ^ 2 ≠ 0`.  The repair changes only the proof order to apply
`pow_ne_zero` after `Complex.ofReal_ne_zero`; it changes no theorem statement,
constant, or hypothesis.

The downloaded archive is `evidence.tar.gz` with SHA-256
`1107E82AEDA4F6EB6C56E9F2514B9DF9839D7A983BD63A775A1D0DED146E9427`.
It contains the fail-closed `evidence.json`; the output hash for the failing
stage is
`2870384AF51DC9730119ECD54B90B3335B9002353402C54811A76F690F6C6127`.

This is FAIL evidence, not a compiler seal.  All six PRE-VALIDATION notices
remain, `20/41` is unchanged, and `TermSource = 0` remains exact.
