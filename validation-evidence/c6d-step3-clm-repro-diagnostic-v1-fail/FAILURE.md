# C6d Step3 CLM repro diagnostic v1 — exact first error

- Source checkpoint: `1b4eaf235013811886948bb466c4f310d1f0be34`
- Parent runner checkpoint: `f16687415761e238897b90b7565a0771ae9e6df3`
- Diagnostic notebook checkpoint: `ca4f0894440d7e675b48c17fdf2ab2257ae8cd3c`
- Diagnostic revision: `c6d-step3-clm-repro-diagnostic-v1`
- Runtime: Colab Pro+ CPU, high RAM (50.99 GiB)
- Opened: `2026-08-27T02:00:26.429784+00:00`
- Closed by runner: `2026-08-27T02:02:28.857083+00:00`
- Failed stage: `00_c6d_step3_clm_extensionality_repro`, exit `1`, 2.800 s

First real compiler error:

```text
tmp/C6dStep3ContinuousLinearMapEquality.repro.lean:27:8:
Tactic `rewrite` failed: Did not find an occurrence of the pattern
⟪↑KU phi, phi⟫ in the target expression
⟪KU phi, phi⟫ - ⟪KV phi, phi⟫ = 0
```

The failure is the explicit coercion boundary between a continuous linear map
and its underlying linear map. The repair replaces `hKU phi phi` and
`hKV phi phi` with the Mathlib bridge `LinearMap.IsSymmetric.apply_clm` in both
the minimal reproduction and the physical source proof. No statement,
hypothesis or physical constant changes.
