# K4 centred delta–t box candidate (2026-07-21)

This record covers one closed parameter box only:

```text
delta = [1/25, 81/2000]
t     = [11/5, 111/50]
```

The production and replay runs each contain 9,216 terminal cells at 140 Arb
bits. The transcripts are byte-identical and pass
`scripts/validate_surface_remainder_k4_t_box_probe.py`. All seven literal
carrier fractions are strictly below one; the largest is
`MD2r_mirror = 0.503333970406320...`. Both files have SHA-256
`994e62e6cff74680b3ee1168eba326b0f542bbf42e80c16d239c1b282cdf5089`.

The manifest is
`run-manifests/surface-remainder-k4-tbox-delta0040-t220-222-20260721.json`.
This is a `K4_T_BOX_CERTIFIED_CANDIDATE` with promotion `NONE`. It does not
prove a union in `t`, the regular-ball endpoint, overlap, the weighted
S1'''/S2''' judges, or G6. The global theorem and the final seal therefore
remain blocked exactly as required.

The carrier hash changed after the historical centred-band transcripts were
sealed because commit `9bcc7f55` preserves `TJet` inputs. Their validators now
accept the old carrier hash only for the six recorded historical `git_head`
values; current transcripts still require the current dependency hash.
