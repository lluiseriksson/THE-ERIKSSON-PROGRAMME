# Spatial-ring sector interface Lean failure 002

Status: **VERIFIED failure**. No oracle or core certificate was produced.

## Immutable inputs

- Repository SHA elaborated: `303fe056d73b2cee3e2fac77a9113c7f3b7cdf46`.
- Branch carrying the preregistered notebook: `codex/spatial-ring-uniformity` at `77cdb6ee`.
- Lean: `4.29.0-rc6`, commit `00659f8e6071d7e46131ed643bf8003b99b044e9`.
- Mathlib: `07642720480157414db592fa85b626dafb71355b`.
- Colab UTC start: `2026-07-31T20:44:37.209418+00:00`.
- Runtime: Linux `6.6.122+`, 8 Intel Xeon logical CPUs, `53467192 kB` RAM, Python `3.12.13`, no GPU.

The repository SHA, toolchain, and Mathlib preregistration checks passed. The isolated cache and all dependencies through job `8170/8171` built successfully.

## Command and measured result

```text
lake build YangMills.OS.SpatialRing
```

The four proof failures recorded in `INC-SPATIAL-RING-SECTOR-LEAN-001.md` no longer appeared. Lean reported exactly one error:

```text
YangMills/OS/SpatialRing.lean:445:16: Unknown identifier `tanh_nonneg`
```

The command exited 1, so the notebook stopped before the oracle, consistency judge, core build, archive, or PASS marker.

## Diagnosis and bounded correction

The pinned Mathlib contains `Real.tanh_eq`, `Real.exp_le_exp`, and `Real.exp_pos`, but no lemma named `tanh_nonneg`. For `0 ≤ β`, nonnegativity follows directly from

```text
tanh β = (exp β - exp (-β)) / (exp β + exp (-β)).
```

The repair will replace only the nonexistent lemma call by this explicit numerator/denominator proof. The theorem statement and both sign hypotheses remain unchanged.
