# Spatial-ring sector interface Lean failure 001

Status: **VERIFIED failure**. No declaration from this run is certified.

## Immutable inputs

- Branch: `codex/spatial-ring-uniformity`.
- Repository SHA elaborated: `5da2453fb24b09be544983f698661d3917119061`.
- Lean: `4.29.0-rc6`, commit `00659f8e6071d7e46131ed643bf8003b99b044e9`.
- Lake: `5.0.0-src+00659f8`.
- Mathlib: `07642720480157414db592fa85b626dafb71355b`.
- Colab UTC start: `2026-07-31T20:35:14.856186+00:00`.
- Runtime: Linux `6.6.122+`, 8 Intel Xeon logical CPUs, `53467192 kB` RAM, Python `3.12.13`, no GPU.
- Elan installer SHA-256: `a620ff1641616222c8d37c54845492004bb84d6877cdbc944dd65c1aa685bf53`.

The repository SHA, toolchain, and Mathlib preregistration checks passed. The official Mathlib cache was obtained only inside the isolated Colab runtime.

## Command and measured result

```text
lake build YangMills.OS.SpatialRing
```

The dependency build reached job `8171/8171`; `YangMills.OS.SpatialRing` then failed with exit code 1. Lean reported exactly five source errors:

1. `SpatialRing.lean:257:68`: the sum expansion in `eucNorm_add_sq_of_orthogonal` left an associativity/distributivity goal.
2. `SpatialRing.lean:267:2`: rewriting the reconstruction identity also rewrote the `evenPart` and `oddPart` terms on the right-hand side.
3. `SpatialRing.lean:336:84`: the analogous global rewrite under `act` rewrote the projected summands again.
4. `SpatialRing.lean:354:4`: `linarith` did not close the norm-square recombination from the two sector inequalities.
5. `SpatialRing.lean:408:4`: the result type left the implicit ring extent of `symWeighted_symm` unresolved, so `DecidableEq (Fin (?m + 1) → Fin 2)` was stuck.

The notebook then raised `RuntimeError: command failed (1): lake build YangMills.OS.SpatialRing`. The oracle, consistency judge, and `YangMillsCore` build did not run. No artifact archive or PASS marker was produced.

## Bounded repair plan

- Expand the Pythagorean sum using only `Finset.sum_add_distrib`, and cancel both cross sums explicitly.
- Replace the two global rewrites by `calc` steps using `congrArg`, so reconstruction is applied only at the intended function argument.
- Prove the combined square inequality by an explicit `calc` chain with `add_le_add` and ring normalization.
- Supply `L := L + 1` to `symWeighted_symm` and type the local kernel `S` explicitly.

The analytic odd- and even-sector obligations remain hypotheses and are not changed by these repairs.
