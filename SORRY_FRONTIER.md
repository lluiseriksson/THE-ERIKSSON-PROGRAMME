# SORRY FRONTIER — THE ERIKSSON PROGRAMME

Last updated: v0.8.28

Two executable sorrys remain. Both are mathematically honest and not eliminable
with the current infrastructure.

---

## 1. `matExp_traceless_det_one`

**File:** `YangMills/Experimental/LieSUN/LieExpCurve.lean`

**Statement:**
```lean
theorem matExp_traceless_det_one
    (X : Matrix (Fin n) (Fin n) ℂ) (htr : X.trace = 0) (t : ℝ) :
    Matrix.det (matExp ((t : ℂ) • X)) = 1
```

**Gap:** Jacobi formula — `det(exp A) = exp(trace A)` is explicit TODO in
`Mathlib.Analysis.Normed.Algebra.MatrixExponential` L57.

**Probe result (v0.8.27):** Mathlib master = `leanprover/lean4:v4.29.0-rc6`
(same as our toolchain — no bump available). Gap is **pinned external**.

**Resolution:** When Mathlib adds `Matrix.det_exp`:
```lean
rw [matExp, Matrix.det_exp, Matrix.trace_smul, htr, smul_zero, Real.exp_zero]
```

**Type:** Mathlib infrastructure gap (irreducible)

---

## 2. `locality_to_static_covariance`

**File:** `YangMills/P8_PhysicalGap/SpatialLocalityFramework.lean`

**Statement:**
```lean
theorem locality_to_static_covariance
    {d : ℕ} (A B : Finset (Site d)) ...
    (hF_loc : IsLocalObservable A F)
    (hG_loc : IsLocalObservable B G) ... :
    |Cov(F,G)| ≤ C · √Var(F) · √Var(G) · exp(-γ · supportDist A B)
```

**Gap:** SZ §4 locality argument — dynamic→static covariance transfer.

`sz_covariance_bridge` gives `|Cov(F, T_t G)| ≤ exp(-γt) · √Var · √Var`.
Evaluating at t=0 gives C=1 with no exponential (pure Cauchy-Schwarz).
The bound `1 ≤ 2·exp(-λ)` requires `λ ≤ ln(2)` — false in general.

**SZ §4 proof route:**
1. `optimalTime A B γ := supportDist A B / γ`
2. Apply `sz_covariance_bridge` at `t*`
3. **Lieb-Robinson bound:** locality gives `Cov(F,G) ≈ Cov(F, T_{t*} G)`
4. Combine → exponential decay in `supportDist A B`

**Next decomposition (v0.8.29):**
- `optimalTime` definition + basic lemmas
- `dynamic_covariance_at_optimalTime` (wraps `sz_covariance_bridge`)
- `local_to_dynamic_covariance` ← the Lieb-Robinson bound (real gap)

**Type:** Mathematical gap (SZ §4 + Lieb-Robinson, requires lattice structure)

---

## Summary

| Sorry | File | Type | Next step |
|-------|------|------|-----------|
| `matExp_traceless_det_one` | LieExpCurve.lean | Mathlib TODO | Wait for `Matrix.det_exp` |
| `locality_to_static_covariance` | SpatialLocalityFramework.lean | SZ §4 gap | v0.8.29: Lieb-Robinson decomposition |
