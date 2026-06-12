# Phase 8 Attack Plan: Physical SU(N) Mass Gap

## Goal

Prove `sun_physical_mass_gap` with 0 axioms and 0 sorrys.
This establishes that 4D SU(N) Yang-Mills has a positive mass gap,
directly addressing the Clay/Jaffe-Witten problem.

## Current state (start of Phase 8)

```
sun_gibbs_dlr_lsi  ← AXIOM (main E26 content)
sz_lsi_to_clustering ← AXIOM (Stroock-Zegarlinski 1992)
clustering_to_spectralGap ← sorry
FeynmanKacFormula ← sorry (will derive from L6_OS)
```

## Milestone M1: Prove Ric_{SU(N)} ≥ N/4

**File:** `P8_PhysicalGap/RicciSUN.lean` (to create)

**Goal:**
```lean
theorem ricci_sun_lower_bound (N : ℕ) (hN : 2 ≤ N) :
    ∀ X : su N, RicciCurvature (biInvariantMetric N) X X ≥
    (N : ℝ) / 4 * ‖X‖^2
```

**Proof strategy:**
1. `su N` has structure constants `f^{abc}` with `Σ_c f^{abc} f^{abd} = N·δ^{cd}`
2. `Ric(X,X) = (1/4) Σ_{a,b} f^{abc}² ‖X^a‖²` (standard Lie group formula)
3. Casimir: `f^{acd}f^{bcd} = N·δ^{ab}` → `Ric = (N/4)·g`
4. Verified for SU(2), SU(3) numerically (P91 ratio=1.00)

**Mathlib tools:** `LieAlgebra.killing_form`, `Matrix.trace`

**Estimated:** 2–4 weeks

---

## Milestone M2: Polymer derivative bounds (A2)

**File:** `P8_PhysicalGap/PolymerBounds.lean` (to create)

**Goal:**
```lean
-- OscBound for the SU(N) effective action
theorem sun_osc_bound (N k : ℕ) (κ : ℝ) (hκ : Real.log 512 < κ) :
    OscBound N k C_osc κ
```

**Proof strategy:**
1. Effective action = Wilson action + polymer remainder R^(k)
2. R^(k)(X) analytic in fluctuation field (Bałaban CMP 116-122)
3. Cauchy estimate: |∂_v R^(k)(X)| ≤ C/â · e^{-κ·d_k(X)}
4. â > 0 uniform in k (Bałaban inductive scheme)

**Dependencies:** `L2_Balaban/RGFlow.lean`, `L4_LargeField/Suppression.lean`

**Estimated:** 4–8 weeks

---

## Milestone M3: DLR-LSI for SU(N)

**File:** `P8_PhysicalGap/DLR_LSI_SUN.lean` (to create)

**Goal:** Replace `sun_gibbs_dlr_lsi` axiom with theorem.

**Proof strategy (E26 chain):**
```
M1 (Ric ≥ N/4)
  → Haar LSI(N/4)  [Bakry-Émery]
  → Holley-Stroock: α_blk = (N/4)·exp(-osc(W_k,B)) > 0  [ω-independent]

M2 (polymer bounds A2)
  → cross-scale Σ D_k < ∞  [E26III]
  → entropy telescoping  [E26I]

+ Horizon Transfer [2602.0046 Gap A]
  → esssup_{G_{k+1}} μ_k(Z_k(B)|G_{k+1}) ≤ exp(-c·p₀(g_k))

+ Yoshida-GZ [2602.0046 Gap C]
  → α₀ = α_blk - 4δ_k > 0  [replaces Dobrushin]

→ DLR-LSI(α*) uniform in Λ', ω  [2602.0073 Main Thm]
```

**Key lemmas to formalize:**
- `holley_stroock_block_sun`: α_blk > 0 for SU(N) block
- `yoshida_gz_sun`: δ_k < α_blk/4 for β ≥ β₀
- `horizon_transfer_sun`: esssup bound from T-operation
- `entropy_telescoping`: standard measure theory

**Estimated:** 8–12 weeks

---

## Milestone M4: Stroock-Zegarlinski theorem

**File:** `P8_PhysicalGap/StroockZegarlinski.lean` (to create)

**Goal:** Replace `sz_lsi_to_clustering` axiom with theorem.

**Source:** Stroock-Zegarlinski, J. Funct. Anal. 101 (1992) 249-285.

**Proof strategy:**
1. LSI(α) → Poincaré inequality (λ₁ ≥ α/2)
2. Poincaré → exponential L²-decay of semigroup
3. L²-decay → pointwise covariance decay
4. Covariance decay = exponential clustering with ξ = 2/α

**Mathlib tools:** `MeasureTheory.Lp`, spectral theory of self-adjoint operators

**Estimated:** 4–6 weeks

---

## Milestone M5: Feynman-Kac formula

**File:** `P8_PhysicalGap/FeynmanKacProof.lean` (to create)

**Goal:** Derive `FeynmanKacFormula` from `L6_OS/OsterwalderSchrader.lean`

**Proof strategy:**
1. OS axioms → time-ordered products via reconstruction
2. Transfer matrix defined via time-slice Gibbs kernel
3. `wilsonConnectedCorr` = connected 2-pt function = ⟨ψ_p, T^n ψ_q⟩_conn
4. The "conn" part subtracts the vacuum contribution P₀

**Dependencies:** `L6_OS/OsterwalderSchrader.lean`, `L4_TransferMatrix/TransferMatrix.lean`

**Estimated:** 4–6 weeks

---

## After M1–M5: Final assembly

```lean
-- P8_PhysicalGap/PhysicalMassGap.lean (upgraded)
theorem sun_physical_mass_gap ... : ∃ m > 0, ... := by
  -- All steps now theorems, 0 axioms, 0 sorrys
  obtain ⟨α*, hα, hLSI⟩ := sun_gibbs_dlr_lsi ...    -- M3 theorem
  obtain ⟨C, ξ, ...⟩    := sz_lsi_to_clustering ...  -- M4 theorem
  obtain hgap            := clustering_to_spectralGap  -- M4
  obtain hFK             := feynmanKac_from_OS ...     -- M5
  exact massGap_from_feynmanKac ...
```

**Result:** Physical Yang-Mills mass gap for 4D SU(N), 0 sorrys, 0 axioms.

---

## Parallel track: Phase 9 (Wightman spec)

While Phase 8 runs, Phase 9 can start on:
- Formalizing OS axioms OS0–OS4 properly in Lean
- OS→Wightman reconstruction
- Connecting Hamiltonian spectral gap to the lattice mass gap

These are independent of Phase 8 and can proceed in parallel.
