/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import Mathlib
import YangMills.RG.PhysicalGaugeCovarianceLocalization
import YangMills.RG.PhysicalBondDistance

/-!
# Gram-kernel calculus for adjoint compositions on physical cochains
(`hRpoly` campaign — P4-CT, toward owner obligation 2)

The flat physical precision operator is
`K₀ + a•Q†Q − ∑'Σᵢ` with `K₀ = D1†D1 + div†div`: every non-`Sigma` term is
an ADJOINT COMPOSITION `B†B`.  This module proves the transfer lemmas that
turn the PROVED pointwise stencils of `B ∈ {D1, div, Q}` into the
finite-range and kernel-bound hypotheses consumed by the CT2 Schur bound —
without any entrywise adjoint calculus, via the Gram identity

`⟪(B†B δ_p v) q, w⟫ = ⟪B δ_p v, B δ_q w⟫`

and the norm trick `‖y‖² ≤ (M‖v‖)(M‖y‖) ⟹ ‖y‖ ≤ M²‖v‖`:

* `adjointCompSelf_single_inner` — the Gram identity on single-bond probes;
* `adjointCompSelf_finiteRange` — cross-orthogonality of probe images at
  distance `> R` gives `PhysicalCovarianceFiniteRange (B†B) dist R`;
* `adjointCompSelf_kernelBound` — the probe-image bound `‖B δ_p v‖ ≤ M‖v‖`
  gives `PhysicalCovarianceKernelBound (B†B) (fun _ _ => M²)`;
* sum/smul combinators for assembling `K₀ + a•Q†Q` from the three pieces.

**Honest scope.**  Calculus only: the cross-orthogonality and probe-image
bounds for the CONCRETE `D1`, `div`, `Q` at the trivial background (in
`physicalBondDist`, with explicit `R` and `M`) are the next brick — they are
where the actual stencil geometry enters.  Nothing here is a localization
theorem for `flatGaugeFixedPrecisionCLM` yet, and nothing touches `Sigma`,
CT3/CT4, volume uniformity, the root, G5, `hRpoly`, mass gap, or Clay.

Oracle target: `[propext, Classical.choice, Quot.sound]`.  No sorry, no axioms.
-/

namespace YangMills.RG

open scoped RealInnerProductSpace

variable {d N Nc : ℕ} [NeZero N]

/-- Inner product against a single-bond probe extracts the block at that
bond. -/
theorem inner_singlePhysicalBondCochain_right
    (Y : PhysicalGaugeOneCochain d N Nc) (q : PhysicalBond d N)
    (w : SUNLieCoord Nc) :
    inner ℝ Y (singlePhysicalBondCochain (d := d) (N := N) (Nc := Nc) q w) =
      inner ℝ (Y q) w := by
  classical
  rw [PiLp.inner_apply]
  rw [Finset.sum_eq_single q]
  · rw [singlePhysicalBondCochain_self]
  · intro b _ hbq
    rw [singlePhysicalBondCochain_of_ne w hbq, inner_zero_right]
  · intro hq
    exact absurd (Finset.mem_univ q) hq

/-- **The Gram identity on probes**: the `(q,p)` block of `B†B` against a
test vector is the inner product of the two probe images. -/
theorem adjointCompSelf_single_inner
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [CompleteSpace F]
    (B : PhysicalGaugeOneCochain d N Nc →L[ℝ] F)
    (p q : PhysicalBond d N) (v w : SUNLieCoord Nc) :
    inner ℝ ((B.adjoint.comp B)
        (singlePhysicalBondCochain (d := d) (N := N) (Nc := Nc) p v) q) w =
      inner ℝ (B (singlePhysicalBondCochain (d := d) (N := N) (Nc := Nc) p v))
        (B (singlePhysicalBondCochain (d := d) (N := N) (Nc := Nc) q w)) := by
  have h1 : inner ℝ ((B.adjoint.comp B)
      (singlePhysicalBondCochain (d := d) (N := N) (Nc := Nc) p v) q) w =
      inner ℝ ((B.adjoint.comp B)
        (singlePhysicalBondCochain (d := d) (N := N) (Nc := Nc) p v))
        (singlePhysicalBondCochain (d := d) (N := N) (Nc := Nc) q w) :=
    (inner_singlePhysicalBondCochain_right _ q w).symm
  rw [h1, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_left]

/-- **Finite range for adjoint compositions**: if the probe images of `B` at
bonds farther than `R` apart are orthogonal, then `B†B` has kernel range `R`. -/
theorem adjointCompSelf_finiteRange
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [CompleteSpace F]
    (B : PhysicalGaugeOneCochain d N Nc →L[ℝ] F)
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ) {R : ℕ}
    (hdisj : ∀ p q : PhysicalBond d N, ∀ v w : SUNLieCoord Nc,
      R < dist q p →
        inner ℝ (B (singlePhysicalBondCochain (d := d) (N := N) (Nc := Nc) p v))
          (B (singlePhysicalBondCochain (d := d) (N := N) (Nc := Nc) q w)) = 0) :
    PhysicalCovarianceFiniteRange (B.adjoint.comp B) dist R := by
  intro p q v hR
  set y := (B.adjoint.comp B)
    (singlePhysicalBondCochain (d := d) (N := N) (Nc := Nc) p v) q with hy
  have hself : inner ℝ y y = 0 := by
    rw [hy, adjointCompSelf_single_inner]
    exact hdisj p q v _ hR
  exact inner_self_eq_zero.mp hself

/-- **Kernel bound for adjoint compositions**: if every probe image of `B`
has norm at most `M‖v‖`, then the blocks of `B†B` are bounded by `M²‖v‖`
(the `‖y‖² ≤ (M‖v‖)(M‖y‖)` trick — no adjoint entry calculus). -/
theorem adjointCompSelf_kernelBound
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [CompleteSpace F]
    (B : PhysicalGaugeOneCochain d N Nc →L[ℝ] F) {M : ℝ}
    (hM : ∀ p : PhysicalBond d N, ∀ v : SUNLieCoord Nc,
      ‖B (singlePhysicalBondCochain (d := d) (N := N) (Nc := Nc) p v)‖ ≤ M * ‖v‖) :
    PhysicalCovarianceKernelBound (B.adjoint.comp B) (fun _ _ => M ^ 2) := by
  intro p q v
  set y := (B.adjoint.comp B)
    (singlePhysicalBondCochain (d := d) (N := N) (Nc := Nc) p v) q with hy
  have hsq : ‖y‖ ^ 2 ≤ (M * ‖v‖) * (M * ‖y‖) := by
    have hinner : inner ℝ y y =
        inner ℝ (B (singlePhysicalBondCochain (d := d) (N := N) (Nc := Nc) p v))
          (B (singlePhysicalBondCochain (d := d) (N := N) (Nc := Nc) q y)) := by
      rw [hy, adjointCompSelf_single_inner]
    have hCS : inner ℝ (B (singlePhysicalBondCochain (d := d) (N := N) (Nc := Nc) p v))
          (B (singlePhysicalBondCochain (d := d) (N := N) (Nc := Nc) q y))
        ≤ ‖B (singlePhysicalBondCochain (d := d) (N := N) (Nc := Nc) p v)‖ *
          ‖B (singlePhysicalBondCochain (d := d) (N := N) (Nc := Nc) q y)‖ :=
      real_inner_le_norm _ _
    have hb1 := hM p v
    have hb2 := hM q y
    calc ‖y‖ ^ 2 = inner ℝ y y := (real_inner_self_eq_norm_sq y).symm
      _ ≤ ‖B (singlePhysicalBondCochain (d := d) (N := N) (Nc := Nc) p v)‖ *
          ‖B (singlePhysicalBondCochain (d := d) (N := N) (Nc := Nc) q y)‖ := by
          rw [hinner]; exact hCS
      _ ≤ (M * ‖v‖) * (M * ‖y‖) :=
          mul_le_mul hb1 hb2 (norm_nonneg _)
            (le_trans (norm_nonneg _) hb1)
  rcases eq_or_lt_of_le (norm_nonneg y) with hy0 | hy0
  · rw [← hy0]
    positivity
  · have h2 : ‖y‖ * ‖y‖ ≤ (M ^ 2 * ‖v‖) * ‖y‖ := by
      calc ‖y‖ * ‖y‖ = ‖y‖ ^ 2 := (sq ‖y‖).symm
        _ ≤ (M * ‖v‖) * (M * ‖y‖) := hsq
        _ = (M ^ 2 * ‖v‖) * ‖y‖ := by ring
    exact le_of_mul_le_mul_right h2 hy0

/-! ## Mixed adjoint compositions -/

/-- **Mixed Gram identity on probes**: the `(q,p)` block of `B†C` is the
inner product of the `C`-probe at `p` with the `B`-probe at `q`. -/
theorem adjointCompMixed_single_inner
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [CompleteSpace F]
    (B C : PhysicalGaugeOneCochain d N Nc →L[ℝ] F)
    (p q : PhysicalBond d N) (v w : SUNLieCoord Nc) :
    inner ℝ ((B.adjoint.comp C)
        (singlePhysicalBondCochain (d := d) (N := N) (Nc := Nc) p v) q) w =
      inner ℝ (C (singlePhysicalBondCochain
        (d := d) (N := N) (Nc := Nc) p v))
        (B (singlePhysicalBondCochain
          (d := d) (N := N) (Nc := Nc) q w)) := by
  have h1 : inner ℝ ((B.adjoint.comp C)
      (singlePhysicalBondCochain (d := d) (N := N) (Nc := Nc) p v) q) w =
      inner ℝ ((B.adjoint.comp C)
        (singlePhysicalBondCochain (d := d) (N := N) (Nc := Nc) p v))
        (singlePhysicalBondCochain
          (d := d) (N := N) (Nc := Nc) q w) :=
    (inner_singlePhysicalBondCochain_right _ q w).symm
  rw [h1, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_left]

/-- Mixed probe orthogonality transfers to finite range of `B†C`. -/
theorem adjointCompMixed_finiteRange
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [CompleteSpace F]
    (B C : PhysicalGaugeOneCochain d N Nc →L[ℝ] F)
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ) {R : ℕ}
    (hdisj : ∀ p q : PhysicalBond d N, ∀ v w : SUNLieCoord Nc,
      R < dist q p →
        inner ℝ (C (singlePhysicalBondCochain
          (d := d) (N := N) (Nc := Nc) p v))
          (B (singlePhysicalBondCochain
            (d := d) (N := N) (Nc := Nc) q w)) = 0) :
    PhysicalCovarianceFiniteRange (B.adjoint.comp C) dist R := by
  intro p q v hR
  set y := (B.adjoint.comp C)
    (singlePhysicalBondCochain (d := d) (N := N) (Nc := Nc) p v) q with hy
  have hself : inner ℝ y y = 0 := by
    rw [hy, adjointCompMixed_single_inner]
    exact hdisj p q v _ hR
  exact inner_self_eq_zero.mp hself

/-- Probe-image bounds for `B` and `C` give the entrywise mixed bound
`M_C M_B` for `B†C`. -/
theorem adjointCompMixed_kernelBound
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [CompleteSpace F]
    (B C : PhysicalGaugeOneCochain d N Nc →L[ℝ] F)
    {MB MC : ℝ}
    (hMB : 0 ≤ MB) (hMC : 0 ≤ MC)
    (hB : ∀ p : PhysicalBond d N, ∀ v : SUNLieCoord Nc,
      ‖B (singlePhysicalBondCochain
        (d := d) (N := N) (Nc := Nc) p v)‖ ≤ MB * ‖v‖)
    (hC : ∀ p : PhysicalBond d N, ∀ v : SUNLieCoord Nc,
      ‖C (singlePhysicalBondCochain
        (d := d) (N := N) (Nc := Nc) p v)‖ ≤ MC * ‖v‖) :
    PhysicalCovarianceKernelBound
      (B.adjoint.comp C) (fun _ _ => MC * MB) := by
  intro p q v
  set y := (B.adjoint.comp C)
    (singlePhysicalBondCochain (d := d) (N := N) (Nc := Nc) p v) q with hy
  have hsq : ‖y‖ ^ 2 ≤ (MC * ‖v‖) * (MB * ‖y‖) := by
    have hinner : inner ℝ y y =
        inner ℝ (C (singlePhysicalBondCochain
          (d := d) (N := N) (Nc := Nc) p v))
          (B (singlePhysicalBondCochain
            (d := d) (N := N) (Nc := Nc) q y)) := by
      rw [hy, adjointCompMixed_single_inner]
    have hCS : inner ℝ (C (singlePhysicalBondCochain
          (d := d) (N := N) (Nc := Nc) p v))
        (B (singlePhysicalBondCochain
          (d := d) (N := N) (Nc := Nc) q y)) ≤
        ‖C (singlePhysicalBondCochain
          (d := d) (N := N) (Nc := Nc) p v)‖ *
        ‖B (singlePhysicalBondCochain
          (d := d) (N := N) (Nc := Nc) q y)‖ :=
      real_inner_le_norm _ _
    have hc := hC p v
    have hb := hB q y
    calc
      ‖y‖ ^ 2 = inner ℝ y y := (real_inner_self_eq_norm_sq y).symm
      _ ≤ ‖C (singlePhysicalBondCochain
            (d := d) (N := N) (Nc := Nc) p v)‖ *
          ‖B (singlePhysicalBondCochain
            (d := d) (N := N) (Nc := Nc) q y)‖ := by
            rw [hinner]
            exact hCS
      _ ≤ (MC * ‖v‖) * (MB * ‖y‖) :=
        mul_le_mul hc hb (norm_nonneg _)
          (le_trans (norm_nonneg _) hc)
  rcases eq_or_lt_of_le (norm_nonneg y) with hy0 | hy0
  · rw [← hy0]
    positivity
  · have h2 : ‖y‖ * ‖y‖ ≤ (MC * MB * ‖v‖) * ‖y‖ := by
      calc
        ‖y‖ * ‖y‖ = ‖y‖ ^ 2 := (sq ‖y‖).symm
        _ ≤ (MC * ‖v‖) * (MB * ‖y‖) := hsq
        _ = (MC * MB * ‖v‖) * ‖y‖ := by ring
    exact le_of_mul_le_mul_right h2 hy0

/-! ## Assembly combinators -/

/-- Finite range is preserved by sums (at the larger range). -/
theorem physicalCovarianceFiniteRange_add
    {A B : PhysicalGaugeOneCochain d N Nc →L[ℝ] PhysicalGaugeOneCochain d N Nc}
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ) {R : ℕ}
    (hA : PhysicalCovarianceFiniteRange A dist R)
    (hB : PhysicalCovarianceFiniteRange B dist R) :
    PhysicalCovarianceFiniteRange (A + B) dist R := by
  intro p q v hR
  have hsum : (A + B) (singlePhysicalBondCochain (d := d) (N := N) (Nc := Nc) p v) q
      = A (singlePhysicalBondCochain (d := d) (N := N) (Nc := Nc) p v) q
        + B (singlePhysicalBondCochain (d := d) (N := N) (Nc := Nc) p v) q := rfl
  rw [hsum, hA p q v hR, hB p q v hR, add_zero]

/-- Finite range is monotone in the range. -/
theorem physicalCovarianceFiniteRange_mono
    {A : PhysicalGaugeOneCochain d N Nc →L[ℝ] PhysicalGaugeOneCochain d N Nc}
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ) {R R' : ℕ} (hRR' : R ≤ R')
    (hA : PhysicalCovarianceFiniteRange A dist R) :
    PhysicalCovarianceFiniteRange A dist R' := by
  intro p q v hR
  exact hA p q v (lt_of_le_of_lt hRR' hR)

/-- Kernel bounds add over operator sums. -/
theorem physicalCovarianceKernelBound_add
    {A B : PhysicalGaugeOneCochain d N Nc →L[ℝ] PhysicalGaugeOneCochain d N Nc}
    {MA MB : ℝ}
    (hA : PhysicalCovarianceKernelBound A (fun _ _ => MA))
    (hB : PhysicalCovarianceKernelBound B (fun _ _ => MB)) :
    PhysicalCovarianceKernelBound (A + B) (fun _ _ => MA + MB) := by
  intro p q v
  have hsum : (A + B) (singlePhysicalBondCochain (d := d) (N := N) (Nc := Nc) p v) q
      = A (singlePhysicalBondCochain (d := d) (N := N) (Nc := Nc) p v) q
        + B (singlePhysicalBondCochain (d := d) (N := N) (Nc := Nc) p v) q := rfl
  calc ‖(A + B) (singlePhysicalBondCochain (d := d) (N := N) (Nc := Nc) p v) q‖
      = ‖A (singlePhysicalBondCochain (d := d) (N := N) (Nc := Nc) p v) q
          + B (singlePhysicalBondCochain (d := d) (N := N) (Nc := Nc) p v) q‖ := by
        rw [hsum]
    _ ≤ ‖A (singlePhysicalBondCochain (d := d) (N := N) (Nc := Nc) p v) q‖
        + ‖B (singlePhysicalBondCochain (d := d) (N := N) (Nc := Nc) p v) q‖ :=
        norm_add_le _ _
    _ ≤ MA * ‖v‖ + MB * ‖v‖ := add_le_add (hA p q v) (hB p q v)
    _ = (MA + MB) * ‖v‖ := by ring

/-- Finite range is preserved by scalar multiples. -/
theorem physicalCovarianceFiniteRange_smul
    {A : PhysicalGaugeOneCochain d N Nc →L[ℝ] PhysicalGaugeOneCochain d N Nc}
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ) {R : ℕ} (a : ℝ)
    (hA : PhysicalCovarianceFiniteRange A dist R) :
    PhysicalCovarianceFiniteRange (a • A) dist R := by
  intro p q v hR
  have hsm : (a • A) (singlePhysicalBondCochain (d := d) (N := N) (Nc := Nc) p v) q
      = a • A (singlePhysicalBondCochain (d := d) (N := N) (Nc := Nc) p v) q := rfl
  rw [hsm, hA p q v hR, smul_zero]

/-- Kernel bounds scale with scalar multiples. -/
theorem physicalCovarianceKernelBound_smul
    {A : PhysicalGaugeOneCochain d N Nc →L[ℝ] PhysicalGaugeOneCochain d N Nc}
    {MA : ℝ} (a : ℝ)
    (hA : PhysicalCovarianceKernelBound A (fun _ _ => MA)) :
    PhysicalCovarianceKernelBound (a • A) (fun _ _ => |a| * MA) := by
  intro p q v
  have hsm : (a • A) (singlePhysicalBondCochain (d := d) (N := N) (Nc := Nc) p v) q
      = a • A (singlePhysicalBondCochain (d := d) (N := N) (Nc := Nc) p v) q := rfl
  calc ‖(a • A) (singlePhysicalBondCochain (d := d) (N := N) (Nc := Nc) p v) q‖
      = |a| * ‖A (singlePhysicalBondCochain (d := d) (N := N) (Nc := Nc) p v) q‖ := by
        rw [hsm, norm_smul, Real.norm_eq_abs]
    _ ≤ |a| * (MA * ‖v‖) :=
        mul_le_mul_of_nonneg_left (hA p q v) (abs_nonneg a)
    _ = |a| * MA * ‖v‖ := by ring

end YangMills.RG
