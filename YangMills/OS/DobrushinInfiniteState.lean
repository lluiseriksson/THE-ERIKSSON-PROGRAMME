/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson
-/
import YangMills.OS.DobrushinThermodynamicLimit

/-!
# D-7 — the positive normalized cylinder-state family

This file packages the thermodynamic-limit value as a compatible family of
positive normalized real-linear functionals on centred cylinder
presentations.  It also records two canonicality statements which are useful
independently of the packaging:

* every cofinal schedule of the complete centred-square sequence has the same
  limit;
* changing a Hamiltonian only on rows receding from the support gives the same
  limit, with the explicit Dobrushin error.

No infinite-volume value, Cauchy property, or convergence statement is assumed
by the boundary-perturbation theorem.  Full `ℤ²` translation covariance and a
quotient/direct-limit implementation of the local algebra remain outside the
scope of this file.
-/

namespace YangMills.OS

namespace Dobrushin

open Filter Topology

/-! ## Finite-volume algebra -/

theorem centeredLocalGibbsExpectation_add
    (β γ : ℝ) (r : ℕ)
    (g h : (CenteredRect r → Fin 2) → ℝ) (n : ℕ) :
    centeredLocalGibbsExpectation β γ r (fun η => g η + h η) n =
      centeredLocalGibbsExpectation β γ r g n +
        centeredLocalGibbsExpectation β γ r h n := by
  classical
  unfold centeredLocalGibbsExpectation liftCenteredObservable expect
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro η _
  ring

theorem centeredLocalGibbsExpectation_smul
    (β γ c : ℝ) (r : ℕ)
    (g : (CenteredRect r → Fin 2) → ℝ) (n : ℕ) :
    centeredLocalGibbsExpectation β γ r (fun η => c * g η) n =
      c * centeredLocalGibbsExpectation β γ r g n := by
  classical
  unfold centeredLocalGibbsExpectation liftCenteredObservable expect
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro η _
  ring

theorem centeredLocalGibbsExpectation_one
    (β γ : ℝ) (r n : ℕ) :
    centeredLocalGibbsExpectation β γ r (fun _ => 1) n = 1 := by
  classical
  unfold centeredLocalGibbsExpectation liftCenteredObservable expect
  simpa using gibbsMu_sum_one
    (fun η => isingWeight_pos
      (rectJ (L := 2 * (r + n) + 1) (T := 2 * (r + n) + 1) β γ) η)

theorem centeredLocalGibbsExpectation_nonneg
    (β γ : ℝ) (r : ℕ)
    (g : (CenteredRect r → Fin 2) → ℝ)
    (hg : ∀ η, 0 ≤ g η) (n : ℕ) :
    0 ≤ centeredLocalGibbsExpectation β γ r g n := by
  classical
  unfold centeredLocalGibbsExpectation liftCenteredObservable expect
  exact Finset.sum_nonneg fun η _ =>
    mul_nonneg
      (gibbsMu_nonneg
        (fun ξ => isingWeight_pos
          (rectJ (L := 2 * (r + n) + 1) (T := 2 * (r + n) + 1) β γ) ξ) η)
      (hg _)

/-! ## The limiting functional -/

theorem infiniteCenteredLocalGibbsExpectation_add
    (β γ α : ℝ) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hwin : 2 * Real.tanh |β| + 2 * Real.tanh |γ| ≤ α)
    (r : ℕ) (g h : (CenteredRect r → Fin 2) → ℝ) :
    infiniteCenteredLocalGibbsExpectation β γ α hα0 hα1 hwin r
        (fun η => g η + h η) =
      infiniteCenteredLocalGibbsExpectation β γ α hα0 hα1 hwin r g +
        infiniteCenteredLocalGibbsExpectation β γ α hα0 hα1 hwin r h := by
  have hAdd := tendsto_infiniteCenteredLocalGibbsExpectation
    β γ α hα0 hα1 hwin r (fun η => g η + h η)
  have hSum :=
    (tendsto_infiniteCenteredLocalGibbsExpectation
      β γ α hα0 hα1 hwin r g).add
    (tendsto_infiniteCenteredLocalGibbsExpectation
      β γ α hα0 hα1 hwin r h)
  have heq : ∀ᶠ n in atTop,
      centeredLocalGibbsExpectation β γ r g n +
          centeredLocalGibbsExpectation β γ r h n =
        centeredLocalGibbsExpectation β γ r (fun η => g η + h η) n :=
    Eventually.of_forall fun n =>
      (centeredLocalGibbsExpectation_add β γ r g h n).symm
  exact tendsto_nhds_unique hAdd (hSum.congr' heq)

theorem infiniteCenteredLocalGibbsExpectation_smul
    (β γ α : ℝ) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hwin : 2 * Real.tanh |β| + 2 * Real.tanh |γ| ≤ α)
    (c : ℝ) (r : ℕ) (g : (CenteredRect r → Fin 2) → ℝ) :
    infiniteCenteredLocalGibbsExpectation β γ α hα0 hα1 hwin r
        (fun η => c * g η) =
      c * infiniteCenteredLocalGibbsExpectation β γ α hα0 hα1 hwin r g := by
  have hScalar := tendsto_infiniteCenteredLocalGibbsExpectation
    β γ α hα0 hα1 hwin r (fun η => c * g η)
  have hMul :=
    (tendsto_const_nhds.mul
      (tendsto_infiniteCenteredLocalGibbsExpectation
        β γ α hα0 hα1 hwin r g) :
      Tendsto
        (fun n : ℕ => c * centeredLocalGibbsExpectation β γ r g n)
        atTop
        (𝓝 (c * infiniteCenteredLocalGibbsExpectation
          β γ α hα0 hα1 hwin r g)))
  have heq : ∀ᶠ n in atTop,
      c * centeredLocalGibbsExpectation β γ r g n =
        centeredLocalGibbsExpectation β γ r (fun η => c * g η) n :=
    Eventually.of_forall fun n =>
      (centeredLocalGibbsExpectation_smul β γ c r g n).symm
  exact tendsto_nhds_unique hScalar (hMul.congr' heq)

theorem infiniteCenteredLocalGibbsExpectation_one
    (β γ α : ℝ) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hwin : 2 * Real.tanh |β| + 2 * Real.tanh |γ| ≤ α)
    (r : ℕ) :
    infiniteCenteredLocalGibbsExpectation β γ α hα0 hα1 hwin r
      (fun _ => 1) = 1 := by
  have hLimit := tendsto_infiniteCenteredLocalGibbsExpectation
    β γ α hα0 hα1 hwin r (fun _ => 1)
  have hOne : Tendsto
      (centeredLocalGibbsExpectation β γ r (fun _ => 1))
      atTop (𝓝 1) :=
    (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).congr'
        (Eventually.of_forall fun n =>
          (centeredLocalGibbsExpectation_one β γ r n).symm)
  exact tendsto_nhds_unique hLimit hOne

theorem infiniteCenteredLocalGibbsExpectation_nonneg
    (β γ α : ℝ) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hwin : 2 * Real.tanh |β| + 2 * Real.tanh |γ| ≤ α)
    (r : ℕ) (g : (CenteredRect r → Fin 2) → ℝ)
    (hg : ∀ η, 0 ≤ g η) :
    0 ≤ infiniteCenteredLocalGibbsExpectation
      β γ α hα0 hα1 hwin r g := by
  apply ge_of_tendsto'
    (tendsto_infiniteCenteredLocalGibbsExpectation
      β γ α hα0 hα1 hwin r g)
  exact fun n => centeredLocalGibbsExpectation_nonneg β γ r g hg n

/-! ## Canonicality -/

/-- Every cofinal sampling of the complete sequence converges to the same
value.  This is schedule independence for centred squares, not independence
of shape. -/
theorem tendsto_infiniteCenteredLocalGibbsExpectation_comp
    (β γ α : ℝ) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hwin : 2 * Real.tanh |β| + 2 * Real.tanh |γ| ≤ α)
    (r : ℕ) (g : (CenteredRect r → Fin 2) → ℝ)
    (volume : ℕ → ℕ) (hvolume : Tendsto volume atTop atTop) :
    Tendsto
      (fun n => centeredLocalGibbsExpectation β γ r g (volume n))
      atTop
      (𝓝 (infiniteCenteredLocalGibbsExpectation
        β γ α hα0 hα1 hwin r g)) :=
  (tendsto_infiniteCenteredLocalGibbsExpectation
    β γ α hα0 hα1 hwin r g).comp hvolume

/-- The chosen limit does not depend on which admissible Dobrushin envelope
`α` (or which proofs of its hypotheses) is used to construct it. -/
theorem infiniteCenteredLocalGibbsExpectation_independent_alpha
    (β γ α α' : ℝ)
    (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hwin : 2 * Real.tanh |β| + 2 * Real.tanh |γ| ≤ α)
    (hα0' : 0 ≤ α') (hα1' : α' < 1)
    (hwin' : 2 * Real.tanh |β| + 2 * Real.tanh |γ| ≤ α')
    (r : ℕ) (g : (CenteredRect r → Fin 2) → ℝ) :
    infiniteCenteredLocalGibbsExpectation β γ α hα0 hα1 hwin r g =
      infiniteCenteredLocalGibbsExpectation β γ α' hα0' hα1' hwin' r g :=
  tendsto_nhds_unique
    (tendsto_infiniteCenteredLocalGibbsExpectation
      β γ α hα0 hα1 hwin r g)
    (tendsto_infiniteCenteredLocalGibbsExpectation
      β γ α' hα0' hα1' hwin' r g)

/-- Enlarging the declared support radius and canonically lifting the kernel
does not change the infinite-volume value. -/
theorem infiniteCenteredLocalGibbsExpectation_lift
    (β γ α : ℝ) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hwin : 2 * Real.tanh |β| + 2 * Real.tanh |γ| ≤ α)
    {r s : ℕ} (hrs : r ≤ s)
    (g : (CenteredRect r → Fin 2) → ℝ) :
    infiniteCenteredLocalGibbsExpectation β γ α hα0 hα1 hwin s
        (liftCenteredObservable hrs g) =
      infiniteCenteredLocalGibbsExpectation β γ α hα0 hα1 hwin r g := by
  let small : ℕ → ℝ := centeredLocalGibbsExpectation β γ r g
  let large : ℕ → ℝ := centeredLocalGibbsExpectation β γ s
    (liftCenteredObservable hrs g)
  let M : ℝ := (Fintype.card (CenteredRect r) : ℝ) * osc g
  have hSmall : Tendsto small atTop
      (𝓝 (infiniteCenteredLocalGibbsExpectation
        β γ α hα0 hα1 hwin r g)) :=
    tendsto_infiniteCenteredLocalGibbsExpectation
      β γ α hα0 hα1 hwin r g
  have hLarge : Tendsto large atTop
      (𝓝 (infiniteCenteredLocalGibbsExpectation
        β γ α hα0 hα1 hwin s (liftCenteredObservable hrs g))) :=
    tendsto_infiniteCenteredLocalGibbsExpectation
      β γ α hα0 hα1 hwin s (liftCenteredObservable hrs g)
  have hBound : Tendsto
      (fun n : ℕ => (α ^ n / (1 - α)) * M) atTop (𝓝 0) := by
    have hpow : Tendsto (fun n : ℕ => α ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hα0 hα1
    simpa [div_eq_mul_inv, mul_assoc] using
      hpow.mul_const ((1 - α)⁻¹ * M)
  have hNormError : Tendsto (fun n => ‖large n - small n‖) atTop (𝓝 0) := by
    exact squeeze_zero'
      (Eventually.of_forall fun _ => norm_nonneg _)
      (Eventually.of_forall fun n => by
        have hcmp := centered_local_observable_comparison
          β γ α hα0 hα1 hwin
          (r := r) (n := r + n) (m := s + n)
          (Nat.le_add_right r n) (Nat.add_le_add_right hrs n) g
        simpa [small, large, M, centeredLocalGibbsExpectation,
          Real.norm_eq_abs, liftCenteredObservable_comp] using hcmp)
      hBound
  have hError : Tendsto (fun n => large n - small n) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hNormError
  have hzero := tendsto_nhds_unique (hLarge.sub hSmall) hError
  linarith

/-! ## A compatible positive normalized state family -/

structure PositiveNormalizedCenteredCylinderState (r : ℕ) where
  value : ((CenteredRect r → Fin 2) → ℝ) → ℝ
  map_add : ∀ g h, value (fun η => g η + h η) = value g + value h
  map_smul : ∀ c g, value (fun η => c * g η) = c * value g
  map_one : value (fun _ => 1) = 1
  nonneg : ∀ g, (∀ η, 0 ≤ g η) → 0 ≤ value g

instance (r : ℕ) : CoeFun (PositiveNormalizedCenteredCylinderState r)
    (fun _ => ((CenteredRect r → Fin 2) → ℝ) → ℝ) :=
  ⟨PositiveNormalizedCenteredCylinderState.value⟩

structure CompatibleCenteredCylinderStateFamily where
  atRadius : ∀ r, PositiveNormalizedCenteredCylinderState r
  compatible : ∀ {r s} (hrs : r ≤ s) g,
    atRadius s (liftCenteredObservable hrs g) = atRadius r g

noncomputable def infiniteCenteredLocalGibbsStateFamily
    (β γ α : ℝ) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hwin : 2 * Real.tanh |β| + 2 * Real.tanh |γ| ≤ α) :
    CompatibleCenteredCylinderStateFamily where
  atRadius := fun r =>
    { value := infiniteCenteredLocalGibbsExpectation
        β γ α hα0 hα1 hwin r
      map_add := infiniteCenteredLocalGibbsExpectation_add
        β γ α hα0 hα1 hwin r
      map_smul := fun c g => infiniteCenteredLocalGibbsExpectation_smul
        β γ α hα0 hα1 hwin c r g
      map_one := infiniteCenteredLocalGibbsExpectation_one
        β γ α hα0 hα1 hwin r
      nonneg := infiniteCenteredLocalGibbsExpectation_nonneg
        β γ α hα0 hα1 hwin r }
  compatible := infiniteCenteredLocalGibbsExpectation_lift
    β γ α hα0 hα1 hwin

/-! ## Boundary perturbations receding from the support -/

noncomputable def centeredPerturbedGibbsExpectation
    (r : ℕ) (g : (CenteredRect r → Fin 2) → ℝ)
    (K : (n : ℕ) → CenteredRect (r + n) → CenteredRect (r + n) → ℝ)
    (n : ℕ) : ℝ :=
  expect (gibbsMu (isingWeight (K n)))
    (liftCenteredObservable (Nat.le_add_right r n) g)

theorem abs_centeredLocal_sub_perturbed_le
    (β γ α : ℝ) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hwin : 2 * Real.tanh |β| + 2 * Real.tanh |γ| ≤ α)
    (r : ℕ) (g : (CenteredRect r → Fin 2) → ℝ)
    (K : (n : ℕ) → CenteredRect (r + n) → CenteredRect (r + n) → ℝ)
    (hKdiag : ∀ n i, K n i i = 0)
    (hKsymm : ∀ n i j, K n i j = K n j i)
    (D : (n : ℕ) → CenteredRect (r + n) → Prop)
    (hsame : ∀ n i, ¬ D n i → ∀ k,
      rectJ (L := 2 * (r + n) + 1) (T := 2 * (r + n) + 1) β γ i k =
        K n i k)
    (hfar : ∀ n i j, D n i →
      deltaAt j (liftCenteredObservable (Nat.le_add_right r n) g) ≠ 0 →
        n ≤ rectDist j i)
    (n : ℕ) :
    |centeredLocalGibbsExpectation β γ r g n -
        centeredPerturbedGibbsExpectation r g K n| ≤
      (α ^ n / (1 - α)) *
        ((Fintype.card (CenteredRect r) : ℝ) * osc g) := by
  classical
  have hcmp := ising_boundary_comparison
    (rectJ (L := 2 * (r + n) + 1) (T := 2 * (r + n) + 1) β γ)
    (K n) (rectJ_diag β γ) (rectJ_symm β γ)
    (hKdiag n) (hKsymm n) hα0 hα1
    (fun i => le_trans (rectJ_row β γ i) hwin)
    rectDist rectDist_self rectDist_triangle (rectJ_supp β γ)
    (D n) (hsame n)
    (liftCenteredObservable (Nat.le_add_right r n) g) n (hfar n)
  refine hcmp.trans ?_
  apply mul_le_mul_of_nonneg_left
  · exact sum_deltaAt_liftCenteredObservable_le
      (Nat.le_add_right r n) g
  · exact div_nonneg (pow_nonneg hα0 _) (by linarith)

/-- **Boundary-condition stability.**  Any sequence of symmetric
zero-diagonal couplings whose modified rows recede at least linearly from the
fixed support has the same thermodynamic limit as the free rectangles.  The
premises are local row-equality and geometry statements, not a convergence or
Cauchy hypothesis. -/
theorem tendsto_centeredPerturbedGibbsExpectation
    (β γ α : ℝ) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hwin : 2 * Real.tanh |β| + 2 * Real.tanh |γ| ≤ α)
    (r : ℕ) (g : (CenteredRect r → Fin 2) → ℝ)
    (K : (n : ℕ) → CenteredRect (r + n) → CenteredRect (r + n) → ℝ)
    (hKdiag : ∀ n i, K n i i = 0)
    (hKsymm : ∀ n i j, K n i j = K n j i)
    (D : (n : ℕ) → CenteredRect (r + n) → Prop)
    (hsame : ∀ n i, ¬ D n i → ∀ k,
      rectJ (L := 2 * (r + n) + 1) (T := 2 * (r + n) + 1) β γ i k =
        K n i k)
    (hfar : ∀ n i j, D n i →
      deltaAt j (liftCenteredObservable (Nat.le_add_right r n) g) ≠ 0 →
        n ≤ rectDist j i) :
    Tendsto (centeredPerturbedGibbsExpectation r g K) atTop
      (𝓝 (infiniteCenteredLocalGibbsExpectation
        β γ α hα0 hα1 hwin r g)) := by
  let free : ℕ → ℝ := centeredLocalGibbsExpectation β γ r g
  let perturbed : ℕ → ℝ := centeredPerturbedGibbsExpectation r g K
  let M : ℝ := (Fintype.card (CenteredRect r) : ℝ) * osc g
  have hFree : Tendsto free atTop
      (𝓝 (infiniteCenteredLocalGibbsExpectation
        β γ α hα0 hα1 hwin r g)) :=
    tendsto_infiniteCenteredLocalGibbsExpectation
      β γ α hα0 hα1 hwin r g
  have hBound : Tendsto
      (fun n : ℕ => (α ^ n / (1 - α)) * M) atTop (𝓝 0) := by
    have hpow : Tendsto (fun n : ℕ => α ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hα0 hα1
    simpa [div_eq_mul_inv, mul_assoc] using
      hpow.mul_const ((1 - α)⁻¹ * M)
  have hNormError : Tendsto (fun n => ‖free n - perturbed n‖) atTop (𝓝 0) := by
    exact squeeze_zero'
      (Eventually.of_forall fun _ => norm_nonneg _)
      (Eventually.of_forall fun n => by
        simpa [free, perturbed, M, Real.norm_eq_abs] using
          abs_centeredLocal_sub_perturbed_le β γ α hα0 hα1 hwin
            r g K hKdiag hKsymm D hsame hfar n)
      hBound
  have hError : Tendsto (fun n => free n - perturbed n) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hNormError
  have hPerturbed : Tendsto
      (fun n => free n - (free n - perturbed n)) atTop
      (𝓝 (infiniteCenteredLocalGibbsExpectation
        β γ α hα0 hα1 hwin r g - 0)) :=
    hFree.sub hError
  simpa [free, perturbed] using hPerturbed

/-! ## Periodic boundary conditions, concretely -/

/-- Nearest-neighbour adjacency on a finite cyclic coordinate.  The explicit
inequality prevents a one-point coordinate from becoming adjacent to itself. -/
def cyclicNeighbor {N : ℕ} (a b : Fin N) : Prop :=
  a ≠ b ∧
    (Nat.dist a.val b.val = 1 ∨
      (a.val = 0 ∧ b.val + 1 = N) ∨
      (b.val = 0 ∧ a.val + 1 = N))

theorem cyclicNeighbor_comm {N : ℕ} (a b : Fin N) :
    cyclicNeighbor a b ↔ cyclicNeighbor b a := by
  unfold cyclicNeighbor
  rw [Nat.dist_comm]
  tauto

theorem cyclicNeighbor_eq_of_interior {N : ℕ} (a b : Fin N)
    (ha0 : a.val ≠ 0) (haN : a.val + 1 ≠ N) :
    cyclicNeighbor a b ↔ Nat.dist a.val b.val = 1 := by
  unfold cyclicNeighbor
  constructor
  · rintro ⟨_, hdist | hwrap | hwrap⟩
    · exact hdist
    · exact absurd hwrap.1 ha0
    · exact absurd hwrap.2 haN
  · intro hdist
    refine ⟨?_, Or.inl hdist⟩
    intro hab
    subst b
    simp at hdist

/-- The anisotropic nearest-neighbour coupling with periodic wrap-around in
both coordinates. -/
noncomputable def periodicRectJ {L T : ℕ} (β γ : ℝ) :
    (Fin L × Fin T) → (Fin L × Fin T) → ℝ := by
  classical
  exact fun p q =>
    if cyclicNeighbor p.1 q.1 ∧ p.2 = q.2 then β
    else if p.1 = q.1 ∧ cyclicNeighbor p.2 q.2 then γ
    else 0

theorem periodicRectJ_diag {L T : ℕ} (β γ : ℝ) :
    ∀ p, periodicRectJ (L := L) (T := T) β γ p p = 0 := by
  classical
  intro p
  unfold periodicRectJ cyclicNeighbor
  simp

theorem periodicRectJ_symm {L T : ℕ} (β γ : ℝ) :
    ∀ p q, periodicRectJ (L := L) (T := T) β γ p q =
      periodicRectJ (L := L) (T := T) β γ q p := by
  classical
  intro p q
  have hx : cyclicNeighbor p.1 q.1 = cyclicNeighbor q.1 p.1 :=
    propext (cyclicNeighbor_comm p.1 q.1)
  have hy : cyclicNeighbor p.2 q.2 = cyclicNeighbor q.2 p.2 :=
    propext (cyclicNeighbor_comm p.2 q.2)
  simp [periodicRectJ, hx, hy, eq_comm]

/-- The rows on which periodic and free couplings can differ. -/
def centeredBoundaryRow (r n : ℕ) (p : CenteredRect (r + n)) : Prop :=
  p.1.val = 0 ∨ p.1.val + 1 = 2 * (r + n) + 1 ∨
    p.2.val = 0 ∨ p.2.val + 1 = 2 * (r + n) + 1

/-- Away from the four boundary rows, the periodic coupling is exactly the
free rectangular coupling. -/
theorem rectJ_eq_periodicRectJ_of_not_boundary
    (β γ : ℝ) (r n : ℕ) (p : CenteredRect (r + n))
    (hp : ¬ centeredBoundaryRow r n p) (q : CenteredRect (r + n)) :
    rectJ (L := 2 * (r + n) + 1) (T := 2 * (r + n) + 1) β γ p q =
      periodicRectJ (L := 2 * (r + n) + 1) (T := 2 * (r + n) + 1) β γ p q := by
  unfold centeredBoundaryRow at hp
  push_neg at hp
  unfold rectJ periodicRectJ
  rw [cyclicNeighbor_eq_of_interior p.1 q.1 hp.1 hp.2.1,
    cyclicNeighbor_eq_of_interior p.2 q.2 hp.2.2.1 hp.2.2.2]
  by_cases hx : Nat.dist p.1.val q.1.val = 1 ∧ p.2 = q.2
  · simp [hx]
  · by_cases hy : p.1 = q.1 ∧ Nat.dist p.2.val q.2.val = 1 <;>
      simp [hx, hy]

/-- Periodic finite-volume expectation of a fixed centred cylinder
observable. -/
noncomputable def centeredPeriodicGibbsExpectation
    (β γ : ℝ) (r : ℕ) (g : (CenteredRect r → Fin 2) → ℝ) (n : ℕ) : ℝ :=
  centeredPerturbedGibbsExpectation r g
    (fun n => periodicRectJ
      (L := 2 * (r + n) + 1) (T := 2 * (r + n) + 1) β γ) n

/-- **Free-versus-periodic exhaustion independence.**  The complete periodic
sequence converges to the same positive normalized cylinder-state value as
the free centred rectangles, throughout the visible Dobrushin window. -/
theorem tendsto_centeredPeriodicGibbsExpectation
    (β γ α : ℝ) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hwin : 2 * Real.tanh |β| + 2 * Real.tanh |γ| ≤ α)
    (r : ℕ) (g : (CenteredRect r → Fin 2) → ℝ) :
    Tendsto (centeredPeriodicGibbsExpectation β γ r g) atTop
      (𝓝 (infiniteCenteredLocalGibbsExpectation
        β γ α hα0 hα1 hwin r g)) := by
  let K : (n : ℕ) → CenteredRect (r + n) → CenteredRect (r + n) → ℝ :=
    fun n => periodicRectJ
      (L := 2 * (r + n) + 1) (T := 2 * (r + n) + 1) β γ
  have hfar : ∀ n i j, centeredBoundaryRow r n i →
      deltaAt j (liftCenteredObservable (Nat.le_add_right r n) g) ≠ 0 →
        n ≤ rectDist j i := by
    intro n i j hi hδ
    have hj : centeredIn r (r + n) j := by
      by_contra hj
      exact hδ (deltaAt_liftCenteredObservable_eq_zero_of_not_centered
        (Nat.le_add_right r n) g j hj)
    unfold centeredBoundaryRow at hi
    unfold centeredIn at hj
    unfold rectDist Nat.dist
    omega
  have h := tendsto_centeredPerturbedGibbsExpectation
    β γ α hα0 hα1 hwin r g K
    (fun n => periodicRectJ_diag β γ)
    (fun n => periodicRectJ_symm β γ)
    (fun n => centeredBoundaryRow r n)
    (fun n i hi k => rectJ_eq_periodicRectJ_of_not_boundary β γ r n i hi k)
    hfar
  simpa [centeredPeriodicGibbsExpectation, K] using h

end Dobrushin

end YangMills.OS
