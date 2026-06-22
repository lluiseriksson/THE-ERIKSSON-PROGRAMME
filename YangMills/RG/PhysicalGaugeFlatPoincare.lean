import YangMills.RG.PhysicalGaugeHodgePoincare

/-!
# Constant-sector flat block control and harmonic-kernel bridge

This module records the exact norm bookkeeping for direction-wise constant
physical one-cochains under the current unscaled full-periodic block map.  It
does not prove the full periodic curl/divergence/block Poincare theorem.
-/

namespace YangMills.RG

open scoped BigOperators RealInnerProductSpace

/-- Every flat harmonic physical one-cochain on the full periodic lattice is
direction-wise constant.

This predicate isolates the missing reverse implication only.  The forward
direction, namely that direction-wise constant fields are flat harmonic, is
already proved by `isFlatHarmonicOneCochain_constantPhysicalGaugeOneCochain`. -/
def FlatHarmonicKernelClassified
    (d N Nc : ℕ)
    [NeZero d] [NeZero N] [NeZero Nc]
    (ρ : SUNAdjointModel Nc) : Prop :=
  ∀ A : PhysicalGaugeOneCochain d N Nc,
    IsFlatHarmonicOneCochain ρ A →
      ∃ v : Fin d → SUNLieCoord Nc,
        A =
          constantPhysicalGaugeOneCochain
            (d := d) (N := N) (Nc := Nc) v

/-- Under the classification bridge, flat harmonic one-cochains are exactly the
direction-wise constant sector. -/
theorem flatHarmonicKernel_eq_constantSector
    {d N Nc : ℕ}
    [NeZero d] [NeZero N] [NeZero Nc]
    (ρ : SUNAdjointModel Nc)
    (hclass : FlatHarmonicKernelClassified d N Nc ρ)
    (A : PhysicalGaugeOneCochain d N Nc) :
    IsFlatHarmonicOneCochain ρ A ↔
      ∃ v : Fin d → SUNLieCoord Nc,
        A =
          constantPhysicalGaugeOneCochain
            (d := d) (N := N) (Nc := Nc) v := by
  constructor
  · exact hclass A
  · rintro ⟨v, rfl⟩
    exact
      isFlatHarmonicOneCochain_constantPhysicalGaugeOneCochain
        (d := d) (N := N) (Nc := Nc) ρ v

/-- Operator-kernel form of `flatHarmonicKernel_eq_constantSector`. -/
theorem flatGaugeHodgeKernel_eq_constantSector
    {d N Nc : ℕ}
    [NeZero d] [NeZero N] [NeZero Nc]
    (ρ : SUNAdjointModel Nc)
    (hclass : FlatHarmonicKernelClassified d N Nc ρ)
    (A : PhysicalGaugeOneCochain d N Nc) :
    flatGaugeHodgeK0CLM d N Nc ρ A = 0 ↔
      ∃ v : Fin d → SUNLieCoord Nc,
        A =
          constantPhysicalGaugeOneCochain
            (d := d) (N := N) (Nc := Nc) v := by
  rw [flatGaugeHodgeK0CLM_eq_zero_iff_isFlatHarmonicOneCochain]
  exact flatHarmonicKernel_eq_constantSector ρ hclass A

/-- If the flat harmonic kernel is classified by direction-wise constants, then
the joint kernel of the flat Hodge operator and the unscaled block constraint is
trivial at each fixed volume. -/
theorem flatJointKernel_trivial_of_harmonicClassification
    {d L N' Nc : ℕ}
    [NeZero d] [NeZero L] [NeZero N'] [NeZero Nc]
    (ρ : SUNAdjointModel Nc)
    (hclass :
      FlatHarmonicKernelClassified d (L * N') Nc ρ)
    (A : FinePhysicalOneCochain d L N' Nc) :
    (flatGaugeHodgeK0CLM d (L * N') Nc ρ A = 0 ∧
      flatBlockConstraintQCLM
        (d := d) (Nc := Nc) L N' A = 0) ↔
      A = 0 := by
  constructor
  · rintro ⟨hK, hQ⟩
    have hharm :
        IsFlatHarmonicOneCochain ρ A :=
      (flatGaugeHodgeK0CLM_eq_zero_iff_isFlatHarmonicOneCochain
        (d := d) (N := L * N') (Nc := Nc) ρ A).mp hK
    obtain ⟨v, rfl⟩ := hclass A hharm
    have hv : v = 0 :=
      (flatConstant_jointKernel_eq_zero_iff
        (d := d) (L := L) (N' := N') (Nc := Nc) ρ v).mp
        ⟨hK, hQ⟩
    subst v
    apply PiLp.ext
    intro b
    simp
  · rintro rfl
    simp

/-- A finite-dimensional three-map Poincare estimate from trivial joint kernel.

This is the abstract fixed-volume compactness step.  The constant is allowed to
depend on the finite-dimensional domain and on the three maps. -/
theorem exists_sq_norm_le_sum_three_sq_of_jointKernel_trivial
    {E F₁ F₂ F₃ : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
    [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
    [NormedAddCommGroup F₃] [NormedSpace ℝ F₃]
    (T₁ : E →L[ℝ] F₁)
    (T₂ : E →L[ℝ] F₂)
    (T₃ : E →L[ℝ] F₃)
    (hjoint :
      ∀ x : E,
        T₁ x = 0 →
        T₂ x = 0 →
        T₃ x = 0 →
        x = 0) :
    ∃ C : ℝ, 0 < C ∧
      ∀ x : E,
        ‖x‖ ^ 2 ≤
          C *
            (‖T₁ x‖ ^ 2 +
              ‖T₂ x‖ ^ 2 +
              ‖T₃ x‖ ^ 2) := by
  let T : E →L[ℝ] (F₁ × F₂) × F₃ :=
    (T₁.prod T₂).prod T₃
  have hTinj : Function.Injective T := by
    intro x y hxy
    have hzero : T (x - y) = 0 := by
      simp [map_sub, hxy]
    have h₁ : T₁ (x - y) = 0 := by
      simpa [T] using congrArg (fun z : (F₁ × F₂) × F₃ => z.1.1) hzero
    have h₂ : T₂ (x - y) = 0 := by
      simpa [T] using congrArg (fun z : (F₁ × F₂) × F₃ => z.1.2) hzero
    have h₃ : T₃ (x - y) = 0 := by
      simpa [T] using congrArg (fun z : (F₁ × F₂) × F₃ => z.2) hzero
    have hsub : x - y = 0 := hjoint (x - y) h₁ h₂ h₃
    exact sub_eq_zero.mp hsub
  have hker : LinearMap.ker T.toLinearMap = ⊥ :=
    LinearMap.ker_eq_bot.mpr hTinj
  obtain ⟨K, _hK, hanti⟩ :=
    T.toLinearMap.exists_antilipschitzWith hker
  refine ⟨(K : ℝ) ^ 2, by positivity, ?_⟩
  intro x
  have hbound : ‖x‖ ≤ (K : ℝ) * ‖T x‖ := by
    simpa using T.bound_of_antilipschitz hanti x
  have hsq : ‖x‖ ^ 2 ≤ ((K : ℝ) * ‖T x‖) ^ 2 := by
    exact
      (sq_le_sq₀ (norm_nonneg _)
        (mul_nonneg (by positivity) (norm_nonneg _))).mpr hbound
  have hTnormsq :
      ‖T x‖ ^ 2 ≤
        ‖T₁ x‖ ^ 2 + ‖T₂ x‖ ^ 2 + ‖T₃ x‖ ^ 2 := by
    simp only [T, ContinuousLinearMap.prod_apply, Prod.norm_def]
    generalize ha : ‖T₁ x‖ = a
    generalize hb : ‖T₂ x‖ = b
    generalize hc : ‖T₃ x‖ = c
    have hmax1 : max a b ^ 2 ≤ a ^ 2 + b ^ 2 := by
      by_cases hab : a ≤ b
      · rw [max_eq_right hab]
        nlinarith [sq_nonneg a]
      · have hba : b ≤ a := le_of_not_ge hab
        rw [max_eq_left hba]
        nlinarith [sq_nonneg b]
    by_cases hmc : max a b ≤ c
    · rw [max_eq_right hmc]
      nlinarith [sq_nonneg a, sq_nonneg b]
    · have hcm : c ≤ max a b := le_of_not_ge hmc
      rw [max_eq_left hcm]
      nlinarith [hmax1, sq_nonneg c]
  calc
    ‖x‖ ^ 2 ≤ ((K : ℝ) * ‖T x‖) ^ 2 := hsq
    _ = (K : ℝ) ^ 2 * ‖T x‖ ^ 2 := by ring
    _ ≤
        (K : ℝ) ^ 2 *
          (‖T₁ x‖ ^ 2 + ‖T₂ x‖ ^ 2 + ‖T₃ x‖ ^ 2) := by
      exact mul_le_mul_of_nonneg_left hTnormsq (sq_nonneg (K : ℝ))

/-- Fixed-volume flat Hodge/block Poincare from trivial joint kernel. -/
theorem exists_flatGaugeHodgeBlockPoincare_of_jointKernel_trivial
    {d L N' Nc : ℕ}
    [NeZero d] [NeZero L] [NeZero N'] [NeZero Nc]
    (ρ : SUNAdjointModel Nc)
    (hjoint :
      ∀ A : FinePhysicalOneCochain d L N' Nc,
        flatGaugeHodgeK0CLM d (L * N') Nc ρ A = 0 →
        flatBlockConstraintQCLM
          (d := d) (Nc := Nc) L N' A = 0 →
        A = 0) :
    ∃ CP : ℝ,
      FlatGaugeHodgePoincare d L N' Nc ρ CP := by
  let D₁ :=
    covariantD1CLM ρ
      (trivialPhysicalGaugeBackground d (L * N') Nc)
  let div :=
    gaugeConstraintQCLM ρ
      (trivialPhysicalGaugeBackground d (L * N') Nc)
  let Q :=
    flatBlockConstraintQCLM
      (d := d) (Nc := Nc) L N'
  have hkernel :
      ∀ A : FinePhysicalOneCochain d L N' Nc,
        D₁ A = 0 →
        div A = 0 →
        Q A = 0 →
        A = 0 := by
    intro A hD₁ hdiv hQ
    apply hjoint A
    · exact
        (flatGaugeHodgeK0CLM_eq_zero_iff_isFlatHarmonicOneCochain
          (d := d) (N := L * N') (Nc := Nc) ρ A).mpr
          ⟨hD₁, hdiv⟩
    · exact hQ
  obtain ⟨CP, hCP, hineq⟩ :=
    exists_sq_norm_le_sum_three_sq_of_jointKernel_trivial D₁ div Q hkernel
  exact
    ⟨CP, flatGaugeHodgePoincare ρ hCP (by
      simpa only [D₁, div, Q] using hineq)⟩

/-- Classification-dependent fixed-volume flat Hodge/block Poincare. -/
theorem flatGaugeHodgeBlockPoincare_of_harmonicClassification
    {d L N' Nc : ℕ}
    [NeZero d] [NeZero L] [NeZero N'] [NeZero Nc]
    (ρ : SUNAdjointModel Nc)
    (hclass :
      FlatHarmonicKernelClassified d (L * N') Nc ρ) :
    ∃ CP : ℝ,
      FlatGaugeHodgePoincare d L N' Nc ρ CP := by
  apply exists_flatGaugeHodgeBlockPoincare_of_jointKernel_trivial ρ
  intro A hK hQ
  exact
    (flatJointKernel_trivial_of_harmonicClassification
      ρ hclass A).mp ⟨hK, hQ⟩

/-- Explicit curl/divergence/block form of the classification-dependent
fixed-volume flat Hodge/block Poincare theorem. -/
theorem flatCurlDivBlockPoincare_of_harmonicClassification
    {d L N' Nc : ℕ}
    [NeZero d] [NeZero L] [NeZero N'] [NeZero Nc]
    (ρ : SUNAdjointModel Nc)
    (hclass :
      FlatHarmonicKernelClassified d (L * N') Nc ρ) :
    ∃ CP : ℝ, 0 < CP ∧
      ∀ A : FinePhysicalOneCochain d L N' Nc,
        ‖A‖ ^ 2 ≤
          CP *
            (‖covariantD1CLM ρ
                (trivialPhysicalGaugeBackground
                  d (L * N') Nc) A‖ ^ 2
              + ‖gaugeConstraintQCLM ρ
                  (trivialPhysicalGaugeBackground
                    d (L * N') Nc) A‖ ^ 2
              + ‖flatBlockConstraintQCLM
                  (d := d) (Nc := Nc) L N' A‖ ^ 2) := by
  obtain ⟨CP, hCP⟩ :=
    flatGaugeHodgeBlockPoincare_of_harmonicClassification
      ρ hclass
  refine ⟨CP, hCP.1, ?_⟩
  intro A
  simpa only [flatGaugeHodgeK0_inner_right] using hCP.2 A

/-- Norm squared of a direction-wise constant physical one-cochain. -/
theorem norm_sq_constantPhysicalGaugeOneCochain {d N Nc : ℕ} [NeZero N]
    (v : Fin d → SUNLieCoord Nc) :
    ‖constantPhysicalGaugeOneCochain
        (d := d) (N := N) (Nc := Nc) v‖ ^ 2
      = (N : ℝ) ^ d * ∑ i : Fin d, ‖v i‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [constantPhysicalGaugeOneCochain_apply]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  simp only [Finset.sum_const, Finset.card_univ, card_finBox]
  simp [nsmul_eq_mul, Finset.mul_sum]

/-- Exact norm squared of the flat block constraint on direction-wise constants.

The current `linAvg` normalization sends constants to `L` times constants, so
the coarse norm is `(L : ℝ)^2 * (N' : ℝ)^d` times the directional norm sum. -/
theorem flatBlockConstraintQCLM_constant_norm_sq {d L N' Nc : ℕ}
    [NeZero L] [NeZero N'] [NeZero Nc]
    (v : Fin d → SUNLieCoord Nc) :
    ‖flatBlockConstraintQCLM
        (d := d) (Nc := Nc) L N'
        (constantPhysicalGaugeOneCochain
          (d := d) (N := L * N') (Nc := Nc) v)‖ ^ 2
      = (L : ℝ) ^ 2 * (N' : ℝ) ^ d
          * ∑ i : Fin d, ‖v i‖ ^ 2 := by
  rw [flatBlockConstraintQCLM_constant]
  rw [norm_smul]
  rw [mul_pow]
  rw [norm_sq_constantPhysicalGaugeOneCochain]
  have hLnonneg : 0 ≤ (L : ℝ) := by
    exact_mod_cast Nat.zero_le L
  rw [Real.norm_of_nonneg hLnonneg]
  ring

/-- Exact constant-sector block control for the current full-periodic
normalization.

For constants on the fine side length `L * N'`, the fine norm squared is
`(L^d / L^2)` times the coarse block norm squared.  This is the sharp harmonic
sector normalization used by the future full Poincare theorem. -/
theorem flatBlockConstraint_controls_constantSector {d L N' Nc : ℕ}
    [NeZero L] [NeZero N'] [NeZero Nc]
    (v : Fin d → SUNLieCoord Nc) :
    ‖constantPhysicalGaugeOneCochain
        (d := d) (N := L * N') (Nc := Nc) v‖ ^ 2
      = ((L : ℝ) ^ d / (L : ℝ) ^ 2) *
          ‖flatBlockConstraintQCLM
              (d := d) (Nc := Nc) L N'
              (constantPhysicalGaugeOneCochain
                (d := d) (N := L * N') (Nc := Nc) v)‖ ^ 2 := by
  rw [norm_sq_constantPhysicalGaugeOneCochain]
  rw [flatBlockConstraintQCLM_constant_norm_sq]
  have hL : (L : ℝ) ≠ 0 := by
    exact_mod_cast NeZero.ne L
  field_simp [hL]
  rw [Nat.cast_mul, mul_pow]
  ring

end YangMills.RG
