import YangMills.RG.BlockMaps
import YangMills.RG.FiniteTorusCurlDiv
import YangMills.RG.PhysicalGaugeHodgePoincare

/-!
# Constant-sector flat block control and harmonic-kernel bridge

This module records the exact norm bookkeeping for direction-wise constant
physical one-cochains under the current unscaled full-periodic block map.  It
now proves the full-periodic curl/divergence kernel classification and the
resulting fixed-volume flat Hodge/block Poincare theorem.  The Poincare
constant is not volume-uniform.
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

/-- Adapter from the source-facing periodic curl/divergence classification to
the physical flat-harmonic kernel predicate. -/
theorem flatHarmonicKernelClassified_of_curl_div
    {d N Nc : ℕ}
    [NeZero d] [NeZero N] [NeZero Nc]
    (ρ : SUNAdjointModel Nc)
    (hcd :
      PeriodicCurlDivKernelClassified
        d N (SUNLieCoord Nc)) :
    FlatHarmonicKernelClassified d N Nc ρ := by
  intro A hA
  obtain ⟨v, hv⟩ :=
    hcd
      (fun x i => A (x, i))
      (fun x i j hij =>
        isFlatHarmonicOneCochain_curl_apply_eq_zero
          ρ hA ⟨x, i, j, hij⟩)
      (fun x =>
        isFlatHarmonicOneCochain_div_apply_eq_zero
          ρ hA x)
  refine ⟨v, ?_⟩
  apply PiLp.ext
  rintro ⟨x, i⟩
  simpa [constantPhysicalGaugeOneCochain_apply] using hv x i

/-- Flat harmonic physical one-cochains on the finite periodic lattice are
direction-wise constant. -/
theorem flatHarmonicKernelClassified
    {d N Nc : ℕ}
    [NeZero d] [NeZero N] [NeZero Nc]
    (ρ : SUNAdjointModel Nc) :
    FlatHarmonicKernelClassified d N Nc ρ :=
  flatHarmonicKernelClassified_of_curl_div
    ρ periodicCurlDivKernelClassified

/-- Readable one-field form of the flat harmonic classification. -/
theorem flatHarmonic_eq_constantPhysicalGaugeOneCochain
    {d N Nc : ℕ}
    [NeZero d] [NeZero N] [NeZero Nc]
    (ρ : SUNAdjointModel Nc)
    {A : PhysicalGaugeOneCochain d N Nc}
    (hA : IsFlatHarmonicOneCochain ρ A) :
    ∃ v : Fin d → SUNLieCoord Nc,
      A =
        constantPhysicalGaugeOneCochain
          (d := d) (N := N) (Nc := Nc) v :=
  flatHarmonicKernelClassified ρ A hA

/-- Every site of the one-dimensional periodic box is reached from the default
site by iterating the positive shift. -/
theorem finBox_one_eq_iterShift {N : ℕ} [NeZero N]
    (x : FinBox 1 N) :
    ((fun y : FinBox 1 N => FinBox.shift y 0)^[(x 0).val]
      (default : FinBox 1 N)) = x := by
  funext i
  have hi : i = 0 := Subsingleton.elim i 0
  subst hi
  apply Fin.ext
  rw [iterShift_apply_self]
  change (0 + (x 0).val) % N = (x 0).val
  simpa using Nat.mod_eq_of_lt (x 0).isLt

/-- A function on the one-dimensional periodic box that is invariant under the
positive shift is constant. -/
theorem constant_of_shift_invariant_finBox_one
    {N : ℕ} [NeZero N] {V : Type*} (f : FinBox 1 N → V)
    (hshift : ∀ x : FinBox 1 N, f (x.shift 0) = f x) :
    ∀ x : FinBox 1 N, f x = f (default : FinBox 1 N) := by
  intro x
  have hiter : ∀ k : ℕ,
      f (((fun y : FinBox 1 N => FinBox.shift y 0)^[k]
        (default : FinBox 1 N))) = f (default : FinBox 1 N) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [Function.iterate_succ_apply']
        rw [hshift]
        exact ih
  rw [← finBox_one_eq_iterShift x]
  exact hiter (x 0).val

/-- In one dimension, the pointwise flat divergence equation classifies the
flat harmonic kernel: flat harmonic one-cochains are direction-wise constant.

This is a base-case sanity check for the full reverse-classification target.
It does not address the higher-dimensional curl/divergence classification. -/
theorem flatHarmonicKernelClassified_one
    {N Nc : ℕ} [NeZero N] [NeZero Nc]
    (ρ : SUNAdjointModel Nc) :
    FlatHarmonicKernelClassified 1 N Nc ρ := by
  intro A hA
  let v : Fin 1 → SUNLieCoord Nc := fun _ => A ((default : FinBox 1 N), 0)
  refine ⟨v, ?_⟩
  apply PiLp.ext
  intro b
  rcases b with ⟨x, i⟩
  have hi : i = 0 := Subsingleton.elim i 0
  subst hi
  have hstep : ∀ x : FinBox 1 N, A (x.shift 0, 0) = A (x, 0) := by
    intro x
    have hdiv := isFlatHarmonicOneCochain_divergence_apply_eq_zero
      (d := 1) (N := N) (Nc := Nc) ρ hA (x.shift 0)
    have hdiff : A (x.shift 0, 0) - A (((x.shift 0).shiftBack 0), 0) = 0 := by
      simpa using hdiv
    simp [FinBox.shiftBack_shift] at hdiff
    exact sub_eq_zero.mp hdiff
  have hxconst : A (x, 0) = A ((default : FinBox 1 N), 0) :=
    constant_of_shift_invariant_finBox_one
      (fun x : FinBox 1 N => A (x, 0)) hstep x
  simp [v, constantPhysicalGaugeOneCochain_apply, hxconst]

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

/-- Fixed-volume flat Hodge/block Poincare from an explicit source-facing
periodic curl/divergence classification.  The theorem name keeps the remaining
coordinate-classification obligation visible. -/
theorem exists_flatGaugeHodgePoincare_of_periodicCurlDivClassification
    {d L N' Nc : ℕ}
    [NeZero d] [NeZero L] [NeZero N'] [NeZero Nc]
    (ρ : SUNAdjointModel Nc)
    (hcd :
      PeriodicCurlDivKernelClassified
        d (L * N') (SUNLieCoord Nc)) :
    ∃ CP : ℝ,
      FlatGaugeHodgePoincare d L N' Nc ρ CP := by
  exact
    flatGaugeHodgeBlockPoincare_of_harmonicClassification
      ρ
      (flatHarmonicKernelClassified_of_curl_div ρ hcd)

/-- Unconditional fixed-volume flat Hodge/block Poincare on the finite
periodic lattice.  The resulting constant may depend on the fixed volume. -/
theorem exists_flatGaugeHodgePoincare
    {d L N' Nc : ℕ}
    [NeZero d] [NeZero L] [NeZero N'] [NeZero Nc]
    (ρ : SUNAdjointModel Nc) :
    ∃ CP : ℝ,
      FlatGaugeHodgePoincare d L N' Nc ρ CP := by
  exact
    flatGaugeHodgeBlockPoincare_of_harmonicClassification
      ρ (flatHarmonicKernelClassified ρ)

/-- One-dimensional fixed-volume flat Hodge/block Poincare, obtained without
carrying an external classification hypothesis.  The constant is still the
finite-dimensional compactness constant and may depend on the fixed volume. -/
theorem flatGaugeHodgeBlockPoincare_one
    {L N' Nc : ℕ}
    [NeZero L] [NeZero N'] [NeZero Nc]
    (ρ : SUNAdjointModel Nc) :
    ∃ CP : ℝ,
      FlatGaugeHodgePoincare 1 L N' Nc ρ CP := by
  exact
    flatGaugeHodgeBlockPoincare_of_harmonicClassification
      (d := 1) (L := L) (N' := N') (Nc := Nc) ρ
      (flatHarmonicKernelClassified_one
        (N := L * N') (Nc := Nc) ρ)

/-- Explicit one-dimensional curl/divergence/block form of the fixed-volume
flat Hodge/block Poincare theorem. -/
theorem flatCurlDivBlockPoincare_one
    {L N' Nc : ℕ}
    [NeZero L] [NeZero N'] [NeZero Nc]
    (ρ : SUNAdjointModel Nc) :
    ∃ CP : ℝ, 0 < CP ∧
      ∀ A : FinePhysicalOneCochain 1 L N' Nc,
        ‖A‖ ^ 2 ≤
          CP *
            (‖covariantD1CLM ρ
                (trivialPhysicalGaugeBackground
                  1 (L * N') Nc) A‖ ^ 2
              + ‖gaugeConstraintQCLM ρ
                  (trivialPhysicalGaugeBackground
                    1 (L * N') Nc) A‖ ^ 2
              + ‖flatBlockConstraintQCLM
                  (d := 1) (Nc := Nc) L N' A‖ ^ 2) := by
  exact
    flatCurlDivBlockPoincare_of_harmonicClassification
      (d := 1) (L := L) (N' := N') (Nc := Nc) ρ
      (flatHarmonicKernelClassified_one
        (N := L * N') (Nc := Nc) ρ)

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

/-- Any full-periodic flat Hodge/block-Poincare constant must control the
direction-wise constant sector with the sharp normalization forced by the
current unscaled line-integral block map.

This is a necessary-condition audit theorem: it does not prove
`FlatGaugeHodgePoincare`, but it prevents later source matching from claiming
a constant smaller than the constant harmonic sector permits. -/
theorem flatGaugeHodgePoincare_constantSector_lower_bound
    {d L N' Nc : ℕ}
    [NeZero d] [NeZero L] [NeZero N'] [NeZero Nc]
    (ρ : SUNAdjointModel Nc)
    {CP : ℝ}
    (hP : FlatGaugeHodgePoincare d L N' Nc ρ CP)
    (v : Fin d → SUNLieCoord Nc)
    (hv : 0 < ∑ i : Fin d, ‖v i‖ ^ 2) :
    ((L : ℝ) ^ d / (L : ℝ) ^ 2) ≤ CP := by
  let A : FinePhysicalOneCochain d L N' Nc :=
    constantPhysicalGaugeOneCochain
      (d := d) (N := L * N') (Nc := Nc) v
  have hmain := hP.2 A
  have hK :
      flatGaugeHodgeK0CLM d (L * N') Nc ρ A = 0 := by
    dsimp [A]
    exact flatGaugeHodgeK0CLM_constantPhysicalGaugeOneCochain
      (d := d) (N := L * N') (Nc := Nc) ρ v
  have hinner : inner ℝ A (flatGaugeHodgeK0CLM d (L * N') Nc ρ A) = 0 := by
    rw [hK, inner_zero_right]
  have hQpos :
      0 <
        ‖flatBlockConstraintQCLM
            (d := d) (Nc := Nc) L N' A‖ ^ 2 := by
    dsimp [A]
    rw [flatBlockConstraintQCLM_constant_norm_sq]
    have hLpos : 0 < (L : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    have hNpos : 0 < (N' : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N')
    positivity
  have hineq :
      ‖A‖ ^ 2 ≤
        CP *
          ‖flatBlockConstraintQCLM
              (d := d) (Nc := Nc) L N' A‖ ^ 2 := by
    simpa [hinner] using hmain
  have hnorm :
      ‖A‖ ^ 2 =
        ((L : ℝ) ^ d / (L : ℝ) ^ 2) *
          ‖flatBlockConstraintQCLM
              (d := d) (Nc := Nc) L N' A‖ ^ 2 := by
    dsimp [A]
    exact flatBlockConstraint_controls_constantSector
      (d := d) (L := L) (N' := N') (Nc := Nc) v
  rw [hnorm] at hineq
  exact (mul_le_mul_iff_of_pos_right hQpos).mp hineq

end YangMills.RG
