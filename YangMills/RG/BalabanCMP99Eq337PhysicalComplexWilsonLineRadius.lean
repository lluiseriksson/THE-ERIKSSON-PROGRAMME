import YangMills.RG.BalabanCMP99Eq337PhysicalComplexPerturbedLinkRadius
import YangMills.RG.BalabanCMP99ComplexFourFactorDeviation
import YangMills.RG.OrderedProductQuadraticBound
import YangMills.ClayCore.WilsonLine

/-!
# Path radii for the literal complex CMP99 (3.37) background

This leaf turns the two oriented-link estimates into the actual ordered path
product bounds needed by complex Ubar.  Unlike the physical `SU(N)` path
lemma, it does not use norm one: both the deviation and the factor norm retain
the visible `(1+r)^length` cost.
-/

namespace YangMills.RG

open YangMills Matrix YangMills.GaugeConfig
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d N Nc : ℕ} [NeZero d] [NeZero N] [NeZero Nc]

local instance cmp99Eq337PhysicalComplexWilsonMatrixNormOneClass :
    NormOneClass (Matrix (Fin Nc) (Fin Nc) ℂ) where
  norm_one := by
    rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
    simp

/-- A matrix Wilson line in `SL(N,C)` is definitionally the ordered product
of its link deviations added back to one. -/
theorem cmp99SpecialLinearWilsonLine_coe_eq_orderedOnePlusProduct
    (V : GaugeConfig d N (Matrix.SpecialLinearGroup (Fin Nc) ℂ))
    (es : List (ConcreteEdge d N)) :
    ((wilsonLine V es : Matrix.SpecialLinearGroup (Fin Nc) ℂ) :
        Matrix (Fin Nc) (Fin Nc) ℂ) =
      orderedOnePlusProduct
        (es.map fun e ↦
          (V e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1) := by
  induction es with
  | nil =>
      rw [YangMills.GaugeConfig.wilsonLine_nil]
      rfl
  | cons e es ih =>
      rw [wilsonLine_cons, Matrix.SpecialLinearGroup.coe_mul,
        List.map_cons, orderedOnePlusProduct_cons, ih]
      congr 1
      noncomm_ring

/-- Uniform oriented-link deviation gives the explicit complex path
deviation. -/
theorem norm_cmp99SpecialLinearWilsonLine_sub_one_le
    (V : GaugeConfig d N (Matrix.SpecialLinearGroup (Fin Nc) ℂ))
    (es : List (ConcreteEdge d N)) (r : ℝ) (hr : 0 ≤ r)
    (hlink : ∀ e, ‖(V e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ r) :
    ‖((wilsonLine V es : Matrix.SpecialLinearGroup (Fin Nc) ℂ) :
          Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤
      es.length * r * (1 + r) ^ es.length := by
  rw [cmp99SpecialLinearWilsonLine_coe_eq_orderedOnePlusProduct]
  have hm : ∀ X ∈ es.map (fun e ↦
      (V e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1), ‖X‖ ≤ r := by
    intro X hX
    rcases List.mem_map.mp hX with ⟨e, he, rfl⟩
    exact hlink e
  simpa only [List.length_map] using
    (norm_orderedOnePlusProduct_sub_one_le
      (es.map fun e ↦ (V e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1) hr hm)

/-- The same input retains the factor norm needed by heterogeneous
four-factor telescoping. -/
theorem norm_cmp99SpecialLinearWilsonLine_le
    (V : GaugeConfig d N (Matrix.SpecialLinearGroup (Fin Nc) ℂ))
    (es : List (ConcreteEdge d N)) (r : ℝ) (hr : 0 ≤ r)
    (hlink : ∀ e, ‖(V e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ r) :
    ‖((wilsonLine V es : Matrix.SpecialLinearGroup (Fin Nc) ℂ) :
          Matrix (Fin Nc) (Fin Nc) ℂ)‖ ≤
      (1 + r) ^ es.length := by
  rw [cmp99SpecialLinearWilsonLine_coe_eq_orderedOnePlusProduct]
  have hm : ∀ X ∈ es.map (fun e ↦
      (V e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1), ‖X‖ ≤ r := by
    intro X hX
    rcases List.mem_map.mp hX with ⟨e, he, rfl⟩
    exact hlink e
  simpa only [List.length_map] using
    (norm_orderedOnePlusProduct_le
      (es.map fun e ↦ (V e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1) hr hm)

/-- Visible four-path budget obtained by combining ordered-product growth
with heterogeneous four-factor telescoping. -/
def cmp99ComplexFourWilsonPathDeviationBudget
    (paths : Fin 4 → List (ConcreteEdge d N)) (r : ℝ) : ℝ :=
  cmp99ComplexFourFactorDeviationBudget
    (fun i ↦ (paths i).length * r * (1 + r) ^ (paths i).length)
    (fun i ↦ (1 + r) ^ (paths i).length)

/-- Four literal complex Wilson paths are controlled without unitary
weakening.  The cost of every preceding path remains in the conclusion. -/
theorem norm_fourSpecialLinearWilsonLineProduct_sub_one_le
    (V : GaugeConfig d N (Matrix.SpecialLinearGroup (Fin Nc) ℂ))
    (paths : Fin 4 → List (ConcreteEdge d N)) (r : ℝ) (hr : 0 ≤ r)
    (hlink : ∀ e, ‖(V e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ r) :
    ‖fourMatrixProduct (fun i ↦
        ((wilsonLine V (paths i) :
            Matrix.SpecialLinearGroup (Fin Nc) ℂ) :
              Matrix (Fin Nc) (Fin Nc) ℂ)) - 1‖ ≤
      cmp99ComplexFourWilsonPathDeviationBudget paths r := by
  apply norm_fourMatrixProduct_sub_one_le_complexBudget
  · intro i
    exact norm_cmp99SpecialLinearWilsonLine_sub_one_le
      V (paths i) r hr hlink
  · intro i
    exact norm_cmp99SpecialLinearWilsonLine_le V (paths i) r hr hlink

/-- A single length envelope for all four paths gives a scalar complex Ubar
radius independent of the individual path family. -/
def cmp99ComplexFourWilsonUniformDeviationBudget
    (L : ℕ) (r : ℝ) : ℝ :=
  cmp99ComplexFourFactorDeviationBudget
    (fun _ ↦ (L : ℝ) * r * (1 + r) ^ L)
    (fun _ ↦ (1 + r) ^ L)

/-- Monotonicity from literal path lengths to the common scalar envelope.
The proof keeps both the path-deviation and path-norm contributions visible. -/
theorem cmp99ComplexFourWilsonPathDeviationBudget_le_uniform
    (paths : Fin 4 → List (ConcreteEdge d N))
    (L : ℕ) (r : ℝ) (hr : 0 ≤ r)
    (hlen : ∀ i, (paths i).length ≤ L) :
    cmp99ComplexFourWilsonPathDeviationBudget paths r ≤
      cmp99ComplexFourWilsonUniformDeviationBudget L r := by
  have hbase : 1 ≤ 1 + r := by linarith
  have hpow (i : Fin 4) :
      (1 + r) ^ (paths i).length ≤ (1 + r) ^ L :=
    pow_le_pow_right₀ hbase (hlen i)
  have hdelta (i : Fin 4) :
      ((paths i).length : ℝ) * r * (1 + r) ^ (paths i).length ≤
        (L : ℝ) * r * (1 + r) ^ L := by
    have hcast : ((paths i).length : ℝ) ≤ (L : ℝ) := by
      exact_mod_cast hlen i
    have hlength : ((paths i).length : ℝ) * r ≤ (L : ℝ) * r :=
      mul_le_mul_of_nonneg_right hcast hr
    exact mul_le_mul hlength (hpow i)
      (pow_nonneg (by linarith : 0 ≤ 1 + r) _)
      (mul_nonneg (Nat.cast_nonneg _) hr)
  unfold cmp99ComplexFourWilsonPathDeviationBudget
  unfold cmp99ComplexFourWilsonUniformDeviationBudget
  unfold cmp99ComplexFourFactorDeviationBudget
  gcongr
  · exact hdelta 0
  · exact hpow 1
  · exact hpow 2
  · exact hpow 3
  · exact hdelta 1
  · exact hpow 2
  · exact hpow 3
  · exact hdelta 2
  · exact hpow 3
  · exact hdelta 3

/-- The literal Eq. (3.37) background satisfies the same named radius on
both orientations of every fine link. -/
theorem norm_cmp99Eq337PhysicalComplexPerturbedBackground_apply_sub_one_le
    (U : PhysicalGaugeBackground d N Nc)
    (A : CMP99Eq337PhysicalComplexOneCochain d N Nc)
    (eta epsilonU rA : ℝ)
    (hA : ∀ b, ‖A b‖ ≤ rA)
    (hsmall : |eta| *
      (cmp99SUNLieComplexCoordMatrixNormBudget Nc * rA) ≤ 1 / 2)
    (hU : ∀ b, ‖(U (positiveEdgeOfPhysicalBond b) :
        Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilonU)
    (e : ConcreteEdge d N) :
    ‖(cmp99Eq337PhysicalComplexPerturbedBackground U A eta e :
        Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤
      cmp99Eq337PhysicalComplexPerturbedLinkRadius Nc epsilonU eta rA := by
  rcases e with ⟨x, mu, pos⟩
  cases pos with
  | false =>
      rw [cmp99Eq337PhysicalComplexPerturbedBackground_apply_neg_matrix]
      exact
        norm_cmp99Eq337PhysicalComplexPerturbedNegativeBondModel_sub_one_le
          U A eta epsilonU rA (x, mu) (hA (x, mu)) hsmall (hU (x, mu))
  | true =>
      change ‖cmp99Eq337PhysicalComplexPerturbedPositiveBondMatrix
        U A eta (x, mu) - 1‖ ≤ _
      exact
        norm_cmp99Eq337PhysicalComplexPerturbedPositiveBondMatrix_sub_one_le
          U A eta epsilonU rA (x, mu) (hA (x, mu)) hsmall (hU (x, mu))

/-- Source-specialized path deviation for the complex (3.37) background. -/
theorem norm_cmp99Eq337PhysicalComplexPerturbedWilsonLine_sub_one_le
    (U : PhysicalGaugeBackground d N Nc)
    (A : CMP99Eq337PhysicalComplexOneCochain d N Nc)
    (eta epsilonU rA : ℝ)
    (hr : 0 ≤ cmp99Eq337PhysicalComplexPerturbedLinkRadius Nc epsilonU eta rA)
    (hA : ∀ b, ‖A b‖ ≤ rA)
    (hsmall : |eta| *
      (cmp99SUNLieComplexCoordMatrixNormBudget Nc * rA) ≤ 1 / 2)
    (hU : ∀ b, ‖(U (positiveEdgeOfPhysicalBond b) :
        Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilonU)
    (es : List (ConcreteEdge d N)) :
    ‖((wilsonLine
        (cmp99Eq337PhysicalComplexPerturbedBackground U A eta) es :
          Matrix.SpecialLinearGroup (Fin Nc) ℂ) :
            Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤
      es.length *
        cmp99Eq337PhysicalComplexPerturbedLinkRadius Nc epsilonU eta rA *
        (1 + cmp99Eq337PhysicalComplexPerturbedLinkRadius
          Nc epsilonU eta rA) ^ es.length := by
  exact norm_cmp99SpecialLinearWilsonLine_sub_one_le _ es _ hr
    (norm_cmp99Eq337PhysicalComplexPerturbedBackground_apply_sub_one_le
      U A eta epsilonU rA hA hsmall hU)

/-- Source-specialized path norm retained for complex four-factor
telescoping. -/
theorem norm_cmp99Eq337PhysicalComplexPerturbedWilsonLine_le
    (U : PhysicalGaugeBackground d N Nc)
    (A : CMP99Eq337PhysicalComplexOneCochain d N Nc)
    (eta epsilonU rA : ℝ)
    (hr : 0 ≤ cmp99Eq337PhysicalComplexPerturbedLinkRadius Nc epsilonU eta rA)
    (hA : ∀ b, ‖A b‖ ≤ rA)
    (hsmall : |eta| *
      (cmp99SUNLieComplexCoordMatrixNormBudget Nc * rA) ≤ 1 / 2)
    (hU : ∀ b, ‖(U (positiveEdgeOfPhysicalBond b) :
        Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilonU)
    (es : List (ConcreteEdge d N)) :
    ‖((wilsonLine
        (cmp99Eq337PhysicalComplexPerturbedBackground U A eta) es :
          Matrix.SpecialLinearGroup (Fin Nc) ℂ) :
            Matrix (Fin Nc) (Fin Nc) ℂ)‖ ≤
      (1 + cmp99Eq337PhysicalComplexPerturbedLinkRadius
        Nc epsilonU eta rA) ^ es.length := by
  exact norm_cmp99SpecialLinearWilsonLine_le _ es _ hr
    (norm_cmp99Eq337PhysicalComplexPerturbedBackground_apply_sub_one_le
      U A eta epsilonU rA hA hsmall hU)

end

end YangMills.RG
