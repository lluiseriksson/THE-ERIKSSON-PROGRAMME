import YangMills.RG.BalabanCMP99Eq337PhysicalComplexPerturbedLinkRadius
import YangMills.RG.BalabanCMP99ComplexFourFactorDeviation
import YangMills.RG.OrderedProductQuadraticBound

/-!
PRE-VALIDATION: this scratch source has no materialized `.olean` and no
compiler or axiom-oracle verdict.

# Path radii for the literal complex CMP99 (3.37) background

This leaf turns the two oriented-link estimates into the actual ordered path
product bounds needed by complex Ubar.  Unlike the physical `SU(N)` path
lemma, it does not use norm one: both the deviation and the factor norm retain
the visible `(1+r)^length` cost.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d N Nc : ℕ} [NeZero d] [NeZero N] [NeZero Nc]

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
  | nil => simp [orderedOnePlusProduct]
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
  apply norm_orderedOnePlusProduct_sub_one_le _ hr
  intro X hX
  rcases List.mem_map.mp hX with ⟨e, he, rfl⟩
  exact hlink e

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
  apply norm_orderedOnePlusProduct_le _ hr
  intro X hX
  rcases List.mem_map.mp hX with ⟨e, he, rfl⟩
  exact hlink e

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
      rw [cmp99Eq337PhysicalComplexPerturbedBackground_apply_pos]
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
