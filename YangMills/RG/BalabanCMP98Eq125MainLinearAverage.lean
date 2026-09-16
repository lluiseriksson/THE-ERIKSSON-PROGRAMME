/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceUbarContours
import YangMills.RG.BalabanCMP99BlockContour
import YangMills.RG.PhysicalGaugeCochains

/-!
# The literal main linear average in CMP98 (125)

CMP99 (3.14)--(3.16) uses the complete linearization `Q(U)` printed in
CMP98 (124).  That formula consists of the main transported line average
printed separately as CMP98 (125), plus three analytic correction terms.

This file constructs the main term `Q₀` on physical one-cochains.  For a
coarse bond `(y, mu)` and a fine starting point `x` in its source block, the
`k`-th fine bond is transported to the coarse basepoint along the literal
block contour from `y` to `x`, followed by the first `k` bonds of the printed
straight length-`M` path.  The result is summed with the source coefficient
`M^{-(d+1)}`.

The adjoint mass of this literal operator is then constructed and its exact
nonnegative quadratic form is proved.

Honest scope: this is `Q₀` of (125), not the complete `Q(U)` of (124).
In particular, no theorem in this file identifies the three omitted
`g(ad)`/logarithmic correction terms with zero.
-/

namespace YangMills.RG

open YangMills YangMills.GaugeConfig
open scoped BigOperators RealInnerProductSpace

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

/-- Source coefficient `M^{-(d+1)}` in CMP98 (125). -/
noncomputable def cmp98Eq125MainAverageWeight (M d : ℕ) : ℝ :=
  ((M : ℝ) ^ (d + 1))⁻¹

/-- Holonomy from the coarse source basepoint to the source of the `k`-th
bond of the straight length-`M` path beginning at `x`. -/
noncomputable def cmp98Eq125PrefixHolonomy
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (y : FinBox d N')
    (x : {x : FinBox d (M * N') // x ∈ blockOf M N' y})
    (mu : Fin d) (k : ℕ) : SUN Nc :=
  cmp99ContourHolonomy
      (cmp99BlockContainedContourSystem (G := SUN Nc)) U y x.1 *
    wilsonLine U
      ((cmp99SourceParallelTransportPath (G := SUN Nc) x.1 mu).edges.take k)

/-- At the trivial background every source path transport is the identity. -/
@[simp] theorem cmp98Eq125PrefixHolonomy_trivial
    (y : FinBox d N')
    (x : {x : FinBox d (M * N') // x ∈ blockOf M N' y})
    (mu : Fin d) (k : ℕ) :
    cmp98Eq125PrefixHolonomy
        (trivialPhysicalGaugeBackground d (M * N') Nc) y x mu k = 1 := by
  unfold cmp98Eq125PrefixHolonomy cmp99ContourHolonomy
    OrientedLatticePath.holonomy
  rw [wilsonLine_one _ _ (fun _ => rfl),
    wilsonLine_one _ _ (fun _ => rfl), one_mul]

/-- The `k`-th summand of the transported line integral in CMP98 (125). -/
noncomputable def cmp98Eq125TransportedEdgeValue
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (y : FinBox d N')
    (x : {x : FinBox d (M * N') // x ∈ blockOf M N' y})
    (mu : Fin d) (k : ℕ) : SUNLieCoord Nc :=
  rho.adCLM (cmp98Eq125PrefixHolonomy U y x mu k)
    (A (((fun z => FinBox.shift z mu)^[k] x.1), mu))

/-- The transported summand becomes the underlying positive-bond coordinate
at the trivial background. -/
@[simp] theorem cmp98Eq125TransportedEdgeValue_trivial
    (rho : SUNAdjointModel Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (y : FinBox d N')
    (x : {x : FinBox d (M * N') // x ∈ blockOf M N' y})
    (mu : Fin d) (k : ℕ) :
    cmp98Eq125TransportedEdgeValue rho
        (trivialPhysicalGaugeBackground d (M * N') Nc) A y x mu k =
      A (((fun z => FinBox.shift z mu)^[k] x.1), mu) := by
  simp [cmp98Eq125TransportedEdgeValue]

/-- The transported length-`M` line integral entering CMP98 (125). -/
noncomputable def cmp98Eq125TransportedLineSum
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (y : FinBox d N')
    (x : {x : FinBox d (M * N') // x ∈ blockOf M N' y})
    (mu : Fin d) : SUNLieCoord Nc :=
  ∑ k ∈ Finset.range M,
    cmp98Eq125TransportedEdgeValue rho U A y x mu k

/-- At the trivial background the transported line sum is exactly the flat
positive-bond line integral. -/
theorem cmp98Eq125TransportedLineSum_trivial
    (rho : SUNAdjointModel Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (y : FinBox d N')
    (x : {x : FinBox d (M * N') // x ∈ blockOf M N' y})
    (mu : Fin d) :
    cmp98Eq125TransportedLineSum rho
        (trivialPhysicalGaugeBackground d (M * N') Nc) A y x mu =
      fineLineSum M N'
        (fun e : ConcreteEdge d (M * N') => A (physicalBondOfEdge e))
        mu x.1 := by
  simp [cmp98Eq125TransportedLineSum, fineLineSum]

/-- The source coefficient in (125) is one inverse block length times the
flat coefficient `M^{-d}`. -/
theorem cmp98Eq125MainAverageWeight_eq_inv_mul_flatWeight :
    cmp98Eq125MainAverageWeight M d =
      (M : ℝ)⁻¹ * ((M : ℝ) ^ d)⁻¹ := by
  have hM : (M : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne M
  unfold cmp98Eq125MainAverageWeight
  rw [pow_succ]
  field_simp

/-- Pointwise main average `Q₀(U)A` of CMP98 (125). -/
noncomputable def cmp98Eq125MainAverageValue
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') : SUNLieCoord Nc :=
  cmp98Eq125MainAverageWeight M d •
    ∑ x : {x : FinBox d (M * N') // x ∈ blockOf M N' b.1},
      cmp98Eq125TransportedLineSum rho U A b.1 x b.2

/-- The literal main one-step operator `Q₀(U)` from CMP98 (125). -/
noncomputable def cmp98Eq125MainAverageCLM
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d (M * N') Nc) :
    PhysicalGaugeOneCochain d (M * N') Nc →L[ℝ]
      PhysicalGaugeOneCochain d N' Nc :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => WithLp.toLp 2 fun b =>
        cmp98Eq125MainAverageValue rho U A b
      map_add' := fun A B => by
        apply PiLp.ext
        intro b
        simp only [cmp98Eq125MainAverageValue,
          cmp98Eq125TransportedLineSum,
          cmp98Eq125TransportedEdgeValue, PiLp.add_apply, map_add,
          Finset.sum_add_distrib, smul_add]
      map_smul' := fun a A => by
        apply PiLp.ext
        intro b
        simp only [cmp98Eq125MainAverageValue,
          cmp98Eq125TransportedLineSum,
          cmp98Eq125TransportedEdgeValue, PiLp.smul_apply, map_smul,
          Finset.smul_sum, smul_smul, RingHom.id_apply]
        rw [mul_comm (cmp98Eq125MainAverageWeight M d) a] }

@[simp] theorem cmp98Eq125MainAverageCLM_apply
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') :
    cmp98Eq125MainAverageCLM rho U A b =
      cmp98Eq125MainAverageValue rho U A b := rfl

/-- Exact flat-background dictionary: `Q₀(1)` is the ordinary flat block
average with the additional `M⁻¹` scaling printed in CMP98 (125). -/
theorem cmp98Eq125MainAverageCLM_trivial_apply
    (rho : SUNAdjointModel Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') :
    cmp98Eq125MainAverageCLM rho
        (trivialPhysicalGaugeBackground d (M * N') Nc) A b =
      (M : ℝ)⁻¹ •
        flatBlockConstraintQCLM (d := d) (Nc := Nc) M N' A b := by
  rw [cmp98Eq125MainAverageCLM_apply,
    cmp98Eq125MainAverageValue,
    flatBlockConstraintQCLM_apply,
    linAvg]
  simp_rw [cmp98Eq125TransportedLineSum_trivial]
  rw [cmp98Eq125MainAverageWeight_eq_inv_mul_flatWeight]
  simp only [mul_smul]
  congr 2
  exact (Finset.sum_subtype (blockOf M N' b.1) (fun _ => Iff.rfl)
    (fun x => fineLineSum M N'
      (fun e : ConcreteEdge d (M * N') => A (physicalBondOfEdge e))
      b.2 x)).symm

/-- Operator form of the exact flat-background dictionary. -/
theorem cmp98Eq125MainAverageCLM_trivial
    (rho : SUNAdjointModel Nc) :
    cmp98Eq125MainAverageCLM rho
        (trivialPhysicalGaugeBackground d (M * N') Nc) =
      (M : ℝ)⁻¹ • flatBlockConstraintQCLM
        (d := d) (Nc := Nc) M N' := by
  apply ContinuousLinearMap.ext
  intro A
  apply PiLp.ext
  intro b
  exact cmp98Eq125MainAverageCLM_trivial_apply rho A b

/-- The nonnegative adjoint mass generated by the literal main average. -/
noncomputable def cmp98Eq125MainAverageMass
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d (M * N') Nc) :
    PhysicalGaugeOneCochain d (M * N') Nc →L[ℝ]
      PhysicalGaugeOneCochain d (M * N') Nc :=
  (cmp98Eq125MainAverageCLM rho U).adjoint.comp
    (cmp98Eq125MainAverageCLM rho U)

/-- Exact quadratic form of the main-average mass. -/
theorem inner_cmp98Eq125MainAverageMass
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc) :
    inner ℝ A (cmp98Eq125MainAverageMass rho U A) =
      ‖cmp98Eq125MainAverageCLM rho U A‖ ^ 2 := by
  rw [cmp98Eq125MainAverageMass, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right, real_inner_self_eq_norm_sq]

/-- The literal main-average mass is nonnegative. -/
theorem inner_cmp98Eq125MainAverageMass_nonneg
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc) :
    0 ≤ inner ℝ A (cmp98Eq125MainAverageMass rho U A) := by
  rw [inner_cmp98Eq125MainAverageMass]
  positivity

/-- The literal main-average mass is self-adjoint. -/
theorem cmp98Eq125MainAverageMass_isSymmetric
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d (M * N') Nc) :
    (cmp98Eq125MainAverageMass rho U).IsSymmetric := by
  let Q := cmp98Eq125MainAverageCLM rho U
  intro A B
  change inner ℝ ((Q.adjoint.comp Q) A) B =
    inner ℝ A ((Q.adjoint.comp Q) B)
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_left,
    ContinuousLinearMap.adjoint_inner_right]

end

end YangMills.RG
