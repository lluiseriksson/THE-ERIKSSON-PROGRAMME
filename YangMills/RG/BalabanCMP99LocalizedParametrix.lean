import YangMills.RG.BalabanCMP116Eq221PhysicalInteractionExponent
import YangMills.RG.BalabanCMP116InteractingCombesThomas

/-!
# CMP99 localized physical parametrix: coercive compressed precision

A source-faithful generalized random-walk expansion starts from local inverses,
not from a Neumann expansion of the global covariance.  This file constructs
the first analytic brick.  Given a physical precision `K`, a finite bond set
`S`, and a positive exterior mass `m`, define

`K[S,m] = P_S K P_S + m (1 - P_S)`.

The coordinate projection is orthogonal, so coercivity of `K` with constant
`c` implies coercivity of `K[S,m]` with constant `min c m`.  In finite volume
this produces an exact bilateral local covariance.

The terminal specialization consumes the literal interacting Wilson,
gauge-fixing, and block-constraint precision already constructed in the
repository.  No random-walk term or equation-(3.108) estimate is claimed yet:
the next source step is to compare overlapping local inverses and localize the
parametrix defect across a collar.
-/

namespace YangMills.RG

open scoped RealInnerProductSpace

noncomputable section

private abbrev PhysicalEndomorphism (d N Nc : ℕ) [NeZero N] :=
  PhysicalGaugeOneCochain d N Nc →L[ℝ]
    PhysicalGaugeOneCochain d N Nc

/-- Exterior coordinate projection complementary to `S`. -/
noncomputable def physicalBondComplementProjection
    {d N Nc : ℕ} [NeZero N]
    (S : Finset (PhysicalBond d N)) : PhysicalEndomorphism d N Nc :=
  ContinuousLinearMap.id ℝ _ - physicalBondProjection S

/-- Exact Pythagorean splitting into the coordinates in `S` and their
complement. -/
theorem norm_sq_physicalBondProjection_add_complement
    {d N Nc : ℕ} [NeZero N]
    (S : Finset (PhysicalBond d N))
    (x : PhysicalGaugeOneCochain d N Nc) :
    ‖physicalBondProjection S x‖ ^ 2 +
        ‖physicalBondComplementProjection S x‖ ^ 2 = ‖x‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2,
    PiLp.norm_sq_eq_of_L2, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b _hb
  by_cases hbS : b ∈ S
  · simp [physicalBondComplementProjection,
      physicalBondProjection_apply_mem S hbS]
  · simp [physicalBondComplementProjection,
      physicalBondProjection_apply_not_mem S hbS]

/-- The complementary coordinate projection is self-adjoint. -/
theorem inner_physicalBondComplementProjection_right_eq_left
    {d N Nc : ℕ} [NeZero N]
    (S : Finset (PhysicalBond d N))
    (x y : PhysicalGaugeOneCochain d N Nc) :
    inner ℝ x (physicalBondComplementProjection S y) =
      inner ℝ (physicalBondComplementProjection S x) y := by
  simp only [physicalBondComplementProjection, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.id_apply, inner_sub_right, inner_sub_left]
  rw [PhysicalGaugeCMP116Dictionary.inner_physicalBondProjection_right_eq_left]

/-- The quadratic form of the complementary projection is its squared
norm. -/
theorem inner_physicalBondComplementProjection_self
    {d N Nc : ℕ} [NeZero N]
    (S : Finset (PhysicalBond d N))
    (x : PhysicalGaugeOneCochain d N Nc) :
    inner ℝ x (physicalBondComplementProjection S x) =
      ‖physicalBondComplementProjection S x‖ ^ 2 := by
  rw [PiLp.inner_apply, PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_congr rfl
  intro b _hb
  by_cases hbS : b ∈ S
  · simp [physicalBondComplementProjection,
      physicalBondProjection_apply_mem S hbS]
  · simp [physicalBondComplementProjection,
      physicalBondProjection_apply_not_mem S hbS]

/-- Precision compressed to `S`, with a strictly positive mass on the
orthogonal complement. -/
noncomputable def cmp99LocalizedPhysicalPrecision
    {d N Nc : ℕ} [NeZero N]
    (K : PhysicalEndomorphism d N Nc)
    (S : Finset (PhysicalBond d N)) (mass : ℝ) :
    PhysicalEndomorphism d N Nc :=
  (physicalBondProjection S).comp (K.comp (physicalBondProjection S)) +
    mass • physicalBondComplementProjection S

/-- Orthogonal compression preserves coercivity, with the exterior mass
supplying the complementary sector. -/
theorem isCoerciveCLM_cmp99LocalizedPhysicalPrecision
    {d N Nc : ℕ} [NeZero N]
    (K : PhysicalEndomorphism d N Nc)
    (S : Finset (PhysicalBond d N))
    {c mass : ℝ} (hK : IsCoerciveCLM K c) :
    IsCoerciveCLM (cmp99LocalizedPhysicalPrecision K S mass) (min c mass) := by
  intro x
  let P : PhysicalEndomorphism d N Nc := physicalBondProjection S
  let Q : PhysicalEndomorphism d N Nc :=
    physicalBondComplementProjection S
  have hPyth : ‖P x‖ ^ 2 + ‖Q x‖ ^ 2 = ‖x‖ ^ 2 :=
    norm_sq_physicalBondProjection_add_complement S x
  have hKPx : c * ‖P x‖ ^ 2 ≤ inner ℝ (P x) (K (P x)) := hK (P x)
  have hminc : min c mass ≤ c := min_le_left _ _
  have hminm : min c mass ≤ mass := min_le_right _ _
  have hPc : min c mass * ‖P x‖ ^ 2 ≤ c * ‖P x‖ ^ 2 :=
    mul_le_mul_of_nonneg_right hminc (sq_nonneg ‖P x‖)
  have hQm : min c mass * ‖Q x‖ ^ 2 ≤ mass * ‖Q x‖ ^ 2 :=
    mul_le_mul_of_nonneg_right hminm (sq_nonneg ‖Q x‖)
  have hquad :
      inner ℝ x (cmp99LocalizedPhysicalPrecision K S mass x) =
        inner ℝ (P x) (K (P x)) + mass * ‖Q x‖ ^ 2 := by
    rw [cmp99LocalizedPhysicalPrecision, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      inner_add_right,
      PhysicalGaugeCMP116Dictionary.inner_physicalBondProjection_right_eq_left,
      ContinuousLinearMap.smul_apply, inner_smul_right,
      inner_physicalBondComplementProjection_self]
  calc
    min c mass * ‖x‖ ^ 2 =
        min c mass * (‖P x‖ ^ 2 + ‖Q x‖ ^ 2) := by rw [hPyth]
    _ = min c mass * ‖P x‖ ^ 2 + min c mass * ‖Q x‖ ^ 2 := by ring
    _ ≤ c * ‖P x‖ ^ 2 + mass * ‖Q x‖ ^ 2 := add_le_add hPc hQm
    _ ≤ inner ℝ (P x) (K (P x)) + mass * ‖Q x‖ ^ 2 :=
      add_le_add hKPx le_rfl
    _ = inner ℝ x (cmp99LocalizedPhysicalPrecision K S mass x) := hquad.symm

/-- Exact local covariance generated by the compressed coercive precision. -/
noncomputable def cmp99LocalizedPhysicalCovariance
    {d N Nc : ℕ} [NeZero N]
    (K : PhysicalEndomorphism d N Nc)
    (S : Finset (PhysicalBond d N))
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c) : PhysicalEndomorphism d N Nc :=
  covarianceOfIsCoerciveCLM
    (cmp99LocalizedPhysicalPrecision K S mass)
    (lt_min hc hmass)
    (isCoerciveCLM_cmp99LocalizedPhysicalPrecision K S hK)

theorem cmp99LocalizedPhysicalPrecision_comp_covariance
    {d N Nc : ℕ} [NeZero N]
    (K : PhysicalEndomorphism d N Nc)
    (S : Finset (PhysicalBond d N))
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c) :
    (cmp99LocalizedPhysicalPrecision K S mass).comp
        (cmp99LocalizedPhysicalCovariance K S hc hmass hK) =
      ContinuousLinearMap.id ℝ _ := by
  exact precision_comp_covarianceOfIsCoerciveCLM
    (cmp99LocalizedPhysicalPrecision K S mass)
    (lt_min hc hmass)
    (isCoerciveCLM_cmp99LocalizedPhysicalPrecision K S hK)

theorem cmp99LocalizedPhysicalCovariance_comp_precision
    {d N Nc : ℕ} [NeZero N]
    (K : PhysicalEndomorphism d N Nc)
    (S : Finset (PhysicalBond d N))
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c) :
    (cmp99LocalizedPhysicalCovariance K S hc hmass hK).comp
        (cmp99LocalizedPhysicalPrecision K S mass) =
      ContinuousLinearMap.id ℝ _ := by
  exact covarianceOfIsCoerciveCLM_comp_precision
    (cmp99LocalizedPhysicalPrecision K S mass)
    (lt_min hc hmass)
    (isCoerciveCLM_cmp99LocalizedPhysicalPrecision K S hK)

/-- Literal interacting Wilson specialization: local coercivity is generated
from the already proved physical small-background theorem. -/
theorem isCoerciveCLM_cmp99LocalizedInteractingPhysicalPrecision
    {d L N' Nc : ℕ}
    [NeZero d] [NeZero L] [NeZero N'] [NeZero Nc] [NeZero (L * N')]
    (U : PhysicalGaugeBackground d (L * N') Nc)
    (S : Finset (PhysicalBond d (L * N')))
    {a CP ε mass : ℝ} (ha : 0 < a)
    (hP : FlatGaugeHodgePoincare
      d L N' Nc (matrixSUNAdjointModel Nc) CP)
    (hε : 0 ≤ ε)
    (hsmall : PhysicalWilsonSmallBackground U ε) :
    IsCoerciveCLM
      (cmp99LocalizedPhysicalPrecision
        (interactingPhysicalBasePrecisionCLM U a) S mass)
      (min
        (min 1 a / CP -
          cmp116ConcreteInteractingWilsonGaugeDefectBudget d Nc ε)
        mass) := by
  exact isCoerciveCLM_cmp99LocalizedPhysicalPrecision
    (interactingPhysicalBasePrecisionCLM U a) S
    (isCoerciveCLM_interactingPhysicalBasePrecision U ha hP hε hsmall)

end

end YangMills.RG
