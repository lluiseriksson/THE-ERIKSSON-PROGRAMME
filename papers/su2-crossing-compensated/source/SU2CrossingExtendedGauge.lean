import Lean2dYangMills.SU2CrossingWard

/-!
# Extended gauge invariance at a four-edge SU(2) crossing

This module formalizes the local four-edge geometry that precedes the
finite-edge crossing Ward identity.  The two half-gauge actions multiply the
opposite pairs `(0,2)` and `(1,3)` on the right.  We prove that they preserve
product Haar measure, commute, compose to the ordinary vertex gauge action,
and provide an explicit two-coordinate quotient chart.

For the Wilson word

`tr₂(a₃⁻¹ β a₂ a₄⁻¹ α a₁)`

the odd action becomes conjugation inside the trace and the even action
cancels algebraically.  Consequently the word has extended gauge invariance
and factors exactly through the two-coordinate crossing word used by
`SU2CrossingWard`.

No heat-kernel area derivative or Makeenko--Migdal equation is asserted.
-/

noncomputable section

open scoped BigOperators Matrix.Norms.L2Operator

namespace Lean2dYangMills

open MeasureTheory Matrix

/-- The ordered local chart of four distinct outgoing crossing edges. -/
abbrev SU2CrossingConfiguration := Fin 4 -> SU2

/-- Right multiplier on the odd pair of crossing edges `(0,2)`. -/
def su2CrossingOddMultiplier (x : SU2) : SU2CrossingConfiguration :=
  ![x, 1, x, 1]

/-- Right multiplier on the even pair of crossing edges `(1,3)`. -/
def su2CrossingEvenMultiplier (x : SU2) : SU2CrossingConfiguration :=
  ![1, x, 1, x]

/-- Ordinary vertex-gauge multiplier on all four outgoing edges. -/
def su2CrossingVertexMultiplier (x : SU2) : SU2CrossingConfiguration :=
  fun _ => x

/-- The odd half-gauge action. -/
def su2CrossingOddAction (x : SU2) (U : SU2CrossingConfiguration) :
    SU2CrossingConfiguration :=
  U * su2CrossingOddMultiplier x

/-- The even half-gauge action. -/
def su2CrossingEvenAction (x : SU2) (U : SU2CrossingConfiguration) :
    SU2CrossingConfiguration :=
  U * su2CrossingEvenMultiplier x

/-- The ordinary gauge action supported at the crossing vertex. -/
def su2CrossingVertexAction (x : SU2) (U : SU2CrossingConfiguration) :
    SU2CrossingConfiguration :=
  U * su2CrossingVertexMultiplier x

@[simp] theorem su2CrossingOddAction_apply_zero (x : SU2)
    (U : SU2CrossingConfiguration) :
    su2CrossingOddAction x U 0 = U 0 * x := by
  rfl

@[simp] theorem su2CrossingOddAction_apply_one (x : SU2)
    (U : SU2CrossingConfiguration) :
    su2CrossingOddAction x U 1 = U 1 := by
  simp [su2CrossingOddAction, su2CrossingOddMultiplier]

@[simp] theorem su2CrossingOddAction_apply_two (x : SU2)
    (U : SU2CrossingConfiguration) :
    su2CrossingOddAction x U 2 = U 2 * x := by
  rfl

@[simp] theorem su2CrossingOddAction_apply_three (x : SU2)
    (U : SU2CrossingConfiguration) :
    su2CrossingOddAction x U 3 = U 3 := by
  simp [su2CrossingOddAction, su2CrossingOddMultiplier]

@[simp] theorem su2CrossingEvenAction_apply_zero (x : SU2)
    (U : SU2CrossingConfiguration) :
    su2CrossingEvenAction x U 0 = U 0 := by
  simp [su2CrossingEvenAction, su2CrossingEvenMultiplier]

@[simp] theorem su2CrossingEvenAction_apply_one (x : SU2)
    (U : SU2CrossingConfiguration) :
    su2CrossingEvenAction x U 1 = U 1 * x := by
  rfl

@[simp] theorem su2CrossingEvenAction_apply_two (x : SU2)
    (U : SU2CrossingConfiguration) :
    su2CrossingEvenAction x U 2 = U 2 := by
  simp [su2CrossingEvenAction, su2CrossingEvenMultiplier]

@[simp] theorem su2CrossingEvenAction_apply_three (x : SU2)
    (U : SU2CrossingConfiguration) :
    su2CrossingEvenAction x U 3 = U 3 * x := by
  rfl

/-- Driver--Hall--Kemp extended gauge invariance in the local four-edge chart. -/
structure SU2CrossingExtendedGaugeInvariant
    (f : SU2CrossingConfiguration -> Complex) : Prop where
  odd : forall x U, f (su2CrossingOddAction x U) = f U
  even : forall x U, f (su2CrossingEvenAction x U) = f U

/-- The odd half-gauge action preserves four-fold product Haar measure. -/
theorem measurePreserving_su2CrossingOddAction (x : SU2) :
    MeasurePreserving (su2CrossingOddAction x)
      (su2FiniteProductHaar (Fin 4)) (su2FiniteProductHaar (Fin 4)) := by
  simpa [su2CrossingOddAction] using
    MeasureTheory.measurePreserving_mul_right
      (su2FiniteProductHaar (Fin 4)) (su2CrossingOddMultiplier x)

/-- The even half-gauge action preserves four-fold product Haar measure. -/
theorem measurePreserving_su2CrossingEvenAction (x : SU2) :
    MeasurePreserving (su2CrossingEvenAction x)
      (su2FiniteProductHaar (Fin 4)) (su2FiniteProductHaar (Fin 4)) := by
  simpa [su2CrossingEvenAction] using
    MeasureTheory.measurePreserving_mul_right
      (su2FiniteProductHaar (Fin 4)) (su2CrossingEvenMultiplier x)

/-- The identity element acts trivially on the odd pair. -/
theorem su2CrossingOddAction_one (U : SU2CrossingConfiguration) :
    su2CrossingOddAction 1 U = U := by
  funext i
  fin_cases i <;> simp [su2CrossingOddAction, su2CrossingOddMultiplier]

/-- The identity element acts trivially on the even pair. -/
theorem su2CrossingEvenAction_one (U : SU2CrossingConfiguration) :
    su2CrossingEvenAction 1 U = U := by
  funext i
  fin_cases i <;> simp [su2CrossingEvenAction, su2CrossingEvenMultiplier]

/-- Successive odd actions multiply their parameters in traversal order. -/
theorem su2CrossingOddAction_mul (x y : SU2)
    (U : SU2CrossingConfiguration) :
    su2CrossingOddAction y (su2CrossingOddAction x U) =
      su2CrossingOddAction (x * y) U := by
  funext i
  fin_cases i <;>
    simp [su2CrossingOddAction, su2CrossingOddMultiplier, mul_assoc]

/-- Successive even actions multiply their parameters in traversal order. -/
theorem su2CrossingEvenAction_mul (x y : SU2)
    (U : SU2CrossingConfiguration) :
    su2CrossingEvenAction y (su2CrossingEvenAction x U) =
      su2CrossingEvenAction (x * y) U := by
  funext i
  fin_cases i <;>
    simp [su2CrossingEvenAction, su2CrossingEvenMultiplier, mul_assoc]

/-- The two half-gauge actions commute because they have disjoint supports. -/
theorem su2CrossingOddAction_evenAction_commute (x y : SU2)
    (U : SU2CrossingConfiguration) :
    su2CrossingOddAction x (su2CrossingEvenAction y U) =
      su2CrossingEvenAction y (su2CrossingOddAction x U) := by
  funext i
  fin_cases i <;>
    simp [su2CrossingOddAction, su2CrossingEvenAction,
      su2CrossingOddMultiplier, su2CrossingEvenMultiplier]

/-- Equal odd and even parameters compose to the ordinary vertex action. -/
theorem su2CrossingVertexAction_eq_even_odd (x : SU2)
    (U : SU2CrossingConfiguration) :
    su2CrossingVertexAction x U =
      su2CrossingEvenAction x (su2CrossingOddAction x U) := by
  funext i
  fin_cases i <;>
    simp [su2CrossingVertexAction, su2CrossingVertexMultiplier,
      su2CrossingOddAction, su2CrossingOddMultiplier,
      su2CrossingEvenAction, su2CrossingEvenMultiplier]

/-- Extended gauge invariance implies ordinary gauge invariance at the
crossing vertex. -/
theorem SU2CrossingExtendedGaugeInvariant.vertex
    {f : SU2CrossingConfiguration -> Complex}
    (h : SU2CrossingExtendedGaugeInvariant f) (x : SU2)
    (U : SU2CrossingConfiguration) :
    f (su2CrossingVertexAction x U) = f U := by
  rw [su2CrossingVertexAction_eq_even_odd]
  rw [h.even, h.odd]

/-- Normalized fundamental trace is invariant under concrete SU(2)
conjugation. -/
theorem su2FundamentalWilson_conj (x g : SU2) :
    su2FundamentalWilson (x * g * x⁻¹) = su2FundamentalWilson g := by
  unfold su2FundamentalWilson su2NormalizedMatrixTrace
  rw [su2_trace_conj]

/-- Cyclicity of the normalized fundamental trace for two SU(2) factors. -/
theorem su2FundamentalWilson_mul_cycle (g h : SU2) :
    su2FundamentalWilson (g * h) = su2FundamentalWilson (h * g) := by
  unfold su2FundamentalWilson su2NormalizedMatrixTrace
  change Matrix.trace
      ((g : SU2Matrix) * (h : SU2Matrix)) / 2 =
    Matrix.trace ((h : SU2Matrix) * (g : SU2Matrix)) / 2
  rw [Matrix.trace_mul_comm]

/-- Four-edge Wilson word at a simple crossing, in the order-reversing
parallel-transport convention of the primary source. -/
def su2FourEdgeCrossingWilsonWord (alpha beta : SU2)
    (U : SU2CrossingConfiguration) : Complex :=
  su2FundamentalWilson
    ((U 2)⁻¹ * beta * U 1 * (U 3)⁻¹ * alpha * U 0)

/-- The odd half-gauge action becomes conjugation inside the trace. -/
theorem su2FourEdgeCrossingWilsonWord_odd (alpha beta x : SU2)
    (U : SU2CrossingConfiguration) :
    su2FourEdgeCrossingWilsonWord alpha beta
        (su2CrossingOddAction x U) =
      su2FourEdgeCrossingWilsonWord alpha beta U := by
  unfold su2FourEdgeCrossingWilsonWord
  rw [su2CrossingOddAction_apply_two,
    su2CrossingOddAction_apply_one,
    su2CrossingOddAction_apply_three,
    su2CrossingOddAction_apply_zero]
  rw [_root_.mul_inv_rev]
  simp only [mul_assoc]
  have h := su2FundamentalWilson_conj x⁻¹
    ((U 2)⁻¹ * beta * U 1 * (U 3)⁻¹ * alpha * U 0)
  simpa [mul_assoc] using h

/-- The even half-gauge action cancels inside the Wilson word. -/
theorem su2FourEdgeCrossingWilsonWord_even (alpha beta x : SU2)
    (U : SU2CrossingConfiguration) :
    su2FourEdgeCrossingWilsonWord alpha beta
        (su2CrossingEvenAction x U) =
      su2FourEdgeCrossingWilsonWord alpha beta U := by
  unfold su2FourEdgeCrossingWilsonWord
  rw [su2CrossingEvenAction_apply_two,
    su2CrossingEvenAction_apply_one,
    su2CrossingEvenAction_apply_three,
    su2CrossingEvenAction_apply_zero]
  rw [_root_.mul_inv_rev]
  simp [mul_assoc]

/-- The geometric four-edge Wilson word has extended gauge invariance. -/
theorem su2FourEdgeCrossingWilsonWord_extendedGaugeInvariant
    (alpha beta : SU2) :
    SU2CrossingExtendedGaugeInvariant
      (su2FourEdgeCrossingWilsonWord alpha beta) := by
  constructor
  · exact su2FourEdgeCrossingWilsonWord_odd alpha beta
  · exact su2FourEdgeCrossingWilsonWord_even alpha beta

/-- The two gauge-invariant quotient coordinates of the four-edge chart. -/
def su2CrossingReducedConfiguration (U : SU2CrossingConfiguration) :
    Fin 2 -> SU2 :=
  ![U 1 * (U 3)⁻¹, U 0 * (U 2)⁻¹]

/-- The quotient coordinates are unchanged by the odd half-gauge action. -/
theorem su2CrossingReducedConfiguration_odd (x : SU2)
    (U : SU2CrossingConfiguration) :
    su2CrossingReducedConfiguration (su2CrossingOddAction x U) =
      su2CrossingReducedConfiguration U := by
  funext i
  fin_cases i <;>
    simp [su2CrossingReducedConfiguration, su2CrossingOddAction,
      su2CrossingOddMultiplier, mul_assoc]

/-- The quotient coordinates are unchanged by the even half-gauge action. -/
theorem su2CrossingReducedConfiguration_even (x : SU2)
    (U : SU2CrossingConfiguration) :
    su2CrossingReducedConfiguration (su2CrossingEvenAction x U) =
      su2CrossingReducedConfiguration U := by
  funext i
  fin_cases i <;>
    simp [su2CrossingReducedConfiguration, su2CrossingEvenAction,
      su2CrossingEvenMultiplier, mul_assoc]

/-- The same four-edge chart regrouped into the two opposite-edge pairs. -/
abbrev SU2CrossingPairedConfiguration :=
  (SU2 × SU2) × (SU2 × SU2)

/-- Product Haar on the two opposite-edge pairs. -/
def su2CrossingPairedHaar : Measure SU2CrossingPairedConfiguration :=
  (su2HaarProb.prod su2HaarProb).prod
    (su2HaarProb.prod su2HaarProb)

/-- Pairwise quotient-and-gauge coordinates `(a,b) ↦ (a b⁻¹,b)`. -/
def su2CrossingPairGaugeFix
    (p : SU2CrossingPairedConfiguration) :
    SU2CrossingPairedConfiguration :=
  ((p.1.1 / p.1.2, p.1.2), (p.2.1 / p.2.2, p.2.2))

/-- The simultaneous quotient-and-gauge change of variables preserves the
literal four-fold product Haar measure. -/
theorem su2CrossingPairGaugeFix_measurePreserving :
    MeasurePreserving su2CrossingPairGaugeFix
      su2CrossingPairedHaar su2CrossingPairedHaar := by
  have hpair : MeasurePreserving
      (fun z : SU2 × SU2 => (z.1 / z.2, z.2))
      (su2HaarProb.prod su2HaarProb)
      (su2HaarProb.prod su2HaarProb) :=
    measurePreserving_div_prod su2HaarProb su2HaarProb
  simpa [su2CrossingPairGaugeFix, su2CrossingPairedHaar] using
    hpair.prod hpair

/-- Regroup a cyclic four-edge configuration into `(a₂,a₄)` and `(a₁,a₃)`. -/
def su2CrossingToPaired (U : SU2CrossingConfiguration) :
    SU2CrossingPairedConfiguration :=
  ((U 1, U 3), (U 0, U 2))

/-- Coordinate equivalence that orders the four cyclic edges as the two
opposite-edge pairs `(a₂,a₄)` and `(a₁,a₃)`. -/
def su2CrossingPairIndexEquiv : (Fin 2 ⊕ Fin 2) ≃ Fin 4 where
  toFun
    | Sum.inl i => ![1, 3] i
    | Sum.inr i => ![0, 2] i
  invFun i := ![Sum.inr 0, Sum.inl 0, Sum.inr 1, Sum.inl 1] i
  left_inv := by
    rintro (i | i) <;> fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

/-- The cyclic four-edge chart is measurably equivalent to the two
opposite-edge pairs, with the same ordering as `su2CrossingToPaired`. -/
def su2CrossingToPairedEquiv :
    SU2CrossingConfiguration ≃ᵐ SU2CrossingPairedConfiguration :=
  ((MeasurableEquiv.piCongrLeft (fun _ : Fin 4 => SU2)
      su2CrossingPairIndexEquiv).symm).trans
    ((MeasurableEquiv.sumPiEquivProdPi
      (fun _ : Fin 2 ⊕ Fin 2 => SU2)).trans
      (MeasurableEquiv.prodCongr MeasurableEquiv.finTwoArrow
        MeasurableEquiv.finTwoArrow))

/-- The measurable coordinate equivalence is literally the concrete
regrouping map used by the crossing chart. -/
theorem su2CrossingToPairedEquiv_apply (U : SU2CrossingConfiguration) :
    su2CrossingToPairedEquiv U = su2CrossingToPaired U := by
  rfl

/-- Regrouping a cyclic four-edge configuration into opposite-edge pairs
preserves the literal four-fold product Haar measure. -/
theorem su2CrossingToPaired_measurePreserving :
    MeasurePreserving su2CrossingToPaired
      (su2FiniteProductHaar (Fin 4)) su2CrossingPairedHaar := by
  have hperm :=
    (MeasureTheory.measurePreserving_piCongrLeft
      (fun _ : Fin 4 => su2HaarProb) su2CrossingPairIndexEquiv).symm
  have hsplit := MeasureTheory.measurePreserving_sumPiEquivProdPi
    (fun _ : Fin 2 ⊕ Fin 2 => su2HaarProb)
  have hpair : MeasurePreserving
      (MeasurableEquiv.prodCongr MeasurableEquiv.finTwoArrow
        MeasurableEquiv.finTwoArrow)
      ((Measure.pi fun _ : Fin 2 => su2HaarProb).prod
        (Measure.pi fun _ : Fin 2 => su2HaarProb))
      ((su2HaarProb.prod su2HaarProb).prod
        (su2HaarProb.prod su2HaarProb)) := by
    simpa [MeasurableEquiv.prodCongr] using
      (MeasureTheory.measurePreserving_finTwoArrow su2HaarProb).prod
        (MeasureTheory.measurePreserving_finTwoArrow su2HaarProb)
  change MeasurePreserving su2CrossingToPairedEquiv
    (Measure.pi fun _ : Fin 4 => su2HaarProb)
    ((su2HaarProb.prod su2HaarProb).prod
      (su2HaarProb.prod su2HaarProb))
  exact hperm.trans (hsplit.trans hpair)

/-- The complete quotient-and-gauge coordinate transformation from the
cyclic four-edge chart to `(physical,gauge)` opposite-edge coordinates. -/
def su2CrossingFullGaugeFix (U : SU2CrossingConfiguration) :
    SU2CrossingPairedConfiguration :=
  su2CrossingPairGaugeFix (su2CrossingToPaired U)

/-- The complete four-edge `(physical,gauge)` coordinate transformation
preserves product Haar measure in one public endpoint. -/
theorem su2CrossingFullGaugeFix_measurePreserving :
    MeasurePreserving su2CrossingFullGaugeFix
      (su2FiniteProductHaar (Fin 4)) su2CrossingPairedHaar := by
  simpa [su2CrossingFullGaugeFix, Function.comp_def] using
    su2CrossingPairGaugeFix_measurePreserving.comp
      su2CrossingToPaired_measurePreserving

/-- The two reduced coordinates are exactly the physical coordinates exposed
by the pairwise Haar-preserving gauge fix. -/
theorem su2CrossingPairGaugeFix_physical (U : SU2CrossingConfiguration) :
    ((su2CrossingPairGaugeFix (su2CrossingToPaired U)).1.1,
      (su2CrossingPairGaugeFix (su2CrossingToPaired U)).2.1) =
      (su2CrossingReducedConfiguration U 0,
        su2CrossingReducedConfiguration U 1) := by
  simp [su2CrossingPairGaugeFix, su2CrossingToPaired,
    su2CrossingReducedConfiguration, div_eq_mul_inv]

/-- Canonical representative with the two return edges fixed to identity. -/
def su2CrossingCanonicalConfiguration (U : SU2CrossingConfiguration) :
    SU2CrossingConfiguration :=
  ![U 0 * (U 2)⁻¹, U 1 * (U 3)⁻¹, 1, 1]

/-- The two half-gauge transformations send every four-edge configuration to
its explicit canonical representative. -/
theorem su2Crossing_toCanonical (U : SU2CrossingConfiguration) :
    su2CrossingEvenAction (U 3)⁻¹
        (su2CrossingOddAction (U 2)⁻¹ U) =
      su2CrossingCanonicalConfiguration U := by
  funext i
  fin_cases i <;>
    simp [su2CrossingCanonicalConfiguration, su2CrossingOddAction,
      su2CrossingOddMultiplier, su2CrossingEvenAction,
      su2CrossingEvenMultiplier]

/-- Every extended-gauge-invariant function is determined by the explicit
two-coordinate canonical representative. -/
theorem SU2CrossingExtendedGaugeInvariant.eq_canonical
    {f : SU2CrossingConfiguration -> Complex}
    (h : SU2CrossingExtendedGaugeInvariant f)
    (U : SU2CrossingConfiguration) :
    f U = f (su2CrossingCanonicalConfiguration U) := by
  rw [← su2Crossing_toCanonical U]
  rw [h.even, h.odd]

/-- Section of the quotient chart obtained by setting the two return-edge
coordinates to identity. -/
def su2CrossingLiftReduced (V : Fin 2 -> SU2) :
    SU2CrossingConfiguration :=
  ![V 1, V 0, 1, 1]

/-- Reduction followed by the canonical section is the identity on the
two-coordinate quotient chart. -/
theorem su2CrossingReducedConfiguration_lift (V : Fin 2 -> SU2) :
    su2CrossingReducedConfiguration (su2CrossingLiftReduced V) = V := by
  funext i
  fin_cases i <;>
    simp [su2CrossingReducedConfiguration, su2CrossingLiftReduced]

/-- The canonical representative is literally the lift of the two quotient
coordinates. -/
theorem su2CrossingLiftReduced_reduced (U : SU2CrossingConfiguration) :
    su2CrossingLiftReduced (su2CrossingReducedConfiguration U) =
      su2CrossingCanonicalConfiguration U := by
  funext i
  fin_cases i <;>
    simp [su2CrossingLiftReduced, su2CrossingReducedConfiguration,
      su2CrossingCanonicalConfiguration]

/-- The concrete function induced on the two-coordinate quotient chart. -/
def su2CrossingDescendedFunction
    (f : SU2CrossingConfiguration -> Complex) (V : Fin 2 -> SU2) : Complex :=
  f (su2CrossingLiftReduced V)

/-- Universal factorization: every extended-gauge-invariant function factors
through the explicit two-coordinate quotient chart. -/
theorem SU2CrossingExtendedGaugeInvariant.factor_through_reduced
    {f : SU2CrossingConfiguration -> Complex}
    (h : SU2CrossingExtendedGaugeInvariant f)
    (U : SU2CrossingConfiguration) :
    f U = su2CrossingDescendedFunction f
      (su2CrossingReducedConfiguration U) := by
  rw [h.eq_canonical]
  unfold su2CrossingDescendedFunction
  rw [su2CrossingLiftReduced_reduced]

/-- Uniqueness in the universal factorization: every function on the
two-coordinate chart whose pullback is `f` equals the canonical descended
function. -/
theorem SU2CrossingExtendedGaugeInvariant.descended_unique
    {f : SU2CrossingConfiguration -> Complex}
    (_h : SU2CrossingExtendedGaugeInvariant f)
    (g : (Fin 2 -> SU2) -> Complex)
    (hfactor : forall U, f U = g (su2CrossingReducedConfiguration U)) :
    g = su2CrossingDescendedFunction f := by
  funext V
  have hV := (hfactor (su2CrossingLiftReduced V)).symm
  simpa [su2CrossingDescendedFunction,
    su2CrossingReducedConfiguration_lift] using hV

/-- The four-edge geometric Wilson word factors exactly through the concrete
two-edge crossing word used by the finite-edge Ward theorem. -/
theorem su2FourEdgeCrossingWilsonWord_eq_twoEdgeWord
    (alpha beta : SU2) (U : SU2CrossingConfiguration) :
    su2FourEdgeCrossingWilsonWord alpha beta U =
      su2CrossingWilsonWord (0 : Fin 2) (1 : Fin 2) beta alpha
        (su2CrossingReducedConfiguration U) := by
  unfold su2FourEdgeCrossingWilsonWord su2CrossingWilsonWord
    su2CrossingReducedConfiguration su2FundamentalWilson
  change su2NormalizedMatrixTrace
      ((((U 2)⁻¹ * beta * U 1 * (U 3)⁻¹ * alpha * U 0 : SU2) : SU2Matrix)) =
    su2NormalizedMatrixTrace
      ((((beta * (U 1 * (U 3)⁻¹) : SU2) : SU2Matrix) *
        (((alpha * (U 0 * (U 2)⁻¹) : SU2) : SU2Matrix))))
  have hcycle := su2FundamentalWilson_mul_cycle (U 2)⁻¹
    (beta * U 1 * (U 3)⁻¹ * alpha * U 0)
  unfold su2FundamentalWilson at hcycle
  simpa [mul_assoc] using hcycle

end Lean2dYangMills
