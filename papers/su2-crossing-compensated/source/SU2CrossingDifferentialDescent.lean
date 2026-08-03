import Lean2dYangMills.SU2CrossingExtendedGauge

/-!
# Haar and differential descent from the four-edge SU(2) crossing chart

This module proves that the explicit two-coordinate crossing quotient pushes
four-fold product Haar measure to two-fold product Haar measure.  It then
constructs gauge-compensated physical flows on the original four-edge chart
that intertwine exactly with the two right-invariant edge flows used by the
finite-edge crossing Ward theorem.

The geometric Wilson word, its first generator, its mixed generator, and the
Pauli-summed trace-skein closure therefore descend without choosing a gauge.
The final theorem lifts the previously compiled two-coordinate integral Ward
identity to the primary four-edge Wilson word under four-fold Haar measure.

No heat-kernel area derivative or Makeenko--Migdal equation is asserted.
-/

noncomputable section

open scoped BigOperators Matrix.Norms.L2Operator

namespace Lean2dYangMills

open MeasureTheory Matrix

/-! ## Haar pushforward to the physical quotient -/

/-- Project the paired physical/gauge chart to its two physical entries. -/
def su2CrossingPhysicalProjection (p : SU2CrossingPairedConfiguration) :
    Fin 2 -> SU2 :=
  ![p.1.1, p.2.1]

/-- Forgetting the two gauge coordinates in the paired chart preserves the
corresponding normalized product Haar probability. -/
theorem su2CrossingPhysicalProjection_measurePreserving :
    MeasurePreserving su2CrossingPhysicalProjection su2CrossingPairedHaar
      (su2FiniteProductHaar (Fin 2)) := by
  have hone : MeasurePreserving (Prod.fst : SU2 × SU2 -> SU2)
      (su2HaarProb.prod su2HaarProb) su2HaarProb :=
    MeasureTheory.measurePreserving_fst
  have hpairs := hone.prod hone
  have hvec := (MeasureTheory.measurePreserving_finTwoArrow su2HaarProb).symm
  have h := hvec.comp hpairs
  simpa [su2CrossingPhysicalProjection, su2CrossingPairedHaar,
    su2FiniteProductHaar, Function.comp_def, MeasurableEquiv.finTwoArrow,
    MeasurableEquiv.piFinTwo, MeasurableEquiv.prodCongr] using h

/-- The physical projection of the full gauge-fixing chart is literally the
two-coordinate quotient map. -/
theorem su2CrossingPhysicalProjection_fullGaugeFix
    (U : SU2CrossingConfiguration) :
    su2CrossingPhysicalProjection (su2CrossingFullGaugeFix U) =
      su2CrossingReducedConfiguration U := by
  funext i
  fin_cases i <;>
    simp [su2CrossingPhysicalProjection, su2CrossingFullGaugeFix,
      su2CrossingPairGaugeFix, su2CrossingToPaired,
      su2CrossingReducedConfiguration, div_eq_mul_inv]

/-- The quotient map from the cyclic four-edge chart pushes four-fold product
Haar measure exactly to two-fold product Haar measure. -/
theorem su2CrossingReducedConfiguration_measurePreserving :
    MeasurePreserving su2CrossingReducedConfiguration
      (su2FiniteProductHaar (Fin 4)) (su2FiniteProductHaar (Fin 2)) := by
  have h := su2CrossingPhysicalProjection_measurePreserving.comp
    su2CrossingFullGaugeFix_measurePreserving
  convert h using 1

/-- Exact quotient integration: every strongly measurable physical observable
has the same expectation in the four-edge chart and in the quotient chart. -/
theorem integral_su2CrossingReducedConfiguration
    (F : (Fin 2 -> SU2) -> Complex)
    (hF : AEStronglyMeasurable F (su2FiniteProductHaar (Fin 2))) :
    (∫ U, F (su2CrossingReducedConfiguration U)
        ∂su2FiniteProductHaar (Fin 4)) =
      ∫ V, F V ∂su2FiniteProductHaar (Fin 2) := by
  let hmp := su2CrossingReducedConfiguration_measurePreserving
  have hFmap : AEStronglyMeasurable F
      (Measure.map su2CrossingReducedConfiguration
        (su2FiniteProductHaar (Fin 4))) := by
    rw [hmp.map_eq]
    exact hF
  have hmap := MeasureTheory.integral_map hmp.measurable.aemeasurable hFmap
  rw [hmp.map_eq] at hmap
  exact hmap.symm

/-! ## Gauge-compensated physical flows -/

/-- Curve inserted on `a₂`, conjugated by the return edge `a₄`, so that the
first reduced coordinate moves by the original curve on the right. -/
def su2CrossingPhysicalCurve0 (gamma : Real -> SU2)
    (U : SU2CrossingConfiguration) (t : Real) : SU2 :=
  (U 3)⁻¹ * gamma t * U 3

/-- Physical flow of the first reduced coordinate in the four-edge chart. -/
def su2CrossingPhysicalFlow0 (gamma : Real -> SU2) (t : Real)
    (U : SU2CrossingConfiguration) : SU2CrossingConfiguration :=
  su2EdgeRightFlow (1 : Fin 4) (su2CrossingPhysicalCurve0 gamma U) t U

/-- Curve inserted on `a₁`, conjugated by the return edge `a₃`, so that the
second reduced coordinate moves by the original curve on the right. -/
def su2CrossingPhysicalCurve1 (gamma : Real -> SU2)
    (U : SU2CrossingConfiguration) (t : Real) : SU2 :=
  (U 2)⁻¹ * gamma t * U 2

/-- Physical flow of the second reduced coordinate in the four-edge chart. -/
def su2CrossingPhysicalFlow1 (gamma : Real -> SU2) (t : Real)
    (U : SU2CrossingConfiguration) : SU2CrossingConfiguration :=
  su2EdgeRightFlow (0 : Fin 4) (su2CrossingPhysicalCurve1 gamma U) t U

/-- The first compensated four-edge flow intertwines exactly with right flow
of the first quotient coordinate. -/
theorem su2CrossingReducedConfiguration_physicalFlow0
    (gamma : Real -> SU2) (t : Real) (U : SU2CrossingConfiguration) :
    su2CrossingReducedConfiguration (su2CrossingPhysicalFlow0 gamma t U) =
      su2EdgeRightFlow (0 : Fin 2) gamma t
        (su2CrossingReducedConfiguration U) := by
  funext i
  fin_cases i <;>
    simp [su2CrossingReducedConfiguration, su2CrossingPhysicalFlow0,
      su2CrossingPhysicalCurve0, su2EdgeRightFlow,
      su2SingleEdgeMultiplier, mul_assoc]

/-- The second compensated four-edge flow intertwines exactly with right flow
of the second quotient coordinate. -/
theorem su2CrossingReducedConfiguration_physicalFlow1
    (gamma : Real -> SU2) (t : Real) (U : SU2CrossingConfiguration) :
    su2CrossingReducedConfiguration (su2CrossingPhysicalFlow1 gamma t U) =
      su2EdgeRightFlow (1 : Fin 2) gamma t
        (su2CrossingReducedConfiguration U) := by
  funext i
  fin_cases i <;>
    simp [su2CrossingReducedConfiguration, su2CrossingPhysicalFlow1,
      su2CrossingPhysicalCurve1, su2EdgeRightFlow,
      su2SingleEdgeMultiplier, mul_assoc]

/-! ## Differential descent of the geometric Wilson word -/

/-- First physical generator of the four-edge Wilson word. -/
def su2FourEdgeCrossingFirstGenerator (alpha beta : SU2) (X : SU2Matrix)
    (U : SU2CrossingConfiguration) : Complex :=
  su2CrossingFirstGenerator (0 : Fin 2) (1 : Fin 2) beta alpha X
    (su2CrossingReducedConfiguration U)

/-- Ordered mixed physical generator of the four-edge Wilson word. -/
def su2FourEdgeCrossingMixedGenerator (alpha beta : SU2) (X Y : SU2Matrix)
    (U : SU2CrossingConfiguration) : Complex :=
  su2CrossingMixedGenerator (0 : Fin 2) (1 : Fin 2) beta alpha X Y
    (su2CrossingReducedConfiguration U)

/-- Differentiating the geometric four-edge word along the first compensated
physical flow gives the descended first generator. -/
theorem hasDerivAt_su2FourEdgeCrossingWilsonWord_physical0_zero
    (alpha beta : SU2) (U : SU2CrossingConfiguration)
    (gamma : Real -> SU2) (X : SU2Matrix)
    (hgamma : forall i j,
      HasDerivAt (fun s : Real => ((gamma s : SU2) : SU2Matrix) i j)
        (X i j) 0) :
    HasDerivAt
      (fun s : Real => su2FourEdgeCrossingWilsonWord alpha beta
        (su2CrossingPhysicalFlow0 gamma s U))
      (su2FourEdgeCrossingFirstGenerator alpha beta X U) 0 := by
  have h := hasDerivAt_su2CrossingWilsonWord_edge1_zero
    (0 : Fin 2) (1 : Fin 2) (by decide) beta alpha
    (su2CrossingReducedConfiguration U) gamma X hgamma
  convert h using 1
  funext s
  rw [su2FourEdgeCrossingWilsonWord_eq_twoEdgeWord,
    su2CrossingReducedConfiguration_physicalFlow0]

/-- Differentiating the descended first generator along the second compensated
physical flow gives the descended mixed generator. -/
theorem hasDerivAt_su2FourEdgeCrossingFirstGenerator_physical1_zero
    (alpha beta : SU2) (U : SU2CrossingConfiguration)
    (gamma : Real -> SU2) (X Y : SU2Matrix)
    (hgamma : forall i j,
      HasDerivAt (fun s : Real => ((gamma s : SU2) : SU2Matrix) i j)
        (Y i j) 0) :
    HasDerivAt
      (fun s : Real => su2FourEdgeCrossingFirstGenerator alpha beta X
        (su2CrossingPhysicalFlow1 gamma s U))
      (su2FourEdgeCrossingMixedGenerator alpha beta X Y U) 0 := by
  have h := hasDerivAt_su2CrossingFirstGenerator_edge2_zero
    (0 : Fin 2) (1 : Fin 2) (by decide) beta alpha
    (su2CrossingReducedConfiguration U) gamma X Y hgamma
  simpa [su2FourEdgeCrossingFirstGenerator,
    su2FourEdgeCrossingMixedGenerator,
    su2CrossingReducedConfiguration_physicalFlow1] using h

/-- Direct four-edge resolution pulled back from the physical quotient. -/
def su2FourEdgeCrossingDirectResolution (alpha beta : SU2)
    (U : SU2CrossingConfiguration) : Complex :=
  su2CrossingDirectResolution (0 : Fin 2) (1 : Fin 2) beta alpha
    (su2CrossingReducedConfiguration U)

/-- Reverse four-edge resolution pulled back from the physical quotient. -/
def su2FourEdgeCrossingReverseResolution (alpha beta : SU2)
    (U : SU2CrossingConfiguration) : Complex :=
  su2CrossingReverseResolution (0 : Fin 2) (1 : Fin 2) beta alpha
    (su2CrossingReducedConfiguration U)

/-- Pointwise trace-skein closure of the Pauli-summed mixed generator in the
original four-edge chart. -/
theorem su2FourEdgeCrossingMixedGenerator_pauli_sum_closed
    (alpha beta : SU2) (U : SU2CrossingConfiguration) :
    su2FourEdgeCrossingMixedGenerator alpha beta su2PauliX su2PauliX U +
        su2FourEdgeCrossingMixedGenerator alpha beta su2PauliY su2PauliY U +
        su2FourEdgeCrossingMixedGenerator alpha beta su2PauliZ su2PauliZ U =
      -(1 / 4 : Complex) * su2FourEdgeCrossingDirectResolution alpha beta U -
        (1 / 2 : Complex) * su2FourEdgeCrossingReverseResolution alpha beta U := by
  exact su2CrossingMixedGenerator_pauli_sum_closed
    (0 : Fin 2) (1 : Fin 2) beta alpha
      (su2CrossingReducedConfiguration U)

/-! ## Concrete Pauli directions -/

/-- Pauli-X derivative of the geometric word along the first physical flow. -/
theorem hasDerivAt_su2FourEdgeCrossingWilsonWord_pauliX
    (alpha beta : SU2) (U : SU2CrossingConfiguration) :
    HasDerivAt
      (fun s : Real => su2FourEdgeCrossingWilsonWord alpha beta
        (su2CrossingPhysicalFlow0 su2PauliXCurve s U))
      (su2FourEdgeCrossingFirstGenerator alpha beta su2PauliX U) 0 :=
  hasDerivAt_su2FourEdgeCrossingWilsonWord_physical0_zero
    alpha beta U su2PauliXCurve su2PauliX hasDerivAt_su2PauliXCurve_entry

/-- Pauli-Y derivative of the geometric word along the first physical flow. -/
theorem hasDerivAt_su2FourEdgeCrossingWilsonWord_pauliY
    (alpha beta : SU2) (U : SU2CrossingConfiguration) :
    HasDerivAt
      (fun s : Real => su2FourEdgeCrossingWilsonWord alpha beta
        (su2CrossingPhysicalFlow0 su2PauliYCurve s U))
      (su2FourEdgeCrossingFirstGenerator alpha beta su2PauliY U) 0 :=
  hasDerivAt_su2FourEdgeCrossingWilsonWord_physical0_zero
    alpha beta U su2PauliYCurve su2PauliY hasDerivAt_su2PauliYCurve_entry

/-- Pauli-Z derivative of the geometric word along the first physical flow. -/
theorem hasDerivAt_su2FourEdgeCrossingWilsonWord_pauliZ
    (alpha beta : SU2) (U : SU2CrossingConfiguration) :
    HasDerivAt
      (fun s : Real => su2FourEdgeCrossingWilsonWord alpha beta
        (su2CrossingPhysicalFlow0 su2PauliZCurve s U))
      (su2FourEdgeCrossingFirstGenerator alpha beta su2PauliZ U) 0 :=
  hasDerivAt_su2FourEdgeCrossingWilsonWord_physical0_zero
    alpha beta U su2PauliZCurve su2PauliZ hasDerivAt_su2PauliZCurve_entry

/-- Pauli-X second derivative of the descended first generator. -/
theorem hasDerivAt_su2FourEdgeCrossingFirstGenerator_pauliX
    (alpha beta : SU2) (U : SU2CrossingConfiguration) :
    HasDerivAt
      (fun s : Real => su2FourEdgeCrossingFirstGenerator alpha beta su2PauliX
        (su2CrossingPhysicalFlow1 su2PauliXCurve s U))
      (su2FourEdgeCrossingMixedGenerator alpha beta
        su2PauliX su2PauliX U) 0 :=
  hasDerivAt_su2FourEdgeCrossingFirstGenerator_physical1_zero
    alpha beta U su2PauliXCurve su2PauliX su2PauliX
      hasDerivAt_su2PauliXCurve_entry

/-- Pauli-Y second derivative of the descended first generator. -/
theorem hasDerivAt_su2FourEdgeCrossingFirstGenerator_pauliY
    (alpha beta : SU2) (U : SU2CrossingConfiguration) :
    HasDerivAt
      (fun s : Real => su2FourEdgeCrossingFirstGenerator alpha beta su2PauliY
        (su2CrossingPhysicalFlow1 su2PauliYCurve s U))
      (su2FourEdgeCrossingMixedGenerator alpha beta
        su2PauliY su2PauliY U) 0 :=
  hasDerivAt_su2FourEdgeCrossingFirstGenerator_physical1_zero
    alpha beta U su2PauliYCurve su2PauliY su2PauliY
      hasDerivAt_su2PauliYCurve_entry

/-- Pauli-Z second derivative of the descended first generator. -/
theorem hasDerivAt_su2FourEdgeCrossingFirstGenerator_pauliZ
    (alpha beta : SU2) (U : SU2CrossingConfiguration) :
    HasDerivAt
      (fun s : Real => su2FourEdgeCrossingFirstGenerator alpha beta su2PauliZ
        (su2CrossingPhysicalFlow1 su2PauliZCurve s U))
      (su2FourEdgeCrossingMixedGenerator alpha beta
        su2PauliZ su2PauliZ U) 0 :=
  hasDerivAt_su2FourEdgeCrossingFirstGenerator_physical1_zero
    alpha beta U su2PauliZCurve su2PauliZ su2PauliZ
      hasDerivAt_su2PauliZCurve_entry

/-! ## Four-edge integral Ward endpoint -/

/-- The six dominated product-rule certificates needed by the Pauli-summed
crossing Ward identity, packaged on the physical two-coordinate quotient. -/
structure SU2CrossingPauliWardData (alpha beta : SU2) where
  rho : (Fin 2 -> SU2) -> Complex
  D2rhoX : (Fin 2 -> SU2) -> Complex
  D1D2rhoX : (Fin 2 -> SU2) -> Complex
  D2rhoY : (Fin 2 -> SU2) -> Complex
  D1D2rhoY : (Fin 2 -> SU2) -> Complex
  D2rhoZ : (Fin 2 -> SU2) -> Complex
  D1D2rhoZ : (Fin 2 -> SU2) -> Complex
  PX1 : DominatedFlowPair (su2FiniteProductHaar (Fin 2))
    (su2EdgeRightFlow (0 : Fin 2) su2PauliXCurve)
    D2rhoX (su2CrossingWilsonWord (0 : Fin 2) (1 : Fin 2) beta alpha)
    D1D2rhoX
    (su2CrossingFirstGenerator (0 : Fin 2) (1 : Fin 2) beta alpha su2PauliX)
  PX2 : DominatedFlowPair (su2FiniteProductHaar (Fin 2))
    (su2EdgeRightFlow (1 : Fin 2) su2PauliXCurve)
    rho
    (su2CrossingFirstGenerator (0 : Fin 2) (1 : Fin 2) beta alpha su2PauliX)
    D2rhoX
    (su2CrossingMixedGenerator (0 : Fin 2) (1 : Fin 2) beta alpha
      su2PauliX su2PauliX)
  PY1 : DominatedFlowPair (su2FiniteProductHaar (Fin 2))
    (su2EdgeRightFlow (0 : Fin 2) su2PauliYCurve)
    D2rhoY (su2CrossingWilsonWord (0 : Fin 2) (1 : Fin 2) beta alpha)
    D1D2rhoY
    (su2CrossingFirstGenerator (0 : Fin 2) (1 : Fin 2) beta alpha su2PauliY)
  PY2 : DominatedFlowPair (su2FiniteProductHaar (Fin 2))
    (su2EdgeRightFlow (1 : Fin 2) su2PauliYCurve)
    rho
    (su2CrossingFirstGenerator (0 : Fin 2) (1 : Fin 2) beta alpha su2PauliY)
    D2rhoY
    (su2CrossingMixedGenerator (0 : Fin 2) (1 : Fin 2) beta alpha
      su2PauliY su2PauliY)
  PZ1 : DominatedFlowPair (su2FiniteProductHaar (Fin 2))
    (su2EdgeRightFlow (0 : Fin 2) su2PauliZCurve)
    D2rhoZ (su2CrossingWilsonWord (0 : Fin 2) (1 : Fin 2) beta alpha)
    D1D2rhoZ
    (su2CrossingFirstGenerator (0 : Fin 2) (1 : Fin 2) beta alpha su2PauliZ)
  PZ2 : DominatedFlowPair (su2FiniteProductHaar (Fin 2))
    (su2EdgeRightFlow (1 : Fin 2) su2PauliZCurve)
    rho
    (su2CrossingFirstGenerator (0 : Fin 2) (1 : Fin 2) beta alpha su2PauliZ)
    D2rhoZ
    (su2CrossingMixedGenerator (0 : Fin 2) (1 : Fin 2) beta alpha
      su2PauliZ su2PauliZ)

/-- The finite-edge Ward identity lifted to the primary geometric four-edge
Wilson word under literal four-fold Haar measure. -/
theorem integral_su2FourEdgeCrossing_pauliWard_closed
    (alpha beta : SU2) (D : SU2CrossingPauliWardData alpha beta) :
    (∫ U,
        (D.D1D2rhoX (su2CrossingReducedConfiguration U) +
          D.D1D2rhoY (su2CrossingReducedConfiguration U) +
          D.D1D2rhoZ (su2CrossingReducedConfiguration U)) *
          su2FourEdgeCrossingWilsonWord alpha beta U
        ∂su2FiniteProductHaar (Fin 4)) =
      ∫ U, D.rho (su2CrossingReducedConfiguration U) *
        (-(1 / 4 : Complex) *
            su2FourEdgeCrossingDirectResolution alpha beta U -
          (1 / 2 : Complex) *
            su2FourEdgeCrossingReverseResolution alpha beta U)
        ∂su2FiniteProductHaar (Fin 4) := by
  let FL : (Fin 2 -> SU2) -> Complex := fun V =>
    (D.D1D2rhoX V + D.D1D2rhoY V + D.D1D2rhoZ V) *
      su2CrossingWilsonWord (0 : Fin 2) (1 : Fin 2) beta alpha V
  let FR : (Fin 2 -> SU2) -> Complex := fun V => D.rho V *
    (-(1 / 4 : Complex) *
        su2CrossingDirectResolution (0 : Fin 2) (1 : Fin 2) beta alpha V -
      (1 / 2 : Complex) *
        su2CrossingReverseResolution (0 : Fin 2) (1 : Fin 2) beta alpha V)
  have hFL : AEStronglyMeasurable FL (su2FiniteProductHaar (Fin 2)) := by
    exact ((D.PX1.measurable_Df.add D.PY1.measurable_Df).add
      D.PZ1.measurable_Df).mul D.PX1.measurable_g
  have hmixed : AEStronglyMeasurable
      (fun V : Fin 2 -> SU2 =>
        su2CrossingMixedGenerator (0 : Fin 2) (1 : Fin 2) beta alpha
            su2PauliX su2PauliX V +
          su2CrossingMixedGenerator (0 : Fin 2) (1 : Fin 2) beta alpha
            su2PauliY su2PauliY V +
          su2CrossingMixedGenerator (0 : Fin 2) (1 : Fin 2) beta alpha
            su2PauliZ su2PauliZ V)
      (su2FiniteProductHaar (Fin 2)) :=
    (D.PX2.measurable_Dg.add D.PY2.measurable_Dg).add D.PZ2.measurable_Dg
  have hclosed :
      (fun V : Fin 2 -> SU2 =>
        -(1 / 4 : Complex) *
            su2CrossingDirectResolution (0 : Fin 2) (1 : Fin 2) beta alpha V -
          (1 / 2 : Complex) *
            su2CrossingReverseResolution (0 : Fin 2) (1 : Fin 2) beta alpha V) =
      fun V =>
        su2CrossingMixedGenerator (0 : Fin 2) (1 : Fin 2) beta alpha
            su2PauliX su2PauliX V +
          su2CrossingMixedGenerator (0 : Fin 2) (1 : Fin 2) beta alpha
            su2PauliY su2PauliY V +
          su2CrossingMixedGenerator (0 : Fin 2) (1 : Fin 2) beta alpha
            su2PauliZ su2PauliZ V := by
    funext V
    exact (su2CrossingMixedGenerator_pauli_sum_closed
      (0 : Fin 2) (1 : Fin 2) beta alpha V).symm
  have hFR : AEStronglyMeasurable FR (su2FiniteProductHaar (Fin 2)) := by
    unfold FR
    apply D.PX2.measurable_f.mul
    rw [hclosed]
    exact hmixed
  have hward := integral_su2Crossing_pauliWard_closed
    (0 : Fin 2) (1 : Fin 2) beta alpha D.rho
    D.D2rhoX D.D1D2rhoX D.D2rhoY D.D1D2rhoY D.D2rhoZ D.D1D2rhoZ
    D.PX1 D.PX2 D.PY1 D.PY2 D.PZ1 D.PZ2
  have hL := integral_su2CrossingReducedConfiguration FL hFL
  have hR := integral_su2CrossingReducedConfiguration FR hFR
  calc
    (∫ U,
        (D.D1D2rhoX (su2CrossingReducedConfiguration U) +
          D.D1D2rhoY (su2CrossingReducedConfiguration U) +
          D.D1D2rhoZ (su2CrossingReducedConfiguration U)) *
          su2FourEdgeCrossingWilsonWord alpha beta U
        ∂su2FiniteProductHaar (Fin 4)) =
        ∫ U, FL (su2CrossingReducedConfiguration U)
          ∂su2FiniteProductHaar (Fin 4) := by
            apply integral_congr_ae
            exact ae_of_all _ fun U => by
              simpa only [FL] using congrArg
                (fun z =>
                  (D.D1D2rhoX (su2CrossingReducedConfiguration U) +
                    D.D1D2rhoY (su2CrossingReducedConfiguration U) +
                    D.D1D2rhoZ (su2CrossingReducedConfiguration U)) * z)
                (su2FourEdgeCrossingWilsonWord_eq_twoEdgeWord alpha beta U)
    _ = ∫ V, FL V ∂su2FiniteProductHaar (Fin 2) := hL
    _ = ∫ V, FR V ∂su2FiniteProductHaar (Fin 2) := hward
    _ = ∫ U, FR (su2CrossingReducedConfiguration U)
          ∂su2FiniteProductHaar (Fin 4) := hR.symm
    _ = ∫ U, D.rho (su2CrossingReducedConfiguration U) *
        (-(1 / 4 : Complex) *
            su2FourEdgeCrossingDirectResolution alpha beta U -
          (1 / 2 : Complex) *
            su2FourEdgeCrossingReverseResolution alpha beta U)
        ∂su2FiniteProductHaar (Fin 4) := by rfl

end Lean2dYangMills
