import Lean2dYangMills.SU2HaarIntegrationByParts
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Finite-edge SU(2) crossing Ward identity

This module joins the Haar integration-by-parts producer to the finite-rank
Pauli/trace-skein producer.  It gives a concrete Wilson word on two selected
edge coordinates, identifies its first and mixed infinitesimal generators,
and closes the Pauli-summed mixed generator on the two single-trace crossing
resolutions.

The final integral identity is a finite-dimensional Ward identity.  It does
not identify the density-side mixed generator with an alternating four-area
derivative; that heat-density identity remains a separate analytic input.
-/

noncomputable section

open scoped BigOperators Matrix.Norms.L2Operator

namespace Lean2dYangMills

open MeasureTheory Matrix

abbrev SU2Matrix := Matrix (Fin 2) (Fin 2) Complex

/-! ## Differentiating a matrix word from entrywise tangent data -/

/-- Entrywise tangent data for a moving SU(2) factor differentiate its
normalized matrix word.  The proof expands the finite trace and all four
matrix entries, so it does not rely on a differentiable-manifold structure on
the subtype `SU2`. -/
theorem hasDerivAt_normalizedTrace_const_mul_curve_mul_const
    (A B : SU2Matrix) (gamma : Real -> SU2) (X : SU2Matrix) (t : Real)
    (hgamma : forall i j,
      HasDerivAt
        (fun s : Real => ((gamma s : SU2) : SU2Matrix) i j)
        (X i j) t) :
    HasDerivAt
      (fun s : Real => su2NormalizedMatrixTrace
        (A * ((gamma s : SU2) : SU2Matrix) * B))
      (su2NormalizedMatrixTrace (A * X * B)) t := by
  have h00 := hgamma 0 0
  have h01 := hgamma 0 1
  have h10 := hgamma 1 0
  have h11 := hgamma 1 1
  simp only [su2NormalizedMatrixTrace, Matrix.trace_fin_two,
    Matrix.mul_apply, Fin.sum_univ_two]
  exact (((h00.const_mul (A 0 0)).add (h10.const_mul (A 0 1))).mul_const (B 0 0) |>.add
      (((h01.const_mul (A 0 0)).add (h11.const_mul (A 0 1))).mul_const (B 1 0)) |>.add
      ((((h00.const_mul (A 1 0)).add (h10.const_mul (A 1 1))).mul_const (B 0 1)).add
        (((h01.const_mul (A 1 0)).add (h11.const_mul (A 1 1))).mul_const (B 1 1)))) |>.div_const 2

/-! ## The concrete two-edge crossing word -/

/-- A fundamental Wilson word with two distinguished edge coordinates. -/
def su2CrossingWilsonWord {I : Type} [Fintype I]
    (edge1 edge2 : I) (A B : SU2) (U : I -> SU2) : Complex :=
  su2NormalizedMatrixTrace
    (((A * U edge1 : SU2) : SU2Matrix) *
      ((B * U edge2 : SU2) : SU2Matrix))

/-- The first right-invariant generator inserted after the first selected
edge. -/
def su2CrossingFirstGenerator {I : Type} [Fintype I]
    (edge1 edge2 : I) (A B : SU2) (X : SU2Matrix)
    (U : I -> SU2) : Complex :=
  su2NormalizedMatrixTrace
    (((A * U edge1 : SU2) : SU2Matrix) * X *
      ((B * U edge2 : SU2) : SU2Matrix))

/-- The ordered mixed generator, with one insertion at each selected edge. -/
def su2CrossingMixedGenerator {I : Type} [Fintype I]
    (edge1 edge2 : I) (A B : SU2) (X Y : SU2Matrix)
    (U : I -> SU2) : Complex :=
  su2NormalizedMatrixTrace
    (((A * U edge1 : SU2) : SU2Matrix) * X *
      ((B * U edge2 : SU2) : SU2Matrix) * Y)

/-- The named first generator is the actual derivative of the crossing word
at the identity of an arbitrary inserted curve. -/
theorem hasDerivAt_su2CrossingWilsonWord_edge1_zero
    {I : Type} [Fintype I]
    (edge1 edge2 : I) (h12 : edge1 ≠ edge2)
    (A B : SU2) (U : I -> SU2)
    (gamma : Real -> SU2)
    (X : SU2Matrix)
    (hgamma : forall i j,
      HasDerivAt
        (fun s : Real => ((gamma s : SU2) : SU2Matrix) i j)
        (X i j) 0) :
    HasDerivAt
      (fun s : Real => su2CrossingWilsonWord edge1 edge2 A B
        (su2EdgeRightFlow edge1 gamma s U))
      (su2CrossingFirstGenerator edge1 edge2 A B X U) 0 := by
  have h := hasDerivAt_normalizedTrace_const_mul_curve_mul_const
    (((A * U edge1 : SU2) : SU2Matrix))
    (((B * U edge2 : SU2) : SU2Matrix)) gamma X 0 hgamma
  simpa [su2CrossingWilsonWord, su2CrossingFirstGenerator,
    su2EdgeRightFlow, su2SingleEdgeMultiplier, h12, h12.symm,
    mul_assoc] using h

/-- Differentiating the first generator along the second selected edge gives
the named ordered mixed generator. -/
theorem hasDerivAt_su2CrossingFirstGenerator_edge2_zero
    {I : Type} [Fintype I]
    (edge1 edge2 : I) (h12 : edge1 ≠ edge2)
    (A B : SU2) (U : I -> SU2)
    (gamma : Real -> SU2)
    (X Y : SU2Matrix)
    (hgamma : forall i j,
      HasDerivAt
        (fun s : Real => ((gamma s : SU2) : SU2Matrix) i j)
        (Y i j) 0) :
    HasDerivAt
      (fun s : Real => su2CrossingFirstGenerator edge1 edge2 A B X
        (su2EdgeRightFlow edge2 gamma s U))
      (su2CrossingMixedGenerator edge1 edge2 A B X Y U) 0 := by
  have h := hasDerivAt_normalizedTrace_const_mul_curve_mul_const
    ((((A * U edge1 : SU2) : SU2Matrix) * X *
      (((B * U edge2 : SU2) : SU2Matrix))))
    (1 : SU2Matrix) gamma Y 0 hgamma
  simpa [su2CrossingFirstGenerator, su2CrossingMixedGenerator,
    su2EdgeRightFlow, su2SingleEdgeMultiplier, h12, h12.symm,
    mul_assoc] using h

/-- Concrete X-direction first derivative at the crossing. -/
theorem hasDerivAt_su2CrossingWilsonWord_pauliX
    {I : Type} [Fintype I]
    (edge1 edge2 : I) (h12 : edge1 ≠ edge2)
    (A B : SU2) (U : I -> SU2) :
    HasDerivAt
      (fun s : Real => su2CrossingWilsonWord edge1 edge2 A B
        (su2EdgeRightFlow edge1 su2PauliXCurve s U))
      (su2CrossingFirstGenerator edge1 edge2 A B su2PauliX U) 0 := by
  exact hasDerivAt_su2CrossingWilsonWord_edge1_zero
    edge1 edge2 h12 A B U su2PauliXCurve su2PauliX
      hasDerivAt_su2PauliXCurve_entry

/-- Concrete Y-direction first derivative at the crossing. -/
theorem hasDerivAt_su2CrossingWilsonWord_pauliY
    {I : Type} [Fintype I]
    (edge1 edge2 : I) (h12 : edge1 ≠ edge2)
    (A B : SU2) (U : I -> SU2) :
    HasDerivAt
      (fun s : Real => su2CrossingWilsonWord edge1 edge2 A B
        (su2EdgeRightFlow edge1 su2PauliYCurve s U))
      (su2CrossingFirstGenerator edge1 edge2 A B su2PauliY U) 0 := by
  exact hasDerivAt_su2CrossingWilsonWord_edge1_zero
    edge1 edge2 h12 A B U su2PauliYCurve su2PauliY
      hasDerivAt_su2PauliYCurve_entry

/-- Concrete Z-direction first derivative at the crossing. -/
theorem hasDerivAt_su2CrossingWilsonWord_pauliZ
    {I : Type} [Fintype I]
    (edge1 edge2 : I) (h12 : edge1 ≠ edge2)
    (A B : SU2) (U : I -> SU2) :
    HasDerivAt
      (fun s : Real => su2CrossingWilsonWord edge1 edge2 A B
        (su2EdgeRightFlow edge1 su2PauliZCurve s U))
      (su2CrossingFirstGenerator edge1 edge2 A B su2PauliZ U) 0 := by
  exact hasDerivAt_su2CrossingWilsonWord_edge1_zero
    edge1 edge2 h12 A B U su2PauliZCurve su2PauliZ
      hasDerivAt_su2PauliZCurve_entry

/-- Concrete X-direction second step of the mixed derivative. -/
theorem hasDerivAt_su2CrossingFirstGenerator_pauliX
    {I : Type} [Fintype I]
    (edge1 edge2 : I) (h12 : edge1 ≠ edge2)
    (A B : SU2) (U : I -> SU2) :
    HasDerivAt
      (fun s : Real => su2CrossingFirstGenerator edge1 edge2 A B su2PauliX
        (su2EdgeRightFlow edge2 su2PauliXCurve s U))
      (su2CrossingMixedGenerator edge1 edge2 A B su2PauliX su2PauliX U) 0 := by
  exact hasDerivAt_su2CrossingFirstGenerator_edge2_zero
    edge1 edge2 h12 A B U su2PauliXCurve
      su2PauliX su2PauliX hasDerivAt_su2PauliXCurve_entry

/-- Concrete Y-direction second step of the mixed derivative. -/
theorem hasDerivAt_su2CrossingFirstGenerator_pauliY
    {I : Type} [Fintype I]
    (edge1 edge2 : I) (h12 : edge1 ≠ edge2)
    (A B : SU2) (U : I -> SU2) :
    HasDerivAt
      (fun s : Real => su2CrossingFirstGenerator edge1 edge2 A B su2PauliY
        (su2EdgeRightFlow edge2 su2PauliYCurve s U))
      (su2CrossingMixedGenerator edge1 edge2 A B su2PauliY su2PauliY U) 0 := by
  exact hasDerivAt_su2CrossingFirstGenerator_edge2_zero
    edge1 edge2 h12 A B U su2PauliYCurve
      su2PauliY su2PauliY hasDerivAt_su2PauliYCurve_entry

/-- Concrete Z-direction second step of the mixed derivative. -/
theorem hasDerivAt_su2CrossingFirstGenerator_pauliZ
    {I : Type} [Fintype I]
    (edge1 edge2 : I) (h12 : edge1 ≠ edge2)
    (A B : SU2) (U : I -> SU2) :
    HasDerivAt
      (fun s : Real => su2CrossingFirstGenerator edge1 edge2 A B su2PauliZ
        (su2EdgeRightFlow edge2 su2PauliZCurve s U))
      (su2CrossingMixedGenerator edge1 edge2 A B su2PauliZ su2PauliZ U) 0 := by
  exact hasDerivAt_su2CrossingFirstGenerator_edge2_zero
    edge1 edge2 h12 A B U su2PauliZCurve
      su2PauliZ su2PauliZ hasDerivAt_su2PauliZCurve_entry

/-- Direct single-trace resolution of the crossing word. -/
def su2CrossingDirectResolution {I : Type} [Fintype I]
    (edge1 edge2 : I) (A B : SU2) (U : I -> SU2) : Complex :=
  su2FundamentalWilson ((A * U edge1) * (B * U edge2))

/-- Reverse single-trace resolution of the crossing word. -/
def su2CrossingReverseResolution {I : Type} [Fintype I]
    (edge1 edge2 : I) (A B : SU2) (U : I -> SU2) : Complex :=
  su2FundamentalWilson ((A * U edge1) * (B * U edge2)⁻¹)

/-- The Pauli sum of mixed generators is exactly the previously audited
crossing contraction. -/
theorem su2CrossingMixedGenerator_pauli_sum_eq_contraction
    {I : Type} [Fintype I]
    (edge1 edge2 : I) (A B : SU2) (U : I -> SU2) :
    su2CrossingMixedGenerator edge1 edge2 A B su2PauliX su2PauliX U +
        su2CrossingMixedGenerator edge1 edge2 A B su2PauliY su2PauliY U +
        su2CrossingMixedGenerator edge1 edge2 A B su2PauliZ su2PauliZ U =
      su2PauliCrossingContraction
        (((A * U edge1 : SU2) : SU2Matrix))
        (((B * U edge2 : SU2) : SU2Matrix)) := by
  rfl

/-- Pointwise single-trace closure of the Pauli-summed mixed generator. -/
theorem su2CrossingMixedGenerator_pauli_sum_closed
    {I : Type} [Fintype I]
    (edge1 edge2 : I) (A B : SU2) (U : I -> SU2) :
    su2CrossingMixedGenerator edge1 edge2 A B su2PauliX su2PauliX U +
        su2CrossingMixedGenerator edge1 edge2 A B su2PauliY su2PauliY U +
        su2CrossingMixedGenerator edge1 edge2 A B su2PauliZ su2PauliZ U =
      -(1 / 4 : Complex) * su2CrossingDirectResolution edge1 edge2 A B U -
        (1 / 2 : Complex) * su2CrossingReverseResolution edge1 edge2 A B U := by
  rw [su2CrossingMixedGenerator_pauli_sum_eq_contraction]
  simpa [su2CrossingDirectResolution, su2CrossingReverseResolution] using
    su2PauliCrossingContraction_eq_closedResolutions
      (A * U edge1) (B * U edge2)

/-! ## Generator transfer and the finite-edge Ward identity -/

/-- One Pauli direction transfers from a twice differentiated density to the
corresponding mixed generator of the Wilson word. -/
theorem integral_su2Crossing_oneDirection_transfer
    {I : Type} [Fintype I]
    (edge1 edge2 : I) (A B : SU2)
    (gamma : Real -> SU2) (hgamma_zero : gamma 0 = 1)
    (X : SU2Matrix)
    (rho D2rho D1D2rho : (I -> SU2) -> Complex)
    (P1 : DominatedFlowPair (su2FiniteProductHaar I)
      (su2EdgeRightFlow edge1 gamma)
      D2rho (su2CrossingWilsonWord edge1 edge2 A B)
      D1D2rho (su2CrossingFirstGenerator edge1 edge2 A B X))
    (P2 : DominatedFlowPair (su2FiniteProductHaar I)
      (su2EdgeRightFlow edge2 gamma)
      rho (su2CrossingFirstGenerator edge1 edge2 A B X)
      D2rho (su2CrossingMixedGenerator edge1 edge2 A B X X)) :
    (∫ U, D1D2rho U * su2CrossingWilsonWord edge1 edge2 A B U
        ∂su2FiniteProductHaar I) =
      ∫ U, rho U * su2CrossingMixedGenerator edge1 edge2 A B X X U
        ∂su2FiniteProductHaar I := by
  exact integral_su2Edge_two_rightGenerators_transfer
    edge1 edge2 gamma gamma hgamma_zero hgamma_zero
    rho (su2CrossingWilsonWord edge1 edge2 A B)
    D2rho D1D2rho (su2CrossingFirstGenerator edge1 edge2 A B X)
    (su2CrossingMixedGenerator edge1 edge2 A B X X) P1 P2

/-- Exact finite-edge SU(2) crossing Ward identity.  Three Haar transfers and
the rank-two Fierz/trace-skein identity close the density-side Pauli sum on the
two single-trace resolutions. -/
theorem integral_su2Crossing_pauliWard_closed
    {I : Type} [Fintype I]
    (edge1 edge2 : I) (A B : SU2)
    (rho : (I -> SU2) -> Complex)
    (D2rhoX D1D2rhoX D2rhoY D1D2rhoY D2rhoZ D1D2rhoZ :
      (I -> SU2) -> Complex)
    (PX1 : DominatedFlowPair (su2FiniteProductHaar I)
      (su2EdgeRightFlow edge1 su2PauliXCurve)
      D2rhoX (su2CrossingWilsonWord edge1 edge2 A B)
      D1D2rhoX (su2CrossingFirstGenerator edge1 edge2 A B su2PauliX))
    (PX2 : DominatedFlowPair (su2FiniteProductHaar I)
      (su2EdgeRightFlow edge2 su2PauliXCurve)
      rho (su2CrossingFirstGenerator edge1 edge2 A B su2PauliX)
      D2rhoX
      (su2CrossingMixedGenerator edge1 edge2 A B su2PauliX su2PauliX))
    (PY1 : DominatedFlowPair (su2FiniteProductHaar I)
      (su2EdgeRightFlow edge1 su2PauliYCurve)
      D2rhoY (su2CrossingWilsonWord edge1 edge2 A B)
      D1D2rhoY (su2CrossingFirstGenerator edge1 edge2 A B su2PauliY))
    (PY2 : DominatedFlowPair (su2FiniteProductHaar I)
      (su2EdgeRightFlow edge2 su2PauliYCurve)
      rho (su2CrossingFirstGenerator edge1 edge2 A B su2PauliY)
      D2rhoY
      (su2CrossingMixedGenerator edge1 edge2 A B su2PauliY su2PauliY))
    (PZ1 : DominatedFlowPair (su2FiniteProductHaar I)
      (su2EdgeRightFlow edge1 su2PauliZCurve)
      D2rhoZ (su2CrossingWilsonWord edge1 edge2 A B)
      D1D2rhoZ (su2CrossingFirstGenerator edge1 edge2 A B su2PauliZ))
    (PZ2 : DominatedFlowPair (su2FiniteProductHaar I)
      (su2EdgeRightFlow edge2 su2PauliZCurve)
      rho (su2CrossingFirstGenerator edge1 edge2 A B su2PauliZ)
      D2rhoZ
      (su2CrossingMixedGenerator edge1 edge2 A B su2PauliZ su2PauliZ)) :
    (∫ U,
        (D1D2rhoX U + D1D2rhoY U + D1D2rhoZ U) *
          su2CrossingWilsonWord edge1 edge2 A B U
        ∂su2FiniteProductHaar I) =
      ∫ U, rho U *
        (-(1 / 4 : Complex) * su2CrossingDirectResolution edge1 edge2 A B U -
          (1 / 2 : Complex) * su2CrossingReverseResolution edge1 edge2 A B U)
        ∂su2FiniteProductHaar I := by
  have hX := integral_su2Crossing_oneDirection_transfer
    edge1 edge2 A B su2PauliXCurve su2PauliXCurve_zero su2PauliX
    rho D2rhoX D1D2rhoX PX1 PX2
  have hY := integral_su2Crossing_oneDirection_transfer
    edge1 edge2 A B su2PauliYCurve su2PauliYCurve_zero su2PauliY
    rho D2rhoY D1D2rhoY PY1 PY2
  have hZ := integral_su2Crossing_oneDirection_transfer
    edge1 edge2 A B su2PauliZCurve su2PauliZCurve_zero su2PauliZ
    rho D2rhoZ D1D2rhoZ PZ1 PZ2
  have hleftX : Integrable
      (fun U => D1D2rhoX U * su2CrossingWilsonWord edge1 edge2 A B U)
      (su2FiniteProductHaar I) := by
    exact (integrable_const (PX1.bound_Df * PX1.bound_g : Real)).mono'
      (PX1.measurable_Df.mul PX1.measurable_g)
      (ae_of_all _ fun U => by
        have h1 := PX1.norm_Df_le U 0 (by simpa using PX1.epsilon_pos)
        have h2 := PX1.norm_g_le U 0 (by simpa using PX1.epsilon_pos)
        simpa [su2EdgeRightFlow_zero edge1 su2PauliXCurve su2PauliXCurve_zero,
          norm_mul] using
          mul_le_mul h1 h2 (norm_nonneg _) PX1.bound_Df_nonneg)
  have hleftY : Integrable
      (fun U => D1D2rhoY U * su2CrossingWilsonWord edge1 edge2 A B U)
      (su2FiniteProductHaar I) := by
    exact (integrable_const (PY1.bound_Df * PY1.bound_g : Real)).mono'
      (PY1.measurable_Df.mul PY1.measurable_g)
      (ae_of_all _ fun U => by
        have h1 := PY1.norm_Df_le U 0 (by simpa using PY1.epsilon_pos)
        have h2 := PY1.norm_g_le U 0 (by simpa using PY1.epsilon_pos)
        simpa [su2EdgeRightFlow_zero edge1 su2PauliYCurve su2PauliYCurve_zero,
          norm_mul] using
          mul_le_mul h1 h2 (norm_nonneg _) PY1.bound_Df_nonneg)
  have hleftZ : Integrable
      (fun U => D1D2rhoZ U * su2CrossingWilsonWord edge1 edge2 A B U)
      (su2FiniteProductHaar I) := by
    exact (integrable_const (PZ1.bound_Df * PZ1.bound_g : Real)).mono'
      (PZ1.measurable_Df.mul PZ1.measurable_g)
      (ae_of_all _ fun U => by
        have h1 := PZ1.norm_Df_le U 0 (by simpa using PZ1.epsilon_pos)
        have h2 := PZ1.norm_g_le U 0 (by simpa using PZ1.epsilon_pos)
        simpa [su2EdgeRightFlow_zero edge1 su2PauliZCurve su2PauliZCurve_zero,
          norm_mul] using
          mul_le_mul h1 h2 (norm_nonneg _) PZ1.bound_Df_nonneg)
  have hrightX : Integrable
      (fun U => rho U *
        su2CrossingMixedGenerator edge1 edge2 A B su2PauliX su2PauliX U)
      (su2FiniteProductHaar I) := by
    exact (integrable_const (PX2.bound_f * PX2.bound_Dg : Real)).mono'
      (PX2.measurable_f.mul PX2.measurable_Dg)
      (ae_of_all _ fun U => by
        have h1 := PX2.norm_f_le U 0 (by simpa using PX2.epsilon_pos)
        have h2 := PX2.norm_Dg_le U 0 (by simpa using PX2.epsilon_pos)
        simpa [su2EdgeRightFlow_zero edge2 su2PauliXCurve su2PauliXCurve_zero,
          norm_mul] using
          mul_le_mul h1 h2 (norm_nonneg _) PX2.bound_f_nonneg)
  have hrightY : Integrable
      (fun U => rho U *
        su2CrossingMixedGenerator edge1 edge2 A B su2PauliY su2PauliY U)
      (su2FiniteProductHaar I) := by
    exact (integrable_const (PY2.bound_f * PY2.bound_Dg : Real)).mono'
      (PY2.measurable_f.mul PY2.measurable_Dg)
      (ae_of_all _ fun U => by
        have h1 := PY2.norm_f_le U 0 (by simpa using PY2.epsilon_pos)
        have h2 := PY2.norm_Dg_le U 0 (by simpa using PY2.epsilon_pos)
        simpa [su2EdgeRightFlow_zero edge2 su2PauliYCurve su2PauliYCurve_zero,
          norm_mul] using
          mul_le_mul h1 h2 (norm_nonneg _) PY2.bound_f_nonneg)
  have hrightZ : Integrable
      (fun U => rho U *
        su2CrossingMixedGenerator edge1 edge2 A B su2PauliZ su2PauliZ U)
      (su2FiniteProductHaar I) := by
    exact (integrable_const (PZ2.bound_f * PZ2.bound_Dg : Real)).mono'
      (PZ2.measurable_f.mul PZ2.measurable_Dg)
      (ae_of_all _ fun U => by
        have h1 := PZ2.norm_f_le U 0 (by simpa using PZ2.epsilon_pos)
        have h2 := PZ2.norm_Dg_le U 0 (by simpa using PZ2.epsilon_pos)
        simpa [su2EdgeRightFlow_zero edge2 su2PauliZCurve su2PauliZCurve_zero,
          norm_mul] using
          mul_le_mul h1 h2 (norm_nonneg _) PZ2.bound_f_nonneg)
  calc
    (∫ U,
        (D1D2rhoX U + D1D2rhoY U + D1D2rhoZ U) *
          su2CrossingWilsonWord edge1 edge2 A B U
        ∂su2FiniteProductHaar I) =
        (∫ U, D1D2rhoX U * su2CrossingWilsonWord edge1 edge2 A B U
          ∂su2FiniteProductHaar I) +
        (∫ U, D1D2rhoY U * su2CrossingWilsonWord edge1 edge2 A B U
          ∂su2FiniteProductHaar I) +
        (∫ U, D1D2rhoZ U * su2CrossingWilsonWord edge1 edge2 A B U
          ∂su2FiniteProductHaar I) := by
            rw [show (fun U =>
                (D1D2rhoX U + D1D2rhoY U + D1D2rhoZ U) *
                  su2CrossingWilsonWord edge1 edge2 A B U) =
                fun U =>
                  (D1D2rhoX U * su2CrossingWilsonWord edge1 edge2 A B U +
                    D1D2rhoY U * su2CrossingWilsonWord edge1 edge2 A B U) +
                  D1D2rhoZ U * su2CrossingWilsonWord edge1 edge2 A B U by
                funext U
                ring]
            rw [MeasureTheory.integral_add
                  (f := fun U =>
                    D1D2rhoX U * su2CrossingWilsonWord edge1 edge2 A B U +
                    D1D2rhoY U * su2CrossingWilsonWord edge1 edge2 A B U)
                  (g := fun U =>
                    D1D2rhoZ U * su2CrossingWilsonWord edge1 edge2 A B U)
                  (hleftX.add hleftY) hleftZ,
              MeasureTheory.integral_add
                  (f := fun U =>
                    D1D2rhoX U * su2CrossingWilsonWord edge1 edge2 A B U)
                  (g := fun U =>
                    D1D2rhoY U * su2CrossingWilsonWord edge1 edge2 A B U)
                  hleftX hleftY]
    _ =
        (∫ U, rho U *
          su2CrossingMixedGenerator edge1 edge2 A B su2PauliX su2PauliX U
          ∂su2FiniteProductHaar I) +
        (∫ U, rho U *
          su2CrossingMixedGenerator edge1 edge2 A B su2PauliY su2PauliY U
          ∂su2FiniteProductHaar I) +
        (∫ U, rho U *
          su2CrossingMixedGenerator edge1 edge2 A B su2PauliZ su2PauliZ U
          ∂su2FiniteProductHaar I) := by rw [hX, hY, hZ]
    _ = ∫ U, rho U *
        (su2CrossingMixedGenerator edge1 edge2 A B su2PauliX su2PauliX U +
          su2CrossingMixedGenerator edge1 edge2 A B su2PauliY su2PauliY U +
          su2CrossingMixedGenerator edge1 edge2 A B su2PauliZ su2PauliZ U)
        ∂su2FiniteProductHaar I := by
          rw [show (fun U => rho U *
              (su2CrossingMixedGenerator edge1 edge2 A B su2PauliX su2PauliX U +
                su2CrossingMixedGenerator edge1 edge2 A B su2PauliY su2PauliY U +
                su2CrossingMixedGenerator edge1 edge2 A B su2PauliZ su2PauliZ U)) =
              fun U =>
                (rho U * su2CrossingMixedGenerator edge1 edge2 A B
                    su2PauliX su2PauliX U +
                  rho U * su2CrossingMixedGenerator edge1 edge2 A B
                    su2PauliY su2PauliY U) +
                rho U * su2CrossingMixedGenerator edge1 edge2 A B
                  su2PauliZ su2PauliZ U by
            funext U
            ring]
          rw [MeasureTheory.integral_add
                (f := fun U =>
                  rho U * su2CrossingMixedGenerator edge1 edge2 A B
                    su2PauliX su2PauliX U +
                  rho U * su2CrossingMixedGenerator edge1 edge2 A B
                    su2PauliY su2PauliY U)
                (g := fun U =>
                  rho U * su2CrossingMixedGenerator edge1 edge2 A B
                    su2PauliZ su2PauliZ U)
                (hrightX.add hrightY) hrightZ,
            MeasureTheory.integral_add
                (f := fun U =>
                  rho U * su2CrossingMixedGenerator edge1 edge2 A B
                    su2PauliX su2PauliX U)
                (g := fun U =>
                  rho U * su2CrossingMixedGenerator edge1 edge2 A B
                    su2PauliY su2PauliY U)
                hrightX hrightY]
    _ = ∫ U, rho U *
        (-(1 / 4 : Complex) * su2CrossingDirectResolution edge1 edge2 A B U -
          (1 / 2 : Complex) * su2CrossingReverseResolution edge1 edge2 A B U)
        ∂su2FiniteProductHaar I := by
          apply integral_congr_ae
          exact ae_of_all _ fun U => by
            change rho U *
                (su2CrossingMixedGenerator edge1 edge2 A B su2PauliX su2PauliX U +
                  su2CrossingMixedGenerator edge1 edge2 A B su2PauliY su2PauliY U +
                  su2CrossingMixedGenerator edge1 edge2 A B su2PauliZ su2PauliZ U) =
              rho U *
                (-(1 / 4 : Complex) * su2CrossingDirectResolution edge1 edge2 A B U -
                  (1 / 2 : Complex) * su2CrossingReverseResolution edge1 edge2 A B U)
            rw [su2CrossingMixedGenerator_pauli_sum_closed]

end Lean2dYangMills
