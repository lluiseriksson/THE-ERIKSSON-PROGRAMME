/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/
import YangMills.Continuum.WeakLimit
import YangMills.L1_GibbsMeasure.ThermodynamicNonvacuity

/-!
# A compiled nonempty discrete-to-test-distribution example

The example uses the actual four-dimensional `SU(2)` thermodynamic Gibbs
constructor at the positive coupling `10⁻⁶`, the nonconstant physical
plaquette energy `Re tr U`, and the explicit scale `aₙ = 1/(n+1)`.

The observable embedding is deliberately the identity.  Hence this is an
example of the C0 transport mechanics, not a physical rescaling theorem and
not a continuum Yang--Mills construction.  Nonemptiness is checked with a
four-edge plaquette observable; positive limiting variance remains the typed
open obligation `HasFluctuatingLimit`.
-/

namespace YangMills.Continuum

open Filter MeasureTheory Topology
open YangMills WindowPolymer

/-- The positive endpoint of the proved four-dimensional strong-coupling
window. -/
noncomputable def exampleD4Coupling : ℝ :=
  explicitStrongCouplingRadiusD4

theorem exampleD4Coupling_pos :
    0 < exampleD4Coupling :=
  explicitStrongCouplingRadiusD4_pos

theorem exampleD4Coupling_ne_zero :
    exampleD4Coupling ≠ 0 :=
  ne_of_gt exampleD4Coupling_pos

/-- The actual scale-indexed state sequence.  Its state at every scale is
definitionally produced by `integerInfiniteLocalGibbsState`. -/
noncomputable def exampleD4GibbsStateSequence :
    GibbsStateSequence 4 SU2GaugeGroup :=
  GibbsStateSequence.constantCoupling
    reciprocalScale
    (sunHaarProb 2) (by infer_instance)
    su2FundamentalPlaquetteEnergy
    measurable_su2FundamentalPlaquetteEnergy
    2 exampleD4Coupling
    su2FundamentalPlaquetteEnergy_bounded
    (su2D4UniformLocalKPRegimeOfBound
      exampleD4Coupling (by
        rw [abs_of_pos exampleD4Coupling_pos]
        exact le_rfl))

/-- Pointwise weak convergence on the full integer local-observable test
algebra for the constant-coupling mechanics example. -/
theorem exampleD4_hasWeakLimit :
    HasWeakLimit
      exampleD4GibbsStateSequence
      (identityObservableEmbedding
        (d := 4) (G := SU2GaugeGroup)) := by
  exact hasWeakLimit_constantCoupling_identity
    reciprocalScale
    (sunHaarProb 2) (by infer_instance)
    su2FundamentalPlaquetteEnergy
    measurable_su2FundamentalPlaquetteEnergy
    2 exampleD4Coupling
    su2FundamentalPlaquetteEnergy_bounded
    (su2D4UniformLocalKPRegimeOfBound
      exampleD4Coupling (by
        rw [abs_of_pos exampleD4Coupling_pos]
        exact le_rfl))

/-- The same genuine state sequence converges on canonically floor-embedded
one-point cylinders, by translation invariance rather than by assuming a
limit functional. -/
theorem exampleD4_pointCylinder_hasWeakLimit :
    HasWeakLimit
      exampleD4GibbsStateSequence
      (pointCylinderEmbedding
        (d := 4) (G := SU2GaugeGroup) reciprocalScale) := by
  exact hasWeakLimit_constantCoupling_pointCylinder
    reciprocalScale
    (sunHaarProb 2) (by infer_instance)
    su2FundamentalPlaquetteEnergy
    measurable_su2FundamentalPlaquetteEnergy
    2 exampleD4Coupling
    su2FundamentalPlaquetteEnergy_bounded
    (su2D4UniformLocalKPRegimeOfBound
      exampleD4Coupling (by
        rw [abs_of_pos exampleD4Coupling_pos]
        exact le_rfl))

/-- A genuine four-edge plaquette test in the integer-coordinate chart. -/
noncomputable def exampleD4PlaquetteTest :
    IntegerLocalObservable 4 SU2GaugeGroup :=
  IntegerLocalObservable.ofCompatible
    (CompatibleLocalObservable.plaquetteHolonomy
      (d := 4) (G := SU2GaugeGroup)
      (by omega)
      su2FundamentalPlaquetteEnergy
      measurable_su2FundamentalPlaquetteEnergy
      2 (by norm_num)
      su2FundamentalPlaquetteEnergy_bounded)

/-- The example test is not an empty-support constant: it reads four edges. -/
theorem exampleD4PlaquetteTest_support_card :
    Fintype.card exampleD4PlaquetteTest.Support = 4 := by
  rfl

/-- A nonempty plaquette cylinder anchored at a nonzero physical point. -/
noncomputable def exampleD4PointCylinder :
    PointCylinder 4 SU2GaugeGroup where
  point := fun j => (j : ℝ) + 1
  observable := exampleD4PlaquetteTest

/-- The actual evaluations of the canonically floor-translated plaquette
cylinder converge. -/
theorem tendsto_exampleD4PointCylinder :
    Tendsto
      (fun n =>
        exampleD4GibbsStateSequence.expectation
          (pointCylinderEmbedding
            (d := 4) (G := SU2GaugeGroup) reciprocalScale)
          n exampleD4PointCylinder)
      atTop
      (𝓝 (weakLimitValue exampleD4_pointCylinder_hasWeakLimit
        exampleD4PointCylinder)) :=
  tendsto_weakLimitValue
    exampleD4_pointCylinder_hasWeakLimit exampleD4PointCylinder

/-- The compiled discrete-to-distribution statement for the nonempty test:
the actual scale-indexed Gibbs evaluations converge to the constructed weak
limit value. -/
theorem tendsto_exampleD4PlaquetteTest :
    Tendsto
      (fun n =>
        exampleD4GibbsStateSequence.expectation
          (identityObservableEmbedding
            (d := 4) (G := SU2GaugeGroup))
          n exampleD4PlaquetteTest)
      atTop
      (𝓝 (weakLimitValue exampleD4_hasWeakLimit
        exampleD4PlaquetteTest)) :=
  tendsto_weakLimitValue exampleD4_hasWeakLimit exampleD4PlaquetteTest

/-- The weak-limit functional of the example is normalized. -/
theorem exampleD4_weakLimit_one :
    weakLimitValue exampleD4_hasWeakLimit
        (integerObservableTestAlgebra
          (d := 4) (G := SU2GaugeGroup)).one = 1 := by
  exact weakLimitValue_one
    (integerObservableTestAlgebra
      (d := 4) (G := SU2GaugeGroup))
    exampleD4GibbsStateSequence
    (identityObservableEmbedding
      (d := 4) (G := SU2GaugeGroup))
    exampleD4_hasWeakLimit
    identityObservableEmbedding_compatible

/-- The weak-limit functional of the example is invariant under every
integer translation, including inverse translations. -/
theorem exampleD4_weakLimit_translate
    (z : Fin 4 → ℤ)
    (F : IntegerLocalObservable 4 SU2GaugeGroup) :
    weakLimitValue exampleD4_hasWeakLimit (z +ᵥ F) =
      weakLimitValue exampleD4_hasWeakLimit F := by
  exact weakLimitValue_translate
    (integerObservableTestAlgebra
      (d := 4) (G := SU2GaugeGroup))
    exampleD4GibbsStateSequence
    (identityObservableEmbedding
      (d := 4) (G := SU2GaugeGroup))
    exampleD4_hasWeakLimit
    identityObservableEmbedding_compatible z F

end YangMills.Continuum
