/-
SEALED SOURCE-SPECIFIC BRICK -- COMPILER-VERIFIED.

This scratch file isolates the topology below Step 8b.23.  The centered
fundamental interval is forced by the already constructed mass-uniform seam:
under `p(t) = -2*pi*t`, its endpoints are the physical faces `pi` and `-pi`.

No physical endpoint, Fourier coefficient, Green bound, `B0`, window-15
attainment or terminal field is asserted here.
-/

import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Topology.Separation.Hausdorff


namespace YangMills.RG

noncomputable section

open MeasureTheory

/-- Centered representatives of the unit additive circle. -/
abbrev CMP89CenteredUnitInterval :=
  Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)

/-- Finite product of centered circle representatives. -/
abbrev CMP89CenteredUnitCube (iota : Type*) :=
  iota → CMP89CenteredUnitInterval

/-- Lower face of the centered unit fundamental interval. -/
def cmp89CenteredUnitLeft : CMP89CenteredUnitInterval :=
  ⟨-(1 / 2 : ℝ), by norm_num⟩

/-- Upper face of the centered unit fundamental interval. -/
def cmp89CenteredUnitRight : CMP89CenteredUnitInterval :=
  ⟨(1 / 2 : ℝ), by norm_num⟩

/-- Coordinatewise quotient from the centered closed cube to the unit
additive torus. -/
def cmp89CenteredUnitCubeToTorus
    {iota : Type*} (x : CMP89CenteredUnitCube iota) :
    UnitAddTorus iota :=
  fun i ↦ (x i).1

/-- Two centered representatives of one unit-circle point are either equal
or are exactly the two oppositely ordered boundary representatives.  This is
the one-coordinate input to the finite face-replacement proof. -/
theorem cmp89CenteredUnitInterval_eq_or_oppositeEndpoints
    {x y : CMP89CenteredUnitInterval}
    (hxy : ((x.1 : ℝ) : UnitAddCircle) = (y.1 : UnitAddCircle)) :
    x = y ∨
      (x.1 = -(1 / 2 : ℝ) ∧ y.1 = (1 / 2 : ℝ)) ∨
      (x.1 = (1 / 2 : ℝ) ∧ y.1 = -(1 / 2 : ℝ)) := by
  have hfaces :
      (((-(1 / 2 : ℝ) : ℝ) : UnitAddCircle)) =
        ((((1 / 2 : ℝ) : ℝ) : UnitAddCircle)) := by
    simpa only [show (-(1 / 2 : ℝ)) + 1 = 1 / 2 by ring] using
      (AddCircle.coe_add_period (p := (1 : ℝ)) (-(1 / 2 : ℝ))).symm
  have hleftMem : (-(1 / 2 : ℝ)) ∈
      Set.Ico (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ) + 1) := by
    constructor <;> norm_num
  by_cases hxRight : x.1 = (1 / 2 : ℝ)
  · by_cases hyRight : y.1 = (1 / 2 : ℝ)
    · left
      apply Subtype.ext
      linarith
    · right
      right
      refine ⟨hxRight, ?_⟩
      have hyMem : y.1 ∈
          Set.Ico (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ) + 1) := by
        constructor
        · exact y.property.1
        · have hyLt : y.1 < (1 / 2 : ℝ) :=
            lt_of_le_of_ne y.property.2 hyRight
          simpa only [show -(1 / 2 : ℝ) + 1 = 1 / 2 by ring] using hyLt
      have hleftEqY :
          (((-(1 / 2 : ℝ) : ℝ) : UnitAddCircle)) =
            ((y.1 : ℝ) : UnitAddCircle) := by
        rw [hfaces]
        simpa only [hxRight] using hxy
      exact ((AddCircle.coe_eq_coe_iff_of_mem_Ico hleftMem hyMem).mp
        hleftEqY).symm
  · have hxMem : x.1 ∈
        Set.Ico (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ) + 1) := by
      constructor
      · exact x.property.1
      · have hxLt : x.1 < (1 / 2 : ℝ) :=
          lt_of_le_of_ne x.property.2 hxRight
        simpa only [show -(1 / 2 : ℝ) + 1 = 1 / 2 by ring] using hxLt
    by_cases hyRight : y.1 = (1 / 2 : ℝ)
    · right
      left
      refine ⟨?_, hyRight⟩
      have hXLeft :
          ((x.1 : ℝ) : UnitAddCircle) =
            (((-(1 / 2 : ℝ) : ℝ) : UnitAddCircle)) := by
        rw [hfaces]
        simpa only [hyRight] using hxy
      exact (AddCircle.coe_eq_coe_iff_of_mem_Ico hxMem hleftMem).mp
        hXLeft
    · left
      have hyMem : y.1 ∈
          Set.Ico (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ) + 1) := by
        constructor
        · exact y.property.1
        · have hyLt : y.1 < (1 / 2 : ℝ) :=
            lt_of_le_of_ne y.property.2 hyRight
          simpa only [show -(1 / 2 : ℝ) + 1 = 1 / 2 by ring] using hyLt
      apply Subtype.ext
      exact (AddCircle.coe_eq_coe_iff_of_mem_Ico hxMem hyMem).mp hxy

/-- Replace the coordinates in `S` by their values in `y`, leaving every
other coordinate at its value in `x`. -/
def cmp89CenteredUnitCubeReplace
    {iota : Type*} [DecidableEq iota]
    (x y : CMP89CenteredUnitCube iota) (S : Finset iota) :
    CMP89CenteredUnitCube iota :=
  fun i ↦ if i ∈ S then y i else x i

/-- One coordinate can be replaced without changing `f` whenever its two
values represent the same circle point and `f` has the named opposite-face
seam. -/
theorem cmp89CenteredUnitCube_update_eq_of_faceSeam
    {iota E : Type*} [DecidableEq iota]
    (f : CMP89CenteredUnitCube iota → E)
    (hface : ∀ (z : CMP89CenteredUnitCube iota) (i : iota),
      f (Function.update z i cmp89CenteredUnitLeft) =
        f (Function.update z i cmp89CenteredUnitRight))
    (z : CMP89CenteredUnitCube iota) (i : iota)
    {x y : CMP89CenteredUnitInterval}
    (hxy : ((x.1 : ℝ) : UnitAddCircle) = (y.1 : UnitAddCircle)) :
    f (Function.update z i x) = f (Function.update z i y) := by
  rcases cmp89CenteredUnitInterval_eq_or_oppositeEndpoints hxy with
    hEq | hForward | hBackward
  · subst y
    rfl
  · rcases hForward with ⟨hx, hy⟩
    have hx' : x = cmp89CenteredUnitLeft := by
      apply Subtype.ext
      exact hx
    have hy' : y = cmp89CenteredUnitRight := by
      apply Subtype.ext
      exact hy
    rw [hx', hy']
    exact hface z i
  · rcases hBackward with ⟨hx, hy⟩
    have hx' : x = cmp89CenteredUnitRight := by
      apply Subtype.ext
      exact hx
    have hy' : y = cmp89CenteredUnitLeft := by
      apply Subtype.ext
      exact hy
    rw [hx', hy']
    exact (hface z i).symm

/-- Coordinate face seams imply constancy on every fibre of the centered
cube covering.  The proof performs a finite sequence of coordinate
replacements; no global periodicity or pre-supplied `FactorsThrough` witness
is used. -/
theorem cmp89CenteredUnitCube_factorsThrough_of_faceSeam
    {iota E : Type*} [Fintype iota] [DecidableEq iota]
    (f : CMP89CenteredUnitCube iota → E)
    (hface : ∀ (z : CMP89CenteredUnitCube iota) (i : iota),
      f (Function.update z i cmp89CenteredUnitLeft) =
        f (Function.update z i cmp89CenteredUnitRight)) :
    Function.FactorsThrough f
      (cmp89CenteredUnitCubeToTorus (iota := iota)) := by
  intro x y hxy
  have hcoord : ∀ i,
      (((x i).1 : ℝ) : UnitAddCircle) = ((y i).1 : UnitAddCircle) := by
    intro i
    exact congrFun hxy i
  have hchain : ∀ S : Finset iota,
      f x = f (cmp89CenteredUnitCubeReplace x y S) := by
    intro S
    induction S using Finset.induction_on with
    | empty => rfl
    | @insert i S hi ih =>
        have hbefore :
            cmp89CenteredUnitCubeReplace x y S =
              Function.update
                (cmp89CenteredUnitCubeReplace x y S) i (x i) := by
          funext k
          by_cases hki : k = i
          · subst k
            simp [cmp89CenteredUnitCubeReplace, hi]
          · simp [Function.update, hki,
              cmp89CenteredUnitCubeReplace]
        have hafter :
            cmp89CenteredUnitCubeReplace x y (insert i S) =
              Function.update
                (cmp89CenteredUnitCubeReplace x y S) i (y i) := by
          funext k
          by_cases hki : k = i
          · subst k
            simp [cmp89CenteredUnitCubeReplace]
          · simp [Function.update, hki,
              cmp89CenteredUnitCubeReplace]
        calc
          f x = f (cmp89CenteredUnitCubeReplace x y S) := ih
          _ = f (Function.update
                (cmp89CenteredUnitCubeReplace x y S) i (x i)) := by
              rw [← hbefore]
          _ = f (Function.update
                (cmp89CenteredUnitCubeReplace x y S) i (y i)) :=
              cmp89CenteredUnitCube_update_eq_of_faceSeam
                f hface _ i (hcoord i)
          _ = f (cmp89CenteredUnitCubeReplace x y (insert i S)) := by
              rw [hafter]
  have hfinal :
      cmp89CenteredUnitCubeReplace x y (Finset.univ : Finset iota) = y := by
    funext i
    simp [cmp89CenteredUnitCubeReplace]
  have h := hchain (Finset.univ : Finset iota)
  rw [hfinal] at h
  exact h

/-- The centered product covering map is continuous. -/
theorem continuous_cmp89CenteredUnitCubeToTorus
    {iota : Type*} [Fintype iota] :
    Continuous
      (cmp89CenteredUnitCubeToTorus (iota := iota)) := by
  exact continuous_pi fun i =>
    (AddCircle.continuous_mk' (1 : ℝ)).comp
      (continuous_subtype_val.comp (continuous_apply i))

/-- Every torus point has a centered half-open representative, hence a point
in the centered closed cube. -/
theorem surjective_cmp89CenteredUnitCubeToTorus
    {iota : Type*} [Fintype iota] :
    Function.Surjective
      (cmp89CenteredUnitCubeToTorus (iota := iota)) := by
  intro z
  let e := AddCircle.equivIoc (1 : ℝ) (-(1 / 2 : ℝ))
  let x : CMP89CenteredUnitCube iota := fun i ↦
    ⟨(e (z i)).1, by
      have hi := (e (z i)).property
      constructor
      · exact le_of_lt hi.1
      · simpa only [show -(1 / 2 : ℝ) + 1 = 1 / 2 by ring] using hi.2⟩
  refine ⟨x, ?_⟩
  funext i
  change (((e (z i)).1 : ℝ) : UnitAddCircle) = z i
  change e.symm (e (z i)) = z i
  exact e.symm_apply_apply (z i)

/-- The centered finite product covering is a quotient map.  This is the
topological constructor consumed by the later seam-derived lift; it assumes
no `FactorsThrough` proof. -/
theorem isQuotientMap_cmp89CenteredUnitCubeToTorus
    {iota : Type*} [Fintype iota] :
    Topology.IsQuotientMap
      (cmp89CenteredUnitCubeToTorus (iota := iota)) :=
  IsQuotientMap.of_surjective_continuous
    surjective_cmp89CenteredUnitCubeToTorus
    continuous_cmp89CenteredUnitCubeToTorus

/-- Bundled centered covering used by `IsQuotientMap.lift`. -/
def cmp89CenteredUnitCubeCovering
    {iota : Type*} [Fintype iota] :
    C(CMP89CenteredUnitCube iota, UnitAddTorus iota) where
  toFun := cmp89CenteredUnitCubeToTorus
  continuous_toFun := continuous_cmp89CenteredUnitCubeToTorus

/-- Bundled covering is the same quotient map. -/
theorem isQuotientMap_cmp89CenteredUnitCubeCovering
    {iota : Type*} [Fintype iota] :
    Topology.IsQuotientMap
      (cmp89CenteredUnitCubeCovering (iota := iota)) := by
  simpa [cmp89CenteredUnitCubeCovering] using
    (isQuotientMap_cmp89CenteredUnitCubeToTorus (iota := iota))

/-- Descend a continuous centered-cube function using only its coordinate
face seams.  The `FactorsThrough` witness is constructed internally by the
finite replacement theorem above. -/
noncomputable def cmp89CenteredUnitCubeLift
    {iota E : Type*} [Fintype iota] [DecidableEq iota]
    [TopologicalSpace E]
    (f : C(CMP89CenteredUnitCube iota, E))
    (hface : ∀ (z : CMP89CenteredUnitCube iota) (i : iota),
      f (Function.update z i cmp89CenteredUnitLeft) =
        f (Function.update z i cmp89CenteredUnitRight)) :
    C(UnitAddTorus iota, E) :=
  (isQuotientMap_cmp89CenteredUnitCubeCovering (iota := iota)).lift f
    (by
      simpa [cmp89CenteredUnitCubeCovering] using
        cmp89CenteredUnitCube_factorsThrough_of_faceSeam f hface)

/-- Exact pullback identity for the seam-derived lift. -/
theorem cmp89CenteredUnitCubeLift_comp_covering
    {iota E : Type*} [Fintype iota] [DecidableEq iota]
    [TopologicalSpace E]
    (f : C(CMP89CenteredUnitCube iota, E))
    (hface : ∀ (z : CMP89CenteredUnitCube iota) (i : iota),
      f (Function.update z i cmp89CenteredUnitLeft) =
        f (Function.update z i cmp89CenteredUnitRight)) :
    (cmp89CenteredUnitCubeLift f hface).comp
        cmp89CenteredUnitCubeCovering = f := by
  unfold cmp89CenteredUnitCubeLift
  exact Topology.IsQuotientMap.lift_comp _ _ _

/-- Product Lebesgue measure on the centered half-open real cube.  The
topological quotient uses `Icc`; this measure deliberately uses the literal
fundamental domain `Ioc`. -/
def cmp89CenteredUnitRealCubeMeasure
    (iota : Type*) [Fintype iota] : Measure (iota → ℝ) :=
  Measure.pi fun _ : iota =>
    volume.restrict (Set.Ioc (-(1 / 2 : ℝ)) (1 / 2 : ℝ))

/-- Coordinate quotient on the ambient real product used by the measure
transport. -/
def cmp89CenteredUnitRealCubeToTorus
    {iota : Type*} (x : iota → ℝ) : UnitAddTorus iota :=
  fun i => (x i : UnitAddCircle)

/-- The product covering sends the centered half-open cube measure exactly
to Haar measure on the unit torus. -/
theorem measurePreserving_cmp89CenteredUnitRealCubeToTorus
    {iota : Type*} [Fintype iota] :
    MeasurePreserving
      (cmp89CenteredUnitRealCubeToTorus (iota := iota))
      (cmp89CenteredUnitRealCubeMeasure iota)
      (volume : Measure (UnitAddTorus iota)) := by
  have hcoordinate : ∀ _ : iota,
      MeasurePreserving (fun x : ℝ => (x : UnitAddCircle))
        (volume.restrict (Set.Ioc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)))
        volume := by
    intro _
    simpa only [show -(1 / 2 : ℝ) + 1 = 1 / 2 by ring] using
      (AddCircle.measurePreserving_mk (1 : ℝ) (-(1 / 2 : ℝ)))
  have hpi := MeasureTheory.measurePreserving_pi
    (fun _ : iota =>
      volume.restrict (Set.Ioc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)))
    (fun _ : iota => (volume : Measure UnitAddCircle))
    hcoordinate
  simpa [cmp89CenteredUnitRealCubeToTorus,
    cmp89CenteredUnitRealCubeMeasure, MeasureTheory.volume_pi] using hpi

/-- Haar integration on the unit torus is exactly integration of the
pullback over the centered half-open real cube.  This is the generic measure
half of G23.4; it contains no physical `2*pi` affine change of variables. -/
theorem integral_cmp89CenteredUnitRealCubeToTorus
    {iota : Type*} [Fintype iota]
    (f : C(UnitAddTorus iota, ℂ)) :
    (∫ t, f t ∂(volume : Measure (UnitAddTorus iota))) =
      ∫ x, f (cmp89CenteredUnitRealCubeToTorus x)
        ∂cmp89CenteredUnitRealCubeMeasure iota := by
  let h :=
    measurePreserving_cmp89CenteredUnitRealCubeToTorus (iota := iota)
  rw [← h.map_eq]
  exact MeasureTheory.integral_map h.aemeasurable
    f.continuous.aestronglyMeasurable

end

end YangMills.RG
