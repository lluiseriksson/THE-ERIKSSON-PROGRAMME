/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.PhysicalGaugeCochains
import YangMills.RG.PhysicalGaugeFluctuationActivity
import YangMills.RG.BalabanCMP116Dmu0
import YangMills.RG.AppendixFCover

/-!
# Physical gauge / CMP116 finite coordinate dictionary

This file fixes the first purely finite dictionary between physical positive
bonds with `su(N)` coordinates and CMP116 cube coordinates.  It records an
exact scalar-coordinate equivalence and derives the induced pull/push maps
between cube coordinate fields and physical one-cochains.

Honest scope: this is only product-coordinate bookkeeping.  It does not
construct local polymer activities, identify a Wilson Hessian, prove a measure
change theorem, or supply any analytic estimate.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills.RG

open MeasureTheory
open scoped BigOperators RealInnerProductSpace

/-- Flattened CMP116 scalar coordinates: a cube and an internal coordinate. -/
abbrev CMP116CoordIndex (d L lieDim : ℕ) :=
  Cube d L × Fin lieDim

/-- Flattened physical scalar coordinates: a positive physical bond and a Lie
coordinate. -/
abbrev PhysicalGaugeCoordIndex (d N Nc : ℕ) [NeZero N] :=
  PhysicalBond d N × Fin (Nc ^ 2 - 1)

/-- The finite map from physical bonds to CMP116 cubes, together with the
CMP116 active cube set used by later layers. -/
structure PhysicalGaugeCMP116SiteMap
    (dPhys N d L : ℕ) [NeZero N] [NeZero L] where
  bondToCube : PhysicalBond dPhys N → Cube d L
  Omega : Finset (Cube d L)

namespace PhysicalGaugeCMP116SiteMap

variable {dPhys N d L : ℕ} [NeZero N] [NeZero L]

/-- Physical bonds whose assigned CMP116 cube lies in `X`. -/
noncomputable def physicalBondsOver
    (S : PhysicalGaugeCMP116SiteMap dPhys N d L)
    (X : Finset (Cube d L)) :
    Finset (PhysicalBond dPhys N) :=
  Finset.univ.filter fun b => S.bondToCube b ∈ X

@[simp] theorem mem_physicalBondsOver
    (S : PhysicalGaugeCMP116SiteMap dPhys N d L)
    (X : Finset (Cube d L)) (b : PhysicalBond dPhys N) :
    b ∈ S.physicalBondsOver X ↔ S.bondToCube b ∈ X := by
  simp [physicalBondsOver]

@[simp] theorem physicalBondsOver_empty
    (S : PhysicalGaugeCMP116SiteMap dPhys N d L) :
    S.physicalBondsOver (∅ : Finset (Cube d L)) = ∅ := by
  ext b
  simp [physicalBondsOver]

@[simp] theorem physicalBondsOver_univ
    (S : PhysicalGaugeCMP116SiteMap dPhys N d L) :
    S.physicalBondsOver (Finset.univ : Finset (Cube d L)) =
      (Finset.univ : Finset (PhysicalBond dPhys N)) := by
  ext b
  simp [physicalBondsOver]

theorem physicalBondsOver_mono
    (S : PhysicalGaugeCMP116SiteMap dPhys N d L)
    {X Y : Finset (Cube d L)} (hXY : X ⊆ Y) :
    S.physicalBondsOver X ⊆ S.physicalBondsOver Y := by
  intro b hb
  exact (S.mem_physicalBondsOver Y b).mpr
    (hXY ((S.mem_physicalBondsOver X b).mp hb))

@[simp] theorem physicalBondsOver_union
    (S : PhysicalGaugeCMP116SiteMap dPhys N d L)
    (X Y : Finset (Cube d L)) :
    S.physicalBondsOver (X ∪ Y) =
      S.physicalBondsOver X ∪ S.physicalBondsOver Y := by
  ext b
  simp [physicalBondsOver]

@[simp] theorem physicalBondsOver_inter
    (S : PhysicalGaugeCMP116SiteMap dPhys N d L)
    (X Y : Finset (Cube d L)) :
    S.physicalBondsOver (X ∩ Y) =
      S.physicalBondsOver X ∩ S.physicalBondsOver Y := by
  ext b
  simp [physicalBondsOver]

end PhysicalGaugeCMP116SiteMap

/-- A finite scalar-coordinate dictionary between CMP116 coordinates and
physical positive-bond coordinates.

The `coordEquiv_cell` field forbids mixing scalar coordinates across CMP116
cubes: a scalar coordinate tagged by cube `q` can only map to a physical bond
whose site map returns `q`. -/
structure PhysicalGaugeCMP116Dictionary
    (dPhys N Nc d L lieDim : ℕ) [NeZero N] [NeZero L] where
  siteMap : PhysicalGaugeCMP116SiteMap dPhys N d L
  coordEquiv :
    CMP116CoordIndex d L lieDim ≃ PhysicalGaugeCoordIndex dPhys N Nc
  coordEquiv_cell :
    ∀ q a, siteMap.bondToCube (coordEquiv (q, a)).1 = q

namespace PhysicalGaugeCMP116Dictionary

variable {dPhys N Nc d L lieDim : ℕ} [NeZero N] [NeZero L]

/-- Bonds assigned to a finite set of CMP116 cubes by the dictionary site map. -/
noncomputable def physicalBondsOfCells
    (D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim)
    (X : Finset (Cube d L)) :
    Finset (PhysicalBond dPhys N) :=
  D.siteMap.physicalBondsOver X

@[simp] theorem mem_physicalBondsOfCells
    (D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim)
    (X : Finset (Cube d L)) (b : PhysicalBond dPhys N) :
    b ∈ D.physicalBondsOfCells X ↔ D.siteMap.bondToCube b ∈ X := by
  simp [physicalBondsOfCells]

/-- The inverse coordinate equivalence preserves the assigned CMP116 cube. -/
theorem coordEquiv_symm_cell
    (D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim)
    (b : PhysicalBond dPhys N) (a : Fin (Nc ^ 2 - 1)) :
    (D.coordEquiv.symm (b, a)).1 = D.siteMap.bondToCube b := by
  let qa : CMP116CoordIndex d L lieDim := D.coordEquiv.symm (b, a)
  change qa.1 = D.siteMap.bondToCube b
  have hcell : D.siteMap.bondToCube (D.coordEquiv qa).1 = qa.1 := by
    simpa [qa] using D.coordEquiv_cell qa.1 qa.2
  have hpair : D.coordEquiv qa = (b, a) := by
    simp [qa]
  have hb : (D.coordEquiv qa).1 = b := congrArg Prod.fst hpair
  rw [hb] at hcell
  exact hcell.symm

/-- Pack plain scalar coordinates into the Euclidean `su(N)` coordinate model. -/
noncomputable def sunLieCoordOfScalars
    {Nc : ℕ} (f : Fin (Nc ^ 2 - 1) → ℝ) : SUNLieCoord Nc :=
  (EuclideanSpace.equiv (Fin (Nc ^ 2 - 1)) ℝ).symm f

/-- Extract one scalar coordinate from the Euclidean `su(N)` coordinate model. -/
noncomputable def sunLieCoordScalar
    {Nc : ℕ} (X : SUNLieCoord Nc) (a : Fin (Nc ^ 2 - 1)) : ℝ :=
  ((EuclideanSpace.equiv (Fin (Nc ^ 2 - 1)) ℝ) X) a

@[simp] theorem sunLieCoordScalar_sunLieCoordOfScalars
    {Nc : ℕ} (f : Fin (Nc ^ 2 - 1) → ℝ) (a : Fin (Nc ^ 2 - 1)) :
    sunLieCoordScalar (sunLieCoordOfScalars f) a = f a := by
  simp [sunLieCoordScalar, sunLieCoordOfScalars]

@[simp] theorem sunLieCoordOfScalars_sunLieCoordScalar
    {Nc : ℕ} (X : SUNLieCoord Nc) :
    sunLieCoordOfScalars (fun a => sunLieCoordScalar X a) = X := by
  apply (EuclideanSpace.equiv (Fin (Nc ^ 2 - 1)) ℝ).injective
  funext a
  simp [sunLieCoordScalar, sunLieCoordOfScalars]

/-- Pull a CMP116 cube-coordinate fluctuation field to a physical one-cochain
using the scalar-coordinate dictionary. -/
noncomputable def pullFluctuationCochain
    (D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim)
    (ξ : ∀ _ : Cube d L, Fin lieDim → ℝ) :
    PhysicalGaugeOneCochain dPhys N Nc :=
  WithLp.toLp 2 fun b : PhysicalBond dPhys N =>
    sunLieCoordOfScalars fun a : Fin (Nc ^ 2 - 1) =>
      let qa : CMP116CoordIndex d L lieDim := D.coordEquiv.symm (b, a)
      ξ qa.1 qa.2

/-- Push a physical one-cochain to CMP116 cube-coordinate fluctuation fields
using the scalar-coordinate dictionary. -/
noncomputable def pushFluctuation
    (D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim)
    (A : PhysicalGaugeOneCochain dPhys N Nc) :
    ∀ _ : Cube d L, Fin lieDim → ℝ :=
  fun q a =>
    let ba : PhysicalGaugeCoordIndex dPhys N Nc := D.coordEquiv (q, a)
    sunLieCoordScalar (A ba.1) ba.2

@[simp] theorem pushFluctuation_pullFluctuationCochain
    (D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim)
    (ξ : ∀ _ : Cube d L, Fin lieDim → ℝ) :
    D.pushFluctuation (D.pullFluctuationCochain ξ) = ξ := by
  funext q a
  simp [pushFluctuation, pullFluctuationCochain]

@[simp] theorem pullFluctuationCochain_pushFluctuation
    (D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim)
    (A : PhysicalGaugeOneCochain dPhys N Nc) :
    D.pullFluctuationCochain (D.pushFluctuation A) = A := by
  apply PiLp.ext
  intro b
  apply (EuclideanSpace.equiv (Fin (Nc ^ 2 - 1)) ℝ).injective
  funext a
  simp [pullFluctuationCochain, pushFluctuation, sunLieCoordScalar,
    sunLieCoordOfScalars]

theorem pullFluctuationCochain_add
    (D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim)
    (ξ η : ∀ _ : Cube d L, Fin lieDim → ℝ) :
    D.pullFluctuationCochain (ξ + η) =
      D.pullFluctuationCochain ξ + D.pullFluctuationCochain η := by
  apply PiLp.ext
  intro b
  apply (EuclideanSpace.equiv (Fin (Nc ^ 2 - 1)) ℝ).injective
  funext a
  simp [pullFluctuationCochain, sunLieCoordOfScalars]

theorem pullFluctuationCochain_smul
    (D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim)
    (c : ℝ) (ξ : ∀ _ : Cube d L, Fin lieDim → ℝ) :
    D.pullFluctuationCochain (c • ξ) =
      c • D.pullFluctuationCochain ξ := by
  apply PiLp.ext
  intro b
  apply (EuclideanSpace.equiv (Fin (Nc ^ 2 - 1)) ℝ).injective
  funext a
  simp [pullFluctuationCochain, sunLieCoordOfScalars]

theorem pushFluctuation_add
    (D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim)
    (A B : PhysicalGaugeOneCochain dPhys N Nc) :
    D.pushFluctuation (A + B) =
      D.pushFluctuation A + D.pushFluctuation B := by
  funext q a
  simp [pushFluctuation, sunLieCoordScalar]

theorem pushFluctuation_smul
    (D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim)
    (c : ℝ) (A : PhysicalGaugeOneCochain dPhys N Nc) :
    D.pushFluctuation (c • A) = c • D.pushFluctuation A := by
  funext q a
  simp [pushFluctuation, sunLieCoordScalar]

/-- The scalar-coordinate dictionary as a linear equivalence between CMP116
coordinate fields and physical one-cochains. -/
noncomputable def fluctuationFieldLinearEquiv
    (D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim) :
    (∀ _ : Cube d L, Fin lieDim → ℝ) ≃ₗ[ℝ]
      PhysicalGaugeOneCochain dPhys N Nc where
  toFun := D.pullFluctuationCochain
  invFun := D.pushFluctuation
  left_inv := D.pushFluctuation_pullFluctuationCochain
  right_inv := D.pullFluctuationCochain_pushFluctuation
  map_add' := D.pullFluctuationCochain_add
  map_smul' := D.pullFluctuationCochain_smul

@[simp] theorem fluctuationFieldLinearEquiv_apply
    (D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim)
    (ξ : ∀ _ : Cube d L, Fin lieDim → ℝ) :
    D.fluctuationFieldLinearEquiv ξ = D.pullFluctuationCochain ξ := rfl

@[simp] theorem fluctuationFieldLinearEquiv_symm_apply
    (D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim)
    (A : PhysicalGaugeOneCochain dPhys N Nc) :
    D.fluctuationFieldLinearEquiv.symm A = D.pushFluctuation A := rfl

/-- CMP116 agreement on `X` pulls to physical agreement on bonds over `X`. -/
theorem pullFluctuationCochain_agreeOn
    (D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim)
    {X : Finset (Cube d L)}
    {ξ η : ∀ _ : Cube d L, Fin lieDim → ℝ}
    (hξη : AgreeOn X ξ η) :
    AgreeOn (D.physicalBondsOfCells X)
      (D.pullFluctuationCochain ξ) (D.pullFluctuationCochain η) := by
  intro b hb
  apply (EuclideanSpace.equiv (Fin (Nc ^ 2 - 1)) ℝ).injective
  funext a
  let qa : CMP116CoordIndex d L lieDim := D.coordEquiv.symm (b, a)
  have hbcell : D.siteMap.bondToCube b ∈ X := by
    simpa [physicalBondsOfCells] using
      (D.siteMap.mem_physicalBondsOver X b).mp hb
  have hq : qa.1 ∈ X := by
    simpa [qa, D.coordEquiv_symm_cell b a] using hbcell
  have hcoord := congrFun (hξη qa.1 hq) qa.2
  simpa [pullFluctuationCochain, sunLieCoordOfScalars, qa] using hcoord

/-- Physical agreement on bonds over `X` pushes to CMP116 agreement on `X`. -/
theorem pushFluctuation_agreeOn
    (D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim)
    {X : Finset (Cube d L)}
    {A B : PhysicalGaugeOneCochain dPhys N Nc}
    (hAB : AgreeOn (D.physicalBondsOfCells X) A B) :
    AgreeOn X (D.pushFluctuation A) (D.pushFluctuation B) := by
  intro q hq
  funext a
  let ba : PhysicalGaugeCoordIndex dPhys N Nc := D.coordEquiv (q, a)
  have hb : ba.1 ∈ D.physicalBondsOfCells X := by
    have hcell : D.siteMap.bondToCube ba.1 = q := by
      simpa [ba] using D.coordEquiv_cell q a
    simpa [physicalBondsOfCells, hcell] using hq
  have hbond := hAB ba.1 hb
  exact congrArg (fun X : SUNLieCoord Nc => sunLieCoordScalar X ba.2) hbond

/-- The pull map is an exact support dictionary: CMP116 agreement on `X` is
equivalent to physical agreement on all bonds assigned to `X`. -/
theorem pullFluctuationCochain_agreeOn_iff
    (D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim)
    (X : Finset (Cube d L))
    (ξ η : ∀ _ : Cube d L, Fin lieDim → ℝ) :
    AgreeOn (D.physicalBondsOfCells X)
      (D.pullFluctuationCochain ξ) (D.pullFluctuationCochain η) ↔
      AgreeOn X ξ η := by
  constructor
  · intro h q hq
    funext a
    let ba : PhysicalGaugeCoordIndex dPhys N Nc := D.coordEquiv (q, a)
    have hb : ba.1 ∈ D.physicalBondsOfCells X := by
      have hcell : D.siteMap.bondToCube ba.1 = q := by
        simpa [ba] using D.coordEquiv_cell q a
      simpa [physicalBondsOfCells, hcell] using hq
    have hbond := h ba.1 hb
    have hcoord :=
      congrArg (fun X : SUNLieCoord Nc => sunLieCoordScalar X ba.2) hbond
    simpa [ba, pullFluctuationCochain, sunLieCoordScalar,
      sunLieCoordOfScalars] using hcoord
  · exact D.pullFluctuationCochain_agreeOn

/-- A separate finite-measure dictionary layer.  The equality is an explicit
field because the physical product law must be identified by a later source
or finite calculation; it is not definitionally assumed here. -/
structure PhysicalGaugeCMP116GaussianChange
    (D : PhysicalGaugeCMP116Dictionary dPhys N Nc d L lieDim) where
  gaussianCoordinateMap :
    (∀ _ : Cube d L, Fin lieDim → ℝ) →L[ℝ]
      PhysicalGaugeOneCochain dPhys N Nc
  physicalGaussian :
    Measure (PhysicalGaugeOneCochain dPhys N Nc)
  gaussianCoordinateMap_measurable :
    Measurable gaussianCoordinateMap
  map_gaussianChangeOfVariables :
    (balabanCMP116Dmu0 (Cube d L) lieDim).map gaussianCoordinateMap =
      physicalGaussian

end PhysicalGaugeCMP116Dictionary

end YangMills.RG
