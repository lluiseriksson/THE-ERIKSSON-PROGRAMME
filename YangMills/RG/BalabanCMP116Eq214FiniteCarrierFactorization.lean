/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq214ContourDeterminantRatio
import YangMills.RG.BalabanCMP116PhysicalEndomorphismMatrix
import YangMills.RG.BalabanCMP99LocalizedParametrixDecay

/-!
# Finite-carrier matrix factorization for the contour determinant

The diagonal projection onto a finite coordinate carrier factors exactly as
zero-extension followed by restriction.  Consequently every ambient product
`L P_S R` factors through the subtype `S`, which is the rectangular input
required by Weinstein--Aronszajn.
-/

namespace YangMills.RG

open Matrix

noncomputable section

/-- Zero-extension matrix from a finite coordinate subtype to the ambient
coordinate space. -/
def cmp116FinsetColumnInclusion
    {ι α : Type*} [Fintype ι] [DecidableEq ι]
    [CommSemiring α]
    (S : Finset ι) : Matrix ι S α :=
  fun i s => if i = (s : ι) then 1 else 0

/-- Coordinate-restriction matrix from the ambient coordinate space to a
finite subtype. -/
def cmp116FinsetCoordinateRestriction
    {ι α : Type*} [Fintype ι] [DecidableEq ι]
    [CommSemiring α]
    (S : Finset ι) : Matrix S ι α :=
  fun s i => if (s : ι) = i then 1 else 0

/-- Literal diagonal projection onto a finite coordinate carrier. -/
def cmp116FinsetCoordinateProjection
    {ι α : Type*} [Fintype ι] [DecidableEq ι]
    [CommSemiring α]
    (S : Finset ι) : Matrix ι ι α :=
  Matrix.diagonal fun i => if i ∈ S then 1 else 0

/-- Zero extension followed by restriction is exactly the finite-carrier
diagonal projection. -/
theorem cmp116FinsetColumnInclusion_mul_restriction
    {ι α : Type*} [Fintype ι] [DecidableEq ι]
    [CommSemiring α]
    (S : Finset ι) :
    cmp116FinsetColumnInclusion (α := α) S *
        cmp116FinsetCoordinateRestriction (α := α) S =
      cmp116FinsetCoordinateProjection (α := α) S := by
  classical
  ext i j
  rw [Matrix.mul_apply, ← Finset.attach_eq_univ]
  calc
    (∑ x ∈ S.attach,
        cmp116FinsetColumnInclusion (α := α) S i x *
          cmp116FinsetCoordinateRestriction (α := α) S x j) =
        ∑ x ∈ S,
          (if i = x then 1 else 0) *
            (if x = j then 1 else 0) := by
      exact Finset.sum_attach S fun x =>
        (if i = x then 1 else 0) * (if x = j then 1 else 0)
    _ = cmp116FinsetCoordinateProjection (α := α) S i j := by
      by_cases hij : i = j
      · subst j
        simp [cmp116FinsetCoordinateProjection]
      · simp [cmp116FinsetCoordinateProjection, hij]

/-- Any ambient product with one finite-carrier projection factors through
the carrier subtype. -/
theorem mul_cmp116FinsetCoordinateProjection_mul_eq_factorized
    {ι α : Type*} [Fintype ι] [DecidableEq ι]
    [CommSemiring α]
    (S : Finset ι) (L R : Matrix ι ι α) :
    L * cmp116FinsetCoordinateProjection (α := α) S * R =
      (L * cmp116FinsetColumnInclusion (α := α) S) *
        (cmp116FinsetCoordinateRestriction (α := α) S * R) := by
  rw [← cmp116FinsetColumnInclusion_mul_restriction]
  simp only [Matrix.mul_assoc]

/-- Bond--Lie scalar coordinates lying over a finite physical bond core. -/
def cmp116PhysicalCoreCoordinates
    {d N Nc : ℕ} [NeZero N]
    (S : Finset (PhysicalBond d N)) :
    Finset (CMP116PhysicalWalkCoordinate d N Nc) :=
  S ×ˢ (Finset.univ : Finset (Fin (Nc ^ 2 - 1)))

@[simp]
theorem mem_cmp116PhysicalCoreCoordinates_iff
    {d N Nc : ℕ} [NeZero N]
    (S : Finset (PhysicalBond d N))
    (qa : CMP116PhysicalWalkCoordinate d N Nc) :
    qa ∈ cmp116PhysicalCoreCoordinates (Nc := Nc) S ↔ qa.1 ∈ S := by
  simp [cmp116PhysicalCoreCoordinates]

/-- Exact dimension of the scalar coordinate space over a physical bond
core. -/
theorem card_cmp116PhysicalCoreCoordinates
    {d N Nc : ℕ} [NeZero N]
    (S : Finset (PhysicalBond d N)) :
    (cmp116PhysicalCoreCoordinates (Nc := Nc) S).card =
      S.card * (Nc ^ 2 - 1) := by
  simp [cmp116PhysicalCoreCoordinates]

/-- The canonical complex matrix of a physical bond projection is literally
the diagonal projection onto the corresponding bond--Lie coordinates. -/
theorem cmp116PhysicalEndomorphismComplexMatrix_projection
    {d N Nc : ℕ}
    [NeZero d] [NeZero N] [NeZero (Nc ^ 2 - 1)]
    (S : Finset (PhysicalBond d N)) :
    cmp116PhysicalEndomorphismComplexMatrix
        (physicalBondProjection S) =
      cmp116FinsetCoordinateProjection (α := ℂ)
        (cmp116PhysicalCoreCoordinates (Nc := Nc) S) := by
  classical
  ext row col
  rcases row with ⟨target, output⟩
  rcases col with ⟨source, input⟩
  rw [cmp116PhysicalEndomorphismComplexMatrix_apply]
  simp only [cmp116ComplexPhysicalOperatorCoefficient,
    cmp116PhysicalOperatorCoefficient]
  by_cases hsource : source ∈ S
  · rw [physicalBondProjection_single_mem S source
      (EuclideanSpace.single input (1 : ℝ)) hsource]
    by_cases hb : target = source
    · subst target
      by_cases ha : output = input
      · subst output
        simp [cmp116FinsetCoordinateProjection,
          cmp116PhysicalCoreCoordinates,
          singlePhysicalBondCochain, hsource]
      · simp [cmp116FinsetCoordinateProjection,
          cmp116PhysicalCoreCoordinates,
          singlePhysicalBondCochain, ha]
    · simp [cmp116FinsetCoordinateProjection,
        cmp116PhysicalCoreCoordinates,
        singlePhysicalBondCochain, hb]
  · rw [physicalBondProjection_single_not_mem S source
      (EuclideanSpace.single input (1 : ℝ)) hsource]
    by_cases hrow : (target, output) = (source, input)
    · cases hrow
      simp [cmp116FinsetCoordinateProjection,
        cmp116PhysicalCoreCoordinates, hsource]
    · simp [cmp116FinsetCoordinateProjection, hrow]

end

end YangMills.RG
