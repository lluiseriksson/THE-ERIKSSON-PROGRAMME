/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99GeneralizedRandomWalk
import YangMills.RG.BalabanCMP116ComplexWeakenedRandomWalkSeries
import YangMills.RG.BalabanCMP116SourceRestrictedShiftedComplexContour

/-!
# Markov factorization of weakening monomials

The source weakening weight of a walk is indexed by the union of all cubes
visited by its localization domains.  Multiplying one monomial per step would
count a cube repeatedly when several domains activate it.  This file records
the already visited carrier and charges at a step only the genuinely new
cubes.

The resulting recursion is exact.  In particular it provides the finite
state variable needed by a future transfer-operator resummation: on a
restricted contour, the state is a subset of the finite contour carrier.
No covariance or determinant factorization is claimed here.
-/

open scoped BigOperators

namespace YangMills.RG

universe u v w

/-- Product of the weakening variables first encountered along a list of
active carriers, starting with an already visited finite carrier. -/
def cmp116ComplexVisitedWeakeningProduct
    {Delta : Type u} [DecidableEq Delta]
    (sigma : Delta → ℂ) : Finset Delta → List (Finset Delta) → ℂ
  | _, [] => 1
  | visited, active :: rest =>
      cmp116ComplexWeakeningMonomial (active \ visited) sigma *
        cmp116ComplexVisitedWeakeningProduct sigma
          (visited ∪ active) rest

/-- Multiplying the old carrier by the successive genuinely new carriers
counts every visited weakening coordinate exactly once. -/
theorem cmp116ComplexWeakeningMonomial_mul_visitedProduct
    {Delta : Type u} [DecidableEq Delta]
    (sigma : Delta → ℂ) (visited : Finset Delta) :
    ∀ carriers : List (Finset Delta),
      cmp116ComplexWeakeningMonomial visited sigma *
          cmp116ComplexVisitedWeakeningProduct sigma visited carriers =
        cmp116ComplexWeakeningMonomial
          (visited ∪ carriers.foldr (· ∪ ·) ∅) sigma := by
  intro carriers
  induction carriers generalizing visited with
  | nil =>
      simp [cmp116ComplexVisitedWeakeningProduct]
  | cons active rest ih =>
      rw [cmp116ComplexVisitedWeakeningProduct, ← mul_assoc]
      have hdisjoint : Disjoint visited (active \ visited) :=
        Finset.disjoint_sdiff
      have hunion : visited ∪ (active \ visited) = visited ∪ active := by
        ext d
        simp only [Finset.mem_union, Finset.mem_sdiff]
        tauto
      change (∏ d ∈ visited, sigma d) *
          (∏ d ∈ active \ visited, sigma d) *
            cmp116ComplexVisitedWeakeningProduct sigma
              (visited ∪ active) rest =
        cmp116ComplexWeakeningMonomial
          (visited ∪ (active ∪ rest.foldr (· ∪ ·) ∅)) sigma
      rw [← Finset.prod_union hdisjoint, hunion]
      change cmp116ComplexWeakeningMonomial (visited ∪ active) sigma *
          cmp116ComplexVisitedWeakeningProduct sigma
            (visited ∪ active) rest =
        cmp116ComplexWeakeningMonomial
          (visited ∪ (active ∪ rest.foldr (· ∪ ·) ∅)) sigma
      rw [ih]
      congr 1
      ext d
      simp only [Finset.mem_union]
      tauto

/-- Starting from the empty carrier, the visited-state product is exactly the
single monomial on the union of all active carriers. -/
theorem cmp116ComplexVisitedWeakeningProduct_empty
    {Delta : Type u} [DecidableEq Delta]
    (sigma : Delta → ℂ) (carriers : List (Finset Delta)) :
    cmp116ComplexVisitedWeakeningProduct sigma ∅ carriers =
      cmp116ComplexWeakeningMonomial
        (carriers.foldr (· ∪ ·) ∅) sigma := by
  simpa [cmp116ComplexWeakeningMonomial] using
    cmp116ComplexWeakeningMonomial_mul_visitedProduct
      sigma (∅ : Finset Delta) carriers

/-- The weakening monomial of a generalized walk is an exact ordered product
of the newly activated coordinates.  This is the source-faithful
finite-state form of the union monomial. -/
theorem CMP99GeneralizedWalk.complexWeakeningMonomial_active_eq_visitedProduct
    {Label : Type u} {Domain : Type v} {Cube : Type w}
    [DecidableEq Cube]
    (domainActive : Domain → Finset Cube)
    (walk : CMP99GeneralizedWalk Label Domain)
    (sigma : Cube → ℂ) :
    cmp116ComplexWeakeningMonomial (walk.active domainActive) sigma =
      cmp116ComplexVisitedWeakeningProduct sigma ∅
        (walk.domains.map domainActive) := by
  rw [cmp116ComplexVisitedWeakeningProduct_empty]
  rfl

/-- Intersecting every step carrier with one finite contour commutes exactly
with taking the union along the path. -/
theorem foldr_union_map_inter
    {Delta : Type u} [DecidableEq Delta]
    (carrier : Finset Delta) :
    ∀ carriers : List (Finset Delta),
      ((carriers.map fun active => active ∩ carrier).foldr (· ∪ ·) ∅) =
        carriers.foldr (· ∪ ·) ∅ ∩ carrier := by
  intro carriers
  induction carriers with
  | nil => simp
  | cons active rest ih =>
      simp only [List.map_cons, List.foldr_cons]
      rw [ih]
      ext d
      simp only [Finset.mem_union, Finset.mem_inter]
      tauto

/-- On a restricted shifted contour, the exact walk monomial is an ordered
visited-state product whose every state is built only from intersections with
the finite contour carrier.  Thus the memory alphabet is the finite powerset
of that carrier, rather than the ambient periodic volume. -/
theorem CMP99GeneralizedWalk.restrictedShiftedWeakeningMonomial_eq_visitedProduct
    {n : ℕ} {Label : Type u} {Domain : Type v} {Cube : Type w}
    [DecidableEq Cube]
    (domainActive : Domain → Finset Cube)
    (walk : CMP99GeneralizedWalk Label Domain)
    (carrier : Finset Cube) (e : Fin n ≃ ↥carrier)
    (z : Fin n → ℂ) :
    cmp116ComplexWeakeningMonomial (walk.active domainActive)
        (cmp116SourceRestrictedShiftedCoupling carrier e z) =
      cmp116ComplexVisitedWeakeningProduct
        (cmp116SourceRestrictedShiftedCoupling carrier e z) ∅
        (walk.domains.map fun X => domainActive X ∩ carrier) := by
  rw [cmp116ComplexWeakeningMonomial_restrictedShiftedCoupling]
  rw [cmp116ComplexVisitedWeakeningProduct_empty]
  congr 1
  change
    (walk.domains.map domainActive).foldr (· ∪ ·) ∅ ∩ carrier =
      (walk.domains.map fun X => domainActive X ∩ carrier).foldr
        (· ∪ ·) ∅
  rw [← foldr_union_map_inter carrier (walk.domains.map domainActive)]
  apply congrArg
    (fun carriers : List (Finset Cube) =>
      carriers.foldr (· ∪ ·) ∅)
  rw [List.map_map]
  exact List.map_congr_left (fun X _ => rfl)

end YangMills.RG
