/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116RestrictedVisitedTransfer

/-!
# Active-target factorization of the restricted transfer defect

The contour changes a transfer entry only if its target domain activates at
least one contour coordinate.  This gives a common finite column support for
the entire transfer defect.  Restricting to that subtype and including back
factors the whole matrix exactly, so no sum of per-walk factorizations and no
cross terms occur.
-/

namespace YangMills.RG

noncomputable section

universe u v w

/-- Restrict a matrix to the columns satisfying a decidable predicate. -/
def Matrix.predicateColumnRestriction
    {Row : Type u} {Col : Type v} {R : Type w}
    (p : Col → Prop) [DecidablePred p]
    (D : Matrix Row Col R) :
    Matrix Row {col : Col // p col} R :=
  fun row col => D row col.1

/-- Canonical inclusion from predicate-restricted columns. -/
def Matrix.predicateColumnInclusion
    {Col : Type u} {R : Type v}
    [Zero R] [One R] [DecidableEq Col]
    (p : Col → Prop) [DecidablePred p] :
    Matrix {col : Col // p col} Col R :=
  fun restricted col => if restricted.1 = col then 1 else 0

/-- Any matrix with column support in `p` factors exactly through the subtype
of columns satisfying `p`. -/
theorem Matrix.eq_predicateColumnRestriction_mul_inclusion
    {Row : Type u} {Col : Type v} {R : Type w}
    [Fintype Col] [DecidableEq Col] [Semiring R]
    (p : Col → Prop) [DecidablePred p]
    (D : Matrix Row Col R)
    (hzero : ∀ row col, ¬ p col → D row col = 0) :
    D =
      Matrix.predicateColumnRestriction p D *
        Matrix.predicateColumnInclusion p := by
  ext row col
  change D row col =
    ∑ restricted,
      Matrix.predicateColumnRestriction p D row restricted *
        Matrix.predicateColumnInclusion p restricted col
  by_cases hcol : p col
  · rw [Finset.sum_eq_single (⟨col, hcol⟩ : {col : Col // p col})]
    · simp [Matrix.predicateColumnRestriction,
        Matrix.predicateColumnInclusion]
    · intro other _ hne
      have hval : other.1 ≠ col := by
        intro heq
        apply hne
        exact Subtype.ext heq
      simp [Matrix.predicateColumnInclusion, hval]
    · simp
  · rw [hzero row col hcol]
    symm
    apply Finset.sum_eq_zero
    intro other _
    have hval : other.1 ≠ col := by
      intro heq
      exact hcol (heq ▸ other.2)
    simp [Matrix.predicateColumnInclusion, hval]

/-- A transfer target is contour-active when its physical domain activates at
least one coordinate of the restricted carrier. -/
def cmp116RestrictedTransferTargetActive
    {Label : Type u} {Domain : Type v} {Delta : Type w}
    [DecidableEq Delta]
    (carrier : Finset Delta)
    (domainActive : Domain → Finset Delta)
    (target : CMP116RestrictedTransferState Label Domain carrier) : Prop :=
  (domainActive target.1.domain ∩ carrier).Nonempty

instance instDecidableCmp116RestrictedTransferTargetActive
    {Label : Type u} {Domain : Type v} {Delta : Type w}
    [DecidableEq Delta]
    (carrier : Finset Delta)
    (domainActive : Domain → Finset Delta)
    (target : CMP116RestrictedTransferState Label Domain carrier) :
    Decidable
      (cmp116RestrictedTransferTargetActive
        carrier domainActive target) :=
  Finset.decidableNonempty

/-- If the target domain misses the contour carrier, the transfer defect
entry is zero for every source state. -/
theorem cmp116RestrictedVisitedTransferMatrix_sub_one_eq_zero_of_not_targetActive
    {Label : Type u} {Domain : Type v} {Delta : Type w}
    [DecidableEq Label] [DecidableEq Domain] [DecidableEq Delta]
    {Index : Type*} [Fintype Index] [DecidableEq Index]
    (carrier : Finset Delta)
    (domainActive : Domain → Finset Delta)
    (successors : Domain → Finset (CMP99WalkStep Label Domain))
    (R : Label → Domain → Matrix Index Index ℂ)
    (sigma : Delta → ℂ)
    (source target :
      CMP116RestrictedTransferState Label Domain carrier)
    (hinactive :
      ¬ cmp116RestrictedTransferTargetActive
        carrier domainActive target) :
    (cmp116RestrictedVisitedTransferMatrix
        carrier domainActive successors R sigma -
      cmp116RestrictedVisitedTransferMatrix
        carrier domainActive successors R (fun _ => 1))
        source target = 0 := by
  apply
    cmp116RestrictedVisitedTransferMatrix_sub_one_eq_zero_of_newlyActive_eq_empty
  apply Finset.not_nonempty_iff_eq_empty.mp
  intro hnew
  exact hinactive
    (hnew.mono Finset.sdiff_subset)

/-- The complete restricted transfer defect factors through the finite
subtype of contour-active target states. -/
theorem cmp116RestrictedVisitedTransferMatrix_sub_one_eq_activeTargetFactorization
    {Label : Type u} {Domain : Type v} {Delta : Type w}
    [Fintype Label] [DecidableEq Label]
    [Fintype Domain] [DecidableEq Domain] [DecidableEq Delta]
    {Index : Type*} [Fintype Index] [DecidableEq Index]
    (carrier : Finset Delta)
    (domainActive : Domain → Finset Delta)
    (successors : Domain → Finset (CMP99WalkStep Label Domain))
    (R : Label → Domain → Matrix Index Index ℂ)
    (sigma : Delta → ℂ) :
    let D :=
      cmp116RestrictedVisitedTransferMatrix
          carrier domainActive successors R sigma -
        cmp116RestrictedVisitedTransferMatrix
          carrier domainActive successors R (fun _ => 1)
    D =
      Matrix.predicateColumnRestriction
          (cmp116RestrictedTransferTargetActive carrier domainActive) D *
        Matrix.predicateColumnInclusion
          (cmp116RestrictedTransferTargetActive carrier domainActive) := by
  dsimp
  apply Matrix.eq_predicateColumnRestriction_mul_inclusion
  intro source target hinactive
  exact
    cmp116RestrictedVisitedTransferMatrix_sub_one_eq_zero_of_not_targetActive
      carrier domainActive successors R sigma source target hinactive

end

end YangMills.RG
