/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99StraightTransportEnergy

/-!
# Translation between the source and target CMP99 blocks

The middle contour in the literal `Ubar` construction translates every fine
site by exactly one coarse spacing.  Restricted to a source block this is a
bijection onto the target block.  This module records that bijection so that
the target block average can be reindexed without a multiplicity or ambient
volume factor.
-/

namespace YangMills.RG

open YangMills
open scoped BigOperators

noncomputable section

variable {d M N' : ℕ}
variable [NeZero d] [NeZero M] [NeZero N']

/-- Translation by the literal middle contour, restricted from one fine block
to its positive coarse neighbour. -/
def cmp99SourceBlockTranslation
    (y : FinBox d N') (mu : Fin d) :
    {x : FinBox d (M * N') // x ∈ blockOf M N' y} →
      {x : FinBox d (M * N') // x ∈ blockOf M N' (y.shift mu)} :=
  fun x => ⟨cmp99SourceTranslatedSite x.1 mu,
    cmp99SourceTranslatedSite_mem_targetBlock y mu x.1 x.2⟩

/-- The restricted source-to-target translation is injective because it is
an iterate of a periodic coordinate shift. -/
theorem cmp99SourceBlockTranslation_injective
    (y : FinBox d N') (mu : Fin d) :
    Function.Injective (cmp99SourceBlockTranslation (M := M) y mu) := by
  intro x x' h
  apply Subtype.ext
  apply (iterShift_bijective (M * N') mu M).1
  exact congrArg Subtype.val h

/-- The restricted source-to-target translation is bijective.  The two blocks
have the same exact cardinality `M^d`; no choice of inverse coordinates enters
the public interface. -/
theorem cmp99SourceBlockTranslation_bijective
    (y : FinBox d N') (mu : Fin d) :
    Function.Bijective (cmp99SourceBlockTranslation (M := M) y mu) := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  refine ⟨cmp99SourceBlockTranslation_injective (M := M) y mu, ?_⟩
  simp only [Fintype.card_coe, blockOf_card]

/-- Canonical finite equivalence between source and target blocks induced by
the literal straight middle contour. -/
noncomputable def cmp99SourceBlockTranslationEquiv
    (y : FinBox d N') (mu : Fin d) :
    {x : FinBox d (M * N') // x ∈ blockOf M N' y} ≃
      {x : FinBox d (M * N') // x ∈ blockOf M N' (y.shift mu)} :=
  Equiv.ofBijective (cmp99SourceBlockTranslation (M := M) y mu)
    (cmp99SourceBlockTranslation_bijective (M := M) y mu)

@[simp] theorem cmp99SourceBlockTranslationEquiv_apply_val
    (y : FinBox d N') (mu : Fin d)
    (x : {x : FinBox d (M * N') // x ∈ blockOf M N' y}) :
    (cmp99SourceBlockTranslationEquiv (M := M) y mu x).1 =
      cmp99SourceTranslatedSite x.1 mu :=
  rfl

/-- Reindex any target-block sum by the literal source-block translation. -/
theorem sum_cmp99SourceBlockTranslationEquiv
    {E : Type*} [AddCommMonoid E]
    (y : FinBox d N') (mu : Fin d)
    (f : {x : FinBox d (M * N') // x ∈ blockOf M N' (y.shift mu)} → E) :
    (∑ x, f x) =
      ∑ x, f (cmp99SourceBlockTranslationEquiv (M := M) y mu x) := by
  exact ((cmp99SourceBlockTranslationEquiv (M := M) y mu).sum_comp f).symm

end

end YangMills.RG
