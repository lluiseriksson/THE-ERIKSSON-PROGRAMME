/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.AppendixFFiniteCover
import YangMills.RG.ClusterDecay

/-!
# Appendix F: full targets for Ω-active hole covers

This module starts the source-faithful two-support Appendix-F bridge for the
with-holes polymer carrier.

The already verified finite compiler can use an abstract `overlapSupport` for
Ω-connectivity and a separate `targetSupport` for the fiber activity `K(Y)`.
For `omegaHolePolymerSystem`, the source split is:

* Ω-connectivity and admissibility are controlled by active skeletons
  `skeleton HF X.val`;
* the target label `Y` is the full union of the selected hole-polymers
  `X.val`.

The theorems here prove the exact finite geometry needed before the full
two-support target-family Fubini identity: active skeleton unions are recovered
from full target unions, and within an admissible family the full-union target
map is injective.  This avoids silently replacing skeleton disjointness by
full-target disjointness.

Honest scope: this is finite combinatorics only.  It does not prove Dimock's
metric estimate (642), ultralocal integration (643)--(644), the second Ursell
expansion (645)--(646), any `hRpoly` activity decay, or a continuum/Clay mass
gap statement.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

attribute [local instance] Classical.propDecidable

namespace YangMills.RG

open Finset

/-- The active skeleton of a full Appendix-F cover union is exactly the cover
union of the active skeletons.  This is the concrete two-support compatibility:
full targets determine their active part. -/
theorem appendixFHoleCoverUnion_skeleton
    {d L : ℕ} [NeZero L] (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (C : Finset (OmegaPolymerType HF z)) :
    skeleton HF (appendixFCoverUnion (fun X : OmegaPolymerType HF z => X.val) C) =
      appendixFCoverUnion (fun X : OmegaPolymerType HF z => skeleton HF X.val) C := by
  classical
  simpa [appendixFCoverUnion] using
    (skeleton_biUnion HF C (fun X : OmegaPolymerType HF z => X.val))

/-- A connected Appendix-F cover of active hole-polymers has nonempty active
skeleton union.  The proof uses only the nonempty skeleton carried by each
`OmegaPolymerType`, not any analytic estimate. -/
theorem appendixFHoleActiveCoverUnion_nonempty
    {d L : ℕ} [NeZero L] (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    {C : Finset (OmegaPolymerType HF z)}
    (hC : C ∈ appendixFConnectedCoverRegion
      (Finset.univ : Finset (Cube d L))
      (fun X : OmegaPolymerType HF z => skeleton HF X.val) Λ) :
    (appendixFCoverUnion (fun X : OmegaPolymerType HF z => skeleton HF X.val) C).Nonempty := by
  classical
  have hactive :
      ∀ X : OmegaPolymerType HF z, X ∈ Λ →
        ((Finset.univ : Finset (Cube d L)) ∩ skeleton HF X.val).Nonempty := by
    intro X _hX
    simpa using X.property.right.right.right
  have h :=
    omega_inter_coverUnion_nonempty_of_mem_appendixFConnectedCoverRegion
      (Finset.univ : Finset (Cube d L))
      (fun X : OmegaPolymerType HF z => skeleton HF X.val)
      Λ hactive hC
  simpa using h

/-- A connected Appendix-F cover of active hole-polymers has nonempty full
target union.  This is a finite sanity check for the future target polymer
carrier: the target label cannot be the empty full set. -/
theorem appendixFHoleFullCoverUnion_nonempty
    {d L : ℕ} [NeZero L] (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    {C : Finset (OmegaPolymerType HF z)}
    (hC : C ∈ appendixFConnectedCoverRegion
      (Finset.univ : Finset (Cube d L))
      (fun X : OmegaPolymerType HF z => skeleton HF X.val) Λ) :
    (appendixFCoverUnion (fun X : OmegaPolymerType HF z => X.val) C).Nonempty := by
  classical
  rcases appendixFHoleActiveCoverUnion_nonempty HF z Λ hC with ⟨x, hx⟩
  rw [appendixFCoverUnion] at hx ⊢
  rcases Finset.mem_biUnion.mp hx with ⟨X, hX, hxskel⟩
  exact ⟨x, Finset.mem_biUnion.mpr
    ⟨X, hX, skeleton_subset HF X.val hxskel⟩⟩

/-- Active-skeleton adjacency of two source hole-polymers implies their full
targets overlap. -/
theorem appendixFHole_skeletonAdj_not_disjoint_full
    {d L : ℕ} [NeZero L] (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    {X Y : OmegaPolymerType HF z}
    (hAdj : (omegaOverlapGraph (Finset.univ : Finset (Cube d L))
      (fun P : OmegaPolymerType HF z => skeleton HF P.val)).Adj X Y) :
    ¬ Disjoint X.val Y.val := by
  classical
  rw [omegaOverlapGraph_adj_iff] at hAdj
  intro hdisjFull
  apply hAdj.2
  rw [Finset.disjoint_left]
  intro s hsX hsY
  have hsXskel : s ∈ skeleton HF X.val := (Finset.mem_inter.mp hsX).2
  have hsYskel : s ∈ skeleton HF Y.val := (Finset.mem_inter.mp hsY).2
  have hsXfull : s ∈ X.val := skeleton_subset HF X.val hsXskel
  have hsYfull : s ∈ Y.val := skeleton_subset HF Y.val hsYskel
  exact (Finset.disjoint_left.mp hdisjFull hsXfull) hsYfull

/-- A connected Appendix-F active hole-cover has connected full target union.
Connectivity is still sourced from skeleton overlap; the conclusion is only
about the full finite union selected by that connected cover. -/
theorem appendixFHoleCoverUnion_cubeConnected
    {d L : ℕ} [NeZero L] (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    {C : Finset (OmegaPolymerType HF z)}
    (hC : C ∈ appendixFConnectedCoverRegion
      (Finset.univ : Finset (Cube d L))
      (fun X : OmegaPolymerType HF z => skeleton HF X.val) Λ) :
    cubeConnected (appendixFCoverUnion (fun X : OmegaPolymerType HF z => X.val) C) := by
  classical
  rw [cubeConnected]
  intro x hx y hy
  rw [appendixFCoverUnion, Finset.mem_biUnion] at hx hy
  rcases hx with ⟨X, hX, hxX⟩
  rcases hy with ⟨Y, hY, hyY⟩
  have hCdata :=
    (mem_appendixFConnectedCoverRegion_iff
      (Finset.univ : Finset (Cube d L))
      (fun X : OmegaPolymerType HF z => skeleton HF X.val) Λ C).mp hC
  obtain ⟨w, hwC⟩ := hCdata.2.2 X hX Y hY
  obtain ⟨wCube, hwCube⟩ :=
    walk_union_connected
      (omegaOverlapGraph (Finset.univ : Finset (Cube d L))
        (fun P : OmegaPolymerType HF z => skeleton HF P.val))
      (cubeAdj d L)
      (fun P : OmegaPolymerType HF z => P.val)
      (fun P => P.property.right.left)
      (fun P Q hAdj => appendixFHole_skeletonAdj_not_disjoint_full HF z hAdj)
      w x hxX y hyY
  refine ⟨wCube, ?_⟩
  intro v hv
  rcases hwCube v hv with ⟨P, hPw, hvP⟩
  exact Finset.mem_biUnion.mpr ⟨P, hwC P hPw, hvP⟩

/-- A full target union of source hole-polymers still respects the hole
family.  This is independent of connectedness. -/
theorem appendixFHoleCoverUnion_polymerWithHoles
    {d L : ℕ} [NeZero L] (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (C : Finset (OmegaPolymerType HF z)) :
    polymerWithHoles HF
      (appendixFCoverUnion (fun X : OmegaPolymerType HF z => X.val) C) := by
  classical
  dsimp [appendixFCoverUnion]
  exact polymerWithHoles_biUnion HF C (fun X : OmegaPolymerType HF z => X.val)
    (fun X _hX => X.property.right.right.left)

/-- Every full target representable by a connected active hole-cover is
nonempty. -/
theorem appendixFHoleTargetRegion_nonempty
    {d L : ℕ} [NeZero L] (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    {Y : Finset (Cube d L)}
    (hY : Y ∈ appendixFTargetRegion
      (Finset.univ : Finset (Cube d L))
      (fun X : OmegaPolymerType HF z => skeleton HF X.val)
      (fun X : OmegaPolymerType HF z => X.val) Λ) :
    Y.Nonempty := by
  classical
  rw [appendixFTargetRegion] at hY
  rcases Finset.mem_image.mp hY with ⟨C, hC, rfl⟩
  exact appendixFHoleFullCoverUnion_nonempty HF z Λ hC

/-- Every full target representable by a connected active hole-cover is
connected as a cube polymer. -/
theorem appendixFHoleTargetRegion_cubeConnected
    {d L : ℕ} [NeZero L] (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    {Y : Finset (Cube d L)}
    (hY : Y ∈ appendixFTargetRegion
      (Finset.univ : Finset (Cube d L))
      (fun X : OmegaPolymerType HF z => skeleton HF X.val)
      (fun X : OmegaPolymerType HF z => X.val) Λ) :
    cubeConnected Y := by
  classical
  rw [appendixFTargetRegion] at hY
  rcases Finset.mem_image.mp hY with ⟨C, hC, rfl⟩
  exact appendixFHoleCoverUnion_cubeConnected HF z Λ hC

/-- Every full target representable by a connected active hole-cover respects
the source hole family. -/
theorem appendixFHoleTargetRegion_polymerWithHoles
    {d L : ℕ} [NeZero L] (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    {Y : Finset (Cube d L)}
    (hY : Y ∈ appendixFTargetRegion
      (Finset.univ : Finset (Cube d L))
      (fun X : OmegaPolymerType HF z => skeleton HF X.val)
      (fun X : OmegaPolymerType HF z => X.val) Λ) :
    polymerWithHoles HF Y := by
  classical
  rw [appendixFTargetRegion] at hY
  rcases Finset.mem_image.mp hY with ⟨C, _hC, rfl⟩
  exact appendixFHoleCoverUnion_polymerWithHoles HF z C

/-- Every full target representable by a connected active hole-cover has
nonempty active skeleton.  This is the future hard-core self-incompatibility
input for the source-faithful target gas. -/
theorem appendixFHoleTargetRegion_skeleton_nonempty
    {d L : ℕ} [NeZero L] (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    {Y : Finset (Cube d L)}
    (hY : Y ∈ appendixFTargetRegion
      (Finset.univ : Finset (Cube d L))
      (fun X : OmegaPolymerType HF z => skeleton HF X.val)
      (fun X : OmegaPolymerType HF z => X.val) Λ) :
    (skeleton HF Y).Nonempty := by
  classical
  rw [appendixFTargetRegion] at hY
  rcases Finset.mem_image.mp hY with ⟨C, hC, rfl⟩
  rw [appendixFHoleCoverUnion_skeleton]
  exact appendixFHoleActiveCoverUnion_nonempty HF z Λ hC

/-- A representable full target can be reinserted as an active hole-polymer.
This packages the finite target geometry needed before the source-faithful
two-support target gas is built. -/
def appendixFHoleTargetRegion_toOmegaPolymer
    {d L : ℕ} [NeZero L] (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    {Y : Finset (Cube d L)}
    (hY : Y ∈ appendixFTargetRegion
      (Finset.univ : Finset (Cube d L))
      (fun X : OmegaPolymerType HF z => skeleton HF X.val)
      (fun X : OmegaPolymerType HF z => X.val) Λ) :
    OmegaPolymerType HF z :=
  ⟨Y, appendixFHoleTargetRegion_nonempty HF z Λ hY,
    appendixFHoleTargetRegion_cubeConnected HF z Λ hY,
    appendixFHoleTargetRegion_polymerWithHoles HF z Λ hY,
    appendixFHoleTargetRegion_skeleton_nonempty HF z Λ hY⟩

/-- In an admissible Appendix-F family for the active with-holes relation, two
distinct connected covers cannot have the same full target union.

Admissibility is still the source relation: the active skeleton unions are
pairwise disjoint.  The proof first transfers equality of full targets to
equality of active skeleton targets using `appendixFHoleCoverUnion_skeleton`,
then applies the existing single-support injectivity theorem to skeletons. -/
theorem appendixFHoleCoverUnion_injective_on_admissibleConnectedCoverFamily
    {d L : ℕ} [NeZero L] (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    {Γ : Finset (Finset (OmegaPolymerType HF z))}
    (hΓ : Γ ∈ appendixFAdmissibleConnectedCoverFamilies
      (Finset.univ : Finset (Cube d L))
      (fun X : OmegaPolymerType HF z => skeleton HF X.val) Λ)
    {C D : Finset (OmegaPolymerType HF z)}
    (hC : C ∈ Γ) (hD : D ∈ Γ)
    (hCD :
      appendixFCoverUnion (fun X : OmegaPolymerType HF z => X.val) C =
        appendixFCoverUnion (fun X : OmegaPolymerType HF z => X.val) D) :
    C = D := by
  classical
  have hactive :
      ∀ X : OmegaPolymerType HF z, X ∈ Λ →
        ((Finset.univ : Finset (Cube d L)) ∩ skeleton HF X.val).Nonempty := by
    intro X _hX
    simpa using X.property.right.right.right
  have hSkeletonTarget :
      appendixFCoverUnion (fun X : OmegaPolymerType HF z => skeleton HF X.val) C =
        appendixFCoverUnion (fun X : OmegaPolymerType HF z => skeleton HF X.val) D := by
    calc
      appendixFCoverUnion (fun X : OmegaPolymerType HF z => skeleton HF X.val) C
          = skeleton HF
              (appendixFCoverUnion (fun X : OmegaPolymerType HF z => X.val) C) := by
            exact (appendixFHoleCoverUnion_skeleton HF z C).symm
      _ = skeleton HF
              (appendixFCoverUnion (fun X : OmegaPolymerType HF z => X.val) D) := by
            rw [hCD]
      _ = appendixFCoverUnion
              (fun X : OmegaPolymerType HF z => skeleton HF X.val) D := by
            exact appendixFHoleCoverUnion_skeleton HF z D
  exact appendixFCoverUnion_injective_on_admissibleConnectedCoverFamily
    (Finset.univ : Finset (Cube d L))
    (fun X : OmegaPolymerType HF z => skeleton HF X.val)
    Λ hactive hΓ hC hD hSkeletonTarget

/-- Set-level form of full-target injectivity on an admissible active
with-holes connected-cover family. -/
theorem appendixFHoleCoverUnion_setInjOn_admissibleConnectedCoverFamily
    {d L : ℕ} [NeZero L] (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    {Γ : Finset (Finset (OmegaPolymerType HF z))}
    (hΓ : Γ ∈ appendixFAdmissibleConnectedCoverFamilies
      (Finset.univ : Finset (Cube d L))
      (fun X : OmegaPolymerType HF z => skeleton HF X.val) Λ) :
    Set.InjOn
      (appendixFCoverUnion (fun X : OmegaPolymerType HF z => X.val))
      (↑Γ : Set (Finset (OmegaPolymerType HF z))) := by
  classical
  intro C hC D hD hCD
  exact appendixFHoleCoverUnion_injective_on_admissibleConnectedCoverFamily
    HF z Λ hΓ hC hD hCD

/-- Full-target imaging preserves the number of connected components in an
admissible active with-holes connected-cover family.  This is a finite
bookkeeping fact for the upcoming two-support target-choice reindexing. -/
theorem appendixFHoleCoverUnion_image_card_eq
    {d L : ℕ} [NeZero L] (HF : HoleFamily d L)
    (z : Finset (Cube d L) → ℂ)
    (Λ : Finset (OmegaPolymerType HF z))
    {Γ : Finset (Finset (OmegaPolymerType HF z))}
    (hΓ : Γ ∈ appendixFAdmissibleConnectedCoverFamilies
      (Finset.univ : Finset (Cube d L))
      (fun X : OmegaPolymerType HF z => skeleton HF X.val) Λ) :
    (Γ.image (appendixFCoverUnion
        (fun X : OmegaPolymerType HF z => X.val))).card = Γ.card := by
  classical
  exact Finset.card_image_of_injOn
    (appendixFHoleCoverUnion_setInjOn_admissibleConnectedCoverFamily
      HF z Λ hΓ)

end YangMills.RG
