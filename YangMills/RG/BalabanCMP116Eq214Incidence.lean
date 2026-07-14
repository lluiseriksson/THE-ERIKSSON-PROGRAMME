/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq23Cutoff
import YangMills.RG.PhysicalGaugeCochains

/-!
# CMP116 equation (2.14): physical bond incidence and localization seed

This module connects the abstract `(D,P)` geometry to the actual positively
oriented physical bonds of the periodic lattice.  Incidence always uses both
endpoints:

`incident(e,Q) ↔ source(e) ∈ Q ∨ target(e) ∈ Q`.

At block scale `M`, both endpoints are projected through `blockSite`; the
resulting one- or two-element finset is the exact family of `M`-cube labels
hit by the bond.  Taking the union over `P` and adjoining `Y₀ = ⋃ D` produces
the finite localization **seed**.

Honest scope: the seed is not called `Z₀`.  CMP116 additionally requires the
large-field bonds to lie in the interior and avoid the boundary of `Z₀`; the
source localization hull/thickening which enforces those conditions remains a
separate operation.
-/

namespace YangMills.RG

open Finset

/-- Source endpoint of a positively oriented physical bond. -/
def cmp116BondSource {d N : ℕ} [NeZero N]
    (e : PhysicalBond d N) : FinBox d N :=
  e.1

/-- Target endpoint of a positively oriented physical bond. -/
def cmp116BondTarget {d N : ℕ} [NeZero N]
    (e : PhysicalBond d N) : FinBox d N :=
  FinBox.shift e.1 e.2

/-- Site-level incidence, retaining both bond endpoints. -/
def cmp116BondIncidentSite {d N : ℕ} [NeZero N]
    (e : PhysicalBond d N) (Q : Finset (FinBox d N)) : Prop :=
  cmp116BondSource e ∈ Q ∨ cmp116BondTarget e ∈ Q

theorem cmp116BondIncidentSite_iff {d N : ℕ} [NeZero N]
    (e : PhysicalBond d N) (Q : Finset (FinBox d N)) :
    cmp116BondIncidentSite e Q ↔
      cmp116BondSource e ∈ Q ∨ cmp116BondTarget e ∈ Q := by
  rfl

/-- `M`-block containing the source endpoint. -/
def cmp116BondSourceBlock {d M N' : ℕ} [NeZero M] [NeZero N']
    (e : PhysicalBond d (M * N')) : FinBox d N' :=
  blockSite M N' (cmp116BondSource e)

/-- `M`-block containing the target endpoint. -/
def cmp116BondTargetBlock {d M N' : ℕ} [NeZero M] [NeZero N']
    (e : PhysicalBond d (M * N')) : FinBox d N' :=
  blockSite M N' (cmp116BondTarget e)

/-- Block-level incidence, again retaining both physical endpoints. -/
def cmp116BondIncidentBlock {d M N' : ℕ} [NeZero M] [NeZero N']
    (e : PhysicalBond d (M * N')) (Q : Finset (FinBox d N')) : Prop :=
  cmp116BondSourceBlock e ∈ Q ∨ cmp116BondTargetBlock e ∈ Q

/-- The exact one- or two-block carrier of a physical bond. -/
def cmp116BondBlocks {d M N' : ℕ} [NeZero M] [NeZero N']
    (e : PhysicalBond d (M * N')) : Finset (FinBox d N') :=
  {cmp116BondSourceBlock e, cmp116BondTargetBlock e}

@[simp] theorem mem_cmp116BondBlocks_iff {d M N' : ℕ}
    [NeZero M] [NeZero N']
    {e : PhysicalBond d (M * N')} {x : FinBox d N'} :
    x ∈ cmp116BondBlocks e ↔
      x = cmp116BondSourceBlock e ∨ x = cmp116BondTargetBlock e := by
  simp [cmp116BondBlocks]

theorem cmp116BondBlocks_card_le_two {d M N' : ℕ}
    [NeZero M] [NeZero N'] (e : PhysicalBond d (M * N')) :
    (cmp116BondBlocks e).card ≤ 2 := by
  unfold cmp116BondBlocks
  calc
    ({cmp116BondSourceBlock e, cmp116BondTargetBlock e} :
        Finset (FinBox d N')).card ≤
        ({cmp116BondTargetBlock e} : Finset (FinBox d N')).card + 1 :=
      Finset.card_insert_le _ _
    _ = 2 := by simp

theorem cmp116BondIncidentBlock_iff_inter_nonempty {d M N' : ℕ}
    [NeZero M] [NeZero N']
    (e : PhysicalBond d (M * N')) (Q : Finset (FinBox d N')) :
    cmp116BondIncidentBlock e Q ↔
      ∃ x ∈ cmp116BondBlocks e, x ∈ Q := by
  simp [cmp116BondIncidentBlock, cmp116BondBlocks]

/-- Block carrier incident to at least one physical bond of `P`. -/
noncomputable def cmp116PBondBlocks {d M N' : ℕ}
    [NeZero M] [NeZero N']
    (P : Finset (PhysicalBond d (M * N'))) : Finset (FinBox d N') :=
  P.biUnion cmp116BondBlocks

@[simp] theorem mem_cmp116PBondBlocks_iff {d M N' : ℕ}
    [NeZero M] [NeZero N']
    {P : Finset (PhysicalBond d (M * N'))} {x : FinBox d N'} :
    x ∈ cmp116PBondBlocks P ↔
      ∃ e ∈ P, x ∈ cmp116BondBlocks e := by
  classical
  simp [cmp116PBondBlocks]

theorem cmp116PBondBlocks_mono {d M N' : ℕ}
    [NeZero M] [NeZero N']
    {P P' : Finset (PhysicalBond d (M * N'))} (hPP' : P ⊆ P') :
    cmp116PBondBlocks P ⊆ cmp116PBondBlocks P' := by
  classical
  intro x hx
  rcases (mem_cmp116PBondBlocks_iff).1 hx with ⟨e, heP, hxe⟩
  exact (mem_cmp116PBondBlocks_iff).2 ⟨e, hPP' heP, hxe⟩

/-- Finite carrier forced by `D` and `P`, before applying the localization
hull which creates the final interior/boundary geometry of `Z₀`. -/
noncomputable def cmp116LocalizationSeed {d M N' : ℕ}
    [NeZero M] [NeZero N']
    (D : Finset (Finset (FinBox d N')))
    (P : Finset (PhysicalBond d (M * N'))) : Finset (FinBox d N') :=
  cmp116Eq23Y0 D ∪ cmp116PBondBlocks P

theorem cmp116Eq23Y0_subset_localizationSeed {d M N' : ℕ}
    [NeZero M] [NeZero N']
    (D : Finset (Finset (FinBox d N')))
    (P : Finset (PhysicalBond d (M * N'))) :
    cmp116Eq23Y0 D ⊆ cmp116LocalizationSeed D P := by
  classical
  exact Finset.subset_union_left

theorem cmp116BondBlocks_subset_localizationSeed {d M N' : ℕ}
    [NeZero M] [NeZero N']
    (D : Finset (Finset (FinBox d N')))
    {P : Finset (PhysicalBond d (M * N'))} {e : PhysicalBond d (M * N')}
    (heP : e ∈ P) :
    cmp116BondBlocks e ⊆ cmp116LocalizationSeed D P := by
  classical
  intro x hxe
  apply Finset.mem_union_right
  exact (mem_cmp116PBondBlocks_iff).2 ⟨e, heP, hxe⟩

theorem cmp116LocalizationSeed_mono {d M N' : ℕ}
    [NeZero M] [NeZero N']
    {D D' : Finset (Finset (FinBox d N'))}
    {P P' : Finset (PhysicalBond d (M * N'))}
    (hDD' : D ⊆ D') (hPP' : P ⊆ P') :
    cmp116LocalizationSeed D P ⊆ cmp116LocalizationSeed D' P' := by
  classical
  intro x hx
  rw [cmp116LocalizationSeed, Finset.mem_union] at hx ⊢
  rcases hx with hx | hx
  · left
    rcases (mem_cmp116Eq23Y0_iff).1 hx with ⟨Y, hYD, hxY⟩
    exact (mem_cmp116Eq23Y0_iff).2 ⟨Y, hDD' hYD, hxY⟩
  · right
    exact cmp116PBondBlocks_mono hPP' hx

end YangMills.RG
