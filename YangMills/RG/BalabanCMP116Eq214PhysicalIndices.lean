/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq23PhysicalBondIndex

/-!
# CMP116 equation (2.14): physical `D/P/Z₀` source indices

This module turns the geometry established for equations (2.2)--(2.3) into the
first three dependent finite indices of the term displayed in (2.14).

* `D` is a subfamily of the supplied localization-domain family whose union
  lies in the target polymer `Z`;
* `P` is the literal physical powerset of `Y₀^{c,*}`;
* `Z₀` is an allowed localization domain contained in `Z`, satisfying the
  seed/interior constraints, and least by inclusion among all allowed domains
  satisfying those constraints.

The least-domain definition reflects the wording on CMP116 printed page 12.
It is intentionally relative to an explicit finite family of allowed domains:
the paper's connected-domain convention is not silently replaced by all block
carriers.  The exact core theorem from the previous module identifies this
index with a singleton whenever the core itself is an allowed domain.
-/

namespace YangMills.RG

open Finset

/-- Source `D` families drawn from the allowed localization domains and whose
union `Y₀` is contained in the target polymer `Z`. -/
noncomputable def cmp116Eq214DIndex {d N' : ℕ}
    (domainFamily : Finset (Finset (FinBox d N')))
    (Z : Finset (FinBox d N')) :
    Finset (Finset (Finset (FinBox d N'))) :=
  by
    classical
    exact domainFamily.powerset.filter fun D => cmp116Eq23Y0 D ⊆ Z

@[simp] theorem mem_cmp116Eq214DIndex_iff {d N' : ℕ}
    {domainFamily : Finset (Finset (FinBox d N'))}
    {Z : Finset (FinBox d N')}
    {D : Finset (Finset (FinBox d N'))} :
    D ∈ cmp116Eq214DIndex domainFamily Z ↔
      D ⊆ domainFamily ∧ cmp116Eq23Y0 D ⊆ Z := by
  classical
  simp [cmp116Eq214DIndex]

/-- The physical `P` family at fixed `D`. -/
noncomputable def cmp116Eq214PIndex {d M N' : ℕ}
    [NeZero M] [NeZero N']
    (ambient distinguished : Finset (PhysicalBond d (M * N')))
    (D : Finset (Finset (FinBox d N'))) :
    Finset (Finset (PhysicalBond d (M * N'))) :=
  cmp116Eq23PhysicalBondPIndex ambient distinguished D

@[simp] theorem mem_cmp116Eq214PIndex_iff {d M N' : ℕ}
    [NeZero M] [NeZero N']
    {ambient distinguished : Finset (PhysicalBond d (M * N'))}
    {D : Finset (Finset (FinBox d N'))}
    {P : Finset (PhysicalBond d (M * N'))} :
    P ∈ cmp116Eq214PIndex ambient distinguished D ↔
      P ⊆ cmp116Eq23PhysicalBondOutsideCarrier ambient distinguished D := by
  classical
  simp [cmp116Eq214PIndex]

/-- `Z₀` is an allowed, admissible domain contained in `Z` and least among all
allowed admissible domains. -/
def CMP116LeastAllowedLocalizationDomain {d M N' : ℕ}
    [NeZero M] [NeZero N']
    (allowed : Finset (Finset (FinBox d N')))
    (Z : Finset (FinBox d N'))
    (D : Finset (Finset (FinBox d N')))
    (P : Finset (PhysicalBond d (M * N')))
    (Z0 : Finset (FinBox d N')) : Prop :=
  Z0 ∈ allowed ∧ Z0 ⊆ Z ∧
    CMP116LocalizationAdmissible D P Z0 ∧
    ∀ W ∈ allowed, CMP116LocalizationAdmissible D P W → Z0 ⊆ W

/-- Finite source index of least allowed localization domains. -/
noncomputable def cmp116Eq214Z0Index {d M N' : ℕ}
    [NeZero M] [NeZero N']
    (allowed : Finset (Finset (FinBox d N')))
    (Z : Finset (FinBox d N'))
    (D : Finset (Finset (FinBox d N')))
    (P : Finset (PhysicalBond d (M * N'))) :
    Finset (Finset (FinBox d N')) :=
  by
    classical
    exact allowed.filter fun Z0 =>
      Z0 ⊆ Z ∧ CMP116LocalizationAdmissible D P Z0 ∧
        ∀ W ∈ allowed, CMP116LocalizationAdmissible D P W → Z0 ⊆ W

@[simp] theorem mem_cmp116Eq214Z0Index_iff {d M N' : ℕ}
    [NeZero M] [NeZero N']
    {allowed : Finset (Finset (FinBox d N'))}
    {Z : Finset (FinBox d N')}
    {D : Finset (Finset (FinBox d N'))}
    {P : Finset (PhysicalBond d (M * N'))}
    {Z0 : Finset (FinBox d N')} :
    Z0 ∈ cmp116Eq214Z0Index allowed Z D P ↔
      CMP116LeastAllowedLocalizationDomain allowed Z D P Z0 := by
  classical
  simp [cmp116Eq214Z0Index, CMP116LeastAllowedLocalizationDomain]

/-- Any two source-selected least domains coincide. -/
theorem cmp116Eq214Z0Index_pair_eq {d M N' : ℕ}
    [NeZero M] [NeZero N']
    {allowed : Finset (Finset (FinBox d N'))}
    {Z : Finset (FinBox d N')}
    {D : Finset (Finset (FinBox d N'))}
    {P : Finset (PhysicalBond d (M * N'))}
    {Z0 W0 : Finset (FinBox d N')}
    (hZ0 : Z0 ∈ cmp116Eq214Z0Index allowed Z D P)
    (hW0 : W0 ∈ cmp116Eq214Z0Index allowed Z D P) :
    Z0 = W0 := by
  rw [mem_cmp116Eq214Z0Index_iff] at hZ0 hW0
  apply Finset.Subset.antisymm
  · exact hZ0.2.2.2 W0 hW0.1 hW0.2.2.1
  · exact hW0.2.2.2 Z0 hZ0.1 hZ0.2.2.1

/-- The physical `Z₀` source family has at most one element. -/
theorem cmp116Eq214Z0Index_card_le_one {d M N' : ℕ}
    [NeZero M] [NeZero N']
    (allowed : Finset (Finset (FinBox d N')))
    (Z : Finset (FinBox d N'))
    (D : Finset (Finset (FinBox d N')))
    (P : Finset (PhysicalBond d (M * N'))) :
    (cmp116Eq214Z0Index allowed Z D P).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro Z0 hZ0 W0 hW0
  exact cmp116Eq214Z0Index_pair_eq hZ0 hW0

/-- A selected source `Z₀` contains the exact physical localization core. -/
theorem cmp116LocalizationCore_subset_of_mem_Eq214Z0Index {d M N' : ℕ}
    [NeZero M] [NeZero N']
    {allowed : Finset (Finset (FinBox d N'))}
    {Z : Finset (FinBox d N')}
    {D : Finset (Finset (FinBox d N'))}
    {P : Finset (PhysicalBond d (M * N'))}
    {Z0 : Finset (FinBox d N')}
    (hZ0 : Z0 ∈ cmp116Eq214Z0Index allowed Z D P) :
    cmp116LocalizationCore D P ⊆ Z0 := by
  rw [mem_cmp116Eq214Z0Index_iff] at hZ0
  exact cmp116LocalizationCore_minimal hZ0.2.2.1

/-- If the exact core is itself an allowed domain contained in `Z`, it is a
member of the source `Z₀` index. -/
theorem cmp116LocalizationCore_mem_Eq214Z0Index {d M N' : ℕ}
    [NeZero M] [NeZero N']
    {allowed : Finset (Finset (FinBox d N'))}
    {Z : Finset (FinBox d N')}
    (D : Finset (Finset (FinBox d N')))
    (P : Finset (PhysicalBond d (M * N')))
    (hallowed : cmp116LocalizationCore D P ∈ allowed)
    (hZ : cmp116LocalizationCore D P ⊆ Z) :
    cmp116LocalizationCore D P ∈ cmp116Eq214Z0Index allowed Z D P := by
  rw [mem_cmp116Eq214Z0Index_iff]
  refine ⟨hallowed, hZ, cmp116LocalizationCore_admissible D P, ?_⟩
  intro W hWallowed hW
  exact cmp116LocalizationCore_minimal hW

/-- Under the source-compatible allowed-domain hypothesis, the physical `Z₀`
index is literally the singleton containing the constructed core. -/
theorem cmp116Eq214Z0Index_eq_singleton_core {d M N' : ℕ}
    [NeZero M] [NeZero N']
    {allowed : Finset (Finset (FinBox d N'))}
    {Z : Finset (FinBox d N')}
    (D : Finset (Finset (FinBox d N')))
    (P : Finset (PhysicalBond d (M * N')))
    (hallowed : cmp116LocalizationCore D P ∈ allowed)
    (hZ : cmp116LocalizationCore D P ⊆ Z) :
    cmp116Eq214Z0Index allowed Z D P = {cmp116LocalizationCore D P} := by
  classical
  ext Z0
  constructor
  · intro hZ0
    rw [Finset.mem_singleton]
    exact cmp116Eq214Z0Index_pair_eq hZ0
      (cmp116LocalizationCore_mem_Eq214Z0Index D P hallowed hZ)
  · intro hZ0
    rw [Finset.mem_singleton] at hZ0
    subst Z0
    exact cmp116LocalizationCore_mem_Eq214Z0Index D P hallowed hZ

end YangMills.RG
