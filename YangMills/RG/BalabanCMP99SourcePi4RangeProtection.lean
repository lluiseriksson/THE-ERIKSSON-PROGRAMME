/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourcePi4CollarDomain

/-!
# Physical range protection by the CMP99 `Pi^4` collar

One source cell has fine width `2*M`.  This file proves the exact periodic
quotient estimate used by CMP99: fine circular distance at most `4*M`
forces the corresponding source-cell owners to have circular distance at
most two.  The extra unit in `Rrange + 1 <= 4*M` then controls both endpoints
of a target bond and yields literal bilateral support in the `Pi^4` domain.
-/

namespace YangMills.RG

noncomputable section

/-- The source-cell owner of one fine coordinate, expressed as the two
successive CMP block quotients. -/
def cmp99FineCoordCellOwner {M Q : ℕ} [NeZero M] [NeZero Q]
    (a : Fin (M * (2 * Q))) : Fin Q :=
  ⟨a.val / M / 2, by
    have h₁ : a.val / M < 2 * Q := Nat.div_lt_of_lt_mul a.isLt
    exact Nat.div_lt_of_lt_mul h₁⟩

@[simp] theorem cmp99FineCoordCellOwner_val {M Q : ℕ} [NeZero M] [NeZero Q]
    (a : Fin (M * (2 * Q))) :
    (cmp99FineCoordCellOwner a).val = a.val / M / 2 := rfl

private theorem cmp99FineCoord_decomposition {M Q : ℕ} [NeZero M] [NeZero Q]
    (a : Fin (M * (2 * Q))) :
    ∃ r < 2 * M,
      a.val = (2 * M) * (cmp99FineCoordCellOwner a).val + r := by
  let r := M * ((a.val / M) % 2) + a.val % M
  have hM : 0 < M := NeZero.pos M
  have hmodM : a.val % M < M := Nat.mod_lt _ hM
  have hmod2 : (a.val / M) % 2 < 2 := Nat.mod_lt _ (by omega)
  have h₁ := Nat.div_add_mod a.val M
  have h₂ := Nat.div_add_mod (a.val / M) 2
  refine ⟨r, ?_, ?_⟩
  · dsimp only [r]
    nlinarith
  · dsimp only [r, cmp99FineCoordCellOwner]
    nlinarith

set_option maxHeartbeats 800000 in
/-- Periodic block contraction at the exact source scale: a displacement of
at most two cell widths cannot cross more than two source cells. -/
theorem finTorusDist_cmp99FineCoordCellOwner_le_two
    {M Q : ℕ} [NeZero M] [NeZero Q]
    (a b : Fin (M * (2 * Q)))
    (hab : finTorusDist a b ≤ 4 * M) :
    finTorusDist (cmp99FineCoordCellOwner a)
      (cmp99FineCoordCellOwner b) ≤ 2 := by
  let ca := cmp99FineCoordCellOwner a
  let cb := cmp99FineCoordCellOwner b
  obtain ⟨ra, hra, harep⟩ := cmp99FineCoord_decomposition a
  obtain ⟨rb, hrb, hbrep⟩ := cmp99FineCoord_decomposition b
  by_contra howner
  have howner' : 2 < finTorusDist ca cb := Nat.lt_of_not_ge howner
  unfold finTorusDist zmodCircDist zmodCircVal at hab howner'
  rw [neg_sub] at hab howner'
  have hc₁ : 2 < ((ca.val : ZMod Q) - (cb.val : ZMod Q)).val := by
    omega
  have hc₂ : 2 < ((cb.val : ZMod Q) - (ca.val : ZMod Q)).val := by
    omega
  have hfmin : min
      (((a.val : ZMod (M * (2 * Q))) - (b.val : ZMod (M * (2 * Q)))).val)
      (((b.val : ZMod (M * (2 * Q))) - (a.val : ZMod (M * (2 * Q)))).val)
      ≤ 4 * M := hab
  rcases le_total cb.val ca.val with hba | habv
  · have hcaCast : ((ca.val : ZMod Q)).val = ca.val :=
      ZMod.val_cast_of_lt ca.isLt
    have hcbCast : ((cb.val : ZMod Q)).val = cb.val :=
      ZMod.val_cast_of_lt cb.isLt
    have hcf : ((ca.val : ZMod Q) - (cb.val : ZMod Q)).val =
        ca.val - cb.val := by
      have hba' : ((cb.val : ZMod Q)).val ≤ ((ca.val : ZMod Q)).val := by
        rwa [hcaCast, hcbCast]
      simpa [hcaCast, hcbCast] using (ZMod.val_sub hba')
    rw [hcf] at hc₁
    have hcadiff : ca.val - cb.val ≠ 0 := by omega
    have hzneq : (ca.val : ZMod Q) - (cb.val : ZMod Q) ≠ 0 := by
      intro hz
      rw [hz, ZMod.val_zero] at hcf
      exact hcadiff hcf.symm
    letI : NeZero ((ca.val : ZMod Q) - (cb.val : ZMod Q)) := ⟨hzneq⟩
    have hcr : ((cb.val : ZMod Q) - (ca.val : ZMod Q)).val =
        Q - (ca.val - cb.val) := by
      rw [show (cb.val : ZMod Q) - (ca.val : ZMod Q) =
        -((ca.val : ZMod Q) - (cb.val : ZMod Q)) by ring,
        ZMod.val_neg_of_ne_zero, hcf]
    rw [hcr] at hc₂
    have hM : 0 < M := NeZero.pos M
    have hca : ca.val < Q := ca.isLt
    have hcb : cb.val < Q := cb.isLt
    change a.val = 2 * M * ca.val + ra at harep
    change b.val = 2 * M * cb.val + rb at hbrep
    have hgap : cb.val + 3 ≤ ca.val := by omega
    have hfineOrder : b.val < a.val := by
      nlinarith [Nat.zero_le ra, Nat.zero_le rb]
    have hff :
        ((a.val : ZMod (M * (2 * Q))) -
          (b.val : ZMod (M * (2 * Q)))).val = a.val - b.val := by
      have haCast : ((a.val : ZMod (M * (2 * Q)))).val = a.val :=
        ZMod.val_cast_of_lt a.isLt
      have hbCast : ((b.val : ZMod (M * (2 * Q)))).val = b.val :=
        ZMod.val_cast_of_lt b.isLt
      have hba' : ((b.val : ZMod (M * (2 * Q)))).val ≤
          ((a.val : ZMod (M * (2 * Q)))).val := by
        rw [haCast, hbCast]
        exact hfineOrder.le
      simpa [haCast, hbCast] using (ZMod.val_sub hba')
    have hfdiff : a.val - b.val ≠ 0 := by omega
    have hfzneq :
        (a.val : ZMod (M * (2 * Q))) -
          (b.val : ZMod (M * (2 * Q))) ≠ 0 := by
      intro hz
      rw [hz, ZMod.val_zero] at hff
      exact hfdiff hff.symm
    letI : NeZero ((a.val : ZMod (M * (2 * Q))) -
        (b.val : ZMod (M * (2 * Q)))) := ⟨hfzneq⟩
    have hfr :
        ((b.val : ZMod (M * (2 * Q))) -
          (a.val : ZMod (M * (2 * Q)))).val =
            M * (2 * Q) - (a.val - b.val) := by
      rw [show (b.val : ZMod (M * (2 * Q))) -
          (a.val : ZMod (M * (2 * Q))) =
        -((a.val : ZMod (M * (2 * Q))) -
          (b.val : ZMod (M * (2 * Q)))) by ring,
        ZMod.val_neg_of_ne_zero, hff]
    rw [hff, hfr] at hfmin
    have hleftAdd : b.val + 4 * M < a.val := by
      nlinarith [Nat.zero_le ra, Nat.zero_le rb]
    have hleft : 4 * M < a.val - b.val := by omega
    have hwrapGap : ca.val + 3 ≤ Q + cb.val := by omega
    have hrightAdd : a.val + 4 * M < M * (2 * Q) + b.val := by
      nlinarith [Nat.zero_le ra, Nat.zero_le rb]
    have hright : 4 * M < M * (2 * Q) - (a.val - b.val) := by
      omega
    omega
  · by_cases heq : ca.val = cb.val
    · have : ca = cb := Fin.ext heq
      rw [this] at howner'
      simp at howner'
    have habc : ca.val < cb.val := lt_of_le_of_ne habv heq
    have hcaCast : ((ca.val : ZMod Q)).val = ca.val :=
      ZMod.val_cast_of_lt ca.isLt
    have hcbCast : ((cb.val : ZMod Q)).val = cb.val :=
      ZMod.val_cast_of_lt cb.isLt
    have hcf : ((cb.val : ZMod Q) - (ca.val : ZMod Q)).val =
        cb.val - ca.val := by
      have habc' : ((ca.val : ZMod Q)).val ≤ ((cb.val : ZMod Q)).val := by
        rwa [hcaCast, hcbCast]
      simpa [hcaCast, hcbCast] using (ZMod.val_sub habc')
    rw [hcf] at hc₂
    have hcadiff : cb.val - ca.val ≠ 0 := by omega
    have hzneq : (cb.val : ZMod Q) - (ca.val : ZMod Q) ≠ 0 := by
      intro hz
      rw [hz, ZMod.val_zero] at hcf
      exact hcadiff hcf.symm
    letI : NeZero ((cb.val : ZMod Q) - (ca.val : ZMod Q)) := ⟨hzneq⟩
    have hcr : ((ca.val : ZMod Q) - (cb.val : ZMod Q)).val =
        Q - (cb.val - ca.val) := by
      rw [show (ca.val : ZMod Q) - (cb.val : ZMod Q) =
        -((cb.val : ZMod Q) - (ca.val : ZMod Q)) by ring,
        ZMod.val_neg_of_ne_zero, hcf]
    rw [hcr] at hc₁
    have hM : 0 < M := NeZero.pos M
    have hca : ca.val < Q := ca.isLt
    have hcb : cb.val < Q := cb.isLt
    change a.val = 2 * M * ca.val + ra at harep
    change b.val = 2 * M * cb.val + rb at hbrep
    have hgap : ca.val + 3 ≤ cb.val := by omega
    have hfineOrder : a.val < b.val := by
      nlinarith [Nat.zero_le ra, Nat.zero_le rb]
    have hff :
        ((b.val : ZMod (M * (2 * Q))) -
          (a.val : ZMod (M * (2 * Q)))).val = b.val - a.val := by
      have haCast : ((a.val : ZMod (M * (2 * Q)))).val = a.val :=
        ZMod.val_cast_of_lt a.isLt
      have hbCast : ((b.val : ZMod (M * (2 * Q)))).val = b.val :=
        ZMod.val_cast_of_lt b.isLt
      have hab' : ((a.val : ZMod (M * (2 * Q)))).val ≤
          ((b.val : ZMod (M * (2 * Q)))).val := by
        rw [haCast, hbCast]
        exact hfineOrder.le
      simpa [haCast, hbCast] using (ZMod.val_sub hab')
    have hfdiff : b.val - a.val ≠ 0 := by omega
    have hfzneq :
        (b.val : ZMod (M * (2 * Q))) -
          (a.val : ZMod (M * (2 * Q))) ≠ 0 := by
      intro hz
      rw [hz, ZMod.val_zero] at hff
      exact hfdiff hff.symm
    letI : NeZero ((b.val : ZMod (M * (2 * Q))) -
        (a.val : ZMod (M * (2 * Q)))) := ⟨hfzneq⟩
    have hfr :
        ((a.val : ZMod (M * (2 * Q))) -
          (b.val : ZMod (M * (2 * Q)))).val =
            M * (2 * Q) - (b.val - a.val) := by
      rw [show (a.val : ZMod (M * (2 * Q))) -
          (b.val : ZMod (M * (2 * Q))) =
        -((b.val : ZMod (M * (2 * Q))) -
          (a.val : ZMod (M * (2 * Q)))) by ring,
        ZMod.val_neg_of_ne_zero, hff]
    rw [hfr, hff] at hfmin
    have hleftAdd : a.val + 4 * M < b.val := by
      nlinarith [Nat.zero_le ra, Nat.zero_le rb]
    have hleft : 4 * M < b.val - a.val := by omega
    have hwrapGap : cb.val + 3 ≤ Q + ca.val := by omega
    have hrightAdd : b.val + 4 * M < M * (2 * Q) + a.val := by
      nlinarith [Nat.zero_le ra, Nat.zero_le rb]
    have hright : 4 * M < M * (2 * Q) - (b.val - a.val) := by
      omega
    omega

/-- Coordinatewise source-cell owner of a fine site. -/
def cmp99FineSiteCellOwner {M Q : ℕ} [NeZero M] [NeZero Q]
    (x : FinBox 4 (M * (2 * Q))) : FinBox 4 Q :=
  fun i => cmp99FineCoordCellOwner (x i)

/-- The direct fine-site owner is definitionally the same two-stage owner
used by the physical CMP99 dictionary. -/
theorem cmp99FineSiteCellOwner_eq_twoStage {M Q : ℕ}
    [NeZero M] [NeZero Q] (x : FinBox 4 (M * (2 * Q))) :
    cmp99FineSiteCellOwner x =
      cmp99SourceBaseCellOwner (blockSite M (2 * Q) x) := by
  rfl

/-- Four-dimensional lift of the exact periodic quotient contraction. -/
theorem finBoxDist_cmp99FineSiteCellOwner_le_two {M Q : ℕ}
    [NeZero M] [NeZero Q]
    (x y : FinBox 4 (M * (2 * Q)))
    (hxy : finBoxDist x y ≤ 4 * M) :
    finBoxDist (cmp99FineSiteCellOwner x)
      (cmp99FineSiteCellOwner y) ≤ 2 := by
  unfold finBoxDist
  apply Finset.sup_le
  intro i _
  apply finTorusDist_cmp99FineCoordCellOwner_le_two
  exact (finTorusDist_le_finBoxDist x y i).trans hxy

/-- Bond distance controls the source-site distance. -/
theorem finBoxDist_source_le_physicalBondDist {d N : ℕ} [NeZero N]
    (b b' : PhysicalBond d N) :
    finBoxDist (cmp116BondSource b) (cmp116BondSource b') ≤
      physicalBondDist b b' := by
  exact le_max_left _ _

/-- The extra unit in the source condition controls the target endpoint of
the second bond. -/
theorem finBoxDist_source_target_le_physicalBondDist_add_one
    {d N : ℕ} [NeZero N] (b b' : PhysicalBond d N) :
    finBoxDist (cmp116BondSource b) (cmp116BondTarget b') ≤
      physicalBondDist b b' + 1 := by
  calc
    finBoxDist (cmp116BondSource b) (cmp116BondTarget b') ≤
        finBoxDist (cmp116BondSource b) (cmp116BondSource b') +
          finBoxDist (cmp116BondSource b') (cmp116BondTarget b') :=
      finBoxDist_triangle _ _ _
    _ ≤ physicalBondDist b b' + 1 := Nat.add_le_add
      (finBoxDist_source_le_physicalBondDist b b')
      (by simpa [cmp116BondSource, cmp116BondTarget] using
        finBoxDist_shift_le b'.1 b'.2)

/-- Literal bilateral range protection by `Pi^4`.  The `+1` is not a slack
artifact: it is exactly the final edge from the source to the target endpoint
of `b'`. -/
theorem mem_cmp99SourcePi4CollarDomain_physicalBondSupport_of_range
    {M Q Rrange : ℕ} [NeZero M] [NeZero Q]
    (cell : FinBox 4 Q)
    (b b' : PhysicalBond 4 (M * (2 * Q)))
    (hb : b ∈ cmp99SourceBaseCellBondCore (M := M) cell)
    (hbb' : physicalBondDist b b' ≤ Rrange)
    (hrange : Rrange + 1 ≤ 4 * M) :
    b' ∈ cmp99SourceDomainPhysicalBondSupport
      (cmp99SourcePi4CollarDomain cell) := by
  rw [mem_cmp99SourceDomainPhysicalBondSupport_iff]
  rw [mem_cmp99SourceBaseCellBondCore_iff] at hb
  have hsourceOwner : cmp99FineSiteCellOwner (cmp116BondSource b) = cell := by
    rw [cmp99FineSiteCellOwner_eq_twoStage]
    exact hb
  have hsourceDist :
      finBoxDist (cmp116BondSource b) (cmp116BondSource b') ≤ 4 * M :=
    (finBoxDist_source_le_physicalBondDist b b').trans (hbb'.trans (by omega))
  have htargetDist :
      finBoxDist (cmp116BondSource b) (cmp116BondTarget b') ≤ 4 * M :=
    (finBoxDist_source_target_le_physicalBondDist_add_one b b').trans
      (Nat.add_le_add_right hbb' 1 |>.trans hrange)
  have hsourceCells := finBoxDist_cmp99FineSiteCellOwner_le_two
    (cmp116BondSource b) (cmp116BondSource b') hsourceDist
  have htargetCells := finBoxDist_cmp99FineSiteCellOwner_le_two
    (cmp116BondSource b) (cmp116BondTarget b') htargetDist
  constructor
  · rw [cmp99SourcePi4CollarDomain_blocks,
      mem_cmp99SourcePi4CollarCells_iff]
    change finBoxDist cell
      (cmp99SourceBaseCellOwner
        (blockSite M (2 * Q) (cmp116BondSource b'))) ≤ 2
    rw [← cmp99FineSiteCellOwner_eq_twoStage]
    simpa [hsourceOwner] using hsourceCells
  · rw [cmp99SourcePi4CollarDomain_blocks,
      mem_cmp99SourcePi4CollarCells_iff]
    change finBoxDist cell
      (cmp99SourceBaseCellOwner
        (blockSite M (2 * Q) (cmp116BondTarget b'))) ≤ 2
    rw [← cmp99FineSiteCellOwner_eq_twoStage]
    simpa [hsourceOwner] using htargetCells

/-- The complete base core is protected by the source `Pi^4` collar under
the physical range budget. -/
theorem cmp99SourceBaseCellBondCore_subset_pi4PhysicalSupport
    {M Q Rrange : ℕ} [NeZero M] [NeZero Q]
    (cell : FinBox 4 Q)
    (hrange : Rrange + 1 ≤ 4 * M) :
    cmp99SourceBaseCellBondCore (M := M) cell ⊆
      cmp99SourceDomainPhysicalBondSupport
        (cmp99SourcePi4CollarDomain cell) := by
  intro b hb
  exact mem_cmp99SourcePi4CollarDomain_physicalBondSupport_of_range
    cell b b hb (by simp) hrange

end

end YangMills.RG
