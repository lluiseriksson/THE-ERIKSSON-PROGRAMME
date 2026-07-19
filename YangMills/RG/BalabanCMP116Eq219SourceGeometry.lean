import YangMills.RG.BalabanCMP116Eq143To219
import YangMills.RG.BalabanCMP116Eq214Geometry
import YangMills.RG.BalabanCMP116Eq214Incidence
import YangMills.RG.PhysicalShellLocalityQ

/-!
# CMP116 source geometry for equation (2.19)

This file formalizes the geometric step left implicit between Balaban's
equations (1.43), (2.18), and (2.19).  A localization domain is a nonempty
finite family of `M`-blocks connected through codimension-one faces.  Its
fine-lattice carrier is the disjoint union of those blocks, so in dimension
four its cardinality is literally `M ^ 4 * numberOfBlocks`.

For two physical bonds supported in the domain, a spanning walk through the
face graph gives

`physicalBondDist b b' <= 4 * M * numberOfBlocks`.

After rewriting the number of blocks as `M^-4 * |Y|`, this is exactly the
source estimate needed by `cmp116Eq219_metricBudget_of_sourceConditions`.
No kernel-decay hypothesis is introduced here.
-/

namespace YangMills.RG

/-- Lower fine-lattice corner of a coarse `M`-block. -/
def cmp116BlockCorner {d M N' : ℕ} [NeZero M]
    (c : FinBox d N') : FinBox d (M * N') :=
  fun i => ⟨M * (c i).val, by
    exact Nat.mul_lt_mul_of_pos_left (c i).isLt (NeZero.pos M)⟩

@[simp] theorem blockSite_cmp116BlockCorner {d M N' : ℕ}
    [NeZero M] [NeZero N'] (c : FinBox d N') :
    blockSite M N' (cmp116BlockCorner (M := M) c) = c := by
  rw [blockSite_eq_iff]
  intro i
  simp only [cmp116BlockCorner]
  exact Nat.mul_div_cancel_left (c i).val (NeZero.pos M)

/-- Moving by one coarse face moves the lower corner by exactly `M` fine
shifts in that coordinate. -/
theorem cmp116BlockCorner_shift {d M N' : ℕ} [NeZero M] [NeZero N']
    (c : FinBox d N') (i : Fin d) :
    cmp116BlockCorner (FinBox.shift c i) =
      ((fun z : FinBox d (M * N') => FinBox.shift z i)^[M]
        (cmp116BlockCorner c)) := by
  funext j
  apply Fin.ext
  by_cases hji : j = i
  · subst j
    rw [FinBox.iter_shift_apply_self]
    simp only [cmp116BlockCorner, FinBox.shift, if_pos]
    have ha : (c i).val + 1 ≤ N' := (c i).isLt
    by_cases hlt : (c i).val + 1 < N'
    · rw [Nat.mod_eq_of_lt hlt]
      rw [Nat.mod_eq_of_lt]
      · ring
      · nlinarith [NeZero.pos M]
    · have heq : (c i).val + 1 = N' := by omega
      rw [heq, Nat.mod_self]
      simp only [Nat.mul_zero]
      rw [show M * (c i).val + M = M * N' by
        calc
          M * (c i).val + M = M * ((c i).val + 1) := by ring
          _ = M * N' := by rw [heq], Nat.mod_self]
  · rw [FinBox.iter_shift_apply_ne _ _ _ hji]
    simp [cmp116BlockCorner, FinBox.shift, hji]

/-- Periodic face adjacency of coarse blocks.  The two alternatives encode
the two orientations of a shared codimension-one wall. -/
def cmp116CoarseFaceAdj (d N' : ℕ) [NeZero N'] : SimpleGraph (FinBox d N') where
  Adj x y := x ≠ y ∧ ∃ i, y = FinBox.shift x i ∨ x = FinBox.shift y i
  symm := by
    rintro x y ⟨hne, i, h | h⟩
    · exact ⟨hne.symm, i, Or.inr h⟩
    · exact ⟨hne.symm, i, Or.inl h⟩
  loopless := ⟨fun x hx => hx.1 rfl⟩

instance cmp116CoarseFaceAdj_decidableRel (d N' : ℕ) [NeZero N'] :
    DecidableRel (cmp116CoarseFaceAdj d N').Adj := by
  intro x y
  show Decidable (x ≠ y ∧ ∃ i, y = FinBox.shift x i ∨ x = FinBox.shift y i)
  infer_instance

theorem cmp116BlockCorner_adjacent_dist_le {d M N' : ℕ}
    [NeZero M] [NeZero N']
    {x y : FinBox d N'} (hxy : (cmp116CoarseFaceAdj d N').Adj x y) :
    finBoxDist (cmp116BlockCorner (M := M) x)
      (cmp116BlockCorner (M := M) y) ≤ M := by
  rcases hxy.2 with ⟨i, h | h⟩
  · rw [h, cmp116BlockCorner_shift]
    exact finBoxDist_iterate_shift_le _ _ _
  · rw [h, finBoxDist_comm, cmp116BlockCorner_shift]
    exact finBoxDist_iterate_shift_le _ _ _

theorem cmp116BlockCorner_walk_dist_le {d M N' : ℕ}
    [NeZero M] [NeZero N']
    {x y : FinBox d N'} (w : (cmp116CoarseFaceAdj d N').Walk x y) :
    finBoxDist (cmp116BlockCorner (M := M) x)
      (cmp116BlockCorner (M := M) y) ≤ M * w.length := by
  induction w with
  | nil => simp
  | @cons u v t huv p ih =>
      calc
        finBoxDist (cmp116BlockCorner (M := M) u)
            (cmp116BlockCorner (M := M) t) ≤
          finBoxDist (cmp116BlockCorner (M := M) u)
              (cmp116BlockCorner (M := M) v) +
            finBoxDist (cmp116BlockCorner (M := M) v)
              (cmp116BlockCorner (M := M) t) := finBoxDist_triangle _ _ _
        _ ≤ M + M * p.length := Nat.add_le_add
          (cmp116BlockCorner_adjacent_dist_le huv) ih
        _ = M * (SimpleGraph.Walk.cons huv p).length := by
          rw [SimpleGraph.Walk.length_cons]
          ring

/-- Source-faithful localization domain in dimension four: a nonempty finite
face-connected family of coarse `M`-blocks. -/
structure CMP116LocalizationDomain (M N' : ℕ) [NeZero N'] where
  blocks : Finset (FinBox 4 N')
  nonempty : blocks.Nonempty
  connected : walkConnected (cmp116CoarseFaceAdj 4 N') blocks

/-- Physical bonds whose source and target sites both lie in the domain. -/
noncomputable def CMP116LocalizationDomain.bondSupport
    {M N' : ℕ} [NeZero M] [NeZero N']
    (Y : CMP116LocalizationDomain M N') :
    Finset (PhysicalBond 4 (M * N')) :=
  Finset.univ.filter fun b =>
    cmp116BondSourceBlock b ∈ Y.blocks ∧
      cmp116BondTargetBlock b ∈ Y.blocks

theorem mem_cmp116LocalizationDomain_bondSupport_sourceBlock
    {M N' : ℕ} [NeZero M] [NeZero N']
    {Y : CMP116LocalizationDomain M N'} {b : PhysicalBond 4 (M * N')}
    (hb : b ∈ Y.bondSupport) : cmp116BondSourceBlock b ∈ Y.blocks := by
  have h : cmp116BondSourceBlock b ∈ Y.blocks ∧
      cmp116BondTargetBlock b ∈ Y.blocks := by
    simpa [CMP116LocalizationDomain.bondSupport] using hb
  exact h.1

/-- The literal fine-lattice carrier of the union of coarse blocks. -/
noncomputable def CMP116LocalizationDomain.siteSupport
    {M N' : ℕ} [NeZero M] [NeZero N']
    (Y : CMP116LocalizationDomain M N') : Finset (FinBox 4 (M * N')) :=
  Y.blocks.biUnion (blockOf M N')

/-- Source `|Y|`: cardinality of the fine-lattice carrier. -/
noncomputable def CMP116LocalizationDomain.sourceCard
    {M N' : ℕ} [NeZero M] [NeZero N']
    (Y : CMP116LocalizationDomain M N') : ℕ :=
  Y.siteSupport.card

theorem cmp116LocalizationDomain_blocks_pairwiseDisjoint
    {M N' : ℕ} [NeZero M] [NeZero N']
    (Y : CMP116LocalizationDomain M N') :
    (Y.blocks : Set (FinBox 4 N')).PairwiseDisjoint (blockOf M N') := by
  intro x hx y hy hxy
  change Disjoint (blockOf M N' x) (blockOf M N' y)
  rw [Finset.disjoint_left]
  intro z hzx hzy
  have hxz : blockSite M N' z = x := (mem_blockOf M N' x z).mp hzx
  have hyz : blockSite M N' z = y := (mem_blockOf M N' y z).mp hzy
  exact hxy (hxz.symm.trans hyz)

/-- Exact normalization from equation (2.30): `M^-4 |Y|` is the number of
coarse blocks. -/
theorem cmp116LocalizationDomain_sourceCard_eq
    {M N' : ℕ} [NeZero M] [NeZero N']
    (Y : CMP116LocalizationDomain M N') :
    Y.sourceCard = M ^ 4 * Y.blocks.card := by
  unfold CMP116LocalizationDomain.sourceCard CMP116LocalizationDomain.siteSupport
  rw [Finset.card_biUnion (cmp116LocalizationDomain_blocks_pairwiseDisjoint Y)]
  simp [blockOf_card, Nat.mul_comm]

/-- Face connectivity supplies a walk no longer than twice the number of
edges in a spanning tree of the block family. -/
theorem cmp116LocalizationDomain_exists_short_walk
    {M N' : ℕ} [NeZero N']
    (Y : CMP116LocalizationDomain M N')
    {x y : FinBox 4 N'} (hx : x ∈ Y.blocks) (hy : y ∈ Y.blocks) :
    ∃ w : (cmp116CoarseFaceAdj 4 N').Walk x y,
      w.length ≤ 2 * (Y.blocks.card - 1) := by
  obtain ⟨tour, htourSupport, htourLength⟩ :=
    exists_spanning_closed_walk (G := cmp116CoarseFaceAdj 4 N')
      Y.blocks hx (fun z hz => Y.connected x hx z hz)
  have hySupport : y ∈ tour.support := by
    rw [← List.mem_toFinset, htourSupport]
    exact hy
  refine ⟨tour.takeUntil y hySupport, ?_⟩
  exact (tour.length_takeUntil_le hySupport).trans_eq htourLength

theorem cmp116BondSource_to_blockCorner_dist_le
    {M N' : ℕ} [NeZero M] [NeZero N']
    (b : PhysicalBond 4 (M * N')) :
    finBoxDist b.1
      (cmp116BlockCorner (M := M) (cmp116BondSourceBlock b)) ≤ M - 1 := by
  apply finBoxDist_le_of_same_block
  change blockSite M N' b.1 =
    blockSite M N' (cmp116BlockCorner (M := M) (cmp116BondSourceBlock b))
  rw [blockSite_cmp116BlockCorner]
  rfl

/-- Geometric source estimate `(G)`: two bonds supported in a face-connected
domain of `n` coarse blocks have physical distance at most `4 M n`. -/
theorem physicalBondDist_le_four_mul_cmp116DomainBlockCard
    {M N' : ℕ} [NeZero M] [NeZero N']
    (Y : CMP116LocalizationDomain M N')
    {b b' : PhysicalBond 4 (M * N')}
    (hb : b ∈ Y.bondSupport) (hb' : b' ∈ Y.bondSupport) :
    physicalBondDist b b' ≤ 4 * M * Y.blocks.card := by
  have hbBlock := mem_cmp116LocalizationDomain_bondSupport_sourceBlock hb
  have hb'Block := mem_cmp116LocalizationDomain_bondSupport_sourceBlock hb'
  obtain ⟨w, hwlen⟩ :=
    cmp116LocalizationDomain_exists_short_walk Y hbBlock hb'Block
  have hcorners :
      finBoxDist
        (cmp116BlockCorner (M := M) (cmp116BondSourceBlock b))
        (cmp116BlockCorner (M := M) (cmp116BondSourceBlock b')) ≤
      M * (2 * (Y.blocks.card - 1)) :=
    (cmp116BlockCorner_walk_dist_le w).trans (Nat.mul_le_mul_left M hwlen)
  have hsite : finBoxDist b.1 b'.1 ≤ 4 * M * Y.blocks.card := by
    calc
      finBoxDist b.1 b'.1 ≤
          finBoxDist b.1
              (cmp116BlockCorner (M := M) (cmp116BondSourceBlock b)) +
            finBoxDist
              (cmp116BlockCorner (M := M) (cmp116BondSourceBlock b)) b'.1 :=
        finBoxDist_triangle _ _ _
      _ ≤ finBoxDist b.1
              (cmp116BlockCorner (M := M) (cmp116BondSourceBlock b)) +
            (finBoxDist
                (cmp116BlockCorner (M := M) (cmp116BondSourceBlock b))
                (cmp116BlockCorner (M := M) (cmp116BondSourceBlock b')) +
              finBoxDist
                (cmp116BlockCorner (M := M) (cmp116BondSourceBlock b')) b'.1) :=
        Nat.add_le_add_left (finBoxDist_triangle _ _ _) _
      _ ≤ (M - 1) + (M * (2 * (Y.blocks.card - 1)) + (M - 1)) := by
        exact Nat.add_le_add (cmp116BondSource_to_blockCorner_dist_le b)
          (Nat.add_le_add hcorners (by
            rw [finBoxDist_comm]
            exact cmp116BondSource_to_blockCorner_dist_le b'))
      _ ≤ 4 * M * Y.blocks.card := by
        have hn : 1 ≤ Y.blocks.card := Finset.one_le_card.mpr Y.nonempty
        have hM : 1 ≤ M := NeZero.one_le
        have hsub : M * (2 * (Y.blocks.card - 1)) ≤
            2 * M * Y.blocks.card := by
          calc
            M * (2 * (Y.blocks.card - 1)) =
                2 * M * (Y.blocks.card - 1) := by ring
            _ ≤ 2 * M * Y.blocks.card :=
              Nat.mul_le_mul_left (2 * M) (Nat.sub_le _ _)
        have hMn : M ≤ M * Y.blocks.card := by
          simpa using Nat.mul_le_mul_left M hn
        calc
          (M - 1) + (M * (2 * (Y.blocks.card - 1)) + (M - 1)) ≤
              M + (2 * M * Y.blocks.card + M) := by omega
          _ ≤ 4 * M * Y.blocks.card := by nlinarith
  unfold physicalBondDist
  apply max_le
  · exact hsite
  · split_ifs
    · exact Nat.zero_le _
    · have hn : 1 ≤ Y.blocks.card := Finset.one_le_card.mpr Y.nonempty
      have hM : 1 ≤ M := NeZero.one_le
      have hone : 1 ≤ M * Y.blocks.card := by
        simpa using Nat.mul_le_mul hM hn
      calc
        1 ≤ M * Y.blocks.card := hone
        _ ≤ 4 * M * Y.blocks.card := by
          have h := Nat.mul_le_mul_right (M * Y.blocks.card) (show 1 ≤ 4 by omega)
          simpa [Nat.mul_assoc] using h

/-- Real-valued source geometry in exactly the scale used by equation (2.19). -/
theorem cmp116Eq219_sourceGeometry
    {M N' : ℕ} [NeZero M] [NeZero N']
    (Y : CMP116LocalizationDomain M N')
    {b b' : PhysicalBond 4 (M * N')}
    (hb : b ∈ Y.bondSupport) (hb' : b' ∈ Y.bondSupport)
    {kappa1 : ℝ} (hkappa1 : 1 ≤ kappa1) :
    (1 / 16 : ℝ) * (kappa1 - 1) * (M : ℝ)⁻¹ *
        (physicalBondDist b b' : ℝ) ≤
      (1 / 4 : ℝ) * (kappa1 - 1) * ((M : ℝ) ^ 4)⁻¹ *
        Y.sourceCard := by
  have hdistNat := physicalBondDist_le_four_mul_cmp116DomainBlockCard Y hb hb'
  have hdist : (physicalBondDist b b' : ℝ) ≤
      4 * (M : ℝ) * Y.blocks.card := by
    exact_mod_cast hdistNat
  have hkdiff : 0 ≤ kappa1 - 1 := sub_nonneg.mpr hkappa1
  have hcoef : 0 ≤ (1 / 16 : ℝ) * (kappa1 - 1) * (M : ℝ)⁻¹ := by
    positivity
  calc
    (1 / 16 : ℝ) * (kappa1 - 1) * (M : ℝ)⁻¹ *
          (physicalBondDist b b' : ℝ) ≤
        (1 / 16 : ℝ) * (kappa1 - 1) * (M : ℝ)⁻¹ *
          (4 * (M : ℝ) * Y.blocks.card) :=
      mul_le_mul_of_nonneg_left hdist hcoef
    _ = (1 / 4 : ℝ) * (kappa1 - 1) * ((M : ℝ) ^ 4)⁻¹ *
          Y.sourceCard := by
      rw [cmp116LocalizationDomain_sourceCard_eq]
      push_cast
      field_simp
      ring

/-- The printed scale condition and source domain geometry produce the full
metric budget required for equation (2.19). -/
theorem cmp116Eq219_metricBudget_physical
    {M N' : ℕ} [NeZero M] [NeZero N']
    (Y : CMP116LocalizationDomain M N')
    {b b' : PhysicalBond 4 (M * N')}
    (hb : b ∈ Y.bondSupport) (hb' : b' ∈ Y.bondSupport)
    {kappa1 delta kappa domainDist : ℝ}
    (hkappa1 : 1 ≤ kappa1) (hdomainDist : 0 ≤ domainDist)
    (hkappa : (1 - 3 * delta) * kappa ≤
      (1 / 8 : ℝ) * (kappa1 - 1)) :
    CMP116Eq219MetricBudget M kappa1 delta kappa domainDist
      Y.sourceCard (physicalBondDist b b') := by
  exact cmp116Eq219_metricBudget_of_sourceConditions hdomainDist hkappa
    (cmp116Eq219_sourceGeometry Y hb hb' hkappa1)

end YangMills.RG
