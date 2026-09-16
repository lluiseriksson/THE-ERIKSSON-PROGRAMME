import YangMills.RG.BalabanCMP116Eq143To219
import YangMills.RG.BalabanCMP116Eq214Geometry
import YangMills.RG.BalabanCMP116Eq214Incidence
import YangMills.RG.PhysicalShellLocalityQ

namespace YangMills.RG

def testBlockCorner {d M N' : ℕ} [NeZero M]
    (c : FinBox d N') : FinBox d (M * N') :=
  fun i => ⟨M * (c i).val, by
    exact Nat.mul_lt_mul_of_pos_left (c i).isLt (NeZero.pos M)⟩

@[simp] theorem blockSite_testBlockCorner {d M N' : ℕ}
    [NeZero M] [NeZero N'] (c : FinBox d N') :
    blockSite M N' (testBlockCorner (M := M) c) = c := by
  rw [blockSite_eq_iff]
  intro i
  simp only [testBlockCorner]
  exact Nat.mul_div_cancel_left (c i).val (NeZero.pos M)

theorem testBlockCorner_shift {d M N' : ℕ} [NeZero M] [NeZero N']
    (c : FinBox d N') (i : Fin d) :
    testBlockCorner (FinBox.shift c i) =
      ((fun z : FinBox d (M * N') => FinBox.shift z i)^[M]
        (testBlockCorner c)) := by
  funext j
  apply Fin.ext
  by_cases hji : j = i
  · subst j
    rw [FinBox.iter_shift_apply_self]
    simp only [testBlockCorner, FinBox.shift, if_pos]
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
    simp [testBlockCorner, FinBox.shift, hji]

def testCoarseFaceAdj (d N' : ℕ) [NeZero N'] : SimpleGraph (FinBox d N') where
  Adj x y := x ≠ y ∧ ∃ i, y = FinBox.shift x i ∨ x = FinBox.shift y i
  symm := by
    rintro x y ⟨hne, i, h | h⟩
    · exact ⟨hne.symm, i, Or.inr h⟩
    · exact ⟨hne.symm, i, Or.inl h⟩
  loopless := ⟨fun x hx => hx.1 rfl⟩

instance testCoarseFaceAdj_decidableRel (d N' : ℕ) [NeZero N'] :
    DecidableRel (testCoarseFaceAdj d N').Adj := by
  intro x y
  show Decidable (x ≠ y ∧ ∃ i, y = FinBox.shift x i ∨ x = FinBox.shift y i)
  infer_instance

theorem testBlockCorner_adjacent_dist_le {d M N' : ℕ}
    [NeZero M] [NeZero N']
    {x y : FinBox d N'} (hxy : (testCoarseFaceAdj d N').Adj x y) :
    finBoxDist (testBlockCorner (M := M) x)
      (testBlockCorner (M := M) y) ≤ M := by
  rcases hxy.2 with ⟨i, h | h⟩
  · rw [h, testBlockCorner_shift]
    exact finBoxDist_iterate_shift_le _ _ _
  · rw [h, finBoxDist_comm, testBlockCorner_shift]
    exact finBoxDist_iterate_shift_le _ _ _

theorem testBlockCorner_walk_dist_le {d M N' : ℕ}
    [NeZero M] [NeZero N']
    {x y : FinBox d N'} (w : (testCoarseFaceAdj d N').Walk x y) :
    finBoxDist (testBlockCorner (M := M) x)
      (testBlockCorner (M := M) y) ≤ M * w.length := by
  induction w with
  | nil => simp
  | @cons u v t huv p ih =>
      calc
        finBoxDist (testBlockCorner (M := M) u)
            (testBlockCorner (M := M) t) ≤
          finBoxDist (testBlockCorner (M := M) u)
              (testBlockCorner (M := M) v) +
            finBoxDist (testBlockCorner (M := M) v)
              (testBlockCorner (M := M) t) := finBoxDist_triangle _ _ _
        _ ≤ M + M * p.length := Nat.add_le_add
          (testBlockCorner_adjacent_dist_le huv) ih
        _ = M * (SimpleGraph.Walk.cons huv p).length := by
          rw [SimpleGraph.Walk.length_cons]
          ring

structure TestLocalizationDomain (d M N' : ℕ) [NeZero N'] where
  blocks : Finset (FinBox d N')
  nonempty : blocks.Nonempty
  connected : walkConnected (testCoarseFaceAdj d N') blocks

noncomputable def TestLocalizationDomain.bondSupport
    {d M N' : ℕ} [NeZero M] [NeZero N']
    (Y : TestLocalizationDomain d M N') :
    Finset (PhysicalBond d (M * N')) :=
  Finset.univ.filter fun b =>
    cmp116BondSourceBlock b ∈ Y.blocks ∧
      cmp116BondTargetBlock b ∈ Y.blocks

theorem mem_testBondSupport_sourceBlock
    {d M N' : ℕ} [NeZero M] [NeZero N']
    {Y : TestLocalizationDomain d M N'} {b : PhysicalBond d (M * N')}
    (hb : b ∈ Y.bondSupport) : cmp116BondSourceBlock b ∈ Y.blocks := by
  have h : cmp116BondSourceBlock b ∈ Y.blocks ∧
      cmp116BondTargetBlock b ∈ Y.blocks := by
    simpa [TestLocalizationDomain.bondSupport] using hb
  exact h.1

theorem testLocalizationDomain_exists_short_walk
    {d M N' : ℕ} [NeZero N']
    (Y : TestLocalizationDomain d M N')
    {x y : FinBox d N'} (hx : x ∈ Y.blocks) (hy : y ∈ Y.blocks) :
    ∃ w : (testCoarseFaceAdj d N').Walk x y,
      w.length ≤ 2 * (Y.blocks.card - 1) := by
  obtain ⟨tour, htourSupport, htourLength⟩ :=
    exists_spanning_closed_walk (G := testCoarseFaceAdj d N')
      Y.blocks hx (fun z hz => Y.connected x hx z hz)
  have hySupport : y ∈ tour.support := by
    rw [← List.mem_toFinset, htourSupport]
    exact hy
  refine ⟨tour.takeUntil y hySupport, ?_⟩
  exact (tour.length_takeUntil_le hySupport).trans_eq htourLength

theorem testBondSource_to_blockCorner_dist_le
    {d M N' : ℕ} [NeZero M] [NeZero N']
    (b : PhysicalBond d (M * N')) :
    finBoxDist b.1
      (testBlockCorner (M := M) (cmp116BondSourceBlock b)) ≤ M - 1 := by
  apply finBoxDist_le_of_same_block
  change blockSite M N' b.1 =
    blockSite M N' (testBlockCorner (M := M) (cmp116BondSourceBlock b))
  rw [blockSite_testBlockCorner]
  rfl

theorem testPhysicalBondDist_le_four_mul_blockCard
    {d M N' : ℕ} [NeZero M] [NeZero N']
    (Y : TestLocalizationDomain d M N')
    {b b' : PhysicalBond d (M * N')}
    (hb : b ∈ Y.bondSupport) (hb' : b' ∈ Y.bondSupport) :
    physicalBondDist b b' ≤ 4 * M * Y.blocks.card := by
  have hbBlock := mem_testBondSupport_sourceBlock hb
  have hb'Block := mem_testBondSupport_sourceBlock hb'
  obtain ⟨w, hwlen⟩ :=
    testLocalizationDomain_exists_short_walk Y hbBlock hb'Block
  have hcorners :
      finBoxDist
        (testBlockCorner (M := M) (cmp116BondSourceBlock b))
        (testBlockCorner (M := M) (cmp116BondSourceBlock b')) ≤
      M * (2 * (Y.blocks.card - 1)) :=
    (testBlockCorner_walk_dist_le w).trans (Nat.mul_le_mul_left M hwlen)
  have hsite : finBoxDist b.1 b'.1 ≤ 4 * M * Y.blocks.card := by
    calc
      finBoxDist b.1 b'.1 ≤
          finBoxDist b.1
              (testBlockCorner (M := M) (cmp116BondSourceBlock b)) +
            finBoxDist
              (testBlockCorner (M := M) (cmp116BondSourceBlock b)) b'.1 :=
        finBoxDist_triangle _ _ _
      _ ≤ finBoxDist b.1
              (testBlockCorner (M := M) (cmp116BondSourceBlock b)) +
            (finBoxDist
                (testBlockCorner (M := M) (cmp116BondSourceBlock b))
                (testBlockCorner (M := M) (cmp116BondSourceBlock b')) +
              finBoxDist
                (testBlockCorner (M := M) (cmp116BondSourceBlock b')) b'.1) :=
        Nat.add_le_add_left (finBoxDist_triangle _ _ _) _
      _ ≤ (M - 1) + (M * (2 * (Y.blocks.card - 1)) + (M - 1)) := by
        exact Nat.add_le_add (testBondSource_to_blockCorner_dist_le b)
          (Nat.add_le_add hcorners (by
            rw [finBoxDist_comm]
            exact testBondSource_to_blockCorner_dist_le b'))
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

def TestLocalizationDomain.sourceFineCard4
    {M N' : ℕ} [NeZero N']
    (Y : TestLocalizationDomain 4 M N') : ℕ :=
  M ^ 4 * Y.blocks.card

noncomputable def TestLocalizationDomain.siteSupport
    {d M N' : ℕ} [NeZero M] [NeZero N']
    (Y : TestLocalizationDomain d M N') : Finset (FinBox d (M * N')) :=
  Y.blocks.biUnion (blockOf M N')

theorem testLocalizationDomain_blocks_pairwiseDisjoint
    {d M N' : ℕ} [NeZero M] [NeZero N']
    (Y : TestLocalizationDomain d M N') :
    (Y.blocks : Set (FinBox d N')).PairwiseDisjoint (blockOf M N') := by
  intro x hx y hy hxy
  change Disjoint (blockOf M N' x) (blockOf M N' y)
  rw [Finset.disjoint_left]
  intro z hzx hzy
  have hxz : blockSite M N' z = x := (mem_blockOf M N' x z).mp hzx
  have hyz : blockSite M N' z = y := (mem_blockOf M N' y z).mp hzy
  exact hxy (hxz.symm.trans hyz)

theorem testLocalizationDomain_siteSupport_card
    {d M N' : ℕ} [NeZero M] [NeZero N']
    (Y : TestLocalizationDomain d M N') :
    Y.siteSupport.card = M ^ d * Y.blocks.card := by
  unfold TestLocalizationDomain.siteSupport
  rw [Finset.card_biUnion (testLocalizationDomain_blocks_pairwiseDisjoint Y)]
  simp [blockOf_card, Nat.mul_comm]

theorem testLocalizationDomain_sourceFineCard4_eq_siteSupport_card
    {M N' : ℕ} [NeZero M] [NeZero N']
    (Y : TestLocalizationDomain 4 M N') :
    Y.sourceFineCard4 = Y.siteSupport.card := by
  rw [testLocalizationDomain_siteSupport_card]
  rfl

theorem testCmp116Eq219_sourceGeometry
    {M N' : ℕ} [NeZero M] [NeZero N']
    (Y : TestLocalizationDomain 4 M N')
    {b b' : PhysicalBond 4 (M * N')}
    (hb : b ∈ Y.bondSupport) (hb' : b' ∈ Y.bondSupport)
    {kappa1 : ℝ} (hkappa1 : 1 ≤ kappa1) :
    (1 / 16 : ℝ) * (kappa1 - 1) * (M : ℝ)⁻¹ *
        (physicalBondDist b b' : ℝ) ≤
      (1 / 4 : ℝ) * (kappa1 - 1) * ((M : ℝ) ^ 4)⁻¹ *
        Y.sourceFineCard4 := by
  have hdistNat := testPhysicalBondDist_le_four_mul_blockCard Y hb hb'
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
          Y.sourceFineCard4 := by
      unfold TestLocalizationDomain.sourceFineCard4
      push_cast
      field_simp
      <;> ring

theorem testCmp116Eq219_metricBudget_physical
    {M N' : ℕ} [NeZero M] [NeZero N']
    (Y : TestLocalizationDomain 4 M N')
    {b b' : PhysicalBond 4 (M * N')}
    (hb : b ∈ Y.bondSupport) (hb' : b' ∈ Y.bondSupport)
    {kappa1 delta kappa domainDist : ℝ}
    (hkappa1 : 1 ≤ kappa1) (hdomainDist : 0 ≤ domainDist)
    (hkappa : (1 - 3 * delta) * kappa ≤
      (1 / 8 : ℝ) * (kappa1 - 1)) :
    CMP116Eq219MetricBudget M kappa1 delta kappa domainDist
      Y.sourceFineCard4 (physicalBondDist b b') := by
  exact cmp116Eq219_metricBudget_of_sourceConditions hdomainDist hkappa
    (testCmp116Eq219_sourceGeometry Y hb hb' hkappa1)

end YangMills.RG
