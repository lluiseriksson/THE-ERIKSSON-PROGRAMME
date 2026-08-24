import YangMills.RG.BalabanCMP99SourceRetainedExactReadCarrier
import YangMills.RG.BalabanCMP99CovariantPathControl
import YangMills.RG.BalabanCMP98ContourPivotAvoidance

/-!
PRE-VALIDATION: source is present in scratch only; no `.olean` has been
materialized and no compiler or axiom-oracle verdict exists for this module.

# Endpoint geometry for the retained CMP99 read carrier

This is the geometric prefix of C6c.8f2g.  It records the orientation-safe
two-endpoint invariant and proves it for the exact carrier of one transported
average and for one selected Ubar bond whose two coarse endpoint blocks are
active.  It does not yet close the recursive retained carrier or discharge the
f4 cube-containment premise.
-/

namespace YangMills.RG

open YangMills

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

/-- Both sites read by a positive physical-bond coordinate lie in `S`.  The
second endpoint is the positive shift of the stored source coordinate. -/
def CMP99PhysicalBondEndpointsIn
    {N : ℕ} [NeZero N] (S : Finset (FinBox d N))
    (b : PhysicalBond d N) : Prop :=
  b.1 ∈ S ∧ b.1.shift b.2 ∈ S

/-- Endpoint containment is monotone in its site carrier. -/
theorem CMP99PhysicalBondEndpointsIn.mono
    {N : ℕ} [NeZero N] {S T : Finset (FinBox d N)}
    {b : PhysicalBond d N}
    (hST : S ⊆ T) (hb : CMP99PhysicalBondEndpointsIn S b) :
    CMP99PhysicalBondEndpointsIn T b :=
  ⟨hST hb.1, hST hb.2⟩

/-- Reversing a literal oriented path preserves its site carrier.  This is the
orientation-safe bridge used for the return contour `Gamma3`; it swaps source
and target explicitly rather than treating the reversed edge as the same
positive physical coordinate. -/
theorem OrientedLatticePath.StaysIn.symm
    {G : Type*} [Group G]
    {a b : FinBox d (M * N')}
    {Gamma : OrientedLatticePath (G := G) a b}
    {S : Finset (FinBox d (M * N'))}
    (hstay : Gamma.StaysIn S) : Gamma.symm.StaysIn S := by
  intro e he
  simp only [OrientedLatticePath.symm, reverseLatticePath,
    List.mem_reverse, List.mem_map] at he
  obtain ⟨f, hf, rfl⟩ := he
  have h := hstay f hf
  simpa only [FiniteLatticeGeometry.src_reverse,
    FiniteLatticeGeometry.dst_reverse] using And.intro h.2 h.1

/-- `StaysIn` controls both endpoints of the positive physical coordinate,
including when the literal path edge is negatively oriented. -/
theorem physicalBondOfEdge_endpointsIn_of_staysIn
    {G : Type*} [Group G]
    {a b : FinBox d (M * N')}
    {Gamma : OrientedLatticePath (G := G) a b}
    {S : Finset (FinBox d (M * N'))}
    (hstay : Gamma.StaysIn S)
    {e : ConcreteEdge d (M * N')} (he : e ∈ Gamma.edges) :
    CMP99PhysicalBondEndpointsIn S (physicalBondOfEdge e) := by
  have h := hstay e he
  rcases e with ⟨x, i, sign⟩
  cases sign with
  | false =>
      constructor
      · simpa [CMP99PhysicalBondEndpointsIn, physicalBondOfEdge,
          ConcreteEdge.dstV] using h.2
      · simpa [CMP99PhysicalBondEndpointsIn, physicalBondOfEdge,
          ConcreteEdge.srcV] using h.1
  | true =>
      constructor
      · simpa [CMP99PhysicalBondEndpointsIn, physicalBondOfEdge,
          ConcreteEdge.srcV] using h.1
      · simpa [CMP99PhysicalBondEndpointsIn, physicalBondOfEdge,
          ConcreteEdge.dstV] using h.2

/-- During the first `M` positive fine steps from a point of `y`'s block, the
block owner is either `y` or its single positive `mu`-neighbour.  The proof
tracks the internal offset and treats the periodic seam separately. -/
theorem blockSite_iterate_shift_eq_self_or_shift
    (y : FinBox d N') (x : FinBox d (M * N')) (mu : Fin d)
    (hx : x ∈ blockOf M N' y) (k : ℕ) (hk : k ≤ M) :
    blockSite M N' ((fun z => FinBox.shift z mu)^[k] x) = y ∨
      blockSite M N' ((fun z => FinBox.shift z mu)^[k] x) = y.shift mu := by
  let r := cmp99BlockOffsetOfMem y x hx
  have hxrepr : cmp99BlockEmbed y r = x :=
    cmp99BlockEmbed_offsetOfMem y x hx
  rw [← hxrepr]
  have hbase : blockSite M N' (cmp99BlockEmbed y r) = y :=
    (mem_blockOf M N' y (cmp99BlockEmbed y r)).mp
      (cmp99BlockEmbed_mem_blockOf y r)
  by_cases hcross : (r mu).val + k < M
  · left
    rw [blockSite_eq_iff]
    intro i
    by_cases hi : i = mu
    · subst i
      rw [iterShift_apply_self]
      simp only [cmp99BlockEmbed]
      rw [Nat.mod_eq_of_lt]
      · apply Nat.div_eq_of_lt_le
        · rw [Nat.mul_comm]
          omega
        · rw [Nat.succ_mul, Nat.mul_comm (y mu).val M]
          omega
      · calc
          M * (y mu).val + (r mu).val + k <
              M * (y mu).val + M := by omega
          _ = M * ((y mu).val + 1) := by ring
          _ ≤ M * N' := Nat.mul_le_mul_left M (y mu).isLt
    · rw [iterShift_apply_ne _ _ _ hi]
      exact congrArg Fin.val (congrFun hbase i)
  · right
    rw [blockSite_eq_iff]
    intro i
    by_cases hi : i = mu
    · subst i
      rw [iterShift_apply_self]
      simp only [cmp99BlockEmbed, FinBox.shift, if_pos]
      have hsum_lt : (r mu).val + k < 2 * M := by
        have hr := (r mu).isLt
        omega
      by_cases hnowrap : (y mu).val + 1 < N'
      · rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt hnowrap]
        · apply Nat.div_eq_of_lt_le
          · rw [Nat.mul_comm]
            have hlower :
                M * ((y mu).val + 1) ≤
                  M * (y mu).val + (r mu).val + k := by
              rw [Nat.mul_add, Nat.mul_one]
              omega
            exact hlower
          · rw [Nat.succ_mul, Nat.mul_comm ((y mu).val + 1) M]
            have hupper :
                M * (y mu).val + (r mu).val + k <
                  M * ((y mu).val + 2) := by
              rw [show M * ((y mu).val + 2) =
                M * (y mu).val + 2 * M by ring]
              omega
            exact hupper
        · calc
            M * (y mu).val + (r mu).val + k <
                M * ((y mu).val + 2) := by
              rw [show M * ((y mu).val + 2) =
                M * (y mu).val + 2 * M by ring]
              omega
            _ ≤ M * N' := by
              exact Nat.mul_le_mul_left M (by omega)
      · have hlast : (y mu).val + 1 = N' := by omega
        have hremDecomp :
            (r mu).val + k = M + ((r mu).val + k - M) := by
          omega
        have hsplit :
            M * (y mu).val + (r mu).val + k =
              M * N' + ((r mu).val + k - M) := by
          calc
            M * (y mu).val + (r mu).val + k =
                M * (y mu).val +
                  (M + ((r mu).val + k - M)) := by omega
            _ = M * ((y mu).val + 1) +
                  ((r mu).val + k - M) := by ring
            _ = M * N' + ((r mu).val + k - M) := by rw [hlast]
        have hrem_lt_M : (r mu).val + k - M < M := by omega
        have hM_le_MN : M ≤ M * N' := by
          simpa using Nat.mul_le_mul_left M
            (Nat.one_le_iff_ne_zero.mpr (NeZero.ne N'))
        have hrem_lt_MN : (r mu).val + k - M < M * N' :=
          lt_of_lt_of_le hrem_lt_M hM_le_MN
        rw [hsplit, Nat.add_mod, Nat.mod_self, zero_add]
        simp [Nat.mod_eq_of_lt hrem_lt_MN,
          Nat.div_eq_of_lt hrem_lt_M, hlast]
    · rw [iterShift_apply_ne _ _ _ hi]
      have hcoord := congrArg Fin.val (congrFun hbase i)
      simpa [FinBox.shift, hi] using hcoord

/-- The literal `M`-step source transport reads only the source block and its
single positive coarse neighbour, including across the periodic seam. -/
theorem cmp99SourceParallelTransportPath_endpointsIn_twoBlocks
    (y : FinBox d N') (x : FinBox d (M * N')) (mu : Fin d)
    (hx : x ∈ blockOf M N' y)
    (e : ConcreteEdge d (M * N'))
    (he : e ∈
      (cmp99SourceParallelTransportPath (G := SUN Nc) x mu).edges) :
    CMP99PhysicalBondEndpointsIn
      (blockOf M N' y ∪ blockOf M N' (y.shift mu))
      (physicalBondOfEdge e) := by
  obtain ⟨k, hk, hbond⟩ :=
    mem_cmp99StraightPositivePath_edges_exists
      (G := SUN Nc) x mu M e he
  rw [hbond]
  unfold CMP99PhysicalBondEndpointsIn
  constructor
  · rw [Finset.mem_union, mem_blockOf, mem_blockOf]
    exact blockSite_iterate_shift_eq_self_or_shift y x mu hx k
      (Nat.le_of_lt hk)
  · have hsucc :
        (((fun z => FinBox.shift z mu)^[k] x).shift mu) =
          ((fun z => FinBox.shift z mu)^[k + 1] x) := by
      rw [Function.iterate_succ_apply']
    rw [hsucc, Finset.mem_union, mem_blockOf, mem_blockOf]
    exact blockSite_iterate_shift_eq_self_or_shift y x mu hx (k + 1)
      (Nat.succ_le_of_lt hk)

/-- Every positive coordinate read by the literal one-step transported average
has both endpoints in the physical active region.  The proof consumes the
complete-block active-site law and the actual block-contained contour; it
accepts no carrier inclusion from the caller. -/
theorem cmp99SourceTransportedAverageFineReadBonds_endpointsIn
    (Omega : ActiveGaugeRegion d (M * N'))
    (q : PhysicalBond d (M * N'))
    (hq : q ∈ cmp99SourceTransportedAverageFineReadBonds
      (Nc := Nc) Omega) :
    CMP99PhysicalBondEndpointsIn Omega.sites q := by
  unfold cmp99SourceTransportedAverageFineReadBonds at hq
  obtain ⟨y, hy, hq⟩ := Finset.mem_biUnion.mp hq
  obtain ⟨x, hx, hq⟩ := Finset.mem_biUnion.mp hq
  unfold cmp99PhysicalBondsOfEdgeList at hq
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hq
  have he' : e ∈
      (cmp99BlockContainedContourSystem (G := SUN Nc) y x).edges := by
    simpa using he
  have hendpoints : CMP99PhysicalBondEndpointsIn (blockOf M N' y)
      (physicalBondOfEdge e) :=
    physicalBondOfEdge_endpointsIn_of_staysIn
      (cmp99BlockContainedContourSystem_staysIn
        (G := SUN Nc) y x hx) he'
  have hblock : blockOf M N' y ⊆ Omega.sites :=
    (mem_cmp99ActiveCoarseRegion_sites_iff Omega y).mp hy
  exact CMP99PhysicalBondEndpointsIn.mono
    (b := physicalBondOfEdge e) hblock hendpoints

/-- The exact fine read carrier of one selected Ubar bond stays inside the
union of its two active endpoint blocks.  The base path and `Gamma2` use the
seam-safe `M`-step theorem, while `Gamma1` and reversed `Gamma3` consume the
literal block-contour certificates.  No carrier inclusion is accepted from the
caller. -/
theorem cmp99SourceUbarFineReadBonds_endpointsIn
    (Omega : ActiveGaugeRegion d (M * N'))
    (b : PhysicalBond d N')
    (hb : b.1 ∈
          (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega).sites ∧
        b.1.shift b.2 ∈
          (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega).sites)
    (q : PhysicalBond d (M * N'))
    (hq : q ∈ cmp99SourceUbarFineReadBonds (Nc := Nc) b) :
    CMP99PhysicalBondEndpointsIn Omega.sites q := by
  have hsource : blockOf M N' b.1 ⊆ Omega.sites :=
    (mem_cmp99ActiveCoarseRegion_sites_iff Omega b.1).mp hb.1
  have htarget : blockOf M N' (b.1.shift b.2) ⊆ Omega.sites :=
    (mem_cmp99ActiveCoarseRegion_sites_iff Omega (b.1.shift b.2)).mp hb.2
  have hblocks :
      blockOf M N' b.1 ∪ blockOf M N' (b.1.shift b.2) ⊆ Omega.sites :=
    Finset.union_subset hsource htarget
  unfold cmp99SourceUbarFineReadBonds at hq
  rw [Finset.mem_union] at hq
  rcases hq with hbase | hcontour
  · unfold cmp99PhysicalBondsOfEdgeList at hbase
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hbase
    have he' : e ∈
        (cmp99SourceParallelTransportPath (G := SUN Nc)
          (blockBasepoint M N' b.1) b.2).edges := by
      simpa [cmp99SourceUbarBaseEdgeList] using he
    have hbasepoint : blockBasepoint M N' b.1 ∈ blockOf M N' b.1 :=
      (mem_blockOf M N' b.1 (blockBasepoint M N' b.1)).2
        (blockSite_blockBasepoint M N' b.1)
    exact CMP99PhysicalBondEndpointsIn.mono
      (b := physicalBondOfEdge e) hblocks
      (cmp99SourceParallelTransportPath_endpointsIn_twoBlocks
        b.1 (blockBasepoint M N' b.1) b.2 hbasepoint e he')
  · obtain ⟨x, hx, hcontour⟩ := Finset.mem_biUnion.mp hcontour
    unfold cmp99PhysicalBondsOfEdgeList at hcontour
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hcontour
    have he' : e ∈ cmp99SourceUbarFineContourEdgeList
        (Nc := Nc) b x := by
      simpa using he
    unfold cmp99SourceUbarFineContourEdgeList at he'
    rcases List.mem_append.mp he' with hleft | hgamma3
    · rcases List.mem_append.mp hleft with hgamma1 | hgamma2
      · have hgamma1' : e ∈
          (cmp99BlockContainedContourSystem (G := SUN Nc) b.1 x).edges := by
          simpa [cmp99SourceUbarGamma1] using hgamma1
        exact CMP99PhysicalBondEndpointsIn.mono
          (b := physicalBondOfEdge e) hsource
          (physicalBondOfEdge_endpointsIn_of_staysIn
            (cmp99BlockContainedContourSystem_staysIn
              (G := SUN Nc) b.1 x hx) hgamma1')
      · have hgamma2' : e ∈
          (cmp99SourceParallelTransportPath (G := SUN Nc) x b.2).edges := by
          simpa [cmp99SourceUbarGamma2] using hgamma2
        exact CMP99PhysicalBondEndpointsIn.mono
          (b := physicalBondOfEdge e) hblocks
          (cmp99SourceParallelTransportPath_endpointsIn_twoBlocks
            b.1 x b.2 hx e hgamma2')
    · let hx' := cmp99SourceTranslatedSite_mem_targetBlock b.1 b.2 x hx
      have hgamma3' : e ∈
          ((concreteCMP99BlockContour (G := SUN Nc) (b.1.shift b.2)
            ⟨cmp99SourceTranslatedSite x b.2, hx'⟩).path.symm).edges := by
        simpa only [cmp99SourceUbarGamma3, dif_pos hx] using hgamma3
      have hstay :
          ((concreteCMP99BlockContour (G := SUN Nc) (b.1.shift b.2)
            ⟨cmp99SourceTranslatedSite x b.2, hx'⟩).path.symm).StaysIn
              (blockOf M N' (b.1.shift b.2)) :=
        OrientedLatticePath.StaysIn.symm
          (concreteCMP99BlockContour (G := SUN Nc) (b.1.shift b.2)
            ⟨cmp99SourceTranslatedSite x b.2, hx'⟩).staysInBlock
      exact CMP99PhysicalBondEndpointsIn.mono
        (b := physicalBondOfEdge e) htarget
        (physicalBondOfEdge_endpointsIn_of_staysIn hstay hgamma3')

/-- Family form of the one-bond Ubar endpoint theorem.  The premise is itself
orientation-safe: every selected coarse positive bond carries membership of
both its source and shifted target in the active coarse region. -/
theorem cmp99SourceUbarFineReadBondsOfCoarseBonds_endpointsIn
    (Omega : ActiveGaugeRegion d (M * N'))
    (coarseBonds : Finset (PhysicalBond d N'))
    (hcoarse : ∀ b ∈ coarseBonds,
      b.1 ∈ (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega).sites ∧
        b.1.shift b.2 ∈
          (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega).sites)
    (q : PhysicalBond d (M * N'))
    (hq : q ∈ cmp99SourceUbarFineReadBondsOfCoarseBonds
      (Nc := Nc) coarseBonds) :
    CMP99PhysicalBondEndpointsIn Omega.sites q := by
  unfold cmp99SourceUbarFineReadBondsOfCoarseBonds at hq
  obtain ⟨b, hb, hq⟩ := Finset.mem_biUnion.mp hq
  exact cmp99SourceUbarFineReadBonds_endpointsIn Omega b
    (hcoarse b hb) q hq

/-- Every fine positive coordinate read by the complete retained tower has
both endpoints in the head physical region.  The successor proof consumes the
tail induction hypothesis as the two-endpoint active-coarse certificate needed
by the exact selected-family Ubar pullback; no free carrier map or inclusion is
accepted. -/
theorem CMP99SourceActiveRegionChain.retainedFineReadBonds_endpointsIn
    {N depth : ℕ} {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth)
    (q : @PhysicalBond d N regions.neZero)
    (hq : q ∈ regions.retainedFineReadBonds (Nc := Nc)) :
    @CMP99PhysicalBondEndpointsIn d N regions.neZero Omega.sites q := by
  induction regions with
  | stop Omega =>
      simpa using hq
  | @step N' depth _ Omega hOmega tail ih =>
      rw [CMP99SourceActiveRegionChain.retainedFineReadBonds_step,
        Finset.mem_union] at hq
      rcases hq with haverage | hubar
      · exact cmp99SourceTransportedAverageFineReadBonds_endpointsIn
          Omega q haverage
      · exact cmp99SourceUbarFineReadBondsOfCoarseBonds_endpointsIn
          Omega (tail.retainedFineReadBonds (Nc := Nc))
          (fun b hb => ih b hb) q hubar

end

end YangMills.RG
