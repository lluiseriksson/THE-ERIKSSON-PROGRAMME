import YangMills.RG.BalabanCMP109Lemma1ResidualFamily
import YangMills.RG.BalabanCMP116Eq229ConnectedDomainSum
import YangMills.RG.BalabanCMP116Eq230TreeMetric

/-!
# Exact coarse-carrier regrouping of the CMP109 Lemma-1 residual

The literal CMP109 Lemma-1 expansion is indexed by connected domains of
order-two blocks on `FinBox 4 (M * (2 * Q))`.  CMP116 instead uses domains
of `M`-blocks, whose block lattice is `FinBox 4 (2 * Q)`.

This file performs the first exact part of that scale dictionary.  It maps
every native block through the literal block map `blockSite M (2 * Q)` and
regroups the Lemma-1 energy difference by the resulting finite block
carriers.  The target family is the image of `E.terms`, so it is independent
of the fluctuation field; coincident carriers are quotiented out by
`Finset.image`, and no arbitrary enumeration is supplied.

For the terminal contour ledger, however, quotienting coincident carriers is
unnecessary and quantitatively expensive.  Its domain index need not be
injective in `domainSupport`.  This file therefore also gives the canonical
enumeration of the *native* source domains, retaining the native tree metric
while assigning each index its literal coarsened support.  That is the
preferred terminal dictionary: no coarsification fiber is summed, hence no
additional entropy loss is introduced merely by changing supports.  It does
not make the native family free: every retained index still contributes to
the centered potential-rate sum, the equation-(2.26) domain product, and the
rooted residual sum.  Their common native-metric summability and the resulting
`volume_budget` remain quantitative obligations.

Honest scope: a coarsened support is still represented here as a
`Finset (FinBox 4 (2 * Q))`.  Proving that the image of every native
face-connected domain is again face-connected is the next geometric
obligation before these carriers can be packaged as
`CMP116LocalizationDomain M (2 * Q)`.  Consequently this module does not
claim the CMP116 metric comparison or equation-(1.36).  In particular,
the diagnostic coarse-carrier quotient below genuinely sums coincident
fibers and would therefore require an entropy estimate.  The preferred
native-indexed route does not perform that quotient: it retains every native
metric separately and leaves the resulting rooted-animal and domain-product
sums as explicit quantitative obligations.
-/

namespace YangMills.RG

noncomputable section

private abbrev Lemma1CoarseningNativeDomain (M Q : ℕ)
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))] :=
  CMP116LocalizationDomain 2 (M * (2 * Q))

/-- Literal `M`-block carrier of a native order-two Lemma-1 domain. -/
noncomputable def cmp109Lemma1CoarsenedBlocks
    {M Q : ℕ}
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))]
    (Y : Lemma1CoarseningNativeDomain M Q) :
    Finset (FinBox 4 (2 * Q)) :=
  Y.blocks.image (blockSite M (2 * Q))

/-- Coarsening cannot turn a source localization domain into the empty
carrier. -/
theorem cmp109Lemma1CoarsenedBlocks_nonempty
    {M Q : ℕ}
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))]
    (Y : Lemma1CoarseningNativeDomain M Q) :
    (cmp109Lemma1CoarsenedBlocks Y).Nonempty := by
  obtain ⟨block, hblock⟩ := Y.nonempty
  exact ⟨blockSite M (2 * Q) block,
    Finset.mem_image.mpr ⟨block, hblock, rfl⟩⟩

/-- Field-independent family of literal native Lemma-1 domains occurring in
one localized-action expansion.  Unlike the affected-domain family, this
does not depend on the fluctuation field. -/
noncomputable def cmp109Lemma1NativeDomainFamily
    {Index : Type*} {M Q Nc : ℕ}
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))]
    (E : CMP109LocalizedActionExpansion Index 2 (M * (2 * Q)) Nc) :
    Finset (Lemma1CoarseningNativeDomain M Q) :=
  E.terms.image E.domainOf

/-- The field-independent family of native block carriers.  The projection
from localization domains to their block carrier is injective by proof
irrelevance, so this image does not quotient distinct physical domains. -/
noncomputable def cmp109Lemma1NativeBlockFamily
    {Index : Type*} {M Q Nc : ℕ}
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))]
    (E : CMP109LocalizedActionExpansion Index 2 (M * (2 * Q)) Nc) :
    Finset (Finset (FinBox 4 (M * (2 * Q)))) :=
  (cmp109Lemma1NativeDomainFamily E).image fun Y => Y.blocks

/-- A localization domain is determined by its block carrier; its remaining
fields are propositions. -/
theorem cmp109Lemma1NativeDomain_blocks_injective
    {M Q : ℕ}
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))] :
    Function.Injective
      (fun Y : Lemma1CoarseningNativeDomain M Q => Y.blocks) := by
  intro Y Y' hblocks
  cases Y
  cases Y'
  simp_all

/-- Every carrier in the native block family is face-connected. -/
theorem cmp109Lemma1NativeBlockFamily_connected
    {Index : Type*} {M Q Nc : ℕ}
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))]
    (E : CMP109LocalizedActionExpansion Index 2 (M * (2 * Q)) Nc) :
    ∀ blocks ∈ cmp109Lemma1NativeBlockFamily E,
      walkConnected
        (cmp116CoarseFaceAdj 4 (M * (2 * Q))) blocks := by
  classical
  intro blocks hblocks
  obtain ⟨Y, _hY, rfl⟩ := Finset.mem_image.mp hblocks
  exact Y.connected

/-- Native connected-domain entropy seen from one coarse `M`-block.

The only coarsification cost is the exact `M⁴` cardinality of the fine block
fiber.  Distinct native domains remain distinct throughout the estimate. -/
theorem cmp109Lemma1NativeBlockFamily_coarsenedRoot_sum_pow_card_le
    {Index : Type*} {M Q Nc : ℕ}
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))]
    (E : CMP109LocalizedActionExpansion Index 2 (M * (2 * Q)) Nc)
    (root : FinBox 4 (2 * Q))
    (q : ℝ)
    (hq0 : 0 ≤ q)
    (hsmall : 64 * q < 1) :
    (∑ blocks ∈
        (cmp109Lemma1NativeBlockFamily E).filter fun blocks =>
          root ∈ blocks.image (blockSite M (2 * Q)),
        q ^ blocks.card) ≤
      (M : ℝ) ^ 4 * (1 - 64 * q)⁻¹ := by
  classical
  let family := cmp109Lemma1NativeBlockFamily E
  let rootedAt : FinBox 4 (M * (2 * Q)) →
      Finset (Finset (FinBox 4 (M * (2 * Q)))) :=
    fun nativeRoot => family.filter fun blocks => nativeRoot ∈ blocks
  let relevant :=
    family.filter fun blocks =>
      root ∈ blocks.image (blockSite M (2 * Q))
  have hpow_nonneg :
      ∀ blocks : Finset (FinBox 4 (M * (2 * Q))),
        0 ≤ q ^ blocks.card :=
    fun blocks => pow_nonneg hq0 _
  have hsub :
      relevant ⊆ (blockOf M (2 * Q) root).biUnion rootedAt := by
    intro blocks hblocks
    have hmem := Finset.mem_filter.mp hblocks
    obtain ⟨nativeRoot, hnBlocks, hnRoot⟩ :=
      Finset.mem_image.mp hmem.2
    rw [Finset.mem_biUnion]
    refine ⟨nativeRoot, ?_, ?_⟩
    · rw [mem_blockOf]
      exact hnRoot
    · rw [Finset.mem_filter]
      exact ⟨hmem.1, hnBlocks⟩
  have hsub_sum :
      (∑ blocks ∈ relevant, q ^ blocks.card) ≤
        ∑ blocks ∈ (blockOf M (2 * Q) root).biUnion rootedAt,
          q ^ blocks.card := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun blocks _ _ => hpow_nonneg blocks)
  have hbi :
      (∑ blocks ∈ (blockOf M (2 * Q) root).biUnion rootedAt,
          q ^ blocks.card) ≤
        ∑ nativeRoot ∈ blockOf M (2 * Q) root,
          ∑ blocks ∈ rootedAt nativeRoot, q ^ blocks.card := by
    exact sum_biUnion_le (blockOf M (2 * Q) root) rootedAt
      (fun blocks => q ^ blocks.card) hpow_nonneg
  have hroot :
      ∀ nativeRoot : FinBox 4 (M * (2 * Q)),
        (∑ blocks ∈ rootedAt nativeRoot, q ^ blocks.card) ≤
          (1 - 64 * q)⁻¹ := by
    intro nativeRoot
    have hrooted :=
      connectedDomainFamily_rooted_sum_pow_card_le
        family nativeRoot
        (cmp109Lemma1NativeBlockFamily_connected E)
        (cmp116CoarseFaceAdj_degree_le_eight (M * (2 * Q)))
        (by norm_num) hq0 (by
          convert hsmall using 1 <;> norm_num)
    norm_num at hrooted
    simpa [rootedAt] using hrooted
  calc
    (∑ blocks ∈
        (cmp109Lemma1NativeBlockFamily E).filter fun blocks =>
          root ∈ blocks.image (blockSite M (2 * Q)),
        q ^ blocks.card) =
        ∑ blocks ∈ relevant, q ^ blocks.card := by rfl
    _ ≤
        ∑ blocks ∈ (blockOf M (2 * Q) root).biUnion rootedAt,
          q ^ blocks.card := hsub_sum
    _ ≤
        ∑ nativeRoot ∈ blockOf M (2 * Q) root,
          ∑ blocks ∈ rootedAt nativeRoot, q ^ blocks.card := hbi
    _ ≤
        ∑ _nativeRoot ∈ blockOf M (2 * Q) root,
          (1 - 64 * q)⁻¹ := by
      exact Finset.sum_le_sum fun nativeRoot _hroot =>
        hroot nativeRoot
    _ =
        (M : ℝ) ^ 4 * (1 - 64 * q)⁻¹ := by
      rw [Finset.sum_const, nsmul_eq_mul, blockOf_card]
      norm_num

/-- The same rooted entropy estimate on the literal native localization
domains.  This is the form used to transport their native tree metrics. -/
theorem cmp109Lemma1NativeDomainFamily_coarsenedRoot_sum_pow_card_le
    {Index : Type*} {M Q Nc : ℕ}
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))]
    (E : CMP109LocalizedActionExpansion Index 2 (M * (2 * Q)) Nc)
    (root : FinBox 4 (2 * Q))
    (q : ℝ)
    (hq0 : 0 ≤ q)
    (hsmall : 64 * q < 1) :
    (∑ Y ∈
        (cmp109Lemma1NativeDomainFamily E).filter fun Y =>
          root ∈ cmp109Lemma1CoarsenedBlocks Y,
        q ^ Y.blocks.card) ≤
      (M : ℝ) ^ 4 * (1 - 64 * q)⁻¹ := by
  classical
  let relevant :=
    (cmp109Lemma1NativeDomainFamily E).filter fun Y =>
      root ∈ cmp109Lemma1CoarsenedBlocks Y
  have himage :
      relevant.image (fun Y => Y.blocks) =
        (cmp109Lemma1NativeBlockFamily E).filter fun blocks =>
          root ∈ blocks.image (blockSite M (2 * Q)) := by
    ext blocks
    constructor
    · intro hblocks
      obtain ⟨Y, hY, rfl⟩ := Finset.mem_image.mp hblocks
      have hYmem := Finset.mem_filter.mp hY
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_image.mpr ⟨Y, hYmem.1, rfl⟩, hYmem.2⟩
    · intro hblocks
      have hmem := Finset.mem_filter.mp hblocks
      obtain ⟨Y, hY, rfl⟩ := Finset.mem_image.mp hmem.1
      exact Finset.mem_image.mpr
        ⟨Y, Finset.mem_filter.mpr ⟨hY, hmem.2⟩, rfl⟩
  calc
    (∑ Y ∈
        (cmp109Lemma1NativeDomainFamily E).filter fun Y =>
          root ∈ cmp109Lemma1CoarsenedBlocks Y,
        q ^ Y.blocks.card) =
        ∑ Y ∈ relevant, q ^ Y.blocks.card := by rfl
    _ =
        ∑ blocks ∈ relevant.image (fun Y => Y.blocks),
          q ^ blocks.card := by
      rw [Finset.sum_image
        (cmp109Lemma1NativeDomain_blocks_injective
          (M := M) (Q := Q)).injOn]
    _ =
        ∑ blocks ∈
          (cmp109Lemma1NativeBlockFamily E).filter fun blocks =>
            root ∈ blocks.image (blockSite M (2 * Q)),
          q ^ blocks.card := by rw [himage]
    _ ≤ (M : ℝ) ^ 4 * (1 - 64 * q)⁻¹ :=
      cmp109Lemma1NativeBlockFamily_coarsenedRoot_sum_pow_card_le
        E root q hq0 hsmall

/-- The shifted source form of equation `(2.30)` converts native tree-metric
decay to block-cardinality decay without weakening the physical decay rate.
The singleton convention costs only the explicit factor `exp decay`. -/
theorem exp_neg_cmp109Lemma1NativeMetric_le_cardWeight
    {M Q : ℕ}
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))]
    (Y : Lemma1CoarseningNativeDomain M Q)
    (decay : ℝ)
    (hdecay : 0 ≤ decay) :
    Real.exp (-(decay * (cmp116CubeEdgeTreeMetric Y : ℝ))) ≤
      Real.exp decay *
        Real.exp (-(decay / 24)) ^ Y.blocks.card := by
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hmetric := cmp116LocalizationDomain_eq230_shifted Y
  have hscaled :
      decay * ((Y.blocks.card : ℝ) / 24) ≤
        decay * ((cmp116CubeEdgeTreeMetric Y : ℝ) + 1) :=
    mul_le_mul_of_nonneg_left hmetric hdecay
  nlinarith

/-- Uniform rooted sum of native tree-metric exponentials after only the
literal support coarsification. -/
theorem cmp109Lemma1NativeDomainFamily_coarsenedRoot_exp_metric_sum_le
    {Index : Type*} {M Q Nc : ℕ}
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))]
    (E : CMP109LocalizedActionExpansion Index 2 (M * (2 * Q)) Nc)
    (root : FinBox 4 (2 * Q))
    (decay : ℝ)
    (hdecay : 0 ≤ decay)
    (hsmall : 64 * Real.exp (-(decay / 24)) < 1) :
    (∑ Y ∈
        (cmp109Lemma1NativeDomainFamily E).filter fun Y =>
          root ∈ cmp109Lemma1CoarsenedBlocks Y,
        Real.exp
          (-(decay * (cmp116CubeEdgeTreeMetric Y : ℝ)))) ≤
      (M : ℝ) ^ 4 * Real.exp decay *
        (1 - 64 * Real.exp (-(decay / 24)))⁻¹ := by
  let q : ℝ := Real.exp (-(decay / 24))
  let relevant :=
    (cmp109Lemma1NativeDomainFamily E).filter fun Y =>
      root ∈ cmp109Lemma1CoarsenedBlocks Y
  have hq0 : 0 ≤ q := Real.exp_nonneg _
  have hpoint :
      ∀ Y ∈ relevant,
        Real.exp
            (-(decay * (cmp116CubeEdgeTreeMetric Y : ℝ))) ≤
          Real.exp decay * q ^ Y.blocks.card := by
    intro Y _hY
    simpa [q] using
      exp_neg_cmp109Lemma1NativeMetric_le_cardWeight Y decay hdecay
  have hcard :=
    cmp109Lemma1NativeDomainFamily_coarsenedRoot_sum_pow_card_le
      E root q hq0 (by simpa [q] using hsmall)
  calc
    (∑ Y ∈
        (cmp109Lemma1NativeDomainFamily E).filter fun Y =>
          root ∈ cmp109Lemma1CoarsenedBlocks Y,
        Real.exp
          (-(decay * (cmp116CubeEdgeTreeMetric Y : ℝ)))) =
        ∑ Y ∈ relevant,
          Real.exp
            (-(decay * (cmp116CubeEdgeTreeMetric Y : ℝ))) := by rfl
    _ ≤ ∑ Y ∈ relevant,
        Real.exp decay * q ^ Y.blocks.card := by
      exact Finset.sum_le_sum fun Y hY => hpoint Y hY
    _ =
        Real.exp decay *
          (∑ Y ∈ relevant, q ^ Y.blocks.card) := by
      rw [Finset.mul_sum]
    _ ≤
        Real.exp decay *
          ((M : ℝ) ^ 4 * (1 - 64 * q)⁻¹) :=
      mul_le_mul_of_nonneg_left hcard (Real.exp_nonneg _)
    _ =
        (M : ℝ) ^ 4 * Real.exp decay *
          (1 - 64 * Real.exp (-(decay / 24)))⁻¹ := by
      simp only [q]
      ring

/-- Amplitude-weighted form of the native rooted metric sum. -/
theorem cmp109Lemma1NativeDomainFamily_coarsenedRoot_weighted_exp_metric_sum_le
    {Index : Type*} {M Q Nc : ℕ}
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))]
    (E : CMP109LocalizedActionExpansion Index 2 (M * (2 * Q)) Nc)
    (root : FinBox 4 (2 * Q))
    (amplitude decay : ℝ)
    (hamplitude : 0 ≤ amplitude)
    (hdecay : 0 ≤ decay)
    (hsmall : 64 * Real.exp (-(decay / 24)) < 1) :
    (∑ Y ∈
        (cmp109Lemma1NativeDomainFamily E).filter fun Y =>
          root ∈ cmp109Lemma1CoarsenedBlocks Y,
        amplitude *
          Real.exp
            (-(decay * (cmp116CubeEdgeTreeMetric Y : ℝ)))) ≤
      amplitude * (M : ℝ) ^ 4 * Real.exp decay *
        (1 - 64 * Real.exp (-(decay / 24)))⁻¹ := by
  have hsum :=
    cmp109Lemma1NativeDomainFamily_coarsenedRoot_exp_metric_sum_le
      E root decay hdecay hsmall
  calc
    (∑ Y ∈
        (cmp109Lemma1NativeDomainFamily E).filter fun Y =>
          root ∈ cmp109Lemma1CoarsenedBlocks Y,
        amplitude *
          Real.exp
            (-(decay * (cmp116CubeEdgeTreeMetric Y : ℝ)))) =
        amplitude *
          (∑ Y ∈
            (cmp109Lemma1NativeDomainFamily E).filter fun Y =>
              root ∈ cmp109Lemma1CoarsenedBlocks Y,
            Real.exp
              (-(decay * (cmp116CubeEdgeTreeMetric Y : ℝ)))) := by
      rw [Finset.mul_sum]
    _ ≤
        amplitude *
          ((M : ℝ) ^ 4 * Real.exp decay *
            (1 - 64 * Real.exp (-(decay / 24)))⁻¹) :=
      mul_le_mul_of_nonneg_left hsum hamplitude
    _ =
        amplitude * (M : ℝ) ^ 4 * Real.exp decay *
          (1 - 64 * Real.exp (-(decay / 24)))⁻¹ := by ring

/-- Canonical number of native Lemma-1 domains in the source expansion. -/
abbrev CMP109Lemma1NativeDomainCount
    {Index : Type*} {M Q Nc : ℕ}
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))]
    (E : CMP109LocalizedActionExpansion Index 2 (M * (2 * Q)) Nc) : ℕ :=
  (cmp109Lemma1NativeDomainFamily E).card

/-- Canonical enumeration of the literal native Lemma-1 domains. -/
noncomputable def cmp109Lemma1NativeDomainAt
    {Index : Type*} {M Q Nc : ℕ}
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))]
    (E : CMP109LocalizedActionExpansion Index 2 (M * (2 * Q)) Nc)
    (i : Fin (CMP109Lemma1NativeDomainCount E)) :
    Lemma1CoarseningNativeDomain M Q :=
  ((cmp109Lemma1NativeDomainFamily E).equivFin.symm i).1

/-- Every canonical native index denotes a domain produced by `E`. -/
theorem cmp109Lemma1NativeDomainAt_mem
    {Index : Type*} {M Q Nc : ℕ}
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))]
    (E : CMP109LocalizedActionExpansion Index 2 (M * (2 * Q)) Nc)
    (i : Fin (CMP109Lemma1NativeDomainCount E)) :
    cmp109Lemma1NativeDomainAt E i ∈ cmp109Lemma1NativeDomainFamily E :=
  ((cmp109Lemma1NativeDomainFamily E).equivFin.symm i).2

/-- The canonical native enumeration has no repeated native domains. -/
theorem cmp109Lemma1NativeDomainAt_injective
    {Index : Type*} {M Q Nc : ℕ}
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))]
    (E : CMP109LocalizedActionExpansion Index 2 (M * (2 * Q)) Nc) :
    Function.Injective (cmp109Lemma1NativeDomainAt E) := by
  intro i j hij
  apply (cmp109Lemma1NativeDomainFamily E).equivFin.symm.injective
  exact Subtype.ext hij

/-- The range of the canonical native enumeration is exactly the
field-independent source family. -/
theorem image_cmp109Lemma1NativeDomainAt_univ
    {Index : Type*} {M Q Nc : ℕ}
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))]
    (E : CMP109LocalizedActionExpansion Index 2 (M * (2 * Q)) Nc) :
    Finset.image (cmp109Lemma1NativeDomainAt E) Finset.univ =
      cmp109Lemma1NativeDomainFamily E := by
  classical
  ext Y
  constructor
  · intro hY
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hY
    exact cmp109Lemma1NativeDomainAt_mem E i
  · intro hY
    let Ysub : ↥(cmp109Lemma1NativeDomainFamily E) := ⟨Y, hY⟩
    apply Finset.mem_image.mpr
    refine ⟨(cmp109Lemma1NativeDomainFamily E).equivFin Ysub,
      Finset.mem_univ _, ?_⟩
    exact congrArg Subtype.val
      ((cmp109Lemma1NativeDomainFamily E).equivFin.symm_apply_apply Ysub)

/-- Canonical enumeration preserves every finite sum over the native domain
family. -/
theorem sum_cmp109Lemma1NativeDomainAt_eq_sum_nativeDomainFamily
    {Index : Type*} {M Q Nc : ℕ}
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))]
    (E : CMP109LocalizedActionExpansion Index 2 (M * (2 * Q)) Nc)
    (f : Lemma1CoarseningNativeDomain M Q → ℝ) :
    (∑ i : Fin (CMP109Lemma1NativeDomainCount E),
        f (cmp109Lemma1NativeDomainAt E i)) =
      ∑ Y ∈ cmp109Lemma1NativeDomainFamily E, f Y := by
  classical
  rw [← image_cmp109Lemma1NativeDomainAt_univ E]
  rw [Finset.sum_image (cmp109Lemma1NativeDomainAt_injective E).injOn]

/-- Literal native tree metric retained by the terminal dictionary. -/
noncomputable def cmp109Lemma1NativeIndexedDomainMetric
    {Index : Type*} {M Q Nc : ℕ}
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))]
    (E : CMP109LocalizedActionExpansion Index 2 (M * (2 * Q)) Nc)
    (i : Fin (CMP109Lemma1NativeDomainCount E)) : ℕ :=
  cmp116CubeEdgeTreeMetric (cmp109Lemma1NativeDomainAt E i)

/-- Literal native block cardinality retained by the terminal dictionary. -/
noncomputable def cmp109Lemma1NativeIndexedDomainCard
    {Index : Type*} {M Q Nc : ℕ}
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))]
    (E : CMP109LocalizedActionExpansion Index 2 (M * (2 * Q)) Nc)
    (i : Fin (CMP109Lemma1NativeDomainCount E)) : ℕ :=
  (cmp109Lemma1NativeDomainAt E i).blocks.card

/-- Coarsened physical support of one native index.  Different native indices
may have the same support; they remain distinct in the terminal ledger. -/
noncomputable def cmp109Lemma1NativeIndexedDomainSupport
    {Index : Type*} {M Q Nc : ℕ}
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))]
    (E : CMP109LocalizedActionExpansion Index 2 (M * (2 * Q)) Nc)
    (i : Fin (CMP109Lemma1NativeDomainCount E)) :
    Finset (FinBox 4 (2 * Q)) :=
  cmp109Lemma1CoarsenedBlocks (cmp109Lemma1NativeDomainAt E i)

/-- Every coarsened support in the native enumeration is nonempty. -/
theorem cmp109Lemma1NativeIndexedDomainSupport_nonempty
    {Index : Type*} {M Q Nc : ℕ}
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))]
    (E : CMP109LocalizedActionExpansion Index 2 (M * (2 * Q)) Nc)
    (i : Fin (CMP109Lemma1NativeDomainCount E)) :
    (cmp109Lemma1NativeIndexedDomainSupport E i).Nonempty :=
  cmp109Lemma1CoarsenedBlocks_nonempty (cmp109Lemma1NativeDomainAt E i)

/-- Exact reindexing after selecting native domains whose coarsified support
contains one coarse root. -/
theorem sum_cmp109Lemma1NativeDomainAt_filter_support_eq
    {Index : Type*} {M Q Nc : ℕ}
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))]
    (E : CMP109LocalizedActionExpansion Index 2 (M * (2 * Q)) Nc)
    (root : FinBox 4 (2 * Q))
    (f : Lemma1CoarseningNativeDomain M Q → ℝ) :
    (∑ i ∈ (Finset.univ.filter fun i :
          Fin (CMP109Lemma1NativeDomainCount E) =>
        root ∈ cmp109Lemma1NativeIndexedDomainSupport E i),
        f (cmp109Lemma1NativeDomainAt E i)) =
      ∑ Y ∈
          (cmp109Lemma1NativeDomainFamily E).filter fun Y =>
            root ∈ cmp109Lemma1CoarsenedBlocks Y,
        f Y := by
  classical
  rw [Finset.sum_filter, Finset.sum_filter]
  simpa [cmp109Lemma1NativeIndexedDomainSupport] using
    sum_cmp109Lemma1NativeDomainAt_eq_sum_nativeDomainFamily
      E (fun Y =>
        if root ∈ cmp109Lemma1CoarsenedBlocks Y then f Y else 0)

/-- The field-independent finite family of actual coarsened carriers in one
CMP109 localized-action expansion. -/
noncomputable def cmp109Lemma1CoarsenedBlockFamily
    {Index : Type*} {M Q Nc : ℕ}
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))]
    (E : CMP109LocalizedActionExpansion Index 2 (M * (2 * Q)) Nc) :
    Finset (Finset (FinBox 4 (2 * Q))) :=
  E.terms.image fun i =>
    cmp109Lemma1CoarsenedBlocks (E.domainOf i)

/-- Lemma-1 residual attached to one actual coarsened block carrier.  The
fiber is taken inside the canonical affected-term set, but the ambient
carrier family itself is independent of the field. -/
noncomputable def cmp109Eq212Lemma1CoarsenedResidualActivity
    {Index : Type*} {M Q Nc : ℕ}
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))] [NeZero Nc]
    (E : CMP109LocalizedActionExpansion Index 2 (M * (2 * Q)) Nc)
    (V : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    (gk : ℝ)
    (B : FinePhysicalOneCochain 4 M (2 * Q) Nc)
    (D : CoarsePhysicalOneCochain 4 (2 * Q) Nc)
    (target : Finset (FinBox 4 (2 * Q))) : ℝ :=
  by
    classical
    exact
      ∑ i ∈
        (E.affectedDomains
          (CMP109LocalizedActionExpansion.changedPositiveBonds
            (cmp109Eq212PerturbedFineBackground V gk B D)
            (cmp109Eq212BaseFineBackground V))).filter
              (fun i =>
                cmp109Lemma1CoarsenedBlocks (E.domainOf i) = target),
        cmp109Eq212Lemma1LocalizedDifference E V gk B D i

/-- Exact source regrouping over the field-independent family of native
domains.  Keeping this family unquotiented is the route used by the terminal
dictionary; coarsened supports may coincide without summing their residuals
or weakening their native metrics. -/
theorem cmp109Eq212Lemma1EnergyDifference_eq_sum_nativeResidualActivity
    {Index : Type*} {M Q Nc : ℕ}
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))] [NeZero Nc]
    (E : CMP109LocalizedActionExpansion Index 2 (M * (2 * Q)) Nc)
    (V : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    (gk : ℝ)
    (B : FinePhysicalOneCochain 4 M (2 * Q) Nc)
    (D : CoarsePhysicalOneCochain 4 (2 * Q) Nc) :
    cmp109Eq212Lemma1EnergyDifference E V gk B D =
      ∑ Y ∈ cmp109Lemma1NativeDomainFamily E,
        cmp109Eq212Lemma1ResidualActivity E V gk B D Y := by
  classical
  rw [cmp109Eq212Lemma1EnergyDifference_eq_sum_changed]
  unfold cmp109Lemma1NativeDomainFamily
    cmp109Eq212Lemma1ResidualActivity
    cmp109Eq212Lemma1LocalizedDifference
  exact
    (Finset.sum_fiberwise_of_maps_to
      (fun i hi =>
        Finset.mem_image.mpr
          ⟨i, (Finset.mem_filter.mp hi).1, rfl⟩)
      (fun i =>
        (E.activity i).globalEval
            (CMP109LocalizedActionExpansion.positiveBondField
              (cmp109Eq212PerturbedFineBackground V gk B D)) -
          (E.activity i).globalEval
            (CMP109LocalizedActionExpansion.positiveBondField
              (cmp109Eq212BaseFineBackground V)))).symm

/-- Exact `Fin`-indexed form consumed by the terminal contour record.  The
indexing is canonical and keeps distinct native domains distinct even when
their coarsened supports coincide. -/
theorem cmp109Eq212Lemma1EnergyDifference_eq_sum_indexedNativeResidualActivity
    {Index : Type*} {M Q Nc : ℕ}
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))] [NeZero Nc]
    (E : CMP109LocalizedActionExpansion Index 2 (M * (2 * Q)) Nc)
    (V : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    (gk : ℝ)
    (B : FinePhysicalOneCochain 4 M (2 * Q) Nc)
    (D : CoarsePhysicalOneCochain 4 (2 * Q) Nc) :
    cmp109Eq212Lemma1EnergyDifference E V gk B D =
      ∑ i : Fin (CMP109Lemma1NativeDomainCount E),
        cmp109Eq212Lemma1ResidualActivity E V gk B D
          (cmp109Lemma1NativeDomainAt E i) := by
  classical
  rw [cmp109Eq212Lemma1EnergyDifference_eq_sum_nativeResidualActivity]
  rw [← image_cmp109Lemma1NativeDomainAt_univ E]
  rw [Finset.sum_image (cmp109Lemma1NativeDomainAt_injective E).injOn]

/-- Exact two-stage regrouping of the physical CMP109 Lemma-1 energy
difference by its actual coarsened carriers.

No target-domain assignment is an input: the family and every fiber are
derived from `E.domainOf`. -/
theorem cmp109Eq212Lemma1EnergyDifference_eq_sum_coarsenedResidualActivity
    {Index : Type*} {M Q Nc : ℕ}
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))] [NeZero Nc]
    (E : CMP109LocalizedActionExpansion Index 2 (M * (2 * Q)) Nc)
    (V : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    (gk : ℝ)
    (B : FinePhysicalOneCochain 4 M (2 * Q) Nc)
    (D : CoarsePhysicalOneCochain 4 (2 * Q) Nc) :
    cmp109Eq212Lemma1EnergyDifference E V gk B D =
      ∑ target ∈ cmp109Lemma1CoarsenedBlockFamily E,
        cmp109Eq212Lemma1CoarsenedResidualActivity
          E V gk B D target := by
  classical
  rw [cmp109Eq212Lemma1EnergyDifference_eq_sum_changed]
  unfold cmp109Lemma1CoarsenedBlockFamily
    cmp109Eq212Lemma1CoarsenedResidualActivity
    cmp109Eq212Lemma1LocalizedDifference
  exact
    (Finset.sum_fiberwise_of_maps_to
      (fun i hi =>
        Finset.mem_image.mpr
          ⟨i, (Finset.mem_filter.mp hi).1, rfl⟩)
      (fun i =>
        (E.activity i).globalEval
            (CMP109LocalizedActionExpansion.positiveBondField
              (cmp109Eq212PerturbedFineBackground V gk B D)) -
          (E.activity i).globalEval
            (CMP109LocalizedActionExpansion.positiveBondField
              (cmp109Eq212BaseFineBackground V)))).symm

end

end YangMills.RG
