/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceCoarseCovariance

/-!
# A region-dependent CMP99 transported block average

Printed CMP99 (3.18)--(3.19) does not map a regional fine field into a
global coarse field space.  Its target is the active coarse stratum, and the
kernel at a coarse site `y` is a normalized sum over the complete block
`B^j(y)`, with parallel transport along the printed contour.

This file fixes the corresponding type-level issue at one effective scale.
It defines active coarse sites by **complete block containment**, separates a
physical fine boundary from its canonical block-saturated operator domain,
and constructs the transported block kernel and its explicit synthesis map.
Their composition is calculated exactly; with scalar weight `w` and
four-dimensional blocks of side `M`, the normalization is

`Q_r S_r = (w^2 M^4) I`.

Honest scope: the transports are supplied as real-linear isometries.  The
file does not yet construct them from `U(Gamma^(j)_{y,x})`, does not build the
recursive composition over the averaged backgrounds, and does not identify
the several scale-dependent strata with the one-scale p. 408 region type.
The scalar is deliberately not set to one: the current `PiLp 2` fields use
unweighted counting norms, whereas the printed Hilbert spaces carry lattice
spacing weights.
-/

namespace YangMills.RG

open scoped RealInnerProductSpace

noncomputable section

variable {d M N' : ℕ} [NeZero M] [NeZero N']

/-- A coarse site is regionally active exactly when its *whole* fine block is
active.  Nonempty intersection would include boundary-straddling blocks and
would make the exact normalization false. -/
def cmp99ActiveCoarseRegion
    (Ω : ActiveGaugeRegion d (M * N')) : ActiveGaugeRegion d N' where
  sites := Finset.univ.filter fun y => blockOf M N' y ⊆ Ω.sites

omit [NeZero N'] in
@[simp] theorem mem_cmp99ActiveCoarseRegion_sites_iff
    (Ω : ActiveGaugeRegion d (M * N')) (y : FinBox d N') :
    y ∈ (cmp99ActiveCoarseRegion (M := M) (N' := N') Ω).sites ↔
      blockOf M N' y ⊆ Ω.sites := by
  simp [cmp99ActiveCoarseRegion]

/-- Every active fine site brings its complete order-`M` block with it. -/
def ActiveGaugeRegion.BlockSaturated
    (Ω : ActiveGaugeRegion d (M * N')) : Prop :=
  ∀ x ∈ Ω.sites, blockOf M N' (blockSite M N' x) ⊆ Ω.sites

/-- Canonical fine realization of a coarse active region: a fine site is
active exactly when its complete order-`M` owner block is indexed by an
active coarse site.  This is the scale realization used implicitly when the
same CMP99 source domain is viewed before and after one averaging step. -/
noncomputable def cmp99LiftActiveRegion
    (OmegaCoarse : ActiveGaugeRegion d N') :
    ActiveGaugeRegion d (M * N') where
  sites := cmp116RegionSites (M := M) (N' := N') OmegaCoarse.sites

omit [NeZero N'] in
@[simp] theorem mem_cmp99LiftActiveRegion_sites_iff
    (OmegaCoarse : ActiveGaugeRegion d N')
    (x : FinBox d (M * N')) :
    x ∈ (cmp99LiftActiveRegion (M := M) OmegaCoarse).sites ↔
      blockSite M N' x ∈ OmegaCoarse.sites := by
  exact mem_cmp116RegionSites_iff

omit [NeZero N'] in
/-- Every canonical fine realization is block-saturated. -/
theorem cmp99LiftActiveRegion_blockSaturated
    (OmegaCoarse : ActiveGaugeRegion d N') :
    (cmp99LiftActiveRegion (M := M) OmegaCoarse).BlockSaturated := by
  intro x hx z hz
  rw [mem_cmp99LiftActiveRegion_sites_iff] at hx ⊢
  have hzx : blockSite M N' z = blockSite M N' x :=
    (mem_blockOf M N' (blockSite M N' x) z).mp hz
  simpa [hzx] using hx

omit [NeZero N'] in
/-- Coarsening the canonical fine realization recovers the original active
region as an equality of the dependent region objects, not merely as a
cardinality or membership equivalence. -/
theorem cmp99ActiveCoarseRegion_lift_eq
    (OmegaCoarse : ActiveGaugeRegion d N') :
    cmp99ActiveCoarseRegion (M := M) (N' := N')
        (cmp99LiftActiveRegion (M := M) OmegaCoarse) =
      OmegaCoarse := by
  cases OmegaCoarse with
  | mk sites =>
      apply congrArg ActiveGaugeRegion.mk
      ext y
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hy
        obtain ⟨x, hx⟩ := blockSite_surjective (d := d) M N' y
        have hmem : x ∈ blockOf M N' y :=
          (mem_blockOf M N' y x).2 hx
        have hactive := hy hmem
        simpa [mem_cmp99LiftActiveRegion_sites_iff, hx] using hactive
      · intro hy x hx
        rw [mem_cmp99LiftActiveRegion_sites_iff]
        exact (mem_blockOf M N' y x).mp hx ▸ hy

/-- Canonical complete-block interior realization of a physical fine region.

The local domains on CMP99 printed p. 408 are specified by physical
distances on the fine lattice.  They therefore need not themselves be unions
of complete order-`M` averaging blocks.  The regional average acts on the
largest canonical union of complete blocks contained in the physical region:
first retain the coarse sites whose full blocks are contained in `Omega`, then
lift those sites back to the fine lattice.  This keeps the physical boundary
separate from the block-saturated operator domain. -/
noncomputable def cmp99BlockInteriorActiveRegion
    (Omega : ActiveGaugeRegion d (M * N')) :
    ActiveGaugeRegion d (M * N') :=
  cmp99LiftActiveRegion (M := M)
    (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega)

omit [NeZero N'] in
@[simp] theorem mem_cmp99BlockInteriorActiveRegion_sites_iff
    (Omega : ActiveGaugeRegion d (M * N'))
    (x : FinBox d (M * N')) :
    x ∈ (cmp99BlockInteriorActiveRegion (M := M) (N' := N') Omega).sites ↔
      blockOf M N' (blockSite M N' x) ⊆ Omega.sites := by
  rw [cmp99BlockInteriorActiveRegion,
    mem_cmp99LiftActiveRegion_sites_iff,
    mem_cmp99ActiveCoarseRegion_sites_iff]

omit [NeZero N'] in
/-- The complete-block realization never enlarges the physical region. -/
theorem cmp99BlockInteriorActiveRegion_subset
    (Omega : ActiveGaugeRegion d (M * N')) :
    (cmp99BlockInteriorActiveRegion (M := M) (N' := N') Omega).sites ⊆
      Omega.sites := by
  intro x hx
  rw [mem_cmp99BlockInteriorActiveRegion_sites_iff] at hx
  exact hx ((mem_blockOf M N' (blockSite M N' x) x).2 rfl)

omit [NeZero N'] in
/-- The canonical realization is block-saturated by construction, without a
block-saturation hypothesis on the physical source domain. -/
theorem cmp99BlockInteriorActiveRegion_blockSaturated
    (Omega : ActiveGaugeRegion d (M * N')) :
    (cmp99BlockInteriorActiveRegion (M := M) (N' := N') Omega).BlockSaturated :=
  cmp99LiftActiveRegion_blockSaturated
    (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega)

omit [NeZero N'] in
/-- Coarsening the canonical realization returns exactly the complete blocks
selected from the original physical region. -/
theorem cmp99ActiveCoarseRegion_blockInterior_eq
    (Omega : ActiveGaugeRegion d (M * N')) :
    cmp99ActiveCoarseRegion (M := M) (N' := N')
        (cmp99BlockInteriorActiveRegion (M := M) (N' := N') Omega) =
      cmp99ActiveCoarseRegion (M := M) (N' := N') Omega := by
  exact cmp99ActiveCoarseRegion_lift_eq
    (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega)

omit [NeZero N'] in
/-- If a region was already a union of complete averaging blocks, taking its
canonical block interior changes nothing. -/
theorem cmp99BlockInteriorActiveRegion_eq_of_blockSaturated
    (Omega : ActiveGaugeRegion d (M * N'))
    (hOmega : Omega.BlockSaturated) :
    cmp99BlockInteriorActiveRegion (M := M) (N' := N') Omega = Omega := by
  cases Omega with
  | mk sites =>
      apply congrArg ActiveGaugeRegion.mk
      ext x
      rw [mem_cmp116RegionSites_iff,
        mem_cmp99ActiveCoarseRegion_sites_iff]
      constructor
      · intro hx
        exact hx ((mem_blockOf M N' (blockSite M N' x) x).2 rfl)
      · intro hx
        exact hOmega x hx

variable {Q j : ℕ} [NeZero Q]
variable {cell : FinBox 4 Q}

/-- The coarse-carrier realization of a p. 408 region is lifted through
complete side-`M` blocks and is therefore block-saturated on the fine
lattice.  This does not assert that the original physical boundary, specified
at the `R₀M₀` resolution, is itself aligned with order-`M` blocks. -/
theorem cmp99OmegaActiveGaugeRegion_blockSaturated
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 2)) :
    (cmp99OmegaActiveGaugeRegion (M := M) Seq r).BlockSaturated := by
  intro x hx z hz
  rw [mem_cmp99OmegaActiveGaugeRegion_sites_iff] at hx ⊢
  have hzx : blockSite M (2 * Q) z = blockSite M (2 * Q) x :=
    (mem_blockOf M (2 * Q) (blockSite M (2 * Q) x) z).mp hz
  simpa [hzx] using hx

/-- For a literal CMP99 region, complete-containment indexing recovers
exactly the source region on the coarse block lattice. -/
theorem cmp99OmegaActiveCoarseRegion_sites_eq
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 2)) :
    (cmp99ActiveCoarseRegion (M := M) (N' := 2 * Q)
      (cmp99OmegaActiveGaugeRegion (M := M) Seq r)).sites =
        Seq.regions r := by
  ext y
  rw [mem_cmp99ActiveCoarseRegion_sites_iff]
  constructor
  · intro hy
    obtain ⟨x, hx⟩ := blockSite_surjective (d := 4) M (2 * Q) y
    have hmem : x ∈ blockOf M (2 * Q) y :=
      (mem_blockOf M (2 * Q) y x).2 hx
    have hactive := hy hmem
    rw [mem_cmp99OmegaActiveGaugeRegion_sites_iff, hx] at hactive
    exact hactive
  · intro hy x hx
    rw [mem_cmp99OmegaActiveGaugeRegion_sites_iff]
    exact (mem_blockOf M (2 * Q) y x).mp hx ▸ hy

/-- The actual regional coarse zero-field target. -/
abbrev CMP99OmegaRegionalCoarseField
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 2))
    (g : Type*) :=
  ActiveGaugeZeroCochain
    (cmp99ActiveCoarseRegion (M := M) (N' := 2 * Q)
      (cmp99OmegaActiveGaugeRegion (M := M) Seq r)) g

section TransportedKernel

variable {g : Type*}
variable [NormedAddCommGroup g] [InnerProductSpace ℝ g]
variable [FiniteDimensional ℝ g]

/-- A fine site in the complete block of an active coarse site, regarded as
an active fine site.  Keeping the membership proof in the subtype avoids
fragile proof extraction inside finite sums. -/
def cmp99ActiveFineSiteOfBlock
    (Ω : ActiveGaugeRegion d (M * N'))
    (y : ActiveGaugeRegion.Site
      (cmp99ActiveCoarseRegion (M := M) (N' := N') Ω))
    (x : {x : FinBox d (M * N') // x ∈ blockOf M N' y.1}) :
    ActiveGaugeRegion.Site Ω :=
  ⟨x.1,
    (mem_cmp99ActiveCoarseRegion_sites_iff
      (M := M) (N' := N') Ω y.1).mp y.2 x.2⟩

omit [NeZero N'] in
@[simp] theorem cmp99ActiveFineSiteOfBlock_val
    (Ω : ActiveGaugeRegion d (M * N'))
    (y : ActiveGaugeRegion.Site
      (cmp99ActiveCoarseRegion (M := M) (N' := N') Ω))
    (x : {x : FinBox d (M * N') // x ∈ blockOf M N' y.1}) :
    (cmp99ActiveFineSiteOfBlock Ω y x).1 = x.1 := rfl

omit [NeZero N'] in
@[simp] theorem blockSite_cmp99ActiveFineSiteOfBlock
    (Ω : ActiveGaugeRegion d (M * N'))
    (y : ActiveGaugeRegion.Site
      (cmp99ActiveCoarseRegion (M := M) (N' := N') Ω))
    (x : {x : FinBox d (M * N') // x ∈ blockOf M N' y.1}) :
    blockSite M N' (cmp99ActiveFineSiteOfBlock Ω y x).1 = y.1 :=
  (mem_blockOf M N' y.1 x.1).mp x.2

/-- The single-scale transported kernel of CMP99 (3.19), restricted to
coarse blocks wholly contained in the fine region.  The isometries represent
the adjoint action of the contour holonomies; their source construction is a
separate obligation. -/
noncomputable def cmp99TransportedBlockAverageCLM
    (Ω : ActiveGaugeRegion d (M * N')) (w : ℝ)
    (transport : FinBox d N' → FinBox d (M * N') → (g ≃ₗᵢ[ℝ] g)) :
    ActiveGaugeZeroCochain Ω g →L[ℝ]
      ActiveGaugeZeroCochain
        (cmp99ActiveCoarseRegion (M := M) (N' := N') Ω) g :=
  LinearMap.toContinuousLinearMap
    { toFun := fun phi =>
        WithLp.toLp 2 fun y =>
          w • ∑ x : {x : FinBox d (M * N') // x ∈ blockOf M N' y.1},
            transport y.1 x.1 (phi (cmp99ActiveFineSiteOfBlock Ω y x))
      map_add' := fun phi psi => by
        ext y
        simp only [PiLp.add_apply, map_add, Finset.sum_add_distrib, smul_add]
      map_smul' := fun a phi => by
        ext y
        simp only [PiLp.smul_apply, map_smul, Finset.smul_sum,
          RingHom.id_apply]
        apply Finset.sum_congr rfl
        intro x _
        simp only [smul_smul]
        rw [mul_comm w a] }

@[simp] theorem cmp99TransportedBlockAverageCLM_apply
    (Ω : ActiveGaugeRegion d (M * N')) (w : ℝ)
    (transport : FinBox d N' → FinBox d (M * N') → (g ≃ₗᵢ[ℝ] g))
    (phi : ActiveGaugeZeroCochain Ω g)
    (y : ActiveGaugeRegion.Site
      (cmp99ActiveCoarseRegion (M := M) (N' := N') Ω)) :
    cmp99TransportedBlockAverageCLM Ω w transport phi y =
      w • ∑ x : {x : FinBox d (M * N') // x ∈ blockOf M N' y.1},
        transport y.1 x.1 (phi (cmp99ActiveFineSiteOfBlock Ω y x)) := by
  rfl

/-- Explicit synthesis associated with the transported average.  Saturation
ensures that the owner block of every active fine site is an active coarse
site. -/
noncomputable def cmp99TransportedBlockSynthesisCLM
    (Ω : ActiveGaugeRegion d (M * N')) (hΩ : Ω.BlockSaturated)
    (w : ℝ)
    (transport : FinBox d N' → FinBox d (M * N') → (g ≃ₗᵢ[ℝ] g)) :
    ActiveGaugeZeroCochain
        (cmp99ActiveCoarseRegion (M := M) (N' := N') Ω) g →L[ℝ]
      ActiveGaugeZeroCochain Ω g :=
  LinearMap.toContinuousLinearMap
    { toFun := fun eta =>
        WithLp.toLp 2 fun x =>
          w • (transport (blockSite M N' x.1) x.1).symm
            (eta ⟨blockSite M N' x.1,
              (mem_cmp99ActiveCoarseRegion_sites_iff
                (M := M) (N' := N') Ω (blockSite M N' x.1)).2
                  (hΩ x.1 x.2)⟩)
      map_add' := fun eta theta => by
        ext x
        simp [smul_add]
      map_smul' := fun a eta => by
        ext x
        simp only [PiLp.smul_apply, map_smul, smul_smul,
          RingHom.id_apply]
        rw [mul_comm w a] }

@[simp] theorem cmp99TransportedBlockSynthesisCLM_apply
    (Ω : ActiveGaugeRegion d (M * N')) (hΩ : Ω.BlockSaturated)
    (w : ℝ)
    (transport : FinBox d N' → FinBox d (M * N') → (g ≃ₗᵢ[ℝ] g))
    (eta : ActiveGaugeZeroCochain
      (cmp99ActiveCoarseRegion (M := M) (N' := N') Ω) g)
    (x : ActiveGaugeRegion.Site Ω) :
    cmp99TransportedBlockSynthesisCLM Ω hΩ w transport eta x =
      w • (transport (blockSite M N' x.1) x.1).symm
        (eta ⟨blockSite M N' x.1,
          (mem_cmp99ActiveCoarseRegion_sites_iff
            (M := M) (N' := N') Ω (blockSite M N' x.1)).2
              (hΩ x.1 x.2)⟩) := by
  rfl

/-- On a fine site in the block of `y`, synthesis uses exactly the inverse
transport from `y`; all dependent proof terms disappear propositionally. -/
theorem cmp99TransportedBlockSynthesisCLM_apply_block
    (Ω : ActiveGaugeRegion d (M * N')) (hΩ : Ω.BlockSaturated)
    (w : ℝ)
    (transport : FinBox d N' → FinBox d (M * N') → (g ≃ₗᵢ[ℝ] g))
    (eta : ActiveGaugeZeroCochain
      (cmp99ActiveCoarseRegion (M := M) (N' := N') Ω) g)
    (y : ActiveGaugeRegion.Site
      (cmp99ActiveCoarseRegion (M := M) (N' := N') Ω))
    (x : {x : FinBox d (M * N') // x ∈ blockOf M N' y.1}) :
    cmp99TransportedBlockSynthesisCLM Ω hΩ w transport eta
        (cmp99ActiveFineSiteOfBlock Ω y x) =
      w • (transport y.1 x.1).symm (eta y) := by
  rw [cmp99TransportedBlockSynthesisCLM_apply]
  have howner : blockSite M N' x.1 = y.1 :=
    (mem_blockOf M N' y.1 x.1).mp x.2
  let y' : ActiveGaugeRegion.Site
      (cmp99ActiveCoarseRegion (M := M) (N' := N') Ω) :=
    ⟨blockSite M N' x.1,
      (mem_cmp99ActiveCoarseRegion_sites_iff
        (M := M) (N' := N') Ω (blockSite M N' x.1)).2
          (hΩ x.1
            (cmp99ActiveFineSiteOfBlock Ω y x).2)⟩
  have hy' : y' = y := Subtype.ext howner
  change w • (transport y'.1 x.1).symm (eta y') =
    w • (transport y.1 x.1).symm (eta y)
  rw [hy']

/-- Exact normalization in the unweighted `PiLp 2` convention. -/
theorem cmp99TransportedBlockAverage_comp_synthesis
    (Ω : ActiveGaugeRegion d (M * N')) (hΩ : Ω.BlockSaturated)
    (w : ℝ)
    (transport : FinBox d N' → FinBox d (M * N') → (g ≃ₗᵢ[ℝ] g)) :
    (cmp99TransportedBlockAverageCLM Ω w transport).comp
        (cmp99TransportedBlockSynthesisCLM Ω hΩ w transport) =
      (w ^ 2 * (M : ℝ) ^ d) •
        ContinuousLinearMap.id ℝ
          (ActiveGaugeZeroCochain
            (cmp99ActiveCoarseRegion (M := M) (N' := N') Ω) g) := by
  apply ContinuousLinearMap.ext
  intro eta
  ext y
  rw [ContinuousLinearMap.comp_apply,
    cmp99TransportedBlockAverageCLM_apply]
  simp_rw [cmp99TransportedBlockSynthesisCLM_apply_block,
    map_smul, LinearIsometryEquiv.apply_symm_apply]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, blockOf_card,
    ← Nat.cast_smul_eq_nsmul ℝ (M ^ d) (w • eta y), Nat.cast_pow]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
    PiLp.smul_apply, smul_smul]
  congr 1
  ring

/-- If the scalar weight is normalized for the unweighted counting Hilbert
spaces, the explicit synthesis is an exact right inverse.  This corollary
keeps the normalization obligation visible instead of silently importing the
lattice-spacing convention of the printed source. -/
theorem cmp99TransportedBlockAverage_comp_synthesis_of_normalization
    (Ω : ActiveGaugeRegion d (M * N')) (hΩ : Ω.BlockSaturated)
    (w : ℝ)
    (transport : FinBox d N' → FinBox d (M * N') → (g ≃ₗᵢ[ℝ] g))
    (hw : w ^ 2 * (M : ℝ) ^ d = 1) :
    (cmp99TransportedBlockAverageCLM Ω w transport).comp
        (cmp99TransportedBlockSynthesisCLM Ω hΩ w transport) =
      ContinuousLinearMap.id ℝ
        (ActiveGaugeZeroCochain
          (cmp99ActiveCoarseRegion (M := M) (N' := N') Ω) g) := by
  rw [cmp99TransportedBlockAverage_comp_synthesis Ω hΩ w transport, hw,
    one_smul]

end TransportedKernel

end

end YangMills.RG
