/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq229ShiftedCardMetric

/-!
# A cube-edge tree metric for CMP116 equation (2.30)

CMP109 defines `d_k(Y)` as the length, in `M`-units, of a shortest
continuous tree contained in `Y` and meeting every `M`-cube.  It explicitly
states that an equivalent shortest tree may be chosen from cube edges.

This file gives the finite combinatorial realization needed for the lower
cardinality estimate.  A tree carrier is a nonempty face-connected finite set
of periodic cube vertices.  Every carrier vertex must be a corner of a cube
of `Y`, and every cube of `Y` must meet a carrier vertex.  Its normalized
length is `vertices.card - 1`; minimizing this length defines
`cmp116CubeEdgeTreeMetric`.

The incidence count is source-safe:

* one periodic cube vertex belongs to at most `2^4 = 16` cubes;
* hence a carrier with `e + 1` vertices meets at most `16 (e + 1)` cubes;
* weakening `16` to the printed constant `24 = 3 * 2^3` gives

`|Y| / 24 ≤ cmp116CubeEdgeTreeMetric Y + 1`.

The `+1` is essential for a one-cube domain with a degenerate length-zero
tree.  No convention excluding that tree is imposed.
-/

namespace YangMills.RG

open Finset

/-- Coordinatewise predecessor choice: the `2^4` cubes having `v` as a
corner are obtained by independently taking the cube based at `v` or the
cube immediately behind `v` in each coordinate. -/
def cmp116CornerCube {N' : ℕ} [NeZero N']
    (v : FinBox 4 N') (back : Fin 4 → Bool) : FinBox 4 N' :=
  fun i =>
    if back i then
      (FinBox.shiftBack v i) i
    else
      v i

/-- The finite family of coarse cubes incident to a periodic cube vertex. -/
noncomputable def cmp116CubesAtCorner {N' : ℕ} [NeZero N']
    (v : FinBox 4 N') : Finset (FinBox 4 N') :=
  Finset.univ.image (cmp116CornerCube v)

/-- A cube is incident to its own lower corner. -/
theorem mem_cmp116CubesAtCorner_self
    {N' : ℕ} [NeZero N'] (c : FinBox 4 N') :
    c ∈ cmp116CubesAtCorner c := by
  classical
  rw [cmp116CubesAtCorner, Finset.mem_image]
  refine ⟨fun _ => false, Finset.mem_univ _, ?_⟩
  funext i
  simp [cmp116CornerCube]

/-- Periodic identifications can only reduce the `2^4` corner incidence
count. -/
theorem cmp116CubesAtCorner_card_le_sixteen
    {N' : ℕ} [NeZero N'] (v : FinBox 4 N') :
    (cmp116CubesAtCorner v).card ≤ 16 := by
  classical
  calc
    (cmp116CubesAtCorner v).card ≤
        (Finset.univ : Finset (Fin 4 → Bool)).card := by
      simpa [cmp116CubesAtCorner] using
        (Finset.card_image_le :
          (Finset.univ.image (cmp116CornerCube v)).card ≤
            (Finset.univ : Finset (Fin 4 → Bool)).card)
    _ = 16 := by norm_num

/-- Finite cube-edge carrier meeting all cubes of a localization domain.

Face connectivity of the vertex carrier encodes a tree after choosing a
spanning tree.  The two incidence fields express containment in the union of
cubes and intersection with every cube. -/
def CMP116CubeEdgeTreeCarrier
    {M N' : ℕ} [NeZero N']
    (Y : CMP116LocalizationDomain M N')
    (vertices : Finset (FinBox 4 N')) : Prop :=
  vertices.Nonempty ∧
    walkConnected (cmp116CoarseFaceAdj 4 N') vertices ∧
    (∀ v ∈ vertices, ∃ c ∈ Y.blocks, c ∈ cmp116CubesAtCorner v) ∧
    (∀ c ∈ Y.blocks, ∃ v ∈ vertices, c ∈ cmp116CubesAtCorner v)

/-- The source block family itself is a cube-edge carrier: take every lower
corner and a spanning tree of the face-connected block family. -/
theorem cmp116LocalizationDomain_blocks_treeCarrier
    {M N' : ℕ} [NeZero N']
    (Y : CMP116LocalizationDomain M N') :
    CMP116CubeEdgeTreeCarrier Y Y.blocks := by
  refine ⟨Y.nonempty, Y.connected, ?_, ?_⟩
  · intro v hv
    exact ⟨v, hv, mem_cmp116CubesAtCorner_self v⟩
  · intro c hc
    exact ⟨c, hc, mem_cmp116CubesAtCorner_self c⟩

/-- All normalized lengths of admissible cube-edge tree carriers. -/
noncomputable def cmp116CubeEdgeTreeLengths
    {M N' : ℕ} [NeZero N']
    (Y : CMP116LocalizationDomain M N') : Finset ℕ :=
  by
    classical
    exact
      (Finset.univ.filter (CMP116CubeEdgeTreeCarrier Y)).image
        (fun vertices => vertices.card - 1)

theorem cmp116CubeEdgeTreeLengths_nonempty
    {M N' : ℕ} [NeZero N']
    (Y : CMP116LocalizationDomain M N') :
    (cmp116CubeEdgeTreeLengths Y).Nonempty := by
  classical
  refine ⟨Y.blocks.card - 1, ?_⟩
  rw [cmp116CubeEdgeTreeLengths, Finset.mem_image]
  exact ⟨Y.blocks, by
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, cmp116LocalizationDomain_blocks_treeCarrier Y⟩,
    rfl⟩

/-- The normalized length of a shortest finite cube-edge carrier. -/
noncomputable def cmp116CubeEdgeTreeMetric
    {M N' : ℕ} [NeZero N']
    (Y : CMP116LocalizationDomain M N') : ℕ :=
  (cmp116CubeEdgeTreeLengths Y).min'
    (cmp116CubeEdgeTreeLengths_nonempty Y)

/-- The source block family itself gives the elementary upper bound on the
shortest cube-edge tree length.  This is the upper half of the printed
equation-(2.30) normalization. -/
theorem cmp116CubeEdgeTreeMetric_le_blockCard_sub_one
    {M N' : ℕ} [NeZero N']
    (Y : CMP116LocalizationDomain M N') :
    cmp116CubeEdgeTreeMetric Y ≤ Y.blocks.card - 1 := by
  classical
  apply Finset.min'_le
  rw [cmp116CubeEdgeTreeLengths, Finset.mem_image]
  exact ⟨Y.blocks, by
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _,
      cmp116LocalizationDomain_blocks_treeCarrier Y⟩, rfl⟩

/-- A minimizing carrier exists because the periodic coarse lattice is
finite. -/
theorem exists_cmp116CubeEdgeTreeCarrier_metric
    {M N' : ℕ} [NeZero N']
    (Y : CMP116LocalizationDomain M N') :
    ∃ vertices : Finset (FinBox 4 N'),
      CMP116CubeEdgeTreeCarrier Y vertices ∧
        cmp116CubeEdgeTreeMetric Y = vertices.card - 1 := by
  classical
  have hmem :
      cmp116CubeEdgeTreeMetric Y ∈ cmp116CubeEdgeTreeLengths Y := by
    exact Finset.min'_mem _ _
  rw [cmp116CubeEdgeTreeLengths, Finset.mem_image] at hmem
  obtain ⟨vertices, hvertices, hlength⟩ := hmem
  rw [Finset.mem_filter] at hvertices
  exact ⟨vertices, hvertices.2, hlength.symm⟩

/-- Any cube-edge carrier has enough vertices to meet all source cubes. -/
theorem cmp116LocalizationDomain_blockCard_le_sixteen_mul_treeVertexCard
    {M N' : ℕ} [NeZero N']
    (Y : CMP116LocalizationDomain M N')
    (vertices : Finset (FinBox 4 N'))
    (hvertices : CMP116CubeEdgeTreeCarrier Y vertices) :
    Y.blocks.card ≤ 16 * vertices.card := by
  classical
  have hsub :
      Y.blocks ⊆ vertices.biUnion cmp116CubesAtCorner := by
    intro c hc
    obtain ⟨v, hv, hcv⟩ := hvertices.2.2.2 c hc
    exact Finset.mem_biUnion.mpr ⟨v, hv, hcv⟩
  calc
    Y.blocks.card ≤
        (vertices.biUnion cmp116CubesAtCorner).card :=
      Finset.card_le_card hsub
    _ ≤ ∑ v ∈ vertices, (cmp116CubesAtCorner v).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _v ∈ vertices, 16 := by
      exact Finset.sum_le_sum fun v _hv =>
        cmp116CubesAtCorner_card_le_sixteen v
    _ = 16 * vertices.card := by
      simp [mul_comm]

/-- Convention-robust lower half of equation (2.30), derived from the
literal finite cube-edge metric. -/
theorem cmp116LocalizationDomain_eq230_shifted
    {M N' : ℕ} [NeZero N']
    (Y : CMP116LocalizationDomain M N') :
    (Y.blocks.card : ℝ) / 24 ≤
      (cmp116CubeEdgeTreeMetric Y : ℝ) + 1 := by
  obtain ⟨vertices, hvertices, hmetric⟩ :=
    exists_cmp116CubeEdgeTreeCarrier_metric Y
  have hcount :=
    cmp116LocalizationDomain_blockCard_le_sixteen_mul_treeVertexCard
      Y vertices hvertices
  have hvertexPos : 0 < vertices.card :=
    Finset.card_pos.mpr hvertices.1
  have hmetricSucc :
      cmp116CubeEdgeTreeMetric Y + 1 = vertices.card := by
    rw [hmetric]
    exact Nat.succ_pred_eq_of_pos hvertexPos
  have hcount24 : Y.blocks.card ≤ 24 * vertices.card := by
    omega
  have hcountR :
      (Y.blocks.card : ℝ) ≤ 24 * (vertices.card : ℝ) := by
    exact_mod_cast hcount24
  rw [← hmetricSucc] at hcountR
  norm_num at hcountR
  nlinarith

/-- The same bound in the literal source normalization
`M⁻⁴ |Y| ≤ 24 (d_k(Y)+1)`. -/
theorem cmp116LocalizationDomain_sourceCard_eq230_shifted
    {M N' : ℕ} [NeZero M] [NeZero N']
    (Y : CMP116LocalizationDomain M N') :
    ((M : ℝ) ^ 4)⁻¹ * (Y.sourceCard : ℝ) / 24 ≤
      (cmp116CubeEdgeTreeMetric Y : ℝ) + 1 := by
  have hblocks := cmp116LocalizationDomain_eq230_shifted Y
  have hM : (M : ℝ) ≠ 0 := by
    exact_mod_cast (NeZero.ne M)
  calc
    ((M : ℝ) ^ 4)⁻¹ * (Y.sourceCard : ℝ) / 24 =
        (Y.blocks.card : ℝ) / 24 := by
      rw [cmp116LocalizationDomain_sourceCard_eq]
      push_cast
      field_simp [hM]
    _ ≤ (cmp116CubeEdgeTreeMetric Y : ℝ) + 1 := hblocks

/-- Canonical source tree metric on arbitrary coarse block families.

For physical nonempty face-connected domains the positive branch constructs
the corresponding localization domain.  The value outside that source class
is irrelevant to equation (2.29) and is set to zero. -/
noncomputable def cmp116SourceTreeMetric
    {N' : ℕ} [NeZero N']
    (Y : Finset (FinBox 4 N')) : ℕ :=
  by
    classical
    exact
      if h :
          Y.Nonempty ∧
            walkConnected (cmp116CoarseFaceAdj 4 N') Y then
        cmp116CubeEdgeTreeMetric
          (M := 1)
          ({ blocks := Y
             nonempty := h.1
             connected := h.2 } :
            CMP116LocalizationDomain 1 N')
      else
        0

theorem cmp116SourceTreeMetric_eq
    {N' : ℕ} [NeZero N']
    (Y : Finset (FinBox 4 N'))
    (hY : Y.Nonempty)
    (hconn : walkConnected (cmp116CoarseFaceAdj 4 N') Y) :
    cmp116SourceTreeMetric Y =
      cmp116CubeEdgeTreeMetric
        (M := 1)
        ({ blocks := Y
           nonempty := hY
           connected := hconn } :
          CMP116LocalizationDomain 1 N') := by
  rw [cmp116SourceTreeMetric, dif_pos ⟨hY, hconn⟩]

/-- For a nonempty face-connected physical block family, the canonical source
tree metric is at most the number of blocks minus one. -/
theorem cmp116SourceTreeMetric_le_card_sub_one
    {N' : ℕ} [NeZero N']
    (Y : Finset (FinBox 4 N'))
    (hY : Y.Nonempty)
    (hconn : walkConnected (cmp116CoarseFaceAdj 4 N') Y) :
    cmp116SourceTreeMetric Y ≤ Y.card - 1 := by
  rw [cmp116SourceTreeMetric_eq Y hY hconn]
  exact
    cmp116CubeEdgeTreeMetric_le_blockCard_sub_one
      ({ blocks := Y, nonempty := hY, connected := hconn } :
        CMP116LocalizationDomain 1 N')

/-- The canonical source metric discharges the shifted equation-(2.30)
comparison for every physical domain. -/
theorem cmp116SourceTreeMetric_eq230_shifted
    {N' : ℕ} [NeZero N']
    (Y : Finset (FinBox 4 N'))
    (hY : Y.Nonempty)
    (hconn : walkConnected (cmp116CoarseFaceAdj 4 N') Y) :
    (Y.card : ℝ) / 24 ≤
      (cmp116SourceTreeMetric Y : ℝ) + 1 := by
  let domain : CMP116LocalizationDomain 1 N' :=
    { blocks := Y
      nonempty := hY
      connected := hconn }
  have hsource :
      (domain.blocks.card : ℝ) / 24 ≤
        (cmp116CubeEdgeTreeMetric domain : ℝ) + 1 :=
    cmp116LocalizationDomain_eq230_shifted domain
  simpa [domain, cmp116SourceTreeMetric_eq Y hY hconn] using hsource

/-- Fully constructed convention-robust equation-(2.29) producer.

The interface contains neither equation (2.27), equation (2.29), nor either
form of equation (2.30).  The tree metric and its shifted cardinal comparison
are generated internally from the physical nonempty face-connected domains. -/
theorem CMP116Eq229Summability.of_exactUnion_fourDimensional_sourceTreeMetric_uniform
    {N' : ℕ} [NeZero N']
    (domainFamily : Finset (Finset (FinBox 4 N')))
    (hdomains :
      ∀ Y ∈ domainFamily,
        Y.Nonempty ∧
          walkConnected (cmp116CoarseFaceAdj 4 N') Y)
    (alpha6 delta kappa : ℝ)
    (halpha6 : 0 ≤ alpha6)
    (hdeltaKappa : 0 ≤ delta * kappa)
    (hCq :
      64 * Real.exp (-((delta * kappa) / 48)) < 1)
    (huniform :
      (alpha6 * Real.exp (3 * (delta * kappa))) *
          24 *
          (1 -
            64 * Real.exp (-((delta * kappa) / 48)))⁻¹ ≤
        (delta * kappa) / 2) :
    CMP116Eq229Summability
      (fun Y0 : {Y0 : Finset (FinBox 4 N') // Y0.Nonempty} =>
        cmp116Eq229ExactUnionDIndex domainFamily Y0.1)
      (fun _Y0 D => D)
      alpha6 delta kappa
      (fun _Y0 Y => cmp116SourceTreeMetric Y) := by
  exact
    CMP116Eq229Summability.of_exactUnion_fourDimensional_eq230Shifted_uniform
      domainFamily hdomains alpha6 delta kappa
      cmp116SourceTreeMetric halpha6 hdeltaKappa
      (fun Y hY =>
        cmp116SourceTreeMetric_eq230_shifted
          Y (hdomains Y hY).1 (hdomains Y hY).2)
      hCq huniform

end YangMills.RG
