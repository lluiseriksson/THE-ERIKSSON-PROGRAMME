/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BlockLattice
import YangMills.RG.MayerCoverFactorization
import YangMills.RG.ModifiedMetric

/-!
# CMP109/CMP116 localization geometry for equation (2.14)

CMP109 defines localization domains using **face adjacency**: consecutive
`M`-cubes share a codimension-one wall.  This differs from the king-move
adjacency `cubeAdj`, which also joins cubes through edges and corners.  The
graph `cmp109FaceAdj` below records the source geometry separately.

CMP116 permits `Z₀` to have several connected components.  Accordingly,
`CMP116FaceComponentFamily` stores a finite, disjoint, face-connected and
face-separated family rather than forcing the whole region to be connected.

For the coarse region, CMP116 defines `Z₀'` as the minimal family of
`LM`-blocks covering an enlarged fine region `Ztilde₀`.  The definition
`cmp116Z0Prime` is exactly its image under the already formalized `blockSite`;
the terminal iff theorem proves its covering minimality.

Honest scope: the number of fine face-neighbourhood layers used to construct
`Ztilde₀` is deliberately not fixed here, because the inspected CMP109/CMP116
source window does not define that enlargement unambiguously.  This module
starts from an explicit enlarged fine region and closes only the exact coarse
covering step.
-/

namespace YangMills.RG

open Finset SimpleGraph

/-- Face-only adjacency of `M`-cubes: the cubes differ by one lattice step in
one coordinate and agree in every other coordinate. -/
def cmp109FaceAdj (d L : ℕ) : SimpleGraph (Cube d L) where
  Adj x y :=
    x ≠ y ∧ ∃ i,
      (y i - x i = 1 ∨ y i - x i = -1) ∧
      ∀ j, j ≠ i → y j = x j
  symm := by
    rintro x y ⟨hne, i, hstep, hsame⟩
    refine ⟨hne.symm, i, ?_, fun j hji => (hsame j hji).symm⟩
    have hxy : x i - y i = -(y i - x i) := (neg_sub _ _).symm
    rcases hstep with h | h
    · right
      rw [hxy, h]
    · left
      rw [hxy, h, neg_neg]
  loopless := ⟨fun x hx => hx.1 rfl⟩

instance cmp109FaceAdj_decidableRel (d L : ℕ) :
    DecidableRel (cmp109FaceAdj d L).Adj := by
  intro x y
  show Decidable
    (x ≠ y ∧ ∃ i,
      (y i - x i = 1 ∨ y i - x i = -1) ∧
      ∀ j, j ≠ i → y j = x j)
  infer_instance

/-- A source-faithful certificate for the possibly disconnected region `Z₀`.
Each listed part is a nonempty face-connected component; different parts are
disjoint and have no face-adjacency edge between them. -/
structure CMP116FaceComponentFamily (d L : ℕ) where
  parts : Finset (Finset (Cube d L))
  nonempty : ∀ C ∈ parts, C.Nonempty
  connected : ∀ C ∈ parts, walkConnected (cmp109FaceAdj d L) C
  disjoint : ∀ A ∈ parts, ∀ B ∈ parts, A ≠ B → Disjoint A B
  separated : ∀ A ∈ parts, ∀ B ∈ parts, A ≠ B →
    ∀ x ∈ A, ∀ y ∈ B, ¬(cmp109FaceAdj d L).Adj x y

/-- The complete fine-cube carrier of a component family. -/
def CMP116FaceComponentFamily.region
    {d L : ℕ} (Z0 : CMP116FaceComponentFamily d L) : Finset (Cube d L) :=
  Z0.parts.biUnion fun C => C

@[simp] theorem mem_CMP116FaceComponentFamily_region_iff
    {d L : ℕ} {Z0 : CMP116FaceComponentFamily d L} {x : Cube d L} :
    x ∈ Z0.region ↔ ∃ C ∈ Z0.parts, x ∈ C := by
  simp [CMP116FaceComponentFamily.region]

/-- Canonical face-connected components of an arbitrary finite localization
region.  This uses confined reachability in the face graph, so the result is a
partition of the supplied region rather than an assumed global component. -/
noncomputable def cmp116FaceComponents
    {d L : ℕ} (region : Finset (Cube d L)) :
    CMP116FaceComponentFamily d L where
  parts := confinedComponents (cmp109FaceAdj d L) region
  nonempty := by
    intro C hC
    rcases (mem_confinedComponents_iff (cmp109FaceAdj d L) region C).mp hC with
      ⟨r, hr, rfl⟩
    exact ⟨r, root_mem_confinedComponent (cmp109FaceAdj d L) region hr⟩
  connected := by
    intro C hC
    rcases (mem_confinedComponents_iff (cmp109FaceAdj d L) region C).mp hC with
      ⟨r, _hr, rfl⟩
    exact confinedComponent_walkConnected (cmp109FaceAdj d L) region r
  disjoint := by
    intro A hA B hB hne
    exact disjoint_of_mem_confinedComponents_ne
      (cmp109FaceAdj d L) region hA hB hne
  separated := by
    intro A hA B hB hne x hx y hy
    exact no_adj_of_mem_confinedComponents_ne
      (cmp109FaceAdj d L) region hA hB hne hx hy

/-- The canonical component construction covers exactly its input region. -/
@[simp] theorem cmp116FaceComponents_region
    {d L : ℕ} (region : Finset (Cube d L)) :
    (cmp116FaceComponents region).region = region := by
  exact biUnion_confinedComponents_eq (cmp109FaceAdj d L) region

/-- The coarse `LM`-cube family covering the enlarged fine region
`Ztilde₀`: take exactly the blocks hit by its fine cubes. -/
noncomputable def cmp116Z0Prime
    {d L N' : ℕ} [NeZero L]
    (Ztilde0 : Finset (FinBox d (L * N'))) : Finset (FinBox d N') :=
  Ztilde0.image (blockSite L N')

@[simp] theorem mem_cmp116Z0Prime_iff
    {d L N' : ℕ} [NeZero L]
    {Ztilde0 : Finset (FinBox d (L * N'))} {y : FinBox d N'} :
    y ∈ cmp116Z0Prime Ztilde0 ↔
      ∃ x ∈ Ztilde0, blockSite L N' x = y := by
  classical
  simp [cmp116Z0Prime]

/-- Every fine cube of `Ztilde₀` lies in a block selected by `Z₀'`. -/
theorem cmp116Ztilde0_subset_blocksOf_Z0Prime
    {d L N' : ℕ} [NeZero L]
    (Ztilde0 : Finset (FinBox d (L * N'))) :
    Ztilde0 ⊆ (cmp116Z0Prime Ztilde0).biUnion (blockOf L N') := by
  classical
  intro x hx
  simp only [Finset.mem_biUnion, mem_blockOf]
  have hblock : blockSite L N' x ∈ cmp116Z0Prime Ztilde0 := by
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  exact ⟨blockSite L N' x, hblock, rfl⟩

/-- Characteristic minimality of `Z₀'`: a coarse family contains the exact
image `cmp116Z0Prime Ztilde₀` iff its blocks cover `Ztilde₀`. -/
theorem cmp116Z0Prime_subset_iff_cover
    {d L N' : ℕ} [NeZero L]
    (Ztilde0 : Finset (FinBox d (L * N'))) (coarse : Finset (FinBox d N')) :
    cmp116Z0Prime Ztilde0 ⊆ coarse ↔
      Ztilde0 ⊆ coarse.biUnion (blockOf L N') := by
  classical
  constructor
  · intro h x hx
    simp only [Finset.mem_biUnion, mem_blockOf]
    have hblock : blockSite L N' x ∈ cmp116Z0Prime Ztilde0 := by
      exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
    exact ⟨blockSite L N' x, h hblock, rfl⟩
  · intro h y hy
    rw [mem_cmp116Z0Prime_iff] at hy
    obtain ⟨x, hx, hxy⟩ := hy
    have hxcover := h hx
    simp only [Finset.mem_biUnion, mem_blockOf] at hxcover
    obtain ⟨y', hy'coarse, hxy'⟩ := hxcover
    rw [hxy'] at hxy
    simpa [hxy] using hy'coarse

end YangMills.RG
