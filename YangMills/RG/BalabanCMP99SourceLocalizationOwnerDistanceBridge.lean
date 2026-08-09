/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116CMP89PhysicalSiteTransportDictionary
import YangMills.RG.BalabanCMP99Eq389SourceLocalizationOwner
import YangMills.RG.BlockBasepointDistance
import YangMills.RG.PhysicalShellLocalityQ

/-!
# PRE-VALIDATION: fine-site distance to CMP99 localization-owner distance

Source is present, its `.olean` has not yet been materialized, and the result
has not yet been verified by the compiler.

CMP89 contour displacement produces decay in fine-lattice edge units, while
CMP99 (3.42)/(3.89) consumes distance between localization-block owners.  This
file states the conversion in the load-bearing direction.  If `x` and `y` lie
in blocks of side `ell`, then the two lower block corners are at exact distance
`ell * ownerDist`; each fine site costs at most `ell-1` to reach its corner.
Hence

`ell * ownerDist <= fineDist + 2*(ell-1)`.

For the sealed CMP89 transport displacement, `fineDist <= transportL1`, so the
same inequality holds with its literal `l1` length.  The boundary cost and the
fine/coarse units remain visible; no direct subtraction of a coarse owner from
a fine endpoint occurs.

Honest scope: this is a metric dictionary.  It does not exponentiate the
inequality, construct the complete endpoint bound `B0`, attain window 15,
discharge a terminal field, or inhabit a `TermSource`.
-/

namespace YangMills.RG

noncomputable section

/-- Exact inverse-scale comparison between fine distance and block-owner
distance, including the two block-boundary costs. -/
theorem mul_finBoxDist_blockSite_le_finBoxDist_add_two_mul_sub_one
    {d ell n : ℕ} [NeZero ell] [NeZero n]
    (x y : FinBox d (ell * n)) :
    ell * finBoxDist (blockSite ell n x) (blockSite ell n y) ≤
      finBoxDist x y + 2 * (ell - 1) := by
  let bx := blockBasepoint ell n (blockSite ell n x)
  let bySite := blockBasepoint ell n (blockSite ell n y)
  have hbx : finBoxDist bx x ≤ ell - 1 := by
    apply finBoxDist_le_of_same_block
    simp [bx]
  have hby : finBoxDist y bySite ≤ ell - 1 := by
    apply finBoxDist_le_of_same_block
    simp [bySite]
  calc
    ell * finBoxDist (blockSite ell n x) (blockSite ell n y) =
        finBoxDist bx bySite := by
          symm
          exact finBoxDist_blockBasepoint_eq_mul ell n
            (blockSite ell n x) (blockSite ell n y)
    _ ≤ finBoxDist bx x + finBoxDist x bySite := finBoxDist_triangle _ _ _
    _ ≤ finBoxDist bx x + (finBoxDist x y + finBoxDist y bySite) := by
      exact Nat.add_le_add_left (finBoxDist_triangle x y bySite) _
    _ ≤ (ell - 1) + (finBoxDist x y + (ell - 1)) := by
      exact Nat.add_le_add hbx (Nat.add_le_add_left hby _)
    _ = finBoxDist x y + 2 * (ell - 1) := by omega

/-- Chebyshev torus distance is bounded by the sum of its coordinatewise
torus distances. -/
theorem finBoxDist_le_sum_finTorusDist {d N : ℕ} [NeZero N]
    (x y : FinBox d N) :
    finBoxDist x y ≤ ∑ mu, finTorusDist (x mu) (y mu) := by
  unfold finBoxDist
  apply Finset.sup_le
  intro mu hmu
  exact Finset.single_le_sum (fun nu _ ↦ Nat.zero_le
    (finTorusDist (x nu) (y nu))) hmu

/-- The explicit `Equiv.cast` used by source dictionaries preserves the
literal periodic distance. -/
theorem finBoxDist_equivCast_size
    {d N₁ N₂ : ℕ} (h : N₁ = N₂) (x y : FinBox d N₁) :
    finBoxDist
        ((Equiv.cast (congrArg (FinBox d) h)) x)
        ((Equiv.cast (congrArg (FinBox d) h)) y) =
      finBoxDist x y := by
  subst h
  rfl

private instance instNeZeroSourceLocalizationOwnerDistanceAmbient
    (L K Q depth : ℕ) [NeZero L] [NeZero K] [NeZero Q] :
    NeZero (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)) :=
  ⟨(Nat.mul_pos
    (Nat.mul_pos (NeZero.pos K) (pow_pos (NeZero.pos L) (depth + 1)))
    (Nat.mul_pos (by omega) (NeZero.pos Q))).ne'⟩

/-- CMP99's source-localization owner is exactly the `blockSite` owner at
scale `L^(depth+1)`, so the generic inverse-scale comparison applies after the
single carrier cast already named in the source dictionary. -/
theorem cmp99Eq389SourceLocalizationOwner_mul_dist_le_fineDist_add_boundary
    {L K Q : ℕ} [NeZero L] [NeZero K] [NeZero Q]
    (depth : ℕ)
    (target source : FinBox 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))) :
    L ^ (depth + 1) *
        finBoxDist
          (cmp99Eq389SourceLocalizationOwner L K Q depth target)
          (cmp99Eq389SourceLocalizationOwner L K Q depth source) ≤
      finBoxDist target source + 2 * (L ^ (depth + 1) - 1) := by
  let hsize :=
    cmp99SourceSeparatedCarrier_eq_sourceLocalizationCarrier L K Q depth
  let target' := cmp99Eq389SourceLocalizationSiteEquiv L K Q depth target
  let source' := cmp99Eq389SourceLocalizationSiteEquiv L K Q depth source
  have h :=
    mul_finBoxDist_blockSite_le_finBoxDist_add_two_mul_sub_one target' source'
  have hdist : finBoxDist target' source' = finBoxDist target source := by
    unfold target' source' cmp99Eq389SourceLocalizationSiteEquiv
    exact finBoxDist_equivCast_size hsize target source
  rw [hdist] at h
  simpa [target', source', cmp99Eq389SourceLocalizationOwner] using h

/-- The sealed CMP89 transport `l1` length dominates literal fine Chebyshev
distance. -/
theorem finBoxDist_le_cmp116CMP89PhysicalBondTransportDisplacement_realL1
    {N : ℕ} [NeZero N] (b : PhysicalBond 4 N) (y : FinBox 4 N) :
    (finBoxDist (cmp116BondTarget b) y : ℝ) ≤
      cmp89Eq251LatticeL1Length
        (cmp116CMP89PhysicalBondTransportDisplacement b y) := by
  rw [cmp116CMP89PhysicalBondTransportDisplacement_realL1_eq]
  exact_mod_cast finBoxDist_le_sum_finTorusDist (cmp116BondTarget b) y

/-- Physical transport form of the inverse-scale owner comparison.  The
fine-lattice `l1` displacement is constructed internally from `b` and `y`;
only the literal block-boundary cost remains. -/
theorem cmp99Eq389SourceLocalizationOwner_mul_dist_le_transportL1_add_boundary
    {L K Q : ℕ} [NeZero L] [NeZero K] [NeZero Q]
    (depth : ℕ)
    (b : PhysicalBond 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))
    (y : FinBox 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))) :
    (L ^ (depth + 1) : ℝ) *
        (finBoxDist
          (cmp99Eq389SourceLocalizationOwner L K Q depth (cmp116BondTarget b))
          (cmp99Eq389SourceLocalizationOwner L K Q depth y) : ℝ) ≤
      cmp89Eq251LatticeL1Length
          (cmp116CMP89PhysicalBondTransportDisplacement b y) +
        (2 * (L ^ (depth + 1) - 1) : ℕ) := by
  have howner :=
    cmp99Eq389SourceLocalizationOwner_mul_dist_le_fineDist_add_boundary
      depth (cmp116BondTarget b) y
  have hownerReal :
      (L ^ (depth + 1) : ℝ) *
          (finBoxDist
            (cmp99Eq389SourceLocalizationOwner L K Q depth
              (cmp116BondTarget b))
            (cmp99Eq389SourceLocalizationOwner L K Q depth y) : ℝ) ≤
        (finBoxDist (cmp116BondTarget b) y : ℝ) +
          (2 * (L ^ (depth + 1) - 1) : ℕ) := by
    exact_mod_cast howner
  exact hownerReal.trans (add_le_add
    (finBoxDist_le_cmp116CMP89PhysicalBondTransportDisplacement_realL1 b y)
    (le_refl _))

end

end YangMills.RG
