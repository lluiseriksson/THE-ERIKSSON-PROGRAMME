/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceLocalizationOwnerDistanceBridge

/-!
# PRE-VALIDATION: forward distance to CMP99 localization owners

Source is present at the checkpoint containing this file; its `.olean` has not
yet been materialized and the result is not yet compiler-verified.

The inverse-scale bridge already sealed in the tree retains the sharp block
boundary term

`ell * ownerDist <= fineDist + 2 * (ell - 1)`.

For fixed-rate decay one needs the complementary, coarser statement

`ownerDist <= fineDist`.

It follows from the inverse bridge without a second coordinate dictionary.
Fine distance zero forces equality of the sites; fine distance one forces
owner distance at most one by integrality; from fine distance two onward the
boundary term is absorbed by `ell * fineDist`.  The final physical theorem
also cites the already sealed fact that the literal signed transport `l1`
length dominates fine Chebyshev distance.

Honest scope: this is a metric dictionary.  It does not identify the CMP89
Fourier integral with a Green kernel, construct `B0`, attain window 15,
discharge a terminal field, or inhabit a `TermSource`.
-/

namespace YangMills.RG

noncomputable section

/-- Circular torus distance separates points. -/
theorem finTorusDist_eq_zero_iff {N : ℕ} [NeZero N] (a b : Fin N) :
    finTorusDist a b = 0 ↔ a = b := by
  constructor
  · intro h
    have hz : ((a.val : ZMod N) - (b.val : ZMod N)) = 0 := by
      unfold finTorusDist zmodCircDist zmodCircVal at h
      rcases Nat.min_eq_zero.mp h with hval | hneg
      · exact (ZMod.val_eq_zero _).mp hval
      · have hnegZero : -((a.val : ZMod N) - (b.val : ZMod N)) = 0 :=
          (ZMod.val_eq_zero _).mp hneg
        exact neg_eq_zero.mp hnegZero
    exact finToZMod_injective (sub_eq_zero.mp hz)
  · rintro rfl
    exact finTorusDist_self a

/-- Chebyshev torus distance separates sites. -/
theorem finBoxDist_eq_zero_iff {d N : ℕ} [NeZero N]
    (x y : FinBox d N) :
    finBoxDist x y = 0 ↔ x = y := by
  constructor
  · intro hzero
    funext mu
    apply (finTorusDist_eq_zero_iff (x mu) (y mu)).mp
    apply Nat.eq_zero_of_le
    simpa [hzero] using finTorusDist_le_finBoxDist x y mu
  · rintro rfl
    exact finBoxDist_self x

/-- The block-owner quotient is nonexpanding for the literal Chebyshev torus
distance.  The proof deliberately reuses the sealed inverse-scale comparison,
including separate exact treatments of fine distances zero and one. -/
theorem finBoxDist_blockSite_le_finBoxDist
    {d ell n : ℕ} [NeZero ell] [NeZero n]
    (x y : FinBox d (ell * n)) :
    finBoxDist (blockSite ell n x) (blockSite ell n y) ≤
      finBoxDist x y := by
  let ownerDist := finBoxDist (blockSite ell n x) (blockSite ell n y)
  let fineDist := finBoxDist x y
  have hinverse : ell * ownerDist ≤ fineDist + 2 * (ell - 1) := by
    simpa [ownerDist, fineDist] using
      mul_finBoxDist_blockSite_le_finBoxDist_add_two_mul_sub_one x y
  by_cases hzero : fineDist = 0
  · have hxy : x = y := by
      apply (finBoxDist_eq_zero_iff x y).mp
      exact hzero
    subst y
    simp [ownerDist, fineDist]
  by_cases hone : fineDist = 1
  · have hlt : ell * ownerDist < ell * 2 := by
      rw [hone] at hinverse
      omega
    have howner : ownerDist < 2 :=
      (Nat.mul_lt_mul_left (NeZero.pos ell)).mp hlt
    omega
  · have htwo : 2 ≤ fineDist := by omega
    have hboundary : 2 * (ell - 1) ≤ fineDist * (ell - 1) :=
      Nat.mul_le_mul_right (ell - 1) htwo
    have habsorb : fineDist + 2 * (ell - 1) ≤ ell * fineDist := by
      calc
        fineDist + 2 * (ell - 1) ≤
            fineDist + fineDist * (ell - 1) :=
          Nat.add_le_add_left hboundary fineDist
        _ = ell * fineDist := by omega
    have hscaled : ell * ownerDist ≤ ell * fineDist :=
      hinverse.trans habsorb
    exact (Nat.mul_le_mul_left (NeZero.pos ell)).mp hscaled

/-- The literal CMP99 source owner distance is bounded by fine-site distance,
with the source carrier cast kept explicit. -/
theorem cmp99Eq389SourceLocalizationOwner_dist_le_fineDist
    {L K Q : ℕ} [NeZero L] [NeZero K] [NeZero Q]
    (depth : ℕ)
    (target source : FinBox 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))) :
    finBoxDist
        (cmp99Eq389SourceLocalizationOwner L K Q depth target)
        (cmp99Eq389SourceLocalizationOwner L K Q depth source) ≤
      finBoxDist target source := by
  let hsize :=
    cmp99SourceSeparatedCarrier_eq_sourceLocalizationCarrier L K Q depth
  let target' := cmp99Eq389SourceLocalizationSiteEquiv L K Q depth target
  let source' := cmp99Eq389SourceLocalizationSiteEquiv L K Q depth source
  have h := finBoxDist_blockSite_le_finBoxDist target' source'
  have hdist : finBoxDist target' source' = finBoxDist target source := by
    unfold target' source' cmp99Eq389SourceLocalizationSiteEquiv
    exact finBoxDist_equivCast_size hsize target source
  rw [hdist] at h
  simpa [target', source', cmp99Eq389SourceLocalizationOwner] using h

/-- Physical transport form of the forward owner comparison.  The owner
distance is bounded by the literal signed `l1` length used in the CMP89
contour displacement, with no scale-dependent boundary factor. -/
theorem cmp99Eq389SourceLocalizationOwner_dist_le_transportL1
    {L K Q : ℕ} [NeZero L] [NeZero K] [NeZero Q]
    (depth : ℕ)
    (b : PhysicalBond 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))
    (y : FinBox 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))) :
    (finBoxDist
        (cmp99Eq389SourceLocalizationOwner L K Q depth (cmp116BondTarget b))
        (cmp99Eq389SourceLocalizationOwner L K Q depth y) : ℝ) ≤
      cmp89Eq251LatticeL1Length
        (cmp116CMP89PhysicalBondTransportDisplacement b y) := by
  have howner :=
    cmp99Eq389SourceLocalizationOwner_dist_le_fineDist
      depth (cmp116BondTarget b) y
  have hownerReal :
      (finBoxDist
          (cmp99Eq389SourceLocalizationOwner L K Q depth (cmp116BondTarget b))
          (cmp99Eq389SourceLocalizationOwner L K Q depth y) : ℝ) ≤
        (finBoxDist (cmp116BondTarget b) y : ℝ) := by
    exact_mod_cast howner
  exact hownerReal.trans
    (finBoxDist_le_cmp116CMP89PhysicalBondTransportDisplacement_realL1 b y)

end

end YangMills.RG
