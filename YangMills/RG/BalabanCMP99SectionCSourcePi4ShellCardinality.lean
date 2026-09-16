/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SectionCSourcePi4CovarianceDifference
import YangMills.RG.BalabanCMP116Eq214Interior

/-!
# Explicit cardinality of the literal `Pi^4` covariance shell

The common-collar estimate for `C_{Pi^4} - C_Pi` still displayed the finite
shell cardinality.  This file removes it by counting every supported bond from
its physical source site and one of the four positive directions.

A source domain `X` contains exactly `16 * |X|` large blocks.  Each large
block contains at most `M^4` physical source sites, and each site has four
positive bonds.  Hence a `Pi^4` domain, with at most `625` source cells, has
at most `40000 * M^4` supported bonds.  The same bound controls its shell.
-/

namespace YangMills.RG

noncomputable section

private abbrev PhysicalEndomorphism (d N Nc : ℕ) [NeZero N] :=
  PhysicalGaugeOneCochain d N Nc →L[ℝ]
    PhysicalGaugeOneCochain d N Nc

/-- Bilateral support of a source domain is bounded by its possible physical
source sites and the four positive bond directions. -/
theorem card_cmp99SourceDomainPhysicalBondSupport_le
    {M Q S : ℕ} [NeZero M] [NeZero Q]
    (X : CMP99SimpleLocalizationDomain (cmp116CoarseFaceAdj 4 Q) S) :
    (cmp99SourceDomainPhysicalBondSupport (M := M) X).card ≤
      ((16 * X.blocks.card) * M ^ 4) * 4 := by
  classical
  let blocks := cmp99SourceDomainLargeBlocks X
  let carrier : Finset (PhysicalBond 4 (M * (2 * Q))) :=
    (cmp116RegionSites blocks) ×ˢ (Finset.univ : Finset (Fin 4))
  have hsubset :
      cmp99SourceDomainPhysicalBondSupport (M := M) X ⊆ carrier := by
    intro bond hbond
    rw [mem_cmp99SourceDomainPhysicalBondSupport_iff] at hbond
    have hsourceBlock : cmp116BondSourceBlock bond ∈ blocks := by
      dsimp [blocks]
      rw [mem_cmp99SourceDomainLargeBlocks_iff]
      simpa [cmp99PhysicalBondBaseCell] using hbond.1
    exact Finset.mem_product.mpr
      ⟨mem_cmp116RegionSites_iff.mpr hsourceBlock, Finset.mem_univ _⟩
  calc
    (cmp99SourceDomainPhysicalBondSupport (M := M) X).card ≤
        carrier.card := Finset.card_le_card hsubset
    _ = (cmp116RegionSites blocks).card * 4 := by
      rw [Finset.card_product, Finset.card_univ, Fintype.card_fin]
    _ ≤ (blocks.card * M ^ 4) * 4 := by
      exact Nat.mul_le_mul_right 4 (card_cmp116RegionSites_le blocks)
    _ = ((16 * X.blocks.card) * M ^ 4) * 4 := by
      rw [show blocks.card = 16 * X.blocks.card by
        exact card_cmp99SourceDomainLargeBlocks X]

/-- The literal `Pi^4` bilateral support has at most `40000 * M^4` bonds. -/
theorem card_cmp99SourcePi4PhysicalBondSupport_le
    {M Q : ℕ} [NeZero M] [NeZero Q] (cell : FinBox 4 Q) :
    (cmp99SourcePi4PhysicalBondSupport (M := M) cell).card ≤
      40000 * M ^ 4 := by
  have h := card_cmp99SourceDomainPhysicalBondSupport_le
    (M := M) (cmp99SourcePi4CollarDomain cell)
  calc
    (cmp99SourcePi4PhysicalBondSupport (M := M) cell).card ≤
        ((16 * (cmp99SourcePi4CollarDomain cell).blocks.card) * M ^ 4) * 4 := h
    _ ≤ ((16 * 625) * M ^ 4) * 4 := by
      gcongr
      exact (cmp99SourcePi4CollarDomain cell).card_le
    _ = 40000 * M ^ 4 := by ring

/-- The shell between `Pi` and `Pi^4` obeys the same explicit local bound. -/
theorem card_cmp99SourcePi4CovarianceShell_le
    {M Q : ℕ} [NeZero M] [NeZero Q] (cell : FinBox 4 Q) :
    (cmp99SourcePi4PhysicalBondSupport (M := M) cell \
      cmp99SourcePiPhysicalBondSupport (M := M) cell).card ≤
        40000 * M ^ 4 := by
  have hsubset :
      cmp99SourcePi4PhysicalBondSupport (M := M) cell \
          cmp99SourcePiPhysicalBondSupport (M := M) cell ⊆
        cmp99SourcePi4PhysicalBondSupport (M := M) cell := by
    intro bond hbond
    exact (Finset.mem_sdiff.mp hbond).1
  exact le_trans (Finset.card_le_card hsubset)
    (card_cmp99SourcePi4PhysicalBondSupport_le cell)

/-- The literal `Pi^4`-versus-`Pi` covariance difference with both the
radius-ball count and shell cardinality replaced by explicit, volume-uniform
source constants. -/
theorem cmp99SourcePi4CovarianceDifference_bilateralDecay_explicitGeometry
    {M Q Nc : ℕ} [NeZero M] [NeZero Q]
    (K : PhysicalEndomorphism 4 (M * (2 * Q)) Nc)
    (cell : FinBox 4 Q)
    (R : ℕ) (hrange : PhysicalCovarianceFiniteRange K physicalBondDist R)
    {CK c mass A0 A1 mu : ℝ}
    (hCK : 0 ≤ CK) (hA0 : 0 ≤ A0) (hA1 : 0 ≤ A1)
    (hkernel : PhysicalCovarianceKernelBound K (fun _ _ => CK))
    (hc : 0 < c) (hmass : 0 < mass)
    (hcoercive : IsCoerciveCLM K c)
    (hC4 : PhysicalCovarianceExponentialKernelBound
      (cmp99LocalizedPhysicalCovariance K
        (cmp99SourcePi4PhysicalBondSupport cell) hc hmass hcoercive)
      physicalBondDist A0 mu)
    (hCPi : PhysicalCovarianceExponentialKernelBound
      (cmp99LocalizedPhysicalCovariance K
        (cmp99SourcePiPhysicalBondSupport (M := M) cell)
        hc hmass hcoercive)
      physicalBondDist A1 mu)
    {source target : PhysicalBond 4 (M * (2 * Q))} {L : ℕ}
    (htarget : target ∈ cmp99PhysicalBondShellGap physicalBondDist
      (cmp99SourcePi4PhysicalBondSupport cell \
        cmp99SourcePiPhysicalBondSupport (M := M) cell) R L)
    (hsource : source ∈ cmp99PhysicalBondShellGap physicalBondDist
      (cmp99SourcePi4PhysicalBondSupport cell \
        cmp99SourcePiPhysicalBondSupport (M := M) cell) R L)
    (v0 : SUNLieCoord Nc) :
    ‖cmp99SourcePi4CovarianceDifference K cell hc hmass hcoercive
        (singlePhysicalBondCochain source v0) target‖ ≤
      A0 * A1 *
        ((3 * CK * (cmp99PhysicalBondRangeBallBudget 4 R : ℝ) + |mass|) *
          (40000 * M ^ 4)) *
        Real.exp (-(2 * mu * (L : ℝ))) * ‖v0‖ := by
  have h :=
    cmp99SourcePi4CovarianceDifference_bilateralDecay_of_commonShellGap
      K cell R hrange hCK hkernel hc hmass hcoercive hC4 hCPi
        htarget hsource v0
  refine h.trans ?_
  gcongr
  exact_mod_cast card_cmp99SourcePi4CovarianceShell_le cell

end

end YangMills.RG
