/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SectionCPhysicalBallBudget
import YangMills.RG.BalabanCMP99SourcePi4CollarDomain
import YangMills.RG.BalabanCMP99SourceCellDomains

/-!
# The literal `Pi^4`-versus-`Pi` covariance-support pair

CMP99 Section C modifies a source partition by replacing a base cube with a
larger concentric cube and displays covariance differences between the two
localizations.  This file instantiates the support-level model already used by
`cmp99SectionCCovarianceDifference` with the two source domains that have been
constructed literally in Lean:

* the singleton source cell `Pi`;
* its printed Chebyshev-radius-two collar `Pi^4`.

Both supports use the physical bilateral convention: the source and target
blocks of a bond must lie in the domain.  The inclusion `Pi subset Pi^4` is
proved and consumed internally by the covariance estimate.

Honest scope: this is the literal finite-support realization of the
`Pi^4`-versus-`Pi` pair.  It does not identify these hard-support covariances
with the full propagators constructed in CMP99 from the sequences
`Omega_n(Pi)`; that operator dictionary remains a separate source obligation.
-/

namespace YangMills.RG

noncomputable section

private abbrev PhysicalEndomorphism (d N Nc : ℕ) [NeZero N] :=
  PhysicalGaugeOneCochain d N Nc →L[ℝ]
    PhysicalGaugeOneCochain d N Nc

/-- Bilateral physical bond support of the singleton source cell `Pi`. -/
noncomputable def cmp99SourcePiPhysicalBondSupport
    {M Q : ℕ} [NeZero M] [NeZero Q] (cell : FinBox 4 Q) :
    Finset (PhysicalBond 4 (M * (2 * Q))) :=
  cmp99SourceDomainPhysicalBondSupport (M := M)
    (cmp99SourceSingletonDomain cell)

/-- Bilateral physical bond support of the literal source collar `Pi^4`. -/
noncomputable def cmp99SourcePi4PhysicalBondSupport
    {M Q : ℕ} [NeZero M] [NeZero Q] (cell : FinBox 4 Q) :
    Finset (PhysicalBond 4 (M * (2 * Q))) :=
  cmp99SourceDomainPhysicalBondSupport (M := M)
    (cmp99SourcePi4CollarDomain cell)

/-- Every bond supported bilaterally by `Pi` is supported bilaterally by its
literal `Pi^4` collar. -/
theorem cmp99SourcePiPhysicalBondSupport_subset_pi4
    {M Q : ℕ} [NeZero M] [NeZero Q] (cell : FinBox 4 Q) :
    cmp99SourcePiPhysicalBondSupport (M := M) cell ⊆
      cmp99SourcePi4PhysicalBondSupport cell := by
  intro bond hbond
  rw [cmp99SourcePiPhysicalBondSupport,
    mem_cmp99SourceDomainPhysicalBondSupport_iff,
    cmp99SourceSingletonDomain_blocks] at hbond
  rw [cmp99SourcePi4PhysicalBondSupport,
    mem_cmp99SourceDomainPhysicalBondSupport_iff]
  have hcell : cell ∈ (cmp99SourcePi4CollarDomain cell).blocks := by
    rw [cmp99SourcePi4CollarDomain_blocks]
    exact mem_cmp99SourcePi4CollarCells_self cell
  have hsource := Finset.mem_singleton.mp hbond.1
  have htarget := Finset.mem_singleton.mp hbond.2
  exact ⟨hsource ▸ hcell, htarget ▸ hcell⟩

/-- The support-level covariance difference for the literal nested pair
`Pi subset Pi^4`. -/
noncomputable def cmp99SourcePi4CovarianceDifference
    {M Q Nc : ℕ} [NeZero M] [NeZero Q]
    (K : PhysicalEndomorphism 4 (M * (2 * Q)) Nc)
    (cell : FinBox 4 Q)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hcoercive : IsCoerciveCLM K c) :
    PhysicalEndomorphism 4 (M * (2 * Q)) Nc :=
  cmp99SectionCCovarianceDifference K
    (cmp99SourcePi4PhysicalBondSupport cell)
    (cmp99SourcePiPhysicalBondSupport (M := M) cell)
    hc hmass hcoercive

@[simp] theorem cmp99SourcePi4CovarianceDifference_apply
    {M Q Nc : ℕ} [NeZero M] [NeZero Q]
    (K : PhysicalEndomorphism 4 (M * (2 * Q)) Nc)
    (cell : FinBox 4 Q)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hcoercive : IsCoerciveCLM K c)
    (x : PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc) :
    cmp99SourcePi4CovarianceDifference K cell hc hmass hcoercive x =
      cmp99LocalizedPhysicalCovariance K
          (cmp99SourcePi4PhysicalBondSupport cell) hc hmass hcoercive x -
        cmp99LocalizedPhysicalCovariance K
          (cmp99SourcePiPhysicalBondSupport (M := M) cell)
          hc hmass hcoercive x :=
  rfl

/-- Full-rate common-collar decay for the literal support pair.  Both nesting
and the physical radius-`R` ball count are generated internally. -/
theorem cmp99SourcePi4CovarianceDifference_bilateralDecay_of_commonShellGap
    {M Q Nc : ℕ} [NeZero M] [NeZero Q]
    (K : PhysicalEndomorphism 4 (M * (2 * Q)) Nc)
    (cell : FinBox 4 Q)
    (R : ℕ) (hrange : PhysicalCovarianceFiniteRange K physicalBondDist R)
    {CK c mass A0 A1 mu : ℝ}
    (hCK : 0 ≤ CK)
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
          (cmp99SourcePi4PhysicalBondSupport cell \
            cmp99SourcePiPhysicalBondSupport (M := M) cell).card) *
        Real.exp (-(2 * mu * (L : ℝ))) * ‖v0‖ := by
  exact
    cmp99SectionCCovarianceDifference_bilateralDecay_of_commonShellGap_physicalBallBudget
      K (cmp99SourcePiPhysicalBondSupport_subset_pi4 cell)
        R hrange hCK hkernel hc hmass hcoercive hC4 hCPi
        htarget hsource v0

end

end YangMills.RG
