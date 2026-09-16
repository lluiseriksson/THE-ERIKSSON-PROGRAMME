/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99Eq389CovariantLinkDerivative

/-!
# The first regional-Green species in CMP99 (3.89)

Compiler-verified at exact source checkpoint
`ec36dd107c2dbfd2db003c331dce23d4d787b683` by cold GitHub Actions run
`31058984443`.  The focal completed 8,520 jobs and the audited declaration
uses exactly `[propext, Classical.choice, Quot.sound]`.

This module consumes the literal left covariant-derivative component of the
sealed CMP99 (3.42) regional-Green certificate.  It applies that estimate to
the eight oriented bonds incident to one output site and retains their exact
block-scale distances.  The neighboring distances are not silently replaced
by the central distance; that geometric transport is the next named step.

No Combes--Thomas estimate, Schur bound, Poincare constant, operator norm or
cell cardinality occurs.  This is the first Green-dependent component of the
direct CMP99 (3.89) route, not yet the common-metric pointwise bound, the sum
of all three species, or the contraction `norm R' < 1`.
-/

namespace YangMills.RG

open YangMills
open scoped BigOperators RealInnerProductSpace

noncomputable section

variable {m q Nc : ℕ} [NeZero m] [NeZero q] [NeZero Nc]

/-- The literal link-derivative species applied to one regional Green probe is
bounded by the eight exact CMP99 (3.42) derivative entries.

The output deliberately keeps the four shifted block distances.  Collapsing
them to one central source distance requires a separate block-geometry lemma
and is not smuggled into this analytic step. -/
theorem norm_cmp99CovariantCutoffLinkDerivative_regionalGreen_one_le
    (Omega : ActiveGaugeRegion 4 (m * (2 * q)))
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground 4 (m * (2 * q)) Nc)
    (K : GaugeZeroCochain 4 (m * (2 * q)) (SUNLieCoord Nc) →L[ℝ]
      GaugeZeroCochain 4 (m * (2 * q)) (SUNLieCoord Nc))
    (c : ℝ) (hc : 0 < c) (hKcoer : IsCoerciveCLM K c)
    (B0 delta0 ell : ℝ)
    (C : CMP99Eq342RegionalGreenCertificate Omega rho U 1 K c hc hKcoer
      B0 delta0 ell)
    (h : FinBox 4 (m * (2 * q)) → ℝ)
    (source : ActiveGaugeRegion.Site Omega) (v : SUNLieCoord Nc)
    (x : FinBox 4 (m * (2 * q))) (slope : ℝ) (hslope : 0 ≤ slope)
    (hforward : ∀ i : Fin 4, ‖h x - h (x.shift i)‖ ≤ slope)
    (hback : ∀ i : Fin 4, ‖h x - h (x.shiftBack i)‖ ≤ slope) :
    ‖cmp99CovariantCutoffLinkDerivative rho U 1 h
        (extendZeroZeroCLM Omega
          (cmp99RegionalDirichletGreen Omega K hc hKcoer
            (singleFinitePiLp source v))) x‖ ≤
      slope * ∑ i : Fin 4,
        ((B0 * ell) *
              Real.exp (-(delta0 *
                (cmp99Eq342RescaledBlockDist m q x source.1 : ℝ))) * ‖v‖ +
          (B0 * ell) *
              Real.exp (-(delta0 *
                (cmp99Eq342RescaledBlockDist m q (x.shiftBack i)
                  source.1 : ℝ))) * ‖v‖) := by
  let phi : PhysicalGaugeZeroCochain 4 (m * (2 * q)) Nc :=
    extendZeroZeroCLM Omega
      (cmp99RegionalDirichletGreen Omega K hc hKcoer
        (singleFinitePiLp source v))
  have hforwardD (i : Fin 4) :
      ‖covariantD0CLM rho U phi ((x, i) : PhysicalBond 4 (m * (2 * q)))‖ ≤
        (B0 * ell) *
          Real.exp (-(delta0 *
            (cmp99Eq342RescaledBlockDist m q x source.1 : ℝ))) * ‖v‖ := by
    have hD := C.left_derivative_bound.2.2 source
      ((x, i) : PhysicalBond 4 (m * (2 * q))) v
    simpa [phi, cmp99ActiveRegionSourceCovariantD0CLM] using hD
  have hbackD (i : Fin 4) :
      ‖covariantD0CLM rho U phi
          ((x.shiftBack i, i) : PhysicalBond 4 (m * (2 * q)))‖ ≤
        (B0 * ell) *
          Real.exp (-(delta0 *
            (cmp99Eq342RescaledBlockDist m q (x.shiftBack i)
              source.1 : ℝ))) * ‖v‖ := by
    have hD := C.left_derivative_bound.2.2 source
      ((x.shiftBack i, i) : PhysicalBond 4 (m * (2 * q))) v
    simpa [phi, cmp99ActiveRegionSourceCovariantD0CLM] using hD
  calc
    ‖cmp99CovariantCutoffLinkDerivative rho U 1 h phi x‖ ≤
        slope * ∑ i : Fin 4,
          (‖covariantD0CLM rho U phi
              ((x, i) : PhysicalBond 4 (m * (2 * q)))‖ +
            ‖covariantD0CLM rho U phi
              ((x.shiftBack i, i) : PhysicalBond 4 (m * (2 * q)))‖) :=
      norm_cmp99CovariantCutoffLinkDerivative_one_le rho U h phi x slope
        hforward hback
    _ ≤ slope * ∑ i : Fin 4,
        ((B0 * ell) *
              Real.exp (-(delta0 *
                (cmp99Eq342RescaledBlockDist m q x source.1 : ℝ))) * ‖v‖ +
          (B0 * ell) *
              Real.exp (-(delta0 *
                (cmp99Eq342RescaledBlockDist m q (x.shiftBack i)
                  source.1 : ℝ))) * ‖v‖) := by
      apply mul_le_mul_of_nonneg_left _ hslope
      apply Finset.sum_le_sum
      intro i _hi
      exact add_le_add (hforwardD i) (hbackD i)

end

end YangMills.RG
