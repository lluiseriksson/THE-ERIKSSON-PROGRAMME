/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq246FinePointSourceFibreGreen
import YangMills.RG.BalabanCMP89Eq251ComplexContourPhase

/-!
# Source-endpoint phase bound for CMP89 (2.46)

The normalized fine point source in (2.46) carries the negative Fourier
phase.  This module derives its strip growth from the already sealed
alias-independent contour-phase estimate by applying that estimate to the
negated source displacement.  Reciprocal aliases are real, so no alias
cardinality enters the bound.

This is only the first item of the post-synthesis Eq. (2.46) bridge.  It does
not bound the stabilized fibre solution, construct the continuous Green
kernel, prove CMP89 (2.42), produce uniform `B0`/`delta0`, attain window 15,
move `20/41`, or construct a `TermSource`.

Cold compiler evidence for exact source checkpoint
`00ca45e5544f44566bdf7d3e9339b813774f4e2b` is recorded in Verification
Ledger Addendum 1020. The focal and its exact axiom audit passed in a fresh
Colab Pro+ CPU checkout without restoring a project `.lake/build`.
-/

namespace YangMills.RG

noncomputable section

/-- The literal negative point-source Fourier phase has the same
alias-independent strip-growth budget as the positive phase, because it is
the positive phase evaluated at the negated physical displacement. -/
theorem norm_cmp89Eq246FinePointSourceAliasVector_le_growth
    {d L j : ℕ} {rho : ℝ} {z : Fin d → ℂ}
    (himag : ∀ mu, |(z mu).im| ≤ rho)
    (sourceEndpoint : Fin d → ℝ) (n : CMP89Eq246AliasIndex d L j) :
    ‖cmp89Eq246FinePointSourceAliasVector
        d L j z sourceEndpoint n‖ ≤
      cmp89Eq251ContourPhaseGrowth rho sourceEndpoint := by
  have h :=
    norm_exp_I_cmp89Eq251EntireAliasPhase_le_growth
      (z := z) himag n.1 (fun mu => -sourceEndpoint mu)
  simpa [cmp89Eq246FinePointSourceAliasVector,
    cmp89Eq251ContourPhaseGrowth, cmp89Eq251DisplacementL1,
    cmp89Eq251EntirePhase] using h

end

end YangMills.RG
