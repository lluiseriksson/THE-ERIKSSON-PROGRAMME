import YangMills.RG.BalabanCMP89Eq248FineLatticeNormalizedFourierGreen
import YangMills.RG.BalabanCMP99SourceFlatQprimeEndpointPhase

/-!
# Cold-sealed source-faithful typed CMP89 (2.48) kernel

The source and its two-declaration audit were materialized from exact source
checkpoint `342c232fbbbb961ea8df3b8620e7681a7b557215` in a fresh Colab
CPU/high-RAM checkout on 2026-09-01.  The focal completed `8575/8575` jobs
and the audit used only `{propext, Classical.choice, Quot.sound}`.

CMP89 (2.48) is the kernel of `G_j Q_j^*`, not the full fine-to-fine Green
kernel used in CMP89 (2.42).  Its output endpoint is on the fine lattice and
its input endpoint is on the unit/coarse lattice.  Keeping those two endpoint
types distinct forces the physical displacement `x - L^j y` and prevents the
same-scale `x-y` substitution ruled out by
`BalabanCMP89Eq248SameScaleEndpointNoGo`.
-/

namespace YangMills.RG

open YangMills

noncomputable section

variable {N' : ℕ}

/-- Literal normalized CMP89 (2.48) kernel with its source-faithful endpoint
types visible: a fine output site and a coarse source site.  The negative of
the repository's coarse-to-fine displacement is exactly `x - L^j y`. -/
def cmp89Eq248PhysicalFineToCoarseGreenQprimeStar
    (L j : ℕ) [NeZero L] (mass a : ℝ)
    (x : FinBox 4 (L ^ j * N')) (y : FinBox 4 N') : ℂ :=
  cmp89Eq248NormalizedFineLatticeStabilizedFourierGreen L j mass a
    (fun mu =>
      -cmp99SourceFlatQprimeFineToCoarseEndpointDisplacement
        (L ^ j) x y mu)

/-- The typed kernel is definitionally the normalized Eq. (2.48) integral at
the literal fine-lattice displacement `x - L^j y`. -/
theorem cmp89Eq248PhysicalFineToCoarseGreenQprimeStar_eq_normalized
    (L j : ℕ) [NeZero L] (mass a : ℝ)
    (x : FinBox 4 (L ^ j * N')) (y : FinBox 4 N') :
    cmp89Eq248PhysicalFineToCoarseGreenQprimeStar L j mass a x y =
      cmp89Eq248NormalizedFineLatticeStabilizedFourierGreen L j mass a
        (fun mu =>
          -cmp99SourceFlatQprimeFineToCoarseEndpointDisplacement
            (L ^ j) x y mu) := by
  rfl

end

end YangMills.RG
