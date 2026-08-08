import YangMills.RG.BalabanCMP116FourFactorSecondDerivative
import YangMills.RG.BalabanCMP116FourFactorLipschitz

/-!
# Direct mixed variation of an ordered four-factor product

The quadratic second-variation formula is convenient for differentiation but
not for sharp bilinear estimates.  This module expands its polarization once
and for all.  The result has four diagonal mixed terms and six ordered
cross-pairs, each cross-pair retaining both orders of the two directions.
-/

namespace YangMills.RG

open Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {Nc : ℕ} [NeZero Nc]

/-- Direct bilinear mixed second variation of four ordered factors.

`YAB i` is the mixed second variation of factor `i`, while `XA i` and
`XB i` are its first variations in the two directions.
-/
def fourFactorMixed
    (W XA XB YAB : Fin 4 → Matrix (Fin Nc) (Fin Nc) ℂ) :
    Matrix (Fin Nc) (Fin Nc) ℂ :=
  ((YAB 0 * W 1) * W 2) * W 3 +
  (((XA 0 * XB 1 + XB 0 * XA 1) * W 2) * W 3) +
  (((XA 0 * W 1) * XB 2 + (XB 0 * W 1) * XA 2) * W 3) +
  (((XA 0 * W 1) * W 2) * XB 3 +
    ((XB 0 * W 1) * W 2) * XA 3) +
  ((W 0 * YAB 1) * W 2) * W 3 +
  (((W 0 * XA 1) * XB 2 + (W 0 * XB 1) * XA 2) * W 3) +
  (((W 0 * XA 1) * W 2) * XB 3 +
    ((W 0 * XB 1) * W 2) * XA 3) +
  ((W 0 * W 1) * YAB 2) * W 3 +
  (((W 0 * W 1) * XA 2) * XB 3 +
    ((W 0 * W 1) * XB 2) * XA 3) +
  ((W 0 * W 1) * W 2) * YAB 3

/-- The direct mixed formula is exactly twice the polarization numerator of
the quadratic four-factor second variation.

The combined single-factor second variation is
`YA + YB + 2 • YAB`; hence division by two in polarization leaves precisely
one copy of each diagonal mixed term.
-/
theorem two_smul_fourFactorMixed_eq_polarization
    (W XA XB YA YB YAB :
      Fin 4 → Matrix (Fin Nc) (Fin Nc) ℂ) :
    2 • fourFactorMixed W XA XB YAB =
      fourFactorSecond W (XA + XB) (YA + YB + 2 • YAB) -
      fourFactorSecond W XA YA -
      fourFactorSecond W XB YB := by
  simp only [fourFactorMixed, fourFactorSecond, Pi.add_apply, Pi.smul_apply,
    two_smul]
  noncomm_ring

/-- Symmetry in the two first-variation directions. -/
theorem fourFactorMixed_symm
    (W XA XB YAB : Fin 4 → Matrix (Fin Nc) (Fin Nc) ℂ) :
    fourFactorMixed W XA XB YAB =
      fourFactorMixed W XB XA YAB := by
  simp only [fourFactorMixed]
  noncomm_ring

end

end YangMills.RG
