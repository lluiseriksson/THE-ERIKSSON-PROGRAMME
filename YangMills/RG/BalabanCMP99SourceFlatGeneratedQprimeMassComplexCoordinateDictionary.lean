/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceFlatGeneratedPrecisionScalarDictionary
import YangMills.RG.BalabanCMP99SourceFlatFullComplexQprimeMassCoordinateKernel

/-!
PRE-VALIDATION: source is present, its `.olean` has not yet been materialized,
and the result has not yet been verified by the Lean compiler.

# Complex coordinate dictionary for the generated flat `Q'^*Q'` mass

At generated depth `depth + 1`, the terminal one-block side is literally
`R = M^(depth+1)`.  The generated real counting adjoint contributes
`(R^-d)^2`, while the full-complex coefficient-one weighted adjoint
contributes one `R^-d` and its scalar coefficient contributes the other.

This file compares only those mass terms on a coordinate delta after the
explicit real-to-complex embedding.  It does not identify carriers,
Laplacians, full precisions, inverses or regional Green operators.
-/

namespace YangMills.RG

open YangMills

noncomputable section

variable {d M N Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N] [NeZero Nc]

/-- On a coordinate delta, the complexification of the generated counting
mass is exactly the one-block full-complex weighted-adjoint mass.  The two
normalization factors remain visible on their respective sides. -/
theorem cmp99SourceGeneratedCountingMass_complexCoordinateDictionary
    (Omega : ActiveGaugeRegion d N) (depth : ℕ)
    (spacing epsilon : ℝ)
    (source target : ActiveGaugeRegion.Site
      (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1)))
    (v : SUNLieCoord Nc) :
    let regions :=
      cmp99SourceIteratedLiftActiveRegionChain (M := M) Omega (depth + 1)
    let sourceBox := cmp99GeneratedFineBoxOneBlockEquiv
      (d := d) M N (depth + 1) source.1
    let targetBox := cmp99GeneratedFineBoxOneBlockEquiv
      (d := d) M N (depth + 1) target.1
    cmp99SUNLieCoordComplexificationLM Nc
        (cmp99SourceGeneratedPhysicalMass d M (depth + 1) spacing epsilon •
          (((regions.flatExplicitQprime (Nc := Nc)).adjoint.comp
            (regions.flatExplicitQprime (Nc := Nc)))
              (singleFinitePiLp source v) target)) =
      ((cmp99SourceGeneratedFullComplexA
          d M (depth + 1) spacing epsilon : ℝ) : ℂ) •
        cmp99SourceFlatFullComplexQprimeMass
          (M := M ^ (depth + 1)) (N' := N)
          (cmp99SourceFlatFullComplexSingle sourceBox
            (cmp99SUNLieCoordComplexificationLM Nc v)) targetBox := by
  classical
  dsimp only
  rw [cmp99SourceIteratedLift_flatExplicitCountingMass_single_apply_oneBlock]
  rw [cmp99SourceFlatFullComplexQprimeMass_single_apply]
  by_cases howner :
      blockSite (M ^ (depth + 1)) N
          (cmp99GeneratedFineBoxOneBlockEquiv
            (d := d) M N (depth + 1) target.1) =
        blockSite (M ^ (depth + 1)) N
          (cmp99GeneratedFineBoxOneBlockEquiv
            (d := d) M N (depth + 1) source.1)
  · rw [if_pos howner, if_pos howner]
    ext a
    simp only [cmp99SUNLieCoordComplexificationLM_apply, PiLp.smul_apply,
      RCLike.real_smul_eq_coe_smul, smul_eq_mul]
    push_cast
    rw [← cmp99SourceGeneratedFullComplexA_mul_weight_complex]
    ring
  · rw [if_neg howner, if_neg howner]
    simp

end

end YangMills.RG
