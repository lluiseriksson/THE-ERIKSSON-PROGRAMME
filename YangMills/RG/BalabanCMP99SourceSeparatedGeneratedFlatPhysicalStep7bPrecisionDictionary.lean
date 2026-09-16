/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceSeparatedGeneratedFlatPhysicalAmbientGreenComplexification
import YangMills.RG.BalabanCMP99SourceSeparatedGeneratedFlatPhysicalStep7bCarrier
import YangMills.RG.BalabanCMP99SourceFlatGeneratedPhysicalPrecisionComplexDictionary

/-!
# Source-separated generated Step-7b precision dictionary

This is Step 8b.24/S2b.  It proves, rather than assumes, that the canonical
complexification of the source-separated generated flat ambient precision is
the literal full-box Step-7b precision with fine block side `L^(depth+1)` and
coarse side `2*(K*Q)`.

No inverse, precision equality, regional estimate or terminal field is
accepted from the caller.
-/

namespace YangMills.RG

open YangMills

noncomputable section

variable {L K Q Nc : ℕ}
variable [NeZero L] [NeZero K] [NeZero Q] [NeZero Nc]

private theorem separatedAmbientPrecisionComplex_apply_ofReal
    (hL : 2 ≤ L) (depth : ℕ)
    (phi : GaugeZeroCochain 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
      (SUNLieCoord Nc)) :
    cmp99SourceSeparatedGeneratedFlatPhysicalAmbientPrecisionComplex
        (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth
        (fun x => cmp99SUNLieCoordComplexificationLM Nc (phi x)) =
      fun x => cmp99SUNLieCoordComplexificationLM Nc
        (cmp99SourceSeparatedGeneratedFlatPhysicalAmbientPrecision
          (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth phi x) := by
  let P := cmp99SourceSeparatedGeneratedFlatPhysicalAmbientPrecision
    (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth
  have hinput :
      (fun x => cmp99SUNLieCoordComplexificationLM Nc (phi x)) =
        finitePiLpComplexOuterEquiv (finitePiLpComplexOfReal phi) := by
    funext x
    ext a
    rfl
  have houtput :
      (fun x => cmp99SUNLieCoordComplexificationLM Nc (P phi x)) =
        finitePiLpComplexOuterEquiv (finitePiLpComplexOfReal (P phi)) := by
    funext x
    ext a
    rfl
  rw [hinput, houtput]
  change finitePiLpComplexOuterEquiv
      (finitePiLpCanonicalComplexificationCLM P
        (finitePiLpComplexOuterEquiv.symm
          (finitePiLpComplexOuterEquiv
            (finitePiLpComplexOfReal phi)))) =
    finitePiLpComplexOuterEquiv (finitePiLpComplexOfReal (P phi))
  rw [ContinuousLinearEquiv.symm_apply_apply,
    finitePiLpCanonicalComplexificationCLM_ofReal]

private theorem separatedAmbientPrecision_apply_eq_explicit
    (hL : 2 ≤ L) (depth : ℕ)
    (phi : GaugeZeroCochain 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
      (SUNLieCoord Nc))
    (x : FinBox 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))) :
    cmp99SourceSeparatedGeneratedFlatPhysicalAmbientPrecision
        (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth phi x =
      cmp99SourceGeneratedFlatPhysicalPrecisionExplicit
        (d := 4) (M := L) (N := 2 * (K * Q)) (Nc := Nc)
        (cmp99SourceSeparatedGeneratedPhysicalFullCoarseRegion K Q) depth
        (cmp99SourceGeneratedFullComplexSpacing L (depth + 1))
        (cmp99SourceSeparatedGeneratedPhysicalTerminalDataOfAmbient
          (L := L) (K := K) (Q := Q) (Nc := Nc) depth phi).activeField
        ((cmp99SourceSeparatedGeneratedPhysicalFullSiteEquiv
          L K Q depth).symm x) := by
  rw [cmp99SourceSeparatedGeneratedFlatPhysicalAmbientPrecision_eq_reindex,
    cmp99SourceGeneratedFlatPhysicalPrecision_eq_explicit]
  rfl

omit [NeZero Nc] in
private theorem separatedStep7bAmbientPrecisionCLM_apply
    (depth : ℕ)
    (z : FinBox 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)) →
      SUNLieComplexCoord Nc)
    (x : FinBox 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))) :
    cmp99SourceSeparatedGeneratedFlatPhysicalStep7bAmbientPrecisionCLM
        (L := L) (K := K) (Q := Q) (Nc := Nc) depth z x =
      cmp99SourceFlatFullComplexPrecisionAction
        (M := L ^ (depth + 1)) (N' := 2 * (K * Q)) 0
        (cmp99SourceGeneratedFullComplexA 4 L (depth + 1)
          (cmp99SourceGeneratedFullComplexSpacing L (depth + 1)) 0)
        (cmp99SourceSeparatedGeneratedPhysicalStep7bFieldEquiv
          L K Q Nc depth z)
        (cmp99GeneratedFineBoxOneBlockEquiv
          (d := 4) L (2 * (K * Q)) (depth + 1)
          ((cmp99SourceSeparatedGeneratedPhysicalFullSiteEquiv
            L K Q depth).symm x).1) := by
  simp only [cmp99SourceSeparatedGeneratedFlatPhysicalStep7bAmbientPrecisionCLM,
    ContinuousLinearMap.comp_apply,
    cmp99SourceFlatFullComplexPrecisionCLM_apply]
  rfl

/-- The complexified separated ambient precision agrees with the transported
literal Step-7b precision on every ambient real field. -/
theorem
    cmp99SourceSeparatedGeneratedFlatPhysicalAmbientPrecisionComplex_apply_ofReal
    (hL : 2 ≤ L) (depth : ℕ)
    (phi : GaugeZeroCochain 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
      (SUNLieCoord Nc)) :
    cmp99SourceSeparatedGeneratedFlatPhysicalAmbientPrecisionComplex
        (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth
        (fun x => cmp99SUNLieCoordComplexificationLM Nc (phi x)) =
      cmp99SourceSeparatedGeneratedFlatPhysicalStep7bAmbientPrecisionCLM
        (L := L) (K := K) (Q := Q) (Nc := Nc) depth
        (fun x => cmp99SUNLieCoordComplexificationLM Nc (phi x)) := by
  classical
  let D := cmp99SourceSeparatedGeneratedPhysicalTerminalDataOfAmbient
    (L := L) (K := K) (Q := Q) (Nc := Nc) depth phi
  let eFull :=
    cmp99SourceSeparatedGeneratedPhysicalFullSiteEquiv L K Q depth
  let U :=
    cmp99SourceSeparatedGeneratedPhysicalStep7bFieldEquiv L K Q Nc depth
  have hfield : D.complexZeroExtension =
      U (fun x => cmp99SUNLieCoordComplexificationLM Nc (phi x)) :=
    cmp99SourceSeparatedGeneratedPhysicalTerminalDataOfAmbient_complexZeroExtension
      (L := L) (K := K) (Q := Q) (Nc := Nc) depth phi
  have hambient :
      cmp99SourceSeparatedGeneratedFlatPhysicalAmbientPrecisionComplex
          (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth
          (fun x => cmp99SUNLieCoordComplexificationLM Nc (phi x)) =
        fun x => cmp99SUNLieCoordComplexificationLM Nc
          (cmp99SourceSeparatedGeneratedFlatPhysicalAmbientPrecision
            (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth phi x) := by
    exact separatedAmbientPrecisionComplex_apply_ofReal
      (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth phi
  apply funext
  intro x
  rw [congrFun hambient x]
  have hreal :
      cmp99SourceSeparatedGeneratedFlatPhysicalAmbientPrecision
          (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth phi x =
        cmp99SourceGeneratedFlatPhysicalPrecisionExplicit
          (d := 4) (M := L) (N := 2 * (K * Q)) (Nc := Nc)
          (cmp99SourceSeparatedGeneratedPhysicalFullCoarseRegion K Q) depth
          (cmp99SourceGeneratedFullComplexSpacing L (depth + 1))
          D.activeField (eFull.symm x) := by
    exact separatedAmbientPrecision_apply_eq_explicit
      (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth phi x
  have hphysical :=
    D.physicalPrecision_complexification_eq_fullComplexAction (eFull.symm x)
  rw [hfield] at hphysical
  have hstep :
      cmp99SourceSeparatedGeneratedFlatPhysicalStep7bAmbientPrecisionCLM
          (L := L) (K := K) (Q := Q) (Nc := Nc) depth
          (fun x => cmp99SUNLieCoordComplexificationLM Nc (phi x)) x =
        cmp99SourceFlatFullComplexPrecisionAction
          (M := L ^ (depth + 1)) (N' := 2 * (K * Q)) 0
          (cmp99SourceGeneratedFullComplexA 4 L (depth + 1)
            (cmp99SourceGeneratedFullComplexSpacing L (depth + 1)) 0)
          (U (fun x => cmp99SUNLieCoordComplexificationLM Nc (phi x)))
          (cmp99GeneratedFineBoxOneBlockEquiv
            (d := 4) L (2 * (K * Q)) (depth + 1) (eFull.symm x).1) := by
    exact separatedStep7bAmbientPrecisionCLM_apply
      (L := L) (K := K) (Q := Q) (Nc := Nc) depth
      (fun x => cmp99SUNLieCoordComplexificationLM Nc (phi x)) x
  rw [hreal]
  exact hphysical.trans hstep.symm

/-- Exact source-separated Step-7b physical dictionary.  The operator
equality is derived from the pointwise source dictionary and complex
linearity. -/
theorem
    cmp99SourceSeparatedGeneratedFlatPhysicalAmbientPrecisionComplex_eq_step7b
    (hL : 2 ≤ L) (depth : ℕ) :
    cmp99SourceSeparatedGeneratedFlatPhysicalAmbientPrecisionComplex
        (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth =
      cmp99SourceSeparatedGeneratedFlatPhysicalStep7bAmbientPrecisionCLM
        (L := L) (K := K) (Q := Q) (Nc := Nc) depth := by
  apply ContinuousLinearMap.ext
  intro z
  let xr : GaugeZeroCochain 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
      (SUNLieCoord Nc) :=
    WithLp.toLp 2 fun x => WithLp.toLp 2 fun a => (z x a).re
  let xi : GaugeZeroCochain 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
      (SUNLieCoord Nc) :=
    WithLp.toLp 2 fun x => WithLp.toLp 2 fun a => (z x a).im
  have hz : z =
      (fun x => cmp99SUNLieCoordComplexificationLM Nc (xr x)) +
        Complex.I •
          (fun x => cmp99SUNLieCoordComplexificationLM Nc (xi x)) := by
    funext x
    ext a
    simpa [xr, xi, mul_comm] using (Complex.re_add_im (z x a)).symm
  rw [hz, map_add, map_add, map_smul, map_smul]
  rw [
    cmp99SourceSeparatedGeneratedFlatPhysicalAmbientPrecisionComplex_apply_ofReal
      (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth xr,
    cmp99SourceSeparatedGeneratedFlatPhysicalAmbientPrecisionComplex_apply_ofReal
      (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth xi]

end

end YangMills.RG
