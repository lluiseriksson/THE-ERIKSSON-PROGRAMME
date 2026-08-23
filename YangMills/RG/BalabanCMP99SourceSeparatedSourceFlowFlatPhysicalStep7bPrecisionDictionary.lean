/-
PRE-VALIDATION -- source present; `.olean` not yet materialized and the
result is not yet compiler-verified.
-/

/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceSeparatedSourceFlowFlatAmbientGreenComplexification
import YangMills.RG.BalabanCMP99SourceSeparatedSourceFlowFlatPhysicalPrecisionDictionary
import YangMills.RG.BalabanCMP99SourceSeparatedGeneratedFlatPhysicalStep7bCarrier
import YangMills.RG.BalabanCMP99SourceFlowFlatPhysicalPrecisionComplexDictionary

/-!
# Source-flow separated Step-7b precision dictionary

The canonical complexification of the literal source-flow separated ambient
precision is identified with the full-box Step-7b precision carrying
`cmp99SourceFlowFlatFullComplexA a L depth`.  No complex precision equality or
inverse is accepted from the caller.
-/

namespace YangMills.RG

open YangMills

noncomputable section

variable {L K Q Nc : ℕ}
variable [NeZero L] [NeZero K] [NeZero Q] [NeZero Nc]

/-- Literal source-flow full-box precision transported to the separated
ambient carrier only after the physical block/coarse factorization is fixed. -/
noncomputable def
    cmp99SourceSeparatedSourceFlowFlatPhysicalStep7bAmbientPrecisionCLM
    (depth : ℕ) (a : ℝ) :
    (FinBox 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)) →
      SUNLieComplexCoord Nc) →L[ℂ]
    (FinBox 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)) →
      SUNLieComplexCoord Nc) :=
  let U :=
    cmp99SourceSeparatedGeneratedPhysicalStep7bFieldEquiv L K Q Nc depth
  U.symm.toContinuousLinearMap.comp
    ((cmp99SourceFlatFullComplexPrecisionCLM
      (d := 4) (M := L ^ (depth + 1)) (N' := 2 * (K * Q))
      (Nc := Nc) 0 (cmp99SourceFlowFlatFullComplexA a L depth)).comp
        U.toContinuousLinearMap)

private theorem sourceFlowSeparatedAmbientPrecisionComplex_apply_ofReal
    (hL : 2 ≤ L) (depth : ℕ) (a : ℝ)
    (phi : GaugeZeroCochain 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
      (SUNLieCoord Nc)) :
    cmp99SourceSeparatedSourceFlowFlatAmbientPrecisionComplex
        (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth a
        (fun x => cmp99SUNLieCoordComplexificationLM Nc (phi x)) =
      fun x => cmp99SUNLieCoordComplexificationLM Nc
        (cmp99SourceSeparatedSourceFlowFlatAmbientPrecision
          (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth a phi x) := by
  let P := cmp99SourceSeparatedSourceFlowFlatAmbientPrecision
    (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth a
  have hinput :
      (fun x => cmp99SUNLieCoordComplexificationLM Nc (phi x)) =
        finitePiLpComplexOuterEquiv (finitePiLpComplexOfReal phi) := by
    funext x
    ext b
    rfl
  have houtput :
      (fun x => cmp99SUNLieCoordComplexificationLM Nc (P phi x)) =
        finitePiLpComplexOuterEquiv (finitePiLpComplexOfReal (P phi)) := by
    funext x
    ext b
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

private theorem sourceFlowSeparatedAmbientPrecision_apply_eq_explicit
    (hL : 2 ≤ L) (depth : ℕ) (a : ℝ)
    (phi : GaugeZeroCochain 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
      (SUNLieCoord Nc))
    (x : FinBox 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))) :
    cmp99SourceSeparatedSourceFlowFlatAmbientPrecision
        (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth a phi x =
      cmp99SourceSeparatedSourceFlowFlatFinePrecisionExplicit
        (L := L) (K := K) (Q := Q) (Nc := Nc) depth a
        (cmp99SourceSeparatedGeneratedPhysicalTerminalDataOfAmbient
          (L := L) (K := K) (Q := Q) (Nc := Nc) depth phi).activeField
        ((cmp99SourceSeparatedGeneratedPhysicalFullSiteEquiv
          L K Q depth).symm x) := by
  rw [cmp99SourceSeparatedSourceFlowFlatAmbientPrecision_eq_reindexExplicit]
  rfl

omit [NeZero Nc] in
private theorem sourceFlowSeparatedStep7bAmbientPrecisionCLM_apply
    (depth : ℕ) (a : ℝ)
    (z : FinBox 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)) →
      SUNLieComplexCoord Nc)
    (x : FinBox 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))) :
    cmp99SourceSeparatedSourceFlowFlatPhysicalStep7bAmbientPrecisionCLM
        (L := L) (K := K) (Q := Q) (Nc := Nc) depth a z x =
      cmp99SourceFlatFullComplexPrecisionAction
        (M := L ^ (depth + 1)) (N' := 2 * (K * Q)) 0
        (cmp99SourceFlowFlatFullComplexA a L depth)
        (cmp99SourceSeparatedGeneratedPhysicalStep7bFieldEquiv
          L K Q Nc depth z)
        (cmp99GeneratedFineBoxOneBlockEquiv
          (d := 4) L (2 * (K * Q)) (depth + 1)
          ((cmp99SourceSeparatedGeneratedPhysicalFullSiteEquiv
            L K Q depth).symm x).1) := by
  simp only [cmp99SourceSeparatedSourceFlowFlatPhysicalStep7bAmbientPrecisionCLM,
    ContinuousLinearMap.comp_apply,
    cmp99SourceFlatFullComplexPrecisionCLM_apply]
  rfl

/-- The complexified literal source-flow ambient precision agrees with the
transported full-box precision on every ambient real field. -/
theorem
    cmp99SourceSeparatedSourceFlowFlatAmbientPrecisionComplex_apply_ofReal
    (hL : 2 ≤ L) (depth : ℕ) (a : ℝ)
    (phi : GaugeZeroCochain 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
      (SUNLieCoord Nc)) :
    cmp99SourceSeparatedSourceFlowFlatAmbientPrecisionComplex
        (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth a
        (fun x => cmp99SUNLieCoordComplexificationLM Nc (phi x)) =
      cmp99SourceSeparatedSourceFlowFlatPhysicalStep7bAmbientPrecisionCLM
        (L := L) (K := K) (Q := Q) (Nc := Nc) depth a
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
      cmp99SourceSeparatedSourceFlowFlatAmbientPrecisionComplex
          (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth a
          (fun x => cmp99SUNLieCoordComplexificationLM Nc (phi x)) =
        fun x => cmp99SUNLieCoordComplexificationLM Nc
          (cmp99SourceSeparatedSourceFlowFlatAmbientPrecision
            (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth a phi x) := by
    exact sourceFlowSeparatedAmbientPrecisionComplex_apply_ofReal
      (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth a phi
  apply funext
  intro x
  rw [congrFun hambient x]
  have hreal :
      cmp99SourceSeparatedSourceFlowFlatAmbientPrecision
          (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth a phi x =
        cmp99SourceSeparatedSourceFlowFlatFinePrecisionExplicit
          (L := L) (K := K) (Q := Q) (Nc := Nc) depth a
          D.activeField (eFull.symm x) := by
    exact sourceFlowSeparatedAmbientPrecision_apply_eq_explicit
      (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth a phi x
  have hphysical :=
    D.sourceFlowPhysicalPrecision_complexification_eq_fullComplexAction
      a (eFull.symm x)
  rw [hfield] at hphysical
  have hstep :
      cmp99SourceSeparatedSourceFlowFlatPhysicalStep7bAmbientPrecisionCLM
          (L := L) (K := K) (Q := Q) (Nc := Nc) depth a
          (fun x => cmp99SUNLieCoordComplexificationLM Nc (phi x)) x =
        cmp99SourceFlatFullComplexPrecisionAction
          (M := L ^ (depth + 1)) (N' := 2 * (K * Q)) 0
          (cmp99SourceFlowFlatFullComplexA a L depth)
          (U (fun x => cmp99SUNLieCoordComplexificationLM Nc (phi x)))
          (cmp99GeneratedFineBoxOneBlockEquiv
            (d := 4) L (2 * (K * Q)) (depth + 1) (eFull.symm x).1) := by
    exact sourceFlowSeparatedStep7bAmbientPrecisionCLM_apply
      (L := L) (K := K) (Q := Q) (Nc := Nc) depth a
      (fun x => cmp99SUNLieCoordComplexificationLM Nc (phi x)) x
  rw [hreal]
  exact hphysical.trans hstep.symm

/-- Exact source-flow Step-7b operator dictionary, extended from the real
slice by complex linearity. -/
theorem
    cmp99SourceSeparatedSourceFlowFlatAmbientPrecisionComplex_eq_step7b
    (hL : 2 ≤ L) (depth : ℕ) (a : ℝ) :
    cmp99SourceSeparatedSourceFlowFlatAmbientPrecisionComplex
        (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth a =
      cmp99SourceSeparatedSourceFlowFlatPhysicalStep7bAmbientPrecisionCLM
        (L := L) (K := K) (Q := Q) (Nc := Nc) depth a := by
  apply ContinuousLinearMap.ext
  intro z
  let xr : GaugeZeroCochain 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
      (SUNLieCoord Nc) :=
    WithLp.toLp 2 fun x => WithLp.toLp 2 fun b => (z x b).re
  let xi : GaugeZeroCochain 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))
      (SUNLieCoord Nc) :=
    WithLp.toLp 2 fun x => WithLp.toLp 2 fun b => (z x b).im
  have hz : z =
      (fun x => cmp99SUNLieCoordComplexificationLM Nc (xr x)) +
        Complex.I •
          (fun x => cmp99SUNLieCoordComplexificationLM Nc (xi x)) := by
    funext x
    ext b
    simpa [xr, xi, mul_comm] using (Complex.re_add_im (z x b)).symm
  rw [hz, map_add, map_add, map_smul, map_smul]
  rw [
    cmp99SourceSeparatedSourceFlowFlatAmbientPrecisionComplex_apply_ofReal
      (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth a xr,
    cmp99SourceSeparatedSourceFlowFlatAmbientPrecisionComplex_apply_ofReal
      (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth a xi]

end

end YangMills.RG
