/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99GeneralizedWalkWeightedSplit
import YangMills.RG.BalabanCMP99PatchedParametrixFixedRateWalkDecay
import YangMills.RG.BalabanCMP116SourcePi4TerminalWalkFiniteSum
import YangMills.RG.PhysicalWeightedRowKernelMatrix

/-!
# Matrix bounds for a split source `Pi^4` walk

The factorwise physical weighted-row certificate is specialized here to the
literal source charts.  The prefix through any selected factor and the suffix
strictly after it are converted to matrix `L∞` bounds exactly once.  Their
amplitudes carry complementary powers of the continuation ratio.
-/

namespace YangMills.RG

noncomputable section

open scoped Matrix.Norms.Operator

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc →L[ℝ]
    PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

set_option maxHeartbeats 1000000 in

/-- The source-walk prefix through one literal factor has the exact
head-times-power matrix bound inherited from the physical weighted-row
certificate. -/
theorem cmp116SourcePi4ForwardWalk_prefixThroughFactor_matrix_linfty_le
    {M Q Nc : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    {Ahead rho rate : ℝ}
    (Cert : CMP99PhysicalPatchWeightedCertificate
      (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q))
      K cmp99SourcePi4ChartEnlarged
      (cmp99SourcePi4ChartCore (M := M)) hc hmass hK
      physicalBondDist Ahead rho rate)
    (hrate : 0 < rate)
    (hgeom : ((2 ^ 4 : ℕ) : ℝ) * Real.exp (-rate) < 1)
    (walk : CMP99PhysicalPatchForwardWalkIndex
      (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q)))
    (i : Fin
      ((⟨walk.1, walk.2⟩ :
        CMP99GeneralizedWalk Unit
          ↥(cmp99SourcePi4Charts :
            Finset (CMP99SourcePi4Chart Unit Q)))).domains.length) :
    let rawWalk :=
      (⟨walk.1, walk.2⟩ :
        CMP99GeneralizedWalk Unit
          ↥(cmp99SourcePi4Charts :
            Finset (CMP99SourcePi4Chart Unit Q)))
    let R0 :=
      cmp99PhysicalPatchHead
        (cmp99SourcePi4Charts :
          Finset (CMP99SourcePi4Chart Unit Q))
        K cmp99SourcePi4ChartEnlarged
        (cmp99SourcePi4ChartCore (M := M)) hc hmass hK
    let R := fun (_ : Unit) =>
      cmp99PhysicalPatchContinuation
        (cmp99SourcePi4Charts :
          Finset (CMP99SourcePi4Chart Unit Q))
        K cmp99SourcePi4ChartEnlarged
        (cmp99SourcePi4ChartCore (M := M)) hc hmass hK
    ‖cmp116PhysicalEndomorphismComplexMatrix
        (((rawWalk.factors R0 R).take i).prod *
          rawWalk.factorAt R0 R i)‖ ≤
      (Ahead * rho ^ i.val) *
        (((Nc ^ 2 - 1 : ℕ) : ℝ) *
          cmp99PhysicalBondGeometricRowSum 4 rate) := by
  dsimp only
  apply
    linfty_opNorm_cmp116PhysicalEndomorphismComplexMatrix_le_of_weightedRow
      _ hrate hgeom
  exact
    CMP99GeneralizedWalk.prefixThroughFactor_weightedRowKernelBound
      _ _ _ physicalBondDist
      (fun target source middle =>
        physicalBondDist_triangle target middle source)
      Cert.head (fun _ chart => Cert.continuation chart) i

set_option maxHeartbeats 1000000 in

/-- The possibly empty source-walk suffix after one literal factor has the
exact remaining-power matrix bound. -/
theorem cmp116SourcePi4ForwardWalk_suffixAfterFactor_matrix_linfty_le
    {M Q Nc : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    {Ahead rho rate : ℝ}
    (Cert : CMP99PhysicalPatchWeightedCertificate
      (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q))
      K cmp99SourcePi4ChartEnlarged
      (cmp99SourcePi4ChartCore (M := M)) hc hmass hK
      physicalBondDist Ahead rho rate)
    (hrate : 0 < rate)
    (hgeom : ((2 ^ 4 : ℕ) : ℝ) * Real.exp (-rate) < 1)
    (walk : CMP99PhysicalPatchForwardWalkIndex
      (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q)))
    (i : Fin
      ((⟨walk.1, walk.2⟩ :
        CMP99GeneralizedWalk Unit
          ↥(cmp99SourcePi4Charts :
            Finset (CMP99SourcePi4Chart Unit Q)))).domains.length) :
    let rawWalk :=
      (⟨walk.1, walk.2⟩ :
        CMP99GeneralizedWalk Unit
          ↥(cmp99SourcePi4Charts :
            Finset (CMP99SourcePi4Chart Unit Q)))
    let R0 :=
      cmp99PhysicalPatchHead
        (cmp99SourcePi4Charts :
          Finset (CMP99SourcePi4Chart Unit Q))
        K cmp99SourcePi4ChartEnlarged
        (cmp99SourcePi4ChartCore (M := M)) hc hmass hK
    let R := fun (_ : Unit) =>
      cmp99PhysicalPatchContinuation
        (cmp99SourcePi4Charts :
          Finset (CMP99SourcePi4Chart Unit Q))
        K cmp99SourcePi4ChartEnlarged
        (cmp99SourcePi4ChartCore (M := M)) hc hmass hK
    ‖cmp116PhysicalEndomorphismComplexMatrix
        ((rawWalk.factors R0 R).drop (i + 1)).prod‖ ≤
      rho ^ (rawWalk.tail.length - i.val) *
        (((Nc ^ 2 - 1 : ℕ) : ℝ) *
          cmp99PhysicalBondGeometricRowSum 4 rate) := by
  dsimp only
  apply
    linfty_opNorm_cmp116PhysicalEndomorphismComplexMatrix_le_of_weightedRow
      _ hrate hgeom
  exact
    CMP99GeneralizedWalk.suffixAfterFactor_weightedRowKernelBound
      _ _ _ physicalBondDist physicalBondDist_self
      (fun target source middle =>
        physicalBondDist_triangle target middle source)
      hrate.le
      (fun _ chart => Cert.continuation chart) i

end

end YangMills.RG
