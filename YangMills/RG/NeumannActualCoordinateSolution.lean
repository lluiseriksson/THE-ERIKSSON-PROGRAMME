import YangMills.RG.NeumannCoordinateAveragePhase
import YangMills.RG.NeumannDiagonalTransport
import YangMills.RG.BalabanCMP89Eq246AliasPrecisionUniqueness
import YangMills.RG.BalabanCMP89Eq246FullSolutionDomain

/-!
# PRE-VALIDATION: actual coordinate transport of the constructed full solver
Source present; .olean not materialized; result not compiler-verified.
R3 consumes derived physical matrix conjugacy and existing solver uniqueness.
The caller supplies a source vector and the two literal nonvanishing domains,
not a solution family, inverse, Green covariance, or matrix identity.
Physical endpoint phases and the Brillouin integral remain separate R4/R5.
-/

namespace YangMills.RG
noncomputable section

def neumannActualCoordinateSourceTransport
    (d L j : ℕ) [NeZero L] (mu : Fin d) (z : Fin d → ℂ)
    (f : CMP89Eq246AliasIndex d L j → ℂ) :
    CMP89Eq246AliasIndex d L j → ℂ :=
  NeumannDiagonalTransportRepro.transport
    (neumannPhysicalAliasCoordinateReflection d L j mu)
    (fun m => neumannCoordinateHalfCellPhase d (L ^ j) mu
      (cmp89Eq248EntireAliasMomentum z m.1)) f

theorem neumannActualCoordinatePrecision_action
    (d L j : ℕ) [NeZero L] (mu : Fin d) (mass a : ℝ) (z : Fin d → ℂ)
    (f : CMP89Eq246AliasIndex d L j → ℂ) :
    (cmp89Eq246EntireAliasPrecisionMatrix d L j mass a
      (neumannMomentumCoordinateReflection d mu z)).mulVec
      (neumannActualCoordinateSourceTransport d L j mu z f) =
    neumannActualCoordinateSourceTransport d L j mu z
      ((cmp89Eq246EntireAliasPrecisionMatrix d L j mass a z).mulVec f) := by
  exact NeumannDiagonalTransportRepro.action_function
    (neumannPhysicalAliasCoordinateReflection d L j mu)
    (fun m => neumannCoordinateHalfCellPhase d (L ^ j) mu
      (cmp89Eq248EntireAliasMomentum z m.1))
    (fun m => neumannCoordinateHalfCellPhase_ne_zero d (L ^ j) mu
      (cmp89Eq248EntireAliasMomentum z m.1))
    (cmp89Eq246EntireAliasPrecisionMatrix d L j mass a z)
    (cmp89Eq246EntireAliasPrecisionMatrix d L j mass a
      (neumannMomentumCoordinateReflection d mu z))
    (neumannEntireAliasPrecisionMatrix_coordinateReflection d L j mu mass a z) f

theorem neumannActualCoordinateFullSolution_transport
    (d L j : ℕ) [NeZero L] (mu : Fin d) (mass a : ℝ) (z : Fin d → ℂ)
    (source : CMP89Eq246AliasIndex d L j → ℂ)
    (baseDomain : CMP89Eq246FullSolutionDomain d L j mass a z)
    (reflectedDomain : CMP89Eq246FullSolutionDomain d L j mass a
      (neumannMomentumCoordinateReflection d mu z)) :
    neumannActualCoordinateSourceTransport d L j mu z
      (cmp89Eq246StabilizedAliasFullSolution d L j mass a z source) =
    cmp89Eq246StabilizedAliasFullSolution d L j mass a
      (neumannMomentumCoordinateReflection d mu z)
      (neumannActualCoordinateSourceTransport d L j mu z source) := by
  apply cmp89Eq246EntireAliasPrecisionMatrix_mulVec_injective
    d L j mass a (neumannMomentumCoordinateReflection d mu z)
    reflectedDomain.fine reflectedDomain.stabilized reflectedDomain.row
  rw [neumannActualCoordinatePrecision_action]
  rw [cmp89Eq246EntireAliasPrecisionMatrix_mulVec_stabilizedFullSolution
    d L j mass a z source baseDomain.fine baseDomain.stabilized baseDomain.row]
  rw [cmp89Eq246EntireAliasPrecisionMatrix_mulVec_stabilizedFullSolution
    d L j mass a (neumannMomentumCoordinateReflection d mu z)
    (neumannActualCoordinateSourceTransport d L j mu z source)
    reflectedDomain.fine reflectedDomain.stabilized reflectedDomain.row]


end
end YangMills.RG

