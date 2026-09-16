import YangMills.RG.BalabanCMP89Eq246AliasPrecisionCycle
import YangMills.RG.BalabanCMP89Eq246AliasPrecisionUniqueness
import YangMills.RG.BalabanCMP89Eq246FullSolutionDomain

/-!
# Covariance of the solved CMP89 (2.46) point-source fibre

The shifted explicit solution is transported to the unshifted alias fibre,
shown to solve the same source equation, and identified by the finite-system
uniqueness theorem.  Thus periodicity of the solution is a theorem; it is not
accepted as an input and it does not rely on the distinct Eq. (2.48) source.
-/

namespace YangMills.RG

noncomputable section

private theorem cmp89Eq246SolutionCycleCount_pos
    (L j : ℕ) [NeZero L] : 0 < L ^ j :=
  pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) j

/-- The complete normalized fine-point-source solution transforms by the
centered alias cycle under one physical coarse-momentum period. -/
theorem cmp89Eq246StabilizedFinePointSourceSolution_physicalShift_eq_cycle
    (d L j : ℕ) [NeZero L] (mass a : ℝ) (mu : Fin d)
    (z : Fin d → ℂ) (source : Fin d → ℤ)
    (baseDomain : CMP89Eq246FullSolutionDomain d L j mass a z)
    (shiftedDomain : CMP89Eq246FullSolutionDomain d L j mass a
      (cmp89Eq248PhysicalCoordinatePeriodShift mu z))
    (m : CMP89Eq246AliasIndex d L j) :
    cmp89Eq246StabilizedFinePointSourceSolution d L j mass a
        (cmp89Eq248PhysicalCoordinatePeriodShift mu z)
        (cmp89Eq249PhysicalFineLatticeDisplacement
          (((L ^ j : ℕ) : ℝ)⁻¹) source) m =
      cmp89Eq246StabilizedFinePointSourceSolution d L j mass a z
        (cmp89Eq249PhysicalFineLatticeDisplacement
          (((L ^ j : ℕ) : ℝ)⁻¹) source)
        (cmp89Eq245CenteredAliasVectorCycle d (L ^ j)
          (cmp89Eq246SolutionCycleCount_pos L j) mu m) := by
  let cycle := cmp89Eq245CenteredAliasVectorCycle d (L ^ j)
    (cmp89Eq246SolutionCycleCount_pos L j) mu
  let sourceEndpoint := cmp89Eq249PhysicalFineLatticeDisplacement
    (((L ^ j : ℕ) : ℝ)⁻¹) source
  let shiftedSolution := cmp89Eq246StabilizedFinePointSourceSolution
    d L j mass a (cmp89Eq248PhysicalCoordinatePeriodShift mu z)
      sourceEndpoint
  let transportedSolution : CMP89Eq246AliasIndex d L j → ℂ :=
    fun k => shiftedSolution (cycle.symm k)
  let baseSolution := cmp89Eq246StabilizedFinePointSourceSolution
    d L j mass a z sourceEndpoint
  have hshiftEquation :=
    cmp89Eq246EntireAliasPrecisionMatrix_mulVec_finePointSourceSolution
      d L j mass a (cmp89Eq248PhysicalCoordinatePeriodShift mu z)
      sourceEndpoint shiftedDomain.fine shiftedDomain.stabilized
        shiftedDomain.row
  have hbaseEquation :=
    cmp89Eq246EntireAliasPrecisionMatrix_mulVec_finePointSourceSolution
      d L j mass a z sourceEndpoint baseDomain.fine
        baseDomain.stabilized baseDomain.row
  have htransportEquation :
      (cmp89Eq246EntireAliasPrecisionMatrix d L j mass a z).mulVec
          transportedSolution =
        cmp89Eq246FinePointSourceAliasVector d L j z sourceEndpoint := by
    funext k
    have haction :=
      cmp89Eq246EntireAliasPrecisionMatrix_mulVec_physicalShift_eq_cycle
        d L j mass a mu z shiftedSolution (cycle.symm k)
    calc
      (cmp89Eq246EntireAliasPrecisionMatrix d L j mass a z).mulVec
          transportedSolution k =
        (cmp89Eq246EntireAliasPrecisionMatrix d L j mass a
          (cmp89Eq248PhysicalCoordinatePeriodShift mu z)).mulVec
            shiftedSolution (cycle.symm k) := by
              simpa [cycle, transportedSolution] using haction.symm
      _ = cmp89Eq246FinePointSourceAliasVector d L j
          (cmp89Eq248PhysicalCoordinatePeriodShift mu z)
          sourceEndpoint (cycle.symm k) := congrFun hshiftEquation _
      _ = cmp89Eq246FinePointSourceAliasVector d L j z
          sourceEndpoint k := by
            simpa [cycle, sourceEndpoint] using
              (cmp89Eq246FinePointSourceAliasVector_physicalShift_eq_cycle
                d L j mu z source (cycle.symm k))
  have hinjective :=
    cmp89Eq246EntireAliasPrecisionMatrix_mulVec_injective
      d L j mass a z baseDomain.fine baseDomain.stabilized baseDomain.row
  have hsolution : transportedSolution = baseSolution :=
    hinjective (htransportEquation.trans hbaseEquation.symm)
  have hm := congrFun hsolution (cycle m)
  simpa [cycle, sourceEndpoint, shiftedSolution, transportedSolution,
    baseSolution] using hm

end

end YangMills.RG
