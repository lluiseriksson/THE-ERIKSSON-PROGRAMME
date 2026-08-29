import YangMills.RG.BalabanCMP99Eq389SignedCovariantLinkSourceLocalizedBound
import YangMills.RG.BalabanCMP99SourceGeneratedLaplacianTransitionSupport

/-!
PRE-VALIDATION: source present; its `.olean` is not yet materialized and the result is not compiler-verified.

# Localized Laplacian from a localized left-derivative bound

The literal backward-divergence stencil has four directions.  Its forward
bond keeps the target owner and its backward bond pays exactly `exp rate`.
The terminal factor `(ell * spacing)⁻¹` cancels the remaining `ell` from
the left action, with no carrier cardinality.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace BigOperators

noncomputable section

variable {L K Q Nc depth : ℕ}
variable [NeZero L] [NeZero K] [NeZero Q] [NeZero Nc]

/-- A literal localized `D\u2080 G` estimate yields the literal localized
`D\u2080* D\u2080 G` estimate.  The background and Green remain explicit. -/
theorem cmp99Eq342_laplacian_blockLocalizedSupBound_of_leftDerivative
    (Omega : ActiveGaugeRegion 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))
    [Nonempty (ActiveGaugeRegion.Site Omega)]
    (background : PhysicalGaugeBackground 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)) Nc)
    (G : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) →L[ℝ]
      ActiveGaugeZeroCochain Omega (SUNLieCoord Nc))
    {spacing ell leftA rate : ℝ}
    (hspacing : 0 < spacing) (hell : 0 < ell)
    (hleft : FinitePiLpTypedBlockLocalizedSupBound
      ((cmp99ActiveRegionSourceCovariantD0CLM Omega
          (matrixSUNAdjointModel Nc) background (ell * spacing)).comp G)
      (cmp99Eq342SourceLocalizedActiveOwner L K Q depth)
      (cmp99Eq342SourceLocalizedBondOwner L K Q depth)
      finBoxDist (leftA * ell) rate) :
    FinitePiLpTypedBlockLocalizedSupBound
      ((cmp99ActiveRegionSourceCovariantLaplacian Omega
          (matrixSUNAdjointModel Nc) background (ell * spacing)).comp G)
      (cmp99Eq342SourceLocalizedActiveOwner L K Q depth)
      (cmp99Eq342SourceLocalizedActiveOwner L K Q depth)
      finBoxDist
      (4 * leftA * ((1 + Real.exp rate) / spacing)) rate := by
  let terminalSpacing := ell * spacing
  let D := cmp99ActiveRegionSourceCovariantD0CLM Omega
    (matrixSUNAdjointModel Nc) background terminalSpacing
  let Cleft := D.comp G
  let laplacianAmplitude := 4 * leftA *
    ((1 + Real.exp rate) / spacing)
  have hrate : 0 < rate := hleft.2.1
  have hterminal : 0 < terminalSpacing := mul_pos hell hspacing
  have hleftAell : 0 ≤ leftA * ell := hleft.1
  have hleftA : 0 ≤ leftA :=
    nonneg_of_mul_nonneg_left hleftAell hell
  have hlaplacianAmplitude : 0 ≤ laplacianAmplitude := by
    exact mul_nonneg (mul_nonneg (by positivity) hleftA)
      (div_nonneg (add_nonneg zero_le_one (Real.exp_pos _).le) hspacing.le)
  refine ⟨hlaplacianAmplitude, hrate, ?_⟩
  intro owner f hf target
  have hD := hleft.2.2 owner f hf
  have hforward (i : Fin 4) :
      ‖Cleft f ((target.1, i) : PhysicalBond 4
          (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))‖ ≤
        (leftA * ell) *
          Real.exp (-(rate *
            (finBoxDist
              (cmp99Eq342SourceLocalizedActiveOwner L K Q depth target)
              owner : ℝ))) * finitePiLpSupNorm f := by
    simpa [cmp99Eq342SourceLocalizedBondOwner,
      cmp99Eq342SourceLocalizedActiveOwner, Cleft, D, terminalSpacing] using
      hD ((target.1, i) : PhysicalBond 4
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))
  have hback (i : Fin 4) :
      ‖Cleft f ((target.1.shiftBack i, i) : PhysicalBond 4
          (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))‖ ≤
        (leftA * ell) *
          (Real.exp rate * Real.exp (-(rate *
            (finBoxDist
              (cmp99Eq342SourceLocalizedActiveOwner L K Q depth target)
              owner : ℝ)))) * finitePiLpSupNorm f := by
    have hraw := hD ((target.1.shiftBack i, i) : PhysicalBond 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))
    have hshift := exp_neg_sourceLocalizationOwner_shiftBack_le_exp_mul
      L K Q depth target.1 owner i (delta := rate) hrate.le
    calc
      ‖Cleft f ((target.1.shiftBack i, i) : PhysicalBond 4
          (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))‖ ≤
        (leftA * ell) *
          Real.exp (-(rate *
            (finBoxDist
              (cmp99Eq389SourceLocalizationOwner L K Q depth
                (target.1.shiftBack i)) owner : ℝ))) *
          finitePiLpSupNorm f := by
            simpa [cmp99Eq342SourceLocalizedBondOwner, Cleft, D,
              terminalSpacing] using hraw
      _ ≤ (leftA * ell) *
          (Real.exp rate * Real.exp (-(rate *
            (finBoxDist
              (cmp99Eq342SourceLocalizedActiveOwner L K Q depth target)
              owner : ℝ)))) * finitePiLpSupNorm f := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hshift hleftAell)
          (finitePiLpSupNorm_nonneg f)
  change ‖cmp99ActiveRegionSourceCovariantLaplacian Omega
      (matrixSUNAdjointModel Nc) background terminalSpacing
      (G f) target‖ ≤ _
  rw [cmp99ActiveRegionSourceCovariantLaplacian_apply_eq_compression]
  change ‖cmp99GeneratedAmbientScaledCovariantLaplacian
      (matrixSUNAdjointModel Nc) background terminalSpacing
      (extendZeroZeroCLM Omega (G f)) target.1‖ ≤ _
  rw [cmp99GeneratedAmbientScaledCovariantLaplacian_apply]
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hterminal)]
  calc
    terminalSpacing⁻¹ *
        ‖∑ i : Fin 4,
          (Cleft f ((target.1, i) : PhysicalBond 4
              (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))) -
            (matrixSUNAdjointModel Nc).adCLM
              (background (positiveEdgeOfPhysicalBond
                ((target.1.shiftBack i, i) : PhysicalBond 4
                  (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))))⁻¹
              (Cleft f ((target.1.shiftBack i, i) : PhysicalBond 4
                (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))))‖ ≤
      terminalSpacing⁻¹ * ∑ i : Fin 4,
        (‖Cleft f ((target.1, i) : PhysicalBond 4
            (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))‖ +
          ‖Cleft f ((target.1.shiftBack i, i) : PhysicalBond 4
            (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))‖) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hterminal.le)
      calc
        ‖∑ i : Fin 4, _‖ ≤ ∑ i : Fin 4, ‖_‖ := norm_sum_le _ _
        _ ≤ ∑ i : Fin 4,
            (‖Cleft f ((target.1, i) : PhysicalBond 4
                (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))‖ +
              ‖Cleft f ((target.1.shiftBack i, i) : PhysicalBond 4
                (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))‖) := by
          gcongr with i
          calc
            ‖Cleft f ((target.1, i) : PhysicalBond 4
                  (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))) -
                (matrixSUNAdjointModel Nc).adCLM
                  (background (positiveEdgeOfPhysicalBond
                    ((target.1.shiftBack i, i) : PhysicalBond 4
                      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))))⁻¹
                  (Cleft f ((target.1.shiftBack i, i) : PhysicalBond 4
                    (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))))‖ ≤
              ‖Cleft f ((target.1, i) : PhysicalBond 4
                  (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))‖ +
                ‖(matrixSUNAdjointModel Nc).adCLM
                  (background (positiveEdgeOfPhysicalBond
                    ((target.1.shiftBack i, i) : PhysicalBond 4
                      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))))⁻¹
                  (Cleft f ((target.1.shiftBack i, i) : PhysicalBond 4
                    (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))))‖ :=
                norm_sub_le _ _
            _ = _ := by rw [(matrixSUNAdjointModel Nc).norm_ad]
    _ ≤ terminalSpacing⁻¹ * ∑ _i : Fin 4,
        ((leftA * ell) *
            Real.exp (-(rate *
              (finBoxDist
                (cmp99Eq342SourceLocalizedActiveOwner L K Q depth target)
                owner : ℝ))) * finitePiLpSupNorm f +
          (leftA * ell) *
            (Real.exp rate * Real.exp (-(rate *
              (finBoxDist
                (cmp99Eq342SourceLocalizedActiveOwner L K Q depth target)
                owner : ℝ)))) * finitePiLpSupNorm f) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hterminal.le)
      exact Finset.sum_le_sum fun i _ ⇒ add_le_add (hforward i) (hback i)
    _ = laplacianAmplitude *
        Real.exp (-(rate *
          (finBoxDist
            (cmp99Eq342SourceLocalizedActiveOwner L K Q depth target)
            owner : ℝ))) * finitePiLpSupNorm f := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      dsimp [terminalSpacing, laplacianAmplitude]
      (field_simp [ne_of_gt hspacing, ne_of_gt hell]; ring)

end

end YangMills.RG
