/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP109ConstraintCorrectedFluctuation
import YangMills.RG.BalabanCMP109LocalizedActionExpansion
import YangMills.RG.BalabanCMP109MinimalOrbitExistence
import YangMills.RG.BalabanCMP98PhysicalSpecialUnitaryChart

/-!
# Literal CMP109 Lemma-1 backgrounds

This file installs the two group-valued backgrounds in the second expression
of CMP109 (2.12).  Given the correction produced by the preceding Banach
theorem, it constructs

`B' = g_k C B - h D_tilde(g_k C B)`,

forms the genuine `SU(Nc)` coarse background `exp(i B') V`, and applies the
one-step Wilson minimizer to both that background and `V`.  The resulting
energy difference is localized by the actual set of positive bonds on which
the two minimizing backgrounds differ.

The terminal existence theorem obtains the correction and its nonlinear chart
from `exists_correctedFluctuation_fullConstraint`; they are not postulated.
This is the missing source dictionary for the first variational layer of the
Lemma-1 branch.  It is not equation (1.36): the chosen finite-volume minimizer
is not yet known to be the regular axial-gauge representative or to depend
Lipschitz-continuously on its coarse input.  No residual majorant,
`interaction_bound`, or equation-(2.20) weight is assumed.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No placeholders or
local axioms.
-/

namespace YangMills.RG

noncomputable section

variable {Index : Type*}
variable {L N' Nc : ℕ}
variable [NeZero L] [NeZero N'] [NeZero Nc]

/-- The literal coarse background `exp(i B') V` from CMP109 (2.12).  The
factor `i` is contained in the `su(Nc)` matrix represented by the real Lie
coordinate field. -/
noncomputable def cmp109Eq212PerturbedCoarseBackground
    (V : PhysicalGaugeBackground 4 (L * N') Nc)
    (gk : ℝ) (B : FinePhysicalOneCochain 4 L N' Nc)
    (D : CoarsePhysicalOneCochain 4 N' Nc) :
    PhysicalGaugeBackground 4 (L * N') Nc :=
  cmp98PhysicalSuLeftVariation V
    (cmp109ConstraintCorrectedFluctuation (L := L) gk B D) 1

/-- The minimizing fine background above the unperturbed coarse field. -/
noncomputable def cmp109Eq212BaseFineBackground
    (V : PhysicalGaugeBackground 4 (L * N') Nc) :
    PhysicalGaugeBackground 4 (2 * (L * N')) Nc :=
  cmp109OneStepSUNMinimalBackground (M := L * N') V

/-- The minimizing fine background above the perturbed coarse field. -/
noncomputable def cmp109Eq212PerturbedFineBackground
    (V : PhysicalGaugeBackground 4 (L * N') Nc)
    (gk : ℝ) (B : FinePhysicalOneCochain 4 L N' Nc)
    (D : CoarsePhysicalOneCochain 4 N' Nc) :
    PhysicalGaugeBackground 4 (2 * (L * N')) Nc :=
  cmp109OneStepSUNMinimalBackground (M := L * N')
    (cmp109Eq212PerturbedCoarseBackground V gk B D)

/-- Both fine backgrounds have the exact coarse block images displayed in
CMP109 (2.12). -/
@[simp] theorem blockMap_cmp109Eq212BaseFineBackground
    (V : PhysicalGaugeBackground 4 (L * N') Nc) :
    blockMap (L * N') (cmp109Eq212BaseFineBackground V) = V :=
  blockMap_cmp109OneStepSUNMinimalBackground V

@[simp] theorem blockMap_cmp109Eq212PerturbedFineBackground
    (V : PhysicalGaugeBackground 4 (L * N') Nc)
    (gk : ℝ) (B : FinePhysicalOneCochain 4 L N' Nc)
    (D : CoarsePhysicalOneCochain 4 N' Nc) :
    blockMap (L * N')
        (cmp109Eq212PerturbedFineBackground V gk B D) =
      cmp109Eq212PerturbedCoarseBackground V gk B D :=
  blockMap_cmp109OneStepSUNMinimalBackground _

/-- The literal one-step Lemma-1 energy difference in CMP109 (2.12). -/
noncomputable def cmp109Eq212Lemma1EnergyDifference
    (E : CMP109LocalizedActionExpansion Index 2 (L * N') Nc)
    (V : PhysicalGaugeBackground 4 (L * N') Nc)
    (gk : ℝ) (B : FinePhysicalOneCochain 4 L N' Nc)
    (D : CoarsePhysicalOneCochain 4 N' Nc) : ℝ :=
  E.energyDifference
    (cmp109Eq212PerturbedFineBackground V gk B D)
    (cmp109Eq212BaseFineBackground V)

/-- Exact source localization of the literal one-step CMP109 energy
difference.  Every surviving term is selected by the actual changed-bond set
of the two minimizing backgrounds; no perturbation carrier is supplied. -/
theorem cmp109Eq212Lemma1EnergyDifference_eq_sum_changed
    (E : CMP109LocalizedActionExpansion Index 2 (L * N') Nc)
    (V : PhysicalGaugeBackground 4 (L * N') Nc)
    (gk : ℝ) (B : FinePhysicalOneCochain 4 L N' Nc)
    (D : CoarsePhysicalOneCochain 4 N' Nc) :
    cmp109Eq212Lemma1EnergyDifference E V gk B D =
      ∑ i ∈ E.affectedDomains
          (CMP109LocalizedActionExpansion.changedPositiveBonds
            (cmp109Eq212PerturbedFineBackground V gk B D)
            (cmp109Eq212BaseFineBackground V)),
        ((E.activity i).globalEval
            (CMP109LocalizedActionExpansion.positiveBondField
              (cmp109Eq212PerturbedFineBackground V gk B D)) -
          (E.activity i).globalEval
            (CMP109LocalizedActionExpansion.positiveBondField
              (cmp109Eq212BaseFineBackground V))) := by
  unfold cmp109Eq212Lemma1EnergyDifference
  exact E.energyDifference_eq_sum_changedPositiveBonds _ _

/-- Triangle-inequality form of the same exact physical localization.  This
does not assert the missing source estimate (1.36). -/
theorem norm_cmp109Eq212Lemma1EnergyDifference_le_sum_changed
    (E : CMP109LocalizedActionExpansion Index 2 (L * N') Nc)
    (V : PhysicalGaugeBackground 4 (L * N') Nc)
    (gk : ℝ) (B : FinePhysicalOneCochain 4 L N' Nc)
    (D : CoarsePhysicalOneCochain 4 N' Nc) :
    ‖cmp109Eq212Lemma1EnergyDifference E V gk B D‖ ≤
      ∑ i ∈ E.affectedDomains
          (CMP109LocalizedActionExpansion.changedPositiveBonds
            (cmp109Eq212PerturbedFineBackground V gk B D)
            (cmp109Eq212BaseFineBackground V)),
        ‖(E.activity i).globalEval
            (CMP109LocalizedActionExpansion.positiveBondField
              (cmp109Eq212PerturbedFineBackground V gk B D)) -
          (E.activity i).globalEval
            (CMP109LocalizedActionExpansion.positiveBondField
              (cmp109Eq212BaseFineBackground V))‖ := by
  unfold cmp109Eq212Lemma1EnergyDifference
  exact E.norm_energyDifference_le_sum_changedPositiveBonds _ _

/-- Banach supplies a correction and chart for which the literal (2.12)
backgrounds satisfy the complete nonlinear block constraint.  This theorem
packages existence only; it does not assume a correction field or fixed-point
equation. -/
theorem exists_cmp109Eq212Lemma1PhysicalBackgrounds
    (V : PhysicalGaugeBackground 4 (L * N') Nc)
    (gk : ℝ) (B : FinePhysicalOneCochain 4 L N' Nc)
    (ρ r s : ℝ)
    (Data : CMP109ConstraintCorrectionBallData V
      (cmp109ConstrainedLinearFluctuation (L := L) gk B) ρ r s)
    (hcontract : Data.contractionRate < 1) :
    ∃ (D : CoarsePhysicalOneCochain 4 N' Nc)
      (Chart : CMP102PhysicalNonlinearChartBudget V
        (cmp109ConstraintCorrectedFluctuation (L := L) gk B D)),
      cmp102PhysicalCorrectionSupNorm D ≤ ρ ∧
        flatBlockConstraintQCLM (d := 4) (Nc := Nc) L N'
              (cmp109ConstraintCorrectedFluctuation (L := L) gk B D) +
            cmp102PhysicalNonlinearCorrectionOfBudget V
              (cmp109ConstraintCorrectedFluctuation (L := L) gk B D) Chart =
          0 ∧
        blockMap (L * N') (cmp109Eq212BaseFineBackground V) = V ∧
        blockMap (L * N')
            (cmp109Eq212PerturbedFineBackground V gk B D) =
          cmp109Eq212PerturbedCoarseBackground V gk B D := by
  rcases Data.exists_correctedFluctuation_fullConstraint
      V gk B ρ r s hcontract with
    ⟨D, Chart, hDnorm, hconstraint⟩
  exact ⟨D, Chart, hDnorm, hconstraint,
    blockMap_cmp109Eq212BaseFineBackground V,
    blockMap_cmp109Eq212PerturbedFineBackground V gk B D⟩

end

end YangMills.RG
