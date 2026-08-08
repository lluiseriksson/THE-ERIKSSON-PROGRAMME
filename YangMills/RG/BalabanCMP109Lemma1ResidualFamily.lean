/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP109Lemma1PhysicalBackgrounds

/-!
# The literal CMP109 Lemma-1 residual family

CMP109 Lemma 1 assigns the difference of inductive effective actions to
localization domains `Y`.  The physical backgrounds and the exact
changed-bond localization are already constructed.  This file performs the
remaining finite regrouping by the *actual source domain* carried by every
inductive local activity.

The resulting family is one genuine summand of Balaban's later residual
`V''_k(Y)`.  It is not the full residual: the directly bounded non-dangerous
terms of `F^(k)` still have to be added.  No equation-(1.36) bound, decay
certificate, or `interaction_bound` is assumed here.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No placeholders or
local axioms.
-/

namespace YangMills.RG

noncomputable section

variable {Index : Type*}
variable {L N' Nc : ℕ}
variable [NeZero L] [NeZero N'] [NeZero Nc]

private abbrev Lemma1Domain (L N' : ℕ) [NeZero L] [NeZero N'] :=
  CMP116LocalizationDomain 2 (L * N')

private noncomputable instance lemma1DomainDecidableEq :
    DecidableEq (Lemma1Domain L N') :=
  Classical.decEq _

/-- The contribution of one literal inductive local activity to the CMP109
Lemma-1 energy difference. -/
noncomputable def cmp109Eq212Lemma1LocalizedDifference
    (E : CMP109LocalizedActionExpansion Index 2 (L * N') Nc)
    (V : PhysicalGaugeBackground 4 (L * N') Nc)
    (gk : ℝ) (B : FinePhysicalOneCochain 4 L N' Nc)
    (D : CoarsePhysicalOneCochain 4 N' Nc)
    (i : Index) : ℝ :=
  (E.activity i).globalEval
      (CMP109LocalizedActionExpansion.positiveBondField
        (cmp109Eq212PerturbedFineBackground V gk B D)) -
    (E.activity i).globalEval
      (CMP109LocalizedActionExpansion.positiveBondField
        (cmp109Eq212BaseFineBackground V))

/-- The finite image of the source domains that actually see the physical
change between the two CMP109 backgrounds. -/
noncomputable def cmp109Eq212Lemma1AffectedDomainFamily
    (E : CMP109LocalizedActionExpansion Index 2 (L * N') Nc)
    (V : PhysicalGaugeBackground 4 (L * N') Nc)
    (gk : ℝ) (B : FinePhysicalOneCochain 4 L N' Nc)
    (D : CoarsePhysicalOneCochain 4 N' Nc) :
    Finset (Lemma1Domain L N') :=
  by
    classical
    exact
      (E.affectedDomains
        (CMP109LocalizedActionExpansion.changedPositiveBonds
          (cmp109Eq212PerturbedFineBackground V gk B D)
          (cmp109Eq212BaseFineBackground V))).image E.domainOf

/-- The literal Lemma-1 residual contribution attached to a source domain
`Y`: sum exactly those affected inductive activities whose stored physical
domain is `Y`. -/
noncomputable def cmp109Eq212Lemma1ResidualActivity
    (E : CMP109LocalizedActionExpansion Index 2 (L * N') Nc)
    (V : PhysicalGaugeBackground 4 (L * N') Nc)
    (gk : ℝ) (B : FinePhysicalOneCochain 4 L N' Nc)
    (D : CoarsePhysicalOneCochain 4 N' Nc)
    (Y : Lemma1Domain L N') : ℝ :=
  by
    classical
    exact
      ∑ i ∈
        (E.affectedDomains
          (CMP109LocalizedActionExpansion.changedPositiveBonds
            (cmp109Eq212PerturbedFineBackground V gk B D)
            (cmp109Eq212BaseFineBackground V))).filter
              (fun i => E.domainOf i = Y),
        cmp109Eq212Lemma1LocalizedDifference E V gk B D i

/-- Exact source regrouping: the physical CMP109 Lemma-1 energy difference
is the sum of its domain-indexed residual activities.  No arbitrary domain
assignment or residual function is supplied. -/
theorem cmp109Eq212Lemma1EnergyDifference_eq_sum_residualActivity
    (E : CMP109LocalizedActionExpansion Index 2 (L * N') Nc)
    (V : PhysicalGaugeBackground 4 (L * N') Nc)
    (gk : ℝ) (B : FinePhysicalOneCochain 4 L N' Nc)
    (D : CoarsePhysicalOneCochain 4 N' Nc) :
    cmp109Eq212Lemma1EnergyDifference E V gk B D =
      ∑ Y ∈ cmp109Eq212Lemma1AffectedDomainFamily E V gk B D,
        cmp109Eq212Lemma1ResidualActivity E V gk B D Y := by
  classical
  rw [cmp109Eq212Lemma1EnergyDifference_eq_sum_changed]
  unfold cmp109Eq212Lemma1AffectedDomainFamily
    cmp109Eq212Lemma1ResidualActivity
    cmp109Eq212Lemma1LocalizedDifference
  exact (Finset.sum_fiberwise_of_maps_to
    (fun i hi => Finset.mem_image.mpr ⟨i, hi, rfl⟩)
    (fun i =>
      (E.activity i).globalEval
          (CMP109LocalizedActionExpansion.positiveBondField
            (cmp109Eq212PerturbedFineBackground V gk B D)) -
        (E.activity i).globalEval
          (CMP109LocalizedActionExpansion.positiveBondField
            (cmp109Eq212BaseFineBackground V)))).symm

/-- A domain outside the canonical affected-domain image receives no
Lemma-1 residual contribution. -/
theorem cmp109Eq212Lemma1ResidualActivity_eq_zero_of_not_mem
    (E : CMP109LocalizedActionExpansion Index 2 (L * N') Nc)
    (V : PhysicalGaugeBackground 4 (L * N') Nc)
    (gk : ℝ) (B : FinePhysicalOneCochain 4 L N' Nc)
    (D : CoarsePhysicalOneCochain 4 N' Nc)
    (Y : Lemma1Domain L N')
    (hY : Y ∉ cmp109Eq212Lemma1AffectedDomainFamily E V gk B D) :
    cmp109Eq212Lemma1ResidualActivity E V gk B D Y = 0 := by
  classical
  unfold cmp109Eq212Lemma1ResidualActivity
  apply Finset.sum_eq_zero
  intro i hi
  have hiAffected :
      i ∈ E.affectedDomains
        (CMP109LocalizedActionExpansion.changedPositiveBonds
          (cmp109Eq212PerturbedFineBackground V gk B D)
          (cmp109Eq212BaseFineBackground V)) :=
    (Finset.mem_filter.mp hi).1
  have hiDomain : E.domainOf i = Y :=
    (Finset.mem_filter.mp hi).2
  exfalso
  apply hY
  exact Finset.mem_image.mpr ⟨i, hiAffected, hiDomain⟩

/-- The only estimate used by exact regrouping is the triangle inequality
inside one source-domain fiber.  The missing analytic work is to bound the
individual differences by the CMP109/CMP116 rate of equation (1.36). -/
theorem norm_cmp109Eq212Lemma1ResidualActivity_le
    (E : CMP109LocalizedActionExpansion Index 2 (L * N') Nc)
    (V : PhysicalGaugeBackground 4 (L * N') Nc)
    (gk : ℝ) (B : FinePhysicalOneCochain 4 L N' Nc)
    (D : CoarsePhysicalOneCochain 4 N' Nc)
    (Y : Lemma1Domain L N') :
    ‖cmp109Eq212Lemma1ResidualActivity E V gk B D Y‖ ≤
      ∑ i ∈
        (E.affectedDomains
          (CMP109LocalizedActionExpansion.changedPositiveBonds
            (cmp109Eq212PerturbedFineBackground V gk B D)
            (cmp109Eq212BaseFineBackground V))).filter
              (fun i => E.domainOf i = Y),
        ‖cmp109Eq212Lemma1LocalizedDifference E V gk B D i‖ := by
  unfold cmp109Eq212Lemma1ResidualActivity
  exact norm_sum_le _ _

end

end YangMills.RG
