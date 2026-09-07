/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102PhysicalSupNormTransport
import YangMills.RG.BalabanCMP99SourceEq3126PhysicalH

/-!
# The physical CMP99 background minimizer in source sup norm

The fixed-point equation of CMP102 uses the background minimizer `H` between
coarse and fine physical one-cochains.  This file transports a physical
continuous linear map to the canonical `PiLp ∞` realizations and then applies
that construction to the literal auxiliary CMP99 equation-(3.126) operator.

The resulting source-sup operator norm is an actual norm of the constructed
physical map.  It is not supplied as an `hH` hypothesis.  A future kernel
estimate may bound this number uniformly in the ambient volume without
changing the fixed-point interface.
-/

namespace YangMills.RG

open YangMills

noncomputable section

variable {d N₁ N₂ Nc : ℕ}
variable [NeZero d] [NeZero N₁] [NeZero N₂] [NeZero Nc]

/-- Transport a physical continuous linear map between stored `L²`
cochains to the identical coordinate families carrying source sup norms. -/
noncomputable def physicalGaugeOneCochainSupTransport
  (T : PhysicalGaugeOneCochain d N₁ Nc →L[ℝ]
      PhysicalGaugeOneCochain d N₂ Nc) :
    PhysicalGaugeOneCochainSup d N₁ Nc →L[ℝ]
      PhysicalGaugeOneCochainSup d N₂ Nc :=
  (physicalGaugeOneCochainSupEquiv
      (d := d) (N := N₂) (Nc := Nc)).toContinuousLinearMap.comp
    (T.comp
      (physicalGaugeOneCochainSupEquiv
        (d := d) (N := N₁) (Nc := Nc)).symm.toContinuousLinearMap)

@[simp] theorem physicalGaugeOneCochainSupTransport_apply
    (T : PhysicalGaugeOneCochain d N₁ Nc →L[ℝ]
      PhysicalGaugeOneCochain d N₂ Nc)
    (A : PhysicalGaugeOneCochainSup d N₁ Nc)
    (b : PhysicalBond d N₂) :
    physicalGaugeOneCochainSupTransport T A b =
      T (physicalGaugeOneCochainSupEquiv.symm A) b := by
  rfl

/-- The transported map is bounded by its genuine source-sup operator norm. -/
theorem norm_physicalGaugeOneCochainSupTransport_apply_le
    (T : PhysicalGaugeOneCochain d N₁ Nc →L[ℝ]
      PhysicalGaugeOneCochain d N₂ Nc)
    (A : PhysicalGaugeOneCochainSup d N₁ Nc) :
    ‖physicalGaugeOneCochainSupTransport T A‖ ≤
      ‖physicalGaugeOneCochainSupTransport T‖ * ‖A‖ :=
  ContinuousLinearMap.le_opNorm _ _

section PhysicalH

variable {L N' : ℕ}
variable [NeZero L] [NeZero N'] [NeZero (L * N')]

/-- The literal auxiliary CMP99 equation-(3.126) minimizer, now acting
between the source-sup coarse and fine cochain spaces. -/
noncomputable def cmp99SourceEq3126PhysicalHSup
    (U : PhysicalGaugeBackground d (L * N') Nc)
    {a CP ε : ℝ} (ha : 0 < a)
    (hP : FlatGaugeHodgePoincare d L N' Nc (matrixSUNAdjointModel Nc) CP)
    (hε : 0 ≤ ε) (hsmall : PhysicalWilsonSmallBackground U ε)
    (hbudget : cmp116ConcreteInteractingWilsonGaugeDefectBudget d Nc ε <
      min 1 a / CP) :
    PhysicalGaugeOneCochainSup d N' Nc →L[ℝ]
      PhysicalGaugeOneCochainSup d (L * N') Nc :=
  physicalGaugeOneCochainSupTransport
    (cmp99SourceEq3126PhysicalH U ha hP hε hsmall hbudget)

/-- The concrete source-sup norm of the physical CMP99 minimizer. -/
def cmp99SourceEq3126PhysicalHSourceSupNorm
    (U : PhysicalGaugeBackground d (L * N') Nc)
    {a CP ε : ℝ} (ha : 0 < a)
    (hP : FlatGaugeHodgePoincare d L N' Nc (matrixSUNAdjointModel Nc) CP)
    (hε : 0 ≤ ε) (hsmall : PhysicalWilsonSmallBackground U ε)
    (hbudget : cmp116ConcreteInteractingWilsonGaugeDefectBudget d Nc ε <
      min 1 a / CP) : ℝ :=
  ‖cmp99SourceEq3126PhysicalHSup U ha hP hε hsmall hbudget‖

/-- The source norm of `H D` is controlled by the actual transported
operator norm and the correction sup norm.  No independent `hH` premise
remains. -/
theorem cmp98SourceFieldSupNorm_cmp99SourceEq3126PhysicalH_le
    (U : PhysicalGaugeBackground d (L * N') Nc)
    {a CP ε : ℝ} (ha : 0 < a)
    (hP : FlatGaugeHodgePoincare d L N' Nc (matrixSUNAdjointModel Nc) CP)
    (hε : 0 ≤ ε) (hsmall : PhysicalWilsonSmallBackground U ε)
    (hbudget : cmp116ConcreteInteractingWilsonGaugeDefectBudget d Nc ε <
      min 1 a / CP)
    (D : CoarsePhysicalOneCochain d N' Nc) :
    cmp98SourceFieldSupNorm
        (cmp99SourceEq3126PhysicalH U ha hP hε hsmall hbudget D) ≤
      cmp99SourceEq3126PhysicalHSourceSupNorm
          U ha hP hε hsmall hbudget *
        cmp102PhysicalCorrectionSupNorm D := by
  let Dsup :=
    physicalGaugeOneCochainSupEquiv (d := d) (N := N') (Nc := Nc) D
  have h :=
    norm_physicalGaugeOneCochainSupTransport_apply_le
      (cmp99SourceEq3126PhysicalH U ha hP hε hsmall hbudget) Dsup
  change
    ‖physicalGaugeOneCochainSupEquiv
        (cmp99SourceEq3126PhysicalH U ha hP hε hsmall hbudget D)‖ ≤
      ‖physicalGaugeOneCochainSupTransport
        (cmp99SourceEq3126PhysicalH U ha hP hε hsmall hbudget)‖ *
        ‖physicalGaugeOneCochainSupEquiv D‖ at h
  rw [norm_physicalGaugeOneCochainSupEquiv_eq_sourceSupNorm,
    norm_physicalGaugeOneCochainSupEquiv_eq_correctionSupNorm] at h
  exact h

end PhysicalH

end

end YangMills.RG
