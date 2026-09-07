/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102PhysicalRightVariationLinearity

/-!
# Derivative factorization of the CMP102 represented block

The literal represented block is the ordered product of the exponential
of the logarithmic `Ubar` average and the straight coarse Wilson contour.
This module differentiates that product without commuting its factors and
exposes the four-term two-point telescope needed for quantitative
fixed-point estimates.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

/-- Exact ordered product rule for the literal represented block. -/
theorem fderiv_cmp102AmbientNonlinearBlock_apply
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (b : PhysicalBond d N')
    (Z H : PhysicalAmbientMatrixTangent d (M * N') Nc)
    (hlocal : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x Z‖ < 1) :
    fderiv ℝ (cmp102AmbientNonlinearBlock U b) Z H =
      fderiv ℝ (cmp98UbarExpAverage U b) Z H *
          cmp98AmbientWilsonLineMatrix U Z
            (cmp98SourceCoarseBondPath (Nc := Nc) b) +
        cmp98UbarExpAverage U b Z *
          fderiv ℝ
            (fun W => cmp98AmbientWilsonLineMatrix U W
              (cmp98SourceCoarseBondPath (Nc := Nc) b)) Z H := by
  have hE := (analyticAt_cmp98UbarExpAverage_of_norm_lt_one
    U b Z hlocal).differentiableAt.hasFDerivAt
  have hC := (analyticAt_cmp98AmbientWilsonLineMatrix U Z
    (cmp98SourceCoarseBondPath (Nc := Nc) b)).differentiableAt.hasFDerivAt
  have hprod := hE.mul' hC
  have hEq := hprod.fderiv
  have hApply := congrArg
    (fun L : PhysicalAmbientMatrixTangent d (M * N') Nc →L[ℝ]
      Matrix (Fin Nc) (Fin Nc) ℂ => L H) hEq
  change
    fderiv ℝ
        (cmp98UbarExpAverage U b *
          fun W => cmp98AmbientWilsonLineMatrix U W
            (cmp98SourceCoarseBondPath (Nc := Nc) b)) Z H =
      cmp98UbarExpAverage U b Z *
          fderiv ℝ
            (fun W => cmp98AmbientWilsonLineMatrix U W
              (cmp98SourceCoarseBondPath (Nc := Nc) b)) Z H +
        fderiv ℝ (cmp98UbarExpAverage U b) Z H *
          cmp98AmbientWilsonLineMatrix U Z
            (cmp98SourceCoarseBondPath (Nc := Nc) b) at hApply
  simpa [cmp102AmbientNonlinearBlock, add_comm] using hApply

/-- Exact four-term telescope for the derivatives at two ambient fields.
The factor order is the physical order and is never commuted. -/
theorem fderiv_cmp102AmbientNonlinearBlock_sub_apply
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (b : PhysicalBond d N')
    (Z W H : PhysicalAmbientMatrixTangent d (M * N') Nc)
    (hlocalZ : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x Z‖ < 1)
    (hlocalW : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x W‖ < 1) :
    (fderiv ℝ (cmp102AmbientNonlinearBlock U b) Z -
        fderiv ℝ (cmp102AmbientNonlinearBlock U b) W) H =
      (fderiv ℝ (cmp98UbarExpAverage U b) Z H -
          fderiv ℝ (cmp98UbarExpAverage U b) W H) *
          cmp98AmbientWilsonLineMatrix U Z
            (cmp98SourceCoarseBondPath (Nc := Nc) b) +
        fderiv ℝ (cmp98UbarExpAverage U b) W H *
          (cmp98AmbientWilsonLineMatrix U Z
              (cmp98SourceCoarseBondPath (Nc := Nc) b) -
            cmp98AmbientWilsonLineMatrix U W
              (cmp98SourceCoarseBondPath (Nc := Nc) b)) +
        (cmp98UbarExpAverage U b Z - cmp98UbarExpAverage U b W) *
          fderiv ℝ
            (fun V => cmp98AmbientWilsonLineMatrix U V
              (cmp98SourceCoarseBondPath (Nc := Nc) b)) Z H +
        cmp98UbarExpAverage U b W *
          ((fderiv ℝ
              (fun V => cmp98AmbientWilsonLineMatrix U V
                (cmp98SourceCoarseBondPath (Nc := Nc) b)) Z -
            fderiv ℝ
              (fun V => cmp98AmbientWilsonLineMatrix U V
                (cmp98SourceCoarseBondPath (Nc := Nc) b)) W) H) := by
  simp only [ContinuousLinearMap.sub_apply]
  rw [fderiv_cmp102AmbientNonlinearBlock_apply U b Z H hlocalZ,
    fderiv_cmp102AmbientNonlinearBlock_apply U b W H hlocalW]
  noncomm_ring

/-- Budget for the derivative of an ordered two-factor represented block. -/
def cmp102AmbientNonlinearBlockDerivativeBudget
    (DE C E DC : ℝ) : ℝ :=
  DE * C + E * DC

/-- Budget for the Lipschitz variation of the represented-block derivative.
The four summands correspond exactly to the four ordered telescope terms. -/
def cmp102AmbientNonlinearBlockDerivativeLipschitzBudget
    (DDE C DE LC LE DC E DDC : ℝ) : ℝ :=
  DDE * C + DE * LC + LE * DC + E * DDC

/-- The exact product rule generates the derivative norm bound from
factor-level estimates. -/
theorem norm_fderiv_cmp102AmbientNonlinearBlock_le
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (b : PhysicalBond d N')
    (Z : PhysicalAmbientMatrixTangent d (M * N') Nc)
    {DE C E DC : ℝ}
    (hlocal : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x Z‖ < 1)
    (hDE : ‖fderiv ℝ (cmp98UbarExpAverage U b) Z‖ ≤ DE)
    (hC :
      ‖cmp98AmbientWilsonLineMatrix U Z
        (cmp98SourceCoarseBondPath (Nc := Nc) b)‖ ≤ C)
    (hE : ‖cmp98UbarExpAverage U b Z‖ ≤ E)
    (hDC :
      ‖fderiv ℝ
        (fun W => cmp98AmbientWilsonLineMatrix U W
          (cmp98SourceCoarseBondPath (Nc := Nc) b)) Z‖ ≤ DC) :
    ‖fderiv ℝ (cmp102AmbientNonlinearBlock U b) Z‖ ≤
      cmp102AmbientNonlinearBlockDerivativeBudget DE C E DC := by
  have hDE0 : 0 ≤ DE :=
    (norm_nonneg (fderiv ℝ (cmp98UbarExpAverage U b) Z)).trans hDE
  have hC0 : 0 ≤ C :=
    (norm_nonneg (cmp98AmbientWilsonLineMatrix U Z
      (cmp98SourceCoarseBondPath (Nc := Nc) b))).trans hC
  have hE0 : 0 ≤ E := (norm_nonneg (cmp98UbarExpAverage U b Z)).trans hE
  have hDC0 : 0 ≤ DC :=
    (norm_nonneg (fderiv ℝ
      (fun W => cmp98AmbientWilsonLineMatrix U W
        (cmp98SourceCoarseBondPath (Nc := Nc) b)) Z)).trans hDC
  apply ContinuousLinearMap.opNorm_le_bound
    (fderiv ℝ (cmp102AmbientNonlinearBlock U b) Z)
    (add_nonneg
      (mul_nonneg hDE0 hC0)
      (mul_nonneg hE0 hDC0))
  intro H
  calc
    ‖fderiv ℝ (cmp102AmbientNonlinearBlock U b) Z H‖ =
      ‖fderiv ℝ (cmp98UbarExpAverage U b) Z H *
          cmp98AmbientWilsonLineMatrix U Z
            (cmp98SourceCoarseBondPath (Nc := Nc) b) +
        cmp98UbarExpAverage U b Z *
          fderiv ℝ
            (fun W => cmp98AmbientWilsonLineMatrix U W
              (cmp98SourceCoarseBondPath (Nc := Nc) b)) Z H‖ :=
        congrArg norm
          (fderiv_cmp102AmbientNonlinearBlock_apply U b Z H hlocal)
    _ ≤ ‖fderiv ℝ (cmp98UbarExpAverage U b) Z H‖ *
              ‖cmp98AmbientWilsonLineMatrix U Z
                (cmp98SourceCoarseBondPath (Nc := Nc) b)‖ +
            ‖cmp98UbarExpAverage U b Z‖ *
              ‖fderiv ℝ
                (fun W => cmp98AmbientWilsonLineMatrix U W
                  (cmp98SourceCoarseBondPath (Nc := Nc) b)) Z H‖ := by
          exact (norm_add_le _ _).trans
            (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
    _ ≤ (DE * C + E * DC) * ‖H‖ := by
      have hDEH :
          ‖fderiv ℝ (cmp98UbarExpAverage U b) Z H‖ ≤ DE * ‖H‖ :=
        (ContinuousLinearMap.le_opNorm _ H).trans
          (mul_le_mul_of_nonneg_right hDE (norm_nonneg H))
      have hDCH :
          ‖fderiv ℝ
            (fun W => cmp98AmbientWilsonLineMatrix U W
              (cmp98SourceCoarseBondPath (Nc := Nc) b)) Z H‖ ≤
            DC * ‖H‖ :=
        (ContinuousLinearMap.le_opNorm _ H).trans
          (mul_le_mul_of_nonneg_right hDC (norm_nonneg H))
      calc
        _ ≤ (DE * ‖H‖) * C + E * (DC * ‖H‖) := by
          gcongr
        _ = (DE * C + E * DC) * ‖H‖ := by ring

/-- The exact four-term telescope generates the derivative Lipschitz bound
from the two physical factors. -/
theorem norm_fderiv_cmp102AmbientNonlinearBlock_sub_le
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (b : PhysicalBond d N')
    (Z W : PhysicalAmbientMatrixTangent d (M * N') Nc)
    {DDE C DE LC LE DC E DDC : ℝ}
    (hlocalZ : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x Z‖ < 1)
    (hlocalW : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x W‖ < 1)
    (hDDE : 0 ≤ DDE) (hLC : 0 ≤ LC) (hLE : 0 ≤ LE) (hDDC : 0 ≤ DDC)
    (hDE :
      ‖fderiv ℝ (cmp98UbarExpAverage U b) W‖ ≤ DE)
    (hC :
      ‖cmp98AmbientWilsonLineMatrix U Z
        (cmp98SourceCoarseBondPath (Nc := Nc) b)‖ ≤ C)
    (hE : ‖cmp98UbarExpAverage U b W‖ ≤ E)
    (hDC :
      ‖fderiv ℝ
        (fun V => cmp98AmbientWilsonLineMatrix U V
          (cmp98SourceCoarseBondPath (Nc := Nc) b)) Z‖ ≤ DC)
    (hDDEbound :
      ‖fderiv ℝ (cmp98UbarExpAverage U b) Z -
          fderiv ℝ (cmp98UbarExpAverage U b) W‖ ≤ DDE * ‖Z - W‖)
    (hLCbound :
      ‖cmp98AmbientWilsonLineMatrix U Z
          (cmp98SourceCoarseBondPath (Nc := Nc) b) -
        cmp98AmbientWilsonLineMatrix U W
          (cmp98SourceCoarseBondPath (Nc := Nc) b)‖ ≤ LC * ‖Z - W‖)
    (hLEbound :
      ‖cmp98UbarExpAverage U b Z - cmp98UbarExpAverage U b W‖ ≤
        LE * ‖Z - W‖)
    (hDDCbound :
      ‖fderiv ℝ
          (fun V => cmp98AmbientWilsonLineMatrix U V
            (cmp98SourceCoarseBondPath (Nc := Nc) b)) Z -
        fderiv ℝ
          (fun V => cmp98AmbientWilsonLineMatrix U V
            (cmp98SourceCoarseBondPath (Nc := Nc) b)) W‖ ≤
          DDC * ‖Z - W‖) :
    ‖fderiv ℝ (cmp102AmbientNonlinearBlock U b) Z -
        fderiv ℝ (cmp102AmbientNonlinearBlock U b) W‖ ≤
      cmp102AmbientNonlinearBlockDerivativeLipschitzBudget
        DDE C DE LC LE DC E DDC * ‖Z - W‖ := by
  have hDE0 : 0 ≤ DE :=
    (norm_nonneg (fderiv ℝ (cmp98UbarExpAverage U b) W)).trans hDE
  have hC0 : 0 ≤ C :=
    (norm_nonneg (cmp98AmbientWilsonLineMatrix U Z
      (cmp98SourceCoarseBondPath (Nc := Nc) b))).trans hC
  have hE0 : 0 ≤ E := (norm_nonneg (cmp98UbarExpAverage U b W)).trans hE
  have hDC0 : 0 ≤ DC :=
    (norm_nonneg (fderiv ℝ
      (fun V => cmp98AmbientWilsonLineMatrix U V
        (cmp98SourceCoarseBondPath (Nc := Nc) b)) Z)).trans hDC
  apply ContinuousLinearMap.opNorm_le_bound
    (fderiv ℝ (cmp102AmbientNonlinearBlock U b) Z -
      fderiv ℝ (cmp102AmbientNonlinearBlock U b) W)
    (mul_nonneg
      (add_nonneg
        (add_nonneg
          (add_nonneg
            (mul_nonneg hDDE hC0)
            (mul_nonneg hDE0 hLC))
          (mul_nonneg hLE hDC0))
        (mul_nonneg hE0 hDDC))
      (norm_nonneg (Z - W)))
  intro H
  rw [fderiv_cmp102AmbientNonlinearBlock_sub_apply
    U b Z W H hlocalZ hlocalW]
  calc
    ‖(fderiv ℝ (cmp98UbarExpAverage U b) Z H -
          fderiv ℝ (cmp98UbarExpAverage U b) W H) *
          cmp98AmbientWilsonLineMatrix U Z
            (cmp98SourceCoarseBondPath (Nc := Nc) b) +
        fderiv ℝ (cmp98UbarExpAverage U b) W H *
          (cmp98AmbientWilsonLineMatrix U Z
              (cmp98SourceCoarseBondPath (Nc := Nc) b) -
            cmp98AmbientWilsonLineMatrix U W
              (cmp98SourceCoarseBondPath (Nc := Nc) b)) +
        (cmp98UbarExpAverage U b Z - cmp98UbarExpAverage U b W) *
          fderiv ℝ
            (fun V => cmp98AmbientWilsonLineMatrix U V
              (cmp98SourceCoarseBondPath (Nc := Nc) b)) Z H +
        cmp98UbarExpAverage U b W *
          ((fderiv ℝ
              (fun V => cmp98AmbientWilsonLineMatrix U V
                (cmp98SourceCoarseBondPath (Nc := Nc) b)) Z -
            fderiv ℝ
              (fun V => cmp98AmbientWilsonLineMatrix U V
                (cmp98SourceCoarseBondPath (Nc := Nc) b)) W) H)‖
        ≤
          ‖(fderiv ℝ (cmp98UbarExpAverage U b) Z -
              fderiv ℝ (cmp98UbarExpAverage U b) W) H‖ *
              ‖cmp98AmbientWilsonLineMatrix U Z
                (cmp98SourceCoarseBondPath (Nc := Nc) b)‖ +
          ‖fderiv ℝ (cmp98UbarExpAverage U b) W H‖ *
              ‖cmp98AmbientWilsonLineMatrix U Z
                  (cmp98SourceCoarseBondPath (Nc := Nc) b) -
                cmp98AmbientWilsonLineMatrix U W
                  (cmp98SourceCoarseBondPath (Nc := Nc) b)‖ +
          ‖cmp98UbarExpAverage U b Z - cmp98UbarExpAverage U b W‖ *
              ‖fderiv ℝ
                (fun V => cmp98AmbientWilsonLineMatrix U V
                  (cmp98SourceCoarseBondPath (Nc := Nc) b)) Z H‖ +
          ‖cmp98UbarExpAverage U b W‖ *
              ‖(fderiv ℝ
                  (fun V => cmp98AmbientWilsonLineMatrix U V
                    (cmp98SourceCoarseBondPath (Nc := Nc) b)) Z -
                fderiv ℝ
                  (fun V => cmp98AmbientWilsonLineMatrix U V
                    (cmp98SourceCoarseBondPath (Nc := Nc) b)) W) H‖ := by
          calc
            _ ≤
                ‖(fderiv ℝ (cmp98UbarExpAverage U b) Z H -
                    fderiv ℝ (cmp98UbarExpAverage U b) W H) *
                    cmp98AmbientWilsonLineMatrix U Z
                      (cmp98SourceCoarseBondPath (Nc := Nc) b)‖ +
                ‖fderiv ℝ (cmp98UbarExpAverage U b) W H *
                    (cmp98AmbientWilsonLineMatrix U Z
                        (cmp98SourceCoarseBondPath (Nc := Nc) b) -
                      cmp98AmbientWilsonLineMatrix U W
                        (cmp98SourceCoarseBondPath (Nc := Nc) b))‖ +
                ‖(cmp98UbarExpAverage U b Z -
                    cmp98UbarExpAverage U b W) *
                    fderiv ℝ
                      (fun V => cmp98AmbientWilsonLineMatrix U V
                        (cmp98SourceCoarseBondPath (Nc := Nc) b)) Z H‖ +
                ‖cmp98UbarExpAverage U b W *
                    ((fderiv ℝ
                        (fun V => cmp98AmbientWilsonLineMatrix U V
                          (cmp98SourceCoarseBondPath (Nc := Nc) b)) Z -
                      fderiv ℝ
                        (fun V => cmp98AmbientWilsonLineMatrix U V
                          (cmp98SourceCoarseBondPath (Nc := Nc) b)) W) H)‖ := by
                  exact norm_add₄_le
            _ ≤ _ := by
              gcongr <;> exact norm_mul_le _ _
    _ ≤
        ((DDE * ‖Z - W‖) * ‖H‖) * C +
        (DE * ‖H‖) * (LC * ‖Z - W‖) +
        (LE * ‖Z - W‖) * (DC * ‖H‖) +
        E * ((DDC * ‖Z - W‖) * ‖H‖) := by
      have hDDEH :
          ‖(fderiv ℝ (cmp98UbarExpAverage U b) Z -
            fderiv ℝ (cmp98UbarExpAverage U b) W) H‖ ≤
              (DDE * ‖Z - W‖) * ‖H‖ :=
        (ContinuousLinearMap.le_opNorm _ H).trans
          (mul_le_mul_of_nonneg_right hDDEbound (norm_nonneg H))
      have hDEH :
          ‖fderiv ℝ (cmp98UbarExpAverage U b) W H‖ ≤ DE * ‖H‖ :=
        (ContinuousLinearMap.le_opNorm _ H).trans
          (mul_le_mul_of_nonneg_right hDE (norm_nonneg H))
      have hDCH :
          ‖fderiv ℝ
            (fun V => cmp98AmbientWilsonLineMatrix U V
              (cmp98SourceCoarseBondPath (Nc := Nc) b)) Z H‖ ≤
              DC * ‖H‖ :=
        (ContinuousLinearMap.le_opNorm _ H).trans
          (mul_le_mul_of_nonneg_right hDC (norm_nonneg H))
      have hDDCH :
          ‖(fderiv ℝ
              (fun V => cmp98AmbientWilsonLineMatrix U V
                (cmp98SourceCoarseBondPath (Nc := Nc) b)) Z -
            fderiv ℝ
              (fun V => cmp98AmbientWilsonLineMatrix U V
                (cmp98SourceCoarseBondPath (Nc := Nc) b)) W) H‖ ≤
              (DDC * ‖Z - W‖) * ‖H‖ :=
        (ContinuousLinearMap.le_opNorm _ H).trans
          (mul_le_mul_of_nonneg_right hDDCbound (norm_nonneg H))
      gcongr
    _ =
        (DDE * C + DE * LC + LE * DC + E * DDC) *
          ‖Z - W‖ * ‖H‖ := by ring

end

end YangMills.RG
