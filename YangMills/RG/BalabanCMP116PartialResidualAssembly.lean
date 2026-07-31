/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq142SourceSplit
import YangMills.RG.BalabanCMP116Eq136To220

/-!
# Partial assembly of the CMP116 source residual

The direct equation-(80) sector and the CMP109 Lemma-1 sector contribute to
the same printed residual `V''_k(Y,B)`. Before the source-scale dictionary is
available, the honest terminal interface therefore carries the reindexed
Lemma-1 contribution as one named input.

This file fixes the algebra of that partial assembly. The Lemma-1 term is
added to both the total activity and the residual. It consequently cancels
*exactly* from the quadratic core `total - residual`, while remaining visible
in the residual estimate `(1.36)`. Separate direct and Lemma-1 `(1.36)`
budgets are combined by an explicit split of the printed constant `E0`.

No domain reindexing, Lemma-1 estimate, or scale dictionary is asserted here.
-/

namespace YangMills.RG

noncomputable section

/-- The one named source input left by the partial equation-(1.36)
assembly: a Lemma-1 residual already transported to the consumer's domain
index and metric.

This certificate deliberately does not construct the scale dictionary from
the native Lemma-1 domains to `Y`.  Supplying such a dictionary and proving
this bound after reindexing remain the source-facing Lemma-1 obligation. -/
structure CMP116Lemma1Eq136ResidualCertificate
    {Y E : Type*}
    (domainDist : Y → ℝ)
    (epsilon1 C1 : ℝ) (M q : ℕ)
    (C2 kappa1 delta kappa : ℝ) where
  E0 : ℝ
  residual : Y → E → ℝ
  bound : ∀ y B,
    |residual y B| ≤
      cmp116Eq136ResidualMajorant E0 epsilon1 C1 M q
        C2 kappa1 delta kappa (domainDist y)

/-- Add a separately indexed residual sector to the total localized
activity. -/
noncomputable def cmp116PartialResidualTotal
    {Y E : Type*}
    (directTotal lemma1Residual : Y → E → ℝ) :
    Y → E → ℝ :=
  fun y B => directTotal y B + lemma1Residual y B

/-- Add the same separately indexed sector to the source residual. -/
noncomputable def cmp116PartialResidual
    {Y E : Type*}
    (directResidual lemma1Residual : Y → E → ℝ) :
    Y → E → ℝ :=
  fun y B => directResidual y B + lemma1Residual y B

/-- The named Lemma-1 input cancels exactly from the quadratic core. -/
theorem cmp116Eq142PhysicalQuadraticCore_partialResidual
    {Y : Type*} {d N Nc : ℕ} [NeZero N]
    (directTotal directResidual lemma1Residual :
      Y → PhysicalGaugeOneCochain d N Nc → ℝ)
    (y : Y) (B : PhysicalGaugeOneCochain d N Nc) :
    cmp116Eq142PhysicalQuadraticCore
        (cmp116PartialResidualTotal directTotal lemma1Residual)
        (cmp116PartialResidual directResidual lemma1Residual) y B =
      cmp116Eq142PhysicalQuadraticCore
        directTotal directResidual y B := by
  unfold cmp116Eq142PhysicalQuadraticCore
    cmp116PartialResidualTotal cmp116PartialResidual
  ring

/-- Smoothness of the quadratic core is inherited from the direct sector;
the named Lemma-1 residual does not enter the core. -/
theorem contDiff_cmp116Eq142PhysicalQuadraticCore_partialResidual
    {Y : Type*} {d N Nc : ℕ} [NeZero N]
    (directTotal directResidual lemma1Residual :
      Y → PhysicalGaugeOneCochain d N Nc → ℝ)
    (hsmooth : ∀ y, ContDiff ℝ 2
      (cmp116Eq142PhysicalQuadraticCore directTotal directResidual y))
    (y : Y) :
    ContDiff ℝ 2
      (cmp116Eq142PhysicalQuadraticCore
        (cmp116PartialResidualTotal directTotal lemma1Residual)
        (cmp116PartialResidual directResidual lemma1Residual) y) := by
  convert hsmooth y using 1
  funext B
  exact cmp116Eq142PhysicalQuadraticCore_partialResidual
    directTotal directResidual lemma1Residual y B

/-- The printed `(1.36)` majorant is exactly additive in its `E0`
normalization. -/
theorem cmp116Eq136ResidualMajorant_add_E0
    (E0Direct E0Lemma1 epsilon1 C1 : ℝ) (M q : ℕ)
    (C2 kappa1 delta kappa domainDist : ℝ) :
    cmp116Eq136ResidualMajorant E0Direct epsilon1 C1 M q
        C2 kappa1 delta kappa domainDist +
      cmp116Eq136ResidualMajorant E0Lemma1 epsilon1 C1 M q
        C2 kappa1 delta kappa domainDist =
      cmp116Eq136ResidualMajorant (E0Direct + E0Lemma1) epsilon1 C1 M q
        C2 kappa1 delta kappa domainDist := by
  unfold cmp116Eq136ResidualMajorant
  ring

/-- Monotonicity of the printed `(1.36)` majorant in its `E0`
normalization. -/
theorem cmp116Eq136ResidualMajorant_mono_E0
    {E0Small E0Large epsilon1 C1 : ℝ} {M q : ℕ}
    {C2 kappa1 delta kappa domainDist : ℝ}
    (hE0 : E0Small ≤ E0Large)
    (hepsilon1 : 0 ≤ epsilon1) (hC1 : 0 ≤ C1) :
    cmp116Eq136ResidualMajorant E0Small epsilon1 C1 M q
        C2 kappa1 delta kappa domainDist ≤
      cmp116Eq136ResidualMajorant E0Large epsilon1 C1 M q
        C2 kappa1 delta kappa domainDist := by
  let factor :=
    epsilon1 * C1 * (M : ℝ) ^ q *
      Real.exp (C2 * kappa1) *
      Real.exp (-((1 - 2 * delta) * kappa * domainDist))
  have hfactor : 0 ≤ factor := by
    dsimp [factor]
    positivity
  calc
    cmp116Eq136ResidualMajorant E0Small epsilon1 C1 M q
        C2 kappa1 delta kappa domainDist =
        E0Small * factor := by
          unfold cmp116Eq136ResidualMajorant
          dsimp [factor]
          ring
    _ ≤ E0Large * factor := mul_le_mul_of_nonneg_right hE0 hfactor
    _ = cmp116Eq136ResidualMajorant E0Large epsilon1 C1 M q
        C2 kappa1 delta kappa domainDist := by
          unfold cmp116Eq136ResidualMajorant
          dsimp [factor]
          ring

/-- Separate direct and Lemma-1 `(1.36)` estimates combine without hiding
either input. The only scalar ledger is the explicit split
`E0Direct + E0Lemma1 ≤ E0`. -/
theorem abs_cmp116PartialResidual_le_eq136
    {Y E : Type*}
    (directResidual lemma1Residual : Y → E → ℝ)
    {E0Direct E0Lemma1 E0 epsilon1 C1 : ℝ} {M q : ℕ}
    {C2 kappa1 delta kappa : ℝ}
    (domainDist : Y → ℝ)
    (hepsilon1 : 0 ≤ epsilon1) (hC1 : 0 ≤ C1)
    (hE0 : E0Direct + E0Lemma1 ≤ E0)
    (hdirect : ∀ y B,
      |directResidual y B| ≤
        cmp116Eq136ResidualMajorant E0Direct epsilon1 C1 M q
          C2 kappa1 delta kappa (domainDist y))
    (hlemma1 : ∀ y B,
      |lemma1Residual y B| ≤
        cmp116Eq136ResidualMajorant E0Lemma1 epsilon1 C1 M q
          C2 kappa1 delta kappa (domainDist y))
    (y : Y) (B : E) :
    |cmp116PartialResidual directResidual lemma1Residual y B| ≤
      cmp116Eq136ResidualMajorant E0 epsilon1 C1 M q
        C2 kappa1 delta kappa (domainDist y) := by
  calc
    |cmp116PartialResidual directResidual lemma1Residual y B| =
        |directResidual y B + lemma1Residual y B| := rfl
    _ ≤ |directResidual y B| + |lemma1Residual y B| := abs_add_le _ _
    _ ≤
        cmp116Eq136ResidualMajorant E0Direct epsilon1 C1 M q
            C2 kappa1 delta kappa (domainDist y) +
          cmp116Eq136ResidualMajorant E0Lemma1 epsilon1 C1 M q
            C2 kappa1 delta kappa (domainDist y) :=
      add_le_add (hdirect y B) (hlemma1 y B)
    _ =
        cmp116Eq136ResidualMajorant (E0Direct + E0Lemma1)
          epsilon1 C1 M q C2 kappa1 delta kappa (domainDist y) :=
      cmp116Eq136ResidualMajorant_add_E0
        E0Direct E0Lemma1 epsilon1 C1 M q
        C2 kappa1 delta kappa (domainDist y)
    _ ≤
        cmp116Eq136ResidualMajorant E0 epsilon1 C1 M q
          C2 kappa1 delta kappa (domainDist y) :=
      cmp116Eq136ResidualMajorant_mono_E0
        hE0 hepsilon1 hC1

/-- The direct equation-(80) estimate and the single named, reindexed
Lemma-1 certificate produce the full partial equation-(1.36) bound. -/
theorem abs_cmp116PartialResidual_le_eq136_of_lemma1Certificate
    {Y E : Type*}
    (directResidual : Y → E → ℝ)
    {E0Direct E0 epsilon1 C1 : ℝ} {M q : ℕ}
    {C2 kappa1 delta kappa : ℝ}
    (domainDist : Y → ℝ)
    (lemma1 :
      CMP116Lemma1Eq136ResidualCertificate
        domainDist epsilon1 C1 M q C2 kappa1 delta kappa)
    (hepsilon1 : 0 ≤ epsilon1) (hC1 : 0 ≤ C1)
    (hE0 : E0Direct + lemma1.E0 ≤ E0)
    (hdirect : ∀ y B,
      |directResidual y B| ≤
        cmp116Eq136ResidualMajorant E0Direct epsilon1 C1 M q
          C2 kappa1 delta kappa (domainDist y))
    (y : Y) (B : E) :
    |cmp116PartialResidual directResidual lemma1.residual y B| ≤
      cmp116Eq136ResidualMajorant E0 epsilon1 C1 M q
        C2 kappa1 delta kappa (domainDist y) :=
  abs_cmp116PartialResidual_le_eq136
    directResidual lemma1.residual domainDist
    hepsilon1 hC1 hE0 hdirect lemma1.bound y B

end

end YangMills.RG
