/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq214Cauchy
import YangMills.RG.BalabanCMP116Eq23Cutoff

/-!
# CMP116 equation (2.14): the literal analytic summand

This module records the nested analytic shape printed in CMP116 equation
(2.14), without replacing it by an arbitrary complex-valued `summand`.

The data separate the source ingredients which later have to be instantiated
by the Yang--Mills operators:

* the two finite Cauchy/interpolation families `σ(Δ)` and `τ(Y)`;
* the fixed outer product-Gaussian measure `μ₀`;
* the inner, parameter-dependent conditioned measure `μ_C`;
* the outer quadratic weight and inner bilinear weight;
* the sign `(-1)^|P|`, small-field cutoff on `Y₀`, and large-field cutoff on
  `P`;
* the exponential of the `τ`-weighted interaction potential.

`CMP116Eq214AnalyticData.term` is therefore the literal structural expression
of (2.14).  The operator kernels remain explicit data until the Wilson Hessian,
conditioned covariance and random-walk expansion are identified.

The two terminal theorems are nontrivial finite identities: summing the exact
cutoff factor over the powerset `P ⊆ Y₀^{c,*}` reconstructs the original
small-field cutoff, also in the presence of an arbitrary common analytic
factor.  This is the equation-(2.3) resummation needed inside (2.14).
-/

namespace YangMills.RG

open MeasureTheory
open scoped BigOperators Real Interval

/-- Source-shaped analytic data entering one CMP116 equation-(2.14) term. -/
structure CMP116Eq214AnalyticData
    (nDelta nY : ℕ) (Bond X B Psi Phi E : Type*)
    [MeasurableSpace X] [MeasurableSpace B] [Norm E] where
  deltaRadius : Fin nDelta → ℝ
  yRadius : Fin nY → ℝ
  mu0 : Measure X
  conditionedMeasure :
    (Fin nDelta → ℂ) → (Fin nY → ℂ) → Measure B
  outerWeight :
    (Fin nDelta → ℂ) → (Fin nY → ℂ) → Psi → Phi → X → ℂ
  innerWeight :
    (Fin nDelta → ℂ) → (Fin nY → ℂ) → Psi → Phi → X → B → ℂ
  bondField : B → Bond → E
  threshold : ℝ
  interactionExponent :
    (Fin nDelta → ℂ) → (Fin nY → ℂ) → Psi → Phi → B → ℂ

namespace CMP116Eq214AnalyticData

variable {nDelta nY : ℕ} {Bond X B Psi Phi E : Type*}
  [MeasurableSpace X] [MeasurableSpace B] [Norm E]

/-- The literal `(-1)^|P| χ_{k,Y₀} χ^c_{k,P}` factor in (2.14). -/
noncomputable def cutoffFactor
    (A : CMP116Eq214AnalyticData nDelta nY Bond X B Psi Phi E)
    (Y0 P : Finset Bond) (b : B) : ℂ :=
  (-1 : ℂ) ^ P.card *
    cmp116SmallFieldCutoff Y0 A.threshold (A.bondField b) *
    cmp116LargeFieldCutoff P A.threshold (A.bondField b)

/-- The complete integrand under the conditioned `B`-measure. -/
noncomputable def innerIntegrand
    (A : CMP116Eq214AnalyticData nDelta nY Bond X B Psi Phi E)
    (Y0 P : Finset Bond)
    (sigma : Fin nDelta → ℂ) (tau : Fin nY → ℂ)
    (psi : Psi) (phi : Phi) (x : X) (b : B) : ℂ :=
  A.innerWeight sigma tau psi phi x b * A.cutoffFactor Y0 P b *
    Complex.exp (A.interactionExponent sigma tau psi phi b)

/-- The nested `μ₀(X)` / conditioned `μ_C(B)` integral at fixed complex
interpolation parameters. -/
noncomputable def analyticIntegrand
    (A : CMP116Eq214AnalyticData nDelta nY Bond X B Psi Phi E)
    (Y0 P : Finset Bond)
    (sigma : Fin nDelta → ℂ) (tau : Fin nY → ℂ)
    (psi : Psi) (phi : Phi) : ℂ :=
  ∫ x, A.outerWeight sigma tau psi phi x *
    (∫ b, A.innerIntegrand Y0 P sigma tau psi phi x b
      ∂A.conditionedMeasure sigma tau) ∂A.mu0

/-- The literal equation-(2.14) term: first the `σ(Δ)` Cauchy family, then the
`τ(Y)` family, retaining all cross-coordinate dependence in the nested
Gaussian integrand. -/
noncomputable def term
    (A : CMP116Eq214AnalyticData nDelta nY Bond X B Psi Phi E)
    (Y0 P : Finset Bond) (psi : Psi) (phi : Phi) : ℂ :=
  cmp116Eq214CauchyFamily nDelta A.deltaRadius fun sigma =>
    cmp116Eq214CauchyFamily nY A.yRadius fun tau =>
      A.analyticIntegrand Y0 P sigma tau psi phi

@[simp] theorem term_zero_zero
    (A : CMP116Eq214AnalyticData 0 0 Bond X B Psi Phi E)
    (Y0 P : Finset Bond) (psi : Psi) (phi : Phi) :
    A.term Y0 P psi phi =
      A.analyticIntegrand Y0 P Fin.elim0 Fin.elim0 psi phi := by
  rfl

/-- Exact reconstruction of the exterior small-field cutoff after summing the
fixed-(2.14) cutoff factor over `P`. -/
theorem sum_cutoffFactor_eq_smallFieldCutoffs
    (A : CMP116Eq214AnalyticData nDelta nY Bond X B Psi Phi E)
    [DecidableEq Bond] (Y0 outsideCarrier : Finset Bond) (b : B) :
    ∑ P ∈ cmp116Eq23PIndex outsideCarrier, A.cutoffFactor Y0 P b =
      cmp116SmallFieldCutoff Y0 A.threshold (A.bondField b) *
        cmp116SmallFieldCutoff outsideCarrier A.threshold (A.bondField b) := by
  simpa [cutoffFactor] using
    (cmp116Eq23_cutoff_decomposition
      Y0 outsideCarrier A.threshold (A.bondField b)).symm

/-- The same cutoff resummation with an arbitrary common analytic factor,
which is the form used under the Gaussian integrals of (2.14). -/
theorem sum_common_mul_cutoffFactor
    (A : CMP116Eq214AnalyticData nDelta nY Bond X B Psi Phi E)
    [DecidableEq Bond] (Y0 outsideCarrier : Finset Bond) (b : B)
    (common : ℂ) :
    ∑ P ∈ cmp116Eq23PIndex outsideCarrier,
        common * A.cutoffFactor Y0 P b =
      common *
        (cmp116SmallFieldCutoff Y0 A.threshold (A.bondField b) *
          cmp116SmallFieldCutoff outsideCarrier A.threshold
            (A.bondField b)) := by
  rw [← Finset.mul_sum]
  exact congrArg (common * ·)
    (A.sum_cutoffFactor_eq_smallFieldCutoffs Y0 outsideCarrier b)

end CMP116Eq214AnalyticData

end YangMills.RG
