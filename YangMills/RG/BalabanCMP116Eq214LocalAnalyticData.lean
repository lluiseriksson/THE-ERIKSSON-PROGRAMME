/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq214AnalyticSupport

/-!
# CMP116 equation (2.14): analytic data with physical field support in the type

The literal analytic term already fixes the two Gaussian integrals and the two
Cauchy families.  Its remaining locality debt is upstream: the three weights
which receive the spectator and fluctuation fields must not be able to inspect
those fields outside the localized region.

This module enforces that condition by type.  `CMP116Eq214LocalAnalyticData`
accepts restricted fields at its two declared supports.  Its forgetful map to
the existing global-field analytic data restricts global fields before any
weight is evaluated.  Consequently the primitive weight locality certificate,
and hence locality of the complete equation-(2.14) term, are derived rather
than supplied.

The construction does not choose the supports or manufacture an activity.
The source-specific CMP116 producer must still build these restricted weights
from the localized Wilson operators.
-/

namespace YangMills.RG

open MeasureTheory

noncomputable section

/-- Equation-(2.14) analytic data whose field dependence is physically local
by construction.  The Gaussian variables remain global finite-dimensional
coordinates; only the external spectator and fluctuation fields are restricted
to the declared finite carriers. -/
structure CMP116Eq214LocalAnalyticData
    (nDelta nY : ℕ) (Bond X B Site : Type*)
    (Psi Phi : Site → Type*) (E : Type*)
    [MeasurableSpace X] [MeasurableSpace B] [Norm E] where
  spectatorSupport : Finset Site
  fluctuationSupport : Finset Site
  deltaRadius : Fin nDelta → ℝ
  yRadius : Fin nY → ℝ
  mu0 : Measure X
  conditionedMeasure :
    (Fin nDelta → ℂ) → (Fin nY → ℂ) → Measure B
  outerWeight :
    (Fin nDelta → ℂ) → (Fin nY → ℂ) →
      RestrictedField spectatorSupport Psi →
      RestrictedField fluctuationSupport Phi → X → ℂ
  innerWeight :
    (Fin nDelta → ℂ) → (Fin nY → ℂ) →
      RestrictedField spectatorSupport Psi →
      RestrictedField fluctuationSupport Phi → X → B → ℂ
  bondField : B → Bond → E
  threshold : ℝ
  interactionExponent :
    (Fin nDelta → ℂ) → (Fin nY → ℂ) →
      RestrictedField spectatorSupport Psi →
      RestrictedField fluctuationSupport Phi → B → ℂ

namespace CMP116Eq214LocalAnalyticData

variable {nDelta nY : ℕ} {Bond X B Site E : Type*}
  {Psi Phi : Site → Type*}
  [MeasurableSpace X] [MeasurableSpace B] [Norm E]

/-- Forget the type-local interface by restricting every global field before
passing it to a physical weight. -/
def toAnalyticData
    (A : CMP116Eq214LocalAnalyticData nDelta nY Bond X B Site Psi Phi E) :
    CMP116Eq214AnalyticData nDelta nY Bond X B
      (∀ s, Psi s) (∀ s, Phi s) E where
  deltaRadius := A.deltaRadius
  yRadius := A.yRadius
  mu0 := A.mu0
  conditionedMeasure := A.conditionedMeasure
  outerWeight := fun sigma tau psi phi x =>
    A.outerWeight sigma tau
      (restrictGlobal A.spectatorSupport psi)
      (restrictGlobal A.fluctuationSupport phi) x
  innerWeight := fun sigma tau psi phi x b =>
    A.innerWeight sigma tau
      (restrictGlobal A.spectatorSupport psi)
      (restrictGlobal A.fluctuationSupport phi) x b
  bondField := A.bondField
  threshold := A.threshold
  interactionExponent := fun sigma tau psi phi b =>
    A.interactionExponent sigma tau
      (restrictGlobal A.spectatorSupport psi)
      (restrictGlobal A.fluctuationSupport phi) b

/-- The three primitive weights of the forgotten analytic data inherit their
declared supports definitionally. -/
theorem toAnalyticData_fieldWeightsSupportedOn
    (A : CMP116Eq214LocalAnalyticData nDelta nY Bond X B Site Psi Phi E) :
    A.toAnalyticData.FieldWeightsSupportedOn
      A.spectatorSupport A.fluctuationSupport := by
  constructor <;>
    intro psi₁ psi₂ phi₁ phi₂ hpsi hphi <;>
    simp only [toAnalyticData] <;>
    rw [restrictGlobal_eq_of_agreeOn hpsi,
      restrictGlobal_eq_of_agreeOn hphi] <;>
    intros <;> rfl

/-- The complete literal equation-(2.14) term is local once its physical
weights are supplied through the restricted-field interface. -/
theorem toAnalyticData_termSupportedOn
    (A : CMP116Eq214LocalAnalyticData nDelta nY Bond X B Site Psi Phi E)
    (Y0 P : Finset Bond) :
    A.toAnalyticData.TermSupportedOn Y0 P
      A.spectatorSupport A.fluctuationSupport :=
  CMP116Eq214AnalyticData.TermSupportedOn.of_fieldWeights
    A.toAnalyticData_fieldWeightsSupportedOn

/-- The literal inner integrand evaluated on restricted physical fields. -/
def localInnerIntegrand
    (A : CMP116Eq214LocalAnalyticData nDelta nY Bond X B Site Psi Phi E)
    (Y0 P : Finset Bond)
    (sigma : Fin nDelta → ℂ) (tau : Fin nY → ℂ)
    (psi : RestrictedField A.spectatorSupport Psi)
    (phi : RestrictedField A.fluctuationSupport Phi)
    (x : X) (b : B) : ℂ :=
  A.innerWeight sigma tau psi phi x b *
    A.toAnalyticData.cutoffFactor Y0 P b *
      Complex.exp (A.interactionExponent sigma tau psi phi b)

/-- The nested Gaussian integral before Cauchy extraction, still evaluated on
restricted physical fields. -/
def localAnalyticIntegrand
    (A : CMP116Eq214LocalAnalyticData nDelta nY Bond X B Site Psi Phi E)
    (Y0 P : Finset Bond)
    (sigma : Fin nDelta → ℂ) (tau : Fin nY → ℂ)
    (psi : RestrictedField A.spectatorSupport Psi)
    (phi : RestrictedField A.fluctuationSupport Phi) : ℂ :=
  ∫ x, A.outerWeight sigma tau psi phi x *
    (∫ b, A.localInnerIntegrand Y0 P sigma tau psi phi x b
      ∂A.conditionedMeasure sigma tau) ∂A.mu0

/-- The equation-(2.14) term as an actual `LocalActivity`, not as a global
function later accompanied by a support claim. -/
def localTerm
    (A : CMP116Eq214LocalAnalyticData nDelta nY Bond X B Site Psi Phi E)
    (Y0 P : Finset Bond) : LocalActivity Site Psi Phi ℂ where
  spectatorSupport := A.spectatorSupport
  fluctuationSupport := A.fluctuationSupport
  eval psi phi :=
    cmp116Eq214CauchyFamily nDelta A.deltaRadius fun sigma =>
      cmp116Eq214CauchyFamily nY A.yRadius fun tau =>
        A.localAnalyticIntegrand Y0 P sigma tau psi phi

/-- Forgetting the restricted fields recovers the existing literal analytic
term exactly.  Thus the local activity is source-faithful rather than a
post-hoc function chosen to satisfy the desired equality. -/
@[simp] theorem globalEval_localTerm
    (A : CMP116Eq214LocalAnalyticData nDelta nY Bond X B Site Psi Phi E)
    (Y0 P : Finset Bond) (psi : ∀ s, Psi s) (phi : ∀ s, Phi s) :
    (A.localTerm Y0 P).globalEval psi phi =
      A.toAnalyticData.term Y0 P psi phi := by
  rfl

end CMP116Eq214LocalAnalyticData

end

end YangMills.RG
