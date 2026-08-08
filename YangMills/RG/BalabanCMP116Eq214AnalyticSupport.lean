/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq214AnalyticResummation
import YangMills.RG.LocalFunctional

/-!
# CMP116 equation (2.14): the locality obligation before activity identification

The complex summand in the physical `D/P/Z₀/Z₀'` stack is already fixed
literally by `CMP116Eq214AnalyticData.term`.  What does not follow from that
identity, or from any norm majorant, is that the resulting function reads the
spectator and fluctuation fields only on the finite support of the physical
localized activity.

This module records that missing statement as a property of the existing
analytic term, rather than manufacturing a local activity whose value is
defined to be the desired sum.  It proves two source-neutral facts:

* term support is monotone under enlargement of the declared carriers;
* termwise support passes through the literal finite resummation to `H(Z)`.

It also records the necessary locality consequence of any future physical
activity identification.  No source locality theorem is assumed or claimed:
the concrete CMP116 construction of the analytic data must prove the termwise
support property from its localized operators.
-/

namespace YangMills.RG

open Finset

namespace CMP116Eq214AnalyticData

/-- A literal equation-(2.14) term reads the two global fields only on the
declared finite supports.  This is an extensional property of the already
defined term; it does not construct a replacement summand. -/
def TermSupportedOn
    {nDelta nY : ℕ} {Bond X B Site E : Type*}
    {Psi Phi : Site → Type*}
    [MeasurableSpace X] [MeasurableSpace B] [Norm E]
    (A : CMP116Eq214AnalyticData nDelta nY Bond X B
      (∀ s, Psi s) (∀ s, Phi s) E)
    (Y0 P : Finset Bond) (spectatorSupport fluctuationSupport : Finset Site) :
    Prop :=
  ∀ ψ₁ ψ₂ φ₁ φ₂,
    AgreeOn spectatorSupport ψ₁ ψ₂ →
    AgreeOn fluctuationSupport φ₁ φ₂ →
      A.term Y0 P ψ₁ φ₁ = A.term Y0 P ψ₂ φ₂

/-- A support certificate remains valid after enlarging either field carrier. -/
theorem TermSupportedOn.mono
    {nDelta nY : ℕ} {Bond X B Site E : Type*}
    {Psi Phi : Site → Type*}
    [MeasurableSpace X] [MeasurableSpace B] [Norm E]
    {A : CMP116Eq214AnalyticData nDelta nY Bond X B
      (∀ s, Psi s) (∀ s, Phi s) E}
    {Y0 P : Finset Bond}
    {spectatorSupport fluctuationSupport
      spectatorSupport' fluctuationSupport' : Finset Site}
    (h : A.TermSupportedOn Y0 P spectatorSupport fluctuationSupport)
    (hψ : spectatorSupport ⊆ spectatorSupport')
    (hφ : fluctuationSupport ⊆ fluctuationSupport') :
    A.TermSupportedOn Y0 P spectatorSupport' fluctuationSupport' := by
  intro ψ₁ ψ₂ φ₁ φ₂ hψ' hφ'
  apply h ψ₁ ψ₂ φ₁ φ₂
  · intro x hx
    exact hψ' x (hψ hx)
  · intro x hx
    exact hφ' x (hφ hx)

/-- Primitive field-locality certificate for the three equation-(2.14)
weights that actually receive the spectator and fluctuation fields.

The Gaussian laws, bond field and cutoffs do not receive `ψ` or `φ`; hence no
support premise is attached to them.  This record separates the source-facing
operator-locality work from the formal passage through the two Gaussian
integrals and the two Cauchy families. -/
structure FieldWeightsSupportedOn
    {nDelta nY : ℕ} {Bond X B Site E : Type*}
    {Psi Phi : Site → Type*}
    [MeasurableSpace X] [MeasurableSpace B] [Norm E]
    (A : CMP116Eq214AnalyticData nDelta nY Bond X B
      (∀ s, Psi s) (∀ s, Phi s) E)
    (spectatorSupport fluctuationSupport : Finset Site) : Prop where
  outerWeight_eq :
    ∀ ψ₁ ψ₂ φ₁ φ₂,
      AgreeOn spectatorSupport ψ₁ ψ₂ →
      AgreeOn fluctuationSupport φ₁ φ₂ →
      ∀ sigma tau x,
        A.outerWeight sigma tau ψ₁ φ₁ x =
          A.outerWeight sigma tau ψ₂ φ₂ x
  innerWeight_eq :
    ∀ ψ₁ ψ₂ φ₁ φ₂,
      AgreeOn spectatorSupport ψ₁ ψ₂ →
      AgreeOn fluctuationSupport φ₁ φ₂ →
      ∀ sigma tau x b,
        A.innerWeight sigma tau ψ₁ φ₁ x b =
          A.innerWeight sigma tau ψ₂ φ₂ x b
  interactionExponent_eq :
    ∀ ψ₁ ψ₂ φ₁ φ₂,
      AgreeOn spectatorSupport ψ₁ ψ₂ →
      AgreeOn fluctuationSupport φ₁ φ₂ →
      ∀ sigma tau b,
        A.interactionExponent sigma tau ψ₁ φ₁ b =
          A.interactionExponent sigma tau ψ₂ φ₂ b

/-- Locality of the primitive physical weights propagates through the exact
cutoff, both Gaussian integrals and both finite Cauchy families.  Thus it
produces the term-support obligation without assuming the term equality
itself. -/
theorem TermSupportedOn.of_fieldWeights
    {nDelta nY : ℕ} {Bond X B Site E : Type*}
    {Psi Phi : Site → Type*}
    [MeasurableSpace X] [MeasurableSpace B] [Norm E]
    {A : CMP116Eq214AnalyticData nDelta nY Bond X B
      (∀ s, Psi s) (∀ s, Phi s) E}
    {Y0 P : Finset Bond}
    {spectatorSupport fluctuationSupport : Finset Site}
    (h : A.FieldWeightsSupportedOn spectatorSupport fluctuationSupport) :
    A.TermSupportedOn Y0 P spectatorSupport fluctuationSupport := by
  intro ψ₁ ψ₂ φ₁ φ₂ hψ hφ
  unfold term
  congr 1
  funext sigma
  congr 1
  funext tau
  unfold analyticIntegrand
  apply MeasureTheory.integral_congr_ae
  filter_upwards with x
  rw [h.outerWeight_eq ψ₁ ψ₂ φ₁ φ₂ hψ hφ sigma tau x]
  congr 1
  apply MeasureTheory.integral_congr_ae
  filter_upwards with b
  unfold innerIntegrand
  rw [h.innerWeight_eq ψ₁ ψ₂ φ₁ φ₂ hψ hφ sigma tau x b,
    h.interactionExponent_eq ψ₁ ψ₂ φ₁ φ₂ hψ hφ sigma tau b]

end CMP116Eq214AnalyticData

/-- The literal analytic resummation `H(Z)` reads the fields only on the
declared supports once every term in its dependent physical index stack does.

The premise is deliberately termwise and refers to the existing analytic
data.  In particular, it is not an equality with a separately supplied local
activity and cannot make that equality true by definition. -/
theorem balabanCMP116H_eq_of_agreeOn_of_analyticTermSupportedOn
    {d M N' nDelta nY : ℕ} [NeZero M] [NeZero N']
    {ιZ0' X B Site E : Type*} [DecidableEq ιZ0']
    {Psi Phi : Site → Type*}
    [MeasurableSpace X] [MeasurableSpace B] [Norm E]
    (domainFamily allowed : Finset (Finset (FinBox d N')))
    (ambient distinguished : Finset (PhysicalBond d (M * N')))
    (Z0PrimeIndex :
      Finset (FinBox d N') →
      Finset (Finset (FinBox d N')) →
      Finset (PhysicalBond d (M * N')) →
      Finset (FinBox d N') → Finset ιZ0')
    (analyticData :
      Finset (FinBox d N') →
      Finset (Finset (FinBox d N')) →
      Finset (PhysicalBond d (M * N')) →
      Finset (FinBox d N') → ιZ0' →
        CMP116Eq214AnalyticData nDelta nY
          (PhysicalBond d (M * N')) X B
          (∀ s, Psi s) (∀ s, Phi s) E)
    (termWeight :
      Finset (FinBox d N') →
      Finset (Finset (FinBox d N')) →
      Finset (PhysicalBond d (M * N')) →
      Finset (FinBox d N') → ιZ0' → ℝ)
    (spectatorSupport fluctuationSupport :
      Finset (FinBox d N') → Finset Site)
    (hsupport : ∀ Z x,
      x ∈ cmp116HIndexFinset
        (cmp116Eq214AnalyticResummation domainFamily allowed ambient
          distinguished Z0PrimeIndex analyticData termWeight) Z →
      (analyticData Z x.1.1 x.1.2 x.2.1 x.2.2).TermSupportedOn
        (cmp116Eq214SmallFieldBondCarrier ambient distinguished x.1.1)
        x.1.2 (spectatorSupport Z) (fluctuationSupport Z))
    (Z : Finset (FinBox d N'))
    (ψ₁ ψ₂ : ∀ s, Psi s) (φ₁ φ₂ : ∀ s, Phi s)
    (hψ : AgreeOn (spectatorSupport Z) ψ₁ ψ₂)
    (hφ : AgreeOn (fluctuationSupport Z) φ₁ φ₂) :
    balabanCMP116H
        (cmp116Eq214AnalyticResummation domainFamily allowed ambient
          distinguished Z0PrimeIndex analyticData termWeight) Z ψ₁ φ₁ =
      balabanCMP116H
        (cmp116Eq214AnalyticResummation domainFamily allowed ambient
          distinguished Z0PrimeIndex analyticData termWeight) Z ψ₂ φ₂ := by
  classical
  unfold balabanCMP116H
  apply Finset.sum_congr rfl
  intro x hx
  exact hsupport Z x hx ψ₁ ψ₂ φ₁ φ₂ hψ hφ

/-- Any genuine identification of the analytic resummation with a physical
local activity forces the analytic `H(Z)` to inherit that activity's finite
support.  This is a guardrail: a future identification must prove content that
is absent from a norm estimate alone. -/
theorem balabanCMP116H_eq_of_agreeOn_of_activityIdentification
    {σ ιD ιP ιZ0 ιZ0' Site : Type*}
    [DecidableEq ιD] [DecidableEq ιP]
    [DecidableEq ιZ0] [DecidableEq ιZ0']
    {Psi Phi : Site → Type*}
    (R : CMP116HResummation σ ιD ιP ιZ0 ιZ0'
      (∀ s, Psi s) (∀ s, Phi s))
    (activity : σ → LocalActivity Site Psi Phi ℂ)
    (hidentify : ∀ Z ψ φ,
      (activity Z).globalEval ψ φ = balabanCMP116H R Z ψ φ)
    (Z : σ) (ψ₁ ψ₂ : ∀ s, Psi s) (φ₁ φ₂ : ∀ s, Phi s)
    (hψ : AgreeOn (activity Z).spectatorSupport ψ₁ ψ₂)
    (hφ : AgreeOn (activity Z).fluctuationSupport φ₁ φ₂) :
    balabanCMP116H R Z ψ₁ φ₁ = balabanCMP116H R Z ψ₂ φ₂ := by
  rw [← hidentify Z ψ₁ φ₁, ← hidentify Z ψ₂ φ₂]
  exact LocalActivity.globalEval_eq_of_agreeOn (activity Z) hψ hφ

end YangMills.RG
