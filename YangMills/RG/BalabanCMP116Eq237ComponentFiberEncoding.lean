/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq237FiberEntropyBoundary

/-!
# Componentwise encoding of the CMP116 equation-(2.37) fiber

At fixed `Z0'`, the remaining `Z0` choices must factor through choices local
to the connected components printed in equation (2.37).  This module turns
that source dictionary into the required fiber-entropy estimate.  The caller
supplies an actual componentwise encoding and a count for each component; it
does not supply the final cardinality/product inequality.
-/

namespace YangMills.RG

noncomputable section

/-- Source-facing component dictionary for one fixed equation-(2.37) fiber.
Every global `Z0` choice is encoded by one finite choice on each connected
component, the encoding is injective on the fiber, and each local choice set
is bounded by the literal component factor. -/
structure CMP116Eq237ComponentFiberEncoding
    {ιZ0 ιC ιChoice : Type*}
    (fiber : Finset ιZ0)
    (components : Finset ιC)
    (componentFactor : ιC → ℝ) where
  componentChoices : ιC → Finset ιChoice
  componentChoiceOf : ιZ0 → ιC → ιChoice
  choice_mem :
    ∀ Z0, Z0 ∈ fiber →
      ∀ Zi, Zi ∈ components →
        componentChoiceOf Z0 Zi ∈ componentChoices Zi
  choice_ext :
    ∀ Z0₁, Z0₁ ∈ fiber →
      ∀ Z0₂, Z0₂ ∈ fiber →
        (∀ Zi, Zi ∈ components →
          componentChoiceOf Z0₁ Zi = componentChoiceOf Z0₂ Zi) →
        Z0₁ = Z0₂
  choice_card_le :
    ∀ Zi, Zi ∈ components →
      ((componentChoices Zi).card : ℝ) ≤ componentFactor Zi

/-- An injective componentwise encoding bounds the number of objects in the
fiber by the product of the finite local-choice cardinalities. -/
theorem cmp116Eq237_fiber_card_le_prod_componentChoice_card
    {ιZ0 ιC ιChoice : Type*}
    (fiber : Finset ιZ0)
    (components : Finset ιC)
    (componentChoices : ιC → Finset ιChoice)
    (componentChoiceOf : ιZ0 → ιC → ιChoice)
    (hchoice_mem :
      ∀ Z0, Z0 ∈ fiber →
        ∀ Zi, Zi ∈ components →
          componentChoiceOf Z0 Zi ∈ componentChoices Zi)
    (hchoice_ext :
      ∀ Z0₁, Z0₁ ∈ fiber →
        ∀ Z0₂, Z0₂ ∈ fiber →
          (∀ Zi, Zi ∈ components →
            componentChoiceOf Z0₁ Zi = componentChoiceOf Z0₂ Zi) →
          Z0₁ = Z0₂) :
    fiber.card ≤
      ∏ Zi ∈ components, (componentChoices Zi).card := by
  classical
  let Source := {Z0 // Z0 ∈ fiber}
  let Component := {Zi // Zi ∈ components}
  let Target :=
    ∀ Zi : Component,
      {choice // choice ∈ componentChoices Zi.1}
  let encode : Source → Target :=
    fun Z0 Zi =>
      ⟨componentChoiceOf Z0.1 Zi.1,
        hchoice_mem Z0.1 Z0.2 Zi.1 Zi.2⟩
  have hencode : Function.Injective encode := by
    intro Z0₁ Z0₂ heq
    apply Subtype.ext
    apply hchoice_ext Z0₁.1 Z0₁.2 Z0₂.1 Z0₂.2
    intro Zi hZi
    have hpoint :=
      congrFun heq (⟨Zi, hZi⟩ : Component)
    exact congrArg Subtype.val hpoint
  have hcard :
      Fintype.card Source ≤ Fintype.card Target :=
    Fintype.card_le_of_injective encode hencode
  have hcard' :
      fiber.card ≤
        ∏ Zi ∈ components.attach, (componentChoices Zi.1).card := by
    simpa [Source, Component, Target, Fintype.card_pi] using hcard
  exact hcard'.trans_eq
    (Finset.prod_attach components
      (fun Zi => (componentChoices Zi).card))

/-- Componentwise choice counts bounded by the literal factors of (2.37)
produce the genuine fiber-entropy bound consumed by the contour theorem. -/
theorem cmp116Eq237_fiberEntropy_of_componentEncoding
    {ιZ0 ιC ιChoice : Type*}
    (fiber : Finset ιZ0)
    (components : Finset ιC)
    (componentChoices : ιC → Finset ιChoice)
    (componentChoiceOf : ιZ0 → ιC → ιChoice)
    (componentFactor : ιC → ℝ)
    (hchoice_mem :
      ∀ Z0, Z0 ∈ fiber →
        ∀ Zi, Zi ∈ components →
          componentChoiceOf Z0 Zi ∈ componentChoices Zi)
    (hchoice_ext :
      ∀ Z0₁, Z0₁ ∈ fiber →
        ∀ Z0₂, Z0₂ ∈ fiber →
          (∀ Zi, Zi ∈ components →
            componentChoiceOf Z0₁ Zi = componentChoiceOf Z0₂ Zi) →
          Z0₁ = Z0₂)
    (hcomponent :
      ∀ Zi, Zi ∈ components →
        ((componentChoices Zi).card : ℝ) ≤ componentFactor Zi) :
    (fiber.card : ℝ) ≤
      ∏ Zi ∈ components, componentFactor Zi := by
  classical
  have hcardNat :=
    cmp116Eq237_fiber_card_le_prod_componentChoice_card
      fiber components componentChoices componentChoiceOf
      hchoice_mem hchoice_ext
  have hcardReal :
      (fiber.card : ℝ) ≤
        ∏ Zi ∈ components, ((componentChoices Zi).card : ℝ) := by
    exact_mod_cast hcardNat
  exact hcardReal.trans
    (Finset.prod_le_prod
      (fun Zi hZi => by positivity)
      hcomponent)

namespace CMP116Eq237ComponentFiberEncoding

/-- A source component dictionary directly discharges the pure fiber-entropy
premise; no global fiber cardinality estimate is stored in the record. -/
theorem fiberEntropy
    {ιZ0 ιC ιChoice : Type*}
    {fiber : Finset ιZ0}
    {components : Finset ιC}
    {componentFactor : ιC → ℝ}
    (S :
      CMP116Eq237ComponentFiberEncoding
        (ιChoice := ιChoice) fiber components componentFactor) :
    (fiber.card : ℝ) ≤
      ∏ Zi ∈ components, componentFactor Zi :=
  cmp116Eq237_fiberEntropy_of_componentEncoding
    fiber components S.componentChoices S.componentChoiceOf componentFactor
    S.choice_mem S.choice_ext S.choice_card_le

end CMP116Eq237ComponentFiberEncoding

end

end YangMills.RG
