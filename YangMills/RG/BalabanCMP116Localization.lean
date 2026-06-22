/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Dmu0
import YangMills.RG.MayerCoverFactorization

/-!
# Balaban CMP116: localized `H(Z)` bridge

Balaban CMP116 (2.8)--(2.11) turns the post-`dmu0` integrand into localized
activities `H(Z)`, states connected-component factorization, and introduces the
hard-core compatibility function `zeta`.

This module does not prove Balaban's generalized random-walk localization,
measurability of the constructed local integrands, or the Lemma 3 decay
constants.  Instead it records the exact Lean interface those source theorems
must instantiate: each localized activity has spectator support inside its
declared Balaban domain, fluctuation support inside the active part of that
domain, and measurable dependence on the ultralocal fluctuation field.  Once
those support statements are supplied, the new CMP116 product Gaussian `dmu0`
gives the desired ultralocal component factorization.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills.RG

open MeasureTheory
open scoped BigOperators

/-- Balaban CMP116's hard-core compatibility function, in the same source shape
as (2.11): compatible pieces have value `1`; pieces whose declared active
supports meet inside `Omega` have value `0`. -/
def balabanCMP116HardCoreZeta {Bond ι : Type*} [DecidableEq Bond]
    (Omega : Finset Bond) (activeSupport : ι -> Finset Bond) (i j : ι) : Complex :=
  if Disjoint (Omega ∩ activeSupport i) (Omega ∩ activeSupport j) then 1 else 0

@[simp]
theorem balabanCMP116HardCoreZeta_of_disjoint
    {Bond ι : Type*} [DecidableEq Bond]
    {Omega : Finset Bond} {activeSupport : ι -> Finset Bond} {i j : ι}
    (h : Disjoint (Omega ∩ activeSupport i) (Omega ∩ activeSupport j)) :
    balabanCMP116HardCoreZeta Omega activeSupport i j = 1 := by
  simp [balabanCMP116HardCoreZeta, h]

@[simp]
theorem balabanCMP116HardCoreZeta_of_not_disjoint
    {Bond ι : Type*} [DecidableEq Bond]
    {Omega : Finset Bond} {activeSupport : ι -> Finset Bond} {i j : ι}
    (h : ¬ Disjoint (Omega ∩ activeSupport i) (Omega ∩ activeSupport j)) :
    balabanCMP116HardCoreZeta Omega activeSupport i j = 0 := by
  simp [balabanCMP116HardCoreZeta, h]

theorem balabanCMP116HardCoreZeta_eq_zero_iff
    {Bond ι : Type*} [DecidableEq Bond]
    (Omega : Finset Bond) (activeSupport : ι -> Finset Bond) (i j : ι) :
    balabanCMP116HardCoreZeta Omega activeSupport i j = 0 ↔
      ¬ Disjoint (Omega ∩ activeSupport i) (Omega ∩ activeSupport j) := by
  by_cases h : Disjoint (Omega ∩ activeSupport i) (Omega ∩ activeSupport j)
  · simp [balabanCMP116HardCoreZeta, h]
  · simp [balabanCMP116HardCoreZeta, h]

theorem balabanCMP116HardCoreZeta_eq_one_iff
    {Bond ι : Type*} [DecidableEq Bond]
    (Omega : Finset Bond) (activeSupport : ι -> Finset Bond) (i j : ι) :
    balabanCMP116HardCoreZeta Omega activeSupport i j = 1 ↔
      Disjoint (Omega ∩ activeSupport i) (Omega ∩ activeSupport j) := by
  by_cases h : Disjoint (Omega ∩ activeSupport i) (Omega ∩ activeSupport j)
  · simp [balabanCMP116HardCoreZeta, h]
  · simp [balabanCMP116HardCoreZeta, h]

/-- The source hard-core `zeta = 0` condition is the overlap half of the
existing `omegaOverlapGraph` adjacency relation. -/
theorem omegaOverlapGraph_adj_iff_ne_and_balabanCMP116HardCoreZeta_eq_zero
    {Bond ι : Type*} [DecidableEq Bond]
    (Omega : Finset Bond) (activeSupport : ι -> Finset Bond) (i j : ι) :
    (omegaOverlapGraph Omega activeSupport).Adj i j ↔
      i ≠ j ∧ balabanCMP116HardCoreZeta Omega activeSupport i j = 0 := by
  rw [omegaOverlapGraph_adj_iff,
    balabanCMP116HardCoreZeta_eq_zero_iff Omega activeSupport i j]

/-- Lean-facing package for the CMP116 localized activity family.

The source theorem still has to provide the two support-containment fields from
Balaban's generalized random-walk expansion of `(C^(k))^(1/2)`.  Once supplied,
the family can be fed directly to the existing Appendix-F local activity and
ultralocal factorization layers. -/
structure BalabanCMP116LocalizedActivityFamily
    (Bond : Type*) [Fintype Bond] [DecidableEq Bond]
    (lieDim : Nat) (Psi : Bond -> Type*) (ι : Type*) where
  Omega : Finset Bond
  activeSupport : ι -> Finset Bond
  activity : ι -> LocalActivity Bond Psi (fun _ => Fin lieDim -> Real) Complex
  activity_stronglyMeasurable :
    ∀ i, ∀ psi : ∀ b, Psi b,
      StronglyMeasurable
        (fun X : (∀ _ : Bond, Fin lieDim -> Real) =>
          (activity i).globalEval psi X)
  spectatorSupport_subset :
    ∀ i, (activity i).spectatorSupport ⊆ activeSupport i
  fluctuationSupport_subset :
    ∀ i, (activity i).fluctuationSupport ⊆ Omega ∩ activeSupport i

namespace BalabanCMP116LocalizedActivityFamily

variable {Bond : Type*} [Fintype Bond] [DecidableEq Bond]
    {lieDim : Nat} {Psi : Bond -> Type*} {ι : Type*}

/-- The Ω-overlap graph attached to a CMP116 localized activity family. -/
def omegaGraph (F : BalabanCMP116LocalizedActivityFamily Bond lieDim Psi ι) :
    SimpleGraph ι :=
  omegaOverlapGraph F.Omega F.activeSupport

/-- The source hard-core compatibility function attached to a CMP116 localized
activity family. -/
def zeta (F : BalabanCMP116LocalizedActivityFamily Bond lieDim Psi ι)
    (i j : ι) : Complex :=
  balabanCMP116HardCoreZeta F.Omega F.activeSupport i j

@[simp]
theorem omegaGraph_adj_iff_zeta_eq_zero
    (F : BalabanCMP116LocalizedActivityFamily Bond lieDim Psi ι) (i j : ι) :
    F.omegaGraph.Adj i j ↔ i ≠ j ∧ F.zeta i j = 0 := by
  exact omegaOverlapGraph_adj_iff_ne_and_balabanCMP116HardCoreZeta_eq_zero
    F.Omega F.activeSupport i j

/-- The raw CMP116 localized activities are strongly measurable in the
ultralocal fluctuation variable.  This is a source-facing field of the localized
activity package, not a theorem about an arbitrary Lean function. -/
theorem activity_globalEval_stronglyMeasurable
    (F : BalabanCMP116LocalizedActivityFamily Bond lieDim Psi ι)
    (i : ι) (psi : ∀ b, Psi b) :
    StronglyMeasurable
      (fun X : (∀ _ : Bond, Fin lieDim -> Real) =>
        (F.activity i).globalEval psi X) :=
  F.activity_stronglyMeasurable i psi

/-- A Mayer product over a CMP116 family has spectator support contained in the
union of the declared Balaban domains. -/
theorem mayerCoverActivity_spectatorSupport_subset_activeUnion
    [DecidableEq ι]
    (F : BalabanCMP116LocalizedActivityFamily Bond lieDim Psi ι)
    (I : Finset ι) :
    (LocalActivity.mayerCoverActivity I F.activity).spectatorSupport ⊆
      I.biUnion F.activeSupport := by
  intro x hx
  rw [LocalActivity.mayerCoverActivity_spectatorSupport] at hx
  rcases Finset.mem_biUnion.mp hx with ⟨i, hi, hxi⟩
  exact Finset.mem_biUnion.mpr ⟨i, hi, F.spectatorSupport_subset i hxi⟩

/-- A Mayer product over a CMP116 family has fluctuation support contained in
the active part of the union of the declared Balaban domains. -/
theorem mayerCoverActivity_fluctuationSupport_subset_omega_activeUnion
    [DecidableEq ι]
    (F : BalabanCMP116LocalizedActivityFamily Bond lieDim Psi ι)
    (I : Finset ι) :
    (LocalActivity.mayerCoverActivity I F.activity).fluctuationSupport ⊆
      F.Omega ∩ I.biUnion F.activeSupport :=
  LocalActivity.mayerCoverActivity_fluctuationSupport_subset_omega_biUnion_activeSupport
    I F.activity F.Omega F.activeSupport (fun i _hi => F.fluctuationSupport_subset i)

/-- The localized Mayer product only depends on spectator fields in the union
of declared Balaban domains and on fluctuation fields in the active part of that
union. -/
theorem mayerCoverActivity_globalEval_eq_of_agreeOn_activeUnion
    [DecidableEq ι]
    (F : BalabanCMP116LocalizedActivityFamily Bond lieDim Psi ι)
    (I : Finset ι)
    {psi₁ psi₂ : ∀ b, Psi b}
    {X₁ X₂ : ∀ _ : Bond, Fin lieDim -> Real}
    (hpsi : AgreeOn (I.biUnion F.activeSupport) psi₁ psi₂)
    (hX : AgreeOn (F.Omega ∩ I.biUnion F.activeSupport) X₁ X₂) :
    (LocalActivity.mayerCoverActivity I F.activity).globalEval psi₁ X₁ =
      (LocalActivity.mayerCoverActivity I F.activity).globalEval psi₂ X₂ := by
  refine LocalActivity.mayerCoverActivity_globalEval_eq_of_agreeOn I F.activity ?_ ?_
  · intro x hx
    exact hpsi x (mayerCoverActivity_spectatorSupport_subset_activeUnion F I hx)
  · intro x hx
    exact hX x (mayerCoverActivity_fluctuationSupport_subset_omega_activeUnion F I hx)

/-- CMP116 `dmu0` component factorization for a localized family.  This is the
formal consumer of the source statement "the localized `H(Z)` only depends on
fields in its Balaban domain": confined components in the Ω-overlap graph are
independent under the product Gaussian `dmu0`. -/
theorem mayerCoverActivity_integral_factor_confinedOmegaComponents_dmu0
    [DecidableEq ι]
    (F : BalabanCMP116LocalizedActivityFamily Bond lieDim Psi ι)
    (K : Finset ι) (psi : ∀ b, Psi b) :
    let Gamma := confinedComponents F.omegaGraph K
    ∫ X, (LocalActivity.mayerCoverActivity K F.activity).globalEval psi X
        ∂(balabanCMP116Dmu0 Bond lieDim)
      =
      ∏ C ∈ Gamma,
        (∫ X, (LocalActivity.mayerCoverActivity C F.activity).globalEval psi X
          ∂(balabanCMP116Dmu0 Bond lieDim)) := by
  haveI : IsProbabilityMeasure (balabanCMP116BondGaussian lieDim) :=
    balabanCMP116BondGaussian_isProbability lieDim
  simpa [balabanCMP116Dmu0, omegaGraph] using
    (LocalActivity.mayerCoverActivity_integral_factor_confinedOmegaComponents_of_fluctuationSupport_subset
      (Site := Bond) (β := Fin lieDim -> Real) (ι := ι)
      (μ := balabanCMP116BondGaussian lieDim)
      F.Omega F.activeSupport K F.activity psi
      (fun i _hi => F.fluctuationSupport_subset i))

/-- Cover-facing support containment for a connected component extracted from
the CMP116 Ω-overlap graph. -/
theorem mayerActivity_confinedComponentCover_fluctuationSupport_subset
    [DecidableEq ι]
    (F : BalabanCMP116LocalizedActivityFamily Bond lieDim Psi ι)
    (K : Finset ι) (r : ι) :
    ((OmegaConnectedCover.confinedComponentCover
        F.Omega F.activeSupport K r).mayerActivity F.activity).fluctuationSupport ⊆
      F.Omega ∩
        (confinedComponent F.omegaGraph K r).biUnion F.activeSupport := by
  simpa [omegaGraph] using
    (OmegaConnectedCover.mayerActivity_fluctuationSupport_subset_omega_biUnion_activeSupport
      (OmegaConnectedCover.confinedComponentCover F.Omega F.activeSupport K r)
      F.activity
      (fun i _hi => F.fluctuationSupport_subset i))

end BalabanCMP116LocalizedActivityFamily

end YangMills.RG
