/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80SourcePi4RealMixedPotentialDerivative
import YangMills.RG.BalabanCMP116FTCInterpolation

/-!
# The literal equation-(80) mixed FTC tree

This module builds the finite iterated FTC tree for the complete physical
CMP102 equation-(80) potential.  Each node curve varies one source `Pi^4`
weakening coordinate.  Its derivative is the source-produced mixed covariance
directional derivative, with the actual Fréchet derivative of `V₀` evaluated
at the shifted physical field.

The construction is not an endpoint Möbius expansion.  The coupled-endpoint
theorem below identifies the tree endpoint with the literal potential after
all coordinates in the chosen list have been set to one.
-/

open scoped RealInnerProductSpace

namespace YangMills.RG

noncomputable section

private abbrev PhysicalField (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalField M Q Nc →L[ℝ] PhysicalField M Q Nc

/-- Set each real weakening coordinate in `L` to `z`. -/
def cmp116SetRealWeakeningList
    {D : Type*} [DecidableEq D]
    (s : D → ℝ) (L : List D) (z : ℝ) : D → ℝ :=
  fun x => if x ∈ L then z else s x

@[simp] theorem cmp116SetRealWeakeningList_nil
    {D : Type*} [DecidableEq D]
    (s : D → ℝ) (z : ℝ) :
    cmp116SetRealWeakeningList s [] z = s := by
  funext x
  simp [cmp116SetRealWeakeningList]

theorem cmp116SetRealWeakeningList_cons_of_not_mem
    {D : Type*} [DecidableEq D]
    (s : D → ℝ) (d : D) (L : List D) (z : ℝ)
    (_hdL : d ∉ L) :
    cmp116SetRealWeakeningList s (d :: L) z =
      Function.update (cmp116SetRealWeakeningList s L z) d z := by
  funext x
  by_cases hxd : x = d
  · subst x
    simp [cmp116SetRealWeakeningList]
  · simp [cmp116SetRealWeakeningList, hxd]

/-- Literal finite-depth FTC tree for the complete mixed equation-(80)
potential at one fixed physical field. -/
noncomputable def cmp102Eq80SourcePi4MixedPotentialFTCExpansionTree
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (D D₃ : PhysicalField M Q Nc → PhysicalField M Q Nc)
    (V₀ : PhysicalField M Q Nc → ℝ)
    (Δπ : PhysicalEndomorphism M Q Nc)
    (J : PhysicalField M Q Nc)
    (s : FinBox 4 (2 * Q) → ℝ)
    (S : Finset (FinBox 4 (2 * Q)))
    (L : List (FinBox 4 (2 * Q)))
    (A : PhysicalField M Q Nc) :
    CMP116FTCExpansionTree ℝ L.length :=
  match L with
  | [] =>
      .leaf
        (cmp102Eq80SourcePi4RealMixedPotential
          (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J s S A)
  | d :: tail =>
      let endpointS := cmp116SetRealWeakeningList s tail 1
      .node
        (cmp102Eq80SourcePi4RealMixedPotentialCurve
          (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J
          endpointS S d A)
        (fun t =>
          cmp102Eq80SourcePi4RealMixedPotentialCurveDerivative
            (R := R) anchor K hc hmass hK D D₃ Δπ J
            endpointS S d A t
            (fderiv ℝ V₀
              (A -
                cmp116SourcePi4RealMixedCovarianceOperatorCurve
                  (R := R) anchor K hc hmass hK endpointS S d t
                  (D A))))
        (cmp102Eq80SourcePi4MixedPotentialFTCExpansionTree
          (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J
          (Function.update s d 0) S tail A)
        (fun t =>
          cmp102Eq80SourcePi4MixedPotentialFTCExpansionTree
            (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J
            (Function.update s d t) (insert d S) tail A)

/-- The coupled endpoint is the literal mixed equation-(80) potential with
every remaining listed coordinate set to one. -/
theorem cmp102Eq80SourcePi4MixedPotentialFTCExpansionTree_coupledEndpoint
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (D D₃ : PhysicalField M Q Nc → PhysicalField M Q Nc)
    (V₀ : PhysicalField M Q Nc → ℝ)
    (Δπ : PhysicalEndomorphism M Q Nc)
    (J : PhysicalField M Q Nc)
    (s : FinBox 4 (2 * Q) → ℝ)
    (S : Finset (FinBox 4 (2 * Q)))
    (L : List (FinBox 4 (2 * Q))) (hL : L.Nodup)
    (A : PhysicalField M Q Nc) :
    (cmp102Eq80SourcePi4MixedPotentialFTCExpansionTree
      (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J s S L A).coupledEndpoint =
      cmp102Eq80SourcePi4RealMixedPotential
        (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J
        (cmp116SetRealWeakeningList s L 1) S A := by
  cases L with
  | nil =>
      simp [cmp102Eq80SourcePi4MixedPotentialFTCExpansionTree,
        CMP116FTCExpansionTree.coupledEndpoint]
  | cons d tail =>
      have hdTail : d ∉ tail := (List.nodup_cons.mp hL).1
      change
        cmp102Eq80SourcePi4RealMixedPotentialCurve
            (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J
            (cmp116SetRealWeakeningList s tail 1) S d A 1 =
          cmp102Eq80SourcePi4RealMixedPotential
            (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J
            (cmp116SetRealWeakeningList s (d :: tail) 1) S A
      rw [cmp102Eq80SourcePi4RealMixedPotentialCurve_eq,
        cmp116SetRealWeakeningList_cons_of_not_mem s d tail 1 hdTail]

end

end YangMills.RG
