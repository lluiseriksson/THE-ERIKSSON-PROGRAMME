/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80SourcePi4FTCIntegralLocalization
import YangMills.RG.BalabanCMP102Eq80SourcePi4VertexPolynomialFTC

/-!
# The literal fully decoupled residual of the source FTC tree

The connected terms in the CMP116 FTC expansion must be separated from the
leaf obtained by setting every expanded weakening coordinate to zero.  This
file identifies that leaf exactly, first for the generic FTC tree and then
for the physical equation-(80) vertex polynomial.

The resulting object is called the *fully decoupled residual*.  We do not yet
identify it with Balaban's `V''_k`; that source dictionary additionally
requires the residual estimate (1.36).
-/

namespace YangMills.RG

noncomputable section

private abbrev PhysicalField (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalField M Q Nc →L[ℝ] PhysicalField M Q Nc

/-- Follow only the zero-coordinate base branch of an FTC tree. -/
def CMP116FTCExpansionTree.decoupledLeaf :
    {n : ℕ} → CMP116FTCExpansionTree E n → E
  | 0, .leaf value => value
  | _ + 1, .node _ _ base _ => base.decoupledLeaf

/-- The base branch of the literal real weakening tree is evaluation with
all listed coordinates set to zero. -/
theorem cmp116RealWeakeningFTCExpansionTree_decoupledLeaf
    {D : Type*} [DecidableEq D]
    (f : (D → ℝ) → ℝ) (s : D → ℝ) (L : List D) :
    (cmp116RealWeakeningFTCExpansionTree f s L).decoupledLeaf =
      f (cmp116SetRealWeakeningList s L 0) := by
  induction L generalizing s f with
  | nil =>
      simp [cmp116RealWeakeningFTCExpansionTree,
        CMP116FTCExpansionTree.decoupledLeaf]
  | cons d tail ih =>
      change
        (cmp116RealWeakeningFTCExpansionTree f
          (Function.update s d 0) tail).decoupledLeaf =
            f (cmp116SetRealWeakeningList s (d :: tail) 0)
      rw [ih]
      congr 1
      funext x
      by_cases hx : x ∈ tail
      · simp [cmp116SetRealWeakeningList, hx]
      · by_cases hxd : x = d
        · subst x
          simp [cmp116SetRealWeakeningList, hx]
        · simp [cmp116SetRealWeakeningList, hx, hxd]

/-- Literal fully decoupled leaf of the physical equation-(80) vertex
polynomial FTC construction. -/
noncomputable def cmp102Eq80SourcePi4FullyDecoupledResidual
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
    (base : FinBox 4 (2 * Q) → ℝ)
    (coordinates : List (FinBox 4 (2 * Q)))
    (s : FinBox 4 (2 * Q) → ℝ)
    (L : List (FinBox 4 (2 * Q)))
    (A : PhysicalField M Q Nc) : ℝ :=
  cmp102Eq80SourcePi4RealPotentialVertexPolynomial
    (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J
    base coordinates (cmp116SetRealWeakeningList s L 0) A

/-- The physical FTC tree's base leaf is definitionally the fully decoupled
residual just constructed. -/
theorem
    cmp102Eq80SourcePi4VertexPolynomialFTCExpansionTree_decoupledLeaf
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
    (base : FinBox 4 (2 * Q) → ℝ)
    (coordinates : List (FinBox 4 (2 * Q)))
    (s : FinBox 4 (2 * Q) → ℝ)
    (L : List (FinBox 4 (2 * Q)))
    (A : PhysicalField M Q Nc) :
    (cmp102Eq80SourcePi4VertexPolynomialFTCExpansionTree
      (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J
      base coordinates s L A).decoupledLeaf =
        cmp102Eq80SourcePi4FullyDecoupledResidual
          (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J
          base coordinates s L A := by
  unfold cmp102Eq80SourcePi4VertexPolynomialFTCExpansionTree
    cmp102Eq80SourcePi4FullyDecoupledResidual
  exact cmp116RealWeakeningFTCExpansionTree_decoupledLeaf _ s L

/-- Setting listed coordinates to zero preserves the physical unit-shifted
region. -/
theorem cmp116SetRealWeakeningList_unitShifted_zero
    {D : Type*} [DecidableEq D]
    (s : D → ℝ) (L : List D)
    (hs : ∀ x, ‖(s x : ℂ) - 1‖ ≤ (1 : ℝ)) :
    ∀ x, ‖(cmp116SetRealWeakeningList s L 0 x : ℂ) - 1‖ ≤
      (1 : ℝ) := by
  intro x
  by_cases hx : x ∈ L
  · simp [cmp116SetRealWeakeningList, hx]
  · simpa [cmp116SetRealWeakeningList, hx] using hs x

/-- Setting listed coordinates to zero preserves every physical absolute cap
`Rweak ≥ 1`. -/
theorem cmp116SetRealWeakeningList_cap_zero
    {D : Type*} [DecidableEq D]
    (s : D → ℝ) (L : List D) (Rweak : ℝ)
    (hRweak : 1 ≤ Rweak)
    (hs : ∀ x, ‖(s x : ℂ)‖ ≤ Rweak) :
    ∀ x, ‖(cmp116SetRealWeakeningList s L 0 x : ℂ)‖ ≤ Rweak := by
  intro x
  by_cases hx : x ∈ L
  · simp [cmp116SetRealWeakeningList, hx, zero_le_one.trans hRweak]
  · simpa [cmp116SetRealWeakeningList, hx] using hs x

end

end YangMills.RG
