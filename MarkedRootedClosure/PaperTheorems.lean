/- Copyright (c) 2026 Lluis Eriksson.
SPDX-License-Identifier: AGPL-3.0-or-later -/

import YangMills.KP.RootedLeafSummation
import YangMills.KP.RootedCatalanExact
import YangMills.RG.AppendixFSecondUrsellLeafSummation

/-!
# Publication-facing endpoints

This file gives short, stable names to the five machine-checked theorems used
in the accompanying paper.  The proofs are direct applications of the pinned
upstream theorems; no new axiom, opaque assumption, or model-specific claim is
introduced here.
-/

namespace MarkedRootedClosure

open Finset
open SimpleGraph
open scoped BigOperators
open YangMills.RG

/-- Normalized child-factorial mass of complete-graph spanning trees.

The factor `(n+1)/(n+1)!` is the normalization that occurs after marking one
vertex in an `(n+1)`-vertex Ursell term. -/
theorem normalizedRootedChildFactorialTreeBound (n : ℕ) :
    ((n : ℝ) + 1) *
        (((n + 1).factorial : ℝ))⁻¹ *
        (∑ T ∈ YangMills.KP.spanningTrees
            (⊤ : SimpleGraph (Fin (n + 1))),
          ∏ v : Fin (n + 1),
            ((YangMills.KP.rootedChildCount T v).factorial : ℝ))
      ≤ (4 : ℝ) ^ n :=
  YangMills.KP.rootedChildCount_factorialTreeSum_normalized_le_four_pow n

/-- Exact value of the normalized child-factorial mass: it EQUALS the
`n`-th Catalan number.  Mathematically this implies
`normalizedRootedChildFactorialTreeBound` via `catalan n ≤ 4^n`; the
compiled proof of that bound is the independent pre-Catalan argument in
`YangMills.KP.RootedLeafSummation`. -/
theorem normalizedRootedChildFactorialTreeCatalanIdentity (n : ℕ) :
    ((n : ℝ) + 1) *
        (((n + 1).factorial : ℝ))⁻¹ *
        (∑ T ∈ YangMills.KP.spanningTrees
            (⊤ : SimpleGraph (Fin (n + 1))),
          ∏ v : Fin (n + 1),
            ((YangMills.KP.rootedChildCount T v).factorial : ℝ))
      = (catalan n : ℝ) :=
  YangMills.KP.rootedChildCount_factorialTreeSum_normalized_eq_catalan n

/-- Marked-root finite leaf summation for the second Ursell expansion with
holes.  The moment constant is paid once at the root and the closed leaf ratio
is `4 M²` per additional vertex. -/
theorem markedRootLeafGeometricBound
    {d L : ℕ} [NeZero L]
    (HF : HoleFamily d L)
    (zK : Finset (Cube d L) → ℂ)
    (w : OmegaPolymerType HF zK → ℝ)
    (r : Cube d L)
    (n : ℕ)
    (κ₀ : ℝ)
    (hκ₀ : 0 < κ₀)
    (hw : ∀ Q : OmegaPolymerType HF zK, 0 ≤ w Q)
    (hw_exp :
      ∀ Q : OmegaPolymerType HF zK,
        w Q ≤ appendixFHoleExpWeight HF (2 * κ₀) Q.val)
    (hdisj :
      ∀ H₁ ∈ HF.holes, ∀ H₂ ∈ HF.holes,
        H₁ ≠ H₂ → Disjoint H₁ H₂)
    (hnoedges :
      noEdgesBetweenHoles (cubeAdj d L) HF.holes)
    (hholes_ne : ∀ H₀ ∈ HF.holes, H₀.Nonempty)
    (hCq :
      ((3 ^ d : ℕ) : ℝ) ^ 2 *
          (Real.exp (-κ₀) * 2 ^ (3 ^ d + 1)) < 1) :
    ((n : ℝ) + 1) *
        appendixFHoleHsharpWeightedTreeMarkedRootSum HF zK w r n
      ≤
    appendixFSecondUrsellMomentConstant d κ₀ *
      appendixFSecondUrsellLeafConstant d κ₀ ^ n :=
  appendixFHoleHsharpWeightedTreeMarkedRootSum_le_geometric_of_expWeight
    HF zK w r n κ₀ hκ₀ hw hw_exp hdisj hnoedges hholes_ne hCq

/-- Catalan-sharpened marked-root bound: the closed shape factor `4^n` of
`markedRootLeafGeometricBound` improved to `catalan n`
(`M·(4M²)^n = M^{2n+1}·4^n ⟶ M^{2n+1}·catalan n`, a gain of order
`n^{3/2}`). -/
theorem markedRootCatalanBound
    {d L : ℕ} [NeZero L]
    (HF : HoleFamily d L)
    (zK : Finset (Cube d L) → ℂ)
    (w : OmegaPolymerType HF zK → ℝ)
    (r : Cube d L)
    (n : ℕ)
    (κ₀ : ℝ)
    (hκ₀ : 0 < κ₀)
    (hw : ∀ Q : OmegaPolymerType HF zK, 0 ≤ w Q)
    (hw_exp :
      ∀ Q : OmegaPolymerType HF zK,
        w Q ≤ appendixFHoleExpWeight HF (2 * κ₀) Q.val)
    (hdisj :
      ∀ H₁ ∈ HF.holes, ∀ H₂ ∈ HF.holes,
        H₁ ≠ H₂ → Disjoint H₁ H₂)
    (hnoedges :
      noEdgesBetweenHoles (cubeAdj d L) HF.holes)
    (hholes_ne : ∀ H₀ ∈ HF.holes, H₀.Nonempty)
    (hCq :
      ((3 ^ d : ℕ) : ℝ) ^ 2 *
          (Real.exp (-κ₀) * 2 ^ (3 ^ d + 1)) < 1) :
    ((n : ℝ) + 1) *
        appendixFHoleHsharpWeightedTreeMarkedRootSum HF zK w r n
      ≤
    appendixFSecondUrsellMomentConstant d κ₀ ^ (2 * n + 1) *
      (catalan n : ℝ) :=
  appendixFHoleHsharpWeightedTreeMarkedRootSum_le_catalan_of_expWeight
    HF zK w r n κ₀ hκ₀ hw hw_exp hdisj hnoedges hholes_ne hCq

/-- Target-preserving orderwise bound.  The exact target union remains present
until the modified-metric exponential has been extracted; only then is the
marked-root leaf estimate applied. -/
theorem targetPreservingWeightedTreeBound
    {d L : ℕ} [NeZero L]
    (HF : HoleFamily d L)
    (zK : Finset (Cube d L) → ℂ)
    (w u : OmegaPolymerType HF zK → ℝ)
    (Y : Finset (Cube d L))
    (r : Cube d L)
    (n : ℕ)
    (rate κ₀ : ℝ)
    (hrate : 0 ≤ rate)
    (hw : ∀ Q : OmegaPolymerType HF zK, 0 ≤ w Q)
    (hu : ∀ Q : OmegaPolymerType HF zK, 0 ≤ u Q)
    (hsplit :
      ∀ Q : OmegaPolymerType HF zK,
        w Q ≤ appendixFHoleExpWeight HF rate Q.val * u Q)
    (hu_exp :
      ∀ Q : OmegaPolymerType HF zK,
        u Q ≤ appendixFHoleExpWeight HF (2 * κ₀) Q.val)
    (hr : r ∈ skeleton HF Y)
    (hκ₀ : 0 < κ₀)
    (hdisj :
      ∀ H₁ ∈ HF.holes, ∀ H₂ ∈ HF.holes,
        H₁ ≠ H₂ → Disjoint H₁ H₂)
    (hnoedges :
      noEdgesBetweenHoles (cubeAdj d L) HF.holes)
    (hholes_ne : ∀ H₀ ∈ HF.holes, H₀.Nonempty)
    (hCq :
      ((3 ^ d : ℕ) : ℝ) ^ 2 *
          (Real.exp (-κ₀) * 2 ^ (3 ^ d + 1)) < 1) :
    appendixFHoleHsharpWeightedTreeTerm HF zK w Y n ≤
      appendixFSecondUrsellMomentConstant d κ₀ *
        appendixFHoleExpWeight HF rate Y *
        appendixFSecondUrsellLeafConstant d κ₀ ^ n :=
  appendixFHoleHsharpWeightedTreeTerm_le_geometric_of_expWeight_leafSummation
    HF zK w u Y r n rate κ₀ hrate hw hu hsplit hu_exp hr hκ₀ hdisj
      hnoedges hholes_ne hCq

end MarkedRootedClosure
