import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# CMP116 equations (1.9)--(1.10): finite iterated FTC infrastructure

Balaban's localization of the pre-localized potential does not use an endpoint
Möbius identity.  It inserts finitely many weakening parameters `s(Δ)` and
applies the fundamental theorem of calculus repeatedly.  The resulting terms
retain integrals of mixed derivatives; those derivatives are what later carry
small factors and localization bounds.

This file formalizes that analytic mechanism as a finite-depth expansion tree.
At every node:

* `curve` is the current one-coordinate interpolation;
* `derivative` is its genuine derivative;
* `base` is the fully decoupled contribution in that coordinate;
* `fiber t` recursively expands the derivative at interpolation value `t`.

`CMP116FTCExpansionTree.Valid` requires the derivative identity and interval
integrability at every node.  The terminal theorem proves that the recursively
nested sum/integral is exactly the coupled endpoint.

Honest scope: this is generic analytic infrastructure.  It does **not** build
the physical `s`-dependent propagators, the plaquette partition of unity, the
connected-domain map, or the localized CMP116 functions `V_k(Y, ·)`.  It also
does not assert any decay or identify the fully decoupled term with a physical
residual.  Those are the source-specific producers that must instantiate this
tree before equations (1.36), (1.42), and (1.43) can be claimed.
-/

open Set MeasureTheory intervalIntegral

namespace YangMills.RG

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- A finite iterated fundamental-theorem-of-calculus expansion.

The depth records the number of weakening coordinates still expanded.  The
tree stores functions and recursive branches, but no validity claims; these are
kept in `Valid` so the data can be constructed before its analytic obligations
are discharged. -/
inductive CMP116FTCExpansionTree (E : Type u) : ℕ → Type u
  | leaf (value : E) : CMP116FTCExpansionTree E 0
  | node {n : ℕ} (curve derivative : ℝ → E)
      (base : CMP116FTCExpansionTree E n)
      (fiber : ℝ → CMP116FTCExpansionTree E n) :
      CMP116FTCExpansionTree E (n + 1)

/-- The recursively nested sum/integral represented by an FTC tree. -/
noncomputable def CMP116FTCExpansionTree.expansionSum :
    {n : ℕ} → CMP116FTCExpansionTree E n → E
  | 0, .leaf value => value
  | _ + 1, .node _ _ base fiber =>
      base.expansionSum + ∫ t in (0 : ℝ)..1, (fiber t).expansionSum

/-- The fully coupled endpoint represented by an FTC tree. -/
def CMP116FTCExpansionTree.coupledEndpoint :
    {n : ℕ} → CMP116FTCExpansionTree E n → E
  | 0, .leaf value => value
  | _ + 1, .node curve _ _ _ => curve 1

/-- Source-faithful validity of every FTC step in an expansion tree.

In particular, the recursive branch at `t` must sum to the actual derivative
of the parent curve at `t`; arbitrary coefficients cannot be inserted into a
valid tree. -/
def CMP116FTCExpansionTree.Valid :
    {n : ℕ} → CMP116FTCExpansionTree E n → Prop
  | 0, .leaf _ => True
  | _ + 1, .node curve derivative base fiber =>
      base.Valid ∧
      base.expansionSum = curve 0 ∧
      (∀ t ∈ Set.uIcc (0 : ℝ) 1,
        (fiber t).Valid ∧ (fiber t).expansionSum = derivative t) ∧
      (∀ t ∈ Set.uIcc (0 : ℝ) 1,
        HasDerivAt curve (derivative t) t) ∧
      IntervalIntegrable derivative volume 0 1

/-- One literal FTC step on the unit interval. -/
theorem cmp116FTC_oneStep
    (curve derivative : ℝ → E)
    (hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt curve (derivative t) t)
    (hint : IntervalIntegrable derivative volume 0 1) :
    curve 0 + ∫ t in (0 : ℝ)..1, derivative t = curve 1 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  abel

/-- Finite iterated FTC: a valid expansion tree sums exactly to its coupled
endpoint.  No endpoint finite-difference or Möbius replacement is used. -/
theorem CMP116FTCExpansionTree.expansionSum_eq_coupledEndpoint
    {n : ℕ} (T : CMP116FTCExpansionTree E n) (hT : T.Valid) :
    T.expansionSum = T.coupledEndpoint := by
  induction T with
  | leaf value => rfl
  | @node n curve derivative base fiber ihBase ihFiber =>
      rcases hT with ⟨hbaseValid, hbase, hfiber, hderiv, hint⟩
      have hIntegral :
          (∫ t in (0 : ℝ)..1, (fiber t).expansionSum) =
            ∫ t in (0 : ℝ)..1, derivative t := by
        apply intervalIntegral.integral_congr
        intro t ht
        exact (hfiber t ht).2
      have hFTC :
          (∫ t in (0 : ℝ)..1, derivative t) = curve 1 - curve 0 :=
        intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
      simp only [CMP116FTCExpansionTree.expansionSum,
        CMP116FTCExpansionTree.coupledEndpoint]
      rw [hbase, hIntegral, hFTC]
      abel

/-- A nonzero certified FTC tree, ruling out a vacuous zero-only interface. -/
theorem cmp116FTCExpansionTree_nontrivial_witness :
    ∃ T : CMP116FTCExpansionTree ℝ 1, T.Valid ∧ T.expansionSum = 1 := by
  let base : CMP116FTCExpansionTree ℝ 0 := .leaf 0
  let fiber : ℝ → CMP116FTCExpansionTree ℝ 0 := fun _ => .leaf 1
  let T : CMP116FTCExpansionTree ℝ 1 := .node id (fun _ => 1) base fiber
  have hvalid : T.Valid := by
    dsimp [T, base, fiber, CMP116FTCExpansionTree.Valid,
      CMP116FTCExpansionTree.expansionSum]
    refine ⟨trivial, ?_, ?_, ?_, ?_⟩
    · norm_num [CMP116FTCExpansionTree.expansionSum]
    · intro t ht
      exact ⟨trivial, by simp [CMP116FTCExpansionTree.expansionSum]⟩
    · intro t ht
      exact hasDerivAt_id t
    · exact continuous_const.intervalIntegrable 0 1
  exact ⟨T, hvalid, by
    simpa [T, CMP116FTCExpansionTree.coupledEndpoint] using
      T.expansionSum_eq_coupledEndpoint hvalid⟩

end YangMills.RG
