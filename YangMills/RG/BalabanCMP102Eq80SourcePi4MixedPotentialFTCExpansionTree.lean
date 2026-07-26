/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80SourcePi4RealMixedPotentialDerivative
import YangMills.RG.BalabanCMP116FTCInterpolation

/-!
# The literal equation-(80) mixed FTC tree

This module builds the finite iterated FTC tree for the complete physical
CMP102 equation-(80) potential.  Each node varies one source `Pi^4` weakening
coordinate, and every higher branch is formed by differentiating the complete
functional obtained at the preceding node.

This distinction is essential: after the first differentiation, the next
branch is not obtained merely by replacing the propagator with a higher mixed
covariance.  The quadratic equation-(80) terms and the derivative of `V₀`
must themselves be differentiated.  The generic tree below records those
literal iterated derivatives.  A terminal theorem identifies its first
coordinate derivative with the physical mixed-covariance chain rule.
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

/-- Derivative of a weakening functional in one selected coordinate, at the
specified coordinate value and with all other coordinates supplied by `s`. -/
noncomputable def cmp116RealWeakeningCoordinateDerivative
    {D : Type*} [DecidableEq D]
    (f : (D → ℝ) → ℝ) (d : D) (t : ℝ) (s : D → ℝ) : ℝ :=
  deriv (fun u => f (Function.update s d u)) t

/-- Under differentiability of the full weakening functional, the coordinate
derivative is its Fréchet derivative applied to the canonical coordinate
vector. -/
theorem cmp116RealWeakeningCoordinateDerivative_eq_fderiv
    {D : Type*} [Fintype D] [DecidableEq D]
    (f : (D → ℝ) → ℝ) (d : D) (t : ℝ) (s : D → ℝ)
    (hf : DifferentiableAt ℝ f (Function.update s d t)) :
    cmp116RealWeakeningCoordinateDerivative f d t s =
      fderiv ℝ f (Function.update s d t) (Pi.single d 1) := by
  unfold cmp116RealWeakeningCoordinateDerivative
  simpa [Function.comp_def] using
    ((hf.hasFDerivAt.comp t
      (hasDerivAt_update s d t).hasFDerivAt).hasDerivAt.deriv)

/-- Overwriting one coordinate by a constant is a smooth map on the finite
weakening space. -/
theorem contDiff_update_const
    {D : Type*} [Fintype D] [DecidableEq D]
    (n : WithTop ℕ∞) (d : D) (t : ℝ) :
    ContDiff ℝ n (fun s : D → ℝ => Function.update s d t) := by
  apply contDiff_pi'
  intro i
  by_cases hid : i = d
  · subst i
    simpa using (contDiff_const : ContDiff ℝ n (fun _ : D → ℝ => t))
  · simpa [Function.update_of_ne hid] using
      (contDiff_apply (n := n) ℝ ℝ i :
        ContDiff ℝ n (fun s : D → ℝ => s i))

/-- One coordinate derivative lowers the available differentiability order by
exactly one. -/
theorem contDiff_cmp116RealWeakeningCoordinateDerivative
    {D : Type*} [Fintype D] [DecidableEq D]
    {n : ℕ}
    (f : (D → ℝ) → ℝ) (d : D) (t : ℝ)
    (hf : ContDiff ℝ (n + 1) f) :
    ContDiff ℝ n (cmp116RealWeakeningCoordinateDerivative f d t) := by
  have hupdate :
      ContDiff ℝ n (fun s : D → ℝ => Function.update s d t) :=
    contDiff_update_const n d t
  have hfd :
      ContDiff ℝ n
        (fun s : D → ℝ =>
          fderiv ℝ f (Function.update s d t) (Pi.single d 1)) :=
    ((hf.fderiv_right (m := (n : WithTop ℕ∞)) (by norm_num)).comp hupdate).clm_apply
      contDiff_const
  rw [show
    cmp116RealWeakeningCoordinateDerivative f d t =
      fun s => fderiv ℝ f (Function.update s d t) (Pi.single d 1) by
    funext s
    exact cmp116RealWeakeningCoordinateDerivative_eq_fderiv
      f d t s (hf.differentiable (by norm_num) (Function.update s d t))]
  exact hfd

/-- A source-faithful finite FTC tree for an arbitrary real weakening
functional.  Recursive fibers differentiate the complete current functional,
not a selected factor inside it. -/
noncomputable def cmp116RealWeakeningFTCExpansionTree
    {D : Type*} [DecidableEq D]
    (f : (D → ℝ) → ℝ) (s : D → ℝ) :
    (L : List D) → CMP116FTCExpansionTree ℝ L.length
  | [] => .leaf (f s)
  | d :: tail =>
      let endpointS := cmp116SetRealWeakeningList s tail 1
      .node
        (fun t => f (Function.update endpointS d t))
        (fun t => cmp116RealWeakeningCoordinateDerivative f d t endpointS)
        (cmp116RealWeakeningFTCExpansionTree f
          (Function.update s d 0) tail)
        (fun t =>
          cmp116RealWeakeningFTCExpansionTree
            (cmp116RealWeakeningCoordinateDerivative f d t)
            (Function.update s d t) tail)

/-- The coupled endpoint of the literal real weakening tree evaluates the
original functional with all listed coordinates set to one. -/
theorem cmp116RealWeakeningFTCExpansionTree_coupledEndpoint
    {D : Type*} [DecidableEq D]
    (f : (D → ℝ) → ℝ) (s : D → ℝ)
    (L : List D) (hL : L.Nodup) :
    (cmp116RealWeakeningFTCExpansionTree f s L).coupledEndpoint =
      f (cmp116SetRealWeakeningList s L 1) := by
  cases L with
  | nil =>
      simp [cmp116RealWeakeningFTCExpansionTree,
        CMP116FTCExpansionTree.coupledEndpoint]
  | cons d tail =>
      have hdTail : d ∉ tail := (List.nodup_cons.mp hL).1
      change
        f (Function.update
            (cmp116SetRealWeakeningList s tail 1) d 1) =
          f (cmp116SetRealWeakeningList s (d :: tail) 1)
      rw [cmp116SetRealWeakeningList_cons_of_not_mem s d tail 1 hdTail]

/-- The physical source `Pi^4` FTC tree for the literal equation-(80)
potential.  It starts from the empty covariance mixed-derivative carrier and
then differentiates the whole weakening functional recursively. -/
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
    (L : List (FinBox 4 (2 * Q)))
    (A : PhysicalField M Q Nc) :
    CMP116FTCExpansionTree ℝ L.length :=
  cmp116RealWeakeningFTCExpansionTree
    (fun sigma =>
      cmp102Eq80SourcePi4RealMixedPotential
        (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J sigma ∅ A)
    s L

/-- The source-specific coupled endpoint is the literal equation-(80)
potential with all listed source weakening coordinates set to one. -/
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
    (L : List (FinBox 4 (2 * Q))) (hL : L.Nodup)
    (A : PhysicalField M Q Nc) :
    (cmp102Eq80SourcePi4MixedPotentialFTCExpansionTree
      (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J s L A).coupledEndpoint =
      cmp102Eq80SourcePi4RealMixedPotential
        (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J
        (cmp116SetRealWeakeningList s L 1) ∅ A := by
  exact cmp116RealWeakeningFTCExpansionTree_coupledEndpoint _ s L hL

set_option maxHeartbeats 1200000 in
/-- The first coordinate derivative of the complete physical potential is
the literal mixed-covariance directional derivative already constructed from
the contour theorem. -/
theorem
    CMP116SourcePi4RealMixedDerivativeCertificate.realWeakeningDerivative_eq
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
    (d : FinBox 4 (2 * Q))
    (A : PhysicalField M Q Nc)
    (t : ℝ)
    (Cert : CMP116SourcePi4RealMixedDerivativeCertificate
      (R := R) anchor K hc hmass hK s ∅ d t)
    (V₀' : PhysicalField M Q Nc →L[ℝ] ℝ)
    (hV₀ : HasFDerivAt V₀ V₀'
      (A -
        cmp116SourcePi4RealMixedCovarianceOperatorCurve
          (R := R) anchor K hc hmass hK s ∅ d t (D A))) :
    cmp116RealWeakeningCoordinateDerivative
        (fun sigma =>
          cmp102Eq80SourcePi4RealMixedPotential
            (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J sigma ∅ A)
        d t s =
      cmp102Eq80SourcePi4RealMixedPotentialCurveDerivative
        (R := R) anchor K hc hmass hK D D₃ Δπ J s ∅ d A t V₀' := by
  unfold cmp116RealWeakeningCoordinateDerivative
  rw [show
    (fun u =>
      cmp102Eq80SourcePi4RealMixedPotential
        (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J
        (Function.update s d u) ∅ A) =
      cmp102Eq80SourcePi4RealMixedPotentialCurve
        (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J s ∅ d A by
    funext u
    exact
      (cmp102Eq80SourcePi4RealMixedPotentialCurve_eq
        (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J s ∅ d A u).symm]
  exact
    (CMP116SourcePi4RealMixedDerivativeCertificate.hasDerivAt_eq80Potential
      anchor K hc hmass hK D D₃ V₀ Δπ J s ∅ d A t Cert V₀' hV₀).deriv

end

end YangMills.RG
