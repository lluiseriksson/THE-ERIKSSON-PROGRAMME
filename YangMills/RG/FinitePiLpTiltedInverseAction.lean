/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.FinitePiLpCombesThomas

/-!
# Tilted inverse action before point-source expansion

PRE-VALIDATION: source present, `.olean` not yet materialized, and the result
has not yet been verified by the Lean compiler.

The usual Combes--Thomas endpoint expands an inverse against a coordinate
probe.  CMP96 (2.43) instead applies the regional Green to an arbitrary field
supported in one source owner.  Expanding that field into probes would pay the
fine-fibre cardinality and lose the printed `ell^2` normalization.

This leaf lemma stops one step earlier.  Coercivity of one rooted tilted
precision controls the action of its right inverse on an arbitrary input by
the counting-L2 norm of the tilted input.  No support set, owner cardinality,
physical Green, `B0`, `delta0`, or terminal estimate is an input or a
conclusion here.
-/

namespace YangMills.RG

open scoped RealInnerProductSpace

noncomputable section

/-- A rooted tilted coercivity estimate bounds the action of a right inverse
on an arbitrary input before any expansion into coordinate probes.

The retained `‖tilt f‖` is deliberate: a later source-owner lemma bounds it
once by the sealed `ell^2 * supNorm f` conversion plus the owner-diameter
factor. -/
theorem norm_finitePiLpInverse_apply_le_of_tilted_coercive
    {ι g : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup g] [InnerProductSpace ℝ g]
    [FiniteDimensional ℝ g]
    (dist : ι → ι → ℕ) {rate c : ℝ} (hc : 0 < c)
    (K C : FinitePiLpField ι g →L[ℝ] FinitePiLpField ι g)
    (hKC : K.comp C = ContinuousLinearMap.id ℝ (FinitePiLpField ι g))
    (root : ι)
    (htilt : IsCoerciveCLM
      (finitePiLpTiltConjCLM dist rate root K) (c / 2))
    (f : FinitePiLpField ι g) (target : ι) :
    ‖C f target‖ ≤
      (2 / c) * Real.exp (-(rate * (dist root target : ℝ))) *
        ‖finitePiLpTiltCLM (g := g) dist rate root f‖ := by
  let y : FinitePiLpField ι g :=
    finitePiLpTiltCLM (g := g) dist rate root (C f)
  have huntilt :
      finitePiLpTiltCLM (g := g) dist (-rate) root y = C f := by
    change finitePiLpTiltCLM (g := g) dist (-rate) root
      (finitePiLpTiltCLM (g := g) dist rate root (C f)) = C f
    exact ContinuousLinearMap.ext_iff.mp
      (finitePiLpTiltCLM_neg_comp (g := g) dist rate root) (C f)
  have hKCf : K (C f) = f := by
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]
      using congrArg (fun T => T f) hKC
  have htiltY :
      finitePiLpTiltConjCLM dist rate root K y =
        finitePiLpTiltCLM (g := g) dist rate root f := by
    unfold finitePiLpTiltConjCLM
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      huntilt, hKCf]
  have hynorm :
      ‖y‖ ≤ (2 / c) *
        ‖finitePiLpTiltCLM (g := g) dist rate root f‖ := by
    have hcoerY := htilt y
    rw [htiltY] at hcoerY
    have hinner :
        inner ℝ y (finitePiLpTiltCLM (g := g) dist rate root f) ≤
          ‖y‖ * ‖finitePiLpTiltCLM (g := g) dist rate root f‖ :=
      real_inner_le_norm y
        (finitePiLpTiltCLM (g := g) dist rate root f)
    by_cases hy : ‖y‖ = 0
    · rw [hy]
      positivity
    · have hypos : 0 < ‖y‖ :=
        lt_of_le_of_ne (norm_nonneg y) (Ne.symm hy)
      have hchain :
          c / 2 * ‖y‖ ^ 2 ≤
            ‖y‖ * ‖finitePiLpTiltCLM (g := g) dist rate root f‖ := by
        exact hcoerY.trans hinner
      have hcY :
          c * ‖y‖ ≤
            2 * ‖finitePiLpTiltCLM (g := g) dist rate root f‖ := by
        nlinarith [hchain, hypos]
      rw [div_mul_eq_mul_div, le_div_iff₀ hc]
      linarith
  have hentry :
      C f target =
        Real.exp (-rate * (dist root target : ℝ)) • y target := by
    rw [← huntilt]
    exact finitePiLpTiltCLM_apply dist (-rate) root target y
  calc
    ‖C f target‖ =
        Real.exp (-rate * (dist root target : ℝ)) * ‖y target‖ := by
      rw [hentry, norm_smul, Real.norm_eq_abs, Real.abs_exp]
    _ ≤ Real.exp (-rate * (dist root target : ℝ)) * ‖y‖ := by
      exact mul_le_mul_of_nonneg_left (PiLp.norm_apply_le _ target)
        (Real.exp_pos _).le
    _ ≤ Real.exp (-rate * (dist root target : ℝ)) *
        ((2 / c) * ‖finitePiLpTiltCLM (g := g) dist rate root f‖) := by
      exact mul_le_mul_of_nonneg_left hynorm (Real.exp_pos _).le
    _ = (2 / c) * Real.exp (-(rate * (dist root target : ℝ))) *
        ‖finitePiLpTiltCLM (g := g) dist rate root f‖ := by
      ring

end

end YangMills.RG
