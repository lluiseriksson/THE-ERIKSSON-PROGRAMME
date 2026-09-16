/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99BlockContour

/-!
# Typed multiscale composition of CMP99 averages

The printed operator `Q'_j` is not an endomorphism of one fixed regional
space: its `k`-th factor maps the field space at scale `k` to the distinct
space at scale `k+1`.  This file supplies the dependent composition and proves
that exact one-scale coisometry constants multiply, rather than being lost
behind an untyped product.

The result is deliberately independent of a particular choice of scale
geometry.  A later source layer must instantiate `E k` by the actual regional
cochain space, and `Q k` by the block-contained contour average evaluated in
the recursively averaged background.  No such background recursion is
inferred here.
-/

namespace YangMills.RG

noncomputable section

universe u

variable (E : ℕ → Type u)
variable [∀ k, NormedAddCommGroup (E k)]
variable [∀ k, InnerProductSpace ℝ (E k)]
variable [∀ k, CompleteSpace (E k)]

/-- Cast-free dependent composition
`Q_{n-1} ∘ ⋯ ∘ Q_0 : E 0 → E n`. -/
noncomputable def cmp99MultiscaleQprime
    (Q : ∀ k, E k →L[ℝ] E (k + 1)) :
    ∀ n, E 0 →L[ℝ] E n
  | 0 => ContinuousLinearMap.id ℝ (E 0)
  | n + 1 => (Q n).comp (cmp99MultiscaleQprime Q n)

@[simp] theorem cmp99MultiscaleQprime_zero
    (Q : ∀ k, E k →L[ℝ] E (k + 1)) :
    cmp99MultiscaleQprime E Q 0 = ContinuousLinearMap.id ℝ (E 0) :=
  rfl

theorem cmp99MultiscaleQprime_succ
    (Q : ∀ k, E k →L[ℝ] E (k + 1)) (n : ℕ) :
    cmp99MultiscaleQprime E Q (n + 1) =
      (Q n).comp (cmp99MultiscaleQprime E Q n) :=
  rfl

@[simp] theorem cmp99MultiscaleQprime_zero_apply
    (Q : ∀ k, E k →L[ℝ] E (k + 1)) (x : E 0) :
    cmp99MultiscaleQprime E Q 0 x = x :=
  rfl

theorem cmp99MultiscaleQprime_succ_apply
    (Q : ∀ k, E k →L[ℝ] E (k + 1)) (n : ℕ) (x : E 0) :
    cmp99MultiscaleQprime E Q (n + 1) x =
      Q n (cmp99MultiscaleQprime E Q n x) :=
  rfl

/-- The adjoint of the typed composition runs through the scale tower in the
reverse order. -/
theorem adjoint_cmp99MultiscaleQprime_succ
    (Q : ∀ k, E k →L[ℝ] E (k + 1)) (n : ℕ) :
    (cmp99MultiscaleQprime E Q (n + 1)).adjoint =
      (cmp99MultiscaleQprime E Q n).adjoint.comp (Q n).adjoint := by
  rw [cmp99MultiscaleQprime_succ, ContinuousLinearMap.adjoint_comp]

/-- Exact normalization of the typed multiscale average.  If every scale
satisfies `Q_k Q_k† = c_k I`, then

`Q'_n (Q'_n)† = (∏ k < n, c_k) I`.

The statement is an operator equality between the actual terminal space
`E n`, so no intermediate scale is silently identified with another. -/
theorem cmp99MultiscaleQprime_comp_adjoint
    (Q : ∀ k, E k →L[ℝ] E (k + 1)) (c : ℕ → ℝ)
    (hQ : ∀ k,
      (Q k).comp (Q k).adjoint =
        c k • ContinuousLinearMap.id ℝ (E (k + 1))) :
    ∀ n,
      (cmp99MultiscaleQprime E Q n).comp
          (cmp99MultiscaleQprime E Q n).adjoint =
        (∏ k ∈ Finset.range n, c k) •
          ContinuousLinearMap.id ℝ (E n) := by
  intro n
  induction n with
  | zero =>
      ext x
      simp [cmp99MultiscaleQprime]
  | succ n ih =>
      ext x
      rw [cmp99MultiscaleQprime_succ,
        ContinuousLinearMap.adjoint_comp]
      change Q n
          (((cmp99MultiscaleQprime E Q n).comp
            (cmp99MultiscaleQprime E Q n).adjoint) ((Q n).adjoint x)) = _
      rw [ih]
      simp only [ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.id_apply, map_smul]
      have hQx : Q n ((Q n).adjoint x) = c n • x := by
        have h := congrArg (fun T : E (n + 1) →L[ℝ] E (n + 1) => T x)
          (hQ n)
        simpa using h
      rw [hQx]
      simp only [smul_smul, Finset.prod_range_succ]

/-- Pointwise form of the exact multiscale normalization. -/
theorem cmp99MultiscaleQprime_comp_adjoint_apply
    (Q : ∀ k, E k →L[ℝ] E (k + 1)) (c : ℕ → ℝ)
    (hQ : ∀ k,
      (Q k).comp (Q k).adjoint =
        c k • ContinuousLinearMap.id ℝ (E (k + 1)))
    (n : ℕ) (eta : E n) :
    cmp99MultiscaleQprime E Q n
        ((cmp99MultiscaleQprime E Q n).adjoint eta) =
      (∏ k ∈ Finset.range n, c k) • eta := by
  have h := congrArg (fun T : E n →L[ℝ] E n => T eta)
    (cmp99MultiscaleQprime_comp_adjoint E Q c hQ n)
  simpa using h

/-- Intertwining laws at individual scales compose through the genuinely
typed tower.  This is the abstract covariance mechanism used once the
background and gauge actions at each scale have been instantiated. -/
theorem cmp99MultiscaleQprime_intertwines
    (Q : ∀ k, E k →L[ℝ] E (k + 1))
    (act : ∀ k, E k → E k)
    (hstep : ∀ k x, Q k (act k x) = act (k + 1) (Q k x)) :
    ∀ n x,
      cmp99MultiscaleQprime E Q n (act 0 x) =
        act n (cmp99MultiscaleQprime E Q n x) := by
  intro n
  induction n with
  | zero =>
      intro x
      rfl
  | succ n ih =>
      intro x
      rw [cmp99MultiscaleQprime_succ_apply, ih, hstep,
        cmp99MultiscaleQprime_succ_apply]

end

end YangMills.RG
