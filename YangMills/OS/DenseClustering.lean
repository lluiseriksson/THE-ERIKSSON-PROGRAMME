/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson

O-1b: THE SHARP FORM — clustering on a spanning family, with NO uniformity
on the constants, already forces the gap.

Charter: docs/O-BRIDGE-CHARTER.md, AMENDMENT 1 (registered before this
fabrication, and containing the retraction this module discharges).
-/

import Mathlib

/-!
# O-1b — the constants do not matter

## What this module corrects

`YangMills/OS/TransferGap.lean` (O-1) ships two theorems: clustering at *every*
vector forces the gap (Banach–Steinhaus pays for the uniformity), while
clustering on a merely *dense* set forces it when the constant is uniformly
quadratic (`K‖v‖²`, extended by continuity of the quadratic form).  An earlier
version of that module's docstring, and the audit
`docs/O-BRIDGE-AUDIT-20260727.md`, read the second hypothesis as a candidate
**obstruction**: the repository's clustering constants grow exponentially in the
support of the observable, so — the reading went — a family large enough to be
total cannot have uniform constants, and Bridge O might close as a third wall.

**That reading was wrong, and this module is the theorem that says so.**  The
uniformity is a requirement of *that proof*, not of the theorem.  Set

  `decayDomain S r := {v | ∃ C, ∀ n, ‖Sⁿ v‖ ≤ C · rⁿ}`.

It is a **submodule** (`decaySubmodule`): per-observable constants add,
`C_{u+v} ≤ C_u + C_v`, so however fast the constants grow with the support, they
close up under linear combination with no uniformity whatsoever.  And it is
effectively closed — `norm_le_of_dense_decayDomain` shows that if it is merely
*dense* then `‖S‖ ≤ r`.  Hence:

> exponential growth of the clustering constant in the observable's support is
> **not** an obstruction to the transfer-operator gap.

## The proof, and why it is not elementary

The result genuinely needs the functional calculus; this is not laziness.  The
naive routes fail for a reason worth recording:

* Banach–Steinhaus does not apply: a dense *subspace* may be meagre (the span of
  a countable family is), so its non-meagreness hypothesis is unavailable and
  pointwise bounds on such a set give no uniform bound.
* Powers do not suffice.  Put `B := S²/‖S‖²`, a positive contraction with
  `‖B‖ = 1`.  It can happen that `Bⁿ v → 0` for **every** `v` while `‖Bⁿ‖ = 1`
  for every `n` — multiplication by `x` on `L²[0,1]` is exactly that — so the
  norm level alone yields no contradiction.  (For a general self-adjoint `S` the
  powers need not tend to `0` at all: if `±‖S‖` is an eigenvalue they converge to
  the corresponding eigenprojection.  The claim being made here is only that a
  counterexample to the norm-level argument exists, not that `Bⁿ v → 0` always.)
  The statement is about the spectral measure near the top of the spectrum, and
  only a functional calculus sees that.
* The resolvent route stalls: `v ∈ decayDomain` gives `v ∈ range (t − S)` for
  every `t > r` by a Neumann series, but with a *vector-dependent* bound, and a
  self-adjoint operator with dense range need not be invertible (continuous
  spectrum at the top).

The argument used here: if `λ₀ ∈ spectrum S` with `|λ₀| = ‖S‖ > r`, pick
`r < c < |λ₀|` and `f x := max 0 (|x| − c)`, which vanishes on `{|x| ≤ c}` and
has `f λ₀ > 0`.  Factor `f x = kₙ x · x^{2n}` with

  `kₙ x := f x / (max c |x|) ^ (2n)`,

whose denominator is `≥ c^{2n} > 0` **everywhere** — so `kₙ` is continuous with
no case analysis and `‖kₙ‖_∞ ≤ ‖S‖ / c^{2n}` on the spectrum.  Then
`f(S) v = kₙ(S) (S^{2n} v)`, so for `v ∈ decayDomain S r`

  `‖f(S) v‖ ≤ (‖S‖ / c^{2n}) · C_v · r^{2n} = ‖S‖ · C_v · (r/c)^{2n} → 0`,

giving `f(S) v = 0` on a dense set, hence `f(S) = 0`, contradicting
`‖f(S)‖ ≥ |f λ₀| > 0`.

## Scope, and the ℝ/ℂ boundary (stated, not papered over)

Mathlib derives the **real** continuous functional calculus for `IsSelfAdjoint`
from the complex one (`CStarAlgebra/ContinuousFunctionalCalculus/Instances.lean`,
via `[Algebra ℂ A]`), so it is unavailable for operators on a *real* Hilbert
space.  This module therefore works over a **complex** Hilbert space, while O-1
works over a real one.  The two are separate instantiations of one argument.
**The ℝ↔ℂ bridge is NOT proved here and is NOT claimed** — asserting it without
proof would repeat exactly the unmeasured inference that Amendment 1 retracts.

Nothing here constructs an Osterwalder–Seiler Hilbert space, proves reflection
positivity, or identifies any Euclidean correlator with a matrix element.  No
claim about Yang–Mills, the continuum limit, or the Clay problem.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills.OS

set_option linter.unusedSectionVars false

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ## The decay domain -/

/-- Vectors whose `S`-orbit decays at rate `r`, with a constant **free to depend
on the vector**.  This is the shape a cluster expansion produces: one constant
per observable, with no uniformity across the family. -/
def decayDomain (S : H →L[ℂ] H) (r : ℝ) : Set H :=
  {v | ∃ C : ℝ, ∀ n : ℕ, ‖(S ^ n) v‖ ≤ C * r ^ n}

theorem mem_decayDomain_iff {S : H →L[ℂ] H} {r : ℝ} {v : H} :
    v ∈ decayDomain S r ↔ ∃ C : ℝ, ∀ n : ℕ, ‖(S ^ n) v‖ ≤ C * r ^ n := Iff.rfl

/-- **The decay domain is a submodule.**  This single fact is what kills the
"scissors": constants that grow arbitrarily fast with the observable's support
still add up, so a family with per-observable constants spans a subspace on
which the decay estimate holds. -/
def decaySubmodule (S : H →L[ℂ] H) (r : ℝ) : Submodule ℂ H where
  carrier := decayDomain S r
  zero_mem' := ⟨0, fun n => by simp⟩
  add_mem' := by
    rintro u v ⟨Cu, hu⟩ ⟨Cv, hv⟩
    refine ⟨Cu + Cv, fun n => ?_⟩
    calc ‖(S ^ n) (u + v)‖ = ‖(S ^ n) u + (S ^ n) v‖ := by rw [map_add]
      _ ≤ ‖(S ^ n) u‖ + ‖(S ^ n) v‖ := norm_add_le _ _
      _ ≤ Cu * r ^ n + Cv * r ^ n := add_le_add (hu n) (hv n)
      _ = (Cu + Cv) * r ^ n := by ring
  smul_mem' := by
    rintro a v ⟨C, hC⟩
    refine ⟨‖a‖ * C, fun n => ?_⟩
    have hmap : (S ^ n) (a • v) = a • (S ^ n) v := map_smul _ _ _
    calc ‖(S ^ n) (a • v)‖ = ‖a‖ * ‖(S ^ n) v‖ := by rw [hmap, norm_smul]
      _ ≤ ‖a‖ * (C * r ^ n) := mul_le_mul_of_nonneg_left (hC n) (norm_nonneg a)
      _ = ‖a‖ * C * r ^ n := by ring

@[simp] theorem coe_decaySubmodule (S : H →L[ℂ] H) (r : ℝ) :
    (decaySubmodule S r : Set H) = decayDomain S r := rfl

/-! ## The cut-off function and its factorisation -/

section CutOff

variable (c : ℝ)

/-- `f x = max 0 (|x| − c)`: vanishes on `{|x| ≤ c}`, strictly positive beyond. -/
noncomputable def cutOff : ℝ → ℝ := fun x => max 0 (|x| - c)

/-- The quotient `kₙ = f / (max c |x|)^{2n}`.  The denominator is `≥ c^{2n} > 0`
**everywhere**, which is the whole point: no case analysis is needed for
continuity, and no division by zero can occur even when `0 ∈ spectrum S`. -/
noncomputable def cutOffQuot (n : ℕ) : ℝ → ℝ :=
  fun x => cutOff c x / (max c |x|) ^ (2 * n)

theorem cutOff_nonneg (x : ℝ) : 0 ≤ cutOff c x := le_max_left _ _

theorem cutOff_continuous : Continuous (cutOff c) := by
  unfold cutOff
  exact continuous_const.max (continuous_abs.sub continuous_const)

theorem cutOff_eq_zero_of_le {x : ℝ} (hx : |x| ≤ c) : cutOff c x = 0 := by
  unfold cutOff
  exact max_eq_left (by linarith)

theorem max_pos {x : ℝ} (hc : 0 < c) : 0 < max c |x| := lt_of_lt_of_le hc (le_max_left _ _)

theorem cutOffQuot_continuous (n : ℕ) (hc : 0 < c) : Continuous (cutOffQuot c n) := by
  unfold cutOffQuot
  refine (cutOff_continuous c).div ((continuous_const.max continuous_abs).pow _) ?_
  intro x
  exact pow_ne_zero _ (ne_of_gt (max_pos c hc))

/-- **The factorisation.**  `kₙ(x) · x^{2n} = f(x)` for every real `x`, with no
side condition — the even power is what lets `|x|` stand in for `x`. -/
theorem cutOffQuot_mul_pow (n : ℕ) (hc : 0 < c) (x : ℝ) :
    cutOffQuot c n x * x ^ (2 * n) = cutOff c x := by
  have hxeven : x ^ (2 * n) = |x| ^ (2 * n) := by
    rw [pow_mul, pow_mul, ← sq_abs x]
  rcases le_total (|x|) c with hx | hx
  · -- inside the cut-off: both sides vanish
    rw [cutOff_eq_zero_of_le c hx]
    unfold cutOffQuot
    rw [cutOff_eq_zero_of_le c hx, zero_div, zero_mul]
  · -- outside: `max c |x| = |x|` and the powers cancel
    have hmax : max c |x| = |x| := max_eq_right hx
    have hxpos : (0 : ℝ) < |x| := lt_of_lt_of_le hc hx
    have hxne : |x| ^ (2 * n) ≠ 0 := pow_ne_zero _ (ne_of_gt hxpos)
    unfold cutOffQuot
    rw [hmax, hxeven, div_mul_cancel₀ _ hxne]

/-- On the spectrum the quotient is small: `‖kₙ‖ ≤ M / c^{2n}` whenever the
cut-off itself is bounded by `M`. -/
theorem cutOffQuot_le {n : ℕ} {M : ℝ} (hc : 0 < c) {x : ℝ} (hM : cutOff c x ≤ M) :
    |cutOffQuot c n x| ≤ M / c ^ (2 * n) := by
  have hden : c ^ (2 * n) ≤ (max c |x|) ^ (2 * n) :=
    pow_le_pow_left₀ hc.le (le_max_left _ _) _
  have hcpow : (0 : ℝ) < c ^ (2 * n) := pow_pos hc _
  have hnum : 0 ≤ cutOff c x := cutOff_nonneg c x
  have hM0 : 0 ≤ M := le_trans hnum hM
  unfold cutOffQuot
  rw [abs_div, abs_of_nonneg hnum, abs_of_nonneg (le_of_lt (pow_pos (max_pos c hc) _)),
    div_le_div_iff₀ (pow_pos (max_pos c hc) _) hcpow]
  exact mul_le_mul hM hden hcpow.le hM0

end CutOff

/-! ## The theorem -/

/-- **O-1b — the sharp form.**  If the decay domain of a self-adjoint operator is
dense, then `‖S‖ ≤ r`.  The constants are completely unconstrained: they may
depend on the vector and grow arbitrarily fast along any exhaustion of the space.

It removes the uniformly quadratic hypothesis `K‖v‖²` of
`gap_of_dense_clustering` (`TransferGap.lean`), which is a requirement of *that
proof* and not of the theorem, and it is the formal content of AMENDMENT 1's
retraction.

**Not literally a subsumption of the shipped real statement.**
`gap_of_dense_clustering` is over ℝ and this theorem is over ℂ; the ℝ↔ℂ
transport is not proved anywhere in this development (AMENDMENT 2).  So what is
removed here is that hypothesis *in the complex instantiation* — the same
removal over ℝ is not available, and claiming otherwise would be exactly the
kind of unmeasured inference AMENDMENT 1 retracts. -/
theorem norm_le_of_dense_decayDomain [Nontrivial H] {S : H →L[ℂ] H}
    (hS : IsSelfAdjoint S) {r : ℝ} (hr : 0 ≤ r)
    (hdense : Dense (decayDomain S r)) : ‖S‖ ≤ r := by
  by_contra hcon
  push_neg at hcon
  -- the norm is attained on the spectrum
  obtain ⟨l, hl_mem, hl⟩ :
      ∃ l ∈ spectrum ℝ S, ‖l‖ = ‖S‖ := by
    obtain ⟨⟨l, hl_mem, hl⟩, -⟩ :=
      IsometricContinuousFunctionalCalculus.isGreatest_norm_spectrum (𝕜 := ℝ) S hS
    exact ⟨l, hl_mem, hl⟩
  rw [Real.norm_eq_abs] at hl
  -- pick a threshold strictly between r and |l|.  `c` is obtained OPAQUELY (not
  -- by `set`), so downstream `ring` calls cannot unfold it into `(r + |l|)/2`.
  have hrl : r < |l| := by rw [hl]; exact hcon
  obtain ⟨c, hcr, hcl⟩ : ∃ c : ℝ, r < c ∧ c < |l| :=
    ⟨(r + |l|) / 2, by linarith, by linarith⟩
  have hc0 : 0 < c := lt_of_le_of_lt hr hcr
  -- the cut-off is bounded by ‖S‖ on the spectrum
  have hbound : ∀ x ∈ spectrum ℝ S, cutOff c x ≤ ‖S‖ := by
    intro x hx
    have hxle : |x| ≤ ‖S‖ := by
      have := IsometricContinuousFunctionalCalculus.norm_spectrum_le (𝕜 := ℝ) S hx hS
      rwa [Real.norm_eq_abs] at this
    unfold cutOff
    exact max_le (norm_nonneg S) (by linarith)
  -- the cut-off applied to S is nonzero, because f l > 0
  have hfl : 0 < cutOff c l := by
    unfold cutOff
    exact lt_max_of_lt_right (by linarith)
  have hne : cfc (cutOff c) S ≠ 0 := by
    intro h0
    have hle : |cutOff c l| ≤ ‖cfc (cutOff c) S‖ := by
      have := norm_apply_le_norm_cfc (𝕜 := ℝ) (cutOff c) S hl_mem
        ((cutOff_continuous c).continuousOn) hS
      rwa [Real.norm_eq_abs] at this
    rw [h0, norm_zero, abs_of_pos hfl] at hle
    linarith
  -- but it annihilates the decay domain, which is dense, so it is zero
  refine hne ?_
  have hkey : ∀ v ∈ decayDomain S r, cfc (cutOff c) S v = 0 := by
    rintro v ⟨C, hC⟩
    -- factor f = kₙ · x^{2n}, so f(S) v = kₙ(S) (S^{2n} v)
    have hfac : ∀ n : ℕ, cfc (cutOff c) S
        = cfc (cutOffQuot c n) S * (S ^ (2 * n)) := by
      intro n
      have hrw : cutOff c = fun x : ℝ => cutOffQuot c n x * x ^ (2 * n) := by
        funext x; exact (cutOffQuot_mul_pow c n hc0 x).symm
      rw [hrw, cfc_mul _ _ S ((cutOffQuot_continuous c n hc0).continuousOn)
        ((continuous_pow (2 * n)).continuousOn)]
      congr 1
      have : cfc (fun x : ℝ => x ^ (2 * n)) S = (cfc (id : ℝ → ℝ) S) ^ (2 * n) :=
        cfc_pow (R := ℝ) id (2 * n) S (continuous_id.continuousOn) hS
      rw [this, cfc_id ℝ S hS]
    -- and kₙ(S) has norm at most ‖S‖ / c^{2n}
    have hknorm : ∀ n : ℕ, ‖cfc (cutOffQuot c n) S‖ ≤ ‖S‖ / c ^ (2 * n) := by
      intro n
      refine norm_cfc_le (𝕜 := ℝ) (by positivity) ?_
      intro x hx
      rw [Real.norm_eq_abs]
      exact cutOffQuot_le c hc0 (hbound x hx)
    -- so ‖f(S) v‖ <= ‖S‖ * C * (r/c)^{2n} -> 0
    have hsmall : ∀ n : ℕ,
        ‖cfc (cutOff c) S v‖ ≤ (‖S‖ * C) * (r / c) ^ (2 * n) := by
      intro n
      have hcpow : (0 : ℝ) < c ^ (2 * n) := pow_pos hc0 _
      calc ‖cfc (cutOff c) S v‖
          = ‖(cfc (cutOffQuot c n) S) ((S ^ (2 * n)) v)‖ := by rw [hfac n]; rfl
        _ ≤ ‖cfc (cutOffQuot c n) S‖ * ‖(S ^ (2 * n)) v‖ :=
            (cfc (cutOffQuot c n) S).le_opNorm _
        _ ≤ (‖S‖ / c ^ (2 * n)) * (C * r ^ (2 * n)) := by
            refine mul_le_mul (hknorm n) (hC (2 * n)) (norm_nonneg _) ?_
            positivity
        _ = (‖S‖ * C) * (r / c) ^ (2 * n) := by
            rw [div_pow]; ring
    -- conclude by letting n -> infinity
    by_contra hv
    have hvpos : 0 < ‖cfc (cutOff c) S v‖ := norm_pos_iff.mpr hv
    have hrc : (0 : ℝ) ≤ r / c := div_nonneg hr hc0.le
    have hrc1 : r / c < 1 := (div_lt_one hc0).mpr hcr
    have htend : Filter.Tendsto (fun n : ℕ => (‖S‖ * C) * (r / c) ^ (2 * n))
        Filter.atTop (nhds 0) := by
      have h1 : Filter.Tendsto (fun n : ℕ => ((r / c) ^ 2) ^ n)
          Filter.atTop (nhds 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (by nlinarith)
      have h2 : (fun n : ℕ => (‖S‖ * C) * (r / c) ^ (2 * n))
          = fun n : ℕ => (‖S‖ * C) * ((r / c) ^ 2) ^ n := by
        funext n; rw [← pow_mul, mul_comm 2 n]
      rw [h2]
      simpa using h1.const_mul (‖S‖ * C)
    obtain ⟨n, hn⟩ := (htend.eventually (gt_mem_nhds hvpos)).exists
    exact absurd (hsmall n) (by linarith)
  -- density: the kernel condition is closed
  have hclosed : IsClosed {v : H | cfc (cutOff c) S v = 0} :=
    isClosed_eq (cfc (cutOff c) S).continuous continuous_const
  have huniv : ∀ v : H, cfc (cutOff c) S v = 0 := by
    intro v
    have := hclosed.closure_subset_iff.mpr hkey
    rw [hdense.closure_eq] at this
    exact this (Set.mem_univ v)
  exact ContinuousLinearMap.ext huniv

/-- **The spanning-family form** — the shape an actual cluster expansion feeds.
A family `D` of observables whose span is dense, each with its OWN finite
constant, forces the gap.  No relation between the constants is assumed, so
`C = e^{c · support}` is perfectly admissible. -/
theorem norm_le_of_span_dense_decay [Nontrivial H] {S : H →L[ℂ] H}
    (hS : IsSelfAdjoint S) {r : ℝ} (hr : 0 ≤ r) (D : Set H)
    (hspan : Dense ((Submodule.span ℂ D : Submodule ℂ H) : Set H))
    (hD : ∀ v ∈ D, ∃ C : ℝ, ∀ n : ℕ, ‖(S ^ n) v‖ ≤ C * r ^ n) :
    ‖S‖ ≤ r := by
  refine norm_le_of_dense_decayDomain hS hr (hspan.mono ?_)
  have hsub : Submodule.span ℂ D ≤ decaySubmodule S r := by
    rw [Submodule.span_le]
    exact fun v hv => hD v hv
  exact fun v hv => hsub hv

end YangMills.OS
