/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson

O-1: THE OPERATOR BRIDGE — Euclidean clustering <-> a spectral gap of the
transfer operator.

Charter: docs/O-BRIDGE-CHARTER.md (registered BEFORE this fabrication).
-/

import Mathlib

/-!
# O-1 — Clustering and the transfer-operator gap

## What this module is for

Every "mass gap" statement in this repository is, as of the O-bridge audit
(`docs/O-BRIDGE-AUDIT-20260727.md`), a statement about the decay of a
**real-valued function** `cov : ℕ → ℝ` (see `YangMills/Paper/ClusteringToGap.lean`).
The Osterwalder–Seiler mass gap is a statement about the **spectrum of an
operator**.  Nothing in the tree connects the two: there is no Hilbert space of
states, no transfer operator, no reflection positivity and no spectrum anywhere
under `YangMills/`.

This module supplies the *autonomous* half of the missing link, at the level of
generality where it is a theorem and not a hope: for a symmetric transfer
operator with a fixed unit vacuum vector, exponential decay of the **connected**
two-point function is **equivalent** to a norm bound on the vacuum-projected
operator — i.e. to a spectral gap — and the bound is uniform in whatever
parameter (volume, in the intended application) the data are indexed by,
because it is an operator-norm bound whose constant never sees that parameter.

## What this module does NOT do

It does not construct the Osterwalder–Seiler Hilbert space of any lattice gauge
theory, it does not prove reflection positivity of the Wilson measure, and it
does not identify any Euclidean correlator with a matrix element of any
transfer operator.  Those are O-2 and O-3 of the charter, and they are open.
Consequently **nothing here is a claim about Yang–Mills**, about the continuum
limit, or about the Clay problem; the repository's ~0% Clay distance is
unchanged.

## The two theorems and why there are two

* `gap_of_clustering` — clustering **at every vector**, with a constant allowed
  to depend on the vector, already forces the gap.  The uniformity is bought by
  Banach–Steinhaus, i.e. for free, from completeness.

* `gap_of_dense_clustering` — clustering on a merely **dense set** of vectors
  forces the gap only when the constant is uniform over that set (of the form
  `K‖v‖²`).  Continuity does the extension; no completeness argument is
  available because a dense subspace may be meagre (the span of a countable family is), so Banach-Steinhaus's non-meagreness hypothesis is unavailable.

The pair delimits what these two PROOFS need.  It does **not** delimit the
theorem.

**CORRECTION (Amendment 1, `docs/O-BRIDGE-CHARTER.md`), stated here because an
earlier version of this docstring got it wrong.**  The uniformity of the
constant in `gap_of_dense_clustering` is a requirement of *its proof*
(continuity of the quadratic form), not a necessary condition.  It is removable:
`W := {v | ∃ C, ∀ n, ‖Sⁿ v‖ ≤ C · rⁿ}` is a linear subspace — so
per-observable constants close up under linear combination with no uniformity
whatsoever — and `W` is closed, being `ran E([-r,r])`; dense + closed forces
`‖S‖ ≤ r` however fast the constants grow.  Consequently the earlier reading of
the repository's `C·e^{#supp·4d·K}` constants as a candidate obstruction (a
"scissors") is **withdrawn**.  See `YangMills/OS/DenseClustering.lean` for the
theorem that supersedes this pair, and Amendment 1 for the diagnosis.

## Non-vacuity

`exists_vacuumTransfer_gap` and `euclidean_two_dim_vacuumTransfer_gap` exhibit
inhabitants with a **strictly positive gap and a nonzero fluctuation sector**
(`projectedTransfer T Ω ≠ 0`), so no statement below is satisfied only by the
degenerate one-dimensional instance.

## Positivity is deliberately NOT assumed

The physical Osterwalder–Seiler transfer operator satisfies `0 ≤ T ≤ 1`, and
one writes `T = e^{-H}` with `H ≥ 0`.  Nothing below uses positivity: the
quadratic identity `⟪v, S^{2n} v⟫ = ‖Sⁿ v‖²` holds for any symmetric `S`.  This
is a *strengthening* (fewer hypotheses), not a weakening, but the reading
changes and must be stated:

* with `0 ≤ T`, the conclusion `‖T − |Ω⟩⟨Ω|‖ ≤ e^{-m}` is exactly the usual
  spectral statement `spec(H) \ {0} ⊆ [m, ∞)`;
* without it, the same bound additionally confines the negative part of the
  spectrum to `[-e^{-m}, 0]`, which is strictly more than the physical
  statement needs.

Either way this is the **transfer-operator gap at fixed lattice spacing**, not
a continuum statement and not the Clay mass gap.

## Provenance (obligation, per the house rule that bought the CT brick's
## citation of Combes–Thomas)

The equivalence "exponential clustering ⟺ a gap of the transfer operator" is
**classical**, not new: it is the standard argument of constructive field
theory (Glimm–Jaffe, *Quantum Physics: A Functional Integral Point of View*,
2nd ed., §19; Simon, *The P(φ)₂ Euclidean (Quantum) Field Theory*; Osterwalder–
Seiler, *Gauge field theories on a lattice*, Ann. Phys. 110 (1978) 440, for the
lattice-gauge transfer operator and its positivity).  What is not classical,
and is the reason this module exists, is (i) that it is machine-checked, and
(ii) `gap_of_dense_clustering` together with `gap_of_clustering` as a **pair**,
which is what isolates the uniformity of the constant as the load-bearing
hypothesis.  No novelty is claimed for the equivalence itself.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills.OS

set_option linter.unusedSectionVars false

open scoped RealInnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-! ## The vacuum projection and the projected transfer operator -/

/-- The rank-one orthogonal projection onto the vacuum line `ℝ ∙ Ω`
(an orthogonal projection exactly when `‖Ω‖ = 1`). -/
noncomputable def vacuumProjection (Ω : H) : H →L[ℝ] H :=
  (innerSL ℝ Ω).smulRight Ω

@[simp] theorem vacuumProjection_apply (Ω v : H) :
    vacuumProjection Ω v = (⟪Ω, v⟫ : ℝ) • Ω := rfl

/-- The **vacuum-projected transfer operator** `T - |Ω⟩⟨Ω|`.

This is a bare definition and carries no hypotheses.  *Under* `VacuumTransfer T Ω`
its norm is the norm of `T` restricted to the orthogonal complement of the
vacuum, and *if in addition* `0 ≤ T`, the bound
`‖projectedTransfer T Ω‖ ≤ e^{-m}` is the statement `spec(H) \ {0} ⊆ [m, ∞)` for
`T = e^{-H}` — i.e. "mass gap `m`" at fixed lattice spacing.  Neither reading is
available from this definition alone; see the section on positivity below. -/
noncomputable def projectedTransfer (T : H →L[ℝ] H) (Ω : H) : H →L[ℝ] H :=
  T - vacuumProjection Ω

@[simp] theorem projectedTransfer_apply (T : H →L[ℝ] H) (Ω v : H) :
    projectedTransfer T Ω v = T v - (⟪Ω, v⟫ : ℝ) • Ω := rfl

/-- The **connected (truncated) two-point function** at Euclidean time `n`:
`⟨v, Tⁿ v⟩ − ⟨v⟩²`.  This is the object a cluster expansion bounds. -/
noncomputable def connCorr (T : H →L[ℝ] H) (Ω : H) (v : H) (n : ℕ) : ℝ :=
  ⟪v, (T ^ n) v⟫ - (⟪Ω, v⟫ : ℝ) ^ 2

/-- The data of a transfer operator with a vacuum: symmetric, with a fixed unit
vector.  These are exactly the properties Osterwalder–Seiler reflection
positivity is used to produce; here they are hypotheses, not axioms. -/
structure VacuumTransfer (T : H →L[ℝ] H) (Ω : H) : Prop where
  /-- Symmetry (self-adjointness in elementary form). -/
  symm : ∀ v w, ⟪T v, w⟫ = ⟪v, T w⟫
  /-- The vacuum is a unit vector. -/
  unit : ‖Ω‖ = 1
  /-- The vacuum is fixed: `T Ω = Ω`, i.e. the vacuum has energy `0`. -/
  fix : T Ω = Ω

namespace VacuumTransfer

variable {T : H →L[ℝ] H} {Ω : H}

theorem inner_vacuum_self (hT : VacuumTransfer T Ω) : (⟪Ω, Ω⟫ : ℝ) = 1 := by
  rw [real_inner_self_eq_norm_sq, hT.unit]; norm_num

/-- Every power of a symmetric operator is symmetric. -/
theorem pow_symm (hT : VacuumTransfer T Ω) (n : ℕ) :
    ∀ v w, ⟪(T ^ n) v, w⟫ = ⟪v, (T ^ n) w⟫ := by
  induction n with
  | zero => intro v w; simp
  | succ m ih =>
      intro v w
      have hleft : (T ^ (m + 1)) v = (T ^ m) (T v) := by
        rw [pow_succ]
        rfl
      have hright : (T ^ (m + 1)) w = T ((T ^ m) w) := by
        rw [pow_succ']
        rfl
      rw [hleft, hright, ih, hT.symm]

/-- The vacuum is fixed by every power. -/
theorem pow_fix (hT : VacuumTransfer T Ω) (n : ℕ) : (T ^ n) Ω = Ω := by
  induction n with
  | zero => simp
  | succ m ih =>
      have hstep : (T ^ (m + 1)) Ω = T ((T ^ m) Ω) := by
        rw [pow_succ']
        rfl
      rw [hstep, ih, hT.fix]

/-- The projected operator kills the vacuum. -/
theorem projected_vacuum (hT : VacuumTransfer T Ω) : projectedTransfer T Ω Ω = 0 := by
  simp [projectedTransfer_apply, hT.fix, hT.unit]

/-- The projected operator is symmetric. -/
theorem projected_symm (hT : VacuumTransfer T Ω) :
    ∀ v w, ⟪projectedTransfer T Ω v, w⟫ = ⟪v, projectedTransfer T Ω w⟫ := by
  intro v w
  simp only [projectedTransfer_apply, inner_sub_left, inner_sub_right, real_inner_smul_left,
    real_inner_smul_right]
  rw [hT.symm v w, real_inner_comm v Ω]
  ring

/-- **The structural identity.**  For `n ≥ 1` the `n`-th power of the projected
operator subtracts exactly the vacuum contribution:
`Sⁿ v = Tⁿ v − ⟨Ω,v⟩ Ω`. -/
theorem projected_pow_succ (hT : VacuumTransfer T Ω) (v : H) (n : ℕ) :
    (projectedTransfer T Ω ^ (n + 1)) v = (T ^ (n + 1)) v - (⟪Ω, v⟫ : ℝ) • Ω := by
  induction n with
  | zero => simp [projectedTransfer_apply]
  | succ m ih =>
      have hS : (projectedTransfer T Ω ^ (m + 2)) v
          = projectedTransfer T Ω ((projectedTransfer T Ω ^ (m + 1)) v) := by
        rw [pow_succ']
        rfl
      have hT' : (T ^ (m + 2)) v = T ((T ^ (m + 1)) v) := by
        rw [pow_succ']
        rfl
      -- the vacuum overlap of `T^{m+1} v - ⟨Ω,v⟩ Ω` vanishes
      have horth : (⟪Ω, (T ^ (m + 1)) v - (⟪Ω, v⟫ : ℝ) • Ω⟫ : ℝ) = 0 := by
        rw [inner_sub_right, real_inner_smul_right, hT.inner_vacuum_self]
        have : (⟪Ω, (T ^ (m + 1)) v⟫ : ℝ) = ⟪(T ^ (m + 1)) Ω, v⟫ := (hT.pow_symm _ Ω v).symm
        rw [this, hT.pow_fix]
        ring
      rw [hS, ih, hT']
      simp only [projectedTransfer_apply, horth]
      rw [map_sub, map_smul, hT.fix]
      simp

/-- **The connected correlator is a matrix element of the projected operator.**
This is the elementary reason the *truncated* two-point function, and not the
full one, is the object that sees the gap. -/
theorem connCorr_eq (hT : VacuumTransfer T Ω) (v : H) (n : ℕ) :
    connCorr T Ω v (n + 1) = ⟪v, (projectedTransfer T Ω ^ (n + 1)) v⟫ := by
  rw [connCorr, hT.projected_pow_succ v n, inner_sub_right, real_inner_smul_right,
    real_inner_comm v Ω]
  ring

end VacuumTransfer

/-! ## Norm of a symmetric operator: the elementary C*-step -/

/-- Square roots, by hand: `a ≤ b` from `a² ≤ b²` for nonnegative reals. -/
private theorem le_of_sq_le_sq {a b : ℝ} (_ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 2 ≤ b ^ 2) :
    a ≤ b := by
  by_contra hc
  push_neg at hc
  nlinarith

/-- Applying a power of a continuous linear map, peeling the outer factor. -/
theorem pow_succ_apply (S : H →L[ℝ] H) (n : ℕ) (v : H) :
    (S ^ (n + 1)) v = S ((S ^ n) v) := by
  rw [pow_succ']
  rfl

/-- Applying a power of a continuous linear map, peeling the inner factor. -/
theorem pow_succ_apply' (S : H →L[ℝ] H) (n : ℕ) (v : H) :
    (S ^ (n + 1)) v = (S ^ n) (S v) := by
  rw [pow_succ]
  rfl

/-- Powers of a symmetric operator are symmetric. -/
theorem pow_symm_of_symm {S : H →L[ℝ] H} (hS : ∀ v w, ⟪S v, w⟫ = ⟪v, S w⟫) (n : ℕ) :
    ∀ v w, ⟪(S ^ n) v, w⟫ = ⟪v, (S ^ n) w⟫ := by
  induction n with
  | zero => intro v w; simp
  | succ m ih =>
      intro v w
      rw [pow_succ_apply' S m v, pow_succ_apply S m w, ih, hS]

/-- For a symmetric operator, `⟪v, S^{2n} v⟫ = ‖Sⁿ v‖²`. -/
theorem inner_pow_two_mul {S : H →L[ℝ] H} (hS : ∀ v w, ⟪S v, w⟫ = ⟪v, S w⟫) (n : ℕ) (v : H) :
    (⟪v, (S ^ (2 * n)) v⟫ : ℝ) = ‖(S ^ n) v‖ ^ 2 := by
  have h1 : (S ^ (2 * n)) v = (S ^ n) ((S ^ n) v) := by
    rw [two_mul, pow_add]; rfl
  rw [h1, ← pow_symm_of_symm hS n v ((S ^ n) v), real_inner_self_eq_norm_sq]

/-- For a symmetric operator, `‖S²‖ = ‖S‖²`.  Proved from Cauchy–Schwarz
directly, so the module does not depend on the C*-algebra API. -/
theorem norm_sq_of_symm {S : H →L[ℝ] H} (hS : ∀ v w, ⟪S v, w⟫ = ⟪v, S w⟫) :
    ‖S ^ 2‖ = ‖S‖ ^ 2 := by
  refine le_antisymm ?_ ?_
  · calc ‖S ^ 2‖ = ‖S * S‖ := by rw [sq]
      _ ≤ ‖S‖ * ‖S‖ := norm_mul_le _ _
      _ = ‖S‖ ^ 2 := (sq ‖S‖).symm
  · -- `‖S v‖² = ⟪v, S² v⟫ ≤ ‖v‖ ‖S²‖ ‖v‖`
    have key : ∀ v : H, ‖S v‖ ≤ Real.sqrt ‖S ^ 2‖ * ‖v‖ := by
      intro v
      have h1 : ‖S v‖ ^ 2 = ⟪v, (S ^ 2) v⟫ := by
        have hsq : (S ^ 2) v = S (S v) := by rw [sq]; rfl
        rw [hsq, ← hS v (S v), real_inner_self_eq_norm_sq]
      have h2 : ‖S v‖ ^ 2 ≤ ‖S ^ 2‖ * ‖v‖ ^ 2 := by
        rw [h1]
        calc ⟪v, (S ^ 2) v⟫ ≤ ‖v‖ * ‖(S ^ 2) v‖ := real_inner_le_norm _ _
          _ ≤ ‖v‖ * (‖S ^ 2‖ * ‖v‖) := by
              gcongr
              exact (S ^ 2).le_opNorm v
          _ = ‖S ^ 2‖ * ‖v‖ ^ 2 := by ring
      have hnn : (0 : ℝ) ≤ Real.sqrt ‖S ^ 2‖ * ‖v‖ :=
        mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
      refine le_of_sq_le_sq (norm_nonneg _) hnn ?_
      rw [mul_pow, Real.sq_sqrt (norm_nonneg _)]
      exact h2
    have hkey : ‖S‖ ≤ Real.sqrt ‖S ^ 2‖ :=
      S.opNorm_le_bound (Real.sqrt_nonneg _) key
    nlinarith [Real.sq_sqrt (norm_nonneg (S ^ 2)), norm_nonneg S, Real.sqrt_nonneg ‖S ^ 2‖]

/-- Iterating the C*-step: `‖S^(2^k)‖ = ‖S‖^(2^k)` for symmetric `S`. -/
theorem norm_pow_two_pow_of_symm {S : H →L[ℝ] H} (hS : ∀ v w, ⟪S v, w⟫ = ⟪v, S w⟫) :
    ∀ k : ℕ, ‖S ^ (2 ^ k)‖ = ‖S‖ ^ (2 ^ k) := by
  have hpow : ∀ (n : ℕ), (∀ v w, ⟪(S ^ n) v, w⟫ = ⟪v, (S ^ n) w⟫) := pow_symm_of_symm hS
  intro k
  induction k with
  | zero => simp
  | succ j ih =>
      have hsplit : S ^ (2 ^ (j + 1)) = (S ^ (2 ^ j)) ^ 2 := by
        rw [← pow_mul, pow_succ]
      rw [hsplit, norm_sq_of_symm (hpow (2 ^ j)), ih, ← pow_mul, ← pow_succ]

/-- If the powers of a symmetric operator are dominated by `M·rⁿ`, its norm is
at most `r`.  This is the Gelfand step, done by hand along `n = 2^k`. -/
theorem norm_le_of_pow_bound {S : H →L[ℝ] H} (hS : ∀ v w, ⟪S v, w⟫ = ⟪v, S w⟫)
    {M r : ℝ} (hr : 0 ≤ r)
    (hbound : ∀ n : ℕ, ‖S ^ n‖ ≤ M * r ^ n) : ‖S‖ ≤ r := by
  by_contra hcon
  push_neg at hcon
  -- `r < ‖S‖`, so `q := ‖S‖ / r > 1` (and `r = 0` is immediate)
  rcases eq_or_lt_of_le hr with hr0 | hr0
  · -- r = 0 : the bound at n = 1 forces ‖S‖ = 0
    have h1 := hbound 1
    rw [← hr0] at h1
    have h1' : ‖S‖ ≤ 0 := by simpa using h1
    rw [← hr0] at hcon
    linarith
  · have hq : 1 < ‖S‖ / r := (one_lt_div hr0).mpr hcon
    obtain ⟨n₀, hn₀⟩ := pow_unbounded_of_one_lt M hq
    obtain ⟨k, hk⟩ : ∃ k : ℕ, n₀ ≤ 2 ^ k := ⟨n₀, Nat.lt_two_pow_self.le⟩
    have hmono : (‖S‖ / r) ^ n₀ ≤ (‖S‖ / r) ^ (2 ^ k) :=
      pow_le_pow_right₀ hq.le hk
    have hnorm : ‖S‖ ^ (2 ^ k) ≤ M * r ^ (2 ^ k) := by
      rw [← norm_pow_two_pow_of_symm hS k]; exact hbound _
    have hrpow : (0 : ℝ) < r ^ (2 ^ k) := pow_pos hr0 _
    have : (‖S‖ / r) ^ (2 ^ k) ≤ M := by
      rw [div_pow, div_le_iff₀ hrpow]; exact hnorm
    linarith [hn₀.trans_le (hmono.trans this)]

/-! ## O-1a — clustering at every vector is equivalent to the gap -/

variable [CompleteSpace H]

/-- **Gap ⟹ clustering** (the easy direction), with the explicit constant
`‖v‖²`. -/
theorem clustering_of_gap {T : H →L[ℝ] H} {Ω : H} (hT : VacuumTransfer T Ω)
    {r : ℝ} (hgap : ‖projectedTransfer T Ω‖ ≤ r) (v : H) (n : ℕ) :
    |connCorr T Ω v n| ≤ ‖v‖ ^ 2 * r ^ n := by
  cases n with
  | zero =>
      -- `connCorr … 0 = ‖v‖² − ⟨Ω,v⟩²`, between `0` and `‖v‖²` by Cauchy–Schwarz
      have hcs : (⟪Ω, v⟫ : ℝ) ^ 2 ≤ ‖v‖ ^ 2 := by
        have := abs_real_inner_le_norm Ω v
        rw [hT.unit, one_mul] at this
        nlinarith [abs_nonneg (⟪Ω, v⟫ : ℝ), sq_abs (⟪Ω, v⟫ : ℝ), norm_nonneg v]
      have hself : (⟪v, (T ^ 0) v⟫ : ℝ) = ‖v‖ ^ 2 := by
        simp
      rw [connCorr, hself]
      rw [pow_zero, mul_one, abs_le]
      constructor <;> nlinarith [sq_nonneg (⟪Ω, v⟫ : ℝ)]
  | succ m =>
      rw [hT.connCorr_eq v m]
      set S := projectedTransfer T Ω
      have hstep : ‖(S ^ (m + 1)) v‖ ≤ r ^ (m + 1) * ‖v‖ := by
        calc ‖(S ^ (m + 1)) v‖ ≤ ‖S ^ (m + 1)‖ * ‖v‖ := (S ^ (m + 1)).le_opNorm v
          _ ≤ ‖S‖ ^ (m + 1) * ‖v‖ :=
              mul_le_mul_of_nonneg_right (norm_pow_le' S (Nat.succ_pos m)) (norm_nonneg v)
          _ ≤ r ^ (m + 1) * ‖v‖ :=
              mul_le_mul_of_nonneg_right
                (pow_le_pow_left₀ (norm_nonneg S) hgap (m + 1)) (norm_nonneg v)
      calc |⟪v, (S ^ (m + 1)) v⟫| ≤ ‖v‖ * ‖(S ^ (m + 1)) v‖ := abs_real_inner_le_norm _ _
        _ ≤ ‖v‖ * (r ^ (m + 1) * ‖v‖) :=
            mul_le_mul_of_nonneg_left hstep (norm_nonneg v)
        _ = ‖v‖ ^ 2 * r ^ (m + 1) := by ring

/-- **Clustering ⟹ gap.**  Exponential decay of the connected two-point
function at *every* vector, with a vector-dependent constant, already forces the
operator-norm bound `‖T − |Ω⟩⟨Ω|‖ ≤ r`.  The uniformisation of the constants is
Banach–Steinhaus; completeness is what pays for it. -/
theorem gap_of_clustering {T : H →L[ℝ] H} {Ω : H} (hT : VacuumTransfer T Ω)
    {r : ℝ} (hr : 0 ≤ r)
    (hclust : ∀ v : H, ∃ C : ℝ, ∀ n : ℕ, |connCorr T Ω v n| ≤ C * r ^ n) :
    ‖projectedTransfer T Ω‖ ≤ r := by
  set S := projectedTransfer T Ω with hSdef
  have hSsymm := hT.projected_symm
  rcases eq_or_lt_of_le hr with hr0 | hr0
  · -- `r = 0`: clustering at `n = 2` gives `‖S v‖ = 0` for every `v`
    have hSzero : ∀ v : H, S v = 0 := by
      intro v
      obtain ⟨C, hC⟩ := hclust v
      have h2 := hC 2
      rw [← hr0] at h2
      have hz : C * (0 : ℝ) ^ 2 = 0 := by norm_num
      rw [hz] at h2
      have heq : connCorr T Ω v 2 = ‖S v‖ ^ 2 := by
        have h1 := hT.connCorr_eq v 1
        have h3 := inner_pow_two_mul hSsymm 1 v
        norm_num at h1 h3
        rw [h1, h3, hSdef]
        rfl
      rw [heq] at h2
      have hle : ‖S v‖ ^ 2 ≤ 0 := le_of_abs_le h2
      have : ‖S v‖ = 0 := by nlinarith [norm_nonneg (S v)]
      exact norm_eq_zero.mp this
    have : S = 0 := by ext v; exact hSzero v
    rw [this, norm_zero, ← hr0]
  · -- `r > 0`: pointwise bounds on `S^n / r^n`, then Banach–Steinhaus
    have hptw : ∀ v : H, ∃ C : ℝ, ∀ n : ℕ, ‖((r ^ n)⁻¹ • (S ^ n)) v‖ ≤ C := by
      intro v
      obtain ⟨C, hC⟩ := hclust v
      have hnn : (0 : ℝ) ≤ max C 0 := le_max_right C 0
      -- for `n ≥ 1`: `‖Sⁿ v‖² = connCorr … (2n) ≤ C r^{2n}`
      have hstep : ∀ m : ℕ, ‖(S ^ (m + 1)) v‖ ≤ Real.sqrt (max C 0) * r ^ (m + 1) := by
        intro m
        have hidx : 2 * (m + 1) = (2 * m + 1) + 1 := by ring
        have h2 := hC (2 * (m + 1))
        rw [hidx, hT.connCorr_eq v (2 * m + 1), ← hidx] at h2
        have hsq : (⟪v, (S ^ (2 * (m + 1))) v⟫ : ℝ) = ‖(S ^ (m + 1)) v‖ ^ 2 :=
          inner_pow_two_mul hSsymm (m + 1) v
        have hbnd : ‖(S ^ (m + 1)) v‖ ^ 2 ≤ (Real.sqrt (max C 0) * r ^ (m + 1)) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt hnn, ← pow_mul, mul_comm (m + 1) 2, ← hsq]
          calc (⟪v, (S ^ (2 * (m + 1))) v⟫ : ℝ) ≤ |⟪v, (S ^ (2 * (m + 1))) v⟫| := le_abs_self _
            _ ≤ C * r ^ (2 * (m + 1)) := h2
            _ ≤ max C 0 * r ^ (2 * (m + 1)) :=
                mul_le_mul_of_nonneg_right (le_max_left C 0) (pow_nonneg hr0.le _)
        exact le_of_sq_le_sq (norm_nonneg _) (by positivity) hbnd
      refine ⟨max (Real.sqrt (max C 0)) ‖v‖, fun n => ?_⟩
      have hrn : (0 : ℝ) < r ^ n := pow_pos hr0 n
      rw [ContinuousLinearMap.smul_apply, norm_smul, norm_inv, Real.norm_eq_abs,
        abs_of_pos hrn, inv_mul_le_iff₀ hrn]
      cases n with
      | zero =>
          simp only [pow_zero, one_mul]
          exact le_max_right _ _
      | succ m =>
          calc ‖(S ^ (m + 1)) v‖ ≤ Real.sqrt (max C 0) * r ^ (m + 1) := hstep m
            _ = r ^ (m + 1) * Real.sqrt (max C 0) := mul_comm _ _
            _ ≤ r ^ (m + 1) * max (Real.sqrt (max C 0)) ‖v‖ :=
                mul_le_mul_of_nonneg_left (le_max_left _ _) (pow_nonneg hr0.le _)
    obtain ⟨M, hM⟩ := banach_steinhaus (g := fun n : ℕ => (r ^ n)⁻¹ • (S ^ n)) hptw
    have hbound : ∀ n : ℕ, ‖S ^ n‖ ≤ max M 1 * r ^ n := by
      intro n
      have hrn : (0 : ℝ) < r ^ n := pow_pos hr0 n
      have hn := hM n
      rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hrn, inv_mul_le_iff₀ hrn] at hn
      calc ‖S ^ n‖ ≤ r ^ n * M := hn
        _ = M * r ^ n := mul_comm _ _
        _ ≤ max M 1 * r ^ n := mul_le_mul_of_nonneg_right (le_max_left M 1) hrn.le
    exact norm_le_of_pow_bound hSsymm hr hbound

/-- **O-1a — the equivalence.**  For a symmetric transfer operator with a fixed
unit vacuum, exponential clustering of the connected two-point function at rate
`r` is *equivalent* to the spectral-gap bound `‖T − |Ω⟩⟨Ω|‖ ≤ r`. -/
theorem clustering_iff_gap {T : H →L[ℝ] H} {Ω : H} (hT : VacuumTransfer T Ω)
    {r : ℝ} (hr : 0 ≤ r) :
    ‖projectedTransfer T Ω‖ ≤ r ↔
      ∀ v : H, ∃ C : ℝ, ∀ n : ℕ, |connCorr T Ω v n| ≤ C * r ^ n := by
  constructor
  · intro hgap v
    exact ⟨‖v‖ ^ 2, fun n => clustering_of_gap hT hgap v n⟩
  · exact gap_of_clustering hT hr

/-! ## O-1b — clustering on a dense set needs a uniform constant -/

/-- **Clustering on a dense set with a uniformly quadratic constant ⟹ gap.**

This is the version a cluster expansion can hope to feed, because an expansion
produces bounds for a *family* of observables, not for every vector of the
Hilbert space.  The price is that the constant must be `K‖v‖²` **uniformly over
the family**: the proof is continuity of the quadratic form, and continuity is
exactly what a vector-dependent constant destroys.  There is no
Banach–Steinhaus substitute here, since a dense subspace may be meagre (the span of a countable family is), so Banach-Steinhaus's non-meagreness hypothesis is unavailable.

This theorem is therefore also the precise statement of what an application
would have to supply — see the module docstring and `docs/O-BRIDGE-CHARTER.md`
phase O-2. -/
theorem gap_of_dense_clustering {T : H →L[ℝ] H} {Ω : H} (hT : VacuumTransfer T Ω)
    {r K : ℝ} (hr : 0 ≤ r) (hK : 0 ≤ K) (D : Set H) (hD : Dense D)
    (hclust : ∀ v ∈ D, ∀ n : ℕ, |connCorr T Ω v (2 * n + 2)| ≤ K * ‖v‖ ^ 2 * r ^ (2 * n + 2)) :
    ‖projectedTransfer T Ω‖ ≤ r := by
  set S := projectedTransfer T Ω with hSdef
  have hSsymm := hT.projected_symm
  -- the quadratic identity `⟪v, S^{2n+2} v⟫ = ‖S^{n+1} v‖²`
  have hquad : ∀ (n : ℕ) (v : H), (⟪v, (S ^ (2 * n + 2)) v⟫ : ℝ) = ‖(S ^ (n + 1)) v‖ ^ 2 := by
    intro n v
    have hidx : 2 * n + 2 = 2 * (n + 1) := by ring
    rw [hidx]
    exact inner_pow_two_mul hSsymm (n + 1) v
  -- on `D` the bound reads `‖S^{n+1} v‖² ≤ K ‖v‖² r^{2n+2}`
  have hD' : ∀ (n : ℕ) (v : H), ‖(S ^ (n + 1)) v‖ ^ 2 ≤ K * ‖v‖ ^ 2 * r ^ (2 * n + 2) := by
    intro n
    have hcont₁ : Continuous fun v : H => ‖(S ^ (n + 1)) v‖ ^ 2 := by fun_prop
    have hcont₂ : Continuous fun v : H => K * ‖v‖ ^ 2 * r ^ (2 * n + 2) := by fun_prop
    have hsub : D ⊆ {v : H | ‖(S ^ (n + 1)) v‖ ^ 2 ≤ K * ‖v‖ ^ 2 * r ^ (2 * n + 2)} := by
      intro v hv
      have h := hclust v hv n
      rw [show 2 * n + 2 = (2 * n + 1) + 1 by ring, hT.connCorr_eq v (2 * n + 1),
        show (2 * n + 1) + 1 = 2 * n + 2 by ring] at h
      simp only [Set.mem_setOf_eq]
      rw [← hquad n v]
      calc (⟪v, (S ^ (2 * n + 2)) v⟫ : ℝ) ≤ |⟪v, (S ^ (2 * n + 2)) v⟫| := le_abs_self _
        _ ≤ K * ‖v‖ ^ 2 * r ^ (2 * n + 2) := h
    intro v
    exact (isClosed_le hcont₁ hcont₂).closure_subset_iff.mpr hsub (hD.closure_eq ▸ Set.mem_univ v)
  -- hence `‖S^{n+1}‖ ≤ √K r^{n+1}`, and the Gelfand step finishes
  have hnorm : ∀ n : ℕ, ‖S ^ (n + 1)‖ ≤ Real.sqrt K * r ^ (n + 1) := by
    intro n
    refine (S ^ (n + 1)).opNorm_le_bound (by positivity) fun v => ?_
    have h := hD' n v
    have hrw : K * ‖v‖ ^ 2 * r ^ (2 * n + 2) = (Real.sqrt K * r ^ (n + 1) * ‖v‖) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hK, ← pow_mul]
      ring_nf
    rw [hrw] at h
    exact le_of_sq_le_sq (norm_nonneg _) (by positivity) h
  have hbound : ∀ n : ℕ, ‖S ^ n‖ ≤ max (Real.sqrt K) 1 * r ^ n := by
    intro n
    cases n with
    | zero =>
        simp only [pow_zero, mul_one]
        have hid : ‖(1 : H →L[ℝ] H)‖ ≤ 1 := by
          simpa [ContinuousLinearMap.one_def] using
            (ContinuousLinearMap.norm_id_le : ‖ContinuousLinearMap.id ℝ H‖ ≤ 1)
        exact hid.trans (le_max_right _ _)
    | succ m =>
        calc ‖S ^ (m + 1)‖ ≤ Real.sqrt K * r ^ (m + 1) := hnorm m
          _ ≤ max (Real.sqrt K) 1 * r ^ (m + 1) :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hr _)
  exact norm_le_of_pow_bound hSsymm hr hbound

/-! ## Volume-uniformity -/

/-- **The volume-uniform gap.**  A family of transfer operators — one per
finite volume, on its own Hilbert space — that clusters at a *common* rate
`r < 1` has a *common* strictly positive mass `m = −log r`.  The uniformity is
not an extra hypothesis: the conclusion of `gap_of_clustering` is an
operator-norm bound whose constant never sees the index. -/
theorem volumeUniform_gap {ι : Type*} {Hs : ι → Type*}
    [∀ i, NormedAddCommGroup (Hs i)] [∀ i, InnerProductSpace ℝ (Hs i)]
    [∀ i, CompleteSpace (Hs i)]
    (T : ∀ i, Hs i →L[ℝ] Hs i) (Ω : ∀ i, Hs i)
    (hT : ∀ i, VacuumTransfer (T i) (Ω i))
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (hclust : ∀ i, ∀ v : Hs i, ∃ C : ℝ, ∀ n : ℕ, |connCorr (T i) (Ω i) v n| ≤ C * r ^ n) :
    ∃ m : ℝ, 0 < m ∧ ∀ i, ‖projectedTransfer (T i) (Ω i)‖ ≤ Real.exp (-m) := by
  refine ⟨-Real.log r, neg_pos.mpr (Real.log_neg hr0 hr1), fun i => ?_⟩
  have hexp : Real.exp (-(-Real.log r)) = r := by
    rw [neg_neg, Real.exp_log hr0]
  rw [hexp]
  exact gap_of_clustering (hT i) hr0.le (hclust i)

/-! ## Non-vacuity -/

/-- **Non-vacuity witness (general).**  Whenever the vacuum has a unit normal
companion — i.e. the fluctuation sector is nonzero — there is a transfer
operator with a strictly positive gap `−log r` whose projected part is **not**
the zero operator.  So `VacuumTransfer` together with a strict gap is not
satisfiable only by the degenerate one-dimensional instance. -/
theorem exists_vacuumTransfer_gap {Ω w : H} (hΩ : ‖Ω‖ = 1) (hw : ‖w‖ = 1)
    (hperp : (⟪Ω, w⟫ : ℝ) = 0) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    ∃ T : H →L[ℝ] H, VacuumTransfer T Ω ∧
      ‖projectedTransfer T Ω‖ = r ∧ projectedTransfer T Ω ≠ 0 ∧
      0 < -Real.log r := by
  refine ⟨r • (1 : H →L[ℝ] H) + (1 - r) • vacuumProjection Ω, ?_, ?_, ?_, ?_⟩
  · constructor
    · intro v u
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.one_apply, vacuumProjection_apply, inner_add_left, inner_add_right,
        real_inner_smul_left, real_inner_smul_right]
      rw [real_inner_comm v Ω]
      ring
    · exact hΩ
    · have hΩΩ : (⟪Ω, Ω⟫ : ℝ) = 1 := by rw [real_inner_self_eq_norm_sq, hΩ]; norm_num
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.one_apply, vacuumProjection_apply, hΩΩ, one_smul]
      module
  · -- the projected operator is `r · (1 − |Ω⟩⟨Ω|)`, of norm exactly `r`
    have hEq : projectedTransfer (r • (1 : H →L[ℝ] H) + (1 - r) • vacuumProjection Ω) Ω
        = r • ((1 : H →L[ℝ] H) - vacuumProjection Ω) := by
      rw [projectedTransfer]
      module
    rw [hEq, norm_smul, Real.norm_eq_abs, abs_of_pos hr0]
    have hle : ‖(1 : H →L[ℝ] H) - vacuumProjection Ω‖ ≤ 1 := by
      refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
      have hΩΩ : (⟪Ω, Ω⟫ : ℝ) = 1 := by rw [real_inner_self_eq_norm_sq, hΩ]; norm_num
      have hexp : ‖v - (⟪Ω, v⟫ : ℝ) • Ω‖ ^ 2 = ‖v‖ ^ 2 - (⟪Ω, v⟫ : ℝ) ^ 2 := by
        rw [← real_inner_self_eq_norm_sq, inner_sub_sub_self]
        simp only [real_inner_smul_left, real_inner_smul_right, hΩΩ]
        rw [real_inner_self_eq_norm_sq, real_inner_comm v Ω]
        ring
      have : ‖v - (⟪Ω, v⟫ : ℝ) • Ω‖ ^ 2 ≤ ‖v‖ ^ 2 := by
        rw [hexp]; nlinarith [sq_nonneg (⟪Ω, v⟫ : ℝ)]
      have hnn := norm_nonneg (v - (⟪Ω, v⟫ : ℝ) • Ω)
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
        vacuumProjection_apply, one_mul]
      nlinarith [norm_nonneg v]
    have hge : (1 : ℝ) ≤ ‖(1 : H →L[ℝ] H) - vacuumProjection Ω‖ := by
      have happ : ((1 : H →L[ℝ] H) - vacuumProjection Ω) w = w := by
        simp [vacuumProjection_apply, hperp]
      have := ((1 : H →L[ℝ] H) - vacuumProjection Ω).le_opNorm w
      rw [happ, hw, mul_one] at this
      exact this
    rw [le_antisymm hle hge, mul_one]
  · intro hzero
    have hEq : projectedTransfer (r • (1 : H →L[ℝ] H) + (1 - r) • vacuumProjection Ω) Ω
        = r • ((1 : H →L[ℝ] H) - vacuumProjection Ω) := by
      rw [projectedTransfer]
      module
    rw [hEq] at hzero
    have happ : (r • ((1 : H →L[ℝ] H) - vacuumProjection Ω)) w = r • w := by
      simp [vacuumProjection_apply, hperp]
    rw [hzero] at happ
    simp only [ContinuousLinearMap.zero_apply] at happ
    have hne : r • w ≠ (0 : H) := by
      refine smul_ne_zero (ne_of_gt hr0) ?_
      intro hw0
      rw [hw0, norm_zero] at hw
      exact absurd hw (by norm_num)
    exact hne happ.symm
  · exact neg_pos.mpr (Real.log_neg hr0 hr1)

/-- **Non-vacuity witness (concrete).**  The two-dimensional Euclidean instance:
`Ω = e₀`, `w = e₁`.  Every hypothesis of `exists_vacuumTransfer_gap` is
discharged, so the witness family above is genuinely inhabited. -/
theorem euclidean_two_dim_vacuumTransfer_gap {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    ∃ (T : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)),
      VacuumTransfer T (EuclideanSpace.single 0 1) ∧
      ‖projectedTransfer T (EuclideanSpace.single (0 : Fin 2) (1 : ℝ))‖ = r ∧
      projectedTransfer T (EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) ≠ 0 ∧
      0 < -Real.log r := by
  have hΩ : ‖(EuclideanSpace.single (0 : Fin 2) (1 : ℝ))‖ = 1 := by
    rw [EuclideanSpace.norm_single]; norm_num
  have hw : ‖(EuclideanSpace.single (1 : Fin 2) (1 : ℝ))‖ = 1 := by
    rw [EuclideanSpace.norm_single]; norm_num
  have hperp : (⟪(EuclideanSpace.single (0 : Fin 2) (1 : ℝ)),
      (EuclideanSpace.single (1 : Fin 2) (1 : ℝ))⟫ : ℝ) = 0 := by
    simp [PiLp.inner_apply, EuclideanSpace.single_apply, Fin.sum_univ_two]
  exact exists_vacuumTransfer_gap hΩ hw hperp hr0 hr1

end YangMills.OS
