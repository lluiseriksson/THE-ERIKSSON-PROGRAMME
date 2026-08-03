/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson
-/
import Mathlib
import YangMills.ClayCore.TracePathExpansion
import YangMills.OS.DobrushinBridge
import YangMills.OS.TransferGap

/-!
# D-6 / B-2+B-3 — the abstract transport theorem: uniform band-covariance
decay transports to the uniform operator gap

Design: `docs/DOBRUSHIN-D6-B2-DESIGN.md`, registered before this file.
Gates G21-G23 of `scripts/judge_dobrushin_d6b.py` passed 142/142 in both
interpreter modes on the plane before this file existed (ledger
Addendum 597); G21 measured the identity below to `1e-10`, including on a
matrix with a NEGATIVE subdominant eigenvalue.

## What this module is

For finite `X`, symmetric `M`, strictly positive `Om` with `M Om = Om`
(B-1's normalised data), the operator `opOf M` on `EuclideanSpace ℝ X`
with unit vacuum `vacOf Om = Om / ‖Om‖` is a `VacuumTransfer`, and the
EXACT identity (`connCorr_eq_bandCov`)

    connCorr (opOf M) (vacOf Om) v n
      = (∑ Om²) · bandCov M Om n f_v f_v,       f_v = v / Om,

holds for EVERY vector `v` and every `n` — `bandCov` being the
MEASURE-level band covariance of B-1: path sums of the band weight,
normalised by the n-independent mass, centred by the band expectations.
Consequently (`abstract_uniform_gap`): a family of such data with a
COMMON band-decay rate `r < 1` — constants free per `(i, f)` — has a
common strictly positive mass, `‖projectedTransfer‖ ≤ exp(−m)` for every
member at once, `m = −log r > 0`.

## The anti-circularity clause, discharged (charter Amendment 2(i))

The decay hypothesis of `abstract_uniform_gap` quantifies over band
covariances: finite path sums of `bandW`.  No operator, no norm, no
spectrum occurs in it.  The identification of those sums with operator
matrix elements is the THEOREM `connCorr_eq_bandCov` (via B-1's
`band_pair`), not an assumption, so the hypothesis cannot be the
conclusion in other notation.

## What is deliberately NOT here

* NO positivity of entries: the abstract theorem needs only symmetry, a
  strictly positive fixed vector, and the band-decay hypothesis.  Fewer
  hypotheses than the Perron context that produces the data in practice;
  the corollary module instantiates from actual Perron data.
* NO Ising, NO Dobrushin, NO rectangle: per Amendment 2 the statement is
  free of them.  The two-state witness (`transport_witness`) shows the
  data class is inhabited with a NONZERO fluctuation sector at every
  rate, so nothing here is satisfied only by a degenerate instance; the
  PHYSICAL witness is the corollary module's job.
* NO uniformity of `min Om`, of `‖f_v‖∞`, of constants, of the vector
  `Om` across the family (B-2's binding non-goals): every constant below
  is free per `(i, v)`, exactly as the consumer's quantifier order
  permits.
-/

namespace YangMills.OS

namespace Dobrushin

open Finset
open scoped RealInnerProductSpace

set_option linter.unusedSectionVars false

variable {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]

/-! ## §1  The measure-level band covariance -/

/-- The band covariance of two slice observables at time separation `n`:
path sums of B-1's band weight, normalised by the n-independent mass
`∑ Om²`, centred by the band expectations.  No operator occurs in this
definition. -/
noncomputable def bandCov (M : Matrix X X ℝ) (Om : X → ℝ) (n : ℕ)
    (f g : X → ℝ) : ℝ :=
  (∑ v : Fin (n + 1) → X, f (v 0) * g (v (Fin.last n)) * bandW M Om n v)
      / (∑ x, Om x * Om x)
    - bandE Om f * bandE Om g

/-! ## §2  The operator, the unit vacuum, and their elementary calculus

The continuous linear map comes from `Matrix.toEuclideanCLM`; every fact
about it used below is re-proved entrywise from `opOf_apply`, so no
star-algebra API is load-bearing. -/

/-- The kernel as a continuous linear endomorphism of Euclidean space. -/
noncomputable def opOf (M : Matrix X X ℝ) :
    EuclideanSpace ℝ X →L[ℝ] EuclideanSpace ℝ X :=
  Matrix.toEuclideanCLM (𝕜 := ℝ) M

/-- The unit vacuum: the boundary vector, Euclidean-normalised. -/
noncomputable def vacOf (Om : X → ℝ) : EuclideanSpace ℝ X :=
  WithLp.toLp 2 fun x => Om x / Real.sqrt (∑ y, Om y * Om y)

theorem opOf_apply (M : Matrix X X ℝ) (v : EuclideanSpace ℝ X) (x : X) :
    opOf M v x = ∑ y, M x y * v y := by
  have h : opOf M v x = Matrix.mulVec M (WithLp.ofLp v) x := rfl
  rw [h]
  simp [Matrix.mulVec, dotProduct]

/-- The real inner product of Euclidean vectors, as a plain sum. -/
theorem inner_eq_sum (u w : EuclideanSpace ℝ X) :
    ⟪u, w⟫ = ∑ x, u x * w x := by
  rw [PiLp.inner_apply]
  exact Finset.sum_congr rfl fun x _ => mul_comm _ _

/-- `opOf 1 = 1`, entrywise. -/
theorem opOf_one : opOf (1 : Matrix X X ℝ) = 1 := by
  refine ContinuousLinearMap.ext fun v => ?_
  refine PiLp.ext fun x => ?_
  have hid : (1 : EuclideanSpace ℝ X →L[ℝ] EuclideanSpace ℝ X) v = v := rfl
  rw [hid, opOf_apply]
  have h : ∀ y, (1 : Matrix X X ℝ) x y * v y
      = if x = y then v y else 0 := by
    intro y
    rw [Matrix.one_apply]
    by_cases hxy : x = y
    · rw [if_pos hxy, if_pos hxy, one_mul]
    · rw [if_neg hxy, if_neg hxy, zero_mul]
  rw [Finset.sum_congr rfl fun y _ => h y,
    Finset.sum_ite_eq Finset.univ x (fun y => v y),
    if_pos (Finset.mem_univ x)]

/-- `opOf` is multiplicative, entrywise. -/
theorem opOf_mul (A B : Matrix X X ℝ) : opOf (A * B) = opOf A * opOf B := by
  refine ContinuousLinearMap.ext fun v => ?_
  refine PiLp.ext fun x => ?_
  have hcomp : (opOf A * opOf B) v x = opOf A (opOf B v) x := rfl
  rw [hcomp, opOf_apply, opOf_apply]
  have h : ∀ y, (A * B) x y * v y = ∑ z, A x z * (B z y * v y) := by
    intro y
    rw [Matrix.mul_apply, Finset.sum_mul]
    exact Finset.sum_congr rfl fun z _ => by ring
  rw [Finset.sum_congr rfl fun y _ => h y, Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [← Finset.mul_sum, ← opOf_apply B v z]

theorem opOf_pow (M : Matrix X X ℝ) : ∀ n : ℕ, opOf M ^ n = opOf (M ^ n) := by
  intro n
  induction n with
  | zero => rw [pow_zero, pow_zero, opOf_one]
  | succ m ih =>
      rw [pow_succ, pow_succ, ih]
      exact (opOf_mul (M ^ m) M).symm

/-- Symmetry of the kernel gives symmetry of the operator in the real
inner product. -/
theorem opOf_symm (M : Matrix X X ℝ) (hM : ∀ x y, M x y = M y x)
    (u w : EuclideanSpace ℝ X) : ⟪opOf M u, w⟫ = ⟪u, opOf M w⟫ := by
  rw [inner_eq_sum, inner_eq_sum]
  have hL : ∀ x, opOf M u x * w x = ∑ y, M x y * u y * w x := by
    intro x
    rw [opOf_apply, Finset.sum_mul]
  have hR : ∀ x, u x * opOf M w x = ∑ y, u x * (M x y * w y) := by
    intro x
    rw [opOf_apply, Finset.mul_sum]
  rw [Finset.sum_congr rfl fun x _ => hL x,
    Finset.sum_congr rfl fun x _ => hR x, Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun x _ => ?_
  rw [hM x a]
  ring

/-- The vacuum is a unit vector. -/
theorem vacOf_norm (Om : X → ℝ) (hOm : ∀ x, 0 < Om x) : ‖vacOf Om‖ = 1 := by
  have hS : 0 < ∑ y, Om y * Om y := bandNorm_pos Om hOm
  have hsum : (∑ x, ‖vacOf Om x‖ ^ 2) = 1 := by
    have h1 : ∀ x, ‖vacOf Om x‖ ^ 2
        = Om x * Om x * (∑ y, Om y * Om y)⁻¹ := by
      intro x
      have hx : vacOf Om x = Om x / Real.sqrt (∑ y, Om y * Om y) := rfl
      rw [hx, Real.norm_eq_abs, sq_abs, div_pow, Real.sq_sqrt hS.le,
        pow_two, div_eq_mul_inv]
    rw [Finset.sum_congr rfl fun x _ => h1 x, ← Finset.sum_mul,
      mul_inv_cancel₀ hS.ne']
  rw [EuclideanSpace.norm_eq, hsum, Real.sqrt_one]

/-- The operator fixes the vacuum. -/
theorem opOf_fix (M : Matrix X X ℝ) (Om : X → ℝ)
    (heig : ∀ x, ∑ y, M x y * Om y = Om x) :
    opOf M (vacOf Om) = vacOf Om := by
  refine PiLp.ext fun x => ?_
  rw [opOf_apply]
  have h : ∀ y, M x y * vacOf Om y
      = (M x y * Om y) / Real.sqrt (∑ z, Om z * Om z) := by
    intro y
    have hy : vacOf Om y = Om y / Real.sqrt (∑ z, Om z * Om z) := rfl
    rw [hy]
    ring
  rw [Finset.sum_congr rfl fun y _ => h y, ← Finset.sum_div, heig x]
  rfl

/-- The packaged data are a `VacuumTransfer` — the exact input of the
consumer `volumeUniform_gap`. -/
theorem vacuumTransfer_opOf (M : Matrix X X ℝ) (Om : X → ℝ)
    (hM : ∀ x y, M x y = M y x) (hOm : ∀ x, 0 < Om x)
    (heig : ∀ x, ∑ y, M x y * Om y = Om x) :
    VacuumTransfer (opOf M) (vacOf Om) :=
  ⟨opOf_symm M hM, vacOf_norm Om hOm, opOf_fix M Om heig⟩

/-! ## §3  B-2: the exact identity between the connected correlator and
the band covariance

The whole of "prefactor control": one identity, the prefactor being the
band mass `∑ Om²`.  The observable `v` is represented through Perron
positivity as `f_v = v / Om`, per the charter's B-2 spec; every constant
this produces stays on the `(i, v)` side of the consumer's quantifiers. -/

/-- **The B-2 identity.**  For every Euclidean vector `v` and every `n`,
the connected correlator of the packaged operator equals the band mass
times the measure-level band covariance of `f_v = v / Om`.  Exact — this
is a change of description, not an estimate. -/
theorem connCorr_eq_bandCov (M : Matrix X X ℝ) (Om : X → ℝ)
    (hOm : ∀ x, 0 < Om x) (v : EuclideanSpace ℝ X) (n : ℕ) :
    connCorr (opOf M) (vacOf Om) v n
      = (∑ x, Om x * Om x)
        * bandCov M Om n (fun x => v x / Om x) (fun x => v x / Om x) := by
  have hS : 0 < ∑ x, Om x * Om x := bandNorm_pos Om hOm
  set f : X → ℝ := fun x => v x / Om x with hf
  have hfv : ∀ x, f x * Om x = v x := by
    intro x
    rw [hf]
    exact div_mul_cancel₀ _ (hOm x).ne'
  have hpair : ⟪v, ((opOf M) ^ n) v⟫
      = ∑ p : Fin (n + 1) → X,
          f (p 0) * f (p (Fin.last n)) * bandW M Om n p := by
    rw [opOf_pow M n, inner_eq_sum]
    have h1 : ∀ x, v x * opOf (M ^ n) v x
        = ∑ y, (f x * Om x) * (M ^ n) x y * (f y * Om y) := by
      intro x
      rw [opOf_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun y _ => by rw [hfv x, hfv y]; ring
    rw [Finset.sum_congr rfl fun x _ => h1 x, ← band_pair M Om n f f]
  have hvacsum : ⟪vacOf Om, v⟫
      = (bandE Om f * ∑ y, Om y * Om y)
          / Real.sqrt (∑ y, Om y * Om y) := by
    have h3 : ∀ x, vacOf Om x * v x
        = (f x * Om x * Om x) / Real.sqrt (∑ y, Om y * Om y) := by
      intro x
      have hx : vacOf Om x = Om x / Real.sqrt (∑ y, Om y * Om y) := rfl
      rw [hx, ← hfv x]
      ring
    rw [inner_eq_sum, Finset.sum_congr rfl fun x _ => h3 x,
      ← Finset.sum_div]
    congr 1
    have h4 : bandE Om f * ∑ y, Om y * Om y = ∑ x, f x * Om x * Om x := by
      unfold bandE
      rw [div_mul_cancel₀ _ hS.ne']
    rw [h4]
  have hvac : ⟪vacOf Om, v⟫ * ⟪vacOf Om, v⟫
      = (∑ x, Om x * Om x) * (bandE Om f * bandE Om f) := by
    rw [hvacsum, div_mul_div_comm, Real.mul_self_sqrt hS.le]
    rw [show (bandE Om f * ∑ y, Om y * Om y)
          * (bandE Om f * ∑ y, Om y * Om y)
        = (bandE Om f * bandE Om f * ∑ y, Om y * Om y)
          * ∑ y, Om y * Om y from by ring]
    rw [mul_div_cancel_right₀ _ hS.ne']
    ring
  rw [connCorr, hpair, pow_two, hvac]
  unfold bandCov
  rw [mul_sub,
    mul_comm (∑ x, Om x * Om x)
      ((∑ p : Fin (n + 1) → X,
          f (p 0) * f (p (Fin.last n)) * bandW M Om n p)
        / (∑ x, Om x * Om x)),
    div_mul_cancel₀ _ hS.ne']

/-! ## §4  B-3: the abstract transport theorem -/

/-- **THE ABSTRACT TRANSPORT THEOREM** (charter Amendment 2, public
theorem (i)).  A family of finite slice types with symmetric kernels and
strictly positive normalised fixed vectors, whose band covariances decay
at a COMMON rate `r < 1` with constants free per `(i, f)`, has a common
strictly positive mass: every projected transfer operator of the family
is bounded by `exp(−m)` for one `m > 0`.

The hypothesis `hdecay` is stated on path sums of the band weight — the
measure side.  Its identification with operator matrix elements is
`connCorr_eq_bandCov`, proved, not assumed; no Ising, no Dobrushin, no
rectangle occurs anywhere in this statement. -/
theorem abstract_uniform_gap {ι : Type*} {Xs : ι → Type*}
    [∀ i, Fintype (Xs i)] [∀ i, DecidableEq (Xs i)] [∀ i, Nonempty (Xs i)]
    (M : ∀ i, Matrix (Xs i) (Xs i) ℝ) (Om : ∀ i, Xs i → ℝ)
    (hM : ∀ i, ∀ x y, M i x y = M i y x)
    (hOm : ∀ i, ∀ x, 0 < Om i x)
    (heig : ∀ i, ∀ x, ∑ y, M i x y * Om i y = Om i x)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (hdecay : ∀ i, ∀ f : Xs i → ℝ, ∃ C : ℝ, ∀ n : ℕ,
      |bandCov (M i) (Om i) n f f| ≤ C * r ^ n) :
    ∃ m : ℝ, 0 < m ∧ ∀ i,
      ‖projectedTransfer (opOf (M i)) (vacOf (Om i))‖ ≤ Real.exp (-m) := by
  refine volumeUniform_gap (fun i => opOf (M i)) (fun i => vacOf (Om i))
    (fun i => vacuumTransfer_opOf (M i) (Om i) (hM i) (hOm i) (heig i))
    hr0 hr1 ?_
  intro i v
  obtain ⟨C, hC⟩ := hdecay i (fun x => v x / Om i x)
  refine ⟨(∑ x, Om i x * Om i x) * C, fun n => ?_⟩
  rw [connCorr_eq_bandCov (M i) (Om i) (hOm i) v n]
  have hS : 0 < ∑ x, Om i x * Om i x := bandNorm_pos (Om i) (hOm i)
  rw [abs_mul, abs_of_pos hS, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hC n) hS.le

/-! ## §5  Non-vacuity: a two-state family with a nonzero fluctuation
sector at every rate

The witness kernel is `(1+r)/2` on the diagonal and `(1−r)/2` off it,
with constant boundary vector: symmetric, row sums one, and its band
covariance is EXACTLY `((f 0 − f 1)/2)² · rⁿ` — so the decay hypothesis
holds with equality, and the projected operator is nonzero whenever
`r ≠ 0`.  Nothing in §4 is satisfied only by a degenerate instance. -/

/-- The two-state witness kernel. -/
noncomputable def wKernel (r : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun x y => if x = y then (1 + r) / 2 else (1 - r) / 2

theorem wKernel_symm (r : ℝ) : ∀ x y, wKernel r x y = wKernel r y x := by
  intro x y
  unfold wKernel
  by_cases h : x = y
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (Ne.symm h)]

theorem wKernel_row (r : ℝ) :
    ∀ x : Fin 2, ∑ y, wKernel r x y * (1 : ℝ) = 1 := by
  intro x
  rw [Fin.sum_univ_two]
  fin_cases x <;> simp [wKernel] <;> ring

theorem wKernel_pow (r : ℝ) : ∀ n : ℕ, wKernel r ^ n = wKernel (r ^ n) := by
  intro n
  induction n with
  | zero =>
      rw [pow_zero, pow_zero]
      ext x y
      fin_cases x <;> fin_cases y <;>
        simp [wKernel, Matrix.one_apply] <;> norm_num
  | succ m ih =>
      rw [pow_succ, pow_succ, ih]
      ext x y
      fin_cases x <;> fin_cases y <;>
        simp [wKernel, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- The band covariance of the witness, in closed form: exact geometric
decay at rate `r`, with the variance-type constant `((f 0 − f 1)/2)²`. -/
theorem wKernel_bandCov (r : ℝ) (n : ℕ) (f : Fin 2 → ℝ) :
    bandCov (wKernel r) (fun _ => 1) n f f
      = ((f 0 - f 1) / 2) ^ 2 * r ^ n := by
  unfold bandCov
  rw [band_pair (wKernel r) (fun _ => 1) n f f, wKernel_pow r n]
  have h00 : wKernel (r ^ n) 0 0 = (1 + r ^ n) / 2 := if_pos rfl
  have h11 : wKernel (r ^ n) 1 1 = (1 + r ^ n) / 2 := if_pos rfl
  have h01 : wKernel (r ^ n) 0 1 = (1 - r ^ n) / 2 := if_neg (by decide)
  have h10 : wKernel (r ^ n) 1 0 = (1 - r ^ n) / 2 := if_neg (by decide)
  unfold bandE
  rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two,
    Fin.sum_univ_two, h00, h01, h10, h11]
  ring

/-- The witness discharges the decay hypothesis of §4, with equality. -/
theorem wKernel_bandDecay {r : ℝ} (hr0 : 0 ≤ r) (n : ℕ) (f : Fin 2 → ℝ) :
    |bandCov (wKernel r) (fun _ => 1) n f f|
      ≤ ((f 0 - f 1) / 2) ^ 2 * r ^ n := by
  rw [wKernel_bandCov]
  exact le_of_eq (abs_of_nonneg (mul_nonneg (sq_nonneg _) (pow_nonneg hr0 n)))

/-- The fluctuation sector of the witness is NOT zero: the projected
operator sends the sign vector to `r` times itself. -/
theorem wKernel_fluctuation_ne (r : ℝ) (hr : r ≠ 0) :
    projectedTransfer (opOf (wKernel r))
      (vacOf (fun _ : Fin 2 => (1 : ℝ))) ≠ 0 := by
  intro hzero
  set u : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![1, -1] with hu
  have hu0 : u 0 = 1 := rfl
  have hu1 : u 1 = -1 := rfl
  have hvacentry : ∀ x : Fin 2,
      vacOf (fun _ : Fin 2 => (1 : ℝ)) x = 1 / Real.sqrt 2 := by
    intro x
    have hx : vacOf (fun _ : Fin 2 => (1 : ℝ)) x
        = 1 / Real.sqrt (∑ y : Fin 2, (1 : ℝ) * 1) := rfl
    rw [hx, Fin.sum_univ_two]
    norm_num
  have hvac0 : ⟪vacOf (fun _ : Fin 2 => (1 : ℝ)), u⟫ = 0 := by
    rw [inner_eq_sum, Fin.sum_univ_two, hvacentry 0, hvacentry 1, hu0, hu1]
    ring
  have happ : projectedTransfer (opOf (wKernel r))
      (vacOf (fun _ : Fin 2 => (1 : ℝ))) u 0 = r := by
    rw [projectedTransfer_apply, hvac0, zero_smul]
    have hsub : (opOf (wKernel r) u
        - (0 : EuclideanSpace ℝ (Fin 2))) 0 = opOf (wKernel r) u 0 := by
      rw [sub_zero]
    rw [hsub, opOf_apply, Fin.sum_univ_two, hu0, hu1]
    have h00 : wKernel r 0 0 = (1 + r) / 2 := if_pos rfl
    have h01 : wKernel r 0 1 = (1 - r) / 2 := if_neg (by decide)
    rw [h00, h01]
    ring
  rw [hzero] at happ
  have hz : (0 : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)) u 0
      = 0 := rfl
  rw [hz] at happ
  exact hr happ.symm

/-- **Non-vacuity of the transport theorem**: at every rate `0 < r < 1`
the two-state witness family satisfies every hypothesis of
`abstract_uniform_gap` — so the theorem fires end-to-end and produces a
positive mass — while its projected operator is NOT the zero operator.
The class of §4 is inhabited and not degenerate. -/
theorem transport_witness {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    (∃ m : ℝ, 0 < m ∧
      ‖projectedTransfer (opOf (wKernel r))
          (vacOf (fun _ : Fin 2 => (1 : ℝ)))‖ ≤ Real.exp (-m))
    ∧ projectedTransfer (opOf (wKernel r))
        (vacOf (fun _ : Fin 2 => (1 : ℝ))) ≠ 0 := by
  constructor
  · obtain ⟨m, hm, hall⟩ := abstract_uniform_gap (ι := PUnit)
      (Xs := fun _ => Fin 2)
      (fun _ => wKernel r) (fun _ => fun _ => (1 : ℝ))
      (fun _ => wKernel_symm r) (fun _ => fun _ => one_pos)
      (fun _ => wKernel_row r) hr0 hr1
      (fun _ => fun f => ⟨((f 0 - f 1) / 2) ^ 2,
        fun n => wKernel_bandDecay hr0.le n f⟩)
    exact ⟨m, hm, hall PUnit.unit⟩
  · exact wKernel_fluctuation_ne r hr0.ne'

end Dobrushin

end YangMills.OS
