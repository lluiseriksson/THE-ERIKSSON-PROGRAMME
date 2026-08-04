/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson
-/
import Mathlib
import YangMills.ClayCore.TracePathExpansion

/-!
# D-6 / B-1 — the finite band identity: matrix elements of the normalised
kernel are expectations of an explicit Perron-boundary band weight

Charter: `docs/DOBRUSHIN-D6-CHARTER.md`, Amendments 1-2.  Gates G18-G20
passed 60/60 in both modes before this file existed (ledger Addendum 594);
G18 measured this identity numerically to `1e-10`.

## What this module is, stated with Amendment 2's care

For a FINITE slice space `X`, a symmetric kernel `M` and a strictly
positive vector `Om` with `M Om = Om` (the NORMALISED eigen-relation —
`normalise_eig` shows how a raw Perron pair `(T, lam, Om)` produces it, so
`lam` is visible and not hidden), the band weight

    bandW n v  =  Om (v 0) · ∏ M (v k.castSucc) (v k.succ) · Om (v last)

on paths `v : Fin (n+1) → X` satisfies, EXACTLY and for every `n`:

* `bandZ`      — its total mass is `∑ Om²`, independent of `n`: the
  Perron-boundary normalisation is automatic;
* `band_pair`  — two-endpoint sums against `f, g` are the matrix elements
  `∑ᵢⱼ (f·Om)ᵢ (Mⁿ)ᵢⱼ (g·Om)ⱼ`;
* `band_covariance_eq` — the band COVARIANCE of `f(v 0)` and `g(v last)`
  is the matrix element of `Mⁿ` at the CENTRED dressed observables
  `(f − E f)·Om`, `(g − E g)·Om`, normalised by `∑ Om²`.

No limits, no extrapolation; the time orientation (`castSucc → succ`), the
boundary factors, the normalisation and the centring are all explicit in
the statements.

## What is deliberately NOT here (the charter's named failure modes)

* NO spectral positivity: nothing assumes `0 ≤ M` as a form.  Symmetry and
  the eigen-relation carry every proof; subdominant eigenvalues may be
  negative and nothing here notices.
* NO conflation of boundary dressings: this is the `Ω`-boundary form.  The
  raw `√w`-dressed strip identity that gate G18 measured is connected to
  this one through B-2's boundary-cost representation `f_v = v / Ω`, in a
  later module — silently identifying the two is the failure mode the
  charter names, and this module does not touch the physical kernel at all.
* NO Ising, NO Dobrushin: per Amendment 2 the bridge is abstract; the
  corollary that shows it inhabited comes at the end of D-6.
-/

namespace YangMills.OS

namespace Dobrushin

open Finset

variable {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]

/-! ## §1  The eigen-relation, with the eigenvalue visible -/

/-- Normalising a raw eigen-relation: `lam` enters here and nowhere else,
so it is visible rather than hidden in a convention. -/
theorem normalise_eig (T : Matrix X X ℝ) (Om : X → ℝ) (lam : ℝ)
    (hlam : lam ≠ 0)
    (heigT : ∀ x, ∑ y, T x y * Om y = lam * Om x) :
    ∀ x, ∑ y, ((1 / lam) • T) x y * Om y = Om x := by
  intro x
  have hentry : ∀ y : X, ((1 / lam) • T) x y * Om y
      = (1 / lam) * (T x y * Om y) := by
    intro y
    rw [Matrix.smul_apply, smul_eq_mul]
    ring
  rw [Finset.sum_congr rfl fun y _ => hentry y, ← Finset.mul_sum, heigT x]
  field_simp

/-! ## §2  Powers fix the eigenvector, on both sides -/

theorem pow_fix (M : Matrix X X ℝ) (Om : X → ℝ)
    (heig : ∀ x, ∑ y, M x y * Om y = Om x) :
    ∀ (n : ℕ) (x : X), ∑ y, (M ^ n) x y * Om y = Om x := by
  intro n
  induction n with
  | zero =>
      intro x
      have h0 : ∀ y : X, (M ^ 0) x y * Om y
          = (if x = y then (1 : ℝ) else 0) * Om y := fun y => by
        rw [pow_zero, Matrix.one_apply]
      have h1 : ∀ y : X, (if x = y then (1 : ℝ) else 0) * Om y
          = if x = y then Om y else 0 := by
        intro y
        by_cases h : x = y
        · rw [if_pos h, if_pos h, one_mul]
        · rw [if_neg h, if_neg h, zero_mul]
      rw [Finset.sum_congr rfl fun y _ => h0 y,
        Finset.sum_congr rfl fun y _ => h1 y,
        Finset.sum_ite_eq Finset.univ x Om, if_pos (Finset.mem_univ x)]
  | succ n ih =>
      intro x
      have hstep : ∀ y : X, (M ^ (n + 1)) x y * Om y
          = ∑ z, (M ^ n) x z * (M z y * Om y) := by
        intro y
        rw [pow_succ, Matrix.mul_apply, Finset.sum_mul]
        exact Finset.sum_congr rfl fun z _ => by ring
      rw [Finset.sum_congr rfl fun y _ => hstep y, Finset.sum_comm]
      have hinner : ∀ z : X, ∑ y, (M ^ n) x z * (M z y * Om y)
          = (M ^ n) x z * Om z := by
        intro z
        rw [← Finset.mul_sum, heig z]
      rw [Finset.sum_congr rfl fun z _ => hinner z]
      exact ih x

/-- Powers of a symmetric matrix are symmetric, through the transpose. -/
theorem pow_entry_symm (M : Matrix X X ℝ)
    (hM : ∀ x y, M x y = M y x) (n : ℕ) (x y : X) :
    (M ^ n) x y = (M ^ n) y x := by
  have hMt : M.transpose = M := by
    ext a b
    rw [Matrix.transpose_apply]
    exact hM b a
  have htp : (M ^ n).transpose = M ^ n := by
    rw [Matrix.transpose_pow, hMt]
  calc (M ^ n) x y = (M ^ n).transpose y x := by rw [Matrix.transpose_apply]
    _ = (M ^ n) y x := by rw [htp]

theorem pow_fix_left (M : Matrix X X ℝ) (Om : X → ℝ)
    (hM : ∀ x y, M x y = M y x)
    (heig : ∀ x, ∑ y, M x y * Om y = Om x) (n : ℕ) :
    ∀ y : X, ∑ x, Om x * (M ^ n) x y = Om y := by
  intro y
  have hsw : ∀ x : X, Om x * (M ^ n) x y = (M ^ n) y x * Om x := by
    intro x
    rw [pow_entry_symm M hM n x y]
    ring
  rw [Finset.sum_congr rfl fun x _ => hsw x]
  exact pow_fix M Om heig n y

/-! ## §3  The path expansion of a matrix-power pairing

The orientation is explicit: step `idx` traverses from `v idx.castSucc` to
`v idx.succ`.  The induction peels the FIRST step through `Fin.cons`, the
pattern of the tree's `TracePathExpansion`. -/

theorem pow_pairing (M : Matrix X X ℝ) :
    ∀ (n : ℕ) (u w : X → ℝ),
    ∑ i, ∑ j, u i * (M ^ n) i j * w j
      = ∑ v : Fin (n + 1) → X,
          u (v 0) * (∏ idx : Fin n, M (v idx.castSucc) (v idx.succ))
            * w (v (Fin.last n)) := by
  intro n
  induction n with
  | zero =>
      intro u w
      have hL : ∑ i, ∑ j, u i * (M ^ 0) i j * w j = ∑ i, u i * w i := by
        refine Finset.sum_congr rfl fun i _ => ?_
        have h1 : ∀ j : X, u i * (M ^ 0) i j * w j
            = if i = j then u i * w j else 0 := by
          intro j
          rw [pow_zero, Matrix.one_apply]
          by_cases h : i = j
          · rw [if_pos h, if_pos h, mul_one]
          · rw [if_neg h, if_neg h, mul_zero, zero_mul]
        rw [Finset.sum_congr rfl fun j _ => h1 j,
          Finset.sum_ite_eq Finset.univ i (fun j => u i * w j),
          if_pos (Finset.mem_univ i)]
      have hR : (∑ v : Fin 1 → X,
          u (v 0) * (∏ idx : Fin 0, M (v idx.castSucc) (v idx.succ))
            * w (v (Fin.last 0)))
          = ∑ a : X, u a * w a := by
        refine Fintype.sum_equiv (Equiv.funUnique (Fin 1) X) _ _ fun v => ?_
        rw [Finset.univ_eq_empty, Finset.prod_empty, mul_one]
        rfl
      rw [hL]
      exact hR.symm
  | succ n ih =>
      intro u w
      have hsplit : (∑ v : Fin (n + 1 + 1) → X,
          u (v 0) * (∏ idx : Fin (n + 1), M (v idx.castSucc) (v idx.succ))
            * w (v (Fin.last (n + 1))))
          = ∑ p : X × (Fin (n + 1) → X),
              u p.1 * (M p.1 (p.2 0)
                * ∏ idx : Fin n, M (p.2 idx.castSucc) (p.2 idx.succ))
                * w (p.2 (Fin.last n)) := by
        refine (Fintype.sum_equiv (Fin.consEquiv fun _ => X) _ _
          fun p => ?_).symm
        simp only [Fin.consEquiv_apply]
        have hv0 : Fin.cons (α := fun _ => X) p.1 p.2 0 = p.1 :=
          Fin.cons_zero _ _
        have hvlast : Fin.cons (α := fun _ => X) p.1 p.2
            (Fin.last (n + 1)) = p.2 (Fin.last n) := by
          rw [← Fin.succ_last, Fin.cons_succ]
        have hprod : (∏ idx : Fin (n + 1),
            M (Fin.cons (α := fun _ => X) p.1 p.2 idx.castSucc)
              (Fin.cons (α := fun _ => X) p.1 p.2 idx.succ))
            = M p.1 (p.2 0)
              * ∏ idx : Fin n, M (p.2 idx.castSucc) (p.2 idx.succ) := by
          rw [Fin.prod_univ_succ]
          congr 1
        rw [hv0, hvlast, hprod]
      have hper : ∀ a : X,
          (∑ y : Fin (n + 1) → X,
            u a * (M a (y 0)
              * ∏ idx : Fin n, M (y idx.castSucc) (y idx.succ))
              * w (y (Fin.last n)))
          = ∑ z, ∑ j, (u a * M a z) * (M ^ n) z j * w j := by
        intro a
        have hshape : ∀ y : Fin (n + 1) → X,
            u a * (M a (y 0)
              * ∏ idx : Fin n, M (y idx.castSucc) (y idx.succ))
              * w (y (Fin.last n))
            = (fun z => u a * M a z) (y 0)
                * (∏ idx : Fin n, M (y idx.castSucc) (y idx.succ))
                * w (y (Fin.last n)) := fun y => by ring
        rw [Finset.sum_congr rfl fun y _ => hshape y]
        exact (ih (fun z => u a * M a z) w).symm
      have hLHS : ∑ i, ∑ j, u i * (M ^ (n + 1)) i j * w j
          = ∑ i, ∑ z, ∑ j, (u i * M i z) * (M ^ n) z j * w j := by
        refine Finset.sum_congr rfl fun i _ => ?_
        have hexp : ∀ j : X, u i * (M ^ (n + 1)) i j * w j
            = ∑ z, (u i * M i z) * (M ^ n) z j * w j := by
          intro j
          rw [pow_succ', Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
          exact Finset.sum_congr rfl fun z _ => by ring
        rw [Finset.sum_congr rfl fun j _ => hexp j, Finset.sum_comm]
      rw [hLHS, hsplit, Fintype.sum_prod_type,
        Finset.sum_congr rfl fun a _ => hper a]

/-! ## §4  The band weight, its mass, and the pairing -/

/-- The Perron-boundary band weight of a path. -/
noncomputable def bandW (M : Matrix X X ℝ) (Om : X → ℝ) (n : ℕ)
    (v : Fin (n + 1) → X) : ℝ :=
  Om (v 0) * (∏ idx : Fin n, M (v idx.castSucc) (v idx.succ))
    * Om (v (Fin.last n))

/-- Two-endpoint sums against the band weight are matrix elements at the
dressed observables. -/
theorem band_pair (M : Matrix X X ℝ) (Om : X → ℝ) (n : ℕ) (f g : X → ℝ) :
    ∑ v : Fin (n + 1) → X,
      f (v 0) * g (v (Fin.last n)) * bandW M Om n v
      = ∑ i, ∑ j, (f i * Om i) * (M ^ n) i j * (g j * Om j) := by
  rw [pow_pairing M n (fun i => f i * Om i) (fun j => g j * Om j)]
  refine Finset.sum_congr rfl fun v _ => ?_
  unfold bandW
  ring

/-- **The mass of the band weight is `∑ Om²`, for every `n`**: the
Perron-boundary normalisation is exact and `n`-independent. -/
theorem bandZ (M : Matrix X X ℝ) (Om : X → ℝ)
    (heig : ∀ x, ∑ y, M x y * Om y = Om x) (n : ℕ) :
    ∑ v : Fin (n + 1) → X, bandW M Om n v = ∑ x, Om x * Om x := by
  have h0 : ∑ v : Fin (n + 1) → X, bandW M Om n v
      = ∑ v : Fin (n + 1) → X,
          (fun _ : X => (1 : ℝ)) (v 0)
            * (fun _ : X => (1 : ℝ)) (v (Fin.last n)) * bandW M Om n v :=
    Finset.sum_congr rfl fun v _ => by ring
  rw [h0, band_pair M Om n (fun _ : X => (1 : ℝ)) (fun _ : X => (1 : ℝ))]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : ∀ j : X, ((1 : ℝ) * Om i) * (M ^ n) i j * ((1 : ℝ) * Om j)
      = Om i * ((M ^ n) i j * Om j) := fun j => by ring
  rw [Finset.sum_congr rfl fun j _ => h1 j, ← Finset.mul_sum,
    pow_fix M Om heig n i]

/-! ## §5  Centring, and the covariance identity -/

/-- The band expectation of a slice observable. -/
noncomputable def bandE (Om : X → ℝ) (f : X → ℝ) : ℝ :=
  (∑ x, f x * Om x * Om x) / (∑ x, Om x * Om x)

theorem bandNorm_pos (Om : X → ℝ) (hOm : ∀ x, 0 < Om x) :
    0 < ∑ x, Om x * Om x :=
  Finset.sum_pos (fun x _ => mul_pos (hOm x) (hOm x)) Finset.univ_nonempty

/-- The centred dressed observable is orthogonal to the boundary vector:
the exact statement of "centring against `Ω`". -/
theorem centered_dressed_orth (Om : X → ℝ) (hOm : ∀ x, 0 < Om x)
    (f : X → ℝ) :
    ∑ x, ((f x - bandE Om f) * Om x) * Om x = 0 := by
  have hZ : (∑ x, Om x * Om x) ≠ 0 := (bandNorm_pos Om hOm).ne'
  have hexp : ∀ x : X, ((f x - bandE Om f) * Om x) * Om x
      = f x * Om x * Om x - bandE Om f * (Om x * Om x) := fun x => by ring
  rw [Finset.sum_congr rfl fun x _ => hexp x, Finset.sum_sub_distrib,
    ← Finset.mul_sum]
  unfold bandE
  rw [div_mul_cancel₀ _ hZ]
  exact sub_self _

/-- **B-1, the headline.**  The band covariance of `f` at time `0` and `g`
at time `n` equals the matrix element of `Mⁿ` at the CENTRED dressed
observables, normalised by `∑ Om²`.  Exact, finite, for every `n`. -/
theorem band_covariance_eq (M : Matrix X X ℝ) (Om : X → ℝ)
    (hM : ∀ x y, M x y = M y x)
    (heig : ∀ x, ∑ y, M x y * Om y = Om x)
    (hOm : ∀ x, 0 < Om x) (n : ℕ) (f g : X → ℝ) :
    (∑ v : Fin (n + 1) → X,
      f (v 0) * g (v (Fin.last n)) * bandW M Om n v)
        / (∑ x, Om x * Om x)
      - bandE Om f * bandE Om g
      = (∑ i, ∑ j, ((f i - bandE Om f) * Om i) * (M ^ n) i j
          * ((g j - bandE Om g) * Om j)) / (∑ x, Om x * Om x) := by
  have hZ : (∑ x, Om x * Om x) ≠ 0 := (bandNorm_pos Om hOm).ne'
  have hD : ∑ i, ∑ j, Om i * (M ^ n) i j * Om j = ∑ x, Om x * Om x := by
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 : ∀ j : X, Om i * (M ^ n) i j * Om j
        = Om i * ((M ^ n) i j * Om j) := fun j => by ring
    rw [Finset.sum_congr rfl fun j _ => h1 j, ← Finset.mul_sum,
      pow_fix M Om heig n i]
  have hB : ∑ i, ∑ j, Om i * (M ^ n) i j * (g j * Om j)
      = bandE Om g * ∑ x, Om x * Om x := by
    rw [Finset.sum_comm]
    have hj : ∀ j : X, ∑ i, Om i * (M ^ n) i j * (g j * Om j)
        = g j * Om j * Om j := by
      intro j
      rw [show (∑ i, Om i * (M ^ n) i j * (g j * Om j))
          = (∑ i, Om i * (M ^ n) i j) * (g j * Om j) from by
        rw [Finset.sum_mul]]
      rw [pow_fix_left M Om hM heig n j]
      ring
    rw [Finset.sum_congr rfl fun j _ => hj j]
    unfold bandE
    rw [div_mul_cancel₀ _ hZ]
  have hC : ∑ i, ∑ j, (f i * Om i) * (M ^ n) i j * Om j
      = bandE Om f * ∑ x, Om x * Om x := by
    have hi : ∀ i : X, ∑ j, (f i * Om i) * (M ^ n) i j * Om j
        = f i * Om i * Om i := by
      intro i
      have h1 : ∀ j : X, (f i * Om i) * (M ^ n) i j * Om j
          = (f i * Om i) * ((M ^ n) i j * Om j) := fun j => by ring
      rw [Finset.sum_congr rfl fun j _ => h1 j, ← Finset.mul_sum,
        pow_fix M Om heig n i]
    rw [Finset.sum_congr rfl fun i _ => hi i]
    unfold bandE
    rw [div_mul_cancel₀ _ hZ]
  have hconst : ∀ (c : ℝ) (u : X → X → ℝ),
      (∑ i, ∑ j, c * u i j) = c * ∑ i, ∑ j, u i j := by
    intro c u
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum]
  have hnum : (∑ i, ∑ j, ((f i - bandE Om f) * Om i) * (M ^ n) i j
      * ((g j - bandE Om g) * Om j))
      = (∑ i, ∑ j, (f i * Om i) * (M ^ n) i j * (g j * Om j))
        - bandE Om f * bandE Om g * ∑ x, Om x * Om x := by
    have hexp : ∀ i j : X,
        ((f i - bandE Om f) * Om i) * (M ^ n) i j
          * ((g j - bandE Om g) * Om j)
        = (f i * Om i) * (M ^ n) i j * (g j * Om j)
          - bandE Om f * (Om i * (M ^ n) i j * (g j * Om j))
          - bandE Om g * ((f i * Om i) * (M ^ n) i j * Om j)
          + bandE Om f * bandE Om g
              * (Om i * (M ^ n) i j * Om j) := fun i j => by ring
    rw [Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun j _ => hexp i j]
    have hin : ∀ i : X,
        (∑ j, ((f i * Om i) * (M ^ n) i j * (g j * Om j)
          - bandE Om f * (Om i * (M ^ n) i j * (g j * Om j))
          - bandE Om g * ((f i * Om i) * (M ^ n) i j * Om j)
          + bandE Om f * bandE Om g * (Om i * (M ^ n) i j * Om j)))
        = (∑ j, (f i * Om i) * (M ^ n) i j * (g j * Om j))
          - (∑ j, bandE Om f * (Om i * (M ^ n) i j * (g j * Om j)))
          - (∑ j, bandE Om g * ((f i * Om i) * (M ^ n) i j * Om j))
          + ∑ j, bandE Om f * bandE Om g
              * (Om i * (M ^ n) i j * Om j) := by
      intro i
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        Finset.sum_sub_distrib]
    rw [Finset.sum_congr rfl fun i _ => hin i]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_sub_distrib]
    rw [hconst (bandE Om f) (fun i j => Om i * (M ^ n) i j * (g j * Om j)),
      hconst (bandE Om g) (fun i j => (f i * Om i) * (M ^ n) i j * Om j),
      hconst (bandE Om f * bandE Om g)
        (fun i j => Om i * (M ^ n) i j * Om j)]
    rw [hB, hC, hD]
    ring
  rw [band_pair, hnum, sub_div, mul_div_cancel_right₀ _ hZ]

end Dobrushin

end YangMills.OS
