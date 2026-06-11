/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib
import YangMills.ClayCore.SchurMixedMomentVanishing

/-!
# Milestone F2-selection: the Z_N N-ality rule at the matrix-coefficient level

The centre-symmetry programme so far lives at the level of **characters** (traces):
`∫ (tr U)^a conj(tr U)^b = 0` for `N_c ∤ (a − b)` (`SchurMixedMomentVanishing.lean`).
But the objects the cluster expansion actually consumes — Wilson loops, the
Boltzmann weight `exp(−β Re tr U)` expanded in plaquette variables — are built from
the **entries** `U_{ij}` of the fundamental representation, not only from traces.

This file lifts the selection rule one layer, from characters to **matrix
coefficients**, *without* invoking Peter–Weyl (the F3 bottleneck of `HORIZON.md`):

  `∫ (∏_{s} U_{iₛjₛ}) · (∏_{t} conj U_{kₜlₜ}) dHaar = 0`   whenever  `N_c ∤ (n − m)`,

where `n` is the number of holomorphic factors `U_{ij}` and `m` the number of
antiholomorphic factors `conj U_{kl}`.  This is exactly the integrand of the
**Weingarten calculus** (`HORIZON.md §3.2`), and the selection rule is its leading
constraint: the Haar average of a monomial of "matrix-coefficient N-ality"
`n − m` vanishes unless that N-ality is trivial mod `N_c`.

## Why this is the right next rung

* It sits at the F2/F4 layer (matrix coefficients), strictly above the character
  layer: the trace statement is the special case where each product factor is the
  diagonal sum `∑_i U_{ii}`.
* It is **Peter–Weyl-free** — it follows from left-invariance of Haar under the
  single centre element `ω·I` (`scalarCenterElement`), exactly as the trace
  version does.
* It is the precise vanishing pattern that prunes the Weingarten sum, and the
  algebraic reason only N-ality-zero Wilson observables survive Haar averaging
  (the skeleton of the area law; `HORIZON.md §3.3`).

## Proof strategy

With `g = ω·I` and `M := the monomial`, the entry transformation
`(g·U)_{ij} = ω · U_{ij}` (entry-level `scalarCenterElement` action) gives, per
factor, a scalar `ω` on holomorphic factors and `ω̄` on antiholomorphic ones, so

  `M(g·U) = ω^n · ω̄^m · M(U)`,

hence `J = (ω^n ω̄^m) · J` by Haar invariance and `(1 − ω^n ω̄^m)·J = 0`.  The
primitivity `ω^n ω̄^m ≠ 1` for `N_c ∤ (n − m)` is the *already-proved*
`rootOfUnity_pow_mul_star_pow_ne_one` from `SchurMixedMomentVanishing.lean`.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no new axioms.

NOTE. Written to mirror the proven patterns of `SchurZeroMean.lean` /
`SchurMixedMomentVanishing.lean`; not yet run through `lake build` here.  The
`Finset.prod` bookkeeping in `fundMonomial_scalarCenter` and the structure-
projection `simp only` in `entry_scalarCenter_mul` are the residual compile risks
and must be `#print axioms`-checked before this is reported closed.
-/

namespace YangMills

open MeasureTheory Matrix Complex Real

noncomputable section

variable {N_c n m : ℕ}

/-! ## Entry-level action of the centre element -/

/-- `((ω·I)·U)_{a b} = ω · U_{a b}`.  The entry-level analogue of
`trace_scalarCenter_mul`. -/
theorem entry_scalarCenter_mul (N_c : ℕ) [NeZero N_c]
    (U : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) (a b : Fin N_c) :
    (scalarCenterElement N_c * U).val a b = rootOfUnity N_c * U.val a b := by
  show ((scalarCenterElement N_c).val * U.val) a b = _
  unfold scalarCenterElement
  simp only
  rw [Matrix.smul_mul, Matrix.one_mul, Matrix.smul_apply, smul_eq_mul]

/-- Continuity of a single matrix entry on SU(N_c). -/
theorem continuous_entry (N_c : ℕ) [NeZero N_c] (a b : Fin N_c) :
    Continuous
      (fun U : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ) => U.val a b) :=
  (continuous_apply b).comp ((continuous_apply a).comp continuous_subtype_val)

/-! ## The fundamental-coefficient monomial -/

/-- A monomial in the fundamental matrix coefficients: `n` holomorphic factors
`U_{iₛ jₛ}` and `m` antiholomorphic factors `conj U_{kₜ lₜ}`. -/
def fundMonomial (N_c n m : ℕ)
    (i j : Fin n → Fin N_c) (k l : Fin m → Fin N_c)
    (U : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) : ℂ :=
  (∏ s : Fin n, U.val (i s) (j s)) * (∏ t : Fin m, star (U.val (k t) (l t)))

/-- Under the centre element, the monomial scales by `ω^n · ω̄^m`. -/
theorem fundMonomial_scalarCenter (N_c n m : ℕ) [NeZero N_c]
    (i j : Fin n → Fin N_c) (k l : Fin m → Fin N_c)
    (U : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) :
    fundMonomial N_c n m i j k l (scalarCenterElement N_c * U) =
    ((rootOfUnity N_c) ^ n * (star (rootOfUnity N_c)) ^ m) *
      fundMonomial N_c n m i j k l U := by
  unfold fundMonomial
  have e1 : ∀ s : Fin n,
      (scalarCenterElement N_c * U).val (i s) (j s) =
        rootOfUnity N_c * U.val (i s) (j s) :=
    fun s => entry_scalarCenter_mul N_c U (i s) (j s)
  have e2 : ∀ t : Fin m,
      star ((scalarCenterElement N_c * U).val (k t) (l t)) =
        star (rootOfUnity N_c) * star (U.val (k t) (l t)) := by
    intro t; rw [entry_scalarCenter_mul N_c U (k t) (l t), star_mul']
  rw [Finset.prod_congr rfl (fun s _ => e1 s),
      Finset.prod_congr rfl (fun t _ => e2 t),
      Finset.prod_mul_distrib, Finset.prod_mul_distrib,
      Finset.prod_const, Finset.prod_const,
      Finset.card_univ, Finset.card_univ, Fintype.card_fin, Fintype.card_fin]
  ring

/-- The monomial is integrable against `sunHaarProb N_c` (continuous on a compact
group). -/
theorem fundMonomial_integrable (N_c n m : ℕ) [NeZero N_c]
    (i j : Fin n → Fin N_c) (k l : Fin m → Fin N_c) :
    Integrable (fundMonomial N_c n m i j k l) (sunHaarProb N_c) := by
  have hcont : Continuous (fundMonomial N_c n m i j k l) := by
    unfold fundMonomial
    refine Continuous.mul ?_ ?_
    · exact continuous_finset_prod _ (fun s _ => continuous_entry N_c (i s) (j s))
    · exact continuous_finset_prod _
        (fun t _ => continuous_star.comp (continuous_entry N_c (k t) (l t)))
  exact hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-! ## The matrix-coefficient N-ality selection rule -/

/-- **Main theorem — matrix-coefficient Z_N selection rule.**

`∫ (∏ U_{iₛjₛ}) · (∏ conj U_{kₜlₜ}) dHaar = 0` on SU(N_c) whenever
`N_c ∤ (n − m)`, where `n`/`m` are the numbers of holomorphic/antiholomorphic
factors. -/
theorem sunHaarProb_fundMonomial_integral_zero
    (N_c n m : ℕ) [NeZero N_c]
    (i j : Fin n → Fin N_c) (k l : Fin m → Fin N_c)
    (hdvd : ¬ (N_c : ℤ) ∣ ((n : ℤ) - (m : ℤ))) :
    ∫ U : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ),
      fundMonomial N_c n m i j k l U ∂(sunHaarProb N_c) = 0 := by
  set J : ℂ := ∫ U, fundMonomial N_c n m i j k l U ∂(sunHaarProb N_c) with hJ
  have hinv : J = ∫ U, fundMonomial N_c n m i j k l (scalarCenterElement N_c * U)
                      ∂(sunHaarProb N_c) := by
    rw [hJ]
    symm
    exact MeasureTheory.integral_mul_left_eq_self
      (fundMonomial N_c n m i j k l) (scalarCenterElement N_c)
  have heq : (fun U => fundMonomial N_c n m i j k l (scalarCenterElement N_c * U)) =
             (fun U => ((rootOfUnity N_c) ^ n * (star (rootOfUnity N_c)) ^ m) *
                fundMonomial N_c n m i j k l U) := by
    funext U; exact fundMonomial_scalarCenter N_c n m i j k l U
  have hmul : (∫ U, fundMonomial N_c n m i j k l (scalarCenterElement N_c * U)
                      ∂(sunHaarProb N_c)) =
               ((rootOfUnity N_c) ^ n * (star (rootOfUnity N_c)) ^ m) * J := by
    calc ∫ U, fundMonomial N_c n m i j k l (scalarCenterElement N_c * U)
              ∂(sunHaarProb N_c)
        = ∫ U, ((rootOfUnity N_c) ^ n * (star (rootOfUnity N_c)) ^ m) *
              fundMonomial N_c n m i j k l U ∂(sunHaarProb N_c) := by rw [heq]
      _ = ((rootOfUnity N_c) ^ n * (star (rootOfUnity N_c)) ^ m) *
              ∫ U, fundMonomial N_c n m i j k l U ∂(sunHaarProb N_c) :=
          MeasureTheory.integral_const_mul _ _
      _ = ((rootOfUnity N_c) ^ n * (star (rootOfUnity N_c)) ^ m) * J := by rw [← hJ]
  rw [hmul] at hinv
  have hfactor :
      (1 - (rootOfUnity N_c) ^ n * (star (rootOfUnity N_c)) ^ m) * J = 0 := by
    linear_combination hinv
  rcases mul_eq_zero.mp hfactor with h1 | h2
  · exfalso
    have hω : (rootOfUnity N_c) ^ n * (star (rootOfUnity N_c)) ^ m = 1 :=
      (sub_eq_zero.mp h1).symm
    exact rootOfUnity_pow_mul_star_pow_ne_one N_c n m hdvd hω
  · exact h2

/-! ## Faithfulness corollary: matrix-coefficient zero-mean -/

/-- `∫ U_{a b} dHaar = 0` on SU(N_c) for `N_c ≥ 2` — the single-entry (`n=1, m=0`)
case.  This is the matrix-coefficient analogue of `∫ tr U = 0` (F0) and lives one
layer below it: summing over `a = b` recovers F0. -/
theorem sunHaarProb_entry_integral_zero
    (N_c : ℕ) [NeZero N_c] (hN : 2 ≤ N_c) (a b : Fin N_c) :
    ∫ U : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ),
      U.val a b ∂(sunHaarProb N_c) = 0 := by
  have hdvd : ¬ (N_c : ℤ) ∣ ((1 : ℤ) - (0 : ℤ)) := by
    simp only [sub_zero]
    intro h
    have hle := Int.le_of_dvd (by norm_num) h
    have h2 : (2 : ℤ) ≤ (N_c : ℤ) := by exact_mod_cast hN
    omega
  have h := sunHaarProb_fundMonomial_integral_zero N_c 1 0
    (fun _ => a) (fun _ => b) (fun _ => a) (fun _ => a) hdvd
  simpa [fundMonomial, Fin.prod_univ_one] using h

/-- **Decorated-entry-product selection rule** (AL4.5, brick DB-1).
The `Finset`-indexed form of the `N`-ality selection rule: a product
of matrix entries `U_{aᵢbᵢ}` (positions with `dec i = true`) and
conjugated entries (positions with `dec i = false`) integrates to
zero against Haar unless `N_c` divides the holomorphic-minus-
antiholomorphic count.  This is exactly the shape of one per-edge
fiber factor of a Wilson-loop path term after the grouping
`prod_comp_eq_prod_fiber`; the area-law join (J) consumes this
interface and never touches the `Fin`-indexed `fundMonomial`. -/
theorem sunHaarProb_decoratedEntryProduct_integral_zero
    (N_c : ℕ) [NeZero N_c] {ι₀ : Type*} (s : Finset ι₀)
    (dec : ι₀ → Bool) (a b : ι₀ → Fin N_c)
    (hdvd : ¬ (N_c : ℤ) ∣
      (((s.filter (fun i => dec i)).card : ℤ)
        - ((s.filter (fun i => ¬ dec i)).card : ℤ))) :
    ∫ U : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ),
      ∏ i ∈ s, (if dec i then U.val (a i) (b i)
        else star (U.val (a i) (b i))) ∂(sunHaarProb N_c) = 0 := by
  set t₁ := s.filter (fun i => dec i) with ht₁
  set t₂ := s.filter (fun i => ¬ dec i) with ht₂
  have hsplit : ∀ U : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ),
      (∏ i ∈ s, (if dec i then U.val (a i) (b i)
        else star (U.val (a i) (b i))))
      = fundMonomial N_c t₁.card t₂.card
          (fun x => a ((t₁.equivFin.symm x) : ι₀))
          (fun x => b ((t₁.equivFin.symm x) : ι₀))
          (fun x => a ((t₂.equivFin.symm x) : ι₀))
          (fun x => b ((t₂.equivFin.symm x) : ι₀)) U := by
    intro U
    rw [← Finset.prod_filter_mul_prod_filter_not s (fun i => dec i)]
    unfold fundMonomial
    congr 1
    · have h1 : ∏ i ∈ t₁, (if dec i then U.val (a i) (b i)
          else star (U.val (a i) (b i)))
          = ∏ i ∈ t₁, U.val (a i) (b i) :=
        Finset.prod_congr rfl fun i hi =>
          if_pos (Finset.mem_filter.mp hi).2
      rw [h1, ← Finset.prod_coe_sort]
      exact Fintype.prod_equiv t₁.equivFin _ _ fun x => by simp
    · have h2 : ∏ i ∈ t₂, (if dec i then U.val (a i) (b i)
          else star (U.val (a i) (b i)))
          = ∏ i ∈ t₂, star (U.val (a i) (b i)) :=
        Finset.prod_congr rfl fun i hi =>
          if_neg (Finset.mem_filter.mp hi).2
      rw [h2, ← Finset.prod_coe_sort]
      exact Fintype.prod_equiv t₂.equivFin _ _ fun x => by simp
  have hfun : (fun U : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ) =>
      ∏ i ∈ s, (if dec i then U.val (a i) (b i)
        else star (U.val (a i) (b i))))
      = fun U => fundMonomial N_c t₁.card t₂.card
          (fun x => a ((t₁.equivFin.symm x) : ι₀))
          (fun x => b ((t₁.equivFin.symm x) : ι₀))
          (fun x => a ((t₂.equivFin.symm x) : ι₀))
          (fun x => b ((t₂.equivFin.symm x) : ι₀)) U :=
    funext hsplit
  rw [hfun]
  exact sunHaarProb_fundMonomial_integral_zero N_c t₁.card t₂.card
    _ _ _ _ hdvd

end

end YangMills
