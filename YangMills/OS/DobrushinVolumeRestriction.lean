/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson
-/
import YangMills.OS.DobrushinIsingComparison

/-!
# D-7 — exact identification of a cut Hamiltonian with its active volume

The comparison theorem lives on one common finite chart.  This file proves
that cutting all bonds outside a predicate `A` really produces the Gibbs
measure on the active subtype: the inactive spins are uniform spectators and
their finite multiplicity cancels between the numerator and partition
function.  This is an exact finite-sum identity, not a limiting hypothesis.
-/

namespace YangMills.OS

namespace Dobrushin

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]

/-- Restrict a configuration to the active subtype. -/
def restrictConfigTo (A : ι → Prop) (η : ι → S) : {i : ι // A i} → S :=
  fun i => η i.1

/-- Split a finite configuration into its active and inactive coordinates. -/
noncomputable def configSplitEquiv (A : ι → Prop) :
    (ι → S) ≃ (({i : ι // A i} → S) × ({i : ι // ¬ A i} → S)) := by
  classical
  exact
    { toFun := fun η =>
        (fun i => η i.1, fun i => η i.1)
      invFun := fun x i =>
        if hi : A i then x.1 ⟨i, hi⟩ else x.2 ⟨i, hi⟩
      left_inv := by
        intro η
        funext i
        by_cases hi : A i <;> simp [hi]
      right_inv := by
        intro x
        apply Prod.ext
        · funext i
          simp [i.2]
        · funext i
          simp [i.2] }

/-- The coupling matrix seen by the active subtype. -/
noncomputable def activeCoupling (J : ι → ι → ℝ) (A : ι → Prop) :
    {i : ι // A i} → {i : ι // A i} → ℝ :=
  fun i j => J i.1 j.1

/-- Cutting all exterior bonds leaves exactly the active Ising weight after
restriction of the configuration. -/
theorem isingWeight_restrictCoupling
    (J : ι → ι → ℝ) (A : ι → Prop) [DecidablePred A]
    (η : ι → Fin 2) :
    isingWeight (restrictCoupling J A) η =
      isingWeight (activeCoupling J A) (restrictConfigTo A η) := by
  classical
  have hfilter :
      ∑ a, ∑ b, restrictCoupling J A a b * spin (η a) * spin (η b)
        = ∑ a ∈ Finset.univ.filter A,
            ∑ b ∈ Finset.univ.filter A, J a b * spin (η a) * spin (η b) := by
    calc
      ∑ a, ∑ b, restrictCoupling J A a b * spin (η a) * spin (η b)
          = ∑ a, if A a then
              (∑ b, if A b then J a b * spin (η a) * spin (η b) else 0)
            else 0 := by
              exact Finset.sum_congr rfl fun a _ => by
                by_cases ha : A a
                · simp only [if_pos ha]
                  exact Finset.sum_congr rfl fun b _ => by
                    by_cases hb : A b <;>
                      simp [restrictCoupling, ha, hb]
                · simp [restrictCoupling, ha]
      _ = ∑ a ∈ Finset.univ.filter A,
            ∑ b ∈ Finset.univ.filter A, J a b * spin (η a) * spin (η b) := by
          simp only [Finset.sum_filter]
  have hsubtype :
      ∑ a ∈ Finset.univ.filter A,
          ∑ b ∈ Finset.univ.filter A, J a b * spin (η a) * spin (η b)
        = ∑ a : {i : ι // A i}, ∑ b : {i : ι // A i},
            J a.1 b.1 * spin (η a.1) * spin (η b.1) := by
    rw [Finset.sum_subtype (p := A) (Finset.univ.filter A) (by simp)]
    exact Finset.sum_congr rfl fun a _ => by
      rw [Finset.sum_subtype (p := A) (Finset.univ.filter A) (by simp)]
  unfold isingWeight
  rw [hfilter, hsubtype]
  rfl

private theorem expect_gibbs_eq_ratio
    {κ T : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype T] [DecidableEq T] [Nonempty T]
    (w : (κ → T) → ℝ) (f : (κ → T) → ℝ) :
    expect (gibbsMu w) f = (∑ η, w η * f η) / gibbsZ w := by
  unfold expect gibbsMu
  calc
    ∑ η, w η / gibbsZ w * f η = ∑ η, (w η * f η) / gibbsZ w := by
      exact Finset.sum_congr rfl fun η _ => by ring
    _ = (∑ η, w η * f η) / gibbsZ w := by
      rw [Finset.sum_div]

/-- **Exact cross-volume identification.**  For every observable on the active
coordinates, its expectation in the cut common-chart Hamiltonian equals its
expectation in the genuine active-volume Gibbs measure. -/
theorem expect_restrictCoupling_eq_active
    (J : ι → ι → ℝ) (A : ι → Prop) [DecidablePred A]
    [Nonempty {i : ι // A i}]
    (f : ({i : ι // A i} → Fin 2) → ℝ) :
    expect (gibbsMu (isingWeight (restrictCoupling J A)))
        (fun η => f (restrictConfigTo A η)) =
      expect (gibbsMu (isingWeight (activeCoupling J A))) f := by
  classical
  let ActiveConfig := {i : ι // A i} → Fin 2
  let InactiveConfig := {i : ι // ¬ A i} → Fin 2
  let wA : ActiveConfig → ℝ := isingWeight (activeCoupling J A)
  let wR : (ι → Fin 2) → ℝ := isingWeight (restrictCoupling J A)
  let c : ℝ := Fintype.card InactiveConfig
  letI : Nonempty InactiveConfig := ⟨fun _ => 0⟩
  have hweight : ∀ η : ι → Fin 2,
      wR η = wA (restrictConfigTo A η) := by
    intro η
    exact isingWeight_restrictCoupling J A η
  have hsplit : ∀ η : ι → Fin 2,
      (configSplitEquiv (S := Fin 2) A η).1 = restrictConfigTo A η :=
    fun _ => rfl
  have hZ : gibbsZ wR = c * gibbsZ wA := by
    unfold gibbsZ
    calc
      ∑ η, wR η = ∑ η, wA (configSplitEquiv (S := Fin 2) A η).1 := by
        exact Finset.sum_congr rfl fun η _ => by rw [hweight η, hsplit η]
      _ = ∑ x : ActiveConfig × InactiveConfig, wA x.1 :=
        (configSplitEquiv (S := Fin 2) A).sum_comp (fun x => wA x.1)
      _ = c * ∑ η, wA η := by
        rw [Fintype.sum_prod_type]
        simp only [Finset.sum_const, nsmul_eq_mul]
        change (∑ x, c * wA x) = c * ∑ x, wA x
        rw [Finset.mul_sum]
      _ = c * gibbsZ wA := rfl
  have hnum :
      (∑ η : ι → Fin 2, wR η * f (restrictConfigTo A η))
        = c * ∑ ξ : ActiveConfig, wA ξ * f ξ := by
    calc
      ∑ η : ι → Fin 2, wR η * f (restrictConfigTo A η)
          = ∑ η : ι → Fin 2,
              (wA (configSplitEquiv (S := Fin 2) A η).1
                * f (configSplitEquiv (S := Fin 2) A η).1) := by
              exact Finset.sum_congr rfl fun η _ => by
                rw [hweight η, hsplit η]
      _ = ∑ x : ActiveConfig × InactiveConfig, wA x.1 * f x.1 :=
        (configSplitEquiv (S := Fin 2) A).sum_comp
          (fun x => wA x.1 * f x.1)
      _ = c * ∑ ξ : ActiveConfig, wA ξ * f ξ := by
        rw [Fintype.sum_prod_type]
        simp only [Finset.sum_const, nsmul_eq_mul]
        change (∑ x, c * (wA x * f x)) = c * ∑ x, wA x * f x
        rw [Finset.mul_sum]
  have hc : c ≠ 0 := by
    have hcpos : 0 < Fintype.card InactiveConfig := Fintype.card_pos
    dsimp [c]
    exact_mod_cast (ne_of_gt hcpos)
  have hZA : gibbsZ wA ≠ 0 :=
    ne_of_gt (gibbsZ_pos (fun η => isingWeight_pos (activeCoupling J A) η))
  change expect (gibbsMu wR) (fun η => f (restrictConfigTo A η)) =
    expect (gibbsMu wA) f
  rw [expect_gibbs_eq_ratio, expect_gibbs_eq_ratio, hnum, hZ]
  field_simp [hc, hZA]
  rfl

/-- **D-7 two-volume theorem.**  The outer Gibbs expectation is compared to
the genuine Gibbs expectation on an active subvolume.  The only geometric
input says that every row changed by cutting the outer Hamiltonian is at
distance at least `R` from every coordinate on which the lifted observable
depends. -/
theorem ising_active_volume_comparison
    (J : ι → ι → ℝ)
    (hJdiag : ∀ a, J a a = 0) (hJsim : ∀ a b, J a b = J b a)
    {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hrow : ∀ i, ∑ k, Real.tanh |J i k| ≤ α)
    (d : ι → ι → ℕ) (hself : ∀ i, d i i = 0)
    (htri : ∀ i j k, d i k ≤ d i j + d j k)
    (hJsupp : ∀ i j, 1 < d i j → J i j = 0)
    (A : ι → Prop) [DecidablePred A] [Nonempty {i : ι // A i}]
    (g : ({i : ι // A i} → Fin 2) → ℝ) (R : ℕ)
    (hfar : ∀ i j,
      (∃ k, J i k ≠ restrictCoupling J A i k) →
      deltaAt j (fun η => g (restrictConfigTo A η)) ≠ 0 →
      R ≤ d j i) :
    |expect (gibbsMu (isingWeight J))
          (fun η => g (restrictConfigTo A η))
        - expect (gibbsMu (isingWeight (activeCoupling J A))) g|
      ≤ (α ^ R / (1 - α)) *
          ∑ j, deltaAt j (fun η => g (restrictConfigTo A η)) := by
  have h := ising_restriction_comparison J hJdiag hJsim hα0 hα1 hrow
    d hself htri hJsupp A (fun η => g (restrictConfigTo A η)) R hfar
  rw [expect_restrictCoupling_eq_active J A g] at h
  exact h

end Dobrushin

end YangMills.OS
