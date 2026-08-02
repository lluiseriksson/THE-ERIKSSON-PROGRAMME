/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson
-/
import Mathlib
import YangMills.OS.DobrushinComparison

/-!
# D-4a — the Gibbs instantiation: every hypothesis of the comparison
estimate, discharged from a positive weight

Charter lineage: `docs/DOBRUSHIN-D3-CHARTER.md`.  Gates: G12/G14 of
`scripts/judge_dobrushin_d4.py`, committed before this file (`2cda729f5`).

## What this module is for

`DobrushinComparison.lean` proves the comparison estimate for DATA — a weight
`μ`, a kernel `p`, a majorant `C` — under six hypotheses.  This module
CONSTRUCTS that data from a single input, a strictly positive weight `w` on a
finite product space, and PROVES the hypotheses:

* `gibbsMu w = w / Z` is a probability weight;
* the heat-bath kernel `heatBath w i η s = w(η^{i→s}) / ∑_t w(η^{i→t})` is
  nonnegative, normalised, and local;
* `μ` is invariant under every single-site conditioning — proved by the
  involution `(η, s) ↦ (η^{i→s}, η_i)` on `Ω × S`, under which the integrand
  of `E_μ[E_i F]` is carried to the integrand of `E_μ[F]`;
* the INTRINSIC Dobrushin matrix `dobCoeff w i k` — the supremum of the total
  variation moved at site `i` by changing the configuration at `k` — has zero
  diagonal (a THEOREM here, by locality, not a hypothesis) and dominates the
  influence BY CONSTRUCTION.

What survives as a hypothesis of the endpoints is exactly Dobrushin's
condition: row sums of the intrinsic matrix at most `α < 1` (plus, for the
distance form, the finite-range support of the intrinsic matrix).  Nothing
else is left for a user to discharge.

## What this module does NOT claim

No bound on `dobCoeff` is computed here for any concrete interaction; the
comparison with the `tanh|J|` envelope of `DobrushinCoefficient.lean` is
D-4b's, and the operator transport to `volumeUniform_gap` is untouched.
Dobrushin's theorem is classical; the claim is mechanisation.
-/

namespace YangMills.OS

namespace Dobrushin

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]

/-! ## §0  One more update fact, from this file's own primitives -/

theorem update_self_id (η : ι → S) (i : ι) :
    Function.update η i (η i) = η := by
  funext j
  by_cases hj : j = i
  · subst hj
    rw [update_self']
  · rw [update_other _ _ _ hj]

/-! ## §1  The measure of a positive weight -/

/-- The partition sum. -/
noncomputable def gibbsZ (w : (ι → S) → ℝ) : ℝ := ∑ η, w η

/-- The normalised Gibbs weight. -/
noncomputable def gibbsMu (w : (ι → S) → ℝ) : (ι → S) → ℝ :=
  fun η => w η / gibbsZ w

theorem gibbsZ_pos {w : (ι → S) → ℝ} (hw : ∀ η, 0 < w η) : 0 < gibbsZ w := by
  unfold gibbsZ
  exact Finset.sum_pos (fun η _ => hw η) Finset.univ_nonempty

theorem gibbsMu_nonneg {w : (ι → S) → ℝ} (hw : ∀ η, 0 < w η) :
    ∀ η, 0 ≤ gibbsMu w η := fun η =>
  le_of_lt (div_pos (hw η) (gibbsZ_pos hw))

theorem gibbsMu_sum_one {w : (ι → S) → ℝ} (hw : ∀ η, 0 < w η) :
    ∑ η, gibbsMu w η = 1 := by
  unfold gibbsMu
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt (gibbsZ_pos hw))

/-! ## §2  The heat-bath kernel -/

/-- The local partition sum at site `i`. -/
noncomputable def localZ (w : (ι → S) → ℝ) (i : ι) (η : ι → S) : ℝ :=
  ∑ s, w (Function.update η i s)

theorem localZ_pos {w : (ι → S) → ℝ} (hw : ∀ η, 0 < w η) (i : ι) (η : ι → S) :
    0 < localZ w i η := by
  unfold localZ
  exact Finset.sum_pos (fun s _ => hw _) Finset.univ_nonempty

/-- Moving the coordinate `i` does not move the local partition sum at `i`. -/
theorem localZ_update_self (w : (ι → S) → ℝ) (i : ι) (η : ι → S) (s : S) :
    localZ w i (Function.update η i s) = localZ w i η := by
  unfold localZ
  exact Finset.sum_congr rfl fun t _ => by rw [update_update]

/-- The heat-bath kernel of the weight. -/
noncomputable def heatBath (w : (ι → S) → ℝ) : ι → (ι → S) → S → ℝ :=
  fun i η s => w (Function.update η i s) / localZ w i η

theorem heatBath_nonneg {w : (ι → S) → ℝ} (hw : ∀ η, 0 < w η) :
    ∀ (i : ι) (η : ι → S) (s : S), 0 ≤ heatBath w i η s := fun i η s =>
  le_of_lt (div_pos (hw _) (localZ_pos hw i η))

theorem heatBath_sum_one {w : (ι → S) → ℝ} (hw : ∀ η, 0 < w η) :
    ∀ (i : ι) (η : ι → S), ∑ s, heatBath w i η s = 1 := by
  intro i η
  unfold heatBath
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt (localZ_pos hw i η))

/-- Locality: the kernel at `i` does not see the value at `i`. -/
theorem heatBath_local (w : (ι → S) → ℝ) : KernelLocal (heatBath w) := by
  intro i η η' hagree
  funext s
  unfold heatBath localZ
  have hupd : ∀ t : S, Function.update η i t = Function.update η' i t := by
    intro t
    funext j
    by_cases hj : j = i
    · subst hj
      rw [update_self', update_self']
    · rw [update_other _ _ _ hj, update_other _ _ _ hj]
      exact hagree j hj
  rw [hupd s]
  congr 1
  exact Finset.sum_congr rfl fun t _ => by rw [hupd t]

/-! ## §3  Invariance, by an involution

The integrand of `E_μ[E_i F]` over `Ω × S` is carried to the integrand of
`E_μ[F]` by the swap `(η, s) ↦ (η^{i→s}, η_i)`, which is its own inverse.
This is the only place positivity of `w` is spent on anything beyond
nonnegativity: the two local partition sums that appear are cancelled against
themselves. -/

/-- The swap at site `i`. -/
def siteSwap (i : ι) : ((ι → S) × S) → ((ι → S) × S) :=
  fun q => (Function.update q.1 i q.2, q.1 i)

theorem siteSwap_involutive (i : ι) :
    Function.Involutive (siteSwap (S := S) i) := by
  intro q
  unfold siteSwap
  refine Prod.ext ?_ ?_
  · show Function.update (Function.update q.1 i q.2) i (q.1 i) = q.1
    rw [update_update, update_self_id]
  · show (Function.update q.1 i q.2) i = q.2
    rw [update_self']

/-- **Invariance.**  The Gibbs weight of `w` is invariant under conditioning
at every site with the heat-bath kernel of `w`. -/
theorem expect_heatBath {w : (ι → S) → ℝ} (hw : ∀ η, 0 < w η)
    (i : ι) (F : (ι → S) → ℝ) :
    expect (gibbsMu w) (condExp (heatBath w) i F) = expect (gibbsMu w) F := by
  unfold expect condExp
  -- both sides as sums over the product type
  have hL : ∑ η, gibbsMu w η * ∑ s, heatBath w i η s * F (Function.update η i s)
      = ∑ q : (ι → S) × S,
          gibbsMu w q.1 * (heatBath w i q.1 q.2 * F (Function.update q.1 i q.2)) := by
    rw [Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun η _ => by rw [Finset.mul_sum]
  rw [hL]
  -- reindex by the involution
  have hswap : ∑ q : (ι → S) × S,
        gibbsMu w q.1 * (heatBath w i q.1 q.2 * F (Function.update q.1 i q.2))
      = ∑ q : (ι → S) × S,
          gibbsMu w (siteSwap i q).1
            * (heatBath w i (siteSwap i q).1 (siteSwap i q).2
              * F (Function.update (siteSwap i q).1 i (siteSwap i q).2)) := by
    exact (Equiv.sum_comp ((siteSwap_involutive (S := S) i).toPerm)
      (fun q : (ι → S) × S => gibbsMu w q.1
        * (heatBath w i q.1 q.2 * F (Function.update q.1 i q.2)))).symm
  rw [hswap]
  -- evaluate the reindexed integrand
  have hterm : ∀ q : (ι → S) × S,
      gibbsMu w (siteSwap i q).1
          * (heatBath w i (siteSwap i q).1 (siteSwap i q).2
            * F (Function.update (siteSwap i q).1 i (siteSwap i q).2))
        = gibbsMu w (Function.update q.1 i q.2)
            * (w q.1 / localZ w i q.1 * F q.1) := by
    intro q
    unfold siteSwap
    have h1 : Function.update (Function.update q.1 i q.2) i (q.1 i) = q.1 := by
      rw [update_update, update_self_id]
    have h2 : localZ w i (Function.update q.1 i q.2) = localZ w i q.1 :=
      localZ_update_self w i q.1 q.2
    show gibbsMu w (Function.update q.1 i q.2)
        * (heatBath w i (Function.update q.1 i q.2) (q.1 i)
          * F (Function.update (Function.update q.1 i q.2) i (q.1 i)))
      = gibbsMu w (Function.update q.1 i q.2) * (w q.1 / localZ w i q.1 * F q.1)
    unfold heatBath
    rw [h1, h2]
  rw [Finset.sum_congr rfl fun q _ => hterm q]
  -- regroup: the s-sum reconstitutes the local partition sum, which cancels
  rw [Fintype.sum_prod_type]
  have hη : ∀ η : ι → S,
      ∑ s, gibbsMu w (Function.update η i s) * (w η / localZ w i η * F η)
        = gibbsMu w η * F η := by
    intro η
    have hfold : ∑ s, gibbsMu w (Function.update η i s)
        = localZ w i η / gibbsZ w := by
      unfold gibbsMu localZ
      rw [← Finset.sum_div]
    rw [← Finset.sum_mul, hfold]
    have hlz : localZ w i η ≠ 0 := ne_of_gt (localZ_pos hw i η)
    have hZ : gibbsZ w ≠ 0 := ne_of_gt (gibbsZ_pos hw)
    unfold gibbsMu
    field_simp
    ring
  rw [Finset.sum_congr rfl fun η _ => hη η]

/-! ## §4  The intrinsic Dobrushin matrix

Not a majorant chosen from outside: the supremum itself, over the finite set
of single-site discrepancies.  The diagonal vanishes as a THEOREM (locality),
and domination holds by `le_sup'`. -/

/-- The intrinsic Dobrushin coefficient: the largest total variation moved at
site `i` by changing the configuration at site `k`. -/
noncomputable def dobCoeff (w : (ι → S) → ℝ) (i k : ι) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun q : (ι → S) × S =>
      TV (heatBath w i q.1) (heatBath w i (Function.update q.1 k q.2)))

theorem dobCoeff_nonneg (w : (ι → S) → ℝ) (i k : ι) : 0 ≤ dobCoeff w i k := by
  obtain ⟨η⟩ : Nonempty (ι → S) := inferInstance
  obtain ⟨s⟩ := ‹Nonempty S›
  exact le_trans (TV_nonneg _ _)
    (Finset.le_sup'
      (fun q : (ι → S) × S =>
        TV (heatBath w i q.1) (heatBath w i (Function.update q.1 k q.2)))
      (Finset.mem_univ (⟨η, s⟩ : (ι → S) × S)))

/-- **The zero diagonal is a theorem here**, resting on locality alone: moving
the coordinate `i` does not move the conditional at `i`. -/
theorem dobCoeff_diag (w : (ι → S) → ℝ) (i : ι) : dobCoeff w i i = 0 := by
  refine le_antisymm ?_ (dobCoeff_nonneg w i i)
  refine Finset.sup'_le _ _ fun q _ => ?_
  have hloc : heatBath w i (Function.update q.1 i q.2) = heatBath w i q.1 := by
    refine heatBath_local w i _ _ fun j hj => ?_
    rw [update_other _ _ _ hj]
  rw [hloc]
  exact le_of_eq (TV_self _)

/-- **Domination by construction**: the intrinsic coefficient bounds the
influence of `k` on the conditional at `i`, for every pair agreeing off `k`. -/
theorem dobCoeff_dominates (w : (ι → S) → ℝ) (i k : ι) :
    ∀ η η' : ι → S, (∀ j, j ≠ k → η j = η' j) →
      TV (heatBath w i η) (heatBath w i η') ≤ dobCoeff w i k := by
  intro η η' hagree
  have hη' : η' = Function.update η k (η' k) := by
    funext j
    by_cases hj : j = k
    · subst hj
      rw [update_self']
    · rw [update_other _ _ _ hj]
      exact (hagree j hj).symm
  rw [hη']
  exact Finset.le_sup'
    (fun q : (ι → S) × S =>
      TV (heatBath w i q.1) (heatBath w i (Function.update q.1 k q.2)))
    (Finset.mem_univ (⟨η, η' k⟩ : (ι → S) × S))

/-- The intrinsic matrix, as a matrix. -/
noncomputable def dobMatrixOf (w : (ι → S) → ℝ) : Matrix ι ι ℝ :=
  fun i k => dobCoeff w i k

/-! ## §5  The instantiated endpoints

The single surviving hypothesis is Dobrushin's condition on the intrinsic
matrix (plus, for the distance forms, its finite range). -/

/-- **D-4a, series form.**  For a strictly positive weight whose intrinsic
Dobrushin matrix has row sums at most `α < 1`, connected correlations of the
Gibbs weight obey the comparison estimate.  Every kernel-side hypothesis is
discharged by construction. -/
theorem gibbs_covar_le_resolvent {w : (ι → S) → ℝ} (hw : ∀ η, 0 < w η)
    {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hrow : ∀ i, ∑ k, dobCoeff w i k ≤ α)
    (f g : (ι → S) → ℝ) :
    |covar (gibbsMu w) f g|
      ≤ (∑ i, ∑ j, deltaAt i f * (∑' n : ℕ, ((dobMatrixOf w) ^ n) i j)
          * deltaAt j g) / 4 :=
  covar_le_resolvent_tsum
    (gibbsMu_nonneg hw) (gibbsMu_sum_one hw)
    (heatBath_nonneg hw) (heatBath_sum_one hw) (heatBath_local w)
    (fun i F => expect_heatBath hw i F)
    (dobCoeff_diag w)
    (fun i k _ η η' hagree => dobCoeff_dominates w i k η η' hagree)
    hα0 hα1 hrow f g

/-- **D-4a, distance form**: when the intrinsic matrix is supported at range
one for a distance `d`, correlations decay exponentially in `d`, with rate and
prefactor read off `α` alone. -/
theorem gibbs_covar_exp_decay {w : (ι → S) → ℝ} (hw : ∀ η, 0 < w η)
    {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hrow : ∀ i, ∑ k, dobCoeff w i k ≤ α)
    (d : ι → ι → ℕ) (hself : ∀ i, d i i = 0)
    (htri : ∀ i j k, d i k ≤ d i j + d j k)
    (hsupp : ∀ i j, 1 < d i j → dobCoeff w i j = 0)
    (f g : (ι → S) → ℝ) :
    |covar (gibbsMu w) f g|
      ≤ (∑ i, ∑ j, deltaAt i f * (α ^ (d i j) / (1 - α)) * deltaAt j g) / 4 :=
  covar_exp_decay
    (gibbsMu_nonneg hw) (gibbsMu_sum_one hw)
    (heatBath_nonneg hw) (heatBath_sum_one hw) (heatBath_local w)
    (fun i F => expect_heatBath hw i F)
    (dobCoeff_diag w)
    (fun i k _ η η' hagree => dobCoeff_dominates w i k η η' hagree)
    hα0 hα1 hrow d hself htri hsupp f g

/-- **D-4a, two-point form**: for single-site observables, exponential decay
of the connected correlation of the Gibbs weight in the distance between the
sites, uniform in the volume. -/
theorem gibbs_covar_two_point {w : (ι → S) → ℝ} (hw : ∀ η, 0 < w η)
    {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hrow : ∀ i, ∑ k, dobCoeff w i k ≤ α)
    (d : ι → ι → ℕ) (hself : ∀ i, d i i = 0)
    (htri : ∀ i j k, d i k ≤ d i j + d j k)
    (hsupp : ∀ i j, 1 < d i j → dobCoeff w i j = 0)
    (i₀ j₀ : ι) (f g : (ι → S) → ℝ)
    (hf : ∀ k, k ≠ i₀ → deltaAt k f = 0)
    (hg : ∀ k, k ≠ j₀ → deltaAt k g = 0) :
    |covar (gibbsMu w) f g|
      ≤ deltaAt i₀ f * (α ^ (d i₀ j₀) / (1 - α)) * deltaAt j₀ g / 4 :=
  covar_two_point
    (gibbsMu_nonneg hw) (gibbsMu_sum_one hw)
    (heatBath_nonneg hw) (heatBath_sum_one hw) (heatBath_local w)
    (fun i F => expect_heatBath hw i F)
    (dobCoeff_diag w)
    (fun i k _ η η' hagree => dobCoeff_dominates w i k η η' hagree)
    hα0 hα1 hrow d hself htri hsupp i₀ j₀ f g hf hg

/-! ## §6  Non-vacuity

The uniform weight on one site with two states: every hypothesis of
`gibbs_covar_two_point` holds by computation, its Gibbs weight IS the witness
weight of the comparison module, and on the indicator observable the
conclusion is the attained quarter.  So the instantiated hypotheses are
jointly satisfiable and the instantiated bound is still the sharp one. -/

namespace GibbsWitness

/-- The uniform weight. -/
noncomputable def wU : (Fin 1 → Fin 2) → ℝ := fun _ => 1

theorem wU_pos : ∀ η, 0 < wU η := fun _ => one_pos

/-- The Gibbs weight of the uniform weight is the witness weight `muW`. -/
theorem gibbsMu_wU : gibbsMu wU = Witness.muW := by
  funext η
  unfold gibbsMu gibbsZ wU Witness.muW
  rw [Witness.sum_omega (fun _ => (1 : ℝ)), Fin.sum_univ_two]
  norm_num

/-- The intrinsic matrix of the uniform weight vanishes. -/
theorem dobCoeff_wU (i k : Fin 1) : dobCoeff wU i k = 0 := by
  refine le_antisymm ?_ (dobCoeff_nonneg wU i k)
  refine Finset.sup'_le _ _ fun q _ => ?_
  have h : heatBath wU i (Function.update q.1 k q.2) = heatBath wU i q.1 := by
    refine heatBath_local wU i _ _ fun j hj => ?_
    exact absurd (Subsingleton.elim j i) hj
  rw [h]
  exact le_of_eq (TV_self _)

/-- **The instantiated witness.**  The hypotheses of `gibbs_covar_two_point`
hold for the uniform weight, and on the indicator the conclusion is an
equality at the quarter. -/
theorem witness_attained :
    |covar (gibbsMu wU) Witness.fW Witness.fW|
      = deltaAt 0 Witness.fW
          * ((0 : ℝ) ^ (0 : ℕ) / (1 - 0)) * deltaAt 0 Witness.fW / 4 := by
  rw [gibbsMu_wU]
  exact Witness.witness_attained

theorem witness_bound_holds :
    |covar (gibbsMu wU) Witness.fW Witness.fW|
      ≤ deltaAt 0 Witness.fW
          * ((0 : ℝ) ^ (0 : ℕ) / (1 - 0)) * deltaAt 0 Witness.fW / 4 :=
  gibbs_covar_two_point wU_pos (le_refl 0) (by norm_num)
    (fun i => le_of_eq (by rw [Fin.sum_univ_one, dobCoeff_wU]))
    (fun _ _ => 0) (fun _ => rfl) (fun _ _ _ => Nat.zero_le _)
    (fun _ _ hij => absurd hij (Nat.not_lt_zero 1))
    0 0 Witness.fW Witness.fW
    (fun k hk => absurd (Subsingleton.elim k 0) hk)
    (fun k hk => absurd (Subsingleton.elim k 0) hk)

end GibbsWitness

end Dobrushin

end YangMills.OS
