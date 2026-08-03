/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson
-/
import Mathlib
import YangMills.OS.DobrushinLattice
import YangMills.OS.DobrushinTransport
import YangMills.OS.DobrushinTilt
import YangMills.OS.Z2Identification

/-!
# D-6 corollary, stage B — the currying discharge, and the public
Dobrushin–Ising corollary

Design: `docs/DOBRUSHIN-D6-B2-DESIGN.md` §§7-9.  This is the single weld
the paper's Section on the transport declares open: the identification of
the free strip sums of the tilt layer with the rectangle covariances of
the family theorem, and the resulting instantiation of the abstract
transport theorem for the coupled family.  Gate G23 measured the
assembled bound before any of this Lean existed; nothing here is an
estimate.

## The chain

* `adj_pairing` — the one-dimensional pairing: an ordered double sum over
  nearest-neighbour pairs of `Fin (m+1)` is twice the sum over steps.
* `rectJ_energy_split` — the rectangle coupling's ordered double energy,
  halved (exactly the half the development's Ising weight carries to
  compensate ordered double counting), is the single-counted temporal
  energy at `β` plus the single-counted spatial energy at `γ`.
* `curry_weight` — the free strip Gibbs weight of the spatial system IS
  the rectangle Ising weight under currying.  Exact; no measure is
  approximated by another.
* `freeCov_eq_rect_covar` — hence the tilt layer's free covariance IS the
  rectangle covariance of end-slice observables.
* `row_deltaAt_zero`, `row_deltaAt_le` — end-slice observables oscillate
  only on their slice, and their site oscillations are the slice ones.
* `rect_feed` — the family theorem's decay, fed through the above: every
  site pair the covariance sees is at rectangle distance at least the
  horizon, so `α^{d_□}` becomes `α^n`, with the oscillation sums growing
  with the extent exactly as the consumer's quantifier order permits.
* `dobrushin_ising_uniform_gap` — THE PUBLIC COROLLARY: inside the window
  `2·tanh|β| + 2·tanh|γ| ≤ α < 1`, for every extent there are normalised
  Perron data for the coupled kernel whose packaged transfer operator is
  bounded by `e^{-m}` for ONE `m > 0` common to all extents.  Ising
  certifies the abstract bridge is inhabited; the bridge itself never
  mentions it.
-/

namespace YangMills.OS

namespace Dobrushin

open Finset

set_option linter.unusedSectionVars false

/-! ## §1  The one-dimensional pairing -/

theorem adj_pairing (m : ℕ) (F : Fin (m + 1) → Fin (m + 1) → ℝ)
    (hF : ∀ a b, F a b = F b a) :
    (∑ a : Fin (m + 1), ∑ b : Fin (m + 1),
      if Nat.dist a.val b.val = 1 then F a b else 0)
      = 2 * ∑ k : Fin m, F k.castSucc k.succ := by
  have hsplit : ∀ a b : Fin (m + 1),
      (if Nat.dist a.val b.val = 1 then F a b else 0)
      = (if b.val = a.val + 1 then F a b else 0)
        + (if a.val = b.val + 1 then F a b else 0) := by
    intro a b
    by_cases h1 : b.val = a.val + 1
    · have hd : Nat.dist a.val b.val = 1 := by unfold Nat.dist; omega
      have h2 : ¬ a.val = b.val + 1 := by omega
      rw [if_pos hd, if_pos h1, if_neg h2, add_zero]
    · by_cases h2 : a.val = b.val + 1
      · have hd : Nat.dist a.val b.val = 1 := by unfold Nat.dist; omega
        rw [if_pos hd, if_neg h1, if_pos h2, zero_add]
      · have hd : ¬ Nat.dist a.val b.val = 1 := by unfold Nat.dist; omega
        rw [if_neg hd, if_neg h1, if_neg h2, add_zero]
  have hhalf : ∀ G : Fin (m + 1) → Fin (m + 1) → ℝ,
      (∑ a : Fin (m + 1), ∑ b : Fin (m + 1),
        if b.val = a.val + 1 then G a b else 0)
      = ∑ k : Fin m, G k.castSucc k.succ := by
    intro G
    have hinner : ∀ a : Fin (m + 1),
        (∑ b : Fin (m + 1), if b.val = a.val + 1 then G a b else 0)
        = if h : a.val < m then G a ⟨a.val + 1, by omega⟩ else 0 := by
      intro a
      by_cases h : a.val < m
      · rw [dif_pos h]
        rw [Finset.sum_eq_single (⟨a.val + 1, by omega⟩ : Fin (m + 1))]
        · rw [if_pos rfl]
        · intro b _ hb
          have hbv : ¬ b.val = a.val + 1 := by
            intro hv
            exact hb (Fin.ext hv)
          rw [if_neg hbv]
        · intro habs
          exact absurd (Finset.mem_univ _) habs
      · rw [dif_neg h]
        refine Finset.sum_eq_zero fun b _ => ?_
        have hbv : ¬ b.val = a.val + 1 := by omega
        rw [if_neg hbv]
    rw [Finset.sum_congr rfl fun a _ => hinner a]
    rw [Fin.sum_univ_castSucc
      (f := fun a : Fin (m + 1) =>
        if h : a.val < m then G a ⟨a.val + 1, by omega⟩ else 0)]
    have hlast : (if h : (Fin.last m).val < m
        then G (Fin.last m) ⟨(Fin.last m).val + 1, by omega⟩ else 0)
        = 0 := by
      rw [dif_neg]
      simp [Fin.last]
    rw [hlast, add_zero]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hk : (k.castSucc : Fin (m + 1)).val < m := by
      have h := k.isLt
      simpa [Fin.coe_castSucc] using h
    rw [dif_pos hk]
    congr 1
    refine Fin.ext ?_
    simp [Fin.coe_castSucc, Fin.val_succ]
  rw [Finset.sum_congr rfl fun a _ =>
    Finset.sum_congr rfl fun b _ => hsplit a b]
  rw [Finset.sum_congr rfl fun a _ => Finset.sum_add_distrib,
    Finset.sum_add_distrib]
  have h1 := hhalf F
  have h2 : (∑ a : Fin (m + 1), ∑ b : Fin (m + 1),
      if a.val = b.val + 1 then F a b else 0)
      = ∑ k : Fin m, F k.succ k.castSucc := by
    rw [Finset.sum_comm]
    have := hhalf (fun a b => F b a)
    rw [← this]
  rw [h1, h2]
  have h3 : (∑ k : Fin m, F k.succ k.castSucc)
      = ∑ k : Fin m, F k.castSucc k.succ :=
    Finset.sum_congr rfl fun k _ => hF _ _
  rw [h3]
  ring

/-! ## §2  The energy split of the rectangle coupling -/

theorem rectJ_energy_split (β γ : ℝ) {T L : ℕ}
    (η : Fin (T + 1) × Fin (L + 1) → Fin 2) :
    (∑ P : Fin (T + 1) × Fin (L + 1), ∑ Q : Fin (T + 1) × Fin (L + 1),
      rectJ β γ P Q * spin (η P) * spin (η Q)) / 2
      = β * ∑ t : Fin T, ∑ j : Fin (L + 1),
          spin (η (t.castSucc, j)) * spin (η (t.succ, j))
        + γ * ∑ t : Fin (T + 1), ∑ k : Fin L,
            spin (η (t, k.castSucc)) * spin (η (t, k.succ)) := by
  have hsplit : ∀ P Q : Fin (T + 1) × Fin (L + 1),
      rectJ β γ P Q * spin (η P) * spin (η Q)
      = (if Nat.dist P.1.val Q.1.val = 1 ∧ P.2 = Q.2
          then β * spin (η P) * spin (η Q) else 0)
        + (if P.1 = Q.1 ∧ Nat.dist P.2.val Q.2.val = 1
          then γ * spin (η P) * spin (η Q) else 0) := by
    intro P Q
    unfold rectJ
    by_cases h1 : Nat.dist P.1.val Q.1.val = 1 ∧ P.2 = Q.2
    · have h2 : ¬ (P.1 = Q.1 ∧ Nat.dist P.2.val Q.2.val = 1) := by
        rintro ⟨he, -⟩
        have : Nat.dist P.1.val Q.1.val = 0 := by rw [he, Nat.dist_self]
        omega
      rw [if_pos h1, if_pos h1, if_neg h2, add_zero]
    · rw [if_neg h1, if_neg h1, zero_add]
      by_cases h2 : P.1 = Q.1 ∧ Nat.dist P.2.val Q.2.val = 1
      · rw [if_pos h2, if_pos h2]
      · rw [if_neg h2, if_neg h2]
        ring
  rw [Finset.sum_congr rfl fun P _ =>
    Finset.sum_congr rfl fun Q _ => hsplit P Q]
  rw [Finset.sum_congr rfl fun P (_ : P ∈ Finset.univ) =>
    Finset.sum_add_distrib, Finset.sum_add_distrib]
  -- the temporal half
  have htemp : (∑ P : Fin (T + 1) × Fin (L + 1),
      ∑ Q : Fin (T + 1) × Fin (L + 1),
      if Nat.dist P.1.val Q.1.val = 1 ∧ P.2 = Q.2
        then β * spin (η P) * spin (η Q) else 0)
      = 2 * (β * ∑ t : Fin T, ∑ j : Fin (L + 1),
          spin (η (t.castSucc, j)) * spin (η (t.succ, j))) := by
    rw [Fintype.sum_prod_type]
    have hP : ∀ (a : Fin (T + 1)) (j : Fin (L + 1)),
        (∑ Q : Fin (T + 1) × Fin (L + 1),
          if Nat.dist a.val Q.1.val = 1 ∧ (j : Fin (L + 1)) = Q.2
            then β * spin (η (a, j)) * spin (η Q) else 0)
        = ∑ b : Fin (T + 1),
            if Nat.dist a.val b.val = 1
              then β * spin (η (a, j)) * spin (η (b, j)) else 0 := by
      intro a j
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun b _ => ?_
      have hin : ∀ j' : Fin (L + 1),
          (if Nat.dist a.val b.val = 1 ∧ j = j'
            then β * spin (η (a, j)) * spin (η (b, j')) else 0)
          = if j = j'
              then (if Nat.dist a.val b.val = 1
                then β * spin (η (a, j)) * spin (η (b, j')) else 0)
              else 0 := by
        intro j'
        by_cases hd : Nat.dist a.val b.val = 1
        · by_cases hj : j = j'
          · rw [if_pos ⟨hd, hj⟩, if_pos hj, if_pos hd]
          · rw [if_neg (fun h => hj h.2), if_neg hj]
        · by_cases hj : j = j'
          · rw [if_neg (fun h => hd h.1), if_pos hj, if_neg hd]
          · rw [if_neg (fun h => hd h.1), if_neg hj]
      rw [Finset.sum_congr rfl fun j' _ => hin j',
        Finset.sum_ite_eq Finset.univ j
          (fun j' => if Nat.dist a.val b.val = 1
            then β * spin (η (a, j)) * spin (η (b, j')) else 0),
        if_pos (Finset.mem_univ j)]
    rw [Finset.sum_congr rfl fun a _ =>
      Finset.sum_congr rfl fun j _ => hP a j]
    rw [Finset.sum_comm]
    have hj : ∀ j : Fin (L + 1),
        (∑ a : Fin (T + 1), ∑ b : Fin (T + 1),
          if Nat.dist a.val b.val = 1
            then β * spin (η (a, j)) * spin (η (b, j)) else 0)
        = 2 * ∑ t : Fin T,
            β * spin (η (t.castSucc, j)) * spin (η (t.succ, j)) := by
      intro j
      exact adj_pairing T
        (fun a b => β * spin (η (a, j)) * spin (η (b, j)))
        (fun a b => by ring)
    rw [Finset.sum_congr rfl fun j _ => hj j, ← Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  -- the spatial half
  have hspat : (∑ P : Fin (T + 1) × Fin (L + 1),
      ∑ Q : Fin (T + 1) × Fin (L + 1),
      if P.1 = Q.1 ∧ Nat.dist P.2.val Q.2.val = 1
        then γ * spin (η P) * spin (η Q) else 0)
      = 2 * (γ * ∑ t : Fin (T + 1), ∑ k : Fin L,
          spin (η (t, k.castSucc)) * spin (η (t, k.succ))) := by
    rw [Fintype.sum_prod_type]
    have hP : ∀ (a : Fin (T + 1)) (j : Fin (L + 1)),
        (∑ Q : Fin (T + 1) × Fin (L + 1),
          if (a : Fin (T + 1)) = Q.1 ∧ Nat.dist j.val Q.2.val = 1
            then γ * spin (η (a, j)) * spin (η Q) else 0)
        = ∑ j' : Fin (L + 1),
            if Nat.dist j.val j'.val = 1
              then γ * spin (η (a, j)) * spin (η (a, j')) else 0 := by
      intro a j
      rw [Fintype.sum_prod_type]
      have hout : ∀ b : Fin (T + 1),
          (∑ j' : Fin (L + 1),
            if a = b ∧ Nat.dist j.val j'.val = 1
              then γ * spin (η (a, j)) * spin (η (b, j')) else 0)
          = if a = b
              then (∑ j' : Fin (L + 1),
                if Nat.dist j.val j'.val = 1
                  then γ * spin (η (a, j)) * spin (η (b, j')) else 0)
              else 0 := by
        intro b
        by_cases hb : a = b
        · rw [if_pos hb]
          refine Finset.sum_congr rfl fun j' _ => ?_
          by_cases hd : Nat.dist j.val j'.val = 1
          · rw [if_pos ⟨hb, hd⟩, if_pos hd]
          · rw [if_neg (fun h => hd h.2), if_neg hd]
        · rw [if_neg hb]
          refine Finset.sum_eq_zero fun j' _ => ?_
          rw [if_neg (fun h => hb h.1)]
      rw [Finset.sum_congr rfl fun b _ => hout b,
        Finset.sum_ite_eq Finset.univ a
          (fun b => ∑ j' : Fin (L + 1),
            if Nat.dist j.val j'.val = 1
              then γ * spin (η (a, j)) * spin (η (b, j')) else 0),
        if_pos (Finset.mem_univ a)]
    rw [Finset.sum_congr rfl fun a _ =>
      Finset.sum_congr rfl fun j _ => hP a j]
    have ht : ∀ a : Fin (T + 1),
        (∑ j : Fin (L + 1), ∑ j' : Fin (L + 1),
          if Nat.dist j.val j'.val = 1
            then γ * spin (η (a, j)) * spin (η (a, j')) else 0)
        = 2 * ∑ k : Fin L,
            γ * spin (η (a, k.castSucc)) * spin (η (a, k.succ)) := by
      intro a
      exact adj_pairing L
        (fun j j' => γ * spin (η (a, j)) * spin (η (a, j')))
        (fun j j' => by ring)
    rw [Finset.sum_congr rfl fun a _ => ht a, ← Finset.mul_sum]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [htemp, hspat]
  ring

/-! ## §3  The weight identity under currying -/

/-- The open-chain slice weight of extent `L + 1`. -/
noncomputable def sliceW (γ : ℝ) (L : ℕ) : (Fin (L + 1) → Fin 2) → ℝ :=
  fun σ => z2PathWeight γ σ

theorem sliceW_pos (γ : ℝ) (L : ℕ) (σ : Fin (L + 1) → Fin 2) :
    0 < sliceW γ L σ := by
  unfold sliceW z2PathWeight
  exact Finset.prod_pos fun t _ => z2Bond_pos γ _ _

theorem z2Sign_eq_spin (i j : Fin 2) : z2Sign i j = spin i * spin j := by
  fin_cases i <;> fin_cases j <;> simp [z2Sign, spin] <;> norm_num

/-- **The geometry bridge**: the free strip Gibbs weight of the spatial
system IS the rectangle Ising weight, under currying.  Exact: the half in
the Ising weight's exponent compensates ordered double counting, and both
sides are single-counted bond products. -/
theorem curry_weight (β γ : ℝ) {T L : ℕ}
    (X : Fin (T + 1) → Fin (L + 1) → Fin 2) :
    gibbsWeight (sliceW γ L) β X
      = isingWeight (rectJ β γ) (fun P => X P.1 P.2) := by
  unfold isingWeight
  rw [rectJ_energy_split β γ (fun P => X P.1 P.2)]
  unfold gibbsWeight sliceW z2PathWeight spatialKernel
  have hb : ∀ (c : ℝ) (i j : Fin 2),
      z2Bond c i j = Real.exp (c * (spin i * spin j)) := by
    intro c i j
    unfold z2Bond
    rw [z2Sign_eq_spin]
  -- each product of bonds is the exponential of the summed energy
  have hw : ∀ t : Fin (T + 1),
      (∏ k : Fin L, z2Bond γ (X t k.castSucc) (X t k.succ))
      = Real.exp (γ * ∑ k : Fin L, spin (X t k.castSucc)
          * spin (X t k.succ)) := by
    intro t
    rw [Finset.mul_sum, Real.exp_sum]
    exact Finset.prod_congr rfl fun k _ => hb γ _ _
  have hk : ∀ t : Fin T,
      (∏ j : Fin (L + 1), z2Bond β (X t.castSucc j) (X t.succ j))
      = Real.exp (β * ∑ j : Fin (L + 1), spin (X t.castSucc j)
          * spin (X t.succ j)) := by
    intro t
    rw [Finset.mul_sum, Real.exp_sum]
    exact Finset.prod_congr rfl fun j _ => hb β _ _
  rw [Finset.prod_congr rfl fun t _ => hw t,
    Finset.prod_congr rfl fun t _ => hk t,
    ← Real.exp_sum, ← Real.exp_sum, ← Real.exp_add]
  congr 1
  show (∑ t : Fin (T + 1), γ * ∑ k : Fin L,
        spin (X t k.castSucc) * spin (X t k.succ))
      + (∑ t : Fin T, β * ∑ j : Fin (L + 1),
        spin (X t.castSucc j) * spin (X t.succ j))
    = β * ∑ t : Fin T, ∑ j : Fin (L + 1),
        spin (X t.castSucc j) * spin (X t.succ j)
      + γ * ∑ t : Fin (T + 1), ∑ k : Fin L,
        spin (X t k.castSucc) * spin (X t k.succ)
  rw [Finset.mul_sum, Finset.mul_sum]
  exact add_comm _ _

/-! ## §4  The measure transport -/

/-- The tilt layer's free covariance IS the rectangle covariance of the
end-slice observables, through the currying bijection. -/
theorem freeCov_eq_rect_covar (β γ : ℝ) {T L : ℕ}
    (A B : (Fin (L + 1) → Fin 2) → ℝ) :
    freeCov (sliceW γ L) β T A B
      = covar (gibbsMu (isingWeight (rectJ β γ)))
          (fun η => A (fun j => η (0, j)))
          (fun η => B (fun j => η (Fin.last T, j))) := by
  have e : (Fin (T + 1) → Fin (L + 1) → Fin 2)
      ≃ (Fin (T + 1) × Fin (L + 1) → Fin 2) :=
    (Equiv.curry _ _ _).symm
  have he : ∀ X : Fin (T + 1) → Fin (L + 1) → Fin 2,
      e X = fun P => X P.1 P.2 := fun X => rfl
  -- the partition functions agree
  have hZ : gibbsPartition (sliceW γ L) β T
      = gibbsZ (isingWeight (rectJ β γ)) := by
    unfold gibbsPartition gibbsZ
    refine Fintype.sum_equiv e _ _ fun X => ?_
    show gibbsWeight (sliceW γ L) β X
      = isingWeight (rectJ β γ) (fun P => X P.1 P.2)
    exact curry_weight β γ X
  -- generic two-endpoint sums agree
  have hPS : ∀ A' B' : (Fin (L + 1) → Fin 2) → ℝ,
      gibbsPathSum (sliceW γ L) β T A' B'
      = ∑ η : Fin (T + 1) × Fin (L + 1) → Fin 2,
          isingWeight (rectJ β γ) η
            * (A' (fun j => η (0, j)) * B' (fun j => η (Fin.last T, j))) := by
    intro A' B'
    unfold gibbsPathSum
    refine Fintype.sum_equiv e _ _ fun X => ?_
    show A' (X 0) * B' (X (Fin.last T)) * gibbsWeight (sliceW γ L) β X
      = isingWeight (rectJ β γ) (fun P => X P.1 P.2)
        * (A' (fun j => X 0 j) * B' (fun j => X (Fin.last T) j))
    rw [curry_weight β γ X]
    ring
  -- expectations under the normalised rectangle measure
  have hexp : ∀ F : (Fin (T + 1) × Fin (L + 1) → Fin 2) → ℝ,
      expect (gibbsMu (isingWeight (rectJ β γ))) F
      = (∑ η, isingWeight (rectJ β γ) η * F η)
          / gibbsZ (isingWeight (rectJ β γ)) := by
    intro F
    unfold expect gibbsMu
    rw [← Finset.sum_div]
    refine congrArg (· / _) (Finset.sum_congr rfl fun η _ => ?_)
    ring
  unfold freeCov freeE covar
  rw [hZ, hPS, hPS, hPS, hexp, hexp, hexp]
  congr 1
  · congr 1
    refine Finset.sum_congr rfl fun η _ => ?_
    ring
  · congr 1
    · congr 1
      refine Finset.sum_congr rfl fun η _ => ?_
      ring
    · congr 1
      refine Finset.sum_congr rfl fun η _ => ?_
      ring

/-! ## §5  Oscillation transport, and the family feed -/

theorem row_deltaAt_zero {T L : ℕ} (A : (Fin (L + 1) → Fin 2) → ℝ)
    (t : Fin (T + 1)) (j : Fin (L + 1)) (ht : t ≠ 0) :
    deltaAt ((t, j) : Fin (T + 1) × Fin (L + 1))
      (fun η => A (fun j' => η (0, j'))) = 0 := by
  have hconst : ∀ (η : Fin (T + 1) × Fin (L + 1) → Fin 2) (s : Fin 2),
      (fun j' => Function.update η (t, j) s (0, j'))
      = fun j' => η (0, j') := by
    intro η s
    funext j'
    refine Function.update_noteq ?_ _ _
    intro h
    exact ht ((congrArg Prod.fst h).symm)
  refine le_antisymm ?_ ?_
  · refine Finset.sup'_le _ _ fun q _ => ?_
    rw [hconst q.1 q.2, sub_self, abs_zero]
  · have h0 := abs_sub_update_le_deltaAt
      ((t, j) : Fin (T + 1) × Fin (L + 1))
      (fun η => A (fun j' => η (0, j')))
      (fun _ => 0) ((fun _ => 0 : Fin (T + 1) × Fin (L + 1) → Fin 2) (t, j))
    calc (0 : ℝ) = |A (fun j' => (fun _ => (0 : Fin 2)) ((0 : Fin (T + 1)), j'))
        - A (fun j' => Function.update (fun _ => (0 : Fin 2)) (t, j)
            ((fun _ => (0 : Fin 2)) (t, j)) (0, j'))| := by
          rw [Function.update_eq_self, sub_self, abs_zero]
      _ ≤ _ := h0

theorem row_deltaAt_zero' {T L : ℕ} (B : (Fin (L + 1) → Fin 2) → ℝ)
    (t : Fin (T + 1)) (j : Fin (L + 1)) (ht : t ≠ Fin.last T) :
    deltaAt ((t, j) : Fin (T + 1) × Fin (L + 1))
      (fun η => B (fun j' => η (Fin.last T, j'))) = 0 := by
  have hconst : ∀ (η : Fin (T + 1) × Fin (L + 1) → Fin 2) (s : Fin 2),
      (fun j' => Function.update η (t, j) s (Fin.last T, j'))
      = fun j' => η (Fin.last T, j') := by
    intro η s
    funext j'
    refine Function.update_noteq ?_ _ _
    intro h
    exact ht ((congrArg Prod.fst h).symm)
  refine le_antisymm ?_ ?_
  · refine Finset.sup'_le _ _ fun q _ => ?_
    rw [hconst q.1 q.2, sub_self, abs_zero]
  · have h0 := abs_sub_update_le_deltaAt
      ((t, j) : Fin (T + 1) × Fin (L + 1))
      (fun η => B (fun j' => η (Fin.last T, j')))
      (fun _ => 0) ((fun _ => 0 : Fin (T + 1) × Fin (L + 1) → Fin 2) (t, j))
    calc (0 : ℝ) = |B (fun j' => (fun _ => (0 : Fin 2)) (Fin.last T, j'))
        - B (fun j' => Function.update (fun _ => (0 : Fin 2)) (t, j)
            ((fun _ => (0 : Fin 2)) (t, j)) (Fin.last T, j'))| := by
          rw [Function.update_eq_self, sub_self, abs_zero]
      _ ≤ _ := h0

theorem row_deltaAt_le {T L : ℕ} (A : (Fin (L + 1) → Fin 2) → ℝ)
    (j : Fin (L + 1)) :
    deltaAt (((0 : Fin (T + 1)), j) : Fin (T + 1) × Fin (L + 1))
      (fun η => A (fun j' => η (0, j'))) ≤ deltaAt j A := by
  refine Finset.sup'_le _ _ fun q _ => ?_
  have hrow : (fun j' => Function.update q.1 ((0 : Fin (T + 1)), j) q.2
      (0, j'))
      = Function.update (fun j' => q.1 (0, j')) j q.2 := by
    funext j'
    by_cases hj : j' = j
    · rw [hj, Function.update_same, Function.update_same]
    · rw [Function.update_noteq (fun h => hj (congrArg Prod.snd h)),
        Function.update_noteq hj]
  rw [hrow]
  exact abs_sub_update_le_deltaAt j A (fun j' => q.1 (0, j')) q.2

theorem row_deltaAt_le' {T L : ℕ} (B : (Fin (L + 1) → Fin 2) → ℝ)
    (j : Fin (L + 1)) :
    deltaAt ((Fin.last T, j) : Fin (T + 1) × Fin (L + 1))
      (fun η => B (fun j' => η (Fin.last T, j'))) ≤ deltaAt j B := by
  refine Finset.sup'_le _ _ fun q _ => ?_
  have hrow : (fun j' => Function.update q.1 (Fin.last T, j) q.2
      (Fin.last T, j'))
      = Function.update (fun j' => q.1 (Fin.last T, j')) j q.2 := by
    funext j'
    by_cases hj : j' = j
    · rw [hj, Function.update_same, Function.update_same]
    · rw [Function.update_noteq (fun h => hj (congrArg Prod.snd h)),
        Function.update_noteq hj]
  rw [hrow]
  exact abs_sub_update_le_deltaAt j B (fun j' => q.1 (Fin.last T, j')) q.2

theorem deltaAt_nonneg {ι S : Type*} [Fintype ι] [DecidableEq ι] [Fintype S]
    [Nonempty ι] [Nonempty S] (i : ι) (f : (ι → S) → ℝ) :
    0 ≤ deltaAt i f := by
  have h := abs_sub_update_le_deltaAt i f (fun _ => Classical.arbitrary S)
    ((fun _ => Classical.arbitrary S : ι → S) i)
  calc (0 : ℝ) = |f (fun _ => Classical.arbitrary S)
      - f (Function.update (fun _ => Classical.arbitrary S) i
          ((fun _ => Classical.arbitrary S : ι → S) i))| := by
        rw [Function.update_eq_self, sub_self, abs_zero]
    _ ≤ _ := h

/-- **The family feed**: inside the window, the free covariance of
end-slice observables at horizon `T` decays as `α^T`, with slice-level
oscillation-sum constants.  Every site pair the covariance sees is at
rectangle distance at least `T`. -/
theorem rect_feed (β γ : ℝ) {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hwin : 2 * Real.tanh |β| + 2 * Real.tanh |γ| ≤ α)
    {T L : ℕ} (A B : (Fin (L + 1) → Fin 2) → ℝ) :
    |freeCov (sliceW γ L) β T A B|
      ≤ (∑ j, deltaAt j A) * (∑ j, deltaAt j B)
          * (1 / (4 * (1 - α))) * α ^ T := by
  rw [freeCov_eq_rect_covar β γ A B]
  set f : (Fin (T + 1) × Fin (L + 1) → Fin 2) → ℝ :=
    fun η => A (fun j => η (0, j)) with hf
  set g : (Fin (T + 1) × Fin (L + 1) → Fin 2) → ℝ :=
    fun η => B (fun j => η (Fin.last T, j)) with hg
  have hbase := ising_covar_exp_decay (rectJ β γ) (rectJ_diag β γ)
    (rectJ_symm β γ) hα0 hα1
    (fun p => le_trans (rectJ_row β γ p) hwin)
    rectDist rectDist_self rectDist_triangle (rectJ_supp β γ) f g
  refine le_trans hbase ?_
  -- kill the off-row terms and bound the surviving block
  have hterm : ∀ (P Q : Fin (T + 1) × Fin (L + 1)),
      deltaAt P f * (α ^ rectDist P Q / (1 - α)) * deltaAt Q g
      ≤ (if P.1 = 0 ∧ Q.1 = Fin.last T
          then deltaAt P.2 A * (α ^ T / (1 - α)) * deltaAt Q.2 B
          else 0) := by
    intro P Q
    by_cases hP : P.1 = 0
    · by_cases hQ : Q.1 = Fin.last T
      · rw [if_pos ⟨hP, hQ⟩]
        have hdist : T ≤ rectDist P Q := by
          unfold rectDist
          have h1 : Nat.dist P.1.val Q.1.val = T := by
            rw [hP, hQ]
            show Nat.dist 0 (Fin.last T).val = T
            simp [Nat.dist, Fin.last]
          omega
        have hpow : α ^ rectDist P Q ≤ α ^ T :=
          pow_le_pow_right_of_le_one hα0 hα1.le hdist
        have h1α : (0 : ℝ) < 1 - α := by linarith
        have hdf : deltaAt P f ≤ deltaAt P.2 A := by
          have hP' : P = (0, P.2) := by
            rw [Prod.ext_iff]
            exact ⟨hP, rfl⟩
          rw [hP']
          exact row_deltaAt_le A P.2
        have hdg : deltaAt Q g ≤ deltaAt Q.2 B := by
          have hQ' : Q = (Fin.last T, Q.2) := by
            rw [Prod.ext_iff]
            exact ⟨hQ, rfl⟩
          rw [hQ']
          exact row_deltaAt_le' B Q.2
        have hnn1 : 0 ≤ deltaAt P f := deltaAt_nonneg _ _
        have hnn2 : 0 ≤ deltaAt Q g := deltaAt_nonneg _ _
        have hnnA : 0 ≤ deltaAt P.2 A := deltaAt_nonneg _ _
        have hnnB : 0 ≤ deltaAt Q.2 B := deltaAt_nonneg _ _
        have hrate : α ^ rectDist P Q / (1 - α) ≤ α ^ T / (1 - α) :=
          div_le_div_of_nonneg_right hpow h1α.le
        have hratenn : 0 ≤ α ^ rectDist P Q / (1 - α) :=
          div_nonneg (pow_nonneg hα0 _) h1α.le
        calc deltaAt P f * (α ^ rectDist P Q / (1 - α)) * deltaAt Q g
            ≤ deltaAt P.2 A * (α ^ rectDist P Q / (1 - α)) * deltaAt Q g :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right hdf hratenn) hnn2
          _ ≤ deltaAt P.2 A * (α ^ T / (1 - α)) * deltaAt Q g := by
              refine mul_le_mul_of_nonneg_right ?_ hnn2
              exact mul_le_mul_of_nonneg_left hrate hnnA
          _ ≤ deltaAt P.2 A * (α ^ T / (1 - α)) * deltaAt Q.2 B := by
              refine mul_le_mul_of_nonneg_left hdg ?_
              have : (0 : ℝ) ≤ α ^ T / (1 - α) :=
                div_nonneg (pow_nonneg hα0 _) h1α.le
              exact mul_nonneg hnnA this
      · rw [if_neg (fun h => hQ h.2)]
        have hzero : deltaAt Q g = 0 := by
          have hQ' : Q = (Q.1, Q.2) := rfl
          rw [hQ']
          exact row_deltaAt_zero' B Q.1 Q.2 hQ
        rw [hzero, mul_zero]
    · rw [if_neg (fun h => hP h.1)]
      have hzero : deltaAt P f = 0 := by
        have hP' : P = (P.1, P.2) := rfl
        rw [hP']
        exact row_deltaAt_zero A P.1 P.2 hP
      rw [hzero, zero_mul, zero_mul]
  have hsum : (∑ P : Fin (T + 1) × Fin (L + 1),
      ∑ Q : Fin (T + 1) × Fin (L + 1),
      deltaAt P f * (α ^ rectDist P Q / (1 - α)) * deltaAt Q g)
      ≤ ∑ P : Fin (T + 1) × Fin (L + 1),
          ∑ Q : Fin (T + 1) × Fin (L + 1),
          (if P.1 = 0 ∧ Q.1 = Fin.last T
            then deltaAt P.2 A * (α ^ T / (1 - α)) * deltaAt Q.2 B
            else 0) :=
    Finset.sum_le_sum fun P _ => Finset.sum_le_sum fun Q _ => hterm P Q
  have hcollapse : (∑ P : Fin (T + 1) × Fin (L + 1),
      ∑ Q : Fin (T + 1) × Fin (L + 1),
      (if P.1 = 0 ∧ Q.1 = Fin.last T
        then deltaAt P.2 A * (α ^ T / (1 - α)) * deltaAt Q.2 B
        else 0))
      = (∑ j, deltaAt j A) * (∑ j, deltaAt j B) * (α ^ T / (1 - α)) := by
    rw [Fintype.sum_prod_type]
    have hinner : ∀ (a : Fin (T + 1)) (j : Fin (L + 1)),
        (∑ Q : Fin (T + 1) × Fin (L + 1),
          if (a : Fin (T + 1)) = 0 ∧ Q.1 = Fin.last T
            then deltaAt j A * (α ^ T / (1 - α)) * deltaAt Q.2 B
            else 0)
        = if a = 0
            then deltaAt j A * (α ^ T / (1 - α)) * ∑ j', deltaAt j' B
            else 0 := by
      intro a j
      by_cases ha : a = 0
      · rw [if_pos ha, Fintype.sum_prod_type]
        have hb : ∀ b : Fin (T + 1),
            (∑ j' : Fin (L + 1),
              if a = 0 ∧ b = Fin.last T
                then deltaAt j A * (α ^ T / (1 - α)) * deltaAt j' B
                else 0)
            = if b = Fin.last T
                then deltaAt j A * (α ^ T / (1 - α)) * ∑ j', deltaAt j' B
                else 0 := by
          intro b
          by_cases hbl : b = Fin.last T
          · rw [if_pos hbl, Finset.mul_sum]
            refine Finset.sum_congr rfl fun j' _ => ?_
            rw [if_pos ⟨ha, hbl⟩]
          · rw [if_neg hbl]
            refine Finset.sum_eq_zero fun j' _ => ?_
            rw [if_neg (fun h => hbl h.2)]
        rw [Finset.sum_congr rfl fun b _ => hb b,
          Finset.sum_ite_eq' Finset.univ (Fin.last T)
            (fun _ => deltaAt j A * (α ^ T / (1 - α)) * ∑ j', deltaAt j' B),
          if_pos (Finset.mem_univ _)]
      · rw [if_neg ha]
        refine Finset.sum_eq_zero fun Q _ => ?_
        rw [if_neg (fun h => ha h.1)]
    rw [Finset.sum_congr rfl fun a _ =>
      Finset.sum_congr rfl fun j _ => hinner a j]
    have hout : ∀ a : Fin (T + 1),
        (∑ j : Fin (L + 1),
          if a = 0
            then deltaAt j A * (α ^ T / (1 - α)) * ∑ j', deltaAt j' B
            else 0)
        = if a = 0
            then (∑ j, deltaAt j A) * (α ^ T / (1 - α))
                * ∑ j', deltaAt j' B
            else 0 := by
      intro a
      by_cases ha : a = 0
      · rw [if_pos ha, Finset.sum_mul, Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [if_pos ha]
      · rw [if_neg ha]
        exact Finset.sum_eq_zero fun j _ => by rw [if_neg ha]
    rw [Finset.sum_congr rfl fun a _ => hout a,
      Finset.sum_ite_eq' Finset.univ (0 : Fin (T + 1))
        (fun _ => (∑ j, deltaAt j A) * (α ^ T / (1 - α))
          * ∑ j', deltaAt j' B),
      if_pos (Finset.mem_univ _)]
  calc |covar (gibbsMu (isingWeight (rectJ β γ))) f g|
      ≤ (∑ P, ∑ Q, deltaAt P f * (α ^ rectDist P Q / (1 - α))
          * deltaAt Q g) / 4 := hbase
    _ ≤ ((∑ j, deltaAt j A) * (∑ j, deltaAt j B) * (α ^ T / (1 - α))) / 4 := by
        refine div_le_div_of_nonneg_right ?_ (by norm_num)
        exact le_trans hsum (le_of_eq hcollapse)
    _ = (∑ j, deltaAt j A) * (∑ j, deltaAt j B)
          * (1 / (4 * (1 - α))) * α ^ T := by
        ring

/-! ## §6  The public corollary -/

/-- **THE DOBRUSHIN–ISING COROLLARY** (charter Amendment 2, public theorem
(ii)).  Inside the window `2·tanh|β| + 2·tanh|γ| ≤ α < 1` there is ONE
`m > 0` such that for EVERY extent there are normalised Perron data for
the coupled kernel whose packaged transfer operator satisfies
`‖projectedTransfer‖ ≤ e^{-m}`.  Ising certifies the abstract bridge of
`abstract_uniform_gap` is inhabited by the physical family; the bridge
itself never mentions it. -/
theorem dobrushin_ising_uniform_gap (β γ : ℝ) {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1)
    (hwin : 2 * Real.tanh |β| + 2 * Real.tanh |γ| ≤ α) :
    ∃ m : ℝ, 0 < m ∧ ∀ L : ℕ,
      ∃ (lam : ℝ) (Om : (Fin (L + 1) → Fin 2) → ℝ),
        0 < lam ∧ (∀ σ, 0 < Om σ) ∧
        (∀ σ, ∑ τ, tiltKernel (sliceW γ L) β lam σ τ * Om τ = Om σ) ∧
        ‖projectedTransfer (opOf (tiltKernel (sliceW γ L) β lam))
            (vacOf Om)‖ ≤ Real.exp (-m) := by
  -- the Perron family, chosen once
  have hdata : ∀ L : ℕ,
      ∃ (v : (Fin (L + 1) → Fin 2) → ℝ) (lam : ℝ),
        (∀ σ, 0 < v σ) ∧ 0 < lam ∧
        (∀ σ, ∑ τ, symWeighted (sliceW γ L) β σ τ * v τ = lam * v σ) ∧
        (∀ σ, ∑ τ, normalizedKernel (symWeighted (sliceW γ L) β) lam σ τ
            * unitVacuum v τ = unitVacuum v σ) ∧
        (∑ σ, unitVacuum v σ * unitVacuum v σ = 1) :=
    fun L => symVacuum_exists (sliceW_pos γ L) β
  choose v lam hv hlam hraw heig hnorm using hdata
  set Om : ∀ L : ℕ, (Fin (L + 1) → Fin 2) → ℝ :=
    fun L => unitVacuum (v L) with hOmdef
  have hOm : ∀ L σ, 0 < Om L σ := fun L σ => unitVacuum_pos (hv L) σ
  have heig' : ∀ L σ,
      ∑ τ, tiltKernel (sliceW γ L) β (lam L) σ τ * Om L τ = Om L σ :=
    fun L σ => heig L σ
  -- the band-decay hypothesis, per extent, from the tilt layer + the feed
  have hdecay : ∀ L : ℕ, ∀ f : (Fin (L + 1) → Fin 2) → ℝ,
      ∃ C : ℝ, ∀ n : ℕ,
        |bandCov (tiltKernel (sliceW γ L) β (lam L)) (Om L) n f f|
          ≤ C * α ^ n := by
    intro L f
    have hc0 : (0 : ℝ) <
        Finset.univ.inf' Finset.univ_nonempty (tilt (sliceW γ L) (Om L)) := by
      rw [Finset.lt_inf'_iff]
      intro σ _
      exact tilt_pos (sliceW_pos γ L) (hOm L) σ
    obtain ⟨C, hC0, hC⟩ := bandCov_decay_of_free_decay
      (sliceW_pos γ L) (hOm L) β (hlam L) (heig' L)
      hα0.le hα1.le
      (D := 1 / (4 * (1 - α)))
      (by
        have h1α : (0 : ℝ) < 1 - α := by linarith
        positivity)
      hc0
      (fun σ => Finset.inf'_le _ (Finset.mem_univ σ))
      (fun A => ∑ j, deltaAt j A)
      (fun A => Finset.sum_nonneg fun j _ => deltaAt_nonneg j A)
      (fun n A B => rect_feed β γ hα0.le hα1 hwin A B)
      f f
    exact ⟨C, hC⟩
  -- the abstract transport theorem, over the extent family
  obtain ⟨m, hm, hall⟩ := abstract_uniform_gap
    (ι := ℕ) (Xs := fun L => Fin (L + 1) → Fin 2)
    (fun L => tiltKernel (sliceW γ L) β (lam L)) Om
    (fun L => tiltKernel_symm (sliceW γ L) β (lam L))
    hOm heig' hα0 hα1 hdecay
  exact ⟨m, hm, fun L => ⟨lam L, Om L, hlam L, hOm L, heig' L, hall L⟩⟩

end Dobrushin

end YangMills.OS
