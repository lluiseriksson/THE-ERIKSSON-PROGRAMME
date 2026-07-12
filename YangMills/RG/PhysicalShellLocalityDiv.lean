/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import Mathlib
import YangMills.RG.PhysicalShellLocalityD1

/-!
# Concrete locality of the flat divergence term `div†div`
(`hRpoly` campaign — P4-CT, owner obligation 2, second shell term)

Second concrete stencil input: at the trivial background the gauge
constraint `div = gaugeConstraintQCLM ρ triv` is the backward divergence
(`gaugeConstraintQCLM_trivial_apply`), coupling the site `x` to the `2d`
bonds `(x, i)` and `(x.shiftBack i, i)`.  Both slot sites lie within
Chebyshev distance 1 of `x`, so two bond probes at `physicalBondDist > 2`
have orthogonal divergence images; and each of the `2d` slot equations has
at most ONE solving site, so the probe image satisfies the ℓ¹ bound
`‖div δ_p v‖ ≤ 2‖v‖`.  Through the Addendum-263 Gram calculus:

* `flatDiv_adjointCompSelf_finiteRange` —
  `PhysicalCovarianceFiniteRange (div†div) physicalBondDist 2`;
* `flatDiv_adjointCompSelf_kernelBound` —
  `PhysicalCovarianceKernelBound (div†div) (fun _ _ => (2 : ℝ)²)`.

The range matches the curl term's (`2`), so `K₀ = D1†D1 + div†div`
assembles at common range 2 via `physicalCovarianceFiniteRange_add`.

**Honest scope.**  Second of three shell terms.  Remaining: `a·Q†Q`
locality, `Sigma := 0` free shell, CT3, CT4, the positive-`θ` witness, and
the `CT_fixedVolume` endpoint.  Not `hRpoly`, not mass gap, not Clay.

Oracle target: `[propext, Classical.choice, Quot.sound]`.  No sorry, no axioms.
-/

namespace YangMills.RG

open scoped RealInnerProductSpace

variable {d N Nc : ℕ} [NeZero N]

/-! ## Geometry: the backward step -/

/-- One backward coordinate step has circular distance at most 1. -/
theorem finTorusDist_pred_le (a : Fin N) :
    finTorusDist a ⟨(a.val + N - 1) % N, Nat.mod_lt _ (NeZero.pos N)⟩ ≤ 1 := by
  unfold finTorusDist zmodCircDist
  have hsplit : a.val + N - 1 = a.val + (N - 1) := by
    have hN : 1 ≤ N := NeZero.one_le
    omega
  have hcast : (((a.val + N - 1) % N : ℕ) : ZMod N)
      = ((a.val : ℕ) : ZMod N) - 1 := by
    rw [ZMod.natCast_mod, hsplit, Nat.cast_add,
      Nat.cast_sub (NeZero.one_le), ZMod.natCast_self, Nat.cast_one]
    ring
  have harg : ((a.val : ℕ) : ZMod N) - (((a.val + N - 1) % N : ℕ) : ZMod N)
      = 1 := by
    rw [hcast]
    ring
  rw [harg]
  calc zmodCircVal (1 : ZMod N) ≤ (1 : ZMod N).val := zmodCircVal_le_val _
    _ = ((1 : ℕ) : ZMod N).val := by rw [Nat.cast_one]
    _ = 1 % N := ZMod.val_natCast N 1
    _ ≤ 1 := Nat.mod_le 1 N

/-- Backward shift moves a site by Chebyshev distance at most 1. -/
theorem finBoxDist_shiftBack_le (x : FinBox d N) (j : Fin d) :
    finBoxDist x (FinBox.shiftBack x j) ≤ 1 := by
  unfold finBoxDist
  apply Finset.sup_le
  intro i _
  by_cases hij : i = j
  · subst hij
    have hcoord : FinBox.shiftBack x i i
        = ⟨(x i + N - 1) % N, Nat.mod_lt _ (NeZero.pos N)⟩ := by
      unfold FinBox.shiftBack
      rw [if_pos rfl]
    rw [hcoord]
    exact finTorusDist_pred_le (x i)
  · have hcoord : FinBox.shiftBack x j i = x i := by
      unfold FinBox.shiftBack
      rw [if_neg hij]
    rw [hcoord, finTorusDist_self]
    exact Nat.zero_le _

/-- Both divergence slots at site `x` lie within bond distance 1 of any bond
anchored at a site within distance 1 of `x`; concretely, two divergence
slots of the same site are within bond distance 2. -/
theorem div_slots_dist_le (x : FinBox d N) (s₁ s₂ : FinBox d N) (i j : Fin d)
    (h₁ : finBoxDist x s₁ ≤ 1) (h₂ : finBoxDist x s₂ ≤ 1) :
    physicalBondDist ((s₁, i) : PhysicalBond d N) (s₂, j) ≤ 2 := by
  apply max_le
  · show finBoxDist s₁ s₂ ≤ 2
    calc finBoxDist s₁ s₂ ≤ finBoxDist s₁ x + finBoxDist x s₂ :=
        finBoxDist_triangle _ _ _
      _ ≤ 1 + 1 := by
          apply Nat.add_le_add _ h₂
          rw [finBoxDist_comm]
          exact h₁
      _ = 2 := rfl
  · exact le_trans (dir_indicator_le_one _ _) (by norm_num)

section TrivialDiv

variable [NeZero d] [NeZero Nc]

/-! ## The probe image of the trivial divergence -/

/-- The trivial divergence of a single-bond probe, slot by slot. -/
theorem gaugeConstraint_trivial_single_apply
    (ρ : SUNAdjointModel Nc) (p : PhysicalBond d N) (v : SUNLieCoord Nc)
    (x : FinBox d N) :
    gaugeConstraintQCLM ρ (trivialPhysicalGaugeBackground d N Nc)
        (singlePhysicalBondCochain (d := d) (N := N) (Nc := Nc) p v) x =
      ∑ i : Fin d,
        ((if ((x, i) : PhysicalBond d N) = p then v else 0)
          - (if ((FinBox.shiftBack x i, i) : PhysicalBond d N) = p then v else 0)) := by
  rw [gaugeConstraintQCLM_trivial_apply]
  rfl

/-- If no divergence slot of `x` equals `p`, the probe image vanishes at `x`. -/
theorem gaugeConstraint_trivial_single_eq_zero
    (ρ : SUNAdjointModel Nc) (p : PhysicalBond d N) (v : SUNLieCoord Nc)
    (x : FinBox d N)
    (h : ∀ i : Fin d, ((x, i) : PhysicalBond d N) ≠ p ∧
      ((FinBox.shiftBack x i, i) : PhysicalBond d N) ≠ p) :
    gaugeConstraintQCLM ρ (trivialPhysicalGaugeBackground d N Nc)
        (singlePhysicalBondCochain (d := d) (N := N) (Nc := Nc) p v) x = 0 := by
  rw [gaugeConstraint_trivial_single_apply]
  apply Finset.sum_eq_zero
  intro i _
  rw [if_neg (h i).1, if_neg (h i).2, sub_zero]

/-- **Gram orthogonality for the trivial divergence**: probes at bond
distance `> 2` have orthogonal divergence images. -/
theorem gaugeConstraint_trivial_gram_orthogonal
    (ρ : SUNAdjointModel Nc) (p q : PhysicalBond d N) (v w : SUNLieCoord Nc)
    (hfar : 2 < physicalBondDist q p) :
    inner ℝ (gaugeConstraintQCLM ρ (trivialPhysicalGaugeBackground d N Nc)
        (singlePhysicalBondCochain (d := d) (N := N) (Nc := Nc) p v))
      (gaugeConstraintQCLM ρ (trivialPhysicalGaugeBackground d N Nc)
        (singlePhysicalBondCochain (d := d) (N := N) (Nc := Nc) q w)) = 0 := by
  rw [PiLp.inner_apply]
  apply Finset.sum_eq_zero
  intro x _
  by_cases hp : ∀ i : Fin d, ((x, i) : PhysicalBond d N) ≠ p ∧
      ((FinBox.shiftBack x i, i) : PhysicalBond d N) ≠ p
  · rw [gaugeConstraint_trivial_single_eq_zero ρ p v x hp, inner_zero_left]
  · by_cases hq : ∀ i : Fin d, ((x, i) : PhysicalBond d N) ≠ q ∧
        ((FinBox.shiftBack x i, i) : PhysicalBond d N) ≠ q
    · rw [gaugeConstraint_trivial_single_eq_zero ρ q w x hq, inner_zero_right]
    · exfalso
      push_neg at hp hq
      obtain ⟨i, hpi⟩ := hp
      obtain ⟨j, hqj⟩ := hq
      -- extract a slot equal to p and a slot equal to q, each with slot site
      -- within distance 1 of x
      have hpslot : ∃ sp : FinBox d N, ∃ ip : Fin d,
          ((sp, ip) : PhysicalBond d N) = p ∧ finBoxDist x sp ≤ 1 := by
        by_cases h1 : ((x, i) : PhysicalBond d N) = p
        · refine ⟨x, i, h1, ?_⟩
          rw [finBoxDist_self]
          exact Nat.zero_le _
        · refine ⟨FinBox.shiftBack x i, i, hpi h1, finBoxDist_shiftBack_le x i⟩
      have hqslot : ∃ sq : FinBox d N, ∃ iq : Fin d,
          ((sq, iq) : PhysicalBond d N) = q ∧ finBoxDist x sq ≤ 1 := by
        by_cases h1 : ((x, j) : PhysicalBond d N) = q
        · refine ⟨x, j, h1, ?_⟩
          rw [finBoxDist_self]
          exact Nat.zero_le _
        · refine ⟨FinBox.shiftBack x j, j, hqj h1, finBoxDist_shiftBack_le x j⟩
      obtain ⟨sp, ip, hpe, hpd⟩ := hpslot
      obtain ⟨sq, iq, hqe, hqd⟩ := hqslot
      have hd : physicalBondDist q p ≤ 2 := by
        rw [← hpe, ← hqe]
        exact div_slots_dist_le x sq sp iq ip hqd hpd
      omega

/-! ## Probe-image norm bound -/

/-- Per-site value bound for the divergence probe image. -/
theorem gaugeConstraint_trivial_single_norm_apply_le
    (ρ : SUNAdjointModel Nc) (p : PhysicalBond d N) (v : SUNLieCoord Nc)
    (x : FinBox d N) :
    ‖gaugeConstraintQCLM ρ (trivialPhysicalGaugeBackground d N Nc)
        (singlePhysicalBondCochain (d := d) (N := N) (Nc := Nc) p v) x‖ ≤
      ∑ i : Fin d,
        ((if ((x, i) : PhysicalBond d N) = p then ‖v‖ else 0)
          + (if ((FinBox.shiftBack x i, i) : PhysicalBond d N) = p then ‖v‖ else 0)) := by
  rw [gaugeConstraint_trivial_single_apply]
  calc ‖∑ i : Fin d,
        ((if ((x, i) : PhysicalBond d N) = p then v else 0)
          - (if ((FinBox.shiftBack x i, i) : PhysicalBond d N) = p then v else 0))‖
      ≤ ∑ i : Fin d,
          ‖(if ((x, i) : PhysicalBond d N) = p then v else 0)
            - (if ((FinBox.shiftBack x i, i) : PhysicalBond d N) = p then v else 0)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ i : Fin d,
          ((if ((x, i) : PhysicalBond d N) = p then ‖v‖ else 0)
            + (if ((FinBox.shiftBack x i, i) : PhysicalBond d N) = p then ‖v‖ else 0)) := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        have h1 : ‖(if ((x, i) : PhysicalBond d N) = p then v else 0)
            - (if ((FinBox.shiftBack x i, i) : PhysicalBond d N) = p then v else 0)‖
            ≤ ‖(if ((x, i) : PhysicalBond d N) = p then v else 0)‖
              + ‖(if ((FinBox.shiftBack x i, i) : PhysicalBond d N) = p then v else 0)‖ :=
          norm_sub_le _ _
        have e1 : ‖(if ((x, i) : PhysicalBond d N) = p then v else 0)‖
            = (if ((x, i) : PhysicalBond d N) = p then ‖v‖ else 0) := by
          by_cases h : ((x, i) : PhysicalBond d N) = p
          · rw [if_pos h, if_pos h]
          · rw [if_neg h, if_neg h, norm_zero]
        have e2 : ‖(if ((FinBox.shiftBack x i, i) : PhysicalBond d N) = p then v else 0)‖
            = (if ((FinBox.shiftBack x i, i) : PhysicalBond d N) = p then ‖v‖ else 0) := by
          by_cases h : ((FinBox.shiftBack x i, i) : PhysicalBond d N) = p
          · rw [if_pos h, if_pos h]
          · rw [if_neg h, if_neg h, norm_zero]
        rw [e1, e2] at h1
        exact h1

/-- **Probe-image norm bound for the trivial divergence**:
`‖div δ_p v‖ ≤ 2‖v‖` (each of the two slot families has exactly one global
match). -/
theorem gaugeConstraint_trivial_single_norm_le
    (ρ : SUNAdjointModel Nc) (p : PhysicalBond d N) (v : SUNLieCoord Nc) :
    ‖gaugeConstraintQCLM ρ (trivialPhysicalGaugeBackground d N Nc)
        (singlePhysicalBondCochain (d := d) (N := N) (Nc := Nc) p v)‖ ≤
      (2 : ℝ) * ‖v‖ := by
  classical
  have hfwd : ∀ i : Fin d,
      ∑ x : FinBox d N, (if ((x, i) : PhysicalBond d N) = p then ‖v‖ else 0)
        = (if i = p.2 then ‖v‖ else 0) := by
    intro i
    by_cases hi : i = p.2
    · rw [if_pos hi]
      calc ∑ x : FinBox d N, (if ((x, i) : PhysicalBond d N) = p then ‖v‖ else 0)
          = ∑ x : FinBox d N, (if x = p.1 then ‖v‖ else 0) := by
            refine Finset.sum_congr rfl (fun x _ => if_congr ?_ rfl rfl)
            constructor
            · intro h
              exact congrArg Prod.fst h
            · intro h
              rw [h, hi]
        _ = ‖v‖ := by
            rw [Finset.sum_ite_eq' Finset.univ p.1]
            rw [if_pos (Finset.mem_univ _)]
    · rw [if_neg hi]
      apply Finset.sum_eq_zero
      intro x _
      rw [if_neg]
      intro h
      exact hi (congrArg Prod.snd h)
  have hbwd : ∀ i : Fin d,
      ∑ x : FinBox d N,
        (if ((FinBox.shiftBack x i, i) : PhysicalBond d N) = p then ‖v‖ else 0)
        = (if i = p.2 then ‖v‖ else 0) := by
    intro i
    by_cases hi : i = p.2
    · rw [if_pos hi]
      have hbij : Function.Bijective
          (fun x : FinBox d N => FinBox.shiftBack x i) := by
        constructor
        · intro a b hab
          have h1 := congrArg (fun z => FinBox.shift z i) hab
          simpa [FinBox.shift_shiftBack] using h1
        · intro y
          exact ⟨FinBox.shift y i, FinBox.shiftBack_shift y i⟩
      calc ∑ x : FinBox d N,
            (if ((FinBox.shiftBack x i, i) : PhysicalBond d N) = p then ‖v‖ else 0)
          = ∑ x : FinBox d N, (if FinBox.shiftBack x i = p.1 then ‖v‖ else 0) := by
            refine Finset.sum_congr rfl (fun x _ => if_congr ?_ rfl rfl)
            constructor
            · intro h
              exact congrArg Prod.fst h
            · intro h
              rw [h, hi]
        _ = ∑ y : FinBox d N, (if y = p.1 then ‖v‖ else 0) :=
            hbij.sum_comp (fun y => if y = p.1 then ‖v‖ else 0)
        _ = ‖v‖ := by
            rw [Finset.sum_ite_eq' Finset.univ p.1]
            rw [if_pos (Finset.mem_univ _)]
    · rw [if_neg hi]
      apply Finset.sum_eq_zero
      intro x _
      rw [if_neg]
      intro h
      exact hi (congrArg Prod.snd h)
  calc ‖gaugeConstraintQCLM ρ (trivialPhysicalGaugeBackground d N Nc)
        (singlePhysicalBondCochain (d := d) (N := N) (Nc := Nc) p v)‖
      ≤ ∑ x : FinBox d N,
          ‖gaugeConstraintQCLM ρ (trivialPhysicalGaugeBackground d N Nc)
            (singlePhysicalBondCochain (d := d) (N := N) (Nc := Nc) p v) x‖ :=
        piLp_norm_le_sum_norm _
    _ ≤ ∑ x : FinBox d N, ∑ i : Fin d,
          ((if ((x, i) : PhysicalBond d N) = p then ‖v‖ else 0)
            + (if ((FinBox.shiftBack x i, i) : PhysicalBond d N) = p then ‖v‖ else 0)) :=
        Finset.sum_le_sum
          (fun x _ => gaugeConstraint_trivial_single_norm_apply_le ρ p v x)
    _ = ∑ i : Fin d, ∑ x : FinBox d N,
          ((if ((x, i) : PhysicalBond d N) = p then ‖v‖ else 0)
            + (if ((FinBox.shiftBack x i, i) : PhysicalBond d N) = p then ‖v‖ else 0)) :=
        Finset.sum_comm
    _ = ∑ i : Fin d,
          ((if i = p.2 then ‖v‖ else 0) + (if i = p.2 then ‖v‖ else 0)) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.sum_add_distrib, hfwd i, hbwd i]
    _ = 2 * ‖v‖ := by
        rw [Finset.sum_add_distrib]
        rw [Finset.sum_ite_eq' Finset.univ p.2]
        rw [if_pos (Finset.mem_univ _)]
        ring

/-! ## The Gram-package endpoints for the divergence term -/

/-- **Concrete finite range of the flat divergence term**:
`div†div` has kernel range `2` in `physicalBondDist`. -/
theorem flatDiv_adjointCompSelf_finiteRange
    (ρ : SUNAdjointModel Nc) :
    PhysicalCovarianceFiniteRange
      ((gaugeConstraintQCLM (d := d) (N := N) ρ
          (trivialPhysicalGaugeBackground d N Nc)).adjoint.comp
        (gaugeConstraintQCLM ρ (trivialPhysicalGaugeBackground d N Nc)))
      physicalBondDist 2 :=
  adjointCompSelf_finiteRange _ physicalBondDist
    (fun p q v w hR => gaugeConstraint_trivial_gram_orthogonal ρ p q v w hR)

/-- **Concrete kernel bound of the flat divergence term**:
`div†div` has entrywise block bound `2² = 4`. -/
theorem flatDiv_adjointCompSelf_kernelBound
    (ρ : SUNAdjointModel Nc) :
    PhysicalCovarianceKernelBound
      ((gaugeConstraintQCLM (d := d) (N := N) ρ
          (trivialPhysicalGaugeBackground d N Nc)).adjoint.comp
        (gaugeConstraintQCLM ρ (trivialPhysicalGaugeBackground d N Nc)))
      (fun _ _ => (2 : ℝ) ^ 2) :=
  adjointCompSelf_kernelBound _
    (fun p v => gaugeConstraint_trivial_single_norm_le ρ p v)

/-! ## Definitional identification and the `K₀` assembly -/

/-- The divergence composition IS the gauge-fixing mass summand of the flat
Hodge operator, definitionally — no substitute operator was localized. -/
theorem gaugeFixingMassCLM_trivial_eq (ρ : SUNAdjointModel Nc) :
    gaugeFixingMassCLM ρ (trivialPhysicalGaugeBackground d N Nc)
      = (gaugeConstraintQCLM (d := d) (N := N) ρ
          (trivialPhysicalGaugeBackground d N Nc)).adjoint.comp
        (gaugeConstraintQCLM ρ (trivialPhysicalGaugeBackground d N Nc)) := rfl

/-- The flat Hodge operator IS the sum of the two localized compositions,
definitionally. -/
theorem flatGaugeHodgeK0CLM_eq_sum (ρ : SUNAdjointModel Nc) :
    flatGaugeHodgeK0CLM d N Nc ρ
      = (covariantD1CLM (d := d) (N := N) ρ
            (trivialPhysicalGaugeBackground d N Nc)).adjoint.comp
          (covariantD1CLM ρ (trivialPhysicalGaugeBackground d N Nc))
        + (gaugeConstraintQCLM (d := d) (N := N) ρ
            (trivialPhysicalGaugeBackground d N Nc)).adjoint.comp
          (gaugeConstraintQCLM ρ (trivialPhysicalGaugeBackground d N Nc)) := rfl

/-- **Concrete finite range of the FULL flat Hodge operator `K₀`**:
range 2 in `physicalBondDist` — both summands at common range, assembled by
the Addendum-263 combinator.  This closes the `K₀` half of owner
obligation 2. -/
theorem flatGaugeHodgeK0_finiteRange (ρ : SUNAdjointModel Nc) :
    PhysicalCovarianceFiniteRange (flatGaugeHodgeK0CLM d N Nc ρ)
      physicalBondDist 2 := by
  rw [flatGaugeHodgeK0CLM_eq_sum]
  exact physicalCovarianceFiniteRange_add physicalBondDist
    (flatCurl_adjointCompSelf_finiteRange ρ)
    (flatDiv_adjointCompSelf_finiteRange ρ)

/-- **Concrete kernel bound of the FULL flat Hodge operator `K₀`**:
entrywise block bound `(4d)² + 4`. -/
theorem flatGaugeHodgeK0_kernelBound (ρ : SUNAdjointModel Nc) :
    PhysicalCovarianceKernelBound (flatGaugeHodgeK0CLM d N Nc ρ)
      (fun _ _ => ((4 * d : ℕ) : ℝ) ^ 2 + (2 : ℝ) ^ 2) := by
  rw [flatGaugeHodgeK0CLM_eq_sum]
  exact physicalCovarianceKernelBound_add
    (flatCurl_adjointCompSelf_kernelBound ρ)
    (flatDiv_adjointCompSelf_kernelBound ρ)

end TrivialDiv

end YangMills.RG
