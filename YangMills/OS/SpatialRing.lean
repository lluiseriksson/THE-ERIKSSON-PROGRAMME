/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson
-/
import Mathlib
import YangMills.OS.SpatialGibbs

/-!
# The ring weight, and the symmetry that splits its spectrum

The lane's open analytic question is an extent-uniform bound on the COUPLED
kernel.  `docs/UNIFORMITY-TARGET.md` records the pre-registered target and the
measurements behind it:

    for `β ≥ 0`, `γ ≥ 0` and EVERY `L`:   specRatio(L) ≤ tanh β · e^{2γ}

with the ring weight `ringWeight γ`, under which the weighted kernel is the
symmetrised transfer matrix of the anisotropic square-lattice Ising model.  Both
hypotheses are exhibited as active there, and the bound is measured tight on the
whole face `γ = 0`, where it is paper 11's theorem.

**Nothing in this file proves that bound.**  This file builds the first piece of
its skeleton: the global spin flip commutes with the weighted kernel, so the
space splits into an even and an odd sector.  Measurement says the Perron vector
is even and the subdominant odd; a proof of the bound must control BOTH blocks,
and the even one is the debt that no argument yet covers.

## What is here

* `flipCfg` --- the global spin flip on a configuration, an involution;
* `ringWeight` --- the weight whose bonds run around a ring, so that it has no
  first site: this is exactly why paper 11's induction does not transfer;
* the flip-invariance of the kernel and of the ring weight;
* `act_flip_comm` --- the operator commutes with the flip.
-/

namespace YangMills.OS

open Finset

/-! ## §1  The global spin flip -/

/-- Flip a single spin. -/
def z2Flip (i : Fin 2) : Fin 2 := if i = 0 then 1 else 0

@[simp] theorem z2Flip_flip (i : Fin 2) : z2Flip (z2Flip i) = i := by
  fin_cases i <;> rfl

@[simp] theorem z2Sign_flip (i j : Fin 2) :
    z2Sign (z2Flip i) (z2Flip j) = z2Sign i j := by
  fin_cases i <;> fin_cases j <;> rfl

@[simp] theorem z2Bond_flip (β : ℝ) (i j : Fin 2) :
    z2Bond β (z2Flip i) (z2Flip j) = z2Bond β i j := by
  unfold z2Bond
  rw [z2Sign_flip]

/-- The global spin flip on a configuration. -/
def flipCfg {L : ℕ} (σ : Fin L → Fin 2) : Fin L → Fin 2 := fun j => z2Flip (σ j)

@[simp] theorem flipCfg_flip {L : ℕ} (σ : Fin L → Fin 2) :
    flipCfg (flipCfg σ) = σ := by
  funext j
  simp [flipCfg]

theorem flipCfg_involutive {L : ℕ} :
    Function.Involutive (flipCfg (L := L)) := flipCfg_flip

/-- The flip is a bijection of configurations: needed to reindex sums. -/
noncomputable def flipEquiv (L : ℕ) : (Fin L → Fin 2) ≃ (Fin L → Fin 2) :=
  Function.Involutive.toPerm _ flipCfg_involutive

@[simp] theorem flipEquiv_apply {L : ℕ} (σ : Fin L → Fin 2) :
    flipEquiv L σ = flipCfg σ := rfl

/-! ## §2  The kernel and the ring weight are flip-invariant -/

/-- The decoupled kernel does not see a global flip: every bond sign is
unchanged when both spins turn over. -/
@[simp] theorem spatialKernel_flip (β : ℝ) {L : ℕ} (σ τ : Fin L → Fin 2) :
    spatialKernel β (flipCfg σ) (flipCfg τ) = spatialKernel β σ τ := by
  unfold spatialKernel
  exact Finset.prod_congr rfl fun j _ => by
    show z2Bond β (z2Flip (σ j)) (z2Flip (τ j)) = z2Bond β (σ j) (τ j)
    rw [z2Bond_flip]

/-- **THE RING WEIGHT.**  Its bonds run around a ring, so it has NO FIRST SITE.
That is not a detail: paper 11's uniform rate is proved by induction on the
extent, adding one site at a time, and a ring cannot be built that way.  The
weight is written here so the obstruction is an object rather than a remark. -/
noncomputable def ringWeight (γ : ℝ) {L : ℕ} [NeZero L] (σ : Fin L → Fin 2) : ℝ :=
  ∏ j : Fin L, z2Bond γ (σ j) (σ (j + 1))

theorem ringWeight_pos (γ : ℝ) {L : ℕ} [NeZero L] (σ : Fin L → Fin 2) :
    0 < ringWeight γ σ := by
  unfold ringWeight
  exact Finset.prod_pos fun j _ => z2Bond_pos γ _ _

/-- The ring weight does not see a global flip either. -/
@[simp] theorem ringWeight_flip (γ : ℝ) {L : ℕ} [NeZero L] (σ : Fin L → Fin 2) :
    ringWeight γ (flipCfg σ) = ringWeight γ σ := by
  unfold ringWeight
  exact Finset.prod_congr rfl fun j _ => by
    show z2Bond γ (z2Flip (σ j)) (z2Flip (σ (j + 1))) = z2Bond γ (σ j) (σ (j + 1))
    rw [z2Bond_flip]

/-- A weight invariant under the flip gives a flip-invariant weighted kernel.
Stated for an arbitrary such weight, since nothing below needs the ring. -/
theorem symWeighted_flip {L : ℕ} {w : (Fin L → Fin 2) → ℝ}
    (hw : ∀ σ, w (flipCfg σ) = w σ) (β : ℝ) (σ τ : Fin L → Fin 2) :
    symWeighted w β (flipCfg σ) (flipCfg τ) = symWeighted w β σ τ := by
  unfold symWeighted
  rw [hw, hw, spatialKernel_flip]

/-! ## §3  The commutation, which is what splits the spectrum -/

/-- The flip acting on observables. -/
noncomputable def flipObs {L : ℕ} (u : (Fin L → Fin 2) → ℝ) :
    (Fin L → Fin 2) → ℝ := fun σ => u (flipCfg σ)

/-- **`J K = K J`.**  The operator commutes with the global flip, so the space
splits into the even and odd sectors of `J`.  Everything the uniformity target
says about sectors rests on this line. -/
theorem act_flip_comm {L : ℕ} {K : (Fin L → Fin 2) → (Fin L → Fin 2) → ℝ}
    (hK : ∀ σ τ, K (flipCfg σ) (flipCfg τ) = K σ τ)
    (u : (Fin L → Fin 2) → ℝ) :
    act K (flipObs u) = flipObs (act K u) := by
  funext σ
  show ∑ τ, K σ τ * u (flipCfg τ) = ∑ τ, K (flipCfg σ) τ * u τ
  -- reindex the RIGHT side by the flip: it is a bijection of configurations
  rw [← Equiv.sum_comp (flipEquiv L) (fun τ => K (flipCfg σ) τ * u τ)]
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp only [flipEquiv_apply]
  rw [hK]

/-- The same for the ring-weighted kernel, which is the case the target is
about. -/
theorem act_flip_comm_ring {L : ℕ} [NeZero L] (γ β : ℝ)
    (u : (Fin L → Fin 2) → ℝ) :
    act (symWeighted (ringWeight γ) β) (flipObs u)
      = flipObs (act (symWeighted (ringWeight γ) β) u) :=
  act_flip_comm (fun σ τ => symWeighted_flip (ringWeight_flip γ) β σ τ) u

end YangMills.OS
