/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson
-/
import Mathlib
import YangMills.OS.SpatialGibbs
import YangMills.OS.PerronKernel

/-!
# The ring weight, and the symmetry that splits its spectrum

The lane's open analytic question is an extent-uniform bound on the COUPLED
kernel.  `docs/UNIFORMITY-TARGET.md` records the pre-registered target and the
measurements behind it:

    for `β ≥ 0`, `γ ≥ 0` and EVERY `L`:   specRatio(L) ≤ tanh β · e^{2γ}

with the ring weight `spatialWeightRing γ`, under which the weighted kernel is
the symmetrised transfer matrix of the anisotropic square-lattice Ising model.
Both hypotheses are exhibited as active there, and the bound is measured tight on
the whole face `γ = 0`, where it is paper 11's theorem.

**Nothing in this file proves that bound.**  A skeleton for it has four pieces:

  1. `J K = K J`, so the space splits into even and odd sectors   -- HERE
  2. the Perron vector lies in the even sector                    -- HERE
  3. the ODD block is bounded by `q` times the Perron eigenvalue  -- NOT HERE
  4. the EVEN block off the Perron line is bounded too            -- NOT HERE

with `q = tanh β · e^{2γ}`.  The third identifies the rate; the fourth decides
whether there is a theorem, and measurement says only that it is smaller, which
is not an argument.

## What is here

* `flipCfg` --- the global spin flip on a configuration, an involution;
* the flip-invariance of the kernel and of `spatialWeightRing`, the ring weight
  that has been in `PerronKernel` all along --- its bonds run around a ring, so
  it has NO FIRST SITE, which is exactly why paper 11's induction does not
  transfer;
* `act_flip_comm` --- the operator commutes with the flip;
* `perron_even` --- and therefore the Perron vector lies in the even sector.
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

/-- **THE RING WEIGHT DOES NOT SEE A GLOBAL FLIP EITHER.**  `spatialWeightRing`
is the weight whose bonds run around a ring, so it has NO FIRST SITE --- and that
is not a detail: paper 11's uniform rate is proved by induction on the extent,
adding one site at a time, and a ring cannot be built that way.  It lives in
`PerronKernel`; an earlier draft of this file defined a synonym for it, which is
how two names for one object start to diverge. -/
@[simp] theorem spatialWeightRing_flip (γ : ℝ) {L : ℕ}
    (σ : Fin (L + 1) → Fin 2) :
    spatialWeightRing γ (flipCfg σ) = spatialWeightRing γ σ := by
  unfold spatialWeightRing
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

/-- The same for the symmetrised ring-weighted kernel, which is the object the
uniformity target is about. -/
theorem act_flip_comm_ring {L : ℕ} (γ β : ℝ)
    (u : (Fin (L + 1) → Fin 2) → ℝ) :
    act (symWeighted (spatialWeightRing γ) β) (flipObs u)
      = flipObs (act (symWeighted (spatialWeightRing γ) β) u) :=
  act_flip_comm (fun σ τ => symWeighted_flip (spatialWeightRing_flip γ) β σ τ) u

/-! ## §4  The Perron vector is even

Second of the four the uniformity target needs.  It costs nothing beyond the
commutation and the uniqueness of a positive eigenvector, both already in the
tree: if `Ω` is the strictly positive eigenvector then so is `J Ω`, uniqueness
makes them proportional, and the normalisation forces the constant to be one. -/

/-- The source-weighted kernel inherits flip invariance from its weight. -/
theorem sourceWeightedKernelL_flip {L : ℕ} {w : (Fin L → Fin 2) → ℝ}
    (hw : ∀ σ, w (flipCfg σ) = w σ) (β : ℝ) (σ τ : Fin L → Fin 2) :
    sourceWeightedKernelL w β (flipCfg σ) (flipCfg τ)
      = sourceWeightedKernelL w β σ τ := by
  unfold sourceWeightedKernelL
  rw [hw, spatialKernel_flip]

/-- **THE PERRON VECTOR IS EVEN.**  For the ring-coupled slice at every extent,
the strictly positive normalised eigenvector satisfies `Ω ∘ flip = Ω`.

This is the second item of the uniformity skeleton.  It does NOT bound anything:
it says only that the Perron direction lies in the even sector, so that the
subdominant question splits into the odd block and the even block off the Perron
line.  Those two bounds are the ones that decide whether there is a theorem, and
neither is here. -/
theorem perron_even (β γ : ℝ) (L : ℕ) :
    ∃ (Ω : (Fin (L + 1) → Fin 2) → ℝ) (lam : ℝ), (∀ σ, 0 < Ω σ) ∧
      (∑ σ, Ω σ = 1) ∧ 0 < lam ∧
      (∀ σ, ∑ τ : Fin (L + 1) → Fin 2,
        sourceWeightedKernelL (spatialWeightRing γ) β σ τ * Ω τ = lam * Ω σ) ∧
      ∀ σ, Ω (flipCfg σ) = Ω σ := by
  obtain ⟨Ω, lam, hpos, hsum, hlam, heig⟩ := coupled_ring_vacuum_exists β γ L
  set A := sourceWeightedKernelL (spatialWeightRing γ) β with hA
  have hApos : ∀ σ τ, 0 < A σ τ := fun σ τ =>
    sourceWeightedKernelL_pos (spatialWeightRing_pos γ) β σ τ
  have hAflip : ∀ σ τ, A (flipCfg σ) (flipCfg τ) = A σ τ := fun σ τ =>
    sourceWeightedKernelL_flip (spatialWeightRing_flip γ) β σ τ
  -- `J Ω` is a strictly positive eigenvector for the SAME eigenvalue
  have hflipPos : ∀ σ, 0 < flipObs Ω σ := fun σ => hpos _
  have hflipEig : ∀ σ, ∑ τ, A σ τ * flipObs Ω τ = lam * flipObs Ω σ := by
    intro σ
    have h := congrFun (act_flip_comm (K := A) hAflip Ω) σ
    unfold act flipObs at h
    show ∑ τ, A σ τ * Ω (flipCfg τ) = lam * Ω (flipCfg σ)
    rw [h]
    exact heig (flipCfg σ)
  -- uniqueness makes them proportional, and the normalisation fixes the constant
  obtain ⟨-, c, hc, hprop⟩ := pos_eigenvector_unique hApos hpos hflipPos heig hflipEig
  have hone : c = 1 := by
    have hs : ∑ σ, flipObs Ω σ = ∑ σ, Ω σ := by
      unfold flipObs
      exact Equiv.sum_comp (flipEquiv (L + 1)) Ω
    rw [Finset.sum_congr rfl fun σ _ => hprop σ, ← Finset.mul_sum, hsum] at hs
    linarith
  exact ⟨Ω, lam, hpos, hsum, hlam, heig, fun σ => by
    have := hprop σ
    unfold flipObs at this
    rw [this, hone, one_mul]⟩

end YangMills.OS
