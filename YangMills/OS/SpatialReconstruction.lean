/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson
-/
import Mathlib
import YangMills.OS.SpatialOS

/-!
# The transfer operator the two geometries force

Paper 13 gave two reflected forms of the SAME Gibbs measure --- through a SITE
(`osPairingSite_eq_gibbsSum`) and through a BOND
(`osPairingBond_eq_gibbsSum`) --- and both factor through the same map,
`collapse`, which sends an observable of a whole half-chain to a vector on the
boundary slice.  This module asks what operator those two forms define between
them, and finds that the answer is not a choice.

## The operator is forced

If the physical space of boundary vectors is to carry an operator `T` with

  `⟨u, T v⟩_site = ⟨u, v⟩_bond`                                             (∗)

then `T` is determined, because `⟨·,·⟩_site` is definite as soon as `w > 0`:

  `(T v) σ = w σ * ∑ τ, K σ τ * v τ`.

`transferOp` is that operator, `siteForm_transferOp` is (∗), and
`transferOp_selfAdjoint` says it is symmetric for the site inner product.  For
`β ≥ 0` it is moreover POSITIVE, `transferOp_nonneg`.  Self-adjoint and positive
on the physical space is what an Osterwalder--Schrader transfer operator is
asked to be.

## Why BOTH geometries had to exist first

`T` advances a half-chain across ONE more slice, and that turns an even
separation into an odd one.  So (∗) has the site geometry on its left and the
bond geometry on its right: a construction owning only one of the two has no
equation to define `T` by at all.  That is the honest reason paper 13's site
bridge was a precondition rather than a symmetric afterthought, and it is why
`osPairing_transfer` --- the same identity read on the MEASURE --- is the
headline of this file.

## Pre-registration

`scripts/judge_os_reconstruction.py`, committed at `47d48fc2` **before** a line
of this file was written and before it was run.  Four gates, each predicting a
NUMBER: R1 `rank(collapse) = 2^L` exactly as an integer; R2 the
self-adjointness residual zero to `1e-12`, negative `β` included; R3 the
residual of (∗) itself zero to `1e-12`; R4 the spectrum of `T` equal entry by
entry to that of `symWeighted`, all real, with `max|eig|/λ = 1`.  All four
passed.  The file also states what each failure would have meant --- an R3
failure would have meant the reconstruction was built on the wrong map and had
to be redesigned rather than patched.

## What is NOT here

R4 is a gate, not a theorem: this file does NOT prove that `T` inherits the
Perron eigenvalue or the spectral gap of `symWeighted`, and it does not build a
Hamiltonian.  It also does not prove a contraction bound.  Those are the next
step, and naming them here is not the same as having them.
-/

namespace YangMills.OS

open Finset

/-! ## §1  The two forms, on boundary vectors

Both are already known to be the reflected forms of the Gibbs measure; what is
new here is reading them as forms on the boundary space itself, where an
operator can act. -/

/-- The SITE form on boundary vectors: the physical inner product.  Definite as
soon as `w > 0`, which is the whole reason it, and not the bond form, is what
the reconstruction inner product must be. -/
noncomputable def siteForm {L : ℕ} (w : (Fin L → Fin 2) → ℝ)
    (u v : (Fin L → Fin 2) → ℂ) : ℂ :=
  ∑ σ : Fin L → Fin 2, (starRingEnd ℂ) (u σ) * v σ * ((1 / w σ : ℝ) : ℂ)

/-- The BOND form on boundary vectors: the one that carries the kernel. -/
noncomputable def bondForm {L : ℕ} (β : ℝ)
    (u v : (Fin L → Fin 2) → ℂ) : ℂ :=
  ∑ σ : Fin L → Fin 2, ∑ τ : Fin L → Fin 2,
    (starRingEnd ℂ) (u σ) * ((spatialKernel β σ τ : ℝ) : ℂ) * v τ

/-- The site form is exactly paper 13's site pairing, read on boundary
vectors. -/
theorem siteForm_collapse {L : ℕ} (w : (Fin L → Fin 2) → ℝ) (β : ℝ) (m : ℕ)
    (F G : (Fin (m + 1) → (Fin L → Fin 2)) → ℂ) :
    siteForm w (collapse w β m F) (collapse w β m G)
      = osPairingSiteCross w β m F G :=
  (osPairingSiteCross_eq w β m F G).symm

/-- And the bond form is paper 13's bond pairing. -/
theorem bondForm_collapse {L : ℕ} (w : (Fin L → Fin 2) → ℝ) (β : ℝ) (m : ℕ)
    (F G : (Fin (m + 1) → (Fin L → Fin 2)) → ℂ) :
    bondForm β (collapse w β m F) (collapse w β m G)
      = osPairingBondCross w β m F G :=
  (osPairingBondCross_eq w β m F G).symm

/-! ## §2  The operator (∗) forces -/

/-- **THE TRANSFER OPERATOR.**  Not chosen: the unique solution of
`⟨u, T v⟩_site = ⟨u, v⟩_bond`, which is an equation because the site form is
definite. -/
noncomputable def transferOp {L : ℕ} (w : (Fin L → Fin 2) → ℝ) (β : ℝ)
    (v : (Fin L → Fin 2) → ℂ) : (Fin L → Fin 2) → ℂ :=
  fun σ => ((w σ : ℝ) : ℂ) * ∑ τ : Fin L → Fin 2,
    ((spatialKernel β σ τ : ℝ) : ℂ) * v τ

/-- **THE DEFINING EQUATION (∗).**  Site form on the left, bond form on the
right: one geometry on each side, which is why both bridges were needed. -/
theorem siteForm_transferOp {L : ℕ} {w : (Fin L → Fin 2) → ℝ}
    (hw : ∀ σ, 0 < w σ) (β : ℝ) (u v : (Fin L → Fin 2) → ℂ) :
    siteForm w u (transferOp w β v) = bondForm β u v := by
  unfold siteForm bondForm transferOp
  refine Finset.sum_congr rfl fun σ _ => ?_
  have hσ : ((w σ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hw σ).ne'
  simp only [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun τ _ => ?_
  push_cast
  field_simp
  try ring

/-- The same equation with the operator on the LEFT.  It needs the symmetry of
the kernel, which the right-hand version did not. -/
theorem siteForm_transferOp_left {L : ℕ} {w : (Fin L → Fin 2) → ℝ}
    (hw : ∀ σ, 0 < w σ) (β : ℝ) (u v : (Fin L → Fin 2) → ℂ) :
    siteForm w (transferOp w β u) v = bondForm β u v := by
  unfold siteForm bondForm transferOp
  have step : ∀ σ : Fin L → Fin 2,
      (starRingEnd ℂ) (((w σ : ℝ) : ℂ)
            * ∑ τ : Fin L → Fin 2, ((spatialKernel β σ τ : ℝ) : ℂ) * u τ)
          * v σ * ((1 / w σ : ℝ) : ℂ)
        = ∑ τ : Fin L → Fin 2,
            (starRingEnd ℂ) (u τ) * ((spatialKernel β τ σ : ℝ) : ℂ) * v σ := by
    intro σ
    have hσ : ((w σ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hw σ).ne'
    rw [map_mul, map_sum, Complex.conj_ofReal]
    simp only [map_mul, Complex.conj_ofReal, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [spatialKernel_symm β τ σ]
    push_cast
    field_simp
    try ring
  rw [Finset.sum_congr rfl fun σ _ => step σ]
  rw [Finset.sum_comm]

/-- **THE TRANSFER OPERATOR IS SELF-ADJOINT** for the physical inner product,
at EVERY `β` --- negative included.  Only `w > 0` and the symmetry of the kernel
are used. -/
theorem transferOp_selfAdjoint {L : ℕ} {w : (Fin L → Fin 2) → ℝ}
    (hw : ∀ σ, 0 < w σ) (β : ℝ) (u v : (Fin L → Fin 2) → ℂ) :
    siteForm w u (transferOp w β v) = siteForm w (transferOp w β u) v := by
  rw [siteForm_transferOp hw, siteForm_transferOp_left hw]

/-! ## §3  Positivity of the form, and of the operator -/

/-- The physical inner product is positive: a non-negative real on the
diagonal, at every `β`. -/
theorem siteForm_self_nonneg {L : ℕ} {w : (Fin L → Fin 2) → ℝ}
    (hw : ∀ σ, 0 < w σ) (u : (Fin L → Fin 2) → ℂ) :
    ∃ r : ℝ, 0 ≤ r ∧ siteForm w u u = (r : ℂ) := by
  refine ⟨∑ σ : Fin L → Fin 2, Complex.normSq (u σ) / w σ,
    Finset.sum_nonneg fun σ _ =>
      div_nonneg (Complex.normSq_nonneg _) (hw σ).le, ?_⟩
  unfold siteForm
  push_cast
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [mul_comm ((starRingEnd ℂ) (u σ)) (u σ), Complex.mul_conj]
  push_cast
  ring

/-- The bond form is a non-negative real on the diagonal for `β ≥ 0`.  This is
the kernel fact of paper 12, lifted to complex boundary vectors by the generic
real-to-complex step. -/
theorem bondForm_self_nonneg {L : ℕ} {β : ℝ} (hβ : 0 ≤ β)
    (u : (Fin L → Fin 2) → ℂ) :
    ∃ r : ℝ, 0 ≤ r ∧ bondForm β u u = (r : ℂ) := by
  have hsym : ∀ σ τ : Fin L → Fin 2,
      spatialKernel β σ τ = spatialKernel β τ σ := spatialKernel_symm β
  have hquad : ∀ x : (Fin L → Fin 2) → ℝ,
      0 ≤ ∑ σ, ∑ τ, spatialKernel β σ τ * (x σ * x τ) := by
    intro x
    have h := spatialKernel_posSemidef hβ L x
    have hrw : ∑ σ, x σ * act (spatialKernel β) x σ
        = ∑ σ, ∑ τ, spatialKernel β σ τ * (x σ * x τ) := by
      unfold act
      refine Finset.sum_congr rfl fun σ _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun τ _ => by ring
    linarith [hrw ▸ h]
  refine ⟨(∑ σ, ∑ τ, spatialKernel β σ τ * ((u σ).re * (u τ).re))
      + ∑ σ, ∑ τ, spatialKernel β σ τ * ((u σ).im * (u τ).im),
    by have h1 := hquad (fun σ => (u σ).re)
       have h2 := hquad (fun σ => (u σ).im)
       linarith, ?_⟩
  unfold bondForm
  rw [complexQuad_eq hsym u]

/-- **THE TRANSFER OPERATOR IS POSITIVE** for `β ≥ 0`: its quadratic form in
the physical inner product is a non-negative real.  Together with
`transferOp_selfAdjoint` this is what an Osterwalder--Schrader transfer operator
is asked to be. -/
theorem transferOp_nonneg {L : ℕ} {w : (Fin L → Fin 2) → ℝ}
    (hw : ∀ σ, 0 < w σ) {β : ℝ} (hβ : 0 ≤ β) (u : (Fin L → Fin 2) → ℂ) :
    ∃ r : ℝ, 0 ≤ r ∧ siteForm w u (transferOp w β u) = (r : ℂ) := by
  rw [siteForm_transferOp hw]
  exact bondForm_self_nonneg hβ u

/-! ## §4  The physical space is the whole boundary space

Without this the operator would be honest but might live on a proper subspace,
and every statement about it would be weaker than it sounds.  Gate R1 predicted
the rank as an integer before this was written. -/

/-- The constant half-path ending at `σ` is a half-path ending at `σ`.  Trivial,
and it is the non-emptiness witness the surjectivity proof needs. -/
theorem const_mem_halvesAt {L m : ℕ} (σ : Fin L → Fin 2) :
    (fun _ => σ) ∈ halvesAt L m σ := by
  rw [mem_halvesAt]
  rfl

/-- **THE COLLAPSE IS SURJECTIVE.**  Every boundary vector is the collapse of an
observable of the whole half-chain, so the physical space is all of
`(Fin L → Fin 2) → ℂ` and nothing smaller. -/
theorem collapse_surjective {L : ℕ} {w : (Fin L → Fin 2) → ℝ}
    (hw : ∀ σ, 0 < w σ) (β : ℝ) (m : ℕ) (v : (Fin L → Fin 2) → ℂ) :
    ∃ F : (Fin (m + 1) → (Fin L → Fin 2)) → ℂ, collapse w β m F = v := by
  classical
  have hD : ∀ σ : Fin L → Fin 2,
      0 < ∑ b ∈ halvesAt L m σ, gibbsWeight w β b := fun σ =>
    Finset.sum_pos (fun b _ => gibbsWeight_pos hw β b)
      ⟨_, const_mem_halvesAt (m := m) σ⟩
  refine ⟨fun a => v (edgeOf a)
      / ((∑ b ∈ halvesAt L m (edgeOf a), gibbsWeight w β b : ℝ) : ℂ), ?_⟩
  funext σ
  have hDc : ((∑ b ∈ halvesAt L m σ, gibbsWeight w β b : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (hD σ).ne'
  have hcast : ((∑ b ∈ halvesAt L m σ, gibbsWeight w β b : ℝ) : ℂ)
      = ∑ b ∈ halvesAt L m σ, ((gibbsWeight w β b : ℝ) : ℂ) := by
    push_cast
    rfl
  have hterm : ∀ a ∈ halvesAt L m σ,
      ((gibbsWeight w β a : ℝ) : ℂ) * (v (edgeOf a)
          / ((∑ b ∈ halvesAt L m (edgeOf a), gibbsWeight w β b : ℝ) : ℂ))
        = ((gibbsWeight w β a : ℝ) : ℂ) * v σ
            / ((∑ b ∈ halvesAt L m σ, gibbsWeight w β b : ℝ) : ℂ) := by
    intro a ha
    rw [mem_halvesAt.mp ha]
    ring
  calc ∑ a ∈ halvesAt L m σ, ((gibbsWeight w β a : ℝ) : ℂ) * (v (edgeOf a)
          / ((∑ b ∈ halvesAt L m (edgeOf a), gibbsWeight w β b : ℝ) : ℂ))
      = ∑ a ∈ halvesAt L m σ, ((gibbsWeight w β a : ℝ) : ℂ) * v σ
          / ((∑ b ∈ halvesAt L m σ, gibbsWeight w β b : ℝ) : ℂ) :=
        Finset.sum_congr rfl hterm
    _ = ((∑ a ∈ halvesAt L m σ, ((gibbsWeight w β a : ℝ) : ℂ)) * v σ)
          / ((∑ b ∈ halvesAt L m σ, gibbsWeight w β b : ℝ) : ℂ) := by
        rw [← Finset.sum_div, ← Finset.sum_mul]
    _ = v σ := by
        rw [← hcast]
        field_simp

/-! ## §5  The headline, read on the measure

The identities above are about boundary vectors.  Composed with the two bridges
of paper 13 they are about the Gibbs measure, which is the only reason they are
worth stating. -/

/-- **THE RECONSTRUCTION IDENTITY, ON THE MEASURE.**  Pairing an observable of
the past half-chain against the reflection of another one slice further away IS
applying `T` inside the physical inner product.  The left-hand side is the site
geometry and the right-hand side the bond geometry, and paper 13 identified both
with the Gibbs measure --- so this is a statement about the measure, not about
two forms standing in for it. -/
theorem osPairing_transfer {L : ℕ} {w : (Fin L → Fin 2) → ℝ}
    (hw : ∀ σ, 0 < w σ) (β : ℝ) (m : ℕ)
    (F G : (Fin (m + 1) → (Fin L → Fin 2)) → ℂ) :
    siteForm w (collapse w β m F) (transferOp w β (collapse w β m G))
      = osPairingBondCross w β m F G := by
  rw [siteForm_transferOp hw, bondForm_collapse]

/-- **AND THE SAME ON THE PATH SUM ITSELF.**  Substituting paper 13's bond
bridge on the right: the transfer operator's matrix element between two
half-chain observables is a sum over whole paths against the Gibbs weight. -/
theorem osPairing_transfer_gibbsSum {L : ℕ} {w : (Fin L → Fin 2) → ℝ}
    (hw : ∀ σ, 0 < w σ) (β : ℝ) (m : ℕ)
    (F : (Fin (m + 1) → (Fin L → Fin 2)) → ℂ) :
    siteForm w (collapse w β m F) (transferOp w β (collapse w β m F))
      = ∑ X : Fin ((m + 1) + (m + 1)) → (Fin L → Fin 2),
          (starRingEnd ℂ) (F (pastOf X)) * F (futRevOf X)
            * ((gibbsWeight w β (N := m + 1 + m) X : ℝ) : ℂ) := by
  rw [osPairing_transfer hw, osPairingBondCross_self,
    ← osPairingBond_eq_gibbsSum]

end YangMills.OS
