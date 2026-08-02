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

## What an external reading found, and what it changed

A reading of v1.0 pointed out, correctly, that four things the prose claimed
were not in the formal text: `T` was a bare function and not a linear map; its
uniqueness was asserted and not proved; the uniqueness argument needs the site
form to be DEFINITE while only NON-NEGATIVITY was available; and the quotient by
the null space was described rather than constructed.  It also observed that
gate R4 --- the spectrum of `T` --- is one line of algebra.

The first four are now theorems, in §6, §7 and §8: `siteForm_self_eq_zero_iff`,
`siteForm_right_ext`, `transferOp_unique`, `transferOpL`, and `physicalEquiv`
with `mem_ker_collapseL_iff`.

**R4 IS PARTLY, NOT WHOLLY, REPLACED, and the difference is stated because a
second reading found this very sentence overstating it.**  R4 asserted four
things: equality of eigenvalue LISTS entry by entry, reality of all of them,
agreement of MULTIPLICITIES, and the ratio of the largest modulus to the Perron
eigenvalue.  What §7b proves is that `Q` is a linear ISOMORPHISM, that
`T ∘ Q = Q ∘ S` as an equality of linear maps, and that the eigenvalue SETS
coincide in both directions with the non-vanishing carried across
(`transferOp_eigenvalue_iff`).  Multiplicities, characteristic polynomials,
ordered lists, reality, and the Perron ratio are NOT formalised here.  They
follow from a similarity with a real symmetric matrix by standard linear
algebra, and standard is not the same as present.

## What is NOT here

This paragraph said "no contraction bound" for several versions after the bound
was proved, which is the same defect as an overclaim with the sign reversed: a
module describing itself as weaker than it is.  What is actually here now:

* the EXACT physical operator norm is the Perron value, at every `β` ---
  `siteQ_transferOp_le` bounds it, `siteQ_transferOp_perron` attains it, and
  `perron_norm_constant_minimal` makes it minimal;
* for `β > 0` the operator is COERCIVE (`bondQ_ge_siteQ`), hence injective and
  invertible (`transferEquiv`), and the normalised operator is squeezed between
  a strictly positive scalar and the identity (`normalised_two_sided`).

What is genuinely NOT here: no Hamiltonian and no functional calculus ---
`H = -log(T/lam)` is now a meaningful object to SEEK, bounded, bounded away
from zero and invertible, but it is not built.  No spectral gap statement for
`T`.  No thermodynamic limit and no continuum.

**AT `β = 0`, and this sentence used to say "nothing", which contradicted the
sentence beside it claiming the exact norm at EVERY `β`.**  What is absent there,
and only for `L > 0`, is a strictly positive coercive lower bound, and with it
the invertible normalised operator and any route to a Hamiltonian.  What remains
is self-adjointness, semidefinite positivity, and the exact Perron norm with its
attainment and minimality.  At `L = 0` even injectivity remains, by a different
and simpler argument --- `transferOp_injective_zero_extent`, written because the
manuscript asserted it and the kernel did not.

And the mathematics is not new.  Reflection positivity for Ising-type measures,
through sites and through bonds, is classical --- Osterwalder--Schrader, and
Frohlich--Israel--Lieb--Simon; the transfer matrix of a finite spin chain is
older still.  What is new here is that these particular statements are
machine-checked, with the index bookkeeping of the two geometries done
explicitly rather than waved at.
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

/-! ## §6  Definiteness, and the uniqueness the headline needs

v1.0 said in prose that `T` is "not chosen but determined", and the formal text
did not contain it.  The only positivity statement was NON-NEGATIVITY, and a
form that is merely non-negative determines nothing: `⟨u, Sv⟩ = ⟨u, Tv⟩` for all
`u` gives `S = T` only if the form separates points.  An external reading was
right to call this out.  It is the same defect this lane has a name for --- the
prose outrunning the lemma --- one level below where it was last caught, and the
fix is to supply the missing chain rather than to soften the sentence. -/

/-- The physical inner product is additive in its second argument. -/
theorem siteForm_sub_right {L : ℕ} (w : (Fin L → Fin 2) → ℝ)
    (u x y : (Fin L → Fin 2) → ℂ) :
    siteForm w u (x - y) = siteForm w u x - siteForm w u y := by
  unfold siteForm
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun σ _ => ?_
  show (starRingEnd ℂ) (u σ) * (x σ - y σ) * ((1 / w σ : ℝ) : ℂ) = _
  ring

/-- The diagonal of the site form, as a real sum.  Extracted from the
non-negativity proof so that definiteness can use it too. -/
theorem siteForm_self_eq {L : ℕ} (w : (Fin L → Fin 2) → ℝ)
    (u : (Fin L → Fin 2) → ℂ) :
    siteForm w u u = ((∑ σ : Fin L → Fin 2, Complex.normSq (u σ) / w σ : ℝ) : ℂ) := by
  unfold siteForm
  push_cast
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [mul_comm ((starRingEnd ℂ) (u σ)) (u σ), Complex.mul_conj]
  push_cast
  ring

/-- **THE PHYSICAL INNER PRODUCT IS DEFINITE**, not merely non-negative.  This
is exactly what makes the defining equation an equation. -/
theorem siteForm_self_eq_zero_iff {L : ℕ} {w : (Fin L → Fin 2) → ℝ}
    (hw : ∀ σ, 0 < w σ) (u : (Fin L → Fin 2) → ℂ) :
    siteForm w u u = 0 ↔ u = 0 := by
  constructor
  · intro h
    rw [siteForm_self_eq] at h
    have hreal : (∑ σ : Fin L → Fin 2, Complex.normSq (u σ) / w σ) = 0 :=
      Complex.ofReal_eq_zero.mp h
    have hterm : ∀ σ : Fin L → Fin 2, Complex.normSq (u σ) / w σ = 0 := by
      intro σ
      have hnn : ∀ τ ∈ (Finset.univ : Finset (Fin L → Fin 2)),
          0 ≤ Complex.normSq (u τ) / w τ := fun τ _ =>
        div_nonneg (Complex.normSq_nonneg _) (hw τ).le
      exact (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hreal σ (Finset.mem_univ σ)
    funext σ
    have := hterm σ
    rw [div_eq_zero_iff] at this
    rcases this with h1 | h2
    · exact Complex.normSq_eq_zero.mp h1
    · exact absurd h2 (hw σ).ne'
  · intro h
    subst h
    unfold siteForm
    simp

/-- **SEPARATION.**  Two vectors pairing identically against everything are
equal.  Immediate from definiteness, and it is the step v1.0 skipped. -/
theorem siteForm_right_ext {L : ℕ} {w : (Fin L → Fin 2) → ℝ} (hw : ∀ σ, 0 < w σ)
    (x y : (Fin L → Fin 2) → ℂ)
    (h : ∀ u, siteForm w u x = siteForm w u y) : x = y := by
  have hz : siteForm w (x - y) (x - y) = 0 := by
    rw [siteForm_sub_right, h (x - y), sub_self]
  exact sub_eq_zero.mp ((siteForm_self_eq_zero_iff hw (x - y)).mp hz)

/-- **THE OPERATOR IS UNIQUE.**  Any `S` satisfying the defining equation IS
`transferOp`.  The claim that the operator is forced rather than chosen is this
theorem; without it the claim was a sentence. -/
theorem transferOp_unique {L : ℕ} {w : (Fin L → Fin 2) → ℝ} (hw : ∀ σ, 0 < w σ)
    (β : ℝ) (S : ((Fin L → Fin 2) → ℂ) → ((Fin L → Fin 2) → ℂ))
    (hS : ∀ u v, siteForm w u (S v) = bondForm β u v)
    (v : (Fin L → Fin 2) → ℂ) : S v = transferOp w β v := by
  refine siteForm_right_ext hw _ _ fun u => ?_
  rw [hS u v, siteForm_transferOp hw]

/-! ## §7  The operator as a linear map, and its spectrum

Two more things v1.0 asserted without carrying: that `T` is an operator (it was
a bare function), and that its spectrum is the one this lane already knows (that
was gate R4, registered before the fact and cited in no proof).

The first is fixed here.  The second is fixed only in PART, and §7b says which
part: the SIMILARITY and the equality of eigenvalue SETS become theorems;
multiplicities, characteristic polynomials, ordered lists, reality and the
Perron ratio do not.  An earlier draft of this very paragraph said "so it is a
theorem here", which identified one line of algebra with the whole of R4.  It
was wrong in the direction this file exists to avoid. -/

theorem transferOp_add {L : ℕ} (w : (Fin L → Fin 2) → ℝ) (β : ℝ)
    (x y : (Fin L → Fin 2) → ℂ) :
    transferOp w β (x + y) = transferOp w β x + transferOp w β y := by
  funext σ
  show ((w σ : ℝ) : ℂ) * ∑ τ : Fin L → Fin 2,
        ((spatialKernel β σ τ : ℝ) : ℂ) * (x τ + y τ)
      = ((w σ : ℝ) : ℂ) * (∑ τ : Fin L → Fin 2,
          ((spatialKernel β σ τ : ℝ) : ℂ) * x τ)
        + ((w σ : ℝ) : ℂ) * ∑ τ : Fin L → Fin 2,
          ((spatialKernel β σ τ : ℝ) : ℂ) * y τ
  rw [← mul_add, ← Finset.sum_add_distrib]
  exact congrArg _ (Finset.sum_congr rfl fun τ _ => by ring)

theorem transferOp_smul {L : ℕ} (w : (Fin L → Fin 2) → ℝ) (β : ℝ) (c : ℂ)
    (x : (Fin L → Fin 2) → ℂ) :
    transferOp w β (c • x) = c • transferOp w β x := by
  funext σ
  show ((w σ : ℝ) : ℂ) * ∑ τ : Fin L → Fin 2,
        ((spatialKernel β σ τ : ℝ) : ℂ) * (c * x τ)
      = c * (((w σ : ℝ) : ℂ) * ∑ τ : Fin L → Fin 2,
          ((spatialKernel β σ τ : ℝ) : ℂ) * x τ)
  have hstep : ∀ τ : Fin L → Fin 2,
      ((spatialKernel β σ τ : ℝ) : ℂ) * (c * x τ)
        = c * (((spatialKernel β σ τ : ℝ) : ℂ) * x τ) := fun τ => by ring
  rw [Finset.sum_congr rfl fun τ (_ : τ ∈ Finset.univ) => hstep τ,
    ← Finset.mul_sum]
  ring

/-- **THE TRANSFER OPERATOR, AS AN OPERATOR.**  `transferOp` packaged as a
`ℂ`-linear map, so that the word is a type and not a manner of speaking. -/
noncomputable def transferOpL {L : ℕ} (w : (Fin L → Fin 2) → ℝ) (β : ℝ) :
    ((Fin L → Fin 2) → ℂ) →ₗ[ℂ] ((Fin L → Fin 2) → ℂ) where
  toFun := transferOp w β
  map_add' := transferOp_add w β
  map_smul' c x := transferOp_smul w β c x

@[simp] theorem transferOpL_apply {L : ℕ} (w : (Fin L → Fin 2) → ℝ) (β : ℝ)
    (v : (Fin L → Fin 2) → ℂ) : transferOpL w β v = transferOp w β v := rfl

/-- The real identity behind the conjugation: one factor of `√w` moves from the
weight onto the kernel. -/
theorem sqrtw_kernel_mul {L : ℕ} {w : (Fin L → Fin 2) → ℝ} (hw : ∀ σ, 0 ≤ w σ)
    (β : ℝ) (σ τ : Fin L → Fin 2) :
    w σ * (spatialKernel β σ τ * Real.sqrt (w τ))
      = Real.sqrt (w σ) * symWeighted w β σ τ := by
  have h : Real.sqrt (w σ) * Real.sqrt (w σ) = w σ := Real.mul_self_sqrt (hw σ)
  unfold symWeighted
  linear_combination (-(spatialKernel β σ τ * Real.sqrt (w τ))) * h

/-- **THE CONJUGATION.**  `T ∘ (√w ·) = (√w ·) ∘ S`, where `S` is the
symmetrised kernel of this lane's Perron and gap results.  Division-free, so it
needs only `w ≥ 0`.

Deliberately NOT "everything about the spectrum follows from it", which is what
this docstring said first.  Mathematically the standard consequences do follow;
formally, what follows IN THIS FILE is §7b's similarity and equality of
eigenvalue sets, and nothing else.  The two registers are exactly what the rest
of this module refuses to confuse. -/
theorem transferOp_sqrtw {L : ℕ} {w : (Fin L → Fin 2) → ℝ} (hw : ∀ σ, 0 ≤ w σ)
    (β : ℝ) (u : (Fin L → Fin 2) → ℂ) (σ : Fin L → Fin 2) :
    transferOp w β (fun τ => ((Real.sqrt (w τ) : ℝ) : ℂ) * u τ) σ
      = ((Real.sqrt (w σ) : ℝ) : ℂ)
          * ∑ τ : Fin L → Fin 2, ((symWeighted w β σ τ : ℝ) : ℂ) * u τ := by
  show ((w σ : ℝ) : ℂ) * ∑ τ : Fin L → Fin 2, ((spatialKernel β σ τ : ℝ) : ℂ)
      * (((Real.sqrt (w τ) : ℝ) : ℂ) * u τ) = _
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have hc := congrArg (fun r : ℝ => (r : ℂ)) (sqrtw_kernel_mul hw β σ τ)
  push_cast at hc ⊢
  linear_combination u τ * hc

/-- **ONE DIRECTION OF THE EIGEN-EQUATION.**  Note what this is NOT: it does not
require `u ≠ 0`, so at `u = 0` its hypothesis holds for every `lam` and it says
nothing; it assumes only `w ≥ 0`, so the map carrying `u` across need not be
injective; and it has no converse.  It is a forward implication, and §7b is what
turns it into a statement about spectra. -/
theorem transferOp_eigen_of_symWeighted {L : ℕ} {w : (Fin L → Fin 2) → ℝ}
    (hw : ∀ σ, 0 ≤ w σ) (β : ℝ) (u : (Fin L → Fin 2) → ℂ) (lam : ℂ)
    (hu : ∀ σ, (∑ τ : Fin L → Fin 2, ((symWeighted w β σ τ : ℝ) : ℂ) * u τ)
        = lam * u σ) (σ : Fin L → Fin 2) :
    transferOp w β (fun τ => ((Real.sqrt (w τ) : ℝ) : ℂ) * u τ) σ
      = lam * (((Real.sqrt (w σ) : ℝ) : ℂ) * u σ) := by
  rw [transferOp_sqrtw hw β u σ, hu σ]
  ring

/-! ### §7b  The similarity, and what it does and does not give

A second external reading pointed out that the intertwining above is still not
what gate R4 claimed.  R4 asserted equality of eigenvalue LISTS, reality of all
of them, ordering with multiplicity, and the ratio to the Perron eigenvalue.
`transferOp_sqrtw` gives `T ∘ Q = Q ∘ S`; `transferOp_eigen_of_symWeighted`
gives a forward implication that is vacuous at `u = 0`.  Between those and "the
spectrum transports" there is a gap, and the honest response is to close it
rather than to keep the sentence.

What is proved here: `Q` is an ISOMORPHISM when `w > 0`, the intertwining is an
equality of LINEAR MAPS, and consequently the sets of eigenvalues coincide in
BOTH directions with the non-vanishing carried across.

What is still NOT proved, and is stated rather than implied: equality of
multiplicities, of characteristic polynomials, or of ordered eigenvalue lists.
Those follow from a similarity by standard linear algebra; standard is not the
same as present. -/

/-- Multiplication by `√w`, as a linear ISOMORPHISM.  Strict positivity of `w`
is exactly what makes it invertible, and invertibility is what the forward
implication above lacked. -/
noncomputable def sqrtWeightEquiv {L : ℕ} (w : (Fin L → Fin 2) → ℝ)
    (hw : ∀ σ, 0 < w σ) :
    ((Fin L → Fin 2) → ℂ) ≃ₗ[ℂ] ((Fin L → Fin 2) → ℂ) where
  toFun u := fun σ => ((Real.sqrt (w σ) : ℝ) : ℂ) * u σ
  map_add' u v := by
    funext σ
    simp only [Pi.add_apply]
    ring
  map_smul' c u := by
    funext σ
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring
  invFun v := fun σ => v σ / ((Real.sqrt (w σ) : ℝ) : ℂ)
  left_inv u := by
    funext σ
    have h : ((Real.sqrt (w σ) : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (hw σ)).ne'
    field_simp
  right_inv v := by
    funext σ
    have h : ((Real.sqrt (w σ) : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (hw σ)).ne'
    field_simp

@[simp] theorem sqrtWeightEquiv_apply {L : ℕ} (w : (Fin L → Fin 2) → ℝ)
    (hw : ∀ σ, 0 < w σ) (u : (Fin L → Fin 2) → ℂ) (σ : Fin L → Fin 2) :
    sqrtWeightEquiv w hw u σ = ((Real.sqrt (w σ) : ℝ) : ℂ) * u σ := rfl

/-- The symmetrised kernel, acting on complex boundary vectors. -/
noncomputable def symWeightedOp {L : ℕ} (w : (Fin L → Fin 2) → ℝ) (β : ℝ)
    (u : (Fin L → Fin 2) → ℂ) : (Fin L → Fin 2) → ℂ :=
  fun σ => ∑ τ : Fin L → Fin 2, ((symWeighted w β σ τ : ℝ) : ℂ) * u τ

theorem symWeightedOp_add {L : ℕ} (w : (Fin L → Fin 2) → ℝ) (β : ℝ)
    (x y : (Fin L → Fin 2) → ℂ) :
    symWeightedOp w β (x + y) = symWeightedOp w β x + symWeightedOp w β y := by
  funext σ
  show (∑ τ : Fin L → Fin 2, ((symWeighted w β σ τ : ℝ) : ℂ) * (x τ + y τ))
      = (∑ τ : Fin L → Fin 2, ((symWeighted w β σ τ : ℝ) : ℂ) * x τ)
        + ∑ τ : Fin L → Fin 2, ((symWeighted w β σ τ : ℝ) : ℂ) * y τ
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun τ _ => by ring

theorem symWeightedOp_smul {L : ℕ} (w : (Fin L → Fin 2) → ℝ) (β : ℝ) (c : ℂ)
    (x : (Fin L → Fin 2) → ℂ) :
    symWeightedOp w β (c • x) = c • symWeightedOp w β x := by
  funext σ
  show (∑ τ : Fin L → Fin 2, ((symWeighted w β σ τ : ℝ) : ℂ) * (c * x τ))
      = c * ∑ τ : Fin L → Fin 2, ((symWeighted w β σ τ : ℝ) : ℂ) * x τ
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun τ _ => by ring

/-- The symmetrised kernel as a linear map. -/
noncomputable def symWeightedOpL {L : ℕ} (w : (Fin L → Fin 2) → ℝ) (β : ℝ) :
    ((Fin L → Fin 2) → ℂ) →ₗ[ℂ] ((Fin L → Fin 2) → ℂ) where
  toFun := symWeightedOp w β
  map_add' := symWeightedOp_add w β
  map_smul' c x := symWeightedOp_smul w β c x

/-- **THE INTERTWINING, POINTWISE.**  `T (Q u) = Q (S u)`. -/
theorem transferOp_sqrtWeightEquiv {L : ℕ} {w : (Fin L → Fin 2) → ℝ}
    (hw : ∀ σ, 0 < w σ) (β : ℝ) (u : (Fin L → Fin 2) → ℂ) :
    transferOp w β (sqrtWeightEquiv w hw u)
      = sqrtWeightEquiv w hw (symWeightedOp w β u) := by
  funext σ
  exact transferOp_sqrtw (fun σ => (hw σ).le) β u σ

/-- **THE SIMILARITY, AS AN EQUALITY OF LINEAR MAPS**, with `Q` an isomorphism.
This --- and not the forward implication of §7 --- is what determines the
spectrum. -/
theorem transferOpL_comp_sqrtWeightEquiv {L : ℕ} {w : (Fin L → Fin 2) → ℝ}
    (hw : ∀ σ, 0 < w σ) (β : ℝ) :
    (transferOpL w β).comp (sqrtWeightEquiv w hw).toLinearMap
      = ((sqrtWeightEquiv w hw).toLinearMap).comp (symWeightedOpL w β) :=
  LinearMap.ext fun u => transferOp_sqrtWeightEquiv hw β u

/-- **THE EIGENVALUE SETS COINCIDE**, in both directions, with `u ≠ 0` carried
across by the isomorphism.  This is the part of gate R4 that is now a theorem;
multiplicities and characteristic polynomials are not. -/
theorem transferOp_eigenvalue_iff {L : ℕ} {w : (Fin L → Fin 2) → ℝ}
    (hw : ∀ σ, 0 < w σ) (β : ℝ) (lam : ℂ) :
    (∃ u ≠ 0, symWeightedOp w β u = lam • u)
      ↔ ∃ v ≠ 0, transferOp w β v = lam • v := by
  constructor
  · rintro ⟨u, hu0, hu⟩
    refine ⟨sqrtWeightEquiv w hw u, ?_, ?_⟩
    · exact fun h => hu0 ((sqrtWeightEquiv w hw).map_eq_zero_iff.mp h)
    · rw [transferOp_sqrtWeightEquiv hw β u, hu, map_smul]
  · rintro ⟨v, hv0, hv⟩
    refine ⟨(sqrtWeightEquiv w hw).symm v, ?_, ?_⟩
    · exact fun h => hv0 ((sqrtWeightEquiv w hw).symm.map_eq_zero_iff.mp h)
    · have hQ : sqrtWeightEquiv w hw ((sqrtWeightEquiv w hw).symm v) = v :=
        (sqrtWeightEquiv w hw).apply_symm_apply v
      have hstep := transferOp_sqrtWeightEquiv hw β ((sqrtWeightEquiv w hw).symm v)
      rw [hQ, hv] at hstep
      refine (sqrtWeightEquiv w hw).injective ?_
      rw [map_smul, hQ]
      exact hstep.symm

/-! ### §7c  THE CONTRACTION, WITH THE SHARP CONSTANT

Everything above says `T` is self-adjoint and positive and leaves its size
unknown; three readings in a row listed "no contraction bound" as the first
open item, and it is the one that stands between this operator and a
Hamiltonian.  It is closed here, and with the SHARP constant rather than a
lossy row-sum majorant.

The argument uses no spectral theory.  For a symmetric matrix with non-negative
entries possessing a strictly positive eigenvector `Ω` at eigenvalue `lam`,

    2 x_i x_j  ≤  (Ω_j/Ω_i) x_i²  +  (Ω_i/Ω_j) x_j²,

which is `(Ω_j x_i - Ω_i x_j)² ≥ 0` divided by `Ω_i Ω_j`.  Summing against `A`
and folding the two halves together by symmetry gives

    ∑ᵢⱼ Aᵢⱼ xᵢ xⱼ  ≤  ∑ᵢ (xᵢ²/Ωᵢ) ∑ⱼ Aᵢⱼ Ωⱼ  =  lam ∑ᵢ xᵢ² ,

the eigenvector equation collapsing the inner sum exactly.  The Perron vector
is not used as a bound; it is used as the WEIGHT that makes the elementary
inequality tight, which is why the constant comes out sharp and is attained.
-/

/-- The elementary inequality the whole bound rests on: `(b s - a t)² ≥ 0`,
divided by `a b`. -/
theorem two_mul_le_weighted {a b s t : ℝ} (ha : 0 < a) (hb : 0 < b) :
    2 * (s * t) ≤ (b / a) * s ^ 2 + (a / b) * t ^ 2 := by
  have hab : 0 < a * b := mul_pos ha hb
  have hid : (b / a) * s ^ 2 + (a / b) * t ^ 2 - 2 * (s * t)
      = (b * s - a * t) ^ 2 / (a * b) := by
    field_simp
    ring
  nlinarith [div_nonneg (sq_nonneg (b * s - a * t)) hab.le, hid]

/-- **THE SHARP PERRON BOUND, GENERICALLY.**  A symmetric non-negative matrix
with a strictly positive eigenvector has quadratic form bounded by its
eigenvalue.  Nothing here is special to this model, and no spectral theory is
used --- only the eigenvector equation and one square. -/
theorem quad_le_perron {ι : Type*} [Fintype ι] {A : ι → ι → ℝ}
    (hsym : ∀ i j, A i j = A j i) (hA : ∀ i j, 0 ≤ A i j)
    {Ω : ι → ℝ} (hΩ : ∀ i, 0 < Ω i) {lam : ℝ}
    (heig : ∀ i, (∑ j, A i j * Ω j) = lam * Ω i) (x : ι → ℝ) :
    (∑ i, ∑ j, A i j * (x i * x j)) ≤ lam * ∑ i, x i ^ 2 := by
  classical
  set M : ι → ι → ℝ := fun i j => A i j * ((Ω j / Ω i) * x i ^ 2) with hM
  have hterm : ∀ i j, A i j * (x i * x j) ≤ (M i j + M j i) / 2 := by
    intro i j
    have h := two_mul_le_weighted (a := Ω i) (b := Ω j) (s := x i) (t := x j)
      (hΩ i) (hΩ j)
    have hMij : M i j = A i j * ((Ω j / Ω i) * x i ^ 2) := rfl
    have hMji : M j i = A j i * ((Ω i / Ω j) * x j ^ 2) := rfl
    rw [hMij, hMji, hsym j i]
    nlinarith [hA i j, h]
  have hle : (∑ i, ∑ j, A i j * (x i * x j))
      ≤ ∑ i, ∑ j, (M i j + M j i) / 2 :=
    Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
  have hswap : (∑ i, ∑ j, M j i) = ∑ i, ∑ j, M i j := Finset.sum_comm
  have hhalf : (∑ i, ∑ j, (M i j + M j i) / 2) = ∑ i, ∑ j, M i j := by
    have e1 : (∑ i, ∑ j, (M i j + M j i) / 2)
        = (∑ i, ∑ j, M i j / 2) + ∑ i, ∑ j, M j i / 2 := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    have e2 : (∑ i, ∑ j, M j i / 2) = ∑ i, ∑ j, M i j / 2 := Finset.sum_comm
    rw [e1, e2, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hrow : ∀ i, (∑ j, M i j) = lam * x i ^ 2 := by
    intro i
    have hi : (Ω i) ≠ 0 := (hΩ i).ne'
    have hpull : (∑ j, M i j) = (∑ j, A i j * Ω j) * (x i ^ 2 / Ω i) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      show A i j * ((Ω j / Ω i) * x i ^ 2) = A i j * Ω j * (x i ^ 2 / Ω i)
      field_simp
    rw [hpull, heig i]
    field_simp
  calc (∑ i, ∑ j, A i j * (x i * x j))
      ≤ ∑ i, ∑ j, (M i j + M j i) / 2 := hle
    _ = ∑ i, ∑ j, M i j := hhalf
    _ = ∑ i, lam * x i ^ 2 := Finset.sum_congr rfl fun i _ => hrow i
    _ = lam * ∑ i, x i ^ 2 := by rw [Finset.mul_sum]

/-! The two real quadratic forms, so the bound can be stated as an inequality
between real numbers rather than as an existential over `ℂ`. -/

/-- The physical squared norm, as a real number. -/
noncomputable def siteQ {L : ℕ} (w : (Fin L → Fin 2) → ℝ)
    (u : (Fin L → Fin 2) → ℂ) : ℝ :=
  ∑ σ : Fin L → Fin 2, Complex.normSq (u σ) / w σ

/-- The bond quadratic form, as a real number: the two real forms the
real-to-complex step produces. -/
noncomputable def bondQ {L : ℕ} (β : ℝ) (u : (Fin L → Fin 2) → ℂ) : ℝ :=
  (∑ σ : Fin L → Fin 2, ∑ τ : Fin L → Fin 2,
      spatialKernel β σ τ * ((u σ).re * (u τ).re))
    + ∑ σ : Fin L → Fin 2, ∑ τ : Fin L → Fin 2,
      spatialKernel β σ τ * ((u σ).im * (u τ).im)

theorem siteForm_self_eq_siteQ {L : ℕ} (w : (Fin L → Fin 2) → ℝ)
    (u : (Fin L → Fin 2) → ℂ) : siteForm w u u = ((siteQ w u : ℝ) : ℂ) :=
  siteForm_self_eq w u

theorem bondForm_self_eq_bondQ {L : ℕ} (β : ℝ) (u : (Fin L → Fin 2) → ℂ) :
    bondForm β u u = ((bondQ β u : ℝ) : ℂ) := by
  unfold bondForm bondQ
  rw [complexQuad_eq (spatialKernel_symm β) u]

/-- One half of the transport: the symmetrised form at `u/√w` IS the bond form
at `u`.  Stated for a real vector, which is all the bound needs. -/
theorem symWeighted_quad_transport {L : ℕ} {w : (Fin L → Fin 2) → ℝ}
    (hw : ∀ σ, 0 < w σ) (β : ℝ) (y : (Fin L → Fin 2) → ℝ) :
    (∑ σ : Fin L → Fin 2, ∑ τ : Fin L → Fin 2,
        symWeighted w β σ τ * ((y σ / Real.sqrt (w σ)) * (y τ / Real.sqrt (w τ))))
      = ∑ σ : Fin L → Fin 2, ∑ τ : Fin L → Fin 2,
          spatialKernel β σ τ * (y σ * y τ) := by
  refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun τ _ => ?_
  have hs : Real.sqrt (w σ) ≠ 0 := (Real.sqrt_pos.mpr (hw σ)).ne'
  have ht : Real.sqrt (w τ) ≠ 0 := (Real.sqrt_pos.mpr (hw τ)).ne'
  -- both sides carry the SAME divisions, so the first step is pure `ring` and
  -- only the two cancellations need a field fact.  `field_simp` on the whole
  -- identity at once left a goal `ring` could not normalise.
  have cσ : Real.sqrt (w σ) * (y σ / Real.sqrt (w σ)) = y σ := by field_simp
  have cτ : Real.sqrt (w τ) * (y τ / Real.sqrt (w τ)) = y τ := by field_simp
  calc symWeighted w β σ τ * ((y σ / Real.sqrt (w σ)) * (y τ / Real.sqrt (w τ)))
      = spatialKernel β σ τ * ((Real.sqrt (w σ) * (y σ / Real.sqrt (w σ)))
          * (Real.sqrt (w τ) * (y τ / Real.sqrt (w τ)))) := by
        unfold symWeighted
        ring
    _ = spatialKernel β σ τ * (y σ * y τ) := by rw [cσ, cτ]

theorem sq_div_sqrt {L : ℕ} {w : (Fin L → Fin 2) → ℝ} (hw : ∀ σ, 0 < w σ)
    (y : (Fin L → Fin 2) → ℝ) (σ : Fin L → Fin 2) :
    (y σ / Real.sqrt (w σ)) ^ 2 = y σ ^ 2 / w σ := by
  rw [div_pow, Real.sq_sqrt (hw σ).le]

/-- **THE TRANSFER OPERATOR IS A CONTRACTION, WITH THE SHARP CONSTANT.**  For
any strictly positive eigenvector `Ω` of the symmetrised kernel at eigenvalue
`lam` --- the Perron data this lane already constructs ---

    ⟨u, T u⟩_site  ≤  lam · ⟨u, u⟩_site

for every complex boundary vector.  So `T/lam` is a self-adjoint positive
contraction, which is what an Osterwalder--Schrader transfer operator is asked
to be before a Hamiltonian can be taken. -/
theorem transferOp_le_perron {L : ℕ} {w : (Fin L → Fin 2) → ℝ}
    (hw : ∀ σ, 0 < w σ) (β : ℝ) {Ω : (Fin L → Fin 2) → ℝ}
    (hΩ : ∀ σ, 0 < Ω σ) {lam : ℝ}
    (heig : ∀ σ, (∑ τ : Fin L → Fin 2, symWeighted w β σ τ * Ω τ) = lam * Ω σ)
    (u : (Fin L → Fin 2) → ℂ) :
    bondQ β u ≤ lam * siteQ w u := by
  have hsym : ∀ σ τ : Fin L → Fin 2,
      symWeighted w β σ τ = symWeighted w β τ σ := symWeighted_symm w β
  have hpart : ∀ y : (Fin L → Fin 2) → ℝ,
      (∑ σ : Fin L → Fin 2, ∑ τ : Fin L → Fin 2,
          spatialKernel β σ τ * (y σ * y τ))
        ≤ lam * ∑ σ : Fin L → Fin 2, y σ ^ 2 / w σ := by
    intro y
    have hgen := quad_le_perron hsym
      (fun σ τ => (symWeighted_pos hw β σ τ).le) hΩ heig
      (fun σ => y σ / Real.sqrt (w σ))
    rw [symWeighted_quad_transport hw β y] at hgen
    have hnorm : (∑ σ : Fin L → Fin 2, (y σ / Real.sqrt (w σ)) ^ 2)
        = ∑ σ : Fin L → Fin 2, y σ ^ 2 / w σ :=
      Finset.sum_congr rfl fun σ _ => sq_div_sqrt hw y σ
    rw [hnorm] at hgen
    exact hgen
  have hre := hpart (fun σ => (u σ).re)
  have him := hpart (fun σ => (u σ).im)
  have hsplit : lam * siteQ w u
      = lam * (∑ σ : Fin L → Fin 2, (u σ).re ^ 2 / w σ)
        + lam * ∑ σ : Fin L → Fin 2, (u σ).im ^ 2 / w σ := by
    unfold siteQ
    rw [← mul_add, ← Finset.sum_add_distrib]
    refine congrArg _ (Finset.sum_congr rfl fun σ _ => ?_)
    rw [Complex.normSq_apply]
    field_simp
  unfold bondQ
  rw [hsplit]
  exact add_le_add hre him

/-- **AND THE CONSTANT IS ATTAINED**, so it is the sharp one and not merely an
upper bound: at the vector `√w · Ω` the inequality is an equality. -/
theorem transferOp_perron_attained {L : ℕ} {w : (Fin L → Fin 2) → ℝ}
    (hw : ∀ σ, 0 < w σ) (β : ℝ) {Ω : (Fin L → Fin 2) → ℝ}
    (hΩ : ∀ σ, 0 < Ω σ) {lam : ℝ}
    (heig : ∀ σ, (∑ τ : Fin L → Fin 2, symWeighted w β σ τ * Ω τ) = lam * Ω σ) :
    bondQ β (fun σ => ((Real.sqrt (w σ) * Ω σ : ℝ) : ℂ))
      = lam * siteQ w (fun σ => ((Real.sqrt (w σ) * Ω σ : ℝ) : ℂ)) := by
  set y : (Fin L → Fin 2) → ℝ := fun σ => Real.sqrt (w σ) * Ω σ with hy
  have hre : ∀ σ, (((y σ : ℝ) : ℂ)).re = y σ := fun σ => Complex.ofReal_re _
  have him : ∀ σ, (((y σ : ℝ) : ℂ)).im = 0 := fun σ => Complex.ofReal_im _
  have hquad : (∑ σ : Fin L → Fin 2, ∑ τ : Fin L → Fin 2,
      spatialKernel β σ τ * (y σ * y τ)) = lam * ∑ σ : Fin L → Fin 2, Ω σ ^ 2 := by
    have hstep : ∀ σ : Fin L → Fin 2,
        (∑ τ : Fin L → Fin 2, spatialKernel β σ τ * (y σ * y τ))
          = Ω σ * (lam * Ω σ) := by
      intro σ
      rw [← heig σ, Finset.mul_sum]
      refine Finset.sum_congr rfl fun τ _ => ?_
      unfold symWeighted
      rw [hy]
      ring
    rw [Finset.sum_congr rfl fun σ (_ : σ ∈ Finset.univ) => hstep σ,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun σ _ => by ring
  have hnorm : (∑ σ : Fin L → Fin 2,
      Complex.normSq (((y σ : ℝ) : ℂ)) / w σ) = ∑ σ : Fin L → Fin 2, Ω σ ^ 2 := by
    refine Finset.sum_congr rfl fun σ _ => ?_
    have hsq : Real.sqrt (w σ) * Real.sqrt (w σ) = w σ :=
      Real.mul_self_sqrt (hw σ).le
    have hwne : w σ ≠ 0 := (hw σ).ne'
    rw [Complex.normSq_apply, hre σ, him σ, hy]
    -- (√w Ω)·(√w Ω) + 0·0 all over w  is  Ω², and the only fact needed is
    -- √w·√w = w; `field_simp` alone left a goal `ring` could not normalise, so
    -- the cancellation is done as a linear combination of that single fact.
    rw [div_eq_iff hwne]
    linear_combination (Ω σ ^ 2) * hsq
  unfold bondQ siteQ
  rw [hnorm]
  have hzero : (∑ σ : Fin L → Fin 2, ∑ τ : Fin L → Fin 2,
      spatialKernel β σ τ * ((((y σ : ℝ) : ℂ)).im * (((y τ : ℝ) : ℂ)).im)) = 0 := by
    refine Finset.sum_eq_zero fun σ _ => Finset.sum_eq_zero fun τ _ => ?_
    rw [him σ, him τ]
    ring
  rw [hzero, add_zero]
  rw [Finset.sum_congr rfl fun σ (_ : σ ∈ Finset.univ) =>
    Finset.sum_congr rfl fun τ (_ : τ ∈ Finset.univ) =>
      (by rw [hre σ, hre τ] :
        spatialKernel β σ τ * ((((y σ : ℝ) : ℂ)).re * (((y τ : ℝ) : ℂ)).re)
          = spatialKernel β σ τ * (y σ * y τ))]
  exact hquad

/-! #### The NORM inequality, which the quadratic bound does not by itself give

A bound on `⟨u, A u⟩` is not a bound on `‖A u‖`.  For `β ≥ 0` the two are
equivalent by `0 ≤ T ≤ lam·I` and standard finite-dimensional arguments, but
standard is not present, and at `β < 0` positivity is unavailable so the
equivalence is not even available to quote.  So the norm bound is proved
directly, by one more weighted Cauchy--Schwarz with the same Perron weight:

    (A x)ᵢ²  =  (∑ⱼ √(Aᵢⱼ Ωⱼ) · √(Aᵢⱼ/Ωⱼ) xⱼ)²
             ≤  (∑ⱼ Aᵢⱼ Ωⱼ)(∑ⱼ Aᵢⱼ xⱼ²/Ωⱼ)  =  lam Ωᵢ ∑ⱼ Aᵢⱼ xⱼ²/Ωⱼ ,

and summing over `i`, using symmetry once and the eigenvector equation a second
time, gives `‖A x‖² ≤ lam² ‖x‖²` --- with equality at `x = Ω`.  No spectral
theory and no restriction on the sign of `β`.

"No positivity" here means no OPERATOR semidefiniteness hypothesis: nothing like
`0 ≤ T` is assumed, which is why the bound survives at `β < 0` where
`transferOp_nonneg` does not apply.  Entrywise non-negativity `0 ≤ A i j` IS
essential and is carried as `hA`; an external reading was right that the
unqualified phrase claimed more than the proof uses. -/

theorem norm_sq_le_perron {ι : Type*} [Fintype ι] {A : ι → ι → ℝ}
    (hsym : ∀ i j, A i j = A j i) (hA : ∀ i j, 0 ≤ A i j)
    {Ω : ι → ℝ} (hΩ : ∀ i, 0 < Ω i) {lam : ℝ}
    (heig : ∀ i, (∑ j, A i j * Ω j) = lam * Ω i) (x : ι → ℝ) :
    (∑ i, (∑ j, A i j * x j) ^ 2) ≤ lam ^ 2 * ∑ i, x i ^ 2 := by
  classical
  have hstep : ∀ i, (∑ j, A i j * x j) ^ 2
      ≤ (lam * Ω i) * ∑ j, A i j * x j ^ 2 / Ω j := by
    intro i
    have hfg : ∀ j, Real.sqrt (A i j * Ω j)
        * (Real.sqrt (A i j / Ω j) * x j) = A i j * x j := by
      intro j
      have hAΩ : (0:ℝ) ≤ A i j * Ω j := mul_nonneg (hA i j) (hΩ j).le
      have hsq : A i j * Ω j * (A i j / Ω j) = A i j ^ 2 := by
        have : Ω j ≠ 0 := (hΩ j).ne'
        field_simp
      have hprod : Real.sqrt (A i j * Ω j) * Real.sqrt (A i j / Ω j) = A i j := by
        rw [← Real.sqrt_mul hAΩ, hsq, Real.sqrt_sq (hA i j)]
      rw [← mul_assoc, hprod]
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun j => Real.sqrt (A i j * Ω j))
      (fun j => Real.sqrt (A i j / Ω j) * x j)
    rw [Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => hfg j] at hcs
    have hf2 : (∑ j, Real.sqrt (A i j * Ω j) ^ 2) = lam * Ω i := by
      rw [← heig i]
      exact Finset.sum_congr rfl fun j _ =>
        Real.sq_sqrt (mul_nonneg (hA i j) (hΩ j).le)
    have hg2 : (∑ j, (Real.sqrt (A i j / Ω j) * x j) ^ 2)
        = ∑ j, A i j * x j ^ 2 / Ω j := by
      refine Finset.sum_congr rfl fun j _ => ?_
      have hdiv : (0:ℝ) ≤ A i j / Ω j := div_nonneg (hA i j) (hΩ j).le
      rw [mul_pow, Real.sq_sqrt hdiv]
      have : Ω j ≠ 0 := (hΩ j).ne'
      field_simp
    rw [hf2, hg2] at hcs
    exact hcs
  have hsum : (∑ i, (lam * Ω i) * ∑ j, A i j * x j ^ 2 / Ω j)
      = lam ^ 2 * ∑ i, x i ^ 2 := by
    have hexp : (∑ i, (lam * Ω i) * ∑ j, A i j * x j ^ 2 / Ω j)
        = ∑ i, ∑ j, lam * (Ω i * A i j * (x j ^ 2 / Ω j)) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      field_simp
    rw [hexp, Finset.sum_comm]
    have hinner : ∀ j, (∑ i, lam * (Ω i * A i j * (x j ^ 2 / Ω j)))
        = lam ^ 2 * x j ^ 2 := by
      intro j
      have hj : Ω j ≠ 0 := (hΩ j).ne'
      have hcol : (∑ i, lam * (Ω i * A i j * (x j ^ 2 / Ω j)))
          = lam * (x j ^ 2 / Ω j) * ∑ i, A j i * Ω i := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hsym i j]
        ring
      rw [hcol, heig j]
      field_simp
    rw [Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => hinner j,
      ← Finset.mul_sum]
  calc (∑ i, (∑ j, A i j * x j) ^ 2)
      ≤ ∑ i, (lam * Ω i) * ∑ j, A i j * x j ^ 2 / Ω j :=
        Finset.sum_le_sum fun i _ => hstep i
    _ = lam ^ 2 * ∑ i, x i ^ 2 := hsum

/-- **THE NORM BOUND FOR THE TRANSFER OPERATOR.**  `‖T u‖² ≤ lam² ‖u‖²` in the
physical inner product, at EVERY `β` --- positivity is not used, so this holds
where `transferOp_nonneg` does not.  With it, `T/lam` is a contraction as a
statement about norms and not only about a quadratic form. -/
theorem siteQ_transferOp_le {L : ℕ} {w : (Fin L → Fin 2) → ℝ}
    (hw : ∀ σ, 0 < w σ) (β : ℝ) {Ω : (Fin L → Fin 2) → ℝ}
    (hΩ : ∀ σ, 0 < Ω σ) {lam : ℝ}
    (heig : ∀ σ, (∑ τ : Fin L → Fin 2, symWeighted w β σ τ * Ω τ) = lam * Ω σ)
    (u : (Fin L → Fin 2) → ℂ) :
    siteQ w (transferOp w β u) ≤ lam ^ 2 * siteQ w u := by
  classical
  have hsym : ∀ σ τ : Fin L → Fin 2,
      symWeighted w β σ τ = symWeighted w β τ σ := symWeighted_symm w β
  have hAnn : ∀ σ τ : Fin L → Fin 2, (0:ℝ) ≤ symWeighted w β σ τ :=
    fun σ τ => (symWeighted_pos hw β σ τ).le
  -- the diagonal transport, on one real component
  have hcomp : ∀ y : (Fin L → Fin 2) → ℝ, ∀ σ : Fin L → Fin 2,
      (w σ * ∑ τ : Fin L → Fin 2, spatialKernel β σ τ * y τ) / Real.sqrt (w σ)
        = ∑ τ : Fin L → Fin 2,
            symWeighted w β σ τ * (y τ / Real.sqrt (w τ)) := by
    intro y σ
    have hs : Real.sqrt (w σ) ≠ 0 := (Real.sqrt_pos.mpr (hw σ)).ne'
    have hsq : Real.sqrt (w σ) * Real.sqrt (w σ) = w σ :=
      Real.mul_self_sqrt (hw σ).le
    set S : ℝ := ∑ τ : Fin L → Fin 2, spatialKernel β σ τ * y τ with hS
    have hR : (∑ τ : Fin L → Fin 2,
        symWeighted w β σ τ * (y τ / Real.sqrt (w τ)))
        = Real.sqrt (w σ) * S := by
      rw [hS, Finset.mul_sum]
      refine Finset.sum_congr rfl fun τ _ => ?_
      have cτ : Real.sqrt (w τ) * (y τ / Real.sqrt (w τ)) = y τ := by
        have ht : Real.sqrt (w τ) ≠ 0 := (Real.sqrt_pos.mpr (hw τ)).ne'
        field_simp
      calc symWeighted w β σ τ * (y τ / Real.sqrt (w τ))
          = Real.sqrt (w σ) * spatialKernel β σ τ
              * (Real.sqrt (w τ) * (y τ / Real.sqrt (w τ))) := by
            unfold symWeighted
            ring
        _ = Real.sqrt (w σ) * (spatialKernel β σ τ * y τ) := by
            rw [cτ]
            ring
    rw [hR, eq_comm, eq_div_iff hs]
    linear_combination S * hsq
  have hpart : ∀ y : (Fin L → Fin 2) → ℝ,
      (∑ σ : Fin L → Fin 2,
          (w σ * ∑ τ : Fin L → Fin 2, spatialKernel β σ τ * y τ) ^ 2 / w σ)
        ≤ lam ^ 2 * ∑ σ : Fin L → Fin 2, y σ ^ 2 / w σ := by
    intro y
    have hgen := norm_sq_le_perron hsym hAnn hΩ heig
      (fun τ => y τ / Real.sqrt (w τ))
    have hL : ∀ σ : Fin L → Fin 2,
        (∑ τ : Fin L → Fin 2, symWeighted w β σ τ * (y τ / Real.sqrt (w τ))) ^ 2
          = (w σ * ∑ τ : Fin L → Fin 2, spatialKernel β σ τ * y τ) ^ 2 / w σ := by
      intro σ
      have hs : (0:ℝ) < Real.sqrt (w σ) := Real.sqrt_pos.mpr (hw σ)
      have hsq : Real.sqrt (w σ) * Real.sqrt (w σ) = w σ :=
        Real.mul_self_sqrt (hw σ).le
      rw [← hcomp y σ, div_pow]
      congr 1
      linear_combination hsq
    rw [Finset.sum_congr rfl fun σ (_ : σ ∈ Finset.univ) => hL σ] at hgen
    have hR : (∑ τ : Fin L → Fin 2, (y τ / Real.sqrt (w τ)) ^ 2)
        = ∑ τ : Fin L → Fin 2, y τ ^ 2 / w τ :=
      Finset.sum_congr rfl fun τ _ => sq_div_sqrt hw y τ
    rw [hR] at hgen
    exact hgen
  have hre := hpart (fun σ => (u σ).re)
  have him := hpart (fun σ => (u σ).im)
  have hLHS : siteQ w (transferOp w β u)
      = (∑ σ : Fin L → Fin 2,
          (w σ * ∑ τ : Fin L → Fin 2, spatialKernel β σ τ * (u τ).re) ^ 2 / w σ)
        + ∑ σ : Fin L → Fin 2,
          (w σ * ∑ τ : Fin L → Fin 2, spatialKernel β σ τ * (u τ).im) ^ 2 / w σ := by
    unfold siteQ
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun σ _ => ?_
    have hre' : (transferOp w β u σ).re
        = w σ * ∑ τ : Fin L → Fin 2, spatialKernel β σ τ * (u τ).re := by
      show (((w σ : ℝ) : ℂ) * ∑ τ : Fin L → Fin 2,
          ((spatialKernel β σ τ : ℝ) : ℂ) * u τ).re = _
      simp [Complex.re_sum, Finset.mul_sum]
    have him' : (transferOp w β u σ).im
        = w σ * ∑ τ : Fin L → Fin 2, spatialKernel β σ τ * (u τ).im := by
      show (((w σ : ℝ) : ℂ) * ∑ τ : Fin L → Fin 2,
          ((spatialKernel β σ τ : ℝ) : ℂ) * u τ).im = _
      simp [Complex.im_sum, Finset.mul_sum]
    rw [Complex.normSq_apply, hre', him']
    ring
  have hRHS : lam ^ 2 * siteQ w u
      = lam ^ 2 * (∑ σ : Fin L → Fin 2, (u σ).re ^ 2 / w σ)
        + lam ^ 2 * ∑ σ : Fin L → Fin 2, (u σ).im ^ 2 / w σ := by
    unfold siteQ
    rw [← mul_add, ← Finset.sum_add_distrib]
    refine congrArg _ (Finset.sum_congr rfl fun σ _ => ?_)
    rw [Complex.normSq_apply]
    field_simp
  rw [hLHS, hRHS]
  exact add_le_add hre him

/-- The physical norm of the Perron vector is positive, which is what turns the
attained equality into MINIMALITY rather than a coincidence. -/
theorem siteQ_perron_pos {L : ℕ} {w : (Fin L → Fin 2) → ℝ}
    (hw : ∀ σ, 0 < w σ) {Ω : (Fin L → Fin 2) → ℝ} (hΩ : ∀ σ, 0 < Ω σ) :
    0 < siteQ w (fun σ => ((Real.sqrt (w σ) * Ω σ : ℝ) : ℂ)) := by
  unfold siteQ
  refine Finset.sum_pos (fun σ _ => ?_) ⟨Classical.arbitrary _, Finset.mem_univ _⟩
  have hsq : Real.sqrt (w σ) * Real.sqrt (w σ) = w σ :=
    Real.mul_self_sqrt (hw σ).le
  have hns : Complex.normSq (((Real.sqrt (w σ) * Ω σ : ℝ) : ℂ))
      = (Real.sqrt (w σ) * Ω σ) ^ 2 := by
    rw [Complex.normSq_apply, Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [hns]
  have hpos : 0 < (Real.sqrt (w σ) * Ω σ) ^ 2 := by
    have : 0 < Real.sqrt (w σ) * Ω σ :=
      mul_pos (Real.sqrt_pos.mpr (hw σ)) (hΩ σ)
    positivity
  exact div_pos hpos (hw σ)

/-- **THE CONSTANT IS MINIMAL**, and not merely attained: any constant that
bounds the form everywhere is at least `lam`. -/
theorem perron_constant_minimal {L : ℕ} {w : (Fin L → Fin 2) → ℝ}
    (hw : ∀ σ, 0 < w σ) (β : ℝ) {Ω : (Fin L → Fin 2) → ℝ}
    (hΩ : ∀ σ, 0 < Ω σ) {lam c : ℝ}
    (heig : ∀ σ, (∑ τ : Fin L → Fin 2, symWeighted w β σ τ * Ω τ) = lam * Ω σ)
    (hc : ∀ u : (Fin L → Fin 2) → ℂ, bondQ β u ≤ c * siteQ w u) : lam ≤ c := by
  have hpos := siteQ_perron_pos hw hΩ (w := w)
  have hEq := transferOp_perron_attained hw β hΩ heig
  have hle := hc (fun σ => ((Real.sqrt (w σ) * Ω σ : ℝ) : ℂ))
  rw [hEq] at hle
  exact le_of_mul_le_mul_right (by linarith) hpos

/-- The Perron vector is an eigenvector of `T` itself, with the same eigenvalue:
the intertwining carries `Ω` across.  A corollary of §7b, written down because
the norm sharpness below needs it as a theorem and not as a remark. -/
theorem transferOp_perron_eigen {L : ℕ} {w : (Fin L → Fin 2) → ℝ}
    (hw : ∀ σ, 0 < w σ) (β : ℝ) {Ω : (Fin L → Fin 2) → ℝ} {lam : ℝ}
    (heig : ∀ σ, (∑ τ : Fin L → Fin 2, symWeighted w β σ τ * Ω τ) = lam * Ω σ)
    (σ : Fin L → Fin 2) :
    transferOp w β (fun τ => ((Real.sqrt (w τ) * Ω τ : ℝ) : ℂ)) σ
      = ((lam : ℝ) : ℂ) * ((Real.sqrt (w σ) * Ω σ : ℝ) : ℂ) := by
  have hcast : ∀ σ : Fin L → Fin 2,
      (∑ τ : Fin L → Fin 2, ((symWeighted w β σ τ : ℝ) : ℂ) * ((Ω τ : ℝ) : ℂ))
        = ((lam : ℝ) : ℂ) * ((Ω σ : ℝ) : ℂ) := by
    intro σ
    rw [← Complex.ofReal_mul, ← heig σ, Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun τ _ => by push_cast; ring
  have h := transferOp_eigen_of_symWeighted (fun σ => (hw σ).le) β
    (fun τ => ((Ω τ : ℝ) : ℂ)) ((lam : ℝ) : ℂ) hcast σ
  have hfun : (fun τ => ((Real.sqrt (w τ) : ℝ) : ℂ) * ((Ω τ : ℝ) : ℂ))
      = fun τ => ((Real.sqrt (w τ) * Ω τ : ℝ) : ℂ) := by
    funext τ
    push_cast
    ring
  rw [hfun] at h
  rw [h]
  push_cast
  ring

/-- **THE NORM CONSTANT IS ATTAINED**, and not only the quadratic one: at the
Perron vector the norm inequality is an equality. -/
theorem siteQ_transferOp_perron {L : ℕ} {w : (Fin L → Fin 2) → ℝ}
    (hw : ∀ σ, 0 < w σ) (β : ℝ) {Ω : (Fin L → Fin 2) → ℝ} {lam : ℝ}
    (heig : ∀ σ, (∑ τ : Fin L → Fin 2, symWeighted w β σ τ * Ω τ) = lam * Ω σ) :
    siteQ w (transferOp w β (fun τ => ((Real.sqrt (w τ) * Ω τ : ℝ) : ℂ)))
      = lam ^ 2 * siteQ w (fun τ => ((Real.sqrt (w τ) * Ω τ : ℝ) : ℂ)) := by
  unfold siteQ
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [transferOp_perron_eigen hw β heig σ]
  have hns : Complex.normSq (((lam : ℝ) : ℂ)
        * ((Real.sqrt (w σ) * Ω σ : ℝ) : ℂ))
      = lam ^ 2 * Complex.normSq (((Real.sqrt (w σ) * Ω σ : ℝ) : ℂ)) := by
    rw [Complex.normSq_mul, Complex.normSq_ofReal]
    ring
  rw [hns]
  ring

/-- **AND THE NORM CONSTANT IS MINIMAL.**  Any `c ≥ 0` bounding `‖T u‖` by
`c‖u‖` everywhere satisfies `lam ≤ c`.  With the previous theorem this makes
`lam` the operator norm of `T` in the physical metric, not merely an upper
bound for it --- at every `β`. -/
theorem perron_norm_constant_minimal {L : ℕ} {w : (Fin L → Fin 2) → ℝ}
    (hw : ∀ σ, 0 < w σ) (β : ℝ) {Ω : (Fin L → Fin 2) → ℝ} (hΩ : ∀ σ, 0 < Ω σ)
    {lam c : ℝ} (hlam : 0 ≤ lam) (hc0 : 0 ≤ c)
    (heig : ∀ σ, (∑ τ : Fin L → Fin 2, symWeighted w β σ τ * Ω τ) = lam * Ω σ)
    (hc : ∀ u : (Fin L → Fin 2) → ℂ,
      siteQ w (transferOp w β u) ≤ c ^ 2 * siteQ w u) : lam ≤ c := by
  have hpos := siteQ_perron_pos hw hΩ (w := w)
  have hEq := siteQ_transferOp_perron hw β heig
  have hle := hc (fun τ => ((Real.sqrt (w τ) * Ω τ : ℝ) : ℂ))
  rw [hEq] at hle
  have hsq : lam ^ 2 ≤ c ^ 2 := le_of_mul_le_mul_right (by linarith) hpos
  nlinarith [hsq, hlam, hc0]

/-- **THE PERRON DATA EXISTS**, so nothing above is conditional on a hypothesis
nobody can discharge: the symmetrised kernel is strictly positive, and this lane
already proves such a kernel has a strictly positive eigenvector with positive
eigenvalue.  The bundle is therefore an unconditional statement about `T`:
a sharp quadratic bound, a norm bound, attainment, and minimality. -/
theorem exists_contraction_constant {L : ℕ} {w : (Fin L → Fin 2) → ℝ}
    (hw : ∀ σ, 0 < w σ) (β : ℝ) :
    ∃ (Ω : (Fin L → Fin 2) → ℝ) (lam : ℝ), (∀ σ, 0 < Ω σ) ∧ 0 < lam ∧
      (∀ u : (Fin L → Fin 2) → ℂ, bondQ β u ≤ lam * siteQ w u) ∧
      (∀ u : (Fin L → Fin 2) → ℂ,
        siteQ w (transferOp w β u) ≤ lam ^ 2 * siteQ w u) ∧
      bondQ β (fun σ => ((Real.sqrt (w σ) * Ω σ : ℝ) : ℂ))
        = lam * siteQ w (fun σ => ((Real.sqrt (w σ) * Ω σ : ℝ) : ℂ)) ∧
      siteQ w (transferOp w β (fun σ => ((Real.sqrt (w σ) * Ω σ : ℝ) : ℂ)))
        = lam ^ 2 * siteQ w (fun σ => ((Real.sqrt (w σ) * Ω σ : ℝ) : ℂ)) ∧
      (∀ c : ℝ, (∀ u : (Fin L → Fin 2) → ℂ, bondQ β u ≤ c * siteQ w u)
        → lam ≤ c) ∧
      (∀ c : ℝ, 0 ≤ c → (∀ u : (Fin L → Fin 2) → ℂ,
        siteQ w (transferOp w β u) ≤ c ^ 2 * siteQ w u) → lam ≤ c) := by
  obtain ⟨Ω, lam, hΩ, -, hlam, heig⟩ :=
    exists_pos_eigenvector (symWeighted w β) (symWeighted_pos hw β)
  exact ⟨Ω, lam, hΩ, hlam,
    fun u => transferOp_le_perron hw β hΩ heig u,
    fun u => siteQ_transferOp_le hw β hΩ heig u,
    transferOp_perron_attained hw β hΩ heig,
    siteQ_transferOp_perron hw β heig,
    fun c hc => perron_constant_minimal hw β hΩ heig hc,
    fun c hc0 hc => perron_norm_constant_minimal hw β hΩ hlam.le hc0 heig hc⟩

/-! ### §7d  COERCIVITY at `β > 0`, and the constant carries the weight

The upper bound says `T` is not too big.  A Hamiltonian needs the other side:
`T` bounded BELOW away from zero, so that `T/lam` is invertible and its
logarithm can be discussed.  That is what this section proves, for `β > 0`.

The mechanism is the one-site decomposition

    M = 2·sinh(β)·I + e^{-β}·J ,      J the all-ones block,

whose `I` part survives every tensor factor while the rest stays positive
semidefinite.  Rather than expanding over subsets, the induction reuses the
even/odd split this lane already uses for positive semidefiniteness: the two
halves are recombined with `Z = e^β + e^{-β}` and `D = e^β − e^{-β}`, and
`D ≤ Z` turns the recombination into a lower bound.

AND THE PHYSICAL CONSTANT IS NOT `D^L`.  An external reading caught this: the
physical norm is WEIGHTED, `siteQ w u = ∑ |u σ|²/w σ`, so passing from the
Euclidean bound to a `siteQ` bound costs a factor `min w`, which is positive
because the configuration space is finite.  The coercivity constant is

    D^L · min_σ w(σ) ,

not `D^L`.  Writing `D^L` would have claimed a bound that is false for weights
smaller than one. -/

/-- **THE DECOUPLED KERNEL IS COERCIVE**, with constant `(e^β − e^{-β})^L`.
Strictly positive exactly when `β > 0`; at `β = 0` it degenerates to `0`, which
is correct --- the kernel has null modes there. -/
theorem spatialKernel_coercive {β : ℝ} (hβ : 0 ≤ β) :
    ∀ (L : ℕ) (u : (Fin L → Fin 2) → ℝ),
      (Real.exp β - Real.exp (-β)) ^ L * (∑ σ, u σ ^ 2)
        ≤ ∑ σ, u σ * act (spatialKernel β) u σ := by
  intro L
  induction L with
  | zero =>
    intro u
    have hone : ∀ σ : Fin 0 → Fin 2, act (spatialKernel β) u σ = u σ := by
      intro σ
      show (∑ τ, spatialKernel β σ τ * u τ) = u σ
      have hsingle : ∑ τ : Fin 0 → Fin 2, spatialKernel β σ τ * u τ
          = spatialKernel β σ σ * u σ :=
        Finset.sum_eq_single σ
          (fun b _ hb => absurd (Subsingleton.elim b σ) hb)
          (fun h => absurd (Finset.mem_univ σ) h)
      rw [hsingle]
      show (∏ _j : Fin 0, _) * u σ = u σ
      simp
    rw [Finset.sum_congr rfl fun σ _ => by rw [hone σ]]
    rw [pow_zero, one_mul]
    exact le_of_eq (Finset.sum_congr rfl fun σ _ => by ring)
  | succ L ih =>
    intro u
    have hD : (0:ℝ) ≤ Real.exp β - Real.exp (-β) :=
      sub_nonneg.mpr (Real.exp_le_exp.mpr (by linarith))
    have hZ : (0:ℝ) < z2Norm β := z2Norm_pos β
    have hZD : Real.exp β - Real.exp (-β) ≤ z2Norm β := by
      unfold z2Norm
      nlinarith [Real.exp_pos (-β)]
    have hP := ih (fun τ => u (Fin.cons 0 τ) + u (Fin.cons 1 τ))
    have hM := ih (fun τ => u (Fin.cons 0 τ) - u (Fin.cons 1 τ))
    rw [act_add (spatialKernel β)] at hP
    rw [act_sub (spatialKernel β)] at hM
    simp only [] at hP hM
    rw [sum_cons_config (fun σ => u σ * act (spatialKernel β) u σ),
      Fin.sum_univ_two]
    simp only [act_spatialKernel_cons, z2Bond_same,
      z2Bond_ne (by decide : (0:Fin 2) ≠ 1), z2Bond_ne (by decide : (1:Fin 2) ≠ 0)]
    set A0 := act (spatialKernel β) (fun τ => u (Fin.cons 0 τ)) with hA0
    set A1 := act (spatialKernel β) (fun τ => u (Fin.cons 1 τ)) with hA1
    set SP := ∑ τ : Fin L → Fin 2,
      (u (Fin.cons 0 τ) + u (Fin.cons 1 τ)) * (A0 τ + A1 τ) with hSP
    set SM := ∑ τ : Fin L → Fin 2,
      (u (Fin.cons 0 τ) - u (Fin.cons 1 τ)) * (A0 τ - A1 τ) with hSM
    have hkey : (∑ τ : Fin L → Fin 2,
          u (Fin.cons 0 τ) * (Real.exp β * A0 τ + Real.exp (-β) * A1 τ))
        + (∑ τ : Fin L → Fin 2,
          u (Fin.cons 1 τ) * (Real.exp (-β) * A0 τ + Real.exp β * A1 τ))
        = (z2Norm β * SP + (Real.exp β - Real.exp (-β)) * SM) / 2 := by
      rw [← Finset.sum_add_distrib, hSP, hSM, Finset.mul_sum, Finset.mul_sum,
        ← Finset.sum_add_distrib, Finset.sum_div]
      refine Finset.sum_congr rfl fun τ _ => ?_
      unfold z2Norm
      ring
    rw [hkey]
    set D : ℝ := Real.exp β - Real.exp (-β) with hDdef
    set QP := ∑ τ : Fin L → Fin 2,
      (u (Fin.cons 0 τ) + u (Fin.cons 1 τ)) ^ 2 with hQP
    set QM := ∑ τ : Fin L → Fin 2,
      (u (Fin.cons 0 τ) - u (Fin.cons 1 τ)) ^ 2 with hQM
    have hsplit : (∑ σ : Fin (L + 1) → Fin 2, u σ ^ 2)
        = (∑ τ : Fin L → Fin 2, u (Fin.cons 0 τ) ^ 2)
          + ∑ τ : Fin L → Fin 2, u (Fin.cons 1 τ) ^ 2 := by
      rw [sum_cons_config (fun σ => u σ ^ 2), Fin.sum_univ_two]
    have hpar : QP + QM
        = 2 * ((∑ τ : Fin L → Fin 2, u (Fin.cons 0 τ) ^ 2)
            + ∑ τ : Fin L → Fin 2, u (Fin.cons 1 τ) ^ 2) := by
      rw [hQP, hQM, ← Finset.sum_add_distrib, Finset.mul_add,
        ← Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum,
        ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun τ _ => by ring
    -- the two halves, each bounded below by the induction hypothesis
    have hPlow : D ^ L * QP ≤ SP := hP
    have hMlow : D ^ L * QM ≤ SM := hM
    have hDL : (0:ℝ) ≤ D ^ L := pow_nonneg hD L
    have hZP : z2Norm β * (D ^ L * QP) ≤ z2Norm β * SP :=
      mul_le_mul_of_nonneg_left hPlow hZ.le
    have hDM : D * (D ^ L * QM) ≤ D * SM := mul_le_mul_of_nonneg_left hMlow hD
    have hQPnn : (0:ℝ) ≤ QP :=
      Finset.sum_nonneg fun τ _ => sq_nonneg _
    have hDZ : D * (D ^ L * QP) ≤ z2Norm β * (D ^ L * QP) :=
      mul_le_mul_of_nonneg_right hZD (mul_nonneg hDL hQPnn)
    have hfinal : D ^ (L + 1) * (∑ σ : Fin (L + 1) → Fin 2, u σ ^ 2)
        ≤ (D * (D ^ L * QP) + D * (D ^ L * QM)) / 2 := by
      rw [hsplit, pow_succ]
      nlinarith [hpar, hDL, hD]
    linarith [hfinal, hZP, hDM, hDZ]

/-! The physical assembly: the Euclidean coercivity, the weight floor, and the
bound the Hamiltonian route needs. -/

/-- The smallest weight, and it is positive because there are finitely many
configurations.  This is the factor the physical constant carries and the
Euclidean one does not. -/
noncomputable def minWeight {L : ℕ} (w : (Fin L → Fin 2) → ℝ) : ℝ :=
  Finset.univ.inf' ⟨Classical.arbitrary _, Finset.mem_univ _⟩ w

theorem minWeight_pos {L : ℕ} {w : (Fin L → Fin 2) → ℝ} (hw : ∀ σ, 0 < w σ) :
    0 < minWeight w := by
  unfold minWeight
  rw [Finset.lt_inf'_iff]
  exact fun σ _ => hw σ

theorem minWeight_le {L : ℕ} (w : (Fin L → Fin 2) → ℝ) (σ : Fin L → Fin 2) :
    minWeight w ≤ w σ :=
  Finset.inf'_le _ (Finset.mem_univ σ)

/-- **THE COERCIVITY, IN THE PHYSICAL NORM.**  For `β > 0` the reflected bond
form is bounded below by a strictly positive multiple of the physical squared
norm.  The constant carries `min w`: the physical norm is weighted, and passing
from a Euclidean bound to a `siteQ` bound costs exactly that factor. -/
theorem bondQ_ge_siteQ {L : ℕ} {w : (Fin L → Fin 2) → ℝ} (hw : ∀ σ, 0 < w σ)
    {β : ℝ} (hβ : 0 ≤ β) (u : (Fin L → Fin 2) → ℂ) :
    (Real.exp β - Real.exp (-β)) ^ L * minWeight w * siteQ w u ≤ bondQ β u := by
  have hDL : (0:ℝ) ≤ (Real.exp β - Real.exp (-β)) ^ L :=
    pow_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr (by linarith))) L
  have hquad : ∀ y : (Fin L → Fin 2) → ℝ,
      (Real.exp β - Real.exp (-β)) ^ L * (∑ σ, y σ ^ 2)
        ≤ ∑ σ, ∑ τ, spatialKernel β σ τ * (y σ * y τ) := by
    intro y
    have h := spatialKernel_coercive hβ L y
    have hrw : (∑ σ, y σ * act (spatialKernel β) y σ)
        = ∑ σ, ∑ τ, spatialKernel β σ τ * (y σ * y τ) := by
      unfold act
      refine Finset.sum_congr rfl fun σ _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun τ _ => by ring
    rw [hrw] at h
    exact h
  have hfloor : ∀ y : (Fin L → Fin 2) → ℝ,
      minWeight w * (∑ σ, y σ ^ 2 / w σ) ≤ ∑ σ, y σ ^ 2 := by
    intro y
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun σ _ => ?_
    have hnn : (0:ℝ) ≤ y σ ^ 2 / w σ := div_nonneg (sq_nonneg _) (hw σ).le
    have hstep : minWeight w * (y σ ^ 2 / w σ) ≤ w σ * (y σ ^ 2 / w σ) :=
      mul_le_mul_of_nonneg_right (minWeight_le w σ) hnn
    have hcancel : w σ * (y σ ^ 2 / w σ) = y σ ^ 2 := by
      have : w σ ≠ 0 := (hw σ).ne'
      field_simp
    rw [hcancel] at hstep
    exact hstep
  have hre := hquad (fun σ => (u σ).re)
  have him := hquad (fun σ => (u σ).im)
  have hfre := hfloor (fun σ => (u σ).re)
  have hfim := hfloor (fun σ => (u σ).im)
  have hsq : siteQ w u = (∑ σ, (u σ).re ^ 2 / w σ)
      + ∑ σ, (u σ).im ^ 2 / w σ := by
    unfold siteQ
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Complex.normSq_apply]
    field_simp
    ring
  -- the two chains, made explicit rather than left to `nlinarith` to discover:
  -- multiplying an inequality by `D^L ≥ 0` is a step, not a hint.
  have hAre : (Real.exp β - Real.exp (-β)) ^ L
        * (minWeight w * ∑ σ, (u σ).re ^ 2 / w σ)
      ≤ ∑ σ, ∑ τ, spatialKernel β σ τ * ((u σ).re * (u τ).re) :=
    le_trans (mul_le_mul_of_nonneg_left hfre hDL) hre
  have hAim : (Real.exp β - Real.exp (-β)) ^ L
        * (minWeight w * ∑ σ, (u σ).im ^ 2 / w σ)
      ≤ ∑ σ, ∑ τ, spatialKernel β σ τ * ((u σ).im * (u τ).im) :=
    le_trans (mul_le_mul_of_nonneg_left hfim hDL) him
  unfold bondQ
  rw [hsq]
  have hdist : (Real.exp β - Real.exp (-β)) ^ L * minWeight w
        * ((∑ σ, (u σ).re ^ 2 / w σ) + ∑ σ, (u σ).im ^ 2 / w σ)
      = (Real.exp β - Real.exp (-β)) ^ L
          * (minWeight w * ∑ σ, (u σ).re ^ 2 / w σ)
        + (Real.exp β - Real.exp (-β)) ^ L
          * (minWeight w * ∑ σ, (u σ).im ^ 2 / w σ) := by ring
  rw [hdist]
  exact add_le_add hAre hAim

/-- **THE TRANSFER OPERATOR IS BOUNDED BELOW AND ABOVE**, for `β > 0`.

Deliberately NOT titled "the normalised operator is bounded below", which is
what an earlier version said: this theorem does not divide by `lam` and does not
carry `0 < lam` in its conclusion.  The normalised statement
`(a/lam)·I ≤ T/lam ≤ I` is `normalised_two_sided` below, which gets `0 < lam`
from the Perron data.  Naming a theorem after a consequence of itself plus
something else is the defect this module keeps meeting. -/
theorem transferOp_coercive {L : ℕ} {w : (Fin L → Fin 2) → ℝ} (hw : ∀ σ, 0 < w σ)
    {β : ℝ} (hβ : 0 < β) {Ω : (Fin L → Fin 2) → ℝ} (hΩ : ∀ σ, 0 < Ω σ)
    {lam : ℝ}
    (heig : ∀ σ, (∑ τ : Fin L → Fin 2, symWeighted w β σ τ * Ω τ) = lam * Ω σ)
    (u : (Fin L → Fin 2) → ℂ) :
    (Real.exp β - Real.exp (-β)) ^ L * minWeight w * siteQ w u
      ≤ bondQ β u ∧ bondQ β u ≤ lam * siteQ w u :=
  ⟨bondQ_ge_siteQ hw hβ.le u, transferOp_le_perron hw β hΩ heig u⟩

/-- The coercivity constant is strictly positive whenever `β > 0`, which is what
makes the two-sided bound useful.

**THE `L = 0` EDGE, and an earlier version of this docstring got it wrong.**  It
said the constant is positive "exactly when `β > 0`" and vanishes at `β = 0`.
That is false at `L = 0`, where `D ^ 0 = 1` for every `β`, the configuration
space is a single point, the kernel is the scalar `1`, and there are no null
modes: the constant is `min w > 0` even at `β = 0`.  The theorem below was
always safe --- it only ever claimed the `β > 0` direction --- but the sentence
around it claimed a biconditional the proof does not have.

The DISJOINT partition, and it is a partition only once the universe is
delimited --- an earlier draft called the enumeration a "trichotomy" while its
cases overlapped at `L = 0, β > 0` and said nothing about `L > 0, β < 0`.
Within `β ≥ 0`:

    L = 0,  any β ≥ 0        constant = min w  > 0
    L > 0,  β = 0            constant = 0
    L > 0,  β > 0            constant > 0

Outside that range, at `L = 0` the constant is `min w > 0` for every real `β`,
negative ones included, because `D ^ 0 = 1`.  `coercivity_constant_zero` and
`coercivity_constant_zero_extent` below record the two boundary cases, so they
are theorems rather than remarks. -/
theorem coercivity_constant_pos {L : ℕ} {w : (Fin L → Fin 2) → ℝ}
    (hw : ∀ σ, 0 < w σ) {β : ℝ} (hβ : 0 < β) :
    0 < (Real.exp β - Real.exp (-β)) ^ L * minWeight w := by
  have hD : (0:ℝ) < Real.exp β - Real.exp (-β) := by
    have : Real.exp (-β) < Real.exp β := Real.exp_lt_exp.mpr (by linarith)
    linarith
  exact mul_pos (pow_pos hD L) (minWeight_pos hw)

/-- The middle case of the trichotomy, as a theorem: at `β = 0` and `L > 0` the
coercivity constant really is zero.  The bound is then vacuous, which is the
honest reading --- the kernel is degenerate there. -/
theorem coercivity_constant_zero {L : ℕ} (w : (Fin L → Fin 2) → ℝ) (hL : 0 < L) :
    (Real.exp 0 - Real.exp (-0)) ^ L * minWeight w = 0 := by
  have : Real.exp 0 - Real.exp (-0) = 0 := by
    rw [neg_zero, Real.exp_zero]
    ring
  rw [this, zero_pow (Nat.pos_iff_ne_zero.mp hL), zero_mul]

/-- The `L = 0` case of the trichotomy: the constant is `min w`, positive at
EVERY `β`, negative couplings included. -/
theorem coercivity_constant_zero_extent {w : (Fin 0 → Fin 2) → ℝ}
    (hw : ∀ σ, 0 < w σ) (β : ℝ) :
    0 < (Real.exp β - Real.exp (-β)) ^ 0 * minWeight w := by
  rw [pow_zero, one_mul]
  exact minWeight_pos hw

/-- **THE TRANSFER OPERATOR IS INJECTIVE for `β > 0`.**  A direct consequence of
coercivity and definiteness, and one the previous version left as an
observation: if `T u = 0` then the form vanishes, so the physical norm does, so
`u` does.  In finite dimension this is invertibility. -/
theorem transferOp_injective {L : ℕ} {w : (Fin L → Fin 2) → ℝ}
    (hw : ∀ σ, 0 < w σ) {β : ℝ} (hβ : 0 < β)
    {u : (Fin L → Fin 2) → ℂ} (hu : transferOp w β u = 0) : u = 0 := by
  have hform : bondForm β u u = 0 := by
    rw [← siteForm_transferOp hw β u u, hu]
    unfold siteForm
    simp
  have hQ : bondQ β u = 0 := by
    have := bondForm_self_eq_bondQ β u
    rw [hform] at this
    exact_mod_cast this.symm
  have hcoer := bondQ_ge_siteQ hw hβ.le u
  rw [hQ] at hcoer
  have hconst : 0 < (Real.exp β - Real.exp (-β)) ^ L * minWeight w :=
    coercivity_constant_pos hw hβ
  have hsiteQ_nonneg : 0 ≤ siteQ w u :=
    Finset.sum_nonneg fun σ _ => div_nonneg (Complex.normSq_nonneg _) (hw σ).le
  have hzero : siteQ w u = 0 := by
    by_contra hne
    have hpos : 0 < siteQ w u := lt_of_le_of_ne hsiteQ_nonneg (Ne.symm hne)
    nlinarith [hcoer, hconst, hpos]
  have : siteForm w u u = 0 := by
    rw [siteForm_self_eq_siteQ, hzero]
    simp
  exact (siteForm_self_eq_zero_iff hw u).mp this

/-- **INJECTIVE AT ZERO EXTENT, AT EVERY `β`** --- negative ones included.

The manuscript says invertibility survives at `L = 0` even at `β = 0`.  That was
a CONSEQUENCE and not a theorem: every injectivity statement above requires
`0 < β`, because it goes through the coercivity constant.  At zero extent the
argument is different and simpler --- the kernel is the empty product `1`, so
`T` is multiplication by `w` --- and by this lane's own standard the sentence
should be backed by a declaration rather than by a remark.  Here it is. -/
theorem transferOp_injective_zero_extent {w : (Fin 0 → Fin 2) → ℝ}
    (hw : ∀ σ, 0 < w σ) (β : ℝ) {u : (Fin 0 → Fin 2) → ℂ}
    (hu : transferOp w β u = 0) : u = 0 := by
  funext σ
  show u σ = 0
  have hone : (∑ τ : Fin 0 → Fin 2, ((spatialKernel β σ τ : ℝ) : ℂ) * u τ)
      = u σ := by
    have hsingle : (∑ τ : Fin 0 → Fin 2, ((spatialKernel β σ τ : ℝ) : ℂ) * u τ)
        = ((spatialKernel β σ σ : ℝ) : ℂ) * u σ :=
      Finset.sum_eq_single σ
        (fun b _ hb => absurd (Subsingleton.elim b σ) hb)
        (fun h => absurd (Finset.mem_univ σ) h)
    have hk : spatialKernel β σ σ = 1 := by
      unfold spatialKernel
      simp
    rw [hsingle, hk]
    push_cast
    ring
  have hz : ((w σ : ℝ) : ℂ)
      * (∑ τ : Fin 0 → Fin 2, ((spatialKernel β σ τ : ℝ) : ℂ) * u τ) = 0 := by
    have h := congrFun hu σ
    simpa using h
  rw [hone] at hz
  have hwne : ((w σ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hw σ).ne'
  exact (mul_eq_zero.mp hz).resolve_left hwne

/-- **THE TWO-SIDED BOUND, UNCONDITIONAL.**  Both constants exist, both are
strictly positive, and the operator is injective.  This is the package a
functional calculus would consume; the calculus itself is NOT here. -/
theorem exists_two_sided_bound {L : ℕ} {w : (Fin L → Fin 2) → ℝ}
    (hw : ∀ σ, 0 < w σ) {β : ℝ} (hβ : 0 < β) :
    ∃ (a lam : ℝ), 0 < a ∧ 0 < lam ∧
      (∀ u : (Fin L → Fin 2) → ℂ,
        a * siteQ w u ≤ bondQ β u ∧ bondQ β u ≤ lam * siteQ w u) ∧
      (∀ u : (Fin L → Fin 2) → ℂ, transferOp w β u = 0 → u = 0) := by
  obtain ⟨Ω, lam, hΩ, -, hlam, heig⟩ :=
    exists_pos_eigenvector (symWeighted w β) (symWeighted_pos hw β)
  exact ⟨(Real.exp β - Real.exp (-β)) ^ L * minWeight w, lam,
    coercivity_constant_pos hw hβ, hlam,
    fun u => ⟨bondQ_ge_siteQ hw hβ.le u, transferOp_le_perron hw β hΩ heig u⟩,
    fun u hu => transferOp_injective hw hβ hu⟩

/-! ### §7e  From estimates to OBJECTS

The estimates above are what a functional calculus consumes, but a calculus
consumes objects, not inequalities about a bare function.  This section turns
the trivial kernel into `Function.Injective`, then into bijectivity by finite
dimension, then into a bundled `LinearEquiv`; and it writes the normalised
operator down.  None of it is new mathematics --- that is exactly why it is
worth doing rather than asserting. -/

/-- The transfer operator is injective as a FUNCTION.  `transferOp_injective`
gives trivial kernel; linearity turns it into injectivity, and only then can a
consumer use it. -/
theorem transferOp_injective' {L : ℕ} {w : (Fin L → Fin 2) → ℝ}
    (hw : ∀ σ, 0 < w σ) {β : ℝ} (hβ : 0 < β) :
    Function.Injective (transferOp w β) := by
  intro u v huv
  have h := transferOp_add w β (u - v) v
  rw [sub_add_cancel] at h
  rw [huv] at h
  exact sub_eq_zero.mp (transferOp_injective hw hβ (self_eq_add_left.mp h))

theorem transferOpL_injective {L : ℕ} {w : (Fin L → Fin 2) → ℝ}
    (hw : ∀ σ, 0 < w σ) {β : ℝ} (hβ : 0 < β) :
    Function.Injective (transferOpL w β) := transferOp_injective' hw hβ

theorem transferOpL_ker_eq_bot {L : ℕ} {w : (Fin L → Fin 2) → ℝ}
    (hw : ∀ σ, 0 < w σ) {β : ℝ} (hβ : 0 < β) :
    LinearMap.ker (transferOpL w β) = ⊥ :=
  LinearMap.ker_eq_bot.mpr (transferOpL_injective hw hβ)

/-- **AND THEREFORE BIJECTIVE**, by finite dimension.  The physical space is
`(Fin L → Fin 2) → ℂ`, a finite product of copies of `ℂ`. -/
theorem transferOpL_bijective {L : ℕ} {w : (Fin L → Fin 2) → ℝ}
    (hw : ∀ σ, 0 < w σ) {β : ℝ} (hβ : 0 < β) :
    Function.Bijective (transferOpL w β) := by
  have hinj := transferOpL_injective hw hβ
  exact ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩

/-- **THE TRANSFER OPERATOR AS AN ISOMORPHISM**, for `β > 0`.  Invertibility is
what a logarithm needs, and it is an object here rather than a remark about
finite dimension. -/
noncomputable def transferEquiv {L : ℕ} {w : (Fin L → Fin 2) → ℝ}
    (hw : ∀ σ, 0 < w σ) {β : ℝ} (hβ : 0 < β) :
    ((Fin L → Fin 2) → ℂ) ≃ₗ[ℂ] ((Fin L → Fin 2) → ℂ) :=
  LinearEquiv.ofBijective (transferOpL w β) (transferOpL_bijective hw hβ)

/-- The normalised operator `T/lam`, as a linear map. -/
noncomputable def normalisedTransferOpL {L : ℕ} (w : (Fin L → Fin 2) → ℝ)
    (β : ℝ) (lam : ℝ) :
    ((Fin L → Fin 2) → ℂ) →ₗ[ℂ] ((Fin L → Fin 2) → ℂ) :=
  ((lam : ℂ))⁻¹ • transferOpL w β

@[simp] theorem normalisedTransferOpL_apply {L : ℕ} (w : (Fin L → Fin 2) → ℝ)
    (β lam : ℝ) (u : (Fin L → Fin 2) → ℂ) :
    normalisedTransferOpL w β lam u = ((lam : ℂ))⁻¹ • transferOp w β u := rfl

/-- The physical form is linear in its second argument. -/
theorem siteForm_smul_right {L : ℕ} (w : (Fin L → Fin 2) → ℝ) (c : ℂ)
    (u x : (Fin L → Fin 2) → ℂ) :
    siteForm w u (c • x) = c * siteForm w u x := by
  unfold siteForm
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  show (starRingEnd ℂ) (u σ) * (c * x σ) * ((1 / w σ : ℝ) : ℂ) = _
  ring

/-- **THE BRIDGE FROM THE OBJECT TO ITS FORM.**  Without this, the module
contains a definition of `T/lam` and, separately, an inequality about
`bondQ / lam`, with nothing saying they are the same thing.  An external reading
was right that "literally" was not yet earned. -/
theorem siteForm_normalisedTransferOpL {L : ℕ} {w : (Fin L → Fin 2) → ℝ}
    (hw : ∀ σ, 0 < w σ) (β lam : ℝ) (u v : (Fin L → Fin 2) → ℂ) :
    siteForm w u (normalisedTransferOpL w β lam v)
      = ((lam : ℂ))⁻¹ * bondForm β u v := by
  show siteForm w u (((lam : ℂ))⁻¹ • transferOp w β v) = _
  rw [siteForm_smul_right, siteForm_transferOp hw]

/-- And on the diagonal: the quadratic form of the normalised operator IS the
quotient the two-sided bound is about. -/
theorem siteForm_normalisedTransferOpL_self {L : ℕ} {w : (Fin L → Fin 2) → ℝ}
    (hw : ∀ σ, 0 < w σ) (β : ℝ) {lam : ℝ} (hlam : 0 < lam)
    (u : (Fin L → Fin 2) → ℂ) :
    siteForm w u (normalisedTransferOpL w β lam u)
      = ((bondQ β u / lam : ℝ) : ℂ) := by
  rw [siteForm_normalisedTransferOpL hw β lam u u, bondForm_self_eq_bondQ]
  push_cast
  rw [div_eq_inv_mul]

/-- The normalised operator inherits bijectivity, provided `lam ≠ 0`.  Stated
because the definition accepts any `lam` --- at `lam = 0` the field convention
`0⁻¹ = 0` makes it the zero map, and an object that silently degenerates is not
one a functional calculus should be handed. -/
theorem normalisedTransferOpL_bijective {L : ℕ} {w : (Fin L → Fin 2) → ℝ}
    (hw : ∀ σ, 0 < w σ) {β : ℝ} (hβ : 0 < β) {lam : ℝ} (hlam : 0 < lam) :
    Function.Bijective (normalisedTransferOpL w β lam) := by
  have hne : ((lam : ℂ))⁻¹ ≠ 0 :=
    inv_ne_zero (Complex.ofReal_ne_zero.mpr hlam.ne')
  have hinj : Function.Injective (normalisedTransferOpL w β lam) := by
    intro u v huv
    refine transferOpL_injective hw hβ ?_
    funext σ
    have hσ := congrFun huv σ
    show transferOp w β u σ = transferOp w β v σ
    have h' : ((lam : ℂ))⁻¹ * transferOp w β u σ
        = ((lam : ℂ))⁻¹ * transferOp w β v σ := hσ
    exact mul_left_cancel₀ hne h'
  exact ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩

/-- The normalised operator as an isomorphism. -/
noncomputable def normalisedTransferEquiv {L : ℕ} {w : (Fin L → Fin 2) → ℝ}
    (hw : ∀ σ, 0 < w σ) {β : ℝ} (hβ : 0 < β) {lam : ℝ} (hlam : 0 < lam) :
    ((Fin L → Fin 2) → ℂ) ≃ₗ[ℂ] ((Fin L → Fin 2) → ℂ) :=
  LinearEquiv.ofBijective (normalisedTransferOpL w β lam)
    (normalisedTransferOpL_bijective hw hβ hlam)

/-- **`(a/lam)·I ≤ T/lam ≤ I`**, literally: the normalised two-sided bound the
previous section's title claimed before the division existed.  With
`siteForm_normalisedTransferOpL_self` the middle term is the quadratic form of
the normalised OBJECT, not merely a quotient of numbers. -/
theorem normalised_two_sided {L : ℕ} {w : (Fin L → Fin 2) → ℝ}
    (hw : ∀ σ, 0 < w σ) {β : ℝ} (hβ : 0 < β) {Ω : (Fin L → Fin 2) → ℝ}
    (hΩ : ∀ σ, 0 < Ω σ) {lam : ℝ} (hlam : 0 < lam)
    (heig : ∀ σ, (∑ τ : Fin L → Fin 2, symWeighted w β σ τ * Ω τ) = lam * Ω σ)
    (u : (Fin L → Fin 2) → ℂ) :
    ((Real.exp β - Real.exp (-β)) ^ L * minWeight w / lam) * siteQ w u
        ≤ bondQ β u / lam
      ∧ bondQ β u / lam ≤ siteQ w u := by
  have hlo := bondQ_ge_siteQ hw hβ.le u
  have hhi := transferOp_le_perron hw β hΩ heig u
  constructor
  · rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hlam]
    exact hlo
  · rw [div_le_iff₀ hlam]
    calc bondQ β u ≤ lam * siteQ w u := hhi
      _ = siteQ w u * lam := by ring

/-! ## §8  The physical space as a quotient, packaged

v1.0 proved the collapse surjective and then said, in prose, that the null space
is its kernel and the quotient is the boundary space.  Both consequences are
elementary; neither was written down.  Here they are objects. -/

/-- The collapse as a linear map. -/
noncomputable def collapseL {L : ℕ} (w : (Fin L → Fin 2) → ℝ) (β : ℝ) (m : ℕ) :
    ((Fin (m + 1) → (Fin L → Fin 2)) → ℂ) →ₗ[ℂ] ((Fin L → Fin 2) → ℂ) where
  toFun F := collapse w β m F
  map_add' F G := by
    funext σ
    exact collapse_add w β m F G σ
  map_smul' c F := by
    funext σ
    exact collapse_smul w β m c F σ

@[simp] theorem collapseL_apply {L : ℕ} (w : (Fin L → Fin 2) → ℝ) (β : ℝ)
    (m : ℕ) (F : (Fin (m + 1) → (Fin L → Fin 2)) → ℂ) :
    collapseL w β m F = collapse w β m F := rfl

theorem collapseL_surjective {L : ℕ} {w : (Fin L → Fin 2) → ℝ}
    (hw : ∀ σ, 0 < w σ) (β : ℝ) (m : ℕ) :
    Function.Surjective (collapseL w β m) := fun v => collapse_surjective hw β m v

/-- **THE NULL SPACE OF THE REFLECTED FORM IS EXACTLY THE KERNEL OF THE
COLLAPSE.**  So the quotient below is by something identified, not by an
abstract null space that happens to be there. -/
theorem mem_ker_collapseL_iff {L : ℕ} {w : (Fin L → Fin 2) → ℝ}
    (hw : ∀ σ, 0 < w σ) (β : ℝ) (m : ℕ)
    (F : (Fin (m + 1) → (Fin L → Fin 2)) → ℂ) :
    F ∈ LinearMap.ker (collapseL w β m) ↔ osPairingSite w β m F = 0 := by
  rw [LinearMap.mem_ker]
  constructor
  · intro h
    have hcol : collapse w β m F = 0 := h
    rw [← osPairingSiteCross_self, ← siteForm_collapse, hcol]
    unfold siteForm
    simp
  · intro h
    have hz : siteForm w (collapse w β m F) (collapse w β m F) = 0 := by
      rw [siteForm_collapse, osPairingSiteCross_self, h]
    exact (siteForm_self_eq_zero_iff hw _).mp hz

/-- **THE PHYSICAL SPACE.**  The quotient of half-chain observables by the null
space of the reflected form IS the space of boundary vectors, linearly and in
the sense of a bundled equivalence. -/
noncomputable def physicalEquiv {L : ℕ} {w : (Fin L → Fin 2) → ℝ}
    (hw : ∀ σ, 0 < w σ) (β : ℝ) (m : ℕ) :
    (((Fin (m + 1) → (Fin L → Fin 2)) → ℂ) ⧸ LinearMap.ker (collapseL w β m))
      ≃ₗ[ℂ] ((Fin L → Fin 2) → ℂ) :=
  LinearMap.quotKerEquivOfSurjective _ (collapseL_surjective hw β m)

/-- **AND THE SAME ON THE PATH SUM ITSELF.**  Substituting the bond bridge on
the right: the transfer operator's matrix element between two half-chain
observables IS the reflected two-point sum of the Gibbs measure over whole
paths, one slice further apart.

Stated for two observables, not one.  The diagonal case would have been cheaper
and would have left the paper's displayed identity saying more than the formal
text did. -/
theorem osPairing_transfer_gibbsSum {L : ℕ} {w : (Fin L → Fin 2) → ℝ}
    (hw : ∀ σ, 0 < w σ) (β : ℝ) (m : ℕ)
    (F G : (Fin (m + 1) → (Fin L → Fin 2)) → ℂ) :
    siteForm w (collapse w β m F) (transferOp w β (collapse w β m G))
      = ∑ X : Fin ((m + 1) + (m + 1)) → (Fin L → Fin 2),
          (starRingEnd ℂ) (F (pastOf X)) * G (futRevOf X)
            * ((gibbsWeight w β (N := m + 1 + m) X : ℝ) : ℂ) := by
  rw [osPairing_transfer hw, ← osPairingBondCross_eq_gibbsSum]

end YangMills.OS
