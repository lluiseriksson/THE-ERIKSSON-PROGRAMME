/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson
-/
import Mathlib
import YangMills.OS.SpatialReflection

/-!
# The half chain, and the form that survives it

Paper 12 proved the reflected two-point form non-negative for **real** observables
of a **single** slice, at the two **ends** of a path.  The Osterwalder--Schrader
axiom asks for more: a **complex** observable of the whole **past half-chain**,
and the matrix `⟨Θ Fᵢ, Fⱼ⟩` positive semidefinite.  The gap was identified there
as a CONSTRUCTION rather than a further inequality, and this module builds it.

## The objects

A past half-path is a function `a : Fin (m+1) → (Fin L → Fin 2)`, and an
observable of the past half-chain is a function `F` of one, valued in `ℂ`.  Its
weight is the ordinary Gibbs weight of that half, `gibbsWeight w β a` --- no new
notion of weight is introduced anywhere in this file.

The reflection `Θ` is path reversal.  Reflecting through a BOND (`N = 2m+1`,
the plane between slices `m` and `m+1`) the two halves are disjoint; reflecting
through a SITE (`N = 2m`) they SHARE the middle slice, and that shared slice is
where the two cases genuinely differ.

## The collapse

`collapse` sums out the interior of a half and keeps only its boundary slice:

  `collapse w β m F σ = ∑ a, [a (last) = σ] * gibbsWeight w β a * F a`

Everything in this module is a corollary of the two identities saying the
pairing is a quadratic form in `collapse F` --- `osPairingSite_eq` and
`osPairingBond_eq` --- together with the kernel facts of paper 12.

## Pre-registration

`scripts/judge_spatial_os.py`, committed at `08a548cf` **before** a line of this
file was written.  Four gates, each licensing one theorem: A1 the site
factorisation, A2 the bond factorisation, B the `β ≥ 0` axiom form, C the
sharpness witness.  A1/A2 are matrix identities to `1e-12` against a pairing
matrix built by brute force over every full path; B and C read a MINIMUM
EIGENVALUE rather than sampling observables.  All four passed.

## What is NOT here

No reconstruction: the physical Hilbert space as the quotient by this form's
null space is not built in this file.
-/

namespace YangMills.OS

open Finset

/-! ## §1  Half-chain observables and the collapse to the boundary -/

/-- The boundary slice of a past half-path: the one adjacent to the reflection
plane. -/
noncomputable def edgeOf {L m : ℕ} (a : Fin (m + 1) → (Fin L → Fin 2)) :
    Fin L → Fin 2 := a (Fin.last m)

/-- The halves whose boundary slice is `σ`. -/
noncomputable def halvesAt (L m : ℕ) (σ : Fin L → Fin 2) :
    Finset (Fin (m + 1) → (Fin L → Fin 2)) :=
  Finset.univ.filter (fun a => edgeOf a = σ)

/-- **THE COLLAPSE.**  Summing out the interior of a half sends an observable of
the whole half-chain to a vector indexed by the boundary slice alone.  This is
the map the module is about: after it, both reflections reduce to statements
paper 12 already proved. -/
noncomputable def collapse {L : ℕ} (w : (Fin L → Fin 2) → ℝ) (β : ℝ) (m : ℕ)
    (F : (Fin (m + 1) → (Fin L → Fin 2)) → ℂ) (σ : Fin L → Fin 2) : ℂ :=
  ∑ a ∈ halvesAt L m σ, (gibbsWeight w β a : ℂ) * F a

/-- The collapse is additive in the observable. -/
theorem collapse_add {L : ℕ} (w : (Fin L → Fin 2) → ℝ) (β : ℝ) (m : ℕ)
    (F G : (Fin (m + 1) → (Fin L → Fin 2)) → ℂ) (σ : Fin L → Fin 2) :
    collapse w β m (fun a => F a + G a) σ
      = collapse w β m F σ + collapse w β m G σ := by
  unfold collapse
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun a _ => by ring

/-- The collapse is homogeneous. -/
theorem collapse_smul {L : ℕ} (w : (Fin L → Fin 2) → ℝ) (β : ℝ) (m : ℕ)
    (c : ℂ) (F : (Fin (m + 1) → (Fin L → Fin 2)) → ℂ) (σ : Fin L → Fin 2) :
    collapse w β m (fun a => c * F a) σ = c * collapse w β m F σ := by
  unfold collapse
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => by ring

/-- Regrouping a sum over halves by their boundary slice.  This is the only
combinatorial fact the factorisations need. -/
theorem sum_halves_by_edge {L m : ℕ} (f : (Fin (m + 1) → (Fin L → Fin 2)) → ℂ) :
    ∑ σ : Fin L → Fin 2, ∑ a ∈ halvesAt L m σ, f a
      = ∑ a : Fin (m + 1) → (Fin L → Fin 2), f a :=
  Finset.sum_fiberwise Finset.univ edgeOf f

/-! ## §2  The two pairings

Both are sums over PAIRS of halves, weighted by the ordinary Gibbs weight of
each half and by whatever the reflection plane contributes.  Through a bond that
is one kernel factor; through a site it is the shared slice, whose weight must
not be counted twice --- hence the division. -/

/-- The Osterwalder--Schrader pairing of a half-chain observable against its
reflection, through a BOND (`N = 2m+1`). -/
noncomputable def osPairingBond {L : ℕ} (w : (Fin L → Fin 2) → ℝ) (β : ℝ)
    (m : ℕ) (F : (Fin (m + 1) → (Fin L → Fin 2)) → ℂ) : ℂ :=
  ∑ a : Fin (m + 1) → (Fin L → Fin 2), ∑ b : Fin (m + 1) → (Fin L → Fin 2),
    (starRingEnd ℂ) (F a) * F b *
      ((gibbsWeight w β a * spatialKernel β (edgeOf a) (edgeOf b)
          * gibbsWeight w β b : ℝ) : ℂ)

/-- The Osterwalder--Schrader pairing through a SITE (`N = 2m`).  Only pairs of
halves agreeing on the shared slice come from a path, and that slice's weight is
carried by both halves, so it is divided out once. -/
noncomputable def osPairingSite {L : ℕ} (w : (Fin L → Fin 2) → ℝ) (β : ℝ)
    (m : ℕ) (F : (Fin (m + 1) → (Fin L → Fin 2)) → ℂ) : ℂ :=
  ∑ σ : Fin L → Fin 2, ∑ a ∈ halvesAt L m σ, ∑ b ∈ halvesAt L m σ,
    (starRingEnd ℂ) (F a) * F b *
      ((gibbsWeight w β a * gibbsWeight w β b / w σ : ℝ) : ℂ)

/-! ## §3  Gate A1 — the SITE factorisation -/

/-- **THE SITE FACTORISATION.**  Through a site the pairing is a sum of squared
moduli of the boundary vector, weighted by `1/w`, at EVERY `β`.  No property of
the kernel is used: the halves meet only in the shared slice. -/
theorem osPairingSite_eq {L : ℕ} (w : (Fin L → Fin 2) → ℝ) (β : ℝ) (m : ℕ)
    (F : (Fin (m + 1) → (Fin L → Fin 2)) → ℂ) :
    osPairingSite w β m F
      = ∑ σ : Fin L → Fin 2,
          ((Complex.normSq (collapse w β m F σ) / w σ : ℝ) : ℂ) := by
  unfold osPairingSite collapse
  refine Finset.sum_congr rfl fun σ _ => ?_
  have hsplit : ∀ a ∈ halvesAt L m σ, ∀ b ∈ halvesAt L m σ,
      (starRingEnd ℂ) (F a) * F b
          * ((gibbsWeight w β a * gibbsWeight w β b / w σ : ℝ) : ℂ)
        = ((starRingEnd ℂ) ((gibbsWeight w β a : ℂ) * F a)
            * ((gibbsWeight w β b : ℂ) * F b)) * ((1 / w σ : ℝ) : ℂ) := by
    intro a _ b _
    simp only [map_mul, Complex.conj_ofReal]
    push_cast
    ring
  rw [Finset.sum_congr rfl fun a ha =>
        Finset.sum_congr rfl fun b hb => hsplit a ha b hb]
  simp only [← Finset.sum_mul]
  rw [← Finset.sum_mul_sum, ← map_sum, mul_comm ((starRingEnd ℂ) _) _,
    Complex.mul_conj]
  push_cast
  ring

/-- **THROUGH A SITE, AT EVERY `β`.**  The pairing is a non-negative real for
every coupling, negative included, provided only that the weight is positive.
This is the half-chain form of paper 12's even-separation theorem, and it is now
about COMPLEX observables of the WHOLE half. -/
theorem osPairingSite_nonneg {L : ℕ} {w : (Fin L → Fin 2) → ℝ}
    (hw : ∀ σ, 0 < w σ) (β : ℝ) (m : ℕ)
    (F : (Fin (m + 1) → (Fin L → Fin 2)) → ℂ) :
    ∃ r : ℝ, 0 ≤ r ∧ osPairingSite w β m F = (r : ℂ) := by
  refine ⟨∑ σ : Fin L → Fin 2, Complex.normSq (collapse w β m F σ) / w σ,
    Finset.sum_nonneg fun σ _ =>
      div_nonneg (Complex.normSq_nonneg _) (hw σ).le, ?_⟩
  rw [osPairingSite_eq]
  push_cast
  rfl

/-! ## §4  The real-to-complex step, once and generically

For a real SYMMETRIC kernel the complex quadratic form is the sum of the forms
on the real and imaginary parts: the cross terms cancel against each other by
symmetry.  This is the whole content of "real observables to complex ones", and
it costs nothing beyond symmetry. -/

/-- The cross terms of a symmetric real form cancel. -/
theorem sum_cross_antisymm {ι : Type*} [Fintype ι] {K : ι → ι → ℝ}
    (hsym : ∀ i j, K i j = K j i) (x y : ι → ℝ) :
    ∑ i, ∑ j, K i j * (x i * y j) = ∑ i, ∑ j, K i j * (x j * y i) := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [hsym j i]
  try ring

/-- **THE REAL-TO-COMPLEX STEP.**  For a real symmetric kernel the complex
sesquilinear form is exactly the sum of the real forms on the real and imaginary
parts.  Nothing here is special to this kernel. -/
theorem complexQuad_eq {ι : Type*} [Fintype ι] {K : ι → ι → ℝ}
    (hsym : ∀ i j, K i j = K j i) (z : ι → ℂ) :
    ∑ i, ∑ j, (starRingEnd ℂ) (z i) * ((K i j : ℝ) : ℂ) * z j
      = (((∑ i, ∑ j, K i j * ((z i).re * (z j).re))
          + ∑ i, ∑ j, K i j * ((z i).im * (z j).im) : ℝ) : ℂ) := by
  have hre : ∀ i j, (starRingEnd ℂ) (z i) * ((K i j : ℝ) : ℂ) * z j
      = ((K i j * ((z i).re * (z j).re) + K i j * ((z i).im * (z j).im) : ℝ) : ℂ)
        + ((K i j * ((z i).re * (z j).im) - K i j * ((z i).im * (z j).re) : ℝ) : ℂ)
            * Complex.I := by
    intro i j
    apply Complex.ext <;>
      simp [Complex.conj_re, Complex.conj_im] <;> ring
  rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hre i j]
  have hzero : ∑ i, ∑ j : ι,
      ((K i j * ((z i).re * (z j).im) - K i j * ((z i).im * (z j).re) : ℝ) : ℂ)
          * Complex.I = 0 := by
    have : ∑ i, ∑ j : ι,
        (K i j * ((z i).re * (z j).im) - K i j * ((z i).im * (z j).re)) = (0:ℝ) := by
      have h1 := sum_cross_antisymm hsym (fun i => (z i).re) (fun i => (z i).im)
      have h2 : ∀ i j : ι, K i j * ((z i).im * (z j).re)
          = K i j * ((z j).re * (z i).im) := by intro i j; ring
      simp only [Finset.sum_sub_distrib]
      rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => h2 i j]
      linarith [h1]
    calc ∑ i, ∑ j : ι,
          ((K i j * ((z i).re * (z j).im) - K i j * ((z i).im * (z j).re) : ℝ) : ℂ)
            * Complex.I
        = ((∑ i, ∑ j : ι,
            (K i j * ((z i).re * (z j).im) - K i j * ((z i).im * (z j).re)) : ℝ) : ℂ)
              * Complex.I := by
          push_cast
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun i _ => by rw [Finset.sum_mul]
      _ = 0 := by rw [this]; simp
  rw [Finset.sum_congr rfl fun i _ => Finset.sum_add_distrib]
  rw [Finset.sum_add_distrib, hzero, add_zero]
  push_cast
  simp only [Finset.sum_add_distrib]

/-! ## §5  Gate A2 — the BOND factorisation, and the axiom form for `β ≥ 0` -/

/-- **THE BOND FACTORISATION.**  Through a bond the pairing is the quadratic
form of the DECOUPLED kernel in the boundary vector.  The source weight has
disappeared into `collapse`; it is not conjugated away, it is summed away. -/
theorem osPairingBond_eq {L : ℕ} (w : (Fin L → Fin 2) → ℝ) (β : ℝ) (m : ℕ)
    (F : (Fin (m + 1) → (Fin L → Fin 2)) → ℂ) :
    osPairingBond w β m F
      = ∑ σ : Fin L → Fin 2, ∑ τ : Fin L → Fin 2,
          (starRingEnd ℂ) (collapse w β m F σ)
            * ((spatialKernel β σ τ : ℝ) : ℂ) * collapse w β m F τ := by
  have hinner : ∀ a : Fin (m + 1) → (Fin L → Fin 2),
      (∑ b : Fin (m + 1) → (Fin L → Fin 2), (starRingEnd ℂ) (F a) * F b *
          ((gibbsWeight w β a * spatialKernel β (edgeOf a) (edgeOf b)
              * gibbsWeight w β b : ℝ) : ℂ))
        = ∑ τ : Fin L → Fin 2,
            (starRingEnd ℂ) ((gibbsWeight w β a : ℂ) * F a)
              * ((spatialKernel β (edgeOf a) τ : ℝ) : ℂ)
              * collapse w β m F τ := by
    intro a
    rw [← sum_halves_by_edge (m := m)
          (f := fun b => (starRingEnd ℂ) (F a) * F b *
            ((gibbsWeight w β a * spatialKernel β (edgeOf a) (edgeOf b)
                * gibbsWeight w β b : ℝ) : ℂ))]
    refine Finset.sum_congr rfl fun τ _ => ?_
    unfold collapse
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b hb => ?_
    have hbτ : edgeOf b = τ := (Finset.mem_filter.mp hb).2
    rw [hbτ]
    simp only [map_mul, Complex.conj_ofReal]
    push_cast
    ring
  unfold osPairingBond
  rw [Finset.sum_congr rfl fun a _ => hinner a]
  rw [← sum_halves_by_edge (m := m)
        (f := fun a => ∑ τ : Fin L → Fin 2,
          (starRingEnd ℂ) ((gibbsWeight w β a : ℂ) * F a)
            * ((spatialKernel β (edgeOf a) τ : ℝ) : ℂ) * collapse w β m F τ)]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have hedge : ∀ a ∈ halvesAt L m σ,
      (starRingEnd ℂ) ((gibbsWeight w β a : ℂ) * F a)
          * ((spatialKernel β (edgeOf a) τ : ℝ) : ℂ) * collapse w β m F τ
        = (starRingEnd ℂ) ((gibbsWeight w β a : ℂ) * F a)
            * (((spatialKernel β σ τ : ℝ) : ℂ) * collapse w β m F τ) := by
    intro a ha
    rw [(Finset.mem_filter.mp ha).2]
    ring
  rw [Finset.sum_congr rfl hedge, ← Finset.sum_mul, ← map_sum]
  unfold collapse
  ring

/-- **THROUGH A BOND, EXACTLY FOR `β ≥ 0`.**  The pairing of a COMPLEX
observable of the WHOLE past half-chain against its reflection is a non-negative
real.  This is the Osterwalder--Schrader form, for this slice, at odd
separation. -/
theorem osPairingBond_nonneg {L : ℕ} (w : (Fin L → Fin 2) → ℝ) {β : ℝ}
    (hβ : 0 ≤ β) (m : ℕ) (F : (Fin (m + 1) → (Fin L → Fin 2)) → ℂ) :
    ∃ r : ℝ, 0 ≤ r ∧ osPairingBond w β m F = (r : ℂ) := by
  classical
  set z : (Fin L → Fin 2) → ℂ := collapse w β m F with hz
  have hsym : ∀ σ τ : Fin L → Fin 2,
      spatialKernel β σ τ = spatialKernel β τ σ := spatialKernel_symm β
  have hquad : ∀ u : (Fin L → Fin 2) → ℝ,
      0 ≤ ∑ σ, ∑ τ, spatialKernel β σ τ * (u σ * u τ) := by
    intro u
    have h := spatialKernel_posSemidef hβ L u
    have : ∑ σ, u σ * act (spatialKernel β) u σ
        = ∑ σ, ∑ τ, spatialKernel β σ τ * (u σ * u τ) := by
      unfold act
      refine Finset.sum_congr rfl fun σ _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun τ _ => by ring
    linarith [this ▸ h]
  refine ⟨(∑ σ, ∑ τ, spatialKernel β σ τ * ((z σ).re * (z τ).re))
      + ∑ σ, ∑ τ, spatialKernel β σ τ * ((z σ).im * (z τ).im),
    by have h1 := hquad (fun σ => (z σ).re)
       have h2 := hquad (fun σ => (z σ).im)
       linarith, ?_⟩
  rw [osPairingBond_eq, complexQuad_eq hsym z]

end YangMills.OS
