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
as a CONSTRUCTION rather than a further inequality.  This module builds it.

**THE BOND BRIDGE IS CLOSED.**  `bondEquiv` says a whole path of `2m+2` slices
IS a pair of halves, `gibbsWeight_joinBond` says the weights multiply with the
one crossing factor, and `osPairingBond_eq_gibbsSum` composes them: the bond form
is the reflected two-point sum of the Gibbs measure, the reflection entering
through the PAIR `(pastOf, futRevOf)`.  At odd separation the positivity
theorems are therefore about the MEASURE, not about a form standing in for it.

**THE SITE BRIDGE IS NOT.**  Through a site the halves SHARE the middle slice, so
pairs of halves are not a product but a fibred product over that slice, and the
weight of the shared slice is counted twice and must be divided out.  That is a
different statement, not a variation on the bond one.  Until it is proved,
`osPairingSite` remains a CANDIDATE: it is positive and has a PSD Gram matrix,
but its full-path identification is open, and the only evidence for it is a
pre-registered gate verifying it to `1e-12` against brute-force enumeration.

`futRevOf` sends a PATH to a HALF --- the reflected future half.  It is not an
involution on paths and is deliberately not called `Θ` anywhere; the reflection
enters through the PAIR `(pastOf, futRevOf)`, which is what the pairing is built
from.

## The objects

A past half-path is a function `a : Fin (m+1) → (Fin L → Fin 2)`, and an
observable of the past half-chain is a function `F` of one, valued in `ℂ`.  Its
weight is the ordinary Gibbs weight of that half, `gibbsWeight w β a` --- no new
notion of weight is introduced anywhere in this file.

Reflection means reading a half backwards from the far end.  Through a BOND
(`N = 2m+1`,
the plane between slices `m` and `m+1`) the two halves are disjoint; reflecting
through a SITE (`N = 2m`) they SHARE the middle slice, and that shared slice is
where the two cases genuinely differ.

## The collapse

`collapse` sums out the interior of a half and keeps only its boundary slice:

  `collapse w β m F σ = ∑ a, [a (last) = σ] * gibbsWeight w β a * F a`

Every POSITIVITY result for the two half-chain forms is a corollary of the two
identities saying the pairing is a quadratic form in `collapse F` ---
`osPairingSite_eq` and `osPairingBond_eq` --- together with the kernel facts of
paper 12.  Identifying the BOND form with the full-path Gibbs measure needs a
second layer that is not a corollary of those: the assembly `joinBond`, the
equivalence `bondEquiv`, and the weight identity `gibbsWeight_joinBond`.

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

/-- The reflected form of a half-chain observable, through a BOND (`N = 2m+1`).
That this IS the reflected Gibbs sum over whole paths is proved below, at
`osPairingBond_eq_gibbsSum`; it is stated first in this convenient form because
every factorisation argument runs on it. -/
noncomputable def osPairingBond {L : ℕ} (w : (Fin L → Fin 2) → ℝ) (β : ℝ)
    (m : ℕ) (F : (Fin (m + 1) → (Fin L → Fin 2)) → ℂ) : ℂ :=
  ∑ a : Fin (m + 1) → (Fin L → Fin 2), ∑ b : Fin (m + 1) → (Fin L → Fin 2),
    (starRingEnd ℂ) (F a) * F b *
      ((gibbsWeight w β a * spatialKernel β (edgeOf a) (edgeOf b)
          * gibbsWeight w β b : ℝ) : ℂ)

/-- The CANDIDATE reflected form through a SITE (`N = 2m`).  Only pairs of
halves agreeing on the shared slice come from a path, and that slice's weight is
carried by both halves, so it is divided out once.  Still a CANDIDATE, and now
for a reason the bond form no longer shares: the site full-path bridge is open,
the bond one is proved. -/
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

/-- **THROUGH A BOND, FOR `β ≥ 0`.**  The pairing of a COMPLEX observable of the
WHOLE past half-chain against its reflection is a non-negative real.

SUFFICIENCY ONLY.  Necessity is NOT proved anywhere in this module, and there is
no witness for it here.  It could not hold at `L = 0` in any case: the bare
kernel is the scalar `1` there.  From one site upwards it is expected and
authorised by a pre-registered gate, and writing it is open work. -/
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

/-! ## §6  The Gram statement

Reflection positivity is a statement about a MATRIX over a finite family being
positive semidefinite, not about one diagonal entry.  The cross form is defined,
its factorisation proved, and the matrix assembled from it. -/

/-- Reordering a four-fold sum.  Stated separately because it is the only step
in the Gram assembly, and burying it inside a proof would hide that. -/
theorem sum_comm4 {A B C D : Type*} [Fintype A] [Fintype B] [Fintype C]
    [Fintype D] (f : A → B → C → D → ℂ) :
    (∑ i, ∑ j, ∑ s, ∑ u, f i j s u) = ∑ s, ∑ u, ∑ i, ∑ j, f i j s u := by
  have h1 : (∑ i, ∑ j, ∑ s, ∑ u, f i j s u)
      = ∑ i, ∑ s, ∑ j, ∑ u, f i j s u :=
    Finset.sum_congr rfl fun _ _ => Finset.sum_comm
  have h2 : (∑ i, ∑ s, ∑ j, ∑ u, f i j s u)
      = ∑ s, ∑ i, ∑ j, ∑ u, f i j s u := Finset.sum_comm
  have h3 : (∑ s, ∑ i, ∑ j, ∑ u, f i j s u)
      = ∑ s, ∑ i, ∑ u, ∑ j, f i j s u :=
    Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => Finset.sum_comm
  have h4 : (∑ s, ∑ i, ∑ u, ∑ j, f i j s u)
      = ∑ s, ∑ u, ∑ i, ∑ j, f i j s u :=
    Finset.sum_congr rfl fun _ _ => Finset.sum_comm
  rw [h1, h2, h3, h4]

/-- The three-fold sibling of `sum_comm4`, needed by the site assembly. -/
theorem sum_comm3 {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (f : A → B → C → ℂ) :
    (∑ i, ∑ j, ∑ s, f i j s) = ∑ s, ∑ i, ∑ j, f i j s := by
  have h1 : (∑ i, ∑ j, ∑ s, f i j s) = ∑ i, ∑ s, ∑ j, f i j s :=
    Finset.sum_congr rfl fun _ _ => Finset.sum_comm
  rw [h1, Finset.sum_comm]

/-- The CROSS form through a bond: one observable against the reflection of
another.  Its diagonal is the form of §2. -/
noncomputable def osPairingBondCross {L : ℕ} (w : (Fin L → Fin 2) → ℝ) (β : ℝ)
    (m : ℕ) (F G : (Fin (m + 1) → (Fin L → Fin 2)) → ℂ) : ℂ :=
  ∑ a : Fin (m + 1) → (Fin L → Fin 2), ∑ b : Fin (m + 1) → (Fin L → Fin 2),
    (starRingEnd ℂ) (F a) * G b *
      ((gibbsWeight w β a * spatialKernel β (edgeOf a) (edgeOf b)
          * gibbsWeight w β b : ℝ) : ℂ)

/-- The diagonal of the cross form is the form itself. -/
theorem osPairingBondCross_self {L : ℕ} (w : (Fin L → Fin 2) → ℝ) (β : ℝ) (m : ℕ)
    (F : (Fin (m + 1) → (Fin L → Fin 2)) → ℂ) :
    osPairingBondCross w β m F F = osPairingBond w β m F := rfl

/-- The collapse of a linear combination is the combination of the collapses. -/
theorem collapse_sum {L : ℕ} (w : (Fin L → Fin 2) → ℝ) (β : ℝ) (m : ℕ)
    {ι : Type*} [Fintype ι] (c : ι → ℂ)
    (F : ι → (Fin (m + 1) → (Fin L → Fin 2)) → ℂ) (σ : Fin L → Fin 2) :
    collapse w β m (fun a => ∑ i, c i * F i a) σ
      = ∑ i, c i * collapse w β m (F i) σ := by
  unfold collapse
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun a _ => by ring

/-- The cross form factors through the collapse, exactly as the diagonal one
does. -/
theorem osPairingBondCross_eq {L : ℕ} (w : (Fin L → Fin 2) → ℝ) (β : ℝ) (m : ℕ)
    (F G : (Fin (m + 1) → (Fin L → Fin 2)) → ℂ) :
    osPairingBondCross w β m F G
      = ∑ σ : Fin L → Fin 2, ∑ τ : Fin L → Fin 2,
          (starRingEnd ℂ) (collapse w β m F σ)
            * ((spatialKernel β σ τ : ℝ) : ℂ) * collapse w β m G τ := by
  have hinner : ∀ a : Fin (m + 1) → (Fin L → Fin 2),
      (∑ b : Fin (m + 1) → (Fin L → Fin 2), (starRingEnd ℂ) (F a) * G b *
          ((gibbsWeight w β a * spatialKernel β (edgeOf a) (edgeOf b)
              * gibbsWeight w β b : ℝ) : ℂ))
        = ∑ τ : Fin L → Fin 2,
            (starRingEnd ℂ) ((gibbsWeight w β a : ℂ) * F a)
              * ((spatialKernel β (edgeOf a) τ : ℝ) : ℂ)
              * collapse w β m G τ := by
    intro a
    rw [← sum_halves_by_edge (m := m)
          (f := fun b => (starRingEnd ℂ) (F a) * G b *
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
  unfold osPairingBondCross
  rw [Finset.sum_congr rfl fun a _ => hinner a]
  rw [← sum_halves_by_edge (m := m)
        (f := fun a => ∑ τ : Fin L → Fin 2,
          (starRingEnd ℂ) ((gibbsWeight w β a : ℂ) * F a)
            * ((spatialKernel β (edgeOf a) τ : ℝ) : ℂ) * collapse w β m G τ)]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have hedge : ∀ a ∈ halvesAt L m σ,
      (starRingEnd ℂ) ((gibbsWeight w β a : ℂ) * F a)
          * ((spatialKernel β (edgeOf a) τ : ℝ) : ℂ) * collapse w β m G τ
        = (starRingEnd ℂ) ((gibbsWeight w β a : ℂ) * F a)
            * (((spatialKernel β σ τ : ℝ) : ℂ) * collapse w β m G τ) := by
    intro a ha
    rw [(Finset.mem_filter.mp ha).2]
    ring
  rw [Finset.sum_congr rfl hedge, ← Finset.sum_mul, ← map_sum]
  unfold collapse
  ring

/-- **THE GRAM MATRIX.**  The finite-family statement, which is the shape the
axiom actually has.  It equals the form of the combined observable, so
positivity transports to it rather than being re-proved. -/
theorem osPairingBond_gram {L : ℕ} (w : (Fin L → Fin 2) → ℝ) (β : ℝ) (m : ℕ)
    {ι : Type*} [Fintype ι] (c : ι → ℂ)
    (F : ι → (Fin (m + 1) → (Fin L → Fin 2)) → ℂ) :
    (∑ i, ∑ j, (starRingEnd ℂ) (c i) * c j * osPairingBondCross w β m (F i) (F j))
      = osPairingBond w β m (fun a => ∑ i, c i * F i a) := by
  have hL : ∀ i j, (starRingEnd ℂ) (c i) * c j * osPairingBondCross w β m (F i) (F j)
      = ∑ σ : Fin L → Fin 2, ∑ τ : Fin L → Fin 2,
          ((starRingEnd ℂ) (c i) * (starRingEnd ℂ) (collapse w β m (F i) σ))
            * ((spatialKernel β σ τ : ℝ) : ℂ) * (c j * collapse w β m (F j) τ) := by
    intro i j
    rw [osPairingBondCross_eq, Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun τ _ => by ring
  rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hL i j]
  rw [sum_comm4]
  rw [osPairingBond_eq]
  refine Finset.sum_congr rfl fun σ _ => ?_
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [collapse_sum, collapse_sum, map_sum, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [map_mul]
  try ring

/-- **THE AXIOM SHAPE, for `β ≥ 0`.**  For every finite family of complex
observables of the whole past half-chain, and every complex coefficients, the
Gram matrix of the bond form is positive semidefinite. -/
theorem osPairingBond_gram_nonneg {L : ℕ} (w : (Fin L → Fin 2) → ℝ) {β : ℝ}
    (hβ : 0 ≤ β) (m : ℕ) {ι : Type*} [Fintype ι] (c : ι → ℂ)
    (F : ι → (Fin (m + 1) → (Fin L → Fin 2)) → ℂ) :
    ∃ r : ℝ, 0 ≤ r ∧
      (∑ i, ∑ j, (starRingEnd ℂ) (c i) * c j
        * osPairingBondCross w β m (F i) (F j)) = (r : ℂ) := by
  rw [osPairingBond_gram]
  exact osPairingBond_nonneg w hβ m _

/-! ## §7  The Gram statement for the site reflection

The subtitle of this work says TWO reflections; a Gram matrix for one of them
only would not honour that.  The site case is cheaper than the bond case --- no
kernel enters --- and it holds at every `β`. -/

/-- The CROSS form through a site: one observable against the reflection of
another.  Its diagonal is the form of §2. -/
noncomputable def osPairingSiteCross {L : ℕ} (w : (Fin L → Fin 2) → ℝ) (β : ℝ)
    (m : ℕ) (F G : (Fin (m + 1) → (Fin L → Fin 2)) → ℂ) : ℂ :=
  ∑ σ : Fin L → Fin 2, ∑ a ∈ halvesAt L m σ, ∑ b ∈ halvesAt L m σ,
    (starRingEnd ℂ) (F a) * G b *
      ((gibbsWeight w β a * gibbsWeight w β b / w σ : ℝ) : ℂ)

/-- The diagonal of the site cross form is the site form. -/
theorem osPairingSiteCross_self {L : ℕ} (w : (Fin L → Fin 2) → ℝ) (β : ℝ) (m : ℕ)
    (F : (Fin (m + 1) → (Fin L → Fin 2)) → ℂ) :
    osPairingSiteCross w β m F F = osPairingSite w β m F := rfl

/-- The site cross form factors through the collapse: it is the `1/w`-weighted
Hermitian product of the two boundary vectors. -/
theorem osPairingSiteCross_eq {L : ℕ} (w : (Fin L → Fin 2) → ℝ) (β : ℝ) (m : ℕ)
    (F G : (Fin (m + 1) → (Fin L → Fin 2)) → ℂ) :
    osPairingSiteCross w β m F G
      = ∑ σ : Fin L → Fin 2,
          (starRingEnd ℂ) (collapse w β m F σ) * collapse w β m G σ
            * ((1 / w σ : ℝ) : ℂ) := by
  unfold osPairingSiteCross collapse
  refine Finset.sum_congr rfl fun σ _ => ?_
  have hsplit : ∀ a ∈ halvesAt L m σ, ∀ b ∈ halvesAt L m σ,
      (starRingEnd ℂ) (F a) * G b
          * ((gibbsWeight w β a * gibbsWeight w β b / w σ : ℝ) : ℂ)
        = ((starRingEnd ℂ) ((gibbsWeight w β a : ℂ) * F a)
            * ((gibbsWeight w β b : ℂ) * G b)) * ((1 / w σ : ℝ) : ℂ) := by
    intro a _ b _
    simp only [map_mul, Complex.conj_ofReal]
    push_cast
    ring
  rw [Finset.sum_congr rfl fun a ha =>
        Finset.sum_congr rfl fun b hb => hsplit a ha b hb]
  simp only [← Finset.sum_mul]
  rw [← Finset.sum_mul_sum, ← map_sum]

/-- **THE SITE GRAM MATRIX.**  Same architecture as the bond one: the Gram sum
IS the form of the combined observable, so positivity transports. -/
theorem osPairingSite_gram {L : ℕ} (w : (Fin L → Fin 2) → ℝ) (β : ℝ) (m : ℕ)
    {ι : Type*} [Fintype ι] (c : ι → ℂ)
    (F : ι → (Fin (m + 1) → (Fin L → Fin 2)) → ℂ) :
    (∑ i, ∑ j, (starRingEnd ℂ) (c i) * c j * osPairingSiteCross w β m (F i) (F j))
      = osPairingSite w β m (fun a => ∑ i, c i * F i a) := by
  have hL : ∀ i j, (starRingEnd ℂ) (c i) * c j * osPairingSiteCross w β m (F i) (F j)
      = ∑ σ : Fin L → Fin 2,
          ((starRingEnd ℂ) (c i) * (starRingEnd ℂ) (collapse w β m (F i) σ))
            * (c j * collapse w β m (F j) σ) * ((1 / w σ : ℝ) : ℂ) := by
    intro i j
    rw [osPairingSiteCross_eq, Finset.mul_sum]
    exact Finset.sum_congr rfl fun σ _ => by ring
  rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hL i j]
  rw [sum_comm3]
  rw [← osPairingSiteCross_self, osPairingSiteCross_eq]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [collapse_sum, map_sum, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [map_mul]
  try ring

/-- **THE SITE GRAM MATRIX IS PSD, AT EVERY `β`.**  Only `w > 0` is used. -/
theorem osPairingSite_gram_nonneg {L : ℕ} {w : (Fin L → Fin 2) → ℝ}
    (hw : ∀ σ, 0 < w σ) (β : ℝ) (m : ℕ) {ι : Type*} [Fintype ι] (c : ι → ℂ)
    (F : ι → (Fin (m + 1) → (Fin L → Fin 2)) → ℂ) :
    ∃ r : ℝ, 0 ≤ r ∧
      (∑ i, ∑ j, (starRingEnd ℂ) (c i) * c j
        * osPairingSiteCross w β m (F i) (F j)) = (r : ℂ) := by
  rw [osPairingSite_gram]
  exact osPairingSite_nonneg hw β m _

/-! ## §8  The assembly, and the bijection onto whole paths

This is the link the abstract says decides what this paper is.  A full path of
`2m+2` slices is exactly a pair of halves: the past half read forwards, and the
future half read backwards from the far end.  `joinBond` performs the assembly,
`pastOf` and `futRevOf` undo it, and the three lemmas below say they are mutually
inverse — so summing over pairs of halves IS summing over paths.

Nothing here is about weights yet; that is the next step.  Splitting the two
makes the bijection checkable on its own. -/

/-- The assembly: past half forwards, then future half backwards. -/
noncomputable def joinBond {L m : ℕ} (a b : Fin (m + 1) → (Fin L → Fin 2)) :
    Fin ((m + 1) + (m + 1)) → (Fin L → Fin 2) :=
  Fin.append a (fun i => b (Fin.rev i))

/-- The past half of a whole path. -/
noncomputable def pastOf {L m : ℕ}
    (X : Fin ((m + 1) + (m + 1)) → (Fin L → Fin 2)) :
    Fin (m + 1) → (Fin L → Fin 2) := fun i => X (Fin.castAdd (m + 1) i)

/-- The future half of a whole path, read backwards from the far end: the
reflected copy.  It sends a PATH to a HALF, so it is not an involution on paths
and is not `Θ`; together with `pastOf` it defines the reflected pairing. -/
noncomputable def futRevOf {L m : ℕ}
    (X : Fin ((m + 1) + (m + 1)) → (Fin L → Fin 2)) :
    Fin (m + 1) → (Fin L → Fin 2) := fun i => X (Fin.natAdd (m + 1) (Fin.rev i))

@[simp] theorem pastOf_joinBond {L m : ℕ}
    (a b : Fin (m + 1) → (Fin L → Fin 2)) : pastOf (joinBond a b) = a := by
  funext i
  simp [pastOf, joinBond, Fin.append_left]

@[simp] theorem futRevOf_joinBond {L m : ℕ}
    (a b : Fin (m + 1) → (Fin L → Fin 2)) : futRevOf (joinBond a b) = b := by
  funext i
  show Fin.append a (fun j => b (Fin.rev j)) (Fin.natAdd (m + 1) (Fin.rev i)) = b i
  rw [Fin.append_right, Fin.rev_rev]

theorem joinBond_pastOf_futRevOf {L m : ℕ}
    (X : Fin ((m + 1) + (m + 1)) → (Fin L → Fin 2)) :
    joinBond (pastOf X) (futRevOf X) = X := by
  funext t
  induction t using Fin.addCases with
  | left i => simp [joinBond, pastOf, Fin.append_left]
  | right i =>
      show Fin.append (pastOf X) (fun j => futRevOf X (Fin.rev j))
          (Fin.natAdd (m + 1) i) = X (Fin.natAdd (m + 1) i)
      rw [Fin.append_right]
      show X (Fin.natAdd (m + 1) (Fin.rev (Fin.rev i))) = X (Fin.natAdd (m + 1) i)
      rw [Fin.rev_rev]

/-- **THE ASSEMBLY IS A BIJECTION.**  Pairs of halves and whole paths are the
same finite set, so a sum over one is a sum over the other. -/
noncomputable def bondEquiv (L m : ℕ) :
    ((Fin (m + 1) → (Fin L → Fin 2)) × (Fin (m + 1) → (Fin L → Fin 2)))
      ≃ (Fin ((m + 1) + (m + 1)) → (Fin L → Fin 2)) where
  toFun p := joinBond p.1 p.2
  invFun X := (pastOf X, futRevOf X)
  left_inv p := by
    ext1 <;> simp
  right_inv X := joinBond_pastOf_futRevOf X

/-! ### The weight identity for the assembly

The other half of the bond bridge.  The Gibbs weight of an assembled path is the
weight of each half times the ONE kernel factor that crosses the plane, and
nothing else --- which is exactly why the collapse works.

The bookkeeping is index arithmetic.  Every position is converted to a `castAdd`
or a `natAdd` by an explicit lemma rather than by `simp`, because `simp`
normalises `natAdd` into `addNat` and then `Fin.append_right` stops matching. -/

theorem joinBond_left {L m : ℕ} (a b : Fin (m + 1) → (Fin L → Fin 2))
    (i : Fin (m + 1)) : joinBond a b (Fin.castAdd (m + 1) i) = a i :=
  Fin.append_left _ _ _

theorem joinBond_right {L m : ℕ} (a b : Fin (m + 1) → (Fin L → Fin 2))
    (i : Fin (m + 1)) : joinBond a b (Fin.natAdd (m + 1) i) = b (Fin.rev i) :=
  Fin.append_right _ _ _

theorem rev_castSucc_eq {m : ℕ} (i : Fin m) :
    Fin.rev (Fin.castSucc i) = Fin.succ (Fin.rev i) := by
  ext
  simp [Fin.val_rev]
  try omega

theorem rev_succ_eq {m : ℕ} (i : Fin m) :
    Fin.rev (Fin.succ i) = Fin.castSucc (Fin.rev i) := by
  ext
  simp [Fin.val_rev]
  try omega

/-- The `w` factors of an assembled path are exactly those of the two halves. -/
theorem prod_w_joinBond {L m : ℕ} (w : (Fin L → Fin 2) → ℝ)
    (a b : Fin (m + 1) → (Fin L → Fin 2)) :
    (∏ t : Fin ((m + 1) + (m + 1)), w (joinBond a b t))
      = (∏ t : Fin (m + 1), w (a t)) * ∏ t : Fin (m + 1), w (b t) := by
  rw [Fin.prod_univ_add]
  congr 1
  · exact Finset.prod_congr rfl fun i _ => by rw [joinBond_left]
  · have h1 : (∏ i : Fin (m + 1), w (joinBond a b (Fin.natAdd (m + 1) i)))
        = ∏ i : Fin (m + 1), w (b (Fin.rev i)) :=
      Finset.prod_congr rfl fun i _ => by rw [joinBond_right]
    rw [h1]
    simpa using Equiv.prod_comp (Fin.revPerm (n := m + 1)) (fun i => w (b i))

/-- The kernel factors split into: the bonds inside the past half, the ONE bond
that crosses the reflection plane, and the bonds inside the future half --- the
last of these read backwards, which the symmetry of the kernel undoes. -/
theorem prod_K_joinBond {L m : ℕ} (β : ℝ)
    (a b : Fin (m + 1) → (Fin L → Fin 2)) :
    (∏ t : Fin ((m + 1) + m),
        spatialKernel β (joinBond a b t.castSucc) (joinBond a b t.succ))
      = ((∏ t : Fin m, spatialKernel β (a t.castSucc) (a t.succ))
          * spatialKernel β (edgeOf a) (edgeOf b))
        * ∏ t : Fin m, spatialKernel β (b t.castSucc) (b t.succ) := by
  rw [Fin.prod_univ_add]
  congr 1
  · -- the past half, and then the crossing bond
    rw [Fin.prod_univ_castSucc]
    congr 1
    · refine Finset.prod_congr rfl fun i _ => ?_
      have e1 : (Fin.castAdd m (Fin.castSucc i)).castSucc
          = Fin.castAdd (m + 1) (Fin.castSucc i) := by ext; simp
      have e2 : (Fin.castAdd m (Fin.castSucc i)).succ
          = Fin.castAdd (m + 1) (Fin.succ i) := by ext; simp
      rw [e1, e2, joinBond_left, joinBond_left]
    · have e1 : (Fin.castAdd m (Fin.last m)).castSucc
          = Fin.castAdd (m + 1) (Fin.last m) := by ext; simp
      have e2 : (Fin.castAdd m (Fin.last m)).succ
          = Fin.natAdd (m + 1) (0 : Fin (m + 1)) := by ext; simp
      rw [e1, e2, joinBond_left, joinBond_right]
      simp [edgeOf, Fin.rev_zero]
  · -- the future half, read backwards
    have hstep : ∀ i : Fin m,
        spatialKernel β (joinBond a b (Fin.natAdd (m + 1) i).castSucc)
            (joinBond a b (Fin.natAdd (m + 1) i).succ)
          = spatialKernel β (b (Fin.rev i).castSucc) (b (Fin.rev i).succ) := by
      intro i
      have e1 : (Fin.natAdd (m + 1) i).castSucc
          = Fin.natAdd (m + 1) (Fin.castSucc i) := by ext; simp; try omega
      have e2 : (Fin.natAdd (m + 1) i).succ
          = Fin.natAdd (m + 1) (Fin.succ i) := by ext; simp; try omega
      rw [e1, e2, joinBond_right, joinBond_right, rev_castSucc_eq, rev_succ_eq,
        spatialKernel_symm]
    rw [Finset.prod_congr rfl fun i (_ : i ∈ Finset.univ) => hstep i]
    simpa using Equiv.prod_comp (Fin.revPerm (n := m))
      (fun i => spatialKernel β (b i.castSucc) (b i.succ))

/-- **THE WEIGHT IDENTITY.**  With the bijection, this is the whole bond
bridge. -/
theorem gibbsWeight_joinBond {L m : ℕ} (w : (Fin L → Fin 2) → ℝ) (β : ℝ)
    (a b : Fin (m + 1) → (Fin L → Fin 2)) :
    gibbsWeight w β (N := m + 1 + m) (joinBond a b)
      = gibbsWeight w β a * spatialKernel β (edgeOf a) (edgeOf b)
          * gibbsWeight w β b := by
  unfold gibbsWeight
  rw [show (∏ t : Fin (m + 1 + m + 1), w (joinBond a b t))
        = (∏ t : Fin (m + 1), w (a t)) * ∏ t : Fin (m + 1), w (b t)
      from prod_w_joinBond w a b, prod_K_joinBond]
  ring

/-! ### The bond bridge, closed

Assembly is a bijection and the weights multiply, so the sum over pairs of
halves IS the sum over whole paths.  From here the bond form is no longer a
candidate: it is the reflected two-point sum of the Gibbs measure, for a complex
observable of the whole past half-chain, the reflection entering through the
pair `(pastOf, futRevOf)`. -/

/-- **THE BOND BRIDGE.**  The candidate form is the reflected Gibbs sum. -/
theorem osPairingBond_eq_gibbsSum {L m : ℕ} (w : (Fin L → Fin 2) → ℝ) (β : ℝ)
    (F : (Fin (m + 1) → (Fin L → Fin 2)) → ℂ) :
    (∑ X : Fin ((m + 1) + (m + 1)) → (Fin L → Fin 2),
        (starRingEnd ℂ) (F (pastOf X)) * F (futRevOf X)
          * ((gibbsWeight w β (N := m + 1 + m) X : ℝ) : ℂ))
      = osPairingBond w β m F := by
  rw [← Equiv.sum_comp (bondEquiv L m)
        (fun X => (starRingEnd ℂ) (F (pastOf X)) * F (futRevOf X)
          * ((gibbsWeight w β (N := m + 1 + m) X : ℝ) : ℂ))]
  rw [Fintype.sum_prod_type]
  unfold osPairingBond
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  show (starRingEnd ℂ) (F (pastOf (joinBond a b))) * F (futRevOf (joinBond a b))
      * ((gibbsWeight w β (N := m + 1 + m) (joinBond a b) : ℝ) : ℂ) = _
  rw [pastOf_joinBond, futRevOf_joinBond, gibbsWeight_joinBond]

/-- **AND THEREFORE IT IS NON-NEGATIVE, for `β ≥ 0`.**  The reflected two-point
sum of the Gibbs measure itself, not of a form standing in for it. -/
theorem gibbsSum_reflected_nonneg {L m : ℕ} (w : (Fin L → Fin 2) → ℝ) {β : ℝ}
    (hβ : 0 ≤ β) (F : (Fin (m + 1) → (Fin L → Fin 2)) → ℂ) :
    ∃ r : ℝ, 0 ≤ r ∧
      (∑ X : Fin ((m + 1) + (m + 1)) → (Fin L → Fin 2),
        (starRingEnd ℂ) (F (pastOf X)) * F (futRevOf X)
          * ((gibbsWeight w β (N := m + 1 + m) X : ℝ) : ℂ)) = (r : ℂ) := by
  rw [osPairingBond_eq_gibbsSum]
  exact osPairingBond_nonneg w hβ m F

/-- **THE MATRIX FORM, ON THE MEASURE ITSELF.**  The diagonal theorem above
already implies this by applying it to `∑ᵢ cᵢ Fᵢ`, but leaving it implicit would
let the prose say "matrix statement about the measure" while Lean exhibited only
a matrix for the intermediate form and a diagonal identity for the path sum.
The consequence is cheap, which is exactly why it is written down. -/
theorem gibbsSum_reflected_gram_nonneg {L m : ℕ} (w : (Fin L → Fin 2) → ℝ)
    {β : ℝ} (hβ : 0 ≤ β) {ι : Type*} [Fintype ι] (c : ι → ℂ)
    (F : ι → (Fin (m + 1) → (Fin L → Fin 2)) → ℂ) :
    ∃ r : ℝ, 0 ≤ r ∧
      (∑ i, ∑ j, (starRingEnd ℂ) (c i) * c j *
        ∑ X : Fin ((m + 1) + (m + 1)) → (Fin L → Fin 2),
          (starRingEnd ℂ) (F i (pastOf X)) * F j (futRevOf X)
            * ((gibbsWeight w β (N := m + 1 + m) X : ℝ) : ℂ)) = (r : ℂ) := by
  have hcross : ∀ i j : ι,
      (∑ X : Fin ((m + 1) + (m + 1)) → (Fin L → Fin 2),
        (starRingEnd ℂ) (F i (pastOf X)) * F j (futRevOf X)
          * ((gibbsWeight w β (N := m + 1 + m) X : ℝ) : ℂ))
        = osPairingBondCross w β m (F i) (F j) := by
    intro i j
    rw [← Equiv.sum_comp (bondEquiv L m)
          (fun X => (starRingEnd ℂ) (F i (pastOf X)) * F j (futRevOf X)
            * ((gibbsWeight w β (N := m + 1 + m) X : ℝ) : ℂ))]
    rw [Fintype.sum_prod_type]
    unfold osPairingBondCross
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    show (starRingEnd ℂ) (F i (pastOf (joinBond a b))) * F j (futRevOf (joinBond a b))
        * ((gibbsWeight w β (N := m + 1 + m) (joinBond a b) : ℝ) : ℂ) = _
    rw [pastOf_joinBond, futRevOf_joinBond, gibbsWeight_joinBond]
  rw [Finset.sum_congr rfl fun i _ =>
        Finset.sum_congr rfl fun j _ => by rw [hcross i j]]
  exact osPairingBond_gram_nonneg w hβ m c F

end YangMills.OS
