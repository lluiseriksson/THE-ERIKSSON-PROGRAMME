/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson
-/
import Mathlib
import YangMills.OS.SpatialGibbs
import YangMills.OS.PerronKernel
import YangMills.OS.SpatialSpectral

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

/-! ## §3b  The abstract sector interface

The two analytic estimates still missing from the uniformity target live on
different eigenspaces of the flip.  This section makes that reduction an actual
Lean interface before any diagonalisation is attempted.  It is deliberately
independent of the ring kernel except for the two invariance lemmas at the end.
-/

@[simp] theorem flipObs_flip {L : ℕ} (u : (Fin L → Fin 2) → ℝ) :
    flipObs (flipObs u) = u := by
  funext σ
  simp [flipObs]

/-- Membership in the even sector of the global spin flip. -/
def IsFlipEven {L : ℕ} (u : (Fin L → Fin 2) → ℝ) : Prop :=
  flipObs u = u

/-- Membership in the odd sector of the global spin flip. -/
def IsFlipOdd {L : ℕ} (u : (Fin L → Fin 2) → ℝ) : Prop :=
  flipObs u = -u

theorem isFlipEven_iff {L : ℕ} {u : (Fin L → Fin 2) → ℝ} :
    IsFlipEven u ↔ ∀ σ, u (flipCfg σ) = u σ := by
  constructor
  · intro h σ
    simpa [IsFlipEven, flipObs] using congrFun h σ
  · intro h
    unfold IsFlipEven
    funext σ
    exact h σ

theorem isFlipOdd_iff {L : ℕ} {u : (Fin L → Fin 2) → ℝ} :
    IsFlipOdd u ↔ ∀ σ, u (flipCfg σ) = -u σ := by
  constructor
  · intro h σ
    simpa [IsFlipOdd, flipObs] using congrFun h σ
  · intro h
    unfold IsFlipOdd
    funext σ
    simpa using h σ

/-- The projector `u₊ = (u + Ju) / 2` onto the even flip sector. -/
noncomputable def evenPart {L : ℕ} (u : (Fin L → Fin 2) → ℝ) :
    (Fin L → Fin 2) → ℝ :=
  fun σ => (u σ + flipObs u σ) / 2

/-- The projector `u₋ = (u - Ju) / 2` onto the odd flip sector. -/
noncomputable def oddPart {L : ℕ} (u : (Fin L → Fin 2) → ℝ) :
    (Fin L → Fin 2) → ℝ :=
  fun σ => (u σ - flipObs u σ) / 2

/-- Every observable is the sum of its even and odd parts. -/
theorem evenPart_add_oddPart {L : ℕ} (u : (Fin L → Fin 2) → ℝ) :
    (fun σ => evenPart u σ + oddPart u σ) = u := by
  funext σ
  simp only [evenPart, oddPart]
  ring

/-- The even projector lands in the even sector. -/
theorem isFlipEven_evenPart {L : ℕ} (u : (Fin L → Fin 2) → ℝ) :
    IsFlipEven (evenPart u) := by
  unfold IsFlipEven
  funext σ
  simp [evenPart, flipObs]
  ring

/-- The odd projector lands in the odd sector. -/
theorem isFlipOdd_oddPart {L : ℕ} (u : (Fin L → Fin 2) → ℝ) :
    IsFlipOdd (oddPart u) := by
  unfold IsFlipOdd
  funext σ
  simp [oddPart, flipObs]
  ring

/-- The two flip sectors are orthogonal for the Euclidean pairing. -/
theorem flipEven_flipOdd_orthogonal {L : ℕ}
    {u v : (Fin L → Fin 2) → ℝ} (hu : IsFlipEven u) (hv : IsFlipOdd v) :
    ∑ σ, u σ * v σ = 0 := by
  have huflip : ∀ σ, u (flipCfg σ) = u σ := by
    intro σ
    simpa [IsFlipEven, flipObs] using congrFun hu σ
  have hvflip : ∀ σ, v (flipCfg σ) = -v σ := by
    intro σ
    simpa [IsFlipOdd, flipObs] using congrFun hv σ
  have hreindex : ∑ σ, u (flipCfg σ) * v (flipCfg σ) = ∑ σ, u σ * v σ := by
    exact Equiv.sum_comp (flipEquiv L) (fun σ => u σ * v σ)
  have hneg : ∑ σ, u (flipCfg σ) * v (flipCfg σ) = -∑ σ, u σ * v σ := by
    calc
      ∑ σ, u (flipCfg σ) * v (flipCfg σ) = ∑ σ, -(u σ * v σ) := by
        exact Finset.sum_congr rfl fun σ _ => by rw [huflip, hvflip]; ring
      _ = -∑ σ, u σ * v σ := by rw [Finset.sum_neg_distrib]
  linarith

/-- In particular, the canonical even and odd parts are orthogonal. -/
theorem evenPart_oddPart_orthogonal {L : ℕ} (u : (Fin L → Fin 2) → ℝ) :
    ∑ σ, evenPart u σ * oddPart u σ = 0 :=
  flipEven_flipOdd_orthogonal (isFlipEven_evenPart u) (isFlipOdd_oddPart u)

/-- Pythagoras for two observables whose Euclidean pairing vanishes. -/
theorem eucNorm_add_sq_of_orthogonal {L : ℕ}
    {u v : (Fin L → Fin 2) → ℝ} (horth : ∑ σ, u σ * v σ = 0) :
    eucNorm (fun σ => u σ + v σ) * eucNorm (fun σ => u σ + v σ)
      = eucNorm u * eucNorm u + eucNorm v * eucNorm v := by
  rw [eucNorm_mul_self, eucNorm_mul_self, eucNorm_mul_self]
  calc
    ∑ σ, (u σ + v σ) * (u σ + v σ)
        = ∑ σ, (u σ * u σ + (2 * (u σ * v σ) + v σ * v σ)) := by
          exact Finset.sum_congr rfl fun σ _ => by ring
    _ = (∑ σ, u σ * u σ) + (2 * ∑ σ, u σ * v σ) + ∑ σ, v σ * v σ := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum]
    _ = (∑ σ, u σ * u σ) + ∑ σ, v σ * v σ := by rw [horth]; ring

/-- The sector decomposition is orthogonal, hence norm-square preserving. -/
theorem evenPart_oddPart_norm_sq {L : ℕ} (u : (Fin L → Fin 2) → ℝ) :
    eucNorm u * eucNorm u
      = eucNorm (evenPart u) * eucNorm (evenPart u)
        + eucNorm (oddPart u) * eucNorm (oddPart u) := by
  rw [← evenPart_add_oddPart u]
  exact eucNorm_add_sq_of_orthogonal (evenPart_oddPart_orthogonal u)

/-- A flip-invariant kernel preserves the even sector. -/
theorem act_preserves_flipEven {L : ℕ}
    {K : (Fin L → Fin 2) → (Fin L → Fin 2) → ℝ}
    (hK : ∀ σ τ, K (flipCfg σ) (flipCfg τ) = K σ τ)
    {u : (Fin L → Fin 2) → ℝ} (hu : IsFlipEven u) :
    IsFlipEven (act K u) := by
  unfold IsFlipEven at hu ⊢
  rw [← act_flip_comm hK u, hu]

/-- A flip-invariant kernel preserves the odd sector. -/
theorem act_preserves_flipOdd {L : ℕ}
    {K : (Fin L → Fin 2) → (Fin L → Fin 2) → ℝ}
    (hK : ∀ σ τ, K (flipCfg σ) (flipCfg τ) = K σ τ)
    {u : (Fin L → Fin 2) → ℝ} (hu : IsFlipOdd u) :
    IsFlipOdd (act K u) := by
  unfold IsFlipOdd at hu ⊢
  calc
    flipObs (act K u) = act K (flipObs u) := (act_flip_comm hK u).symm
    _ = act K (-u) := by rw [hu]
    _ = -act K u := by
      simpa using act_smul K (-1 : ℝ) u

/-- Because an even vacuum is orthogonal to the whole odd sector, every odd
observable is automatically a fluctuation observable. -/
theorem flipOdd_perp_of_flipEven {L : ℕ}
    {Ω u : (Fin L → Fin 2) → ℝ} (hΩ : IsFlipEven Ω) (hu : IsFlipOdd u) :
    ∑ σ, Ω σ * u σ = 0 :=
  flipEven_flipOdd_orthogonal hΩ hu

/-- If `u` is orthogonal to an even vacuum, then its even projection is still
orthogonal to that vacuum. -/
theorem evenPart_perp_of_perp {L : ℕ}
    {Ω u : (Fin L → Fin 2) → ℝ} (hΩ : IsFlipEven Ω)
    (hperp : ∑ σ, Ω σ * u σ = 0) :
    ∑ σ, Ω σ * evenPart u σ = 0 := by
  have hodd : ∑ σ, Ω σ * oddPart u σ = 0 :=
    flipOdd_perp_of_flipEven hΩ (isFlipOdd_oddPart u)
  have hsplit : ∑ σ, Ω σ * u σ
      = (∑ σ, Ω σ * evenPart u σ) + ∑ σ, Ω σ * oddPart u σ := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun σ _ => by
      have hs := congrFun (evenPart_add_oddPart u) σ
      rw [← hs]
      ring
  linarith

/-- The abstract recombination lemma.  If the two invariant flip sectors obey
the same norm bound, then their orthogonal sum obeys it too.  For the even
sector only the part orthogonal to the even vacuum is required. -/
theorem norm_act_le_of_flip_sector_bounds {L : ℕ}
    {K : (Fin L → Fin 2) → (Fin L → Fin 2) → ℝ}
    (hK : ∀ σ τ, K (flipCfg σ) (flipCfg τ) = K σ τ)
    {Ω : (Fin L → Fin 2) → ℝ} (hΩ : IsFlipEven Ω) {r : ℝ} (hr : 0 ≤ r)
    (hodd : ∀ u, IsFlipOdd u → eucNorm (act K u) ≤ r * eucNorm u)
    (heven : ∀ u, IsFlipEven u → (∑ σ, Ω σ * u σ = 0) →
      eucNorm (act K u) ≤ r * eucNorm u)
    {u : (Fin L → Fin 2) → ℝ} (hperp : ∑ σ, Ω σ * u σ = 0) :
    eucNorm (act K u) ≤ r * eucNorm u := by
  have hpEven : IsFlipEven (evenPart u) := isFlipEven_evenPart u
  have hmOdd : IsFlipOdd (oddPart u) := isFlipOdd_oddPart u
  have hpPerp : ∑ σ, Ω σ * evenPart u σ = 0 := evenPart_perp_of_perp hΩ hperp
  have hpBound := heven (evenPart u) hpEven hpPerp
  have hmBound := hodd (oddPart u) hmOdd
  have hpActEven : IsFlipEven (act K (evenPart u)) := act_preserves_flipEven hK hpEven
  have hmActOdd : IsFlipOdd (act K (oddPart u)) := act_preserves_flipOdd hK hmOdd
  have hactOrth : ∑ σ, act K (evenPart u) σ * act K (oddPart u) σ = 0 :=
    flipEven_flipOdd_orthogonal hpActEven hmActOdd
  have hactSplit : act K u = fun σ => act K (evenPart u) σ + act K (oddPart u) σ := by
    rw [← evenPart_add_oddPart u, act_add]
  have hactSq : eucNorm (act K u) * eucNorm (act K u)
      = eucNorm (act K (evenPart u)) * eucNorm (act K (evenPart u))
        + eucNorm (act K (oddPart u)) * eucNorm (act K (oddPart u)) := by
    rw [hactSplit]
    exact eucNorm_add_sq_of_orthogonal hactOrth
  have huSq := evenPart_oddPart_norm_sq u
  have hpSq : eucNorm (act K (evenPart u)) * eucNorm (act K (evenPart u))
      ≤ (r * eucNorm (evenPart u)) * (r * eucNorm (evenPart u)) := by
    nlinarith [eucNorm_nonneg (act K (evenPart u)), eucNorm_nonneg (evenPart u),
      mul_nonneg hr (eucNorm_nonneg (evenPart u))]
  have hmSq : eucNorm (act K (oddPart u)) * eucNorm (act K (oddPart u))
      ≤ (r * eucNorm (oddPart u)) * (r * eucNorm (oddPart u)) := by
    nlinarith [eucNorm_nonneg (act K (oddPart u)), eucNorm_nonneg (oddPart u),
      mul_nonneg hr (eucNorm_nonneg (oddPart u))]
  have hsq : eucNorm (act K u) * eucNorm (act K u)
      ≤ (r * eucNorm u) * (r * eucNorm u) := by
    nlinarith
  nlinarith [eucNorm_nonneg (act K u), eucNorm_nonneg u,
    mul_nonneg hr (eucNorm_nonneg u)]

/-- The ring-weighted transfer operator preserves the even flip sector. -/
theorem act_ring_preserves_flipEven {L : ℕ} (γ β : ℝ)
    {u : (Fin (L + 1) → Fin 2) → ℝ} (hu : IsFlipEven u) :
    IsFlipEven (act (symWeighted (spatialWeightRing γ) β) u) :=
  act_preserves_flipEven
    (fun σ τ => symWeighted_flip (spatialWeightRing_flip γ) β σ τ) hu

/-- The ring-weighted transfer operator preserves the odd flip sector. -/
theorem act_ring_preserves_flipOdd {L : ℕ} (γ β : ℝ)
    {u : (Fin (L + 1) → Fin 2) → ℝ} (hu : IsFlipOdd u) :
    IsFlipOdd (act (symWeighted (spatialWeightRing γ) β) u) :=
  act_preserves_flipOdd
    (fun σ τ => symWeighted_flip (spatialWeightRing_flip γ) β σ τ) hu

/-! ## §3c  The two remaining analytic obligations, typed

Both propositions include `β ≥ 0` and `γ ≥ 0` as data because the measured
negative-coupling counterexamples show that neither sign assumption is cosmetic.
They are obligations, not results proved in this file.
-/

/-- **ODD-BLOCK OBLIGATION.**  Under `β ≥ 0` and `γ ≥ 0`, the odd flip sector
contracts at the candidate rate `tanh β · exp(2γ)` relative to the Perron scale. -/
def SpatialRingOddSectorBound (β γ : ℝ) (L : ℕ) (lam : ℝ) : Prop :=
  0 ≤ β ∧ 0 ≤ γ ∧
    ∀ u : (Fin (L + 1) → Fin 2) → ℝ, IsFlipOdd u →
      eucNorm (act (symWeighted (spatialWeightRing γ) β) u)
        ≤ (Real.tanh β * Real.exp (2 * γ) * lam) * eucNorm u

/-- **EVEN NON-PERRON OBLIGATION.**  Under `β ≥ 0` and `γ ≥ 0`, the part of
the even flip sector orthogonal to the Perron vector contracts at the same
candidate rate. -/
def SpatialRingEvenFluctuationBound (β γ : ℝ) (L : ℕ)
    (Ω : (Fin (L + 1) → Fin 2) → ℝ) (lam : ℝ) : Prop :=
  0 ≤ β ∧ 0 ≤ γ ∧
    ∀ u : (Fin (L + 1) → Fin 2) → ℝ, IsFlipEven u →
      (∑ σ, Ω σ * u σ = 0) →
      eucNorm (act (symWeighted (spatialWeightRing γ) β) u)
        ≤ (Real.tanh β * Real.exp (2 * γ) * lam) * eucNorm u

/-- **SECTOR REDUCTION OF THE UNIFORM RING TARGET.**  For `β ≥ 0` and
`γ ≥ 0`, the two explicit sector obligations above imply exactly
`specRatio ≤ tanh β · exp(2γ)`.  No analytic sector estimate is hidden here. -/
theorem spatialRing_specRatio_le_of_sector_bounds (β γ : ℝ)
    (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (L : ℕ)
    {Ω : (Fin (L + 1) → Fin 2) → ℝ} {lam : ℝ} (hΩpos : ∀ σ, 0 < Ω σ)
    (hΩeig : ∀ σ, ∑ τ, symWeighted (spatialWeightRing γ) β σ τ * Ω τ = lam * Ω σ)
    (hΩeven : IsFlipEven Ω)
    (hodd : SpatialRingOddSectorBound β γ L lam)
    (heven : SpatialRingEvenFluctuationBound β γ L Ω lam) :
    specRatio (symWeighted_symm (spatialWeightRing γ) β) lam
      ≤ Real.tanh β * Real.exp (2 * γ) := by
  let S := symWeighted (spatialWeightRing γ) β
  have hSpos : ∀ σ τ, 0 < S σ τ := symWeighted_pos (spatialWeightRing_pos γ) β
  have hSflip : ∀ σ τ, S (flipCfg σ) (flipCfg τ) = S σ τ :=
    fun σ τ => symWeighted_flip (spatialWeightRing_flip γ) β σ τ
  have hlam : 0 < lam := eigenvalue_pos hSpos hΩpos hΩeig
  have hq : 0 ≤ Real.tanh β * Real.exp (2 * γ) :=
    mul_nonneg (tanh_nonneg hβ) (Real.exp_pos _).le
  have hfull : ∀ u : (Fin (L + 1) → Fin 2) → ℝ, (∑ σ, Ω σ * u σ = 0) →
      eucNorm (act S u) ≤
        (Real.tanh β * Real.exp (2 * γ) * lam) * eucNorm u := by
    intro u hu
    exact norm_act_le_of_flip_sector_bounds hSflip hΩeven
      (mul_nonneg hq hlam.le) hodd.2.2 heven.2.2 hu
  have hne : ((fun _ => (0 : Fin 2)) : Fin (L + 1) → Fin 2)
      ≠ ((fun _ => (1 : Fin 2)) : Fin (L + 1) → Fin 2) := by
    intro h
    have hc := congrFun h (0 : Fin (L + 1))
    exact absurd hc (by decide)
  obtain ⟨⟨u, hu, hune, hval⟩, -⟩ :=
    specGap_isGreatest hSpos (symWeighted_symm (spatialWeightRing γ) β)
      hΩpos hΩeig hne
  have hunorm : 0 < eucNorm u :=
    lt_of_le_of_ne (eucNorm_nonneg u) (Ne.symm hune)
  have hgap : specGap (symWeighted_symm (spatialWeightRing γ) β) lam
      ≤ (Real.tanh β * Real.exp (2 * γ)) * lam := by
    rw [hval, div_le_iff₀ hunorm]
    simpa [S, mul_assoc] using hfull u hu
  unfold specRatio
  rw [div_le_iff₀ hlam]
  exact hgap

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

/-! ## §5  Transport to the symmetrised kernel

`specRatio` is defined for the SYMMETRISED kernel `S = √w · K · √w`, while
`perron_even` above is about the source-weighted one `A = w · K`.  The two are
similar and the transport is three lines --- but until it is written the parity
result is about a neighbouring operator, not about the one the target names. -/

/-- Dividing an eigenvector of the source-weighted kernel by `√w` gives an
eigenvector of the symmetrised one, with the same eigenvalue. -/
theorem symWeighted_eigen_of_sourceWeighted {L : ℕ} {w : (Fin L → Fin 2) → ℝ}
    (hw : ∀ σ, 0 < w σ) (β lam : ℝ) {v : (Fin L → Fin 2) → ℝ}
    (hv : ∀ σ, ∑ τ, sourceWeightedKernelL w β σ τ * v τ = lam * v σ)
    (σ : Fin L → Fin 2) :
    ∑ τ, symWeighted w β σ τ * (v τ / Real.sqrt (w τ))
      = lam * (v σ / Real.sqrt (w σ)) := by
  have hs : ∀ τ, Real.sqrt (w τ) ≠ 0 := fun τ =>
    ne_of_gt (Real.sqrt_pos.mpr (hw τ))
  have hsq : ∀ τ, Real.sqrt (w τ) * Real.sqrt (w τ) = w τ := fun τ =>
    Real.mul_self_sqrt (hw τ).le
  have hstep : ∀ τ, symWeighted w β σ τ * (v τ / Real.sqrt (w τ))
      = (sourceWeightedKernelL w β σ τ * v τ) / Real.sqrt (w σ) := by
    intro τ
    unfold symWeighted sourceWeightedKernelL
    have h1 : Real.sqrt (w σ) * spatialKernel β σ τ * Real.sqrt (w τ)
          * (v τ / Real.sqrt (w τ))
        = Real.sqrt (w σ) * spatialKernel β σ τ * v τ := by
      field_simp [hs τ]
    have h2 : w σ * spatialKernel β σ τ * v τ / Real.sqrt (w σ)
        = Real.sqrt (w σ) * spatialKernel β σ τ * v τ := by
      rw [div_eq_iff (hs σ)]
      linear_combination (spatialKernel β σ τ * v τ) * (hsq σ).symm
    rw [h1, h2]
  rw [Finset.sum_congr rfl fun τ _ => hstep τ, ← Finset.sum_div, hv σ]
  field_simp

/-- **THE PARITY, ON THE OPERATOR THE TARGET IS ABOUT.**  The symmetrised
ring-weighted kernel has a strictly positive eigenvector which is EVEN under the
global spin flip.  This is `perron_even` transported across the similarity, so
that the sector decomposition applies to the operator `specRatio` is defined
from and not merely to a neighbouring one. -/
theorem symWeighted_perron_even (β γ : ℝ) (L : ℕ) :
    ∃ (Ω : (Fin (L + 1) → Fin 2) → ℝ) (lam : ℝ), (∀ σ, 0 < Ω σ) ∧ 0 < lam ∧
      (∀ σ, ∑ τ : Fin (L + 1) → Fin 2,
        symWeighted (spatialWeightRing γ) β σ τ * Ω τ = lam * Ω σ) ∧
      ∀ σ, Ω (flipCfg σ) = Ω σ := by
  obtain ⟨v, lam, hpos, -, hlam, heig, hflip⟩ := perron_even β γ L
  refine ⟨fun σ => v σ / Real.sqrt (spatialWeightRing γ σ), lam, fun σ => ?_,
    hlam, fun σ => ?_, fun σ => ?_⟩
  · exact div_pos (hpos σ) (Real.sqrt_pos.mpr (spatialWeightRing_pos γ σ))
  · exact symWeighted_eigen_of_sourceWeighted (spatialWeightRing_pos γ) β lam heig σ
  · show v (flipCfg σ) / Real.sqrt (spatialWeightRing γ (flipCfg σ))
      = v σ / Real.sqrt (spatialWeightRing γ σ)
    rw [hflip σ, spatialWeightRing_flip γ σ]

end YangMills.OS
