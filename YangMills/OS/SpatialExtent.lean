/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson

O-3f: spatial extent.  The algebraic half of the reconstruction ports; the
elementary route to the vacuum does not.

Charter: docs/O-BRIDGE-CHARTER.md, AMENDMENT 10 (five pre-registered judges,
the fifth of which exists to prevent the positive half being oversold).
-/

import Mathlib
import YangMills.OS.Z2Quotient

/-!
# O-3f — spatial extent, and where the construction stops

## The point of this module

Time slices now carry `L` spins, so the state space is `Fin L → Fin 2` and the
transfer operator acts on a space of dimension `2 ^ L` — it grows with the
volume.  Two systems are treated.

**DECOUPLED** (`spatialKernel`): time bonds only, no interaction between spatial
sites.  Here everything ports.  Row sums are constant, so the uniform vacuum
survives; and the single-site sign observable is an eigenvector whose eigenvalue
is exactly `tanh β`, with `L` free.

**COUPLED** (`coupledKernel`): the same, multiplied by a spatial weight linking
neighbouring sites inside a slice.  Here the construction stops at its first
step.  The spatial weight depends only on the source configuration, so it
factors out of the sum over the target and the row sum becomes
configuration-dependent.  Constant row sums fail, and with them the property
`T Ω = Ω`, which in the one-dimensional chain was a free consequence of
normalisation.

## The honest reading, fixed in the charter before this file existed

The decoupled system is `L` non-interacting copies of a two-state system.  Its
volume-independent rate is what a tensor power always gives and is
**physically empty**; it is recorded because it isolates exactly which half of
the construction survives, not because a volume-independent rate for an
interacting system was obtained.  It was not.  **No gap for the coupled system
is proved here, and none is claimed.**  Once the vacuum is an unidentified
Perron vector, every later step of the chain has lost its starting point.

Nothing here concerns `SU(N)`, the continuum limit, or the Clay problem.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills.OS

set_option linter.unusedSectionVars false

/-! ## §0  Two small facts about a two-element site -/

theorem fin_two_cases (s : Fin 2) : s = 0 ∨ s = 1 := by
  revert s
  decide

/-- The row sum of the bond weight is the normalisation, whatever the source. -/
theorem sum_bond_row (β : ℝ) (s : Fin 2) : ∑ t, z2Bond β s t = z2Norm β := by
  rw [Fin.sum_univ_two]
  rcases fin_two_cases s with hs | hs
  · rw [hs, z2Bond_same, z2Bond_ne (by decide : (0:Fin 2) ≠ 1)]
    unfold z2Norm; ring
  · rw [hs, z2Bond_ne (by decide : (1:Fin 2) ≠ 0), z2Bond_same]
    unfold z2Norm; ring

/-! ## §1  Summing a product over all configurations -/

/-- The sum over configurations of a product over sites factorises.  This one
lemma carries both halves of the module. -/
theorem sum_prod_config {L : ℕ} (f : Fin L → Fin 2 → ℝ) :
    ∑ τ : Fin L → Fin 2, ∏ j, f j (τ j) = ∏ j, ∑ t, f j t := by
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]

/-! ## §2  The decoupled system: everything ports -/

/-- The decoupled transfer kernel: time bonds only. -/
noncomputable def spatialKernel (β : ℝ) {L : ℕ} (σ τ : Fin L → Fin 2) : ℝ :=
  ∏ j, z2Bond β (σ j) (τ j)

theorem spatialKernel_pos (β : ℝ) {L : ℕ} (σ τ : Fin L → Fin 2) :
    0 < spatialKernel β σ τ := by
  unfold spatialKernel
  exact Finset.prod_pos fun j _ => z2Bond_pos β _ _

theorem spatialKernel_symm (β : ℝ) {L : ℕ} (σ τ : Fin L → Fin 2) :
    spatialKernel β σ τ = spatialKernel β τ σ := by
  unfold spatialKernel
  exact Finset.prod_congr rfl fun j _ => z2Bond_symm β _ _

/-- **Row sums are constant** — independent of the configuration.  This is what
carries the uniform vacuum to arbitrary spatial extent. -/
theorem sum_spatialKernel (β : ℝ) {L : ℕ} (σ : Fin L → Fin 2) :
    ∑ τ : Fin L → Fin 2, spatialKernel β σ τ = (z2Norm β) ^ L := by
  unfold spatialKernel
  rw [sum_prod_config (fun j t => z2Bond β (σ j) t)]
  rw [show (∏ j : Fin L, ∑ t, z2Bond β (σ j) t) = ∏ _j : Fin L, z2Norm β from
      Finset.prod_congr rfl fun j _ => sum_bond_row β (σ j),
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-! ## §3  The volume-independent mode -/

/-- The sign of a single site, as a real observable. -/
noncomputable def siteSign {L : ℕ} (i : Fin L) (σ : Fin L → Fin 2) : ℝ :=
  z2Sign (σ i) 0

theorem sum_bond_sign (β : ℝ) (s : Fin 2) :
    ∑ t, z2Bond β s t * z2Sign t 0 = (Real.exp β - Real.exp (-β)) * z2Sign s 0 := by
  rw [Fin.sum_univ_two]
  rcases fin_two_cases s with hs | hs
  · rw [hs, z2Bond_same, z2Bond_ne (by decide : (0:Fin 2) ≠ 1)]
    unfold z2Sign
    norm_num
    ring
  · rw [hs, z2Bond_ne (by decide : (1:Fin 2) ≠ 0), z2Bond_same]
    unfold z2Sign
    norm_num
    ring

/-- **The single-site sign observable is an eigenvector, and its eigenvalue does
not depend on `L`.**  After dividing by the row sum `Z^L` the eigenvalue is
`(e^β − e^{-β})/Z = tanh β`, the same number as in the one-dimensional chain. -/
theorem spatialKernel_siteSign (β : ℝ) {L : ℕ} (i : Fin L) (σ : Fin L → Fin 2) :
    ∑ τ : Fin L → Fin 2, spatialKernel β σ τ * siteSign i τ
      = (Real.exp β - Real.exp (-β)) * (z2Norm β) ^ (L - 1) * siteSign i σ := by
  unfold spatialKernel siteSign
  have hrw : ∀ τ : Fin L → Fin 2,
      (∏ j, z2Bond β (σ j) (τ j)) * z2Sign (τ i) 0
        = ∏ j, (z2Bond β (σ j) (τ j) * (if j = i then z2Sign (τ j) 0 else 1)) := by
    intro τ
    rw [Finset.prod_mul_distrib]
    simp
  rw [Finset.sum_congr rfl fun τ _ => hrw τ,
    sum_prod_config (fun j t => z2Bond β (σ j) t * (if j = i then z2Sign t 0 else 1))]
  have hi : ∑ t, (z2Bond β (σ i) t * (if i = i then z2Sign t 0 else 1))
      = (Real.exp β - Real.exp (-β)) * z2Sign (σ i) 0 := by
    have he : ∀ t : Fin 2, z2Bond β (σ i) t * (if i = i then z2Sign t 0 else 1)
        = z2Bond β (σ i) t * z2Sign t 0 := by
      intro t; rw [if_pos rfl]
    rw [Finset.sum_congr rfl fun t _ => he t]
    exact sum_bond_sign β (σ i)
  have hne : ∀ j : Fin L, j ≠ i →
      ∑ t, (z2Bond β (σ j) t * (if j = i then z2Sign t 0 else 1)) = z2Norm β := by
    intro j hj
    simp only [if_neg hj, mul_one]
    exact sum_bond_row β (σ j)
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), hi,
    Finset.prod_congr rfl (fun j hj => hne j (Finset.ne_of_mem_erase hj)),
    Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ i),
    Finset.card_univ, Fintype.card_fin]
  ring

/-- The normalised eigenvalue is `tanh β`, with `L` a free variable. -/
theorem spatial_rate_eq_tanh (β : ℝ) :
    (Real.exp β - Real.exp (-β)) / z2Norm β = Real.tanh β := by
  rw [← z2A_sub_z2B_eq_tanh]
  unfold z2A z2B
  rw [div_sub_div_same]

/-! ## §4  THE OBSTRUCTION — the coupled system -/

/-- The spatial weight of a two-site slice: one bond inside the slice.  The
general definition is a product over spatial bonds; the obstruction below needs
only one bond, and keeping it explicit keeps the witness computable. -/
noncomputable def spatialWeight (γ : ℝ) (σ : Fin 2 → Fin 2) : ℝ :=
  z2Bond γ (σ 0) (σ 1)

/-- The coupled kernel.  The spatial weight depends only on the source, which is
exactly why it factors out of the row sum and breaks its constancy. -/
noncomputable def coupledKernel (β γ : ℝ) (σ τ : Fin 2 → Fin 2) : ℝ :=
  spatialWeight γ σ * spatialKernel β σ τ

/-- **The row sum is configuration-dependent.**  The spatial weight factors out
of the sum over the target, and what remains is a constant. -/
theorem sum_coupledKernel (β γ : ℝ) (σ : Fin 2 → Fin 2) :
    ∑ τ : Fin 2 → Fin 2, coupledKernel β γ σ τ
      = spatialWeight γ σ * (z2Norm β) ^ 2 := by
  unfold coupledKernel
  rw [← Finset.mul_sum, sum_spatialKernel]

/-- Two explicit configurations of a two-site slice. -/
noncomputable def cfgFlat : Fin 2 → Fin 2 := fun _ => 0

noncomputable def cfgAlt : Fin 2 → Fin 2
  | 0 => 0
  | 1 => 1

theorem spatialWeight_cfgFlat (γ : ℝ) :
    spatialWeight γ cfgFlat = Real.exp γ := by
  unfold spatialWeight cfgFlat
  exact z2Bond_same γ 0

theorem spatialWeight_cfgAlt (γ : ℝ) :
    spatialWeight γ cfgAlt = Real.exp (-γ) := by
  unfold spatialWeight
  rw [show cfgAlt 0 = 0 from rfl, show cfgAlt 1 = 1 from rfl]
  exact z2Bond_ne (by decide : (0:Fin 2) ≠ 1) γ

/-- **THE OBSTRUCTION.**  At nonzero spatial coupling the row sums of the
coupled kernel are not constant.  Two explicit configurations of a two-site
slice have different row sums. -/
theorem coupled_rowSums_not_constant {β γ : ℝ} (hγ : 0 < γ) :
    ∑ τ : Fin 2 → Fin 2, coupledKernel β γ cfgFlat τ
      ≠ ∑ τ : Fin 2 → Fin 2, coupledKernel β γ cfgAlt τ := by
  rw [sum_coupledKernel, sum_coupledKernel, spatialWeight_cfgFlat,
    spatialWeight_cfgAlt]
  have hz : (0:ℝ) < (z2Norm β) ^ 2 := by
    have := z2Norm_pos β; positivity
  have hlt : Real.exp (-γ) < Real.exp γ := Real.exp_lt_exp.mpr (by linarith)
  intro h
  nlinarith [hz, hlt]

/-- **Consequence: the uniform vector is not fixed.**  There is no constant `c`
with `∑ τ, K σ τ = c` for every `σ`, so the property `T Ω = Ω` — free in the
one-dimensional chain, where it followed from `a + b = 1` — fails as soon as the
spatial coupling is switched on.  Every later step of the chain of O-3c and
O-3d takes that property as its starting point. -/
theorem coupled_no_constant_rowSum {β γ : ℝ} (hγ : 0 < γ) :
    ¬ ∃ c : ℝ, ∀ σ : Fin 2 → Fin 2,
        ∑ τ : Fin 2 → Fin 2, coupledKernel β γ σ τ = c := by
  rintro ⟨c, hc⟩
  exact coupled_rowSums_not_constant (β := β) hγ ((hc cfgFlat).trans (hc cfgAlt).symm)

/-- By contrast, the decoupled system does have a constant row sum at every
spatial extent — the statement that fails above. -/
theorem decoupled_constant_rowSum (β : ℝ) (L : ℕ) :
    ∃ c : ℝ, ∀ σ : Fin L → Fin 2,
        ∑ τ : Fin L → Fin 2, spatialKernel β σ τ = c :=
  ⟨(z2Norm β) ^ L, fun σ => sum_spatialKernel β σ⟩

end YangMills.OS
