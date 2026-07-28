/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson

O-3h: the vacuum that row-sum normalisation stopped supplying, written down.

O-3f proved that at spatial extent with a coupling the uniform vector is no
longer fixed, so the vacuum becomes a Perron vector the elementary normalisation
does not hand us.  This module hands it over at the smallest interacting size,
in closed form, with positivity proved -- and exhibits a second exact eigenpair,
so the subdominant ratio at that size is explicit.

Charter: docs/O-BRIDGE-CHARTER.md.
-/

import Mathlib
import YangMills.OS.SpatialExtent

/-!
# O-3h — the coupled vacuum at `L = 2`, in closed form

## Method: the character basis

Functions on a two-site slice are spanned by the four characters `1`, `s₀`,
`s₁`, `s₀s₁`, where `sᵢ σ = z2Sign (σ i) 0`.  Two facts make the computation
elementary:

* the spatial weight of O-3f is **affine in the top character**,
  `spatialWeight γ σ = cosh γ + sinh γ · (s₀s₁)(σ)` (`spatialWeight_eq`),
  because `z2Sign i j = z2Sign i 0 · z2Sign j 0` and the exponent takes only the
  values `±γ`;
* the decoupled kernel is **diagonal in this basis**: `sum_spatialKernel` and
  `spatialKernel_siteSign` of O-3f give the constant and the single-site
  characters, and `spatialKernel_allSign` below adds the top one.

Multiplying by the weight therefore mixes only `1` with `s₀s₁` (the *even*
sector) and `s₀` with `s₁` (the *odd* sector), and each `2 × 2` block is solved
in closed form.  The identity `A − B = 4` (`evenA_sub_evenB`) drives every
estimate.

## What is proved

* `coupled_perron_eigen` — an explicit eigenvector with eigenvalue `evenTop β γ`;
* `perronVec_pos` — that eigenvector is **strictly positive** at every
  configuration, for `β > 0` and `γ > 0`.  Perron--Frobenius would call it the
  vacuum; that identification is classical and is not formalised here;
* `coupled_odd_eigen` — a second exact eigenpair, with eigenvalue
  `(e^β − e^{-β}) · (e^β + e^{-β}) · e^{γ}` and a nonvanishing eigenvector.

## What is NOT claimed

That these exhaust the spectrum (completeness is not formalised); that anything
holds for `L > 2`; that any of it bears on a volume-uniform statement.  O-3g
proves the elementary uniform route is blind to `γ`, and the general-`L`
behaviour is *measured and unproved* in `docs/O-LANE-CONTINUATION-20260728.md`.

Nothing here concerns `SU(N)`, the continuum limit, or the Clay problem.

Oracle target: `[propext, Classical.choice, Quot.sound]`.  No sorry, no axioms.
-/

namespace YangMills.OS

set_option linter.unusedSectionVars false

/-! ## §0  Self-contained hyperbolic facts -/

theorem exp_mul_exp_neg (x : ℝ) : Real.exp x * Real.exp (-x) = 1 := by
  rw [← Real.exp_add]
  simp

theorem cosh_sq_sub_sinh_sq' (γ : ℝ) :
    Real.cosh γ * Real.cosh γ - Real.sinh γ * Real.sinh γ = 1 := by
  rw [Real.cosh_eq, Real.sinh_eq]
  nlinarith [exp_mul_exp_neg γ]

theorem one_le_cosh' (γ : ℝ) : 1 ≤ Real.cosh γ := by
  rw [Real.cosh_eq]
  have h := exp_mul_exp_neg γ
  have h1 : 0 < Real.exp γ := Real.exp_pos _
  have h2 : 0 < Real.exp (-γ) := Real.exp_pos _
  nlinarith [sq_nonneg (Real.exp γ - Real.exp (-γ)), h, h1, h2]

theorem sinh_pos' {γ : ℝ} (hγ : 0 < γ) : 0 < Real.sinh γ := by
  rw [Real.sinh_eq]
  have : Real.exp (-γ) < Real.exp γ := Real.exp_lt_exp.mpr (by linarith)
  linarith

theorem exp_eq_cosh_add_sinh (γ : ℝ) :
    Real.exp γ = Real.cosh γ + Real.sinh γ := by
  rw [Real.cosh_eq, Real.sinh_eq]; ring

theorem exp_neg_eq_cosh_sub_sinh (γ : ℝ) :
    Real.exp (-γ) = Real.cosh γ - Real.sinh γ := by
  rw [Real.cosh_eq, Real.sinh_eq]; ring

/-! ## §1  The top character -/

/-- The product of all site signs. -/
noncomputable def allSign {L : ℕ} (σ : Fin L → Fin 2) : ℝ := ∏ j, z2Sign (σ j) 0

theorem z2Sign_sq (i j : Fin 2) : z2Sign i j * z2Sign i j = 1 := by
  unfold z2Sign
  by_cases h : i = j
  · rw [if_pos h]; norm_num
  · rw [if_neg h]; norm_num

/-- The sign function factorises through the origin.  This is what makes the
spatial weight affine in the top character. -/
theorem z2Sign_mul (i j : Fin 2) : z2Sign i j = z2Sign i 0 * z2Sign j 0 := by
  fin_cases i <;> fin_cases j <;> simp [z2Sign]

theorem allSign_sq {L : ℕ} (σ : Fin L → Fin 2) : allSign σ * allSign σ = 1 := by
  unfold allSign
  rw [← Finset.prod_mul_distrib,
    Finset.prod_congr rfl fun j _ => z2Sign_sq (σ j) 0]
  simp

theorem allSign_eq_one_or {L : ℕ} (σ : Fin L → Fin 2) :
    allSign σ = 1 ∨ allSign σ = -1 := by
  have h := allSign_sq σ
  have hfac : (allSign σ - 1) * (allSign σ + 1) = 0 := by nlinarith [h]
  rcases mul_eq_zero.mp hfac with h1 | h1
  · left; linarith
  · right; linarith

/-- **The top character is an eigenvector of the decoupled kernel.**  Companion
to `sum_spatialKernel` (constant character) and `spatialKernel_siteSign`
(single-site characters) of O-3f. -/
theorem spatialKernel_allSign (β : ℝ) {L : ℕ} (σ : Fin L → Fin 2) :
    ∑ τ : Fin L → Fin 2, spatialKernel β σ τ * allSign τ
      = (Real.exp β - Real.exp (-β)) ^ L * allSign σ := by
  unfold spatialKernel allSign
  have hrw : ∀ τ : Fin L → Fin 2,
      (∏ j, z2Bond β (σ j) (τ j)) * ∏ j, z2Sign (τ j) 0
        = ∏ j, (z2Bond β (σ j) (τ j) * z2Sign (τ j) 0) :=
    fun _ => (Finset.prod_mul_distrib).symm
  rw [Finset.sum_congr rfl fun τ _ => hrw τ,
    sum_prod_config (fun j t => z2Bond β (σ j) t * z2Sign t 0),
    Finset.prod_congr rfl fun j _ => sum_bond_sign β (σ j),
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

/-! ## §2  The spatial weight is affine in the top character -/

theorem allSign_two (σ : Fin 2 → Fin 2) :
    allSign σ = z2Sign (σ 0) 0 * z2Sign (σ 1) 0 := by
  unfold allSign
  rw [Fin.prod_univ_two]

theorem spatialWeight_eq (γ : ℝ) (σ : Fin 2 → Fin 2) :
    spatialWeight γ σ = Real.cosh γ + Real.sinh γ * allSign σ := by
  have hm : z2Sign (σ 0) (σ 1) = allSign σ := by
    rw [z2Sign_mul, allSign_two]
  unfold spatialWeight z2Bond
  rw [hm]
  rcases allSign_eq_one_or σ with h | h <;> rw [h]
  · rw [mul_one, exp_eq_cosh_add_sinh]; ring
  · rw [show γ * (-1 : ℝ) = -γ by ring, exp_neg_eq_cosh_sub_sinh]; ring

/-! ## §3  The even sector, and the vacuum -/

/-- `A = (e^β + e^{-β})²`, the eigenvalue of the constant character at `L = 2`. -/
noncomputable def evenA (β : ℝ) : ℝ := (z2Norm β) ^ 2

/-- `B = (e^β − e^{-β})²`, the eigenvalue of the top character at `L = 2`. -/
noncomputable def evenB (β : ℝ) : ℝ := (Real.exp β - Real.exp (-β)) ^ 2

theorem evenA_pos (β : ℝ) : 0 < evenA β := by
  unfold evenA
  have := z2Norm_pos β
  positivity

theorem evenB_pos {β : ℝ} (hβ : 0 < β) : 0 < evenB β := by
  unfold evenB
  have h : Real.exp (-β) < Real.exp β := Real.exp_lt_exp.mpr (by linarith)
  have : 0 < Real.exp β - Real.exp (-β) := by linarith
  positivity

/-- **`A − B = 4`, exactly.**  Every estimate below runs on this identity. -/
theorem evenA_sub_evenB (β : ℝ) : evenA β - evenB β = 4 := by
  unfold evenA evenB z2Norm
  have h := exp_mul_exp_neg β
  nlinarith [h]

/-- An even-sector vector: `α · 1 + δ · s₀s₁`. -/
noncomputable def evenVec (α δ : ℝ) {L : ℕ} (σ : Fin L → Fin 2) : ℝ :=
  α + δ * allSign σ

/-- **The even sector closes**, by the matrix
`[[A cosh γ, B sinh γ], [A sinh γ, B cosh γ]]`. -/
theorem coupled_even_action (β γ α δ : ℝ) (σ : Fin 2 → Fin 2) :
    ∑ τ : Fin 2 → Fin 2, coupledKernel β γ σ τ * evenVec α δ τ
      = evenVec (Real.cosh γ * (α * evenA β) + Real.sinh γ * (δ * evenB β))
          (Real.cosh γ * (δ * evenB β) + Real.sinh γ * (α * evenA β)) σ := by
  have hsplit : ∀ τ : Fin 2 → Fin 2,
      coupledKernel β γ σ τ * evenVec α δ τ
        = spatialWeight γ σ * (α * spatialKernel β σ τ)
          + spatialWeight γ σ * (δ * (spatialKernel β σ τ * allSign τ)) := by
    intro τ
    unfold coupledKernel evenVec
    ring
  rw [Finset.sum_congr rfl fun τ _ => hsplit τ, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
    sum_spatialKernel, spatialKernel_allSign, spatialWeight_eq]
  unfold evenVec evenA evenB
  linear_combination (Real.sinh γ * δ * (Real.exp β - Real.exp (-β)) ^ 2) *
    allSign_sq σ

/-- The discriminant of the even block. -/
noncomputable def evenDisc (β γ : ℝ) : ℝ :=
  ((evenA β + evenB β) * Real.cosh γ) ^ 2 - 4 * (evenA β * evenB β)

theorem evenDisc_nonneg (β γ : ℝ) : 0 ≤ evenDisc β γ := by
  unfold evenDisc
  have hc : 1 ≤ Real.cosh γ := one_le_cosh' γ
  have hA : 0 < evenA β := evenA_pos β
  have hB : 0 ≤ evenB β := by unfold evenB; positivity
  nlinarith [sq_nonneg (evenA β - evenB β), sq_nonneg (evenA β + evenB β), hc,
    hA, hB, sq_nonneg (Real.cosh γ - 1)]

/-- The `+` branch of the even block's characteristic equation.  No claim is
made here that it is the larger root or the spectral radius; what is proved is
that it is an eigenvalue with a strictly positive eigenvector. -/
noncomputable def evenTop (β γ : ℝ) : ℝ :=
  ((evenA β + evenB β) * Real.cosh γ + Real.sqrt (evenDisc β γ)) / 2

theorem evenTop_char (β γ : ℝ) :
    evenTop β γ * evenTop β γ
      = (evenA β + evenB β) * Real.cosh γ * evenTop β γ
        - evenA β * evenB β := by
  have hsq : Real.sqrt (evenDisc β γ) * Real.sqrt (evenDisc β γ)
      = ((evenA β + evenB β) * Real.cosh γ) ^ 2 - 4 * (evenA β * evenB β) :=
    Real.mul_self_sqrt (evenDisc_nonneg β γ)
  unfold evenTop
  linear_combination hsq / 4

/-- The closed-form even-sector eigenvector at `L = 2`.  It is the object
Perron--Frobenius would call the vacuum; that identification is classical and is
NOT formalised here (the pinned `mathlib` carries no Perron--Frobenius theorem).
What is proved below is an eigen-equation and strict positivity. -/
noncomputable def perronVec (β γ : ℝ) (σ : Fin 2 → Fin 2) : ℝ :=
  evenVec (evenB β * Real.sinh γ) (evenTop β γ - evenA β * Real.cosh γ) σ

/-- **The eigen-equation.**  This is the object O-3f showed row-sum
normalisation stops producing. -/
theorem coupled_perron_eigen (β γ : ℝ) (σ : Fin 2 → Fin 2) :
    ∑ τ : Fin 2 → Fin 2, coupledKernel β γ σ τ * perronVec β γ τ
      = evenTop β γ * perronVec β γ σ := by
  unfold perronVec
  rw [coupled_even_action]
  unfold evenVec
  have hchar := evenTop_char β γ
  have hcs := cosh_sq_sub_sinh_sq' γ
  linear_combination (-(allSign σ)) * hchar
    - (evenA β * evenB β * allSign σ) * hcs

/-- **The vacuum is strictly positive.** -/
theorem perronVec_pos {β γ : ℝ} (hβ : 0 < β) (hγ : 0 < γ) (σ : Fin 2 → Fin 2) :
    0 < perronVec β γ σ := by
  have hs : 0 < Real.sinh γ := sinh_pos' hγ
  have hc : 1 ≤ Real.cosh γ := one_le_cosh' γ
  have hcs := cosh_sq_sub_sinh_sq' γ
  have hB : 0 < evenB β := evenB_pos hβ
  have hA : evenA β = evenB β + 4 := by
    have := evenA_sub_evenB β; linarith
  have hcgts : Real.sinh γ < Real.cosh γ := by nlinarith [hcs, hs, hc]
  have hsum : (0:ℝ) < Real.cosh γ + Real.sinh γ := by linarith
  have hdiff : (0:ℝ) < Real.cosh γ - Real.sinh γ := by linarith
  -- `Δ − (4c − 2Bs)² = 16 B s (c + s) > 0`, cofactor `4B(B+4)` on `cosh²−sinh²=1`
  have hlow : 4 * Real.cosh γ - 2 * evenB β * Real.sinh γ
      < Real.sqrt (evenDisc β γ) := by
    apply Real.lt_sqrt_of_sq_lt
    have hid : evenDisc β γ
        - (4 * Real.cosh γ - 2 * evenB β * Real.sinh γ) ^ 2
        = 16 * evenB β * Real.sinh γ * (Real.cosh γ + Real.sinh γ) := by
      unfold evenDisc
      rw [hA]
      linear_combination (4 * evenB β * (evenB β + 4)) * hcs
    nlinarith [hid, mul_pos (mul_pos hB hs) hsum]
  -- `(4c + 2Bs)² − Δ = 16 B s (c − s) > 0`
  have hhigh : Real.sqrt (evenDisc β γ)
      < 4 * Real.cosh γ + 2 * evenB β * Real.sinh γ := by
    rw [Real.sqrt_lt' (by nlinarith [hB, hs, hc])]
    have hid : (4 * Real.cosh γ + 2 * evenB β * Real.sinh γ) ^ 2
        - evenDisc β γ
        = 16 * evenB β * Real.sinh γ * (Real.cosh γ - Real.sinh γ) := by
      unfold evenDisc
      rw [hA]
      linear_combination (-(4 * evenB β * (evenB β + 4))) * hcs
    nlinarith [hid, mul_pos (mul_pos hB hs) hdiff]
  unfold perronVec evenVec evenTop
  rcases allSign_eq_one_or σ with h | h <;> rw [h] <;>
    nlinarith [hlow, hhigh, hs, hB, hA]

/-! ## §4  The odd sector: a second exact eigenpair -/

/-- The odd-sector eigenvector `s₀ + s₁`. -/
noncomputable def oddVec (σ : Fin 2 → Fin 2) : ℝ := siteSign 0 σ + siteSign 1 σ

/-- The odd eigenvector does not vanish identically. -/
theorem oddVec_cfgFlat : oddVec cfgFlat = 2 := by
  unfold oddVec siteSign cfgFlat z2Sign
  norm_num

/-- **The second exact eigenpair**, eigenvalue
`(e^β − e^{-β}) · (e^β + e^{-β}) · e^{γ}`. -/
theorem coupled_odd_eigen (β γ : ℝ) (σ : Fin 2 → Fin 2) :
    ∑ τ : Fin 2 → Fin 2, coupledKernel β γ σ τ * oddVec τ
      = (Real.exp β - Real.exp (-β)) * z2Norm β * Real.exp γ * oddVec σ := by
  have hsplit : ∀ τ : Fin 2 → Fin 2,
      coupledKernel β γ σ τ * oddVec τ
        = spatialWeight γ σ * (spatialKernel β σ τ * siteSign 0 τ)
          + spatialWeight γ σ * (spatialKernel β σ τ * siteSign 1 τ) := by
    intro τ; unfold coupledKernel oddVec; ring
  rw [Finset.sum_congr rfl fun τ _ => hsplit τ, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, spatialKernel_siteSign,
    spatialKernel_siteSign, spatialWeight_eq, exp_eq_cosh_add_sinh]
  norm_num
  unfold oddVec siteSign
  rw [allSign_two]
  linear_combination
    (Real.sinh γ * (Real.exp β - Real.exp (-β)) * z2Norm β * z2Sign (σ 1) 0) *
      z2Sign_sq (σ 0) 0
    + (Real.sinh γ * (Real.exp β - Real.exp (-β)) * z2Norm β * z2Sign (σ 0) 0) *
      z2Sign_sq (σ 1) 0
    - ((z2Sign (σ 0) 0 + z2Sign (σ 1) 0) * (Real.exp β - Real.exp (-β)) *
      z2Norm β) * exp_eq_cosh_add_sinh γ

/-! ## §5  The two exhibited eigenpairs are ordered -/

/-- The odd eigenvalue, named. -/
noncomputable def oddEigen (β γ : ℝ) : ℝ :=
  (Real.exp β - Real.exp (-β)) * z2Norm β * Real.exp γ

/-- `A · B = μ²` where `μ` is the odd eigenvalue at `γ = 0`: pure algebra. -/
theorem evenA_mul_evenB (β : ℝ) :
    evenA β * evenB β
      = ((Real.exp β - Real.exp (-β)) * z2Norm β) ^ 2 := by
  unfold evenA evenB z2Norm
  ring

/-- `A + B − 2μ₀ = 4 e^{-2β}` — the companion of `evenA_sub_evenB`, and what
makes the ordering below a two-line estimate. -/
theorem evenSum_sub_two_odd (β : ℝ) :
    evenA β + evenB β - 2 * ((Real.exp β - Real.exp (-β)) * z2Norm β)
      = 4 * Real.exp (-β) ^ 2 := by
  unfold evenA evenB z2Norm
  ring

/-- **The exhibited eigenpairs are ordered.**  The odd eigenvalue is strictly
below the eigenvalue carried by the strictly positive eigenvector, so the ratio
of the two exhibited eigenvalues is genuinely less than one.  This compares the
two eigenpairs of this module; no claim is made that they are the top two of the
spectrum. -/
theorem oddEigen_lt_evenTop {β γ : ℝ} (hβ : 0 < β) (hγ : 0 < γ) :
    oddEigen β γ < evenTop β γ := by
  have hs : 0 < Real.sinh γ := sinh_pos' hγ
  have hc : 1 ≤ Real.cosh γ := one_le_cosh' γ
  have hcs := cosh_sq_sub_sinh_sq' γ
  have hcpos : (0:ℝ) < Real.cosh γ := by linarith
  have hsum : (0:ℝ) < Real.cosh γ + Real.sinh γ := by linarith
  have hxy : Real.exp (-β) < Real.exp β := Real.exp_lt_exp.mpr (by linarith)
  have hy : (0:ℝ) < Real.exp (-β) := Real.exp_pos _
  have hy2 : (0:ℝ) < Real.exp (-β) ^ 2 := by positivity
  have hdiff : (0:ℝ) < Real.exp β ^ 2 - Real.exp (-β) ^ 2 := by nlinarith [hxy, hy]
  -- `Δ − X² = 16 cosh γ (cosh γ + sinh γ) e^{-2β} (e^{2β} − e^{-2β}) > 0`,
  -- cofactor `4 A B` on `cosh² − sinh² = 1`; no `e^β e^{-β} = 1` is needed.
  have hkey : (2 * ((Real.exp β - Real.exp (-β)) * z2Norm β)
        * (Real.cosh γ + Real.sinh γ)
        - (evenA β + evenB β) * Real.cosh γ) ^ 2 < evenDisc β γ := by
    have hid : evenDisc β γ
        - (2 * ((Real.exp β - Real.exp (-β)) * z2Norm β)
            * (Real.cosh γ + Real.sinh γ)
            - (evenA β + evenB β) * Real.cosh γ) ^ 2
        = 16 * Real.cosh γ * (Real.cosh γ + Real.sinh γ) * Real.exp (-β) ^ 2
            * (Real.exp β ^ 2 - Real.exp (-β) ^ 2) := by
      unfold evenDisc evenA evenB z2Norm
      linear_combination
        (4 * (Real.exp β - Real.exp (-β)) ^ 2 * (Real.exp β + Real.exp (-β)) ^ 2) * hcs
    have hpos : (0:ℝ) < 16 * Real.cosh γ * (Real.cosh γ + Real.sinh γ)
        * Real.exp (-β) ^ 2 * (Real.exp β ^ 2 - Real.exp (-β) ^ 2) :=
      mul_pos (mul_pos (mul_pos (mul_pos (by norm_num : (0:ℝ) < 16) hcpos) hsum) hy2)
        hdiff
    linarith [hid, hpos]
  have hlt := Real.lt_sqrt_of_sq_lt hkey
  unfold oddEigen evenTop
  rw [exp_eq_cosh_add_sinh γ]
  linarith [hlt]

end YangMills.OS
