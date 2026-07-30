import YangMills.OS.SpatialUniform

/-!
# Endpoint reflection positivity for the coupled slice

**What this module proves, stated before anything else.**  The reflected
two-point form of the Gibbs measure, at the two ENDS of a path, for REAL
observables of a SINGLE slice, is non-negative --- and the Gram matrix of a
family of them is positive semidefinite.  That is not yet the
Osterwalder–Schrader axiom, which quantifies over observables of the whole past
half-chain and over complex ones.  The half-chain algebra, the reflection map
and the sesquilinear form are **not** built here; see the closing section.

Eleven papers in this lane end with *reflection positivity is untouched*.  This
touches the endpoint form of it, and the interesting part is what the source
weight does --- namely nothing.

Earlier papers do prove statements about the coupled kernel: `specGap < lam`
holds there too.  What is new is that this result is **unchanged** by the
weight: same hypothesis, same conclusion, no constant that depends on `w`.
Every earlier coupled-kernel statement has a number in it that moves when `w`
does.  Positivity is the SIGN of a quadratic form, and conjugating by `√w` is a
congruence, so there is nothing for the weight to move.

## Two reflections, two hypotheses

For a transfer chain the reflected two-point sum is `⟨v, Kᴺ v⟩` with
`v = dress A`, and there are two cases with genuinely different content.

* **Through a site** (`N` even).  `Kᴺ` is a square, so the sum is a norm and is
  non-negative **for every `β`**, negative coupling included.  Nothing is needed
  but symmetry of the kernel.
* **Through a bond** (`N` odd).  Now the sum is `⟨Kᵐv, K Kᵐv⟩`, which needs `K`
  itself positive semidefinite.  That holds exactly for `β ≥ 0`, and the
  boundary is sharp: at `β < 0` the single-site sign observable makes the sum
  equal to `2(e^β − e^{-β})ᴺ`, which is negative --- and, since congruence is
  invertible, the coupled kernel is indefinite below zero for EVERY positive
  weight, at every extent with at least one site.

## What is proved

* `sum_iterate_even_nonneg` — the site reflection, for any symmetric kernel and
  every `β`: `0 ≤ ∑ (Kᴺ u) · u` when `N` is even.
* `spatialKernel_posSemidef` — the decoupled kernel is positive semidefinite for
  `β ≥ 0`, by induction on the extent.
* `posSemidef_congr` / `symWeighted_posSemidef` — **positivity transports through
  the source weight**, because conjugating by `√w` is a congruence.  This is
  what the coupled kernel needs and it costs one line.
* `sum_iterate_odd_nonneg` — the bond reflection at `β ≥ 0`, every `N`.
* `gibbsPathSum_nonneg_even` / `gibbsPathSum_nonneg` — the same two statements
  about the Gibbs measure itself, via the bridge.
* `gibbsPathSum_neg_of_neg_beta` — **sharpness**: at `β < 0` and odd `N` the sign
  observable gives exactly `2(e^β − e^{-β})ᴺ < 0`.  The hypothesis `β ≥ 0` is
  therefore active, not decorative.
* `symWeighted_quadForm_neg_of_neg_beta` — and sharper: for **every** strictly
  positive weight and every extent with at least one site, the COUPLED kernel is
  indefinite below zero.  Congruence is invertible, so the inertia transports
  both ways and the witness is the sign observable divided by `√w`.
* `spatialKernel_posSemidef_zero` — the exception, recorded rather than left to
  be found: at `L = 0` the space is a point, the kernel is `1`, and the form is
  a square at every `β`.  The boundary is sharp from one site upwards.
* `gibbsPathSum_gram_nonneg` / `gibbsPathSum_gram_nonneg_even` — the GRAM
  statement: positivity of the whole matrix over a family of observables, not
  only of one diagonal entry.  `gibbsPathSum_combo` is the bilinearity that
  makes the matrix form visible.

## What is NOT proved, and is not claimed

**This is not the Osterwalder–Schrader axiom yet.**  That axiom is about a
general observable `F` of the past half-chain, complex-valued, with the matrix
`⟨ΘFᵢ, Fⱼ⟩` positive semidefinite.  Here the observables are REAL and depend on a
SINGLE slice, at the two ends of the path; no reflection map `Θ` is defined and
no half-chain algebra is built.  The missing step is the collapse of each half
to its boundary vector, after which `sum_iterate_even_nonneg` and
`symWeighted_posSemidef` are exactly the two facts needed --- so the gap is a
construction, not a further inequality.  It is registered, not done, and not
claimed.

**And no reconstruction.**  The physical Hilbert space as the quotient of the
past algebra by the null space of this form is not built.

The measured degeneration of `specRatio(L)` for a ring weight is exactly that,
measured; no theorem says the weight *destroys* uniformity, only that no uniform
bound is proved for it.  Nothing here concerns uniformity in the extent,
`SU(N)`, the continuum limit, or the Clay problem.

Oracle target: `[propext, Classical.choice, Quot.sound]`.  No sorry, no axioms.
-/

namespace YangMills.OS

set_option linter.unusedSectionVars false

/-! ## §1  Reflection through a site: free, at every coupling -/

section Even

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- **THE SITE REFLECTION.**  At even separation the reflected sum is a norm, so
it is non-negative for a symmetric kernel with no further hypothesis --- in
particular at negative coupling, where the bond reflection fails. -/
theorem sum_iterate_even_nonneg {K : ι → ι → ℝ} (hK : ∀ i j, K i j = K j i)
    (m : ℕ) (u : ι → ℝ) :
    0 ≤ ∑ i, (act K)^[2 * m] u i * u i := by
  have hsplit : (act K)^[2 * m] u = (act K)^[m] ((act K)^[m] u) := by
    rw [← Function.iterate_add_apply]
    congr 1
    omega
  rw [hsplit, iterate_pairing_symm hK m ((act K)^[m] u) u]
  exact Finset.sum_nonneg fun i _ => mul_self_nonneg _

end Even

/-! ## §2  The decoupled kernel is positive semidefinite exactly for `β ≥ 0`

The induction is the one the uniformity module used, with the same split at the
first site; only the bookkeeping changes.  The even part and the odd part each
inherit positivity, and they are recombined with the two bond eigenvalues `Z`
and `D` --- which is where `β ≥ 0` enters, since `D < 0` below it. -/

/-- The image of an observable, split at the first site.  Extracted from the
uniformity module's induction, where it was inline. -/
theorem act_spatialKernel_cons (β : ℝ) {L : ℕ} (u : (Fin (L + 1) → Fin 2) → ℝ)
    (a : Fin 2) (σ : Fin L → Fin 2) :
    act (spatialKernel β) u (Fin.cons a σ)
      = z2Bond β a 0 * act (spatialKernel β) (fun τ => u (Fin.cons 0 τ)) σ
        + z2Bond β a 1 * act (spatialKernel β) (fun τ => u (Fin.cons 1 τ)) σ := by
  show (∑ σ', spatialKernel β (Fin.cons a σ) σ' * u σ') = _
  rw [sum_cons_config (fun σ' => spatialKernel β (Fin.cons a σ) σ' * u σ')]
  have hstep : ∀ s : Fin 2,
      (∑ τ : Fin L → Fin 2,
          spatialKernel β (Fin.cons a σ) (Fin.cons s τ) * u (Fin.cons s τ))
        = z2Bond β a s * act (spatialKernel β) (fun τ => u (Fin.cons s τ)) σ := by
    intro s
    show _ = z2Bond β a s * ∑ τ, spatialKernel β σ τ * u (Fin.cons s τ)
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun τ _ => by
      rw [spatialKernel_cons β a s σ τ]; ring
  rw [Fin.sum_univ_two, hstep 0, hstep 1]

/-- **THE DECOUPLED KERNEL IS PSD, for `β ≥ 0`.**  By induction on the extent:
the even and odd parts of an observable each inherit positivity, and the two are
recombined with the bond eigenvalues `Z > 0` and `D = e^β − e^{-β} ≥ 0`. -/
theorem spatialKernel_posSemidef {β : ℝ} (hβ : 0 ≤ β) :
    ∀ (L : ℕ) (u : (Fin L → Fin 2) → ℝ),
      0 ≤ ∑ σ, u σ * act (spatialKernel β) u σ := by
  intro L
  induction L with
  | zero =>
    intro u
    have hone : ∀ σ : Fin 0 → Fin 2, act (spatialKernel β) u σ = u σ := by
      intro σ
      show (∑ τ, spatialKernel β σ τ * u τ) = u σ
      have : ∑ τ : Fin 0 → Fin 2, spatialKernel β σ τ * u τ
          = spatialKernel β σ σ * u σ :=
        Finset.sum_eq_single σ
          (fun b _ hb => absurd (Subsingleton.elim b σ) hb)
          (fun h => absurd (Finset.mem_univ σ) h)
      rw [this]
      show (∏ _j : Fin 0, _) * u σ = u σ
      simp
    rw [Finset.sum_congr rfl fun σ _ => by rw [hone σ]]
    exact Finset.sum_nonneg fun σ _ => mul_self_nonneg _
  | succ L ih =>
    intro u
    have hD : (0:ℝ) ≤ Real.exp β - Real.exp (-β) :=
      sub_nonneg.mpr (Real.exp_le_exp.mpr (by linarith))
    have hZ : (0:ℝ) < z2Norm β := z2Norm_pos β
    have hP := ih (fun τ => u (Fin.cons 0 τ) + u (Fin.cons 1 τ))
    have hM := ih (fun τ => u (Fin.cons 0 τ) - u (Fin.cons 1 τ))
    rw [act_add (spatialKernel β)] at hP
    rw [act_sub (spatialKernel β)] at hM
    simp only [] at hP hM
    rw [sum_cons_config (fun σ => u σ * act (spatialKernel β) u σ), Fin.sum_univ_two]
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
    have h1 : 0 ≤ z2Norm β * SP := mul_nonneg (le_of_lt hZ) hP
    have h2 : 0 ≤ (Real.exp β - Real.exp (-β)) * SM := mul_nonneg hD hM
    linarith

/-! ## §3  Positivity survives the source weight

This is the whole reason the coupled kernel is reachable when uniformity was
not.  Conjugating by `√w` is a congruence, and a congruence cannot change the
sign of a quadratic form. -/

/-- **CONGRUENCE.**  If a kernel is positive semidefinite then so is
`c · K · c` for any function `c`.  One reindexing of the quadratic form. -/
theorem posSemidef_congr {ι : Type*} [Fintype ι] {K : ι → ι → ℝ}
    (hK : ∀ v : ι → ℝ, 0 ≤ ∑ i, v i * act K v i) (c : ι → ℝ) (u : ι → ℝ) :
    0 ≤ ∑ i, u i * act (fun i j => c i * K i j * c j) u i := by
  have hrw : ∑ i, u i * act (fun i j => c i * K i j * c j) u i
      = ∑ i, (fun k => c k * u k) i * act K (fun k => c k * u k) i := by
    refine Finset.sum_congr rfl fun i _ => ?_
    show u i * (∑ j, c i * K i j * c j * u j)
      = (c i * u i) * ∑ j, K i j * (c j * u j)
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hrw]
  exact hK _

/-- **THE COUPLED KERNEL IS PSD.**  For `β ≥ 0` and **any** strictly positive
source weight --- the weight that destroys uniformity in the extent leaves
positivity exactly where it was. -/
theorem symWeighted_posSemidef {L : ℕ} {w : (Fin L → Fin 2) → ℝ}
    (hw : ∀ σ, 0 < w σ) {β : ℝ} (hβ : 0 ≤ β) (u : (Fin L → Fin 2) → ℝ) :
    0 ≤ ∑ σ, u σ * act (symWeighted w β) u σ := by
  have h := posSemidef_congr (K := spatialKernel β)
    (fun v => spatialKernel_posSemidef hβ L v) (fun σ => Real.sqrt (w σ)) u
  have hfun : (fun σ τ => Real.sqrt (w σ) * spatialKernel β σ τ * Real.sqrt (w τ))
      = symWeighted w β := rfl
  rwa [hfun] at h

/-! ## §4  Reflection through a bond -/

/-- **THE BOND REFLECTION.**  At `β ≥ 0` the reflected sum is non-negative at
**every** separation, even or odd: the odd case is the positive-semidefinite
kernel evaluated on an iterated image. -/
theorem sum_iterate_odd_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι]
    {K : ι → ι → ℝ} (hK : ∀ i j, K i j = K j i)
    (hpsd : ∀ v : ι → ℝ, 0 ≤ ∑ i, v i * act K v i) (m : ℕ) (u : ι → ℝ) :
    0 ≤ ∑ i, (act K)^[2 * m + 1] u i * u i := by
  have hsplit : (act K)^[2 * m + 1] u
      = (act K)^[m] (act K ((act K)^[m] u)) := by
    rw [← Function.iterate_succ_apply, ← Function.iterate_add_apply]
    congr 1
    omega
  rw [hsplit, iterate_pairing_symm hK m (act K ((act K)^[m] u)) u]
  have hcomm : ∑ i, act K ((act K)^[m] u) i * (act K)^[m] u i
      = ∑ i, (act K)^[m] u i * act K ((act K)^[m] u) i :=
    Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [hcomm]
  exact hpsd _

/-! ## §5  The same two statements, about the Gibbs measure

The bridge turns the reflected two-point sum into `⟨v, Kᴺ v⟩`, so §1 and §4
transfer verbatim.  Nothing here is about a normalised expectation: the
partition function is positive, so the signs agree, but the statement proved is
about the unnormalised sum, which is the object reflection positivity is about. -/

/-- **REFLECTION POSITIVITY THROUGH A SITE, in the measure.**  At even
separation the reflected two-point sum is non-negative for **every** `β`, at
every extent, and for **any** strictly positive source weight. -/
theorem gibbsPathSum_nonneg_even {L : ℕ} {w : (Fin L → Fin 2) → ℝ}
    (hw : ∀ σ, 0 < w σ) (β : ℝ) (m : ℕ) (A : (Fin L → Fin 2) → ℝ) :
    0 ≤ gibbsPathSum w β (2 * m) A A := by
  rw [gibbsPathSum_eq_iterate hw β (2 * m) A A]
  exact sum_iterate_even_nonneg (symWeighted_symm w β) m (dress w A)

/-- **REFLECTION POSITIVITY THROUGH A BOND, in the measure.**  At `β ≥ 0` the
reflected sum is non-negative at **every** separation, at every extent, and for
**any** strictly positive source weight --- the coupled kernel included. -/
theorem gibbsPathSum_nonneg {L : ℕ} {w : (Fin L → Fin 2) → ℝ}
    (hw : ∀ σ, 0 < w σ) {β : ℝ} (hβ : 0 ≤ β) (N : ℕ)
    (A : (Fin L → Fin 2) → ℝ) :
    0 ≤ gibbsPathSum w β N A A := by
  rw [gibbsPathSum_eq_iterate hw β N A A]
  rcases Nat.even_or_odd N with ⟨r, hr⟩ | ⟨k, hk⟩
  · have h2 : N = 2 * r := by omega
    rw [h2]
    exact sum_iterate_even_nonneg (symWeighted_symm w β) r (dress w A)
  · rw [hk]
    exact sum_iterate_odd_nonneg (symWeighted_symm w β)
      (fun v => symWeighted_posSemidef hw hβ v) k (dress w A)

/-! ## §6  Sharpness: below zero the bond reflection genuinely fails

A hypothesis that is never active is not worth stating.  At `β < 0` the
single-site sign observable --- the one the extent paper already built ---
gives the reflected sum EXACTLY, and the value is negative. -/

/-- The sign observable squares to one, so its norm counts configurations. -/
theorem sum_siteSign_sq_one :
    ∑ σ : Fin 1 → Fin 2, siteSign 0 σ * siteSign 0 σ = 2 := by
  have hone : ∀ σ : Fin 1 → Fin 2, siteSign 0 σ * siteSign 0 σ = 1 := by
    intro σ
    unfold siteSign z2Sign
    by_cases h : σ 0 = 0 <;> simp [h]
  rw [Finset.sum_congr rfl fun σ _ => hone σ, Finset.sum_const, Finset.card_univ,
    Fintype.card_fun]
  simp

/-- **THE WITNESS, exactly.**  At one site and constant weight, the sign
observable gives the reflected sum in closed form: `2 (e^β − e^{-β})ᴺ`. -/
theorem gibbsPathSum_siteSign_eq (β : ℝ) (N : ℕ) :
    gibbsPathSum (fun _ : Fin 1 → Fin 2 => (1:ℝ)) β N (siteSign 0) (siteSign 0)
      = 2 * (Real.exp β - Real.exp (-β)) ^ N := by
  rw [gibbsPathSum_eq_iterate (fun _ => one_pos) β N, symWeighted_one β (L := 1),
    dress_one]
  have heig : ∀ σ : Fin 1 → Fin 2,
      ∑ τ, spatialKernel β σ τ * siteSign 0 τ
        = (Real.exp β - Real.exp (-β)) * siteSign 0 σ := by
    intro σ
    simpa using spatialKernel_siteSign β (0 : Fin 1) σ
  rw [iterate_act_eigen heig N]
  rw [show (∑ σ : Fin 1 → Fin 2,
      (Real.exp β - Real.exp (-β)) ^ N * siteSign 0 σ * siteSign 0 σ)
      = (Real.exp β - Real.exp (-β)) ^ N
        * ∑ σ : Fin 1 → Fin 2, siteSign 0 σ * siteSign 0 σ by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun σ _ => by ring]
  rw [sum_siteSign_sq_one]
  ring

/-- **THE HYPOTHESIS IS ACTIVE.**  Below zero coupling, at odd separation, the
bond reflection fails --- and the failure is exhibited, not inferred. -/
theorem gibbsPathSum_neg_of_neg_beta {β : ℝ} (hβ : β < 0) (m : ℕ) :
    gibbsPathSum (fun _ : Fin 1 → Fin 2 => (1:ℝ)) β (2 * m + 1)
        (siteSign 0) (siteSign 0) < 0 := by
  rw [gibbsPathSum_siteSign_eq β (2 * m + 1)]
  have hD : Real.exp β - Real.exp (-β) < 0 :=
    sub_neg.mpr (Real.exp_lt_exp.mpr (by linarith))
  have hodd : Odd (2 * m + 1) := ⟨m, rfl⟩
  have := hodd.pow_neg hD
  linarith

/-! ## §7  Sharpness for EVERY positive weight, not only the constant one

The witness above sits at one site and constant weight, so it refutes the
universally quantified statement but says nothing about a particular coupled
kernel.  Congruence is invertible --- `√w` is nowhere zero --- so the inertia
transports in BOTH directions, and the same sign observable divided by `√w`
witnesses indefiniteness of the coupled kernel at every extent with at least one
site.

At `L = 0` there is nothing to witness: the configuration space is a point, the
kernel is the number `1`, and it is positive semidefinite for every `β`.  So the
boundary `β ≥ 0` is sharp exactly from one site upwards. -/

/-- The sign observable, undressed by the weight.  This is the vector congruence
sends to the decoupled witness. -/
noncomputable def unweightedSign {L : ℕ} (w : (Fin L → Fin 2) → ℝ) (i : Fin L)
    (σ : Fin L → Fin 2) : ℝ :=
  siteSign i σ / Real.sqrt (w σ)

/-- **THE COUPLED KERNEL IS INDEFINITE BELOW ZERO, for EVERY positive weight.**
At every extent with at least one site and every strictly positive `w`, the
quadratic form of `symWeighted w β` takes a negative value when `β < 0`.  So
`β ≥ 0` is not merely sufficient for the bond reflection: below it the coupled
kernel itself fails, whatever the weight. -/
theorem symWeighted_quadForm_neg_of_neg_beta {M : ℕ}
    {w : (Fin (M + 1) → Fin 2) → ℝ} (hw : ∀ σ, 0 < w σ) {β : ℝ} (hβ : β < 0) :
    ∑ σ, unweightedSign w 0 σ * act (symWeighted w β) (unweightedSign w 0) σ
      = (Real.exp β - Real.exp (-β)) * (z2Norm β) ^ M * 2 ^ (M + 1)
    ∧ ∑ σ, unweightedSign w 0 σ * act (symWeighted w β) (unweightedSign w 0) σ < 0 := by
  have hsq : ∀ σ : Fin (M + 1) → Fin 2, Real.sqrt (w σ) ≠ 0 := fun σ =>
    ne_of_gt (Real.sqrt_pos.mpr (hw σ))
  -- the weight cancels: congruence carries the witness across
  have hstep : ∀ σ : Fin (M + 1) → Fin 2,
      unweightedSign w 0 σ * act (symWeighted w β) (unweightedSign w 0) σ
        = (Real.exp β - Real.exp (-β)) * (z2Norm β) ^ M
          * (siteSign 0 σ * siteSign 0 σ) := by
    intro σ
    have hact : act (symWeighted w β) (unweightedSign w 0) σ
        = Real.sqrt (w σ) * ((Real.exp β - Real.exp (-β)) * (z2Norm β) ^ M
            * siteSign 0 σ) := by
      show (∑ τ, symWeighted w β σ τ * unweightedSign w 0 τ) = _
      have hin : ∀ τ, symWeighted w β σ τ * unweightedSign w 0 τ
          = Real.sqrt (w σ) * (spatialKernel β σ τ * siteSign 0 τ) := by
        intro τ
        show Real.sqrt (w σ) * spatialKernel β σ τ * Real.sqrt (w τ)
            * (siteSign 0 τ / Real.sqrt (w τ)) = _
        field_simp [hsq τ]
      rw [Finset.sum_congr rfl fun τ _ => hin τ, ← Finset.mul_sum,
        spatialKernel_siteSign β (0 : Fin (M + 1)) σ]
      simp
    rw [hact]
    unfold unweightedSign
    field_simp [hsq σ]
  have hsum : ∑ σ : Fin (M + 1) → Fin 2, siteSign 0 σ * siteSign 0 σ
      = 2 ^ (M + 1) := by
    have hone : ∀ σ : Fin (M + 1) → Fin 2, siteSign 0 σ * siteSign 0 σ = 1 := by
      intro σ
      unfold siteSign z2Sign
      by_cases h : σ 0 = 0 <;> simp [h]
    rw [Finset.sum_congr rfl fun σ _ => hone σ, Finset.sum_const, Finset.card_univ,
      Fintype.card_fun]
    simp
  have hval : ∑ σ, unweightedSign w 0 σ * act (symWeighted w β) (unweightedSign w 0) σ
      = (Real.exp β - Real.exp (-β)) * (z2Norm β) ^ M * 2 ^ (M + 1) := by
    rw [Finset.sum_congr rfl fun σ _ => hstep σ, ← Finset.mul_sum, hsum]
  refine ⟨hval, ?_⟩
  rw [hval]
  have hD : Real.exp β - Real.exp (-β) < 0 :=
    sub_neg.mpr (Real.exp_lt_exp.mpr (by linarith))
  have h1 : (0:ℝ) < (z2Norm β) ^ M := pow_pos (z2Norm_pos β) M
  have h2 : (0:ℝ) < 2 ^ (M + 1) := by positivity
  exact mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hD h1) h2

/-- **At `L = 0` there is nothing to witness.**  One configuration, the kernel is
the number `1`, and the form is a square at every `β`.  The sharpness of the
boundary is a statement from one site upwards, and this records the exception
rather than leaving it to be discovered. -/
theorem spatialKernel_posSemidef_zero (β : ℝ) (u : (Fin 0 → Fin 2) → ℝ) :
    0 ≤ ∑ σ, u σ * act (spatialKernel β) u σ := by
  have hone : ∀ σ : Fin 0 → Fin 2, act (spatialKernel β) u σ = u σ := by
    intro σ
    show (∑ τ, spatialKernel β σ τ * u τ) = u σ
    have h : ∑ τ : Fin 0 → Fin 2, spatialKernel β σ τ * u τ
        = spatialKernel β σ σ * u σ :=
      Finset.sum_eq_single σ
        (fun b _ hb => absurd (Subsingleton.elim b σ) hb)
        (fun h => absurd (Finset.mem_univ σ) h)
    rw [h]
    show (∏ _j : Fin 0, _) * u σ = u σ
    simp
  rw [Finset.sum_congr rfl fun σ _ => by rw [hone σ]]
  exact Finset.sum_nonneg fun σ _ => mul_self_nonneg _

/-! ## §8  The Gram form: positivity of the whole matrix, not only its diagonal

Reflection positivity is a statement about a MATRIX being positive
semidefinite, not about one diagonal entry.  For the endpoint observables the
matrix version follows from the diagonal one by bilinearity, and is stated so
that the diagonal is not mistaken for the whole. -/

/-- A real combination of observables. -/
noncomputable def combo {L k : ℕ} (c : Fin k → ℝ)
    (A : Fin k → (Fin L → Fin 2) → ℝ) (σ : Fin L → Fin 2) : ℝ :=
  ∑ i, c i * A i σ

/-- The reflected form is bilinear, so a combination pulls out. -/
theorem gibbsPathSum_combo {L k : ℕ} {w : (Fin L → Fin 2) → ℝ} (β : ℝ) (N : ℕ)
    (c : Fin k → ℝ) (A : Fin k → (Fin L → Fin 2) → ℝ) :
    gibbsPathSum w β N (combo c A) (combo c A)
      = ∑ i, ∑ j, c i * c j * gibbsPathSum w β N (A i) (A j) := by
  unfold gibbsPathSum combo
  have hpt : ∀ X : Fin (N + 1) → (Fin L → Fin 2),
      (∑ i, c i * A i (X 0)) * (∑ j, c j * A j (X (Fin.last N)))
          * gibbsWeight w β X
        = ∑ i, ∑ j, c i * c j
            * (A i (X 0) * A j (X (Fin.last N)) * gibbsWeight w β X) := by
    intro X
    rw [Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [Finset.sum_congr rfl fun X _ => hpt X, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]

/-- **THE GRAM MATRIX IS POSITIVE SEMIDEFINITE.**  For `β ≥ 0`, every family of
endpoint observables and every real combination, the reflected form of the
combination is non-negative --- which is the matrix statement, with the
single-observable theorem as its diagonal. -/
theorem gibbsPathSum_gram_nonneg {L k : ℕ} {w : (Fin L → Fin 2) → ℝ}
    (hw : ∀ σ, 0 < w σ) {β : ℝ} (hβ : 0 ≤ β) (N : ℕ)
    (c : Fin k → ℝ) (A : Fin k → (Fin L → Fin 2) → ℝ) :
    0 ≤ gibbsPathSum w β N (combo c A) (combo c A) :=
  gibbsPathSum_nonneg hw hβ N (combo c A)

/-- The same at even separation, where no hypothesis on `β` is needed. -/
theorem gibbsPathSum_gram_nonneg_even {L k : ℕ} {w : (Fin L → Fin 2) → ℝ}
    (hw : ∀ σ, 0 < w σ) (β : ℝ) (m : ℕ)
    (c : Fin k → ℝ) (A : Fin k → (Fin L → Fin 2) → ℝ) :
    0 ≤ gibbsPathSum w β (2 * m) (combo c A) (combo c A) :=
  gibbsPathSum_nonneg_even hw β m (combo c A)

end YangMills.OS
