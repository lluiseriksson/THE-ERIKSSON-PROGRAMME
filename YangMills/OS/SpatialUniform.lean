import YangMills.OS.SpatialSpectral

/-!
# The rate that does not depend on the extent

Every rate in this lane so far has been a fixed-`L` rate.  The gap paper proved
strict separation at each extent and said plainly it was not uniform; the S
block gave the separation a modulus, `specRatio(L)`, and reported measurements
saying that modulus tends to `1` outside the disordered region.  A geometric
bound whose rate tends to `1` is empty in the volume limit, so no rate in the
lane was extent-free, and the word *clustering* was never used.

For the **decoupled** kernel this module gives an extent-free rate, sharply:
`specRatio = tanh β` at every **positive** extent.  (At `L = 0` there is one
configuration, the only eigenvalue is the Perron one, and `specRatio = 0`; the
statement is about `L ≥ 1`, as `spatialKernel_specGap_eq` is.)  Throughout, `β ≥ 0` --- at negative
coupling the odd bond eigenvalue `D` is negative and `tanh β · Z^L` is not
`specGap`, so the hypothesis is load-bearing and not a convention.

**An extent-free rate is not a volume limit.**  A bound `C(L) · ρ^N` with
`C(L) → ∞` says nothing as the system grows however small `ρ` is, so the rate
alone settles nothing.  §8 supplies what actually is uniform here: at constant
weight the constant is the observable's mean square, the threshold is absent,
and both are uniform in `L`.  The word *clustering* is still not used, because
no infinite-volume state is constructed.

## The proof, and why it is not the spectral decomposition

The decoupled kernel is a product over sites, so its spectrum is a product and
the answer can be read off a tensor decomposition.  That route needs the
spectrum of a Kronecker power, which mathlib does not carry.

It is not needed.  The S block's `specGap_isGreatest` proved that `specGap` is
the **greatest** norm ratio on the fluctuation sector, so bounding it above is
exactly an operator inequality — no eigenbasis anywhere — and that inequality
falls to induction on the extent:

* split an observable at the first site, `u = (u₀, u₁)`;
* the even part `p = u₀ + u₁` still has mean zero, so the inductive hypothesis
  applies to it with rate `tanh β`;
* the odd part `m = u₀ − u₁` has no orthogonality left, so it gets only Schur's
  test, with rate `1`;
* and the two rates recombine **exactly**, because `Z · tanh β = D`, where
  `Z = e^β + e^{-β}` is the row sum and `D = e^β − e^{-β}` the odd eigenvalue of
  a single bond.

The last line is why the constant does not degrade with `L`: the loss on the
odd part is precisely compensated by the odd bond eigenvalue, at every step.

## What is proved

* `norm_act_le_of_rowSum` — Schur's test: a symmetric nonnegative kernel with
  constant row sums `R` has operator norm at most `R`.  One Cauchy–Schwarz.
* `spatialKernel_fluct_bound` — the uniform operator bound: for every `L` and
  every mean-zero `u`, `‖K u‖ ≤ tanh β · Zᴸ · ‖u‖`.
* `spatialKernel_specGap_le` — hence `specGap ≤ tanh β · Zᴸ`, at every extent.
* `spatialKernel_specGap_eq` — and **equality**, at every extent with at least
  one site: the single-site observable the companion extent paper already built
  attains it.  So `tanh β` is not a bound that happens not to degrade, it is the
  number.
* `symWeighted_one_specRatio_le` — the same for the kernel the S-block endpoint
  is phrased with, since at constant weight the two coincide.
* `gibbs_decay_extent_free_rate` — composing with the S-block endpoint, the
  normalised Gibbs two-point function is bounded by `C · (tanh β) ^ N` past one
  threshold.  The RATE contains no `L`; its `C` and its threshold come from that
  endpoint and are **not** claimed uniform in the extent.
* `gibbsCorr_one_uniform_bound` — and the bound that IS uniform, computed
  directly rather than composed: at constant weight, for **every** `N` and with
  no threshold, `|E[A(X₀)A(X_N)]| ≤ ⟨A²⟩ · (tanh β)^N`, the mean square being
  taken in the uniform measure.  For `|A| ≤ 1` the constant is at most `1` at
  every extent, so here the whole bound is uniform, not merely its rate.
* `gibbsCov_one_uniform_bound` — the same for an ARBITRARY observable, centred:
  the constant becomes its variance in the uniform measure.
* `gibbsCorr_one_le_of_bounded` — and the form with **no `L` on the right at
  all**: for a mean-zero observable bounded by `1`, the two-point function is
  below `(tanh β) ^ N`, with no threshold and no constant.

## What is NOT proved, and is not claimed

The **coupled** kernel — the one with a nonconstant source weight — is not
touched.  Nothing here says its rate is uniform, and the measured evidence in
the S block is that it is not, outside the disordered region.  The constant `C`
in the payoff still depends on the observable; only the rate is uniform.

At constant source weight the Gibbs measure **factorises across spatial sites**
into `L` independent one-dimensional temporal chains --- the slices `X₀, …, X_N`
themselves remain coupled in time, which is exactly what the rate `tanh β`
measures.  So the statement proved here is a statement about a product measure
over sites.  That is exactly why it is
reachable, and it is said here rather than left for a reader to notice.  What it
establishes is narrower than it sounds: **the extent alone does not degrade the
rate** in the product kernel.  It does not show that every nonconstant weight
destroys uniformity, nor that the weight is the sole cause of the coupled
model's degradation.

No infinite-volume state is constructed anywhere in this module, and no
statement here is about one.

Oracle target: `[propext, Classical.choice, Quot.sound]`.  No sorry, no axioms.
-/

namespace YangMills.OS

set_option linter.unusedSectionVars false

/-! ## §1  Schur's test -/

section Schur

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- **Schur's test.**  A symmetric nonnegative kernel all of whose row sums equal
`R` has operator norm at most `R`.  This is the crude bound the odd part of the
induction is allowed, and it is all it needs. -/
theorem norm_act_le_of_rowSum {K : ι → ι → ℝ} {R : ℝ}
    (hnn : ∀ i j, 0 ≤ K i j) (hsym : ∀ i j, K i j = K j i)
    (hrow : ∀ i, ∑ j, K i j = R) (u : ι → ℝ) :
    eucNorm (act K u) ≤ R * eucNorm u := by
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have hR : 0 ≤ R := by
    rw [← hrow i₀]
    exact Finset.sum_nonneg fun j _ => hnn i₀ j
  have hrowsq : ∀ i, act K u i * act K u i ≤ R * ∑ j, K i j * (u j * u j) := by
    intro i
    have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul (Finset.univ : Finset ι)
      (r := fun j => K i j * u j) (f := fun j => K i j)
      (g := fun j => K i j * (u j * u j))
      (fun j _ => hnn i j) (fun j _ => mul_nonneg (hnn i j) (mul_self_nonneg _))
      (fun j _ => by ring)
    rw [hrow i] at hcs
    calc act K u i * act K u i = (∑ j, K i j * u j) ^ 2 := by unfold act; ring
      _ ≤ R * ∑ j, K i j * (u j * u j) := hcs
  have hswap : ∑ i, (∑ j, K i j * (u j * u j)) = R * ∑ j, u j * u j := by
    rw [Finset.sum_comm]
    have hstep : ∀ j, (∑ i, K i j * (u j * u j)) = R * (u j * u j) := by
      intro j
      rw [← Finset.sum_mul]
      congr 1
      rw [← hrow j]
      exact Finset.sum_congr rfl fun i _ => hsym i j
    rw [Finset.sum_congr rfl fun j _ => hstep j, ← Finset.mul_sum]
  have hsum : ∑ i, act K u i * act K u i ≤ R ^ 2 * ∑ j, u j * u j := by
    calc ∑ i, act K u i * act K u i
        ≤ ∑ i, R * ∑ j, K i j * (u j * u j) :=
          Finset.sum_le_sum fun i _ => hrowsq i
      _ = R * ∑ i, (∑ j, K i j * (u j * u j)) := by rw [Finset.mul_sum]
      _ = R ^ 2 * ∑ j, u j * u j := by rw [hswap]; ring
  unfold eucNorm
  rw [show R * Real.sqrt (∑ j, u j * u j) = Real.sqrt (R ^ 2 * ∑ j, u j * u j) by
    rw [Real.sqrt_mul (sq_nonneg R), Real.sqrt_sq hR]]
  exact Real.sqrt_le_sqrt hsum

end Schur

/-! ## §2  Splitting an observable at the first site -/

/-- Splitting the sum over configurations at the first spin. -/
theorem sum_cons_config {L : ℕ} (F : (Fin (L + 1) → Fin 2) → ℝ) :
    ∑ σ : Fin (L + 1) → Fin 2, F σ
      = ∑ s : Fin 2, ∑ τ : Fin L → Fin 2, F (Fin.cons s τ) := by
  rw [← (Fin.consEquiv fun _ : Fin (L + 1) => Fin 2).sum_comp F, Fintype.sum_prod_type]
  rfl

/-- The decoupled kernel splits off its first bond. -/
theorem spatialKernel_cons (β : ℝ) {L : ℕ} (a s : Fin 2) (σ τ : Fin L → Fin 2) :
    spatialKernel β (Fin.cons a σ) (Fin.cons s τ)
      = z2Bond β a s * spatialKernel β σ τ := by
  unfold spatialKernel
  rw [Fin.prod_univ_succ]
  simp

/-- Acting is additive, and subtractive.  `act_add` is in the S block; the
difference is needed here and is the same two lines. -/
theorem act_sub {ι : Type*} [Fintype ι] (K : ι → ι → ℝ) (u z : ι → ℝ) :
    act K (fun i => u i - z i) = fun i => act K u i - act K z i := by
  funext i
  show (∑ j, K i j * (u j - z j)) = (∑ j, K i j * u j) - ∑ j, K i j * z j
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- Squaring an operator bound.  The induction runs on sums of squares, because
a square root in the inductive hypothesis is a square root in every step. -/
theorem sum_sq_le_of_eucNorm_le {ι : Type*} [Fintype ι] [Nonempty ι]
    {a b : ι → ℝ} {c : ℝ}
    (hc : 0 ≤ c) (h : eucNorm a ≤ c * eucNorm b) :
    ∑ i, a i * a i ≤ c ^ 2 * ∑ i, b i * b i := by
  have h1 := eucNorm_mul_self a
  have h2 := eucNorm_mul_self b
  nlinarith [eucNorm_nonneg a, eucNorm_nonneg b, h]

/-! ## §3  The induction

The one identity that makes it close is `tanh β · Z = D`: the rate lost on the
odd part is exactly the odd eigenvalue of a single bond, so the constant does
not degrade as sites are added. -/

/-- The row sum and the odd bond eigenvalue, in the combination the induction
uses.  `Z · tanh β = D`. -/
theorem tanh_mul_z2Norm (β : ℝ) :
    Real.tanh β * z2Norm β = Real.exp β - Real.exp (-β) := by
  rw [← spatial_rate_eq_tanh]
  exact div_mul_cancel₀ _ (ne_of_gt (z2Norm_pos β))

/-- **THE UNIFORM BOUND, squared.**  For every extent and every mean-zero
observable, the decoupled kernel contracts the fluctuation sector by
`tanh β · Zᴸ` --- a rate whose ratio to the Perron scale `Zᴸ` is `tanh β`, with
`L` nowhere in it. -/
theorem spatialKernel_fluct_sq (β : ℝ) :
    ∀ (L : ℕ) (u : (Fin L → Fin 2) → ℝ), (∑ σ, u σ = 0) →
      ∑ σ, act (spatialKernel β) u σ * act (spatialKernel β) u σ
        ≤ (Real.tanh β * (z2Norm β) ^ L) ^ 2 * ∑ σ, u σ * u σ := by
  intro L
  induction L with
  | zero =>
    intro u hu
    have hzero : ∀ σ : Fin 0 → Fin 2, u σ = 0 := by
      intro σ
      have hone : ∑ x : Fin 0 → Fin 2, u x = u σ :=
        Finset.sum_eq_single σ
          (fun b _ hb => absurd (Subsingleton.elim b σ) hb)
          (fun h => absurd (Finset.mem_univ σ) h)
      rw [← hone]
      exact hu
    have hact : ∀ σ : Fin 0 → Fin 2, act (spatialKernel β) u σ = 0 := fun σ =>
      Finset.sum_eq_zero fun τ _ => by rw [hzero τ, mul_zero]
    have hLHS : ∑ σ : Fin 0 → Fin 2,
        act (spatialKernel β) u σ * act (spatialKernel β) u σ = 0 :=
      Finset.sum_eq_zero fun σ _ => by rw [hact σ, mul_zero]
    have hRHS : ∑ σ : Fin 0 → Fin 2, u σ * u σ = 0 :=
      Finset.sum_eq_zero fun σ _ => by rw [hzero σ, mul_zero]
    rw [hLHS, hRHS, mul_zero]
  | succ L ih =>
    intro u hu
    have hZ : 0 < z2Norm β := z2Norm_pos β
    -- the two halves of the observable, and their even and odd combinations
    have hsplit : ∀ (a : Fin 2) (σ : Fin L → Fin 2),
        act (spatialKernel β) u (Fin.cons a σ)
          = z2Bond β a 0 * act (spatialKernel β) (fun τ => u (Fin.cons 0 τ)) σ
            + z2Bond β a 1 * act (spatialKernel β) (fun τ => u (Fin.cons 1 τ)) σ := by
      intro a σ
      show (∑ σ', spatialKernel β (Fin.cons a σ) σ' * u σ') = _
      rw [sum_cons_config (fun σ' => spatialKernel β (Fin.cons a σ) σ' * u σ')]
      have hstep : ∀ (s : Fin 2),
          (∑ τ : Fin L → Fin 2,
              spatialKernel β (Fin.cons a σ) (Fin.cons s τ) * u (Fin.cons s τ))
            = z2Bond β a s * act (spatialKernel β) (fun τ => u (Fin.cons s τ)) σ := by
        intro s
        show _ = z2Bond β a s * ∑ τ, spatialKernel β σ τ * u (Fin.cons s τ)
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun τ _ => by
          rw [spatialKernel_cons β a s σ τ]; ring
      rw [Fin.sum_univ_two, hstep 0, hstep 1]
    -- the even part still has mean zero; the odd part has nothing
    have hmean : ∑ τ : Fin L → Fin 2,
        (u (Fin.cons 0 τ) + u (Fin.cons 1 τ)) = 0 := by
      rw [Finset.sum_add_distrib, ← Fin.sum_univ_two
        (fun s => ∑ τ : Fin L → Fin 2, u (Fin.cons s τ))]
      rw [← sum_cons_config u]
      exact hu
    have hP := ih (fun τ => u (Fin.cons 0 τ) + u (Fin.cons 1 τ)) hmean
    have hM : ∑ τ : Fin L → Fin 2,
        act (spatialKernel β) (fun τ => u (Fin.cons 0 τ) - u (Fin.cons 1 τ)) τ
          * act (spatialKernel β) (fun τ => u (Fin.cons 0 τ) - u (Fin.cons 1 τ)) τ
        ≤ ((z2Norm β) ^ L) ^ 2
          * ∑ τ : Fin L → Fin 2,
              (u (Fin.cons 0 τ) - u (Fin.cons 1 τ)) * (u (Fin.cons 0 τ) - u (Fin.cons 1 τ)) :=
      sum_sq_le_of_eucNorm_le (by positivity)
        (norm_act_le_of_rowSum (fun i j => le_of_lt (spatialKernel_pos β i j))
          (spatialKernel_symm β) (sum_spatialKernel β) _)
    -- both sides, split at the first site
    rw [sum_cons_config (fun σ => act (spatialKernel β) u σ * act (spatialKernel β) u σ),
      sum_cons_config (fun σ => u σ * u σ), Fin.sum_univ_two, Fin.sum_univ_two]
    simp only [hsplit, z2Bond_same, z2Bond_ne (by decide : (0:Fin 2) ≠ 1),
      z2Bond_ne (by decide : (1:Fin 2) ≠ 0)]
    -- the even/odd rewriting, then the exact recombination
    rw [act_add (spatialKernel β)] at hP
    rw [act_sub (spatialKernel β)] at hM
    simp only [] at hP hM
    -- fold the two half-images and the four scalar sums
    set A0 := act (spatialKernel β) (fun τ => u (Fin.cons 0 τ)) with hA0
    set A1 := act (spatialKernel β) (fun τ => u (Fin.cons 1 τ)) with hA1
    set SP := ∑ x : Fin L → Fin 2, (A0 x + A1 x) * (A0 x + A1 x) with hSP
    set SM := ∑ x : Fin L → Fin 2, (A0 x - A1 x) * (A0 x - A1 x) with hSM
    set TP := ∑ τ : Fin L → Fin 2,
      (u (Fin.cons 0 τ) + u (Fin.cons 1 τ)) * (u (Fin.cons 0 τ) + u (Fin.cons 1 τ)) with hTP
    set TM := ∑ τ : Fin L → Fin 2,
      (u (Fin.cons 0 τ) - u (Fin.cons 1 τ)) * (u (Fin.cons 0 τ) - u (Fin.cons 1 τ)) with hTM
    -- the pointwise identity: the two spins recombine into even and odd parts
    have hkey : ∀ x : Fin L → Fin 2,
        (Real.exp β * A0 x + Real.exp (-β) * A1 x)
            * (Real.exp β * A0 x + Real.exp (-β) * A1 x)
          + (Real.exp (-β) * A0 x + Real.exp β * A1 x)
            * (Real.exp (-β) * A0 x + Real.exp β * A1 x)
        = (z2Norm β * z2Norm β * ((A0 x + A1 x) * (A0 x + A1 x))
            + (Real.exp β - Real.exp (-β)) * (Real.exp β - Real.exp (-β))
              * ((A0 x - A1 x) * (A0 x - A1 x))) / 2 := by
      intro x
      unfold z2Norm
      ring
    have hgoalL : (∑ x : Fin L → Fin 2,
          (Real.exp β * A0 x + Real.exp (-β) * A1 x)
            * (Real.exp β * A0 x + Real.exp (-β) * A1 x))
        + (∑ x : Fin L → Fin 2,
          (Real.exp (-β) * A0 x + Real.exp β * A1 x)
            * (Real.exp (-β) * A0 x + Real.exp β * A1 x))
        = (z2Norm β * z2Norm β * SP
            + (Real.exp β - Real.exp (-β)) * (Real.exp β - Real.exp (-β)) * SM) / 2 := by
      rw [← Finset.sum_add_distrib, Finset.sum_congr rfl fun x _ => hkey x,
        ← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hSP, hSM]
    have hgoalR : (∑ τ : Fin L → Fin 2, u (Fin.cons 0 τ) * u (Fin.cons 0 τ))
        + (∑ τ : Fin L → Fin 2, u (Fin.cons 1 τ) * u (Fin.cons 1 τ))
        = (TP + TM) / 2 := by
      rw [hTP, hTM, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.sum_div]
      exact Finset.sum_congr rfl fun τ _ => by ring
    rw [hgoalL, hgoalR]
    -- the exact recombination: `tanh β · Z = D`, so both coefficients agree
    have htz := tanh_mul_z2Norm β
    have hZL : (0:ℝ) ≤ (z2Norm β) ^ L := le_of_lt (pow_pos hZ L)
    have hsq : (Real.tanh β * z2Norm β ^ (L + 1)) ^ 2
        = ((Real.exp β - Real.exp (-β)) * (z2Norm β) ^ L) ^ 2 := by
      rw [← htz]
      ring
    rw [hsq]
    have h1 : z2Norm β * z2Norm β * SP
        ≤ z2Norm β * z2Norm β * ((Real.tanh β * z2Norm β ^ L) ^ 2 * TP) := by
      exact mul_le_mul_of_nonneg_left hP (by positivity)
    have h2 : (Real.exp β - Real.exp (-β)) * (Real.exp β - Real.exp (-β)) * SM
        ≤ (Real.exp β - Real.exp (-β)) * (Real.exp β - Real.exp (-β))
          * ((z2Norm β ^ L) ^ 2 * TM) := by
      exact mul_le_mul_of_nonneg_left hM (mul_self_nonneg _)
    have hexpand : z2Norm β * z2Norm β * ((Real.tanh β * z2Norm β ^ L) ^ 2 * TP)
        = ((Real.exp β - Real.exp (-β)) * (z2Norm β) ^ L) ^ 2 * TP := by
      rw [← htz]; ring
    have hexpand2 : (Real.exp β - Real.exp (-β)) * (Real.exp β - Real.exp (-β))
          * ((z2Norm β ^ L) ^ 2 * TM)
        = ((Real.exp β - Real.exp (-β)) * (z2Norm β) ^ L) ^ 2 * TM := by ring
    rw [hexpand] at h1
    rw [hexpand2] at h2
    linarith

/-- `tanh β ≥ 0` at nonnegative coupling, in the spelling this module needs. -/
theorem tanh_nonneg {β : ℝ} (hβ : 0 ≤ β) : 0 ≤ Real.tanh β := by
  rw [← spatial_rate_eq_tanh]
  exact div_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr (by linarith)))
    (le_of_lt (z2Norm_pos β))

/-- **THE UNIFORM OPERATOR BOUND.**  At every extent, the decoupled kernel maps
the fluctuation sector into itself with norm at most `tanh β · Zᴸ`.  The ratio
to the Perron scale `Zᴸ` is `tanh β`, and `L` does not appear in it. -/
theorem spatialKernel_fluct_bound {β : ℝ} (hβ : 0 ≤ β) (L : ℕ)
    (u : (Fin L → Fin 2) → ℝ) (hu : ∑ σ, u σ = 0) :
    eucNorm (act (spatialKernel β) u)
      ≤ Real.tanh β * (z2Norm β) ^ L * eucNorm u := by
  have hc : 0 ≤ Real.tanh β * (z2Norm β) ^ L :=
    mul_nonneg (tanh_nonneg hβ) (le_of_lt (pow_pos (z2Norm_pos β) L))
  have hsq := spatialKernel_fluct_sq β L u hu
  unfold eucNorm
  rw [show Real.tanh β * (z2Norm β) ^ L * Real.sqrt (∑ σ, u σ * u σ)
      = Real.sqrt ((Real.tanh β * (z2Norm β) ^ L) ^ 2 * ∑ σ, u σ * u σ) by
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hc]]
  exact Real.sqrt_le_sqrt hsq

/-! ## §4  From the operator bound to the modulus

`specGap` is the GREATEST norm ratio on the fluctuation sector (`specGap_isGreatest`),
so an upper bound for the ratios is an upper bound for `specGap`.  That is the
only place the S block is used, and it is used as a bound, not as a spectral
decomposition. -/

/-- The constant observable is the Perron vector of the decoupled kernel, with
eigenvalue the row sum `Zᴸ`. -/
theorem spatialKernel_perron (β : ℝ) {L : ℕ} :
    ∀ σ : Fin L → Fin 2,
      ∑ τ, spatialKernel β σ τ * (1 : ℝ) = (z2Norm β) ^ L * (1 : ℝ) := by
  intro σ
  simpa using sum_spatialKernel β σ

/-- **THE MODULUS DOES NOT DEPEND ON THE EXTENT.**  `specGap ≤ tanh β · Zᴸ`, so
`specRatio ≤ tanh β`, at every `L`.  This is the statement the gap paper
declined to fake and the S block could only give one extent at a time. -/
theorem spatialKernel_specGap_le {β : ℝ} (hβ : 0 ≤ β) {L : ℕ}
    {σ₀ σ₁ : Fin L → Fin 2} (hne : σ₀ ≠ σ₁) :
    specGap (spatialKernel_symm β (L := L)) ((z2Norm β) ^ L)
      ≤ Real.tanh β * (z2Norm β) ^ L := by
  obtain ⟨⟨u, hperp, hune, hval⟩, -⟩ :=
    specGap_isGreatest
      (K := (spatialKernel β : (Fin L → Fin 2) → (Fin L → Fin 2) → ℝ))
      (fun i j => spatialKernel_pos β i j)
      (spatialKernel_symm β) (v := fun _ => (1:ℝ)) (fun _ => one_pos)
      (spatialKernel_perron β (L := L)) (i₀ := σ₀) (i₁ := σ₁) hne
  have hmean : ∑ σ, u σ = 0 := by
    rw [← hperp]
    exact Finset.sum_congr rfl fun σ _ => (one_mul _).symm
  have hpos : 0 < eucNorm u := lt_of_le_of_ne (eucNorm_nonneg u) (Ne.symm hune)
  rw [hval, div_le_iff₀ hpos]
  exact spatialKernel_fluct_bound hβ L u hmean

/-! ## §5  Sharpness: the extent paper's observable attains it

The bound above is an inequality.  The companion extent paper already exhibits
an observable whose eigenvalue is `D · Z^{L-1}`, independent of `L`; all that is
missing is that it is a fluctuation observable, and that the ratio it realises
is exactly the bound. -/

/-- The single-site sign observable has mean zero: half the configurations
carry `+1` and half `-1`, and the product over sites sees the cancelling factor.
-/
theorem sum_siteSign {L : ℕ} (i : Fin L) :
    ∑ τ : Fin L → Fin 2, siteSign i τ = 0 := by
  have hrw : ∀ τ : Fin L → Fin 2,
      siteSign i τ = ∏ j, (if j = i then z2Sign (τ j) 0 else 1) := by
    intro τ
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), if_pos rfl,
      Finset.prod_congr rfl (fun j hj => if_neg (Finset.ne_of_mem_erase hj)),
      Finset.prod_const_one, mul_one]
    rfl
  rw [Finset.sum_congr rfl fun τ _ => hrw τ,
    sum_prod_config (fun j t => if j = i then z2Sign t 0 else 1)]
  refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
  simp only [if_pos rfl]
  rw [Fin.sum_univ_two]
  unfold z2Sign
  norm_num

/-- The sign observable is not the zero observable. -/
theorem eucNorm_siteSign_ne_zero {L : ℕ} (i : Fin L) :
    eucNorm (siteSign i) ≠ 0 := by
  refine ne_of_gt (Real.sqrt_pos.mpr ?_)
  refine Finset.sum_pos (fun τ _ => ?_) Finset.univ_nonempty
  unfold siteSign z2Sign
  by_cases h : τ i = 0 <;> simp [h]

/-- **THE RATE IS EXACTLY `tanh β`, at every extent.**  The inequality of §4 is
attained, by the single-site observable the extent paper already built.  So this
is not a bound that happens not to degrade; it is the number. -/
theorem spatialKernel_specGap_eq {β : ℝ} (hβ : 0 ≤ β) (M : ℕ) :
    specGap (spatialKernel_symm β (L := M + 1)) ((z2Norm β) ^ (M + 1))
      = Real.tanh β * (z2Norm β) ^ (M + 1) := by
  have hZ : (0:ℝ) < z2Norm β := z2Norm_pos β
  have hne : ((fun _ => (0 : Fin 2)) : Fin (M + 1) → Fin 2)
      ≠ ((fun _ => (1 : Fin 2)) : Fin (M + 1) → Fin 2) := by
    intro h
    have hc := congrFun h (0 : Fin (M + 1))
    exact absurd hc (by decide)
  refine le_antisymm (spatialKernel_specGap_le hβ hne) ?_
  -- the attaining observable, and the value it realises
  set i : Fin (M + 1) := 0 with hi
  have hact : act (spatialKernel β) (siteSign i)
      = fun σ => ((Real.exp β - Real.exp (-β)) * (z2Norm β) ^ M) * siteSign i σ := by
    funext σ
    simpa using spatialKernel_siteSign β i σ
  have hmem : Real.tanh β * (z2Norm β) ^ (M + 1)
      ∈ {r : ℝ | ∃ u : (Fin (M + 1) → Fin 2) → ℝ,
          (∑ x, (1:ℝ) * u x = 0) ∧ eucNorm u ≠ 0
            ∧ r = eucNorm (act (spatialKernel β) u) / eucNorm u} := by
    refine ⟨siteSign i, ?_, eucNorm_siteSign_ne_zero i, ?_⟩
    · rw [Finset.sum_congr rfl fun x _ => one_mul (siteSign i x)]
      exact sum_siteSign i
    · have hDnn : (0:ℝ) ≤ (Real.exp β - Real.exp (-β)) * (z2Norm β) ^ M :=
        mul_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr (by linarith)))
          (le_of_lt (pow_pos hZ M))
      rw [hact, eucNorm_smul, abs_of_nonneg hDnn, mul_comm,
        mul_div_assoc, div_self (eucNorm_siteSign_ne_zero i), mul_one,
        ← tanh_mul_z2Norm β]
      ring
  exact (specGap_isGreatest
    (K := (spatialKernel β : (Fin (M + 1) → Fin 2) → (Fin (M + 1) → Fin 2) → ℝ))
    (fun a b => spatialKernel_pos β a b) (spatialKernel_symm β)
    (v := fun _ => (1:ℝ)) (fun _ => one_pos)
    (spatialKernel_perron β (L := M + 1)) hne).2 hmem

/-! ## §6  The same statement for the measure the S block bounds

The S-block endpoint is phrased for `symWeighted w β`.  At constant weight that
IS the decoupled kernel, so the uniform modulus transports, and then the two
compose into a rate with no `L` in it. -/

/-- At constant source weight the symmetrised kernel is the decoupled one. -/
theorem symWeighted_one (β : ℝ) {L : ℕ} :
    symWeighted (fun _ => (1:ℝ)) β
      = (spatialKernel β : (Fin L → Fin 2) → (Fin L → Fin 2) → ℝ) := by
  funext σ τ
  show Real.sqrt 1 * spatialKernel β σ τ * Real.sqrt 1 = _
  rw [Real.sqrt_one, one_mul, mul_one]

/-- **THE RATE, uniform in the extent.**  `specRatio ≤ tanh β`, for the kernel
the S-block endpoint actually uses, at every `L`. -/
theorem symWeighted_one_specRatio_le {β : ℝ} (hβ : 0 ≤ β) {L : ℕ}
    {σ₀ σ₁ : Fin L → Fin 2} (hne : σ₀ ≠ σ₁) :
    specRatio (symWeighted_symm (L := L) (fun _ => (1:ℝ)) β) ((z2Norm β) ^ L)
      ≤ Real.tanh β := by
  have hZL : (0:ℝ) < (z2Norm β) ^ L := pow_pos (z2Norm_pos β) L
  obtain ⟨⟨u, hperp, hune, hval⟩, -⟩ :=
    specGap_isGreatest
      (K := (symWeighted (fun _ => (1:ℝ)) β : (Fin L → Fin 2) → (Fin L → Fin 2) → ℝ))
      (fun i j => symWeighted_pos (fun _ => one_pos) β i j)
      (symWeighted_symm (L := L) (fun _ => (1:ℝ)) β) (v := fun _ => (1:ℝ)) (fun _ => one_pos)
      (by rw [symWeighted_one β (L := L)]; exact spatialKernel_perron β (L := L))
      (i₀ := σ₀) (i₁ := σ₁) hne
  have hmean : ∑ σ, u σ = 0 := by
    rw [← hperp]
    exact Finset.sum_congr rfl fun σ _ => (one_mul _).symm
  have hnpos : 0 < eucNorm u := lt_of_le_of_ne (eucNorm_nonneg u) (Ne.symm hune)
  have hop : eucNorm (act (symWeighted (fun _ => (1:ℝ)) β) u)
      ≤ Real.tanh β * (z2Norm β) ^ L * eucNorm u := by
    rw [symWeighted_one β (L := L)]
    exact spatialKernel_fluct_bound hβ L u hmean
  have hgap : specGap (symWeighted_symm (L := L) (fun _ => (1:ℝ)) β) ((z2Norm β) ^ L)
      ≤ Real.tanh β * (z2Norm β) ^ L := by
    rw [hval, div_le_iff₀ hnpos]
    exact hop
  unfold specRatio
  rw [div_le_iff₀ hZL]
  linarith

/-! ## §7  An extent-independent rate --- which is NOT a volume limit

The S-block endpoint bounds the normalised two-point function by
`C · specRatio ^ N` past one threshold serving every observable.  Its rate
depended on the extent, and the S block said so.  At constant source weight it
no longer does. -/

/-- **Finite-volume decay with an extent-independent exponential rate.**  At
constant source weight, the normalised Gibbs two-point function of a fluctuation
observable is bounded by `C · (tanh β) ^ N` past a threshold, and `tanh β` does
not depend on `L`.

**The constant and the threshold are NOT asserted uniform in `L`**: the extent is
fixed before either is chosen, so both may in principle diverge with it.  No
infinite-volume statement and no clustering theorem is claimed here --- §8 is
where the whole bound, and not merely its rate, becomes uniform. -/
theorem gibbs_decay_extent_free_rate {β : ℝ} (hβ : 0 ≤ β) {L : ℕ}
    {σ₀ σ₁ : Fin L → Fin 2} (hne : σ₀ ≠ σ₁) :
    ∃ N₀ : ℕ, ∀ A : (Fin L → Fin 2) → ℝ,
      (∑ σ, (1:ℝ) * dress (fun _ => (1:ℝ)) A σ = 0) →
        ∃ C > 0, ∀ N, N₀ ≤ N →
          |gibbsCorr (fun _ => (1:ℝ)) β N A A| ≤ C * Real.tanh β ^ N := by
  obtain ⟨N₀, h⟩ := gibbsCorr_decay_uniform_threshold (w := fun _ => (1:ℝ))
    (fun _ => one_pos) β (v := fun _ => (1:ℝ)) (fun _ => one_pos)
    (lam := (z2Norm β) ^ L)
    (by rw [symWeighted_one β (L := L)]; exact spatialKernel_perron β (L := L))
  refine ⟨N₀, fun A hperp => ?_⟩
  obtain ⟨C, hC, hb⟩ := h A hperp
  refine ⟨C, hC, fun N hN => ?_⟩
  refine le_trans (hb N hN) (mul_le_mul_of_nonneg_left ?_ (le_of_lt hC))
  refine pow_le_pow_left₀ ?_ (symWeighted_one_specRatio_le hβ hne) N
  exact specRatio_nonneg (fun i j => symWeighted_pos (fun _ => one_pos) β i j)
    (symWeighted_symm (L := L) (fun _ => (1:ℝ)) β) (fun _ => one_pos)
    (by rw [symWeighted_one β (L := L)]; exact spatialKernel_perron β (L := L))

/-! ## §8  Uniform in the extent, and not only in the rate

`gibbs_decay_extent_free_rate` gives a rate with no `L` in it, but its constant
and its threshold are produced by the S-block endpoint and are **not** claimed
uniform in the extent.  A rate alone does not survive a volume limit: a bound
`C(L) · ρ^N` with `C(L) → ∞` says nothing in the limit however small `ρ` is.

At constant source weight everything in sight is explicit, so the uniform bound
can simply be computed instead of composed.  The dressed constant observable IS
the Perron vector, the partition function is exactly `2ᴸ · Z^{LN}`, and what
comes out is a bound valid **from `N = 0`**, with constant the mean square of
the observable in the uniform measure --- at most `1` for any observable bounded
by `1`, at every extent. -/

section Uniform

variable {L : ℕ}

/-- Dressing by the constant weight is the identity. -/
theorem dress_one (A : (Fin L → Fin 2) → ℝ) :
    dress (fun _ => (1:ℝ)) A = A := by
  funext σ
  show Real.sqrt 1 * A σ = A σ
  rw [Real.sqrt_one, one_mul]

/-- The fluctuation sector is invariant: the decoupled kernel preserves mean
zero, because its columns sum to the same `Zᴸ` its rows do. -/
theorem sum_act_eq_zero (β : ℝ) {u : (Fin L → Fin 2) → ℝ} (hu : ∑ σ, u σ = 0) :
    ∑ σ, act (spatialKernel β) u σ = 0 := by
  have hcol : ∀ τ : Fin L → Fin 2,
      ∑ σ, spatialKernel β σ τ = (z2Norm β) ^ L := by
    intro τ
    rw [← sum_spatialKernel β τ]
    exact Finset.sum_congr rfl fun σ _ => spatialKernel_symm β σ τ
  calc ∑ σ, act (spatialKernel β) u σ
      = ∑ σ, ∑ τ, spatialKernel β σ τ * u τ := rfl
    _ = ∑ τ, ∑ σ, spatialKernel β σ τ * u τ := Finset.sum_comm
    _ = ∑ τ, (∑ σ, spatialKernel β σ τ) * u τ :=
        Finset.sum_congr rfl fun τ _ => by rw [Finset.sum_mul]
    _ = (z2Norm β) ^ L * ∑ τ, u τ := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun τ _ => by rw [hcol τ]
    _ = 0 := by rw [hu, mul_zero]

/-- Iterating the uniform bound.  The rate is a power; nothing accumulates. -/
theorem iterate_fluct_bound {β : ℝ} (hβ : 0 ≤ β) (N : ℕ) :
    ∀ u : (Fin L → Fin 2) → ℝ, (∑ σ, u σ = 0) →
      eucNorm ((act (spatialKernel β))^[N] u)
        ≤ (Real.tanh β * (z2Norm β) ^ L) ^ N * eucNorm u := by
  induction N with
  | zero => intro u _; simpa using le_refl (eucNorm u)
  | succ N ih =>
    intro u hu
    rw [Function.iterate_succ_apply]
    calc eucNorm ((act (spatialKernel β))^[N] (act (spatialKernel β) u))
        ≤ (Real.tanh β * (z2Norm β) ^ L) ^ N
            * eucNorm (act (spatialKernel β) u) :=
          ih _ (sum_act_eq_zero β hu)
      _ ≤ (Real.tanh β * (z2Norm β) ^ L) ^ N
            * (Real.tanh β * (z2Norm β) ^ L * eucNorm u) :=
          mul_le_mul_of_nonneg_left (spatialKernel_fluct_bound hβ L u hu)
            (pow_nonneg (mul_nonneg (tanh_nonneg hβ)
              (le_of_lt (pow_pos (z2Norm_pos β) L))) N)
      _ = (Real.tanh β * (z2Norm β) ^ L) ^ (N + 1) * eucNorm u := by ring

/-- The partition function at constant weight, exactly. -/
theorem gibbsPartition_one (β : ℝ) (N : ℕ) :
    gibbsPartition (fun _ : Fin L → Fin 2 => (1:ℝ)) β N
      = 2 ^ L * ((z2Norm β) ^ L) ^ N := by
  have hiter : ∀ n : ℕ, (act (spatialKernel β))^[n] (fun _ => (1:ℝ))
      = fun _ : Fin L → Fin 2 => ((z2Norm β) ^ L) ^ n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ihn =>
      rw [Function.iterate_succ_apply', ihn]
      funext σ
      unfold act
      rw [← Finset.sum_mul, sum_spatialKernel β σ]
      ring
  rw [gibbsPartition_eq_iterate (fun _ => one_pos) β N, symWeighted_one β (L := L),
    dress_one]
  rw [hiter N]
  simp [Finset.sum_const, Finset.card_univ, Fintype.card_fun]

/-- **UNIFORM IN THE EXTENT, not only in the rate.**  At constant source weight,
for every mean-zero observable and **every** `N` --- no threshold ---
\[
  |\mathbb{E}[A(X_0)A(X_N)]| \le \langle A^2\rangle \cdot (\tanh β)^N ,
\]
where `⟨A²⟩` is the mean square of `A` in the uniform measure.  For an
observable bounded by `1` the constant is at most `1`, **at every extent**, so
here the whole bound and not merely its rate is uniform in `L`. -/
theorem gibbsCorr_one_uniform_bound {β : ℝ} (hβ : 0 ≤ β) (N : ℕ)
    {A : (Fin L → Fin 2) → ℝ} (hA : ∑ σ, A σ = 0) :
    |gibbsCorr (fun _ => (1:ℝ)) β N A A|
      ≤ ((∑ σ, A σ * A σ) / 2 ^ L) * Real.tanh β ^ N := by
  have hZ : (0:ℝ) < (z2Norm β) ^ L := pow_pos (z2Norm_pos β) L
  have hcard : (0:ℝ) < 2 ^ L := by positivity
  have hden : gibbsPartition (fun _ => (1:ℝ)) β N = 2 ^ L * ((z2Norm β) ^ L) ^ N :=
    gibbsPartition_one β N
  have hnum : |gibbsPathSum (fun _ => (1:ℝ)) β N A A|
      ≤ (Real.tanh β * (z2Norm β) ^ L) ^ N * (eucNorm A * eucNorm A) := by
    rw [gibbsPathSum_eq_iterate (fun _ => one_pos) β N A A, symWeighted_one β (L := L),
      dress_one]
    calc |∑ σ, (act (spatialKernel β))^[N] A σ * A σ|
        ≤ eucNorm ((act (spatialKernel β))^[N] A) * eucNorm A := abs_sum_mul_le _ _
      _ ≤ ((Real.tanh β * (z2Norm β) ^ L) ^ N * eucNorm A) * eucNorm A :=
          mul_le_mul_of_nonneg_right (iterate_fluct_bound hβ N A hA) (eucNorm_nonneg A)
      _ = (Real.tanh β * (z2Norm β) ^ L) ^ N * (eucNorm A * eucNorm A) := by ring
  have hZpos : (0:ℝ) < 2 ^ L * ((z2Norm β) ^ L) ^ N :=
    mul_pos hcard (pow_pos hZ N)
  unfold gibbsCorr
  rw [hden, abs_div, abs_of_pos hZpos, div_le_iff₀ hZpos]
  calc |gibbsPathSum (fun _ => (1:ℝ)) β N A A|
      ≤ (Real.tanh β * (z2Norm β) ^ L) ^ N * (eucNorm A * eucNorm A) := hnum
    _ = (Real.tanh β * (z2Norm β) ^ L) ^ N * (∑ σ, A σ * A σ) := by
        rw [eucNorm_mul_self A]
    _ = (∑ σ, A σ * A σ) / 2 ^ L * Real.tanh β ^ N
          * (2 ^ L * ((z2Norm β) ^ L) ^ N) := by
        rw [mul_pow]
        field_simp

/-- The number of configurations, as a real. -/
theorem card_config_real :
    ((Finset.univ : Finset (Fin L → Fin 2)).card : ℝ) = 2 ^ L := by
  rw [Finset.card_univ, Fintype.card_fun]
  simp

/-- **The covariance form, for an ARBITRARY observable.**  Centring an
observable in the uniform measure discharges the mean-zero hypothesis, so the
bound applies to every `A` with its variance as the constant. -/
theorem gibbsCov_one_uniform_bound {β : ℝ} (hβ : 0 ≤ β) (N : ℕ)
    (A : (Fin L → Fin 2) → ℝ) :
    |gibbsCorr (fun _ => (1:ℝ)) β N
        (fun σ => A σ - (∑ τ, A τ) / 2 ^ L) (fun σ => A σ - (∑ τ, A τ) / 2 ^ L)|
      ≤ ((∑ σ, (A σ - (∑ τ, A τ) / 2 ^ L) * (A σ - (∑ τ, A τ) / 2 ^ L)) / 2 ^ L)
        * Real.tanh β ^ N := by
  refine gibbsCorr_one_uniform_bound hβ N ?_
  have hc : (0:ℝ) < 2 ^ L := by positivity
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, card_config_real]
  field_simp
  ring

/-- **THE ENDPOINT WITH NO `L` ON THE RIGHT AT ALL.**  For an observable of mean
zero bounded by `1`, the normalised two-point function is below `(tanh β)^N` --
every symbol on the right-hand side is free of the extent, and there is no
threshold. -/
theorem gibbsCorr_one_le_of_bounded {β : ℝ} (hβ : 0 ≤ β) (N : ℕ)
    {A : (Fin L → Fin 2) → ℝ} (hA : ∑ σ, A σ = 0) (hb : ∀ σ, |A σ| ≤ 1) :
    |gibbsCorr (fun _ => (1:ℝ)) β N A A| ≤ Real.tanh β ^ N := by
  have hc : (0:ℝ) < 2 ^ L := by positivity
  have hsq : (∑ σ, A σ * A σ) ≤ 2 ^ L := by
    calc (∑ σ, A σ * A σ) ≤ ∑ _σ : Fin L → Fin 2, (1:ℝ) := by
          refine Finset.sum_le_sum fun σ _ => ?_
          have := hb σ
          nlinarith [abs_nonneg (A σ), sq_abs (A σ), abs_mul_abs_self (A σ)]
      _ = 2 ^ L := by
          rw [Finset.sum_const, nsmul_eq_mul, card_config_real, mul_one]
  calc |gibbsCorr (fun _ => (1:ℝ)) β N A A|
      ≤ ((∑ σ, A σ * A σ) / 2 ^ L) * Real.tanh β ^ N :=
        gibbsCorr_one_uniform_bound hβ N hA
    _ ≤ 1 * Real.tanh β ^ N :=
        mul_le_mul_of_nonneg_right (by rw [div_le_one hc]; exact hsq)
          (pow_nonneg (tanh_nonneg hβ) N)
    _ = Real.tanh β ^ N := one_mul _

end Uniform

end YangMills.OS
