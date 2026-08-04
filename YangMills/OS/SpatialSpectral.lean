import YangMills.OS.SpatialGibbs
import Mathlib.Analysis.Matrix.Spectrum

/-!
# The S block — the operator bound, and what it does and does not give

Two companion papers were left carrying the same debt from opposite sides.  The
gap paper proved that every eigenvalue other than the Perron eigenvalue is
*strictly* smaller in modulus, with **no modulus of separation**.  The bridge
paper proved that the Gibbs correlations of the spatial system are matrix
elements of a self-adjoint transfer operator, and obtained geometric decay only
**under an explicit contraction hypothesis it did not discharge**.  The missing
step is the same in both cases: a strict inequality among finitely many
eigenvalues is not an operator-norm bound, and turning one into the other needs
the spectral decomposition.

This module supplies it, and spends the result on both debts at once.

## What is proved

* `specGap` — the number.  For a strictly positive symmetric kernel with Perron
  data `(Ω, λ)`, it is the largest `|μ|` over the eigenvalues `μ ≠ λ`, and
  `specGap_lt` proves `specGap < λ`.  This is the modulus the gap paper did not
  provide.
* `norm_act_le_specGap` — the operator bound.  For every observable orthogonal
  to the vacuum, `‖K u‖ ≤ specGap · ‖u‖`.  This is exactly the hypothesis the
  bridge paper carried.
* `specRatio` / `specRatio_lt_one` — the rate that is actually below one.
  `specGap < λ` is **not** `specGap < 1`: the kernel is unnormalised, so both are
  typically far above one and `specGap ^ N` GROWS.  The rate below one is the
  relative one, `specRatio = specGap / λ`.
* `gibbs_pathSum_bound_unconditional` — the bridge module's bound with its
  hypothesis removed.  Its rate is `specGap`, so on its own it bounds the GROWTH
  of the fluctuation contribution; it does not exhibit decay.
* `gibbs_pathSum_relative_decay` — the decay statement for the NUMERATOR:
  suppression by `specRatio ^ N` **relative to the Perron scale** `λ ^ N`.
* `quadForm_split` / `quadForm_lower` — the DENOMINATOR.  Splitting the dressed
  constant observable along the Perron direction kills both cross terms by
  symmetry alone, and bounds the partition function below by
  `c² · λ ^ N − specGap ^ N · ‖u‖²`.  No eigenbasis index is identified.
* `gibbsCorr_decay_uniform_threshold` — the composed endpoint: the
  **normalised** two-point function is bounded by `C · specRatio ^ N`, at a
  fixed extent, past **one threshold that serves every observable at once**.
  The threshold is characterised by an inequality, not computed, and it is
  built from the dressed CONSTANT observable, so it never sees `A`.
  `gibbsCorr_decay_fixed_extent` is its consequence in the familiar order.
* `exists_attaining_fluctuation` — the bound of §6 is **sharp**: whenever the
  state space has two distinct points, some nonzero fluctuation observable
  attains it.  The proof splits at `specGap = 0`, where the maximising index
  need not supply a non-Perron eigenvector.
* `specGap_isGreatest` — the same, said about an object: the set of norm
  ratios on the fluctuation sector has a greatest element, equal to `specGap`.

## The one step that does not come from the inequalities

Eigenvectors whose eigenvalue is exactly `λ` must be shown to be invisible to a
fluctuation observable.  That is geometric simplicity of the Perron eigenvalue —
proved in the companion Perron paper for an arbitrary eigenvector, not merely a
positive one — and it is what makes the sum over the spectrum drop its top term
rather than merely bound it.

## What is NOT proved, and is not claimed

An earlier version of this module asserted here that turning the numerator bound
into a statement about the **normalised** expectation requires identifying the
index of the top eigenvalue.  **That was wrong**, and §8 now proves the
denominator bound with no index at all.  The sentence is kept, in its corrected
form, because a false claim about what is *hard* discourages work in a way a
false claim about what is proved does not.

The same held, until §11, for the sharpness of `specGap`.  It no longer does:
the bound, its attainment, and the `IsGreatest` statement about the set of
norm ratios are all proved.  What is still not done is a `Submodule` /
`ContinuousLinearMap` / `‖·‖` interface for the restricted operator; that would
be a convenience for later reuse, not additional content, and this sentence
says which of the two we did.

`specRatio` **depends on the extent**.  Nothing here bounds it away from `1`
uniformly in the size of the configuration space, and the numerical evidence
recorded in the gap paper is that it approaches `1` with the extent outside the
disordered region.  A geometric bound whose rate tends to `1` is empty in the
limit, and no claim to the contrary is made or implied.  So the endpoint is
**not clustering**: clustering is a statement that survives the infinite-volume
limit, and this one does not.  In particular this module does **not** produce a
mass gap, and reflection positivity remains untouched.

Nothing here concerns `SU(N)`, the continuum limit, or the Clay problem.

Oracle target: `[propext, Classical.choice, Quot.sound]`.  No sorry, no axioms.
-/

namespace YangMills.OS

set_option linter.unusedSectionVars false

open scoped InnerProductSpace
open Matrix

section Spectral

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-! ## §1  The kernel as a Hermitian matrix -/

/-- A symmetric real kernel is a Hermitian matrix.  Over `ℝ` the conjugate
transpose is the transpose, so this is symmetry and nothing more. -/
theorem isHermitian_of_symm {K : ι → ι → ℝ} (hK : ∀ i j, K i j = K j i) :
    (Matrix.of K).IsHermitian := by
  ext i j
  exact hK j i

/-- The action of the kernel, in the `mulVec` spelling mathlib's spectral theory
uses.  It is the `act` of the bridge module, unfolded. -/
theorem mulVec_eq_act (K : ι → ι → ℝ) (u : ι → ℝ) :
    Matrix.mulVec (Matrix.of K) u = act K u := by
  funext i
  simp [Matrix.mulVec, dotProduct, act]

/-! ## §2  Coordinates in the eigenbasis

`emb` is the identification of an observable with a vector of the Euclidean
space mathlib's spectral theorem lives on.  The two lemmas after it are the only
facts about that identification the rest of the module uses. -/

/-- An observable, viewed in Euclidean space. -/
noncomputable def emb (v : ι → ℝ) : EuclideanSpace ℝ ι := WithLp.toLp 2 v

@[simp]
theorem emb_ofLp (v : ι → ℝ) : (emb v).ofLp = v := rfl

theorem inner_emb (u v : ι → ℝ) : ⟪emb u, emb v⟫_ℝ = ∑ i, u i * v i := by
  rw [PiLp.inner_apply]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem norm_emb (v : ι → ℝ) : ‖emb v‖ = eucNorm v := by
  rw [EuclideanSpace.norm_eq]
  unfold eucNorm
  congr 1
  exact Finset.sum_congr rfl fun i _ => by
    rw [show (emb v).ofLp i = v i from rfl, Real.norm_eq_abs, sq_abs, pow_two]

/-! ## §3  The spectral data of a symmetric positive kernel -/

variable {K : ι → ι → ℝ}

/-- The eigenvalues of the kernel, indexed by the configuration type. -/
noncomputable def specEigen (hK : ∀ i j, K i j = K j i) : ι → ℝ :=
  (isHermitian_of_symm hK).eigenvalues

/-- An orthonormal basis of eigenvectors. -/
noncomputable def specBasis (hK : ∀ i j, K i j = K j i) :
    OrthonormalBasis ι ℝ (EuclideanSpace ℝ ι) :=
  (isHermitian_of_symm hK).eigenvectorBasis

/-- Each basis vector is an eigenvector, written as an eigen-equation of the
kernel in exactly the form the companion papers consume. -/
theorem specBasis_eigen (hK : ∀ i j, K i j = K j i) (j : ι) :
    ∀ i, ∑ k, K i k * (specBasis hK j).ofLp k
      = specEigen hK j * (specBasis hK j).ofLp i := by
  intro i
  have h := congrFun ((isHermitian_of_symm hK).mulVec_eigenvectorBasis j) i
  simpa [Matrix.mulVec, dotProduct, specBasis, specEigen] using h

/-- The pairing of a basis vector with an observable, as a plain sum. -/
theorem inner_basis_eq_sum (hK : ∀ i j, K i j = K j i) (j : ι) (u : ι → ℝ) :
    ⟪specBasis hK j, emb u⟫_ℝ = ∑ i, (specBasis hK j).ofLp i * u i := by
  rw [PiLp.inner_apply]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- A basis vector is not the zero observable. -/
theorem specBasis_ne_zero (hK : ∀ i j, K i j = K j i) (j : ι) :
    ∃ i, (specBasis hK j).ofLp i ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  have hz : (specBasis hK j) = 0 := by
    refine PiLp.ext fun i => ?_
    simpa using hcon i
  have hone : ‖(specBasis hK j)‖ = 1 := (specBasis hK).orthonormal.1 j
  rw [hz, norm_zero] at hone
  exact zero_ne_one hone

/-! ## §4  The modulus the gap paper did not provide -/

/-- **The subdominant spectral modulus.**  The largest `|μ|` over the
eigenvalues different from the Perron eigenvalue.

This is NOT the quantity usually called a spectral *gap*: that would be
`lam - specGap`, or `1 - specRatio` after normalising.  The identifier is kept
for continuity with the companion papers; this sentence, not the name, is the
statement.

Eigenvalues equal to `lam` contribute `0`, which is legitimate precisely because
§5 shows they are invisible to a fluctuation observable. -/
noncomputable def specGap (hK : ∀ i j, K i j = K j i) (lam : ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun j => if specEigen hK j = lam then 0 else |specEigen hK j|)

theorem specGap_nonneg (hK : ∀ i j, K i j = K j i) (lam : ℝ) :
    0 ≤ specGap hK lam := by
  obtain ⟨j⟩ := ‹Nonempty ι›
  refine le_trans ?_ (Finset.le_sup' _ (Finset.mem_univ j))
  by_cases h : specEigen hK j = lam <;> simp [h, abs_nonneg]

/-- **`specGap < lam`.**  This is the quantitative statement the gap paper
declined to fake: the separation now has a modulus, at fixed extent. -/
theorem specGap_lt (hpos : ∀ i j, 0 < K i j) (hK : ∀ i j, K i j = K j i)
    {v : ι → ℝ} (hv : ∀ i, 0 < v i) {lam : ℝ}
    (hvE : ∀ i, ∑ j, K i j * v j = lam * v i) :
    specGap hK lam < lam := by
  have hlam : 0 < lam := eigenvalue_pos hpos hv hvE
  rw [specGap, Finset.sup'_lt_iff]
  intro j _
  by_cases h : specEigen hK j = lam
  · simpa [h] using hlam
  · obtain ⟨i₁, hi₁⟩ := specBasis_ne_zero hK j
    simpa [h] using
      abs_lt_of_ne_perron hpos hv hvE hi₁ (specBasis_eigen hK j) h

/-! ## §5  Eigenvectors at the top are invisible to fluctuations

This is the step that does not follow from the inequalities.  Geometric
simplicity says the `lam`-eigenspace is spanned by the Perron vector; hence an
observable orthogonal to that vector has no component along any eigenvector at
the top of the spectrum, and the corresponding term of the sum vanishes rather
than merely being bounded. -/

theorem inner_specBasis_eq_zero_of_top (hpos : ∀ i j, 0 < K i j)
    (hK : ∀ i j, K i j = K j i) {v : ι → ℝ} (hv : ∀ i, 0 < v i) {lam : ℝ}
    (hvE : ∀ i, ∑ j, K i j * v j = lam * v i)
    {u : ι → ℝ} (hperp : ∑ i, v i * u i = 0) {j : ι}
    (htop : specEigen hK j = lam) :
    ⟪specBasis hK j, emb u⟫_ℝ = 0 := by
  obtain ⟨c, hc⟩ :=
    eigenvector_eq_smul_of_pos hpos hv hvE (htop ▸ specBasis_eigen hK j)
  rw [inner_basis_eq_sum hK j u]
  have hrw : ∀ i, (specBasis hK j).ofLp i * u i = c * (v i * u i) := by
    intro i
    rw [hc i]
    ring
  rw [Finset.sum_congr rfl fun i _ => hrw i, ← Finset.mul_sum, hperp, mul_zero]

/-! ## §6  The operator bound -/

/-- The coordinate of an image in the eigenbasis is scaled by the eigenvalue. -/
theorem inner_specBasis_act (hK : ∀ i j, K i j = K j i) (u : ι → ℝ) (j : ι) :
    ⟪specBasis hK j, emb (act K u)⟫_ℝ
      = specEigen hK j * ⟪specBasis hK j, emb u⟫_ℝ := by
  rw [inner_basis_eq_sum hK j (act K u), inner_basis_eq_sum hK j u]
  have hstep : ∀ i, (specBasis hK j).ofLp i * act K u i
      = ∑ k, (K i k * (specBasis hK j).ofLp i) * u k := by
    intro i
    unfold act
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [Finset.sum_congr rfl fun i _ => hstep i, Finset.sum_comm]
  have hswap : ∀ k, (∑ i, (K i k * (specBasis hK j).ofLp i) * u k)
      = (specEigen hK j * (specBasis hK j).ofLp k) * u k := by
    intro k
    rw [← Finset.sum_mul]
    congr 1
    rw [← specBasis_eigen hK j k]
    exact Finset.sum_congr rfl fun i _ => by rw [hK i k]
  rw [Finset.sum_congr rfl fun k _ => hswap k, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- Parseval, in the form this module uses. -/
theorem eucNorm_sq_eq_sum (hK : ∀ i j, K i j = K j i) (u : ι → ℝ) :
    eucNorm u * eucNorm u = ∑ j, ⟪specBasis hK j, emb u⟫_ℝ ^ 2 := by
  have hnn : (0:ℝ) ≤ ∑ j, ((specBasis hK).repr (emb u) j) ^ 2 :=
    Finset.sum_nonneg fun j _ => sq_nonneg _
  have h1 : eucNorm u
      = Real.sqrt (∑ j, ((specBasis hK).repr (emb u) j) ^ 2) := by
    rw [← norm_emb, ← LinearIsometryEquiv.norm_map (specBasis hK).repr (emb u),
      EuclideanSpace.norm_eq]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by rw [Real.norm_eq_abs, sq_abs]
  rw [h1, Real.mul_self_sqrt hnn]
  exact Finset.sum_congr rfl fun j _ => by
    rw [OrthonormalBasis.repr_apply_apply]

/-- **THE OPERATOR BOUND.**  On the orthogonal complement of the Perron vector
the image of the kernel is bounded by the factor `specGap`.  This is NOT a
contraction: `specGap` is below `lam` and typically far ABOVE one.  It is
precisely the hypothesis the bridge module carried and did not discharge. -/
theorem norm_act_le_specGap (hpos : ∀ i j, 0 < K i j) (hK : ∀ i j, K i j = K j i)
    {v : ι → ℝ} (hv : ∀ i, 0 < v i) {lam : ℝ}
    (hvE : ∀ i, ∑ j, K i j * v j = lam * v i)
    {u : ι → ℝ} (hperp : ∑ i, v i * u i = 0) :
    eucNorm (act K u) ≤ specGap hK lam * eucNorm u := by
  have hr0 : 0 ≤ specGap hK lam := specGap_nonneg hK lam
  -- termwise domination of the squared coordinates
  have hterm : ∀ j : ι, ⟪specBasis hK j, emb (act K u)⟫_ℝ ^ 2
      ≤ specGap hK lam ^ 2 * ⟪specBasis hK j, emb u⟫_ℝ ^ 2 := by
    intro j
    rw [inner_specBasis_act hK u j, mul_pow]
    by_cases h : specEigen hK j = lam
    · rw [inner_specBasis_eq_zero_of_top hpos hK hv hvE hperp h]
      simp
    · have habs : |specEigen hK j| ≤ specGap hK lam := by
        refine le_trans ?_ (Finset.le_sup' _ (Finset.mem_univ j))
        simp [specGap, h]
      have : specEigen hK j ^ 2 ≤ specGap hK lam ^ 2 := by
        rw [← sq_abs (specEigen hK j)]
        exact pow_le_pow_left₀ (abs_nonneg _) habs 2
      exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
  have hsum : eucNorm (act K u) * eucNorm (act K u)
      ≤ specGap hK lam ^ 2 * (eucNorm u * eucNorm u) := by
    rw [eucNorm_sq_eq_sum hK, eucNorm_sq_eq_sum hK u, Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => hterm j
  have hn : 0 ≤ eucNorm (act K u) := eucNorm_nonneg _
  nlinarith [eucNorm_nonneg u, hn, hsum, mul_nonneg hr0 (eucNorm_nonneg u)]

/-! ### §5b  The rate that is actually below one

`specGap` is below `lam`, which is NOT the same as below one: the kernel is
unnormalised, so `lam` and `specGap` are both typically far above one and
`specGap ^ N` GROWS.  The number that is below one is the rate relative to the
Perron scale, and it is what makes the endpoint a decay statement rather than a
statement about growing more slowly than the top of the spectrum. -/

/-- The contraction rate of the fluctuation sector **relative to the Perron
eigenvalue**.  Unlike `specGap`, this is genuinely below one. -/
noncomputable def specRatio (hK : ∀ i j, K i j = K j i) (lam : ℝ) : ℝ :=
  specGap hK lam / lam

theorem specRatio_nonneg (hpos : ∀ i j, 0 < K i j) (hK : ∀ i j, K i j = K j i)
    {v : ι → ℝ} (hv : ∀ i, 0 < v i) {lam : ℝ}
    (hvE : ∀ i, ∑ j, K i j * v j = lam * v i) :
    0 ≤ specRatio hK lam :=
  div_nonneg (specGap_nonneg hK lam) (le_of_lt (eigenvalue_pos hpos hv hvE))

/-- **`specRatio < 1`.**  This, and not `specGap < lam`, is the statement that
makes a geometric bound mean decay. -/
theorem specRatio_lt_one (hpos : ∀ i j, 0 < K i j) (hK : ∀ i j, K i j = K j i)
    {v : ι → ℝ} (hv : ∀ i, 0 < v i) {lam : ℝ}
    (hvE : ∀ i, ∑ j, K i j * v j = lam * v i) :
    specRatio hK lam < 1 := by
  have hlam : 0 < lam := eigenvalue_pos hpos hv hvE
  rw [specRatio, div_lt_one hlam]
  exact specGap_lt hpos hK hv hvE

theorem specGap_eq_specRatio_mul (hK : ∀ i j, K i j = K j i) {lam : ℝ}
    (hlam : lam ≠ 0) : specGap hK lam = specRatio hK lam * lam := by
  rw [specRatio, div_mul_cancel₀ _ hlam]

/-- Acting with the kernel divided by its Perron eigenvalue. -/
theorem act_normalizedKernel (K : ι → ι → ℝ) {lam : ℝ} (hlam : lam ≠ 0)
    (u : ι → ℝ) :
    act (normalizedKernel K lam) u = fun i => lam⁻¹ * act K u i := by
  funext i
  unfold act normalizedKernel
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by field_simp

/-- **The NORMALISED kernel is a genuine contraction of the fluctuation
sector**, with rate `specRatio < 1`. -/
theorem norm_act_normalizedKernel_le (hpos : ∀ i j, 0 < K i j)
    (hK : ∀ i j, K i j = K j i) {v : ι → ℝ} (hv : ∀ i, 0 < v i) {lam : ℝ}
    (hvE : ∀ i, ∑ j, K i j * v j = lam * v i)
    {u : ι → ℝ} (hperp : ∑ i, v i * u i = 0) :
    eucNorm (act (normalizedKernel K lam) u) ≤ specRatio hK lam * eucNorm u := by
  have hlam : 0 < lam := eigenvalue_pos hpos hv hvE
  rw [act_normalizedKernel K (ne_of_gt hlam) u, eucNorm_smul,
    abs_of_nonneg (le_of_lt (inv_pos.mpr hlam))]
  have hb := norm_act_le_specGap hpos hK hv hvE hperp
  rw [specRatio, div_mul_eq_mul_div, le_div_iff₀ hlam]
  calc lam⁻¹ * eucNorm (act K u) * lam = eucNorm (act K u) := by
        field_simp
    _ ≤ specGap hK lam * eucNorm u := hb

/-! ## §6b  Invariance of the fluctuation sector at an eigenvector

The bridge module proved invariance for a vector the kernel *fixes*.  Here the
vacuum is an eigenvector with eigenvalue `lam`, not a fixed point --- the kernel
is unnormalised --- so the invariance is reproved in the form the unnormalised
kernel needs.  The scalar drops out because the pairing is bilinear. -/

theorem perp_invariant_eigen (hK : ∀ i j, K i j = K j i) {v : ι → ℝ} {lam : ℝ}
    (hvE : ∀ i, ∑ j, K i j * v j = lam * v i)
    {u : ι → ℝ} (hperp : ∑ i, v i * u i = 0) :
    ∑ i, v i * act K u i = 0 := by
  rw [← act_pairing_symm hK v u]
  have hstep : ∀ i, act K v i * u i = lam * (v i * u i) := by
    intro i
    unfold act
    rw [hvE i]
    ring
  rw [Finset.sum_congr rfl fun i _ => hstep i, ← Finset.mul_sum, hperp, mul_zero]

/-- Iterates of a fluctuation observable satisfy a geometric bound with ratio
`specGap` --- again NOT a contraction unless `specGap < 1`, which it need not
be. -/
theorem iterate_norm_le_specGap (hpos : ∀ i j, 0 < K i j)
    (hK : ∀ i j, K i j = K j i) {v : ι → ℝ} (hv : ∀ i, 0 < v i) {lam : ℝ}
    (hvE : ∀ i, ∑ j, K i j * v j = lam * v i)
    {u : ι → ℝ} (hperp : ∑ i, v i * u i = 0) (n : ℕ) :
    eucNorm ((act K)^[n] u) ≤ specGap hK lam ^ n * eucNorm u := by
  induction n generalizing u with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      calc eucNorm ((act K)^[n] (act K u))
          ≤ specGap hK lam ^ n * eucNorm (act K u) :=
            ih (perp_invariant_eigen hK hvE hperp)
        _ ≤ specGap hK lam ^ n * (specGap hK lam * eucNorm u) :=
            mul_le_mul_of_nonneg_left
              (norm_act_le_specGap hpos hK hv hvE hperp)
              (pow_nonneg (specGap_nonneg hK lam) n)
        _ = specGap hK lam ^ (n + 1) * eucNorm u := by ring

end Spectral

/-! ## §7  The endpoint — an unconditional sub-Perron bound, and relative decay

The bridge module bounded the Gibbs two-point sum under a contraction
hypothesis.  The hypothesis is now a theorem, so the bound is unconditional at
every finite extent.  But its rate is `specGap`, which is below `lam` and NOT
below one, so that bound controls GROWTH.  The decay statement is the second one
below, relative to the Perron scale `lam ^ N`.  Both theorems in this section
bound the NUMERATOR only; the denominator is §8 and the normalised statement is
§10.  Nothing in any of them is uniform in the extent. -/

/-- **THE BRIDGE MODULE'S BOUND, WITHOUT ITS HYPOTHESIS.**  The rate is
`specGap`, which is below `lam` but NOT below one --- the kernel is unnormalised
--- so on its own this bounds the growth of the fluctuation contribution, it does
not exhibit decay.  The decay statement is the relative one below. -/
theorem gibbs_pathSum_bound_unconditional {L : ℕ} {w : (Fin L → Fin 2) → ℝ}
    (hw : ∀ σ, 0 < w σ) (β : ℝ)
    {v : (Fin L → Fin 2) → ℝ} (hv : ∀ σ, 0 < v σ) {lam : ℝ}
    (hvE : ∀ σ, ∑ τ, symWeighted w β σ τ * v τ = lam * v σ)
    {A : (Fin L → Fin 2) → ℝ} (hperp : ∑ σ, v σ * dress w A σ = 0) (N : ℕ) :
    |gibbsPathSum w β N A A|
      ≤ specGap (symWeighted_symm w β) lam ^ N
        * (eucNorm (dress w A) * eucNorm (dress w A))
      ∧ specGap (symWeighted_symm w β) lam < lam := by
  refine ⟨?_, specGap_lt (symWeighted_pos hw β) (symWeighted_symm w β) hv hvE⟩
  rw [gibbsPathSum_eq_iterate hw β N A A]
  have hcomm : ∑ σ, (act (symWeighted w β))^[N] (dress w A) σ * dress w A σ
      = ∑ σ, dress w A σ * (act (symWeighted w β))^[N] (dress w A) σ :=
    Finset.sum_congr rfl fun σ _ => mul_comm _ _
  rw [hcomm]
  calc |∑ σ, dress w A σ * (act (symWeighted w β))^[N] (dress w A) σ|
      ≤ eucNorm (dress w A)
          * eucNorm ((act (symWeighted w β))^[N] (dress w A)) :=
        abs_sum_mul_le _ _
    _ ≤ eucNorm (dress w A)
          * (specGap (symWeighted_symm w β) lam ^ N * eucNorm (dress w A)) :=
        mul_le_mul_of_nonneg_left
          (iterate_norm_le_specGap (symWeighted_pos hw β) (symWeighted_symm w β)
            hv hvE hperp N) (eucNorm_nonneg _)
    _ = specGap (symWeighted_symm w β) lam ^ N
          * (eucNorm (dress w A) * eucNorm (dress w A)) := by ring


/-- **THE DECAY STATEMENT.**  Relative to the Perron scale `lam ^ N`, the
fluctuation contribution to the Gibbs two-point sum is suppressed geometrically,
at a rate `specRatio < 1`, with no carried hypothesis.

The unnormalised bound above has rate `specGap`, which is typically far ABOVE
one; only after comparison with `lam ^ N` does a geometric factor below one
appear.  This is still the NUMERATOR alone: dividing by the partition function
needs the lower bound of §8, and the two are composed in §10.

`specRatio` depends on the extent, and the measured evidence is that it
approaches `1` outside the disordered region, where the bound is empty in the
limit. -/
theorem gibbs_pathSum_relative_decay {L : ℕ} {w : (Fin L → Fin 2) → ℝ}
    (hw : ∀ σ, 0 < w σ) (β : ℝ)
    {v : (Fin L → Fin 2) → ℝ} (hv : ∀ σ, 0 < v σ) {lam : ℝ}
    (hvE : ∀ σ, ∑ τ, symWeighted w β σ τ * v τ = lam * v σ)
    {A : (Fin L → Fin 2) → ℝ} (hperp : ∑ σ, v σ * dress w A σ = 0) (N : ℕ) :
    |gibbsPathSum w β N A A|
      ≤ specRatio (symWeighted_symm w β) lam ^ N
        * (lam ^ N * (eucNorm (dress w A) * eucNorm (dress w A)))
      ∧ specRatio (symWeighted_symm w β) lam < 1 := by
  have hlam : 0 < lam := eigenvalue_pos (symWeighted_pos hw β) hv hvE
  refine ⟨?_, specRatio_lt_one (symWeighted_pos hw β) (symWeighted_symm w β) hv hvE⟩
  have hb := (gibbs_pathSum_bound_unconditional hw β hv hvE hperp N).1
  have hsplit : specGap (symWeighted_symm w β) lam ^ N
      = specRatio (symWeighted_symm w β) lam ^ N * lam ^ N := by
    rw [specGap_eq_specRatio_mul (symWeighted_symm w β) (ne_of_gt hlam), mul_pow]
  rw [hsplit] at hb
  calc |gibbsPathSum w β N A A|
      ≤ specRatio (symWeighted_symm w β) lam ^ N * lam ^ N
          * (eucNorm (dress w A) * eucNorm (dress w A)) := hb
    _ = specRatio (symWeighted_symm w β) lam ^ N
          * (lam ^ N * (eucNorm (dress w A) * eucNorm (dress w A))) := by ring

/-- **The endpoint is not quantified over an empty set.**  Because dressing is
multiplication by a strictly positive function, every fluctuation vector arises
as the dressing of an observable; so whenever the configuration space has two
points there is a NONZERO observable satisfying the orthogonality hypothesis. -/
theorem exists_nonzero_dressed_fluctuation {L : ℕ} {w : (Fin L → Fin 2) → ℝ}
    (hw : ∀ σ, 0 < w σ) {v : (Fin L → Fin 2) → ℝ} (hv : ∀ σ, 0 < v σ)
    {σ₀ σ₁ : Fin L → Fin 2} (hne : σ₀ ≠ σ₁) :
    ∃ A : (Fin L → Fin 2) → ℝ, (∑ σ, v σ * dress w A σ = 0) ∧ A ≠ 0 := by
  classical
  obtain ⟨u, hu, hune⟩ := exists_nonzero_perp hv hne
  refine ⟨fun σ => u σ / Real.sqrt (w σ), ?_, ?_⟩
  · rw [← hu]
    refine Finset.sum_congr rfl fun σ _ => ?_
    have hs : Real.sqrt (w σ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (hw σ))
    unfold dress
    field_simp
  · intro hzero
    apply hune
    funext σ
    have hs : Real.sqrt (w σ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (hw σ))
    have := congrFun hzero σ
    simp only [Pi.zero_apply, div_eq_zero_iff, hs, or_false] at this
    simpa using this

/-! ## §8  The partition function from below

The first version's scope section asserted that a lower bound on the partition
function needs the index of the top eigenvalue identified.  **That was wrong**,
and an external reading supplied the correction used here: split the observable
along the Perron direction, and both cross terms vanish by symmetry alone.  No
eigenvalue index is located anywhere in this section. -/

section Denominator

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] {K : ι → ι → ℝ}

theorem act_add (K : ι → ι → ℝ) (u z : ι → ℝ) :
    act K (fun i => u i + z i) = fun i => act K u i + act K z i := by
  funext i
  show (∑ j, K i j * (u j + z j)) = (∑ j, K i j * u j) + ∑ j, K i j * z j
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem act_smul (K : ι → ι → ℝ) (c : ℝ) (u : ι → ℝ) :
    act K (fun i => c * u i) = fun i => c * act K u i := by
  funext i
  show (∑ j, K i j * (c * u j)) = c * ∑ j, K i j * u j
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem iterate_act_add (K : ι → ι → ℝ) (n : ℕ) (u z : ι → ℝ) :
    (act K)^[n] (fun i => u i + z i)
      = fun i => (act K)^[n] u i + (act K)^[n] z i := by
  induction n generalizing u z with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply, act_add, ih, Function.iterate_succ_apply,
        Function.iterate_succ_apply]

theorem iterate_act_smul (K : ι → ι → ℝ) (c : ℝ) (n : ℕ) (u : ι → ℝ) :
    (act K)^[n] (fun i => c * u i) = fun i => c * (act K)^[n] u i := by
  induction n generalizing u with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply, act_smul, ih, Function.iterate_succ_apply]

/-- Iterating on an eigenvector multiplies by the eigenvalue. -/
theorem iterate_act_eigen {v : ι → ℝ} {lam : ℝ}
    (hvE : ∀ i, ∑ j, K i j * v j = lam * v i) (n : ℕ) :
    (act K)^[n] v = fun i => lam ^ n * v i := by
  induction n with
  | zero => funext i; simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, act_smul]
      funext i
      rw [show act K v i = lam * v i from hvE i]
      ring

/-- The pairing stays symmetric under iterates. -/
theorem iterate_pairing_symm (hK : ∀ i j, K i j = K j i) (n : ℕ) (u z : ι → ℝ) :
    ∑ i, (act K)^[n] u i * z i = ∑ i, u i * (act K)^[n] z i := by
  induction n generalizing u z with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply']
      rw [ih (act K u) z, act_pairing_symm hK u ((act K)^[n] z)]

/-- **The split.**  For a unit eigenvector `Om`, the quadratic form separates
into the Perron part and a fluctuation part, with **no cross term** --- and the
proof uses only symmetry and the eigen-equation, never the position of `lam` in
any enumeration of the spectrum. -/
theorem quadForm_split (hK : ∀ i j, K i j = K j i) {Om : ι → ℝ} {lam : ℝ}
    (hOmE : ∀ i, ∑ j, K i j * Om j = lam * Om i)
    (hOm1 : ∑ i, Om i * Om i = 1) (b : ι → ℝ) (N : ℕ) :
    ∑ i, (act K)^[N] b i * b i
      = (∑ k, Om k * b k) ^ 2 * lam ^ N
        + ∑ i, (act K)^[N] (fun j => b j - (∑ k, Om k * b k) * Om j) i
              * (b i - (∑ k, Om k * b k) * Om i) := by
  set c : ℝ := ∑ k, Om k * b k with hc
  set u : ι → ℝ := fun j => b j - c * Om j with hu
  have hb : ∀ i, b i = c * Om i + u i := by intro i; simp only [hu]; ring
  have hperp : ∑ i, Om i * u i = 0 := by
    have hstep : ∀ i, Om i * u i = Om i * b i - c * (Om i * Om i) := by
      intro i; simp only [hu]; ring
    rw [Finset.sum_congr rfl fun i _ => hstep i, Finset.sum_sub_distrib,
      ← Finset.mul_sum, hOm1, mul_one, ← hc, sub_self]
  have hOmN : (act K)^[N] Om = fun i => lam ^ N * Om i := iterate_act_eigen hOmE N
  have hcross : ∑ i, (act K)^[N] u i * Om i = 0 := by
    rw [iterate_pairing_symm hK N u Om, hOmN]
    have hstep : ∀ i, u i * (lam ^ N * Om i) = lam ^ N * (Om i * u i) := by
      intro i; ring
    rw [Finset.sum_congr rfl fun i _ => hstep i, ← Finset.mul_sum, hperp, mul_zero]
  have hbN : (act K)^[N] b = fun i => c * (lam ^ N * Om i) + (act K)^[N] u i := by
    conv_lhs => rw [show b = fun i => c * Om i + u i from funext hb]
    rw [iterate_act_add, iterate_act_smul, hOmN]
  rw [hbN]
  have hexp : ∀ i, (c * (lam ^ N * Om i) + (act K)^[N] u i) * b i
      = c ^ 2 * lam ^ N * (Om i * Om i) + c * lam ^ N * (Om i * u i)
        + c * ((act K)^[N] u i * Om i) + (act K)^[N] u i * u i := by
    intro i
    rw [show b i = c * Om i + u i from hb i]
    ring
  rw [Finset.sum_congr rfl fun i _ => hexp i, Finset.sum_add_distrib,
    Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, ← Finset.mul_sum, hOm1, hperp, hcross]
  ring

/-- **The partition form from below.**  The Perron term is exact; the
fluctuation term is controlled by the module's own operator bound. -/
theorem quadForm_lower (hpos : ∀ i j, 0 < K i j) (hK : ∀ i j, K i j = K j i)
    {Om : ι → ℝ} (hOm : ∀ i, 0 < Om i) {lam : ℝ}
    (hOmE : ∀ i, ∑ j, K i j * Om j = lam * Om i)
    (hOm1 : ∑ i, Om i * Om i = 1) (b : ι → ℝ) (N : ℕ) :
    (∑ k, Om k * b k) ^ 2 * lam ^ N
        - specGap hK lam ^ N
          * (eucNorm (fun j => b j - (∑ k, Om k * b k) * Om j)
             * eucNorm (fun j => b j - (∑ k, Om k * b k) * Om j))
      ≤ ∑ i, (act K)^[N] b i * b i := by
  set c : ℝ := ∑ k, Om k * b k with hc
  set u : ι → ℝ := fun j => b j - c * Om j with hu
  have hperp : ∑ i, Om i * u i = 0 := by
    have hstep : ∀ i, Om i * u i = Om i * b i - c * (Om i * Om i) := by
      intro i; simp only [hu]; ring
    rw [Finset.sum_congr rfl fun i _ => hstep i, Finset.sum_sub_distrib,
      ← Finset.mul_sum, hOm1, mul_one, ← hc, sub_self]
  have hbound : |∑ i, (act K)^[N] u i * u i|
      ≤ specGap hK lam ^ N * (eucNorm u * eucNorm u) := by
    have hcomm : ∑ i, (act K)^[N] u i * u i = ∑ i, u i * (act K)^[N] u i :=
      Finset.sum_congr rfl fun i _ => mul_comm _ _
    rw [hcomm]
    calc |∑ i, u i * (act K)^[N] u i| ≤ eucNorm u * eucNorm ((act K)^[N] u) :=
          abs_sum_mul_le _ _
      _ ≤ eucNorm u * (specGap hK lam ^ N * eucNorm u) :=
          mul_le_mul_of_nonneg_left
            (iterate_norm_le_specGap hpos hK hOm hOmE hperp N) (eucNorm_nonneg _)
      _ = specGap hK lam ^ N * (eucNorm u * eucNorm u) := by ring
  rw [quadForm_split hK hOmE hOm1 b N]
  have := abs_le.mp hbound
  linarith [this.1]

/-- The Euclidean-normalised vacuum satisfies the same eigen-equation. -/
theorem unitVacuum_eigen {A : ι → ι → ℝ} {v : ι → ℝ} (hv : ∀ i, 0 < v i) {lam : ℝ}
    (hvE : ∀ i, ∑ j, A i j * v j = lam * v i) :
    ∀ i, ∑ j, A i j * unitVacuum v j = lam * unitVacuum v i := by
  intro i
  have hn : eucNorm v ≠ 0 := ne_of_gt (eucNorm_pos hv)
  have hstep : ∀ j, A i j * unitVacuum v j = (A i j * v j) / eucNorm v := by
    intro j
    unfold unitVacuum
    field_simp
  rw [Finset.sum_congr rfl fun j _ => hstep j, ← Finset.sum_div, hvE i]
  unfold unitVacuum
  field_simp

end Denominator

/-! ## §9  The normalised expectation

The two halves compose: any lower bound on the partition function divides the
numerator bound.  Stated for an arbitrary lower bound `D`, so that §8 supplies
it and this theorem does not have to repeat it. -/

/-- **The normalised Gibbs two-point function, bounded.**  With `B` any bound on
the unnormalised sum (§7) and `D` any positive lower bound on the partition
function (§8), the expectation in the measure is bounded by `B / D`. -/
theorem gibbsCorr_bound_of_partition_lower {L : ℕ} {w : (Fin L → Fin 2) → ℝ}
    (β : ℝ) (N : ℕ) {A : (Fin L → Fin 2) → ℝ} {B D : ℝ}
    (hDpos : 0 < D) (hD : D ≤ gibbsPartition w β N)
    (hB : |gibbsPathSum w β N A A| ≤ B) :
    |gibbsCorr w β N A A| ≤ B / D := by
  have hZ : 0 < gibbsPartition w β N := lt_of_lt_of_le hDpos hD
  have hBnn : 0 ≤ B := le_trans (abs_nonneg _) hB
  unfold gibbsCorr
  rw [abs_div, abs_of_pos hZ]
  rw [div_le_div_iff₀ hZ hDpos]
  nlinarith [hB, hD, hBnn, hDpos, abs_nonneg (gibbsPathSum w β N A A)]

/-! ## §10  The composed endpoint

§7 bounds the numerator, §8 bounds the denominator below, §9 divides one by the
other.  Nothing is left to prose: the quantifiers, the choice of threshold and
the positivity of the overlap are assembled here.

**The threshold does not depend on the observable.**  It is built from the
dressed CONSTANT observable and the vacuum, so it is fixed once the extent, the
weight and `β` are; only the constant `C` ever sees `A`.  That is visible in the
order of quantifiers of `gibbsCorr_decay_uniform_threshold`, which is therefore
the statement proved, and `gibbsCorr_decay_fixed_extent` is its three-line
consequence in the more familiar order. -/

/-- **The partition function stays above `D · lam ^ N`, past a threshold that
knows about no observable at all.**  Both `D` and `N₀` are built from the dressed
constant observable and the vacuum; nothing here quantifies over `A`. -/
theorem exists_partition_threshold {L : ℕ} {w : (Fin L → Fin 2) → ℝ}
    (hw : ∀ σ, 0 < w σ) (β : ℝ)
    {v : (Fin L → Fin 2) → ℝ} (hv : ∀ σ, 0 < v σ) {lam : ℝ}
    (hvE : ∀ σ, ∑ τ, symWeighted w β σ τ * v τ = lam * v σ) :
    ∃ (N₀ : ℕ) (D : ℝ), 0 < D ∧
      ∀ N, N₀ ≤ N → D * lam ^ N ≤ gibbsPartition w β N := by
  classical
  have hKpos : ∀ σ τ, 0 < symWeighted w β σ τ := symWeighted_pos hw β
  have hlam : 0 < lam := eigenvalue_pos hKpos hv hvE
  have hOmpos : ∀ i, 0 < unitVacuum v i := fun i => unitVacuum_pos hv i
  have hOmE : ∀ i, ∑ j, symWeighted w β i j * unitVacuum v j
      = lam * unitVacuum v i := unitVacuum_eigen hv hvE
  have hOm1 : ∑ i, unitVacuum v i * unitVacuum v i = 1 := unitVacuum_norm hv
  have hbpos : ∀ i, 0 < dress w (fun _ => (1 : ℝ)) i := by
    intro i
    show 0 < Real.sqrt (w i) * 1
    rw [mul_one]
    exact Real.sqrt_pos.mpr (hw i)
  -- the overlap of the vacuum with the dressed constant observable
  set c : ℝ := ∑ k, unitVacuum v k * dress w (fun _ => (1 : ℝ)) k with hcdef
  have hcpos : 0 < c :=
    Finset.sum_pos (fun k _ => mul_pos (hOmpos k) (hbpos k)) Finset.univ_nonempty
  have hc2 : 0 < c ^ 2 := pow_pos hcpos 2
  set nu : ℝ :=
    eucNorm (fun j => dress w (fun _ => (1 : ℝ)) j - c * unitVacuum v j) with hnudef
  have hnu : 0 ≤ nu := eucNorm_nonneg _
  set rho : ℝ := specRatio (symWeighted_symm w β) lam with hrhodef
  have hrho0 : 0 ≤ rho := specRatio_nonneg hKpos (symWeighted_symm w β) hv hvE
  have hrho1 : rho < 1 := specRatio_lt_one hKpos (symWeighted_symm w β) hv hvE
  -- the threshold: past it, the fluctuation part is below half the Perron part
  obtain ⟨N₀, hN₀⟩ : ∃ n : ℕ, rho ^ n < c ^ 2 / (2 * (nu * nu + 1)) :=
    exists_pow_lt_of_lt_one (by positivity) hrho1
  refine ⟨N₀, c ^ 2 / 2, by linarith, ?_⟩
  intro N hN
  have hlamN : 0 < lam ^ N := pow_pos hlam N
  have hrhoN : (0:ℝ) ≤ rho ^ N := pow_nonneg hrho0 N
  -- the fluctuation part of the partition function, past the threshold
  have hsmall : rho ^ N * (nu * nu) ≤ c ^ 2 / 2 := by
    have hmono : rho ^ N ≤ rho ^ N₀ := pow_le_pow_of_le_one hrho0 (le_of_lt hrho1) hN
    have hlt : rho ^ N < c ^ 2 / (2 * (nu * nu + 1)) := lt_of_le_of_lt hmono hN₀
    have hden : (0:ℝ) < 2 * (nu * nu + 1) := by positivity
    rw [lt_div_iff₀ hden] at hlt
    nlinarith [hlt, hnu, hrhoN]
  have hq := quadForm_lower hKpos (symWeighted_symm w β) hOmpos hOmE hOm1
    (dress w (fun _ => (1 : ℝ))) N
  rw [← gibbsPartition_eq_iterate hw β N, ← hcdef, ← hnudef] at hq
  have hgap : specGap (symWeighted_symm w β) lam ^ N = rho ^ N * lam ^ N := by
    rw [hrhodef,
      specGap_eq_specRatio_mul (symWeighted_symm w β) (ne_of_gt hlam), mul_pow]
  rw [hgap] at hq
  nlinarith [hq, hsmall, hlamN]

/-- **THE ENDPOINT, with the threshold in front of the observable.**  At a fixed
spatial extent there is ONE `N₀` that works for **every** fluctuation observable
at once; only the constant `C` depends on `A`.  That is not a strengthening
bought with extra work --- the threshold never looked at `A` in the first place
--- but a statement has to publish the strength it has, and the previous order
of quantifiers did not.

**This is a fixed-`L` statement and nothing more.**  `specRatio` depends on the
extent, the measured evidence is that it tends to `1`, and therefore this is
*not* clustering: nothing here survives the infinite-volume limit. -/
theorem gibbsCorr_decay_uniform_threshold {L : ℕ} {w : (Fin L → Fin 2) → ℝ}
    (hw : ∀ σ, 0 < w σ) (β : ℝ)
    {v : (Fin L → Fin 2) → ℝ} (hv : ∀ σ, 0 < v σ) {lam : ℝ}
    (hvE : ∀ σ, ∑ τ, symWeighted w β σ τ * v τ = lam * v σ) :
    ∃ N₀ : ℕ, ∀ A : (Fin L → Fin 2) → ℝ, (∑ σ, v σ * dress w A σ = 0) →
      ∃ C > 0, ∀ N, N₀ ≤ N →
        |gibbsCorr w β N A A|
          ≤ C * specRatio (symWeighted_symm w β) lam ^ N := by
  obtain ⟨N₀, D, hDpos, hD⟩ := exists_partition_threshold hw β hv hvE
  have hKpos : ∀ σ τ, 0 < symWeighted w β σ τ := symWeighted_pos hw β
  have hlam : 0 < lam := eigenvalue_pos hKpos hv hvE
  have hrho0 : 0 ≤ specRatio (symWeighted_symm w β) lam :=
    specRatio_nonneg hKpos (symWeighted_symm w β) hv hvE
  refine ⟨N₀, fun A hperp => ?_⟩
  have hdA : (0:ℝ) ≤ eucNorm (dress w A) * eucNorm (dress w A) := mul_self_nonneg _
  have hCnn : (0:ℝ) ≤ eucNorm (dress w A) * eucNorm (dress w A) / D :=
    div_nonneg hdA (le_of_lt hDpos)
  refine ⟨eucNorm (dress w A) * eucNorm (dress w A) / D + 1, by linarith, ?_⟩
  intro N hN
  have hlamN : 0 < lam ^ N := pow_pos hlam N
  have hrhoN : (0:ℝ) ≤ specRatio (symWeighted_symm w β) lam ^ N :=
    pow_nonneg hrho0 N
  have hDlam : 0 < D * lam ^ N := mul_pos hDpos hlamN
  have hnum := (gibbs_pathSum_relative_decay hw β hv hvE hperp N).1
  have hbnd :=
    gibbsCorr_bound_of_partition_lower (A := A) β N hDlam (hD N hN) hnum
  refine le_trans hbnd ?_
  rw [div_le_iff₀ hDlam]
  have hexp : (eucNorm (dress w A) * eucNorm (dress w A) / D + 1)
      * specRatio (symWeighted_symm w β) lam ^ N * (D * lam ^ N)
      = specRatio (symWeighted_symm w β) lam ^ N
          * (lam ^ N * (eucNorm (dress w A) * eucNorm (dress w A)))
        + specRatio (symWeighted_symm w β) lam ^ N * lam ^ N * D := by
    field_simp
  rw [hexp]
  have hp : (0:ℝ) ≤ specRatio (symWeighted_symm w β) lam ^ N * lam ^ N * D :=
    mul_nonneg (mul_nonneg hrhoN (le_of_lt hlamN)) (le_of_lt hDpos)
  linarith

/-- **THE ENDPOINT, in the familiar order.**  The three-line consequence of the
uniform statement above, kept because it is the shape a reader expects. -/
theorem gibbsCorr_decay_fixed_extent {L : ℕ} {w : (Fin L → Fin 2) → ℝ}
    (hw : ∀ σ, 0 < w σ) (β : ℝ)
    {v : (Fin L → Fin 2) → ℝ} (hv : ∀ σ, 0 < v σ) {lam : ℝ}
    (hvE : ∀ σ, ∑ τ, symWeighted w β σ τ * v τ = lam * v σ)
    {A : (Fin L → Fin 2) → ℝ} (hperp : ∑ σ, v σ * dress w A σ = 0) :
    ∃ C > 0, ∃ N₀ : ℕ, ∀ N, N₀ ≤ N →
      |gibbsCorr w β N A A|
        ≤ C * specRatio (symWeighted_symm w β) lam ^ N := by
  obtain ⟨N₀, h⟩ := gibbsCorr_decay_uniform_threshold hw β hv hvE
  obtain ⟨C, hC, hb⟩ := h A hperp
  exact ⟨C, hC, N₀, hb⟩

/-! ## §11  Sharpness: the bound of §6 is attained

§6 proves an inequality.  This section proves it is an equality --- some
fluctuation observable realises `specGap` --- so `specGap` IS the operator norm
of the kernel restricted to the fluctuation sector, not a loose over-estimate.

**The proof splits, and the split is the content.**  When `specGap > 0` the
index attaining the maximum cannot be one of the top ones, because those
contribute `0` by definition; so it hands over a genuine non-Perron
eigenvector, and eigenvectors with different eigenvalues are orthogonal.  When
`specGap = 0` that reasoning fails outright --- the maximiser may perfectly well
be a top index, and such an index supplies an eigenvector (the Perron one) but
no NON-PERRON eigenvector, hence none in the fluctuation sector.  There the §6
bound already annihilates every fluctuation observable, so any nonzero one
attains the value.  It is the second branch that
needs the fluctuation sector to be nonempty, which is why two distinct states
are assumed. -/

section Sharp

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] {K : ι → ι → ℝ}

theorem eucNorm_pos_of_ne_zero {u : ι → ℝ} (hu : u ≠ 0) : 0 < eucNorm u := by
  obtain ⟨i, hi⟩ : ∃ i, u i ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hu (funext fun i => hcon i)
  refine Real.sqrt_pos.mpr (Finset.sum_pos' (fun k _ => mul_self_nonneg _) ?_)
  exact ⟨i, Finset.mem_univ i, mul_self_pos.mpr hi⟩

/-- Eigenvectors whose eigenvalue is **not** the Perron one are orthogonal to
the Perron vector.  This is the mirror of §5, and it is one line of symmetry:
moving the kernel across the pairing scales by `lam` on one side and by the
other eigenvalue on the other. -/
theorem inner_perron_specBasis_eq_zero (hK : ∀ i j, K i j = K j i)
    {v : ι → ℝ} {lam : ℝ} (hvE : ∀ i, ∑ j, K i j * v j = lam * v i) {j : ι}
    (hne : specEigen hK j ≠ lam) :
    ∑ i, v i * (specBasis hK j).ofLp i = 0 := by
  have hsym := iterate_pairing_symm hK 1 v ((specBasis hK j).ofLp)
  simp only [Function.iterate_one] at hsym
  have hL : ∑ i, act K v i * (specBasis hK j).ofLp i
      = lam * ∑ i, v i * (specBasis hK j).ofLp i := by
    have hstep : ∀ i, act K v i * (specBasis hK j).ofLp i
        = lam * (v i * (specBasis hK j).ofLp i) := by
      intro i
      unfold act
      rw [hvE i]
      ring
    rw [Finset.sum_congr rfl fun i _ => hstep i, ← Finset.mul_sum]
  have hR : ∑ i, v i * act K ((specBasis hK j).ofLp) i
      = specEigen hK j * ∑ i, v i * (specBasis hK j).ofLp i := by
    have hstep : ∀ i, v i * act K ((specBasis hK j).ofLp) i
        = specEigen hK j * (v i * (specBasis hK j).ofLp i) := by
      intro i
      unfold act
      rw [specBasis_eigen hK j i]
      ring
    rw [Finset.sum_congr rfl fun i _ => hstep i, ← Finset.mul_sum]
  rw [hL, hR] at hsym
  have hfac : (lam - specEigen hK j) * (∑ i, v i * (specBasis hK j).ofLp i) = 0 := by
    rw [sub_mul]
    linarith
  rcases mul_eq_zero.mp hfac with h | h
  · exact absurd (by linarith : specEigen hK j = lam) hne
  · exact h

/-- **THE BOUND IS SHARP.**  Some fluctuation observable attains `specGap`, so
the inequality of §6 identifies the restricted operator norm rather than merely
bounding it.  Both branches of the proof are needed; see the section note. -/
theorem exists_attaining_fluctuation (hpos : ∀ i j, 0 < K i j)
    (hK : ∀ i j, K i j = K j i) {v : ι → ℝ} (hv : ∀ i, 0 < v i) {lam : ℝ}
    (hvE : ∀ i, ∑ j, K i j * v j = lam * v i) {i₀ i₁ : ι} (hne : i₀ ≠ i₁) :
    ∃ u : ι → ℝ, (∑ i, v i * u i = 0) ∧ eucNorm u ≠ 0 ∧
      eucNorm (act K u) = specGap hK lam * eucNorm u := by
  rcases eq_or_lt_of_le (specGap_nonneg hK lam) with hzero | hgt
  · -- `specGap = 0`: the maximiser may be a top index.  Such an index DOES
    -- supply an eigenvector -- the Perron one -- but not a non-Perron one, so
    -- none in the fluctuation sector.  §6 already annihilates that sector.
    obtain ⟨u, hu, hune⟩ := exists_nonzero_perp hv hne
    refine ⟨u, hu, ne_of_gt (eucNorm_pos_of_ne_zero hune), ?_⟩
    have hle := norm_act_le_specGap hpos hK hv hvE hu
    rw [← hzero, zero_mul] at hle ⊢
    exact le_antisymm hle (eucNorm_nonneg _)
  · -- `specGap > 0`: the maximiser is necessarily non-Perron.
    obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := ι))
      (fun j : ι => if specEigen hK j = lam then 0 else |specEigen hK j|)
    have hj' : specGap hK lam
        = (if specEigen hK j = lam then 0 else |specEigen hK j|) := by
      unfold specGap
      exact hj
    have hjne : specEigen hK j ≠ lam := by
      intro htop
      rw [hj', if_pos htop] at hgt
      exact lt_irrefl 0 hgt
    have hgap : specGap hK lam = |specEigen hK j| := by
      rw [hj', if_neg hjne]
    have hone : eucNorm ((specBasis hK j).ofLp) = 1 := by
      rw [← norm_emb]
      exact (specBasis hK).orthonormal.1 j
    refine ⟨(specBasis hK j).ofLp,
      inner_perron_specBasis_eq_zero hK hvE hjne, by rw [hone]; exact one_ne_zero, ?_⟩
    have hact : act K ((specBasis hK j).ofLp)
        = fun i => specEigen hK j * (specBasis hK j).ofLp i := by
      funext i
      unfold act
      exact specBasis_eigen hK j i
    rw [hact, eucNorm_smul, hgap]

/-- **`specGap` IS the restricted operator norm**, said about an object rather
than about two separate inequalities: the set of norm ratios `‖Ku‖ / ‖u‖` over
nonzero fluctuation observables has a **greatest element**, and it is `specGap`.

(Norm ratios, not *Rayleigh* quotients: those are `⟪u, Ku⟫ / ‖u‖²`, a different
number.)  The two distinct states are needed here for the same reason as in
`exists_attaining_fluctuation`, and for one more: with fewer, the set is EMPTY,
and an empty set has no greatest element.

`IsGreatest` is deliberately weaker machinery than a `Submodule` plus a
`ContinuousLinearMap` plus `‖·‖`: it says the supremum exists and is attained,
which is exactly the content, without committing the module to an operator-norm
interface it does not otherwise use.  `IsGreatest.csSup_eq` turns this into a
statement about `sSup` for anyone who wants one. -/
theorem specGap_isGreatest (hpos : ∀ i j, 0 < K i j)
    (hK : ∀ i j, K i j = K j i) {v : ι → ℝ} (hv : ∀ i, 0 < v i) {lam : ℝ}
    (hvE : ∀ i, ∑ j, K i j * v j = lam * v i) {i₀ i₁ : ι} (hne : i₀ ≠ i₁) :
    IsGreatest {r : ℝ | ∃ u : ι → ℝ, (∑ i, v i * u i = 0) ∧ eucNorm u ≠ 0 ∧
                  r = eucNorm (act K u) / eucNorm u} (specGap hK lam) := by
  constructor
  · obtain ⟨u, hu, hune, hattain⟩ :=
      exists_attaining_fluctuation hpos hK hv hvE hne
    exact ⟨u, hu, hune, by rw [hattain, mul_div_assoc, div_self hune, mul_one]⟩
  · rintro r ⟨u, hu, hune, rfl⟩
    rw [div_le_iff₀ (lt_of_le_of_ne (eucNorm_nonneg u) (Ne.symm hune))]
    exact norm_act_le_specGap hpos hK hv hvE hu

end Sharp

end YangMills.OS
