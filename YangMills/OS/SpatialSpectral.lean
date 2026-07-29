import YangMills.OS.SpatialGibbs
import Mathlib.Analysis.Matrix.Spectrum

/-!
# The S block — the operator bound, and clustering without a hypothesis

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
* `norm_mulVec_le_specGap` — the operator bound.  For every observable
  orthogonal to the vacuum, `‖K u‖ ≤ specGap · ‖u‖`.  This is exactly the
  hypothesis the bridge paper carried.
* `gibbs_pathSum_decay_unconditional` — the endpoint.  The bridge module's
  decay theorem, with its hypothesis removed: for the coupled spatial system, at
  every finite extent, every `β` and every strictly positive source weight, the
  **unnormalised** Gibbs two-point sum of a dressed fluctuation observable decays
  geometrically in the time separation, with a rate strictly below the Perron
  eigenvalue and **no carried hypothesis**.

## The one step that does not come from the inequalities

Eigenvectors whose eigenvalue is exactly `λ` must be shown to be invisible to a
fluctuation observable.  That is geometric simplicity of the Perron eigenvalue —
proved in the companion Perron paper for an arbitrary eigenvector, not merely a
positive one — and it is what makes the sum over the spectrum drop its top term
rather than merely bound it.

## What is NOT proved, and is not claimed

The endpoint bounds the **unnormalised** two-point sum --- the same quantity the
bridge module bounded, since what is removed here is its hypothesis and nothing
else.  Turning it into a statement about the **normalised** expectation needs a
lower bound on the partition function of order `lam^N`, which would in turn need
the top eigenvalue's index to be identified and its overlap with the dressed
constant observable bounded below.  None of that is done here, so the word
*clustering* is deliberately not used for the endpoint.

`specGap` **depends on the extent**.  Nothing here bounds it away from `λ`
uniformly in the size of the configuration space, and the numerical evidence
recorded in the gap paper is that the ratio approaches `1` with the extent
outside the disordered region.  A geometric bound whose rate tends to `1` is
empty in the limit, and no claim to the contrary is made or implied.  In
particular this module does **not** produce a mass gap, and reflection
positivity remains untouched.

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

/-- **The spectral gap of the fluctuation sector.**  The largest `|μ|` over the
eigenvalues different from the Perron eigenvalue --- eigenvalues equal to `lam`
contribute `0`, which is legitimate precisely because §5 shows they are
invisible to a fluctuation observable. -/
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
the kernel contracts by `specGap`.  This is precisely the hypothesis the bridge
module carried and did not discharge. -/
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

/-- Iterates of a fluctuation observable contract geometrically. -/
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

/-! ## §7  The endpoint — clustering with no hypothesis left

The bridge module proved geometric decay of the Gibbs two-point sum under a
contraction hypothesis.  The hypothesis is now a theorem, so the decay is
unconditional at every finite extent. -/

/-- **THE BRIDGE MODULE'S DECAY THEOREM, WITHOUT ITS HYPOTHESIS.**  For the
coupled spatial system at every finite extent, every `β`, and every strictly
positive source weight, the UNNORMALISED Gibbs two-point sum of an observable
whose dressing is orthogonal to the vacuum decays geometrically in the time
separation --- with a rate strictly below the Perron eigenvalue and no carried
hypothesis.

This is the same quantity the bridge module bounded; what is removed is the
assumption, not the normalisation.  The normalised expectation would additionally
need a lower bound on the partition function, which is not proved here.

The rate depends on the extent.  Nothing here bounds it away from `lam`
uniformly, and the measured evidence is that the ratio approaches `1` outside
the disordered region, where the bound is therefore empty in the limit. -/
theorem gibbs_pathSum_decay_unconditional {L : ℕ} {w : (Fin L → Fin 2) → ℝ}
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

end YangMills.OS
