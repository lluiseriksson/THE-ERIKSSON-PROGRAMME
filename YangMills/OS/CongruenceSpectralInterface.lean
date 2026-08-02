/-
Discharging the spectral interface of `CongruenceSpectrum`.

The conditional main theorem of `YangMills/OS/CongruenceSpectrum.lean` carries
two external hypotheses.  One of them, `BirkhoffInterface`, is a genuine
mathematical import.  The other, `SpectralInterface`, is not: its content is
Perron--Frobenius together with the variational characterisation of the second
eigenvalue of a symmetric matrix, and the only reason it was carried is that
neither was available against a `Matrix`-level definition of the ratio.

This module supplies that definition and discharges the interface.  **It does
not modify any published module**; it only imports them.
-/
import YangMills.OS.PerronKernel
import YangMills.OS.SpatialSpectral
import YangMills.OS.CongruenceSpectrum

/-!
# The spectral interface, discharged

`matrixSpecRatio` is a total function `Matrix n n ℝ → ℝ` agreeing with the
subdominant ratio on symmetric entrywise positive matrices and `0` elsewhere.
`matrixSpecRatio_spectralInterface` proves it satisfies `SpectralInterface`, and
`congruenceRatio_isLUB_of_birkhoff` is then the main theorem with **one**
external hypothesis.

Two things are worth stating because they were the registered risks.

*The classical choice is not load-bearing.*  A total ratio has to pick Perron
data, and proof irrelevance only removes the dependence on the *symmetry proof*
— the easy half.  `perronValue_unique` removes the other half: every strictly
positive eigenvector of an entrywise positive matrix carries the same
eigenvalue, so the chosen value is a property of `T`.

*No variational characterisation is reproved.*  The interface premise already
*supplies* the fluctuation witness; all this module does is feed it to
`norm_act_le_specGap`, which is the optimal operator bound on the Perron
complement and already exists.  Cauchy--Schwarz turns the one into the other.
-/

namespace YangMills.OS

namespace Congruence

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

/-! ## §1  The Perron data, chosen once and proved choice-independent -/

open Classical in
/-- A strictly positive eigenvector of an entrywise positive matrix, chosen. -/
noncomputable def perronVec (T : Matrix n n ℝ) : n → ℝ :=
  if h : ∀ i j, 0 < T i j then (exists_pos_eigenvector T h).choose else fun _ => 1

open Classical in
/-- Its eigenvalue, chosen.  `perronValue_unique` shows the choice is immaterial. -/
noncomputable def perronValue (T : Matrix n n ℝ) : ℝ :=
  if h : ∀ i j, 0 < T i j then (exists_pos_eigenvector T h).choose_spec.choose else 0

omit [DecidableEq n] in
theorem perronVec_pos {T : Matrix n n ℝ} (hpos : ∀ i j, 0 < T i j) :
    ∀ i, 0 < perronVec T i := by
  classical
  rw [perronVec, dif_pos hpos]
  exact (exists_pos_eigenvector T hpos).choose_spec.choose_spec.1

omit [DecidableEq n] in
theorem perronValue_pos {T : Matrix n n ℝ} (hpos : ∀ i j, 0 < T i j) :
    0 < perronValue T := by
  classical
  rw [perronValue, dif_pos hpos]
  exact (exists_pos_eigenvector T hpos).choose_spec.choose_spec.2.2.1

omit [DecidableEq n] in
theorem perronVec_eigen {T : Matrix n n ℝ} (hpos : ∀ i j, 0 < T i j) :
    ∀ i, ∑ j, T i j * perronVec T j = perronValue T * perronVec T i := by
  classical
  rw [perronVec, perronValue, dif_pos hpos, dif_pos hpos]
  exact (exists_pos_eigenvector T hpos).choose_spec.choose_spec.2.2.2

omit [DecidableEq n] in
/-- **The choice is immaterial.**  Every strictly positive eigenvector of an
entrywise positive matrix carries the same eigenvalue, so `perronValue` is a
property of `T` and not an artefact of the choice made to define it.  This is
the registered checkpoint: proof irrelevance does not give it, and it does not
need symmetry. -/
theorem perronValue_unique {T : Matrix n n ℝ} (hpos : ∀ i j, 0 < T i j)
    {w : n → ℝ} (hw : ∀ i, 0 < w i) {mu : ℝ}
    (hwE : ∀ i, ∑ j, T i j * w j = mu * w i) :
    mu = perronValue T :=
  (pos_eigenvector_unique hpos hw (perronVec_pos hpos) hwE
    (perronVec_eigen hpos)).1

/-! ## §2  The two estimates the bridge needs -/

omit [DecidableEq n] in
/-- **The Perron value is at most any row-sum bound.**  Evaluate the eigenvalue
equation at a coordinate where the Perron vector is largest. -/
theorem perronValue_le_of_rowSum_le {T : Matrix n n ℝ} (hpos : ∀ i j, 0 < T i j)
    {a : ℝ} (hrow : ∀ i, ∑ j, T i j ≤ a) : perronValue T ≤ a := by
  obtain ⟨i₀, -, hmax⟩ :=
    Finset.exists_max_image Finset.univ (fun i => perronVec T i)
      ⟨Classical.arbitrary n, Finset.mem_univ _⟩
  have hv0 : 0 < perronVec T i₀ := perronVec_pos hpos i₀
  have hle : ∑ j, T i₀ j * perronVec T j ≤ (∑ j, T i₀ j) * perronVec T i₀ := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun j _ => ?_
    exact mul_le_mul_of_nonneg_left (hmax j (Finset.mem_univ _)) (hpos i₀ j).le
  rw [perronVec_eigen hpos i₀] at hle
  have hstep : perronValue T * perronVec T i₀ ≤ a * perronVec T i₀ :=
    le_trans hle (mul_le_mul_of_nonneg_right (hrow i₀) hv0.le)
  exact le_of_mul_le_mul_right hstep hv0

/-- Cauchy--Schwarz, in the plain-sum form the interface speaks. -/
theorem sum_mul_le_eucNorm_mul (x y : n → ℝ) :
    ∑ i, x i * y i ≤ eucNorm x * eucNorm y := by
  have h := real_inner_le_norm (emb x) (emb y)
  rw [norm_emb, norm_emb] at h
  refine le_trans (le_of_eq ?_) h
  rw [PiLp.inner_apply]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

omit [DecidableEq n] [Nonempty n] in
/-- The quadratic form, written as a pairing with one application of the
kernel — the shape `norm_act_le_specGap` is stated in. -/
theorem quad_eq_sum_act (T : Matrix n n ℝ) (x : n → ℝ) :
    quad T x = ∑ i, x i * act T x i := by
  unfold quad act
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- **The Rayleigh bound becomes a bound on the gap.**  A fluctuation witness
orthogonal to the Perron vector with quadratic form at least `b‖x‖²` forces
`b ≤ specGap`.  Nothing variational is reproved here: the premise supplies the
witness and `norm_act_le_specGap` supplies the optimal bound on the Perron
complement; Cauchy--Schwarz joins them. -/
theorem le_specGap_of_witness {T : Matrix n n ℝ} (hpos : ∀ i j, 0 < T i j)
    (hsymm : ∀ i j, T i j = T j i) {b : ℝ} {x : n → ℝ} (hx : x ≠ 0)
    (hperp : ∑ i, perronVec T i * x i = 0)
    (hray : b * (∑ i, x i * x i) ≤ quad T x) :
    b ≤ specGap hsymm (perronValue T) := by
  have hsum : 0 < ∑ i, x i * x i := by
    rcases Function.ne_iff.mp hx with ⟨i, hi⟩
    simp only [Pi.zero_apply] at hi
    exact Finset.sum_pos' (fun j _ => mul_self_nonneg (x j))
      ⟨i, Finset.mem_univ i, mul_self_pos.mpr hi⟩
  have hnormsq : eucNorm x * eucNorm x = ∑ i, x i * x i := by
    rw [eucNorm]
    exact Real.mul_self_sqrt (le_of_lt hsum)
  have hnx : (0 : ℝ) ≤ eucNorm x := by
    rw [eucNorm]; exact Real.sqrt_nonneg _
  have hop : eucNorm (act T x) ≤ specGap hsymm (perronValue T) * eucNorm x :=
    norm_act_le_specGap hpos hsymm (perronVec_pos hpos) (perronVec_eigen hpos) hperp
  have hchain : b * (∑ i, x i * x i)
      ≤ specGap hsymm (perronValue T) * (∑ i, x i * x i) := by
    calc b * (∑ i, x i * x i) ≤ quad T x := hray
      _ = ∑ i, x i * act T x i := quad_eq_sum_act T x
      _ ≤ eucNorm x * eucNorm (act T x) := sum_mul_le_eucNorm_mul x (act T x)
      _ ≤ eucNorm x * (specGap hsymm (perronValue T) * eucNorm x) :=
          mul_le_mul_of_nonneg_left hop hnx
      _ = specGap hsymm (perronValue T) * (eucNorm x * eucNorm x) := by ring
      _ = specGap hsymm (perronValue T) * (∑ i, x i * x i) := by rw [hnormsq]
  exact le_of_mul_le_mul_right hchain hsum

/-! ## §3  The total ratio, and the interface it satisfies -/

open Classical in
/-- **The subdominant ratio as a total function of a matrix.**  On symmetric
entrywise positive matrices it is `specGap / perronValue`; elsewhere it is `0`,
which is why the old non-symmetric counterexample to the interface cannot even
be stated against it: that matrix is outside the domain by construction. -/
noncomputable def matrixSpecRatio (T : Matrix n n ℝ) : ℝ :=
  if h : (∀ i j, T i j = T j i) ∧ (∀ i j, 0 < T i j) then
    specRatio h.1 (perronValue T)
  else 0

theorem matrixSpecRatio_eq {T : Matrix n n ℝ} (hsymm : ∀ i j, T i j = T j i)
    (hpos : ∀ i j, 0 < T i j) :
    matrixSpecRatio T = specRatio hsymm (perronValue T) := by
  classical
  rw [matrixSpecRatio, dif_pos (⟨hsymm, hpos⟩ :
    (∀ i j, T i j = T j i) ∧ (∀ i j, 0 < T i j))]

theorem matrixSpecRatio_nonneg {T : Matrix n n ℝ} (hsymm : ∀ i j, T i j = T j i)
    (hpos : ∀ i j, 0 < T i j) : 0 ≤ matrixSpecRatio T := by
  rw [matrixSpecRatio_eq hsymm hpos]
  exact specRatio_nonneg hpos hsymm (perronVec_pos hpos) (perronVec_eigen hpos)

/-- It really is a ratio below one on its domain, which is what a subdominant
ratio has to be. -/
theorem matrixSpecRatio_lt_one {T : Matrix n n ℝ} (hsymm : ∀ i j, T i j = T j i)
    (hpos : ∀ i j, 0 < T i j) : matrixSpecRatio T < 1 := by
  rw [matrixSpecRatio_eq hsymm hpos]
  exact specRatio_lt_one hpos hsymm (perronVec_pos hpos) (perronVec_eigen hpos)

/-- **The interface, discharged.**  This was a hypothesis of the main theorem;
it is now a theorem about a concrete total ratio. -/
theorem matrixSpecRatio_spectralInterface :
    SpectralInterface (matrixSpecRatio (n := n)) := by
  intro T b a hTsymm ha hTpos hwit hrow
  have hsymm : ∀ i j, T i j = T j i := by
    intro i j
    have h := congrFun (congrFun hTsymm j) i
    simpa [Matrix.transpose_apply] using h
  obtain ⟨x, hx, hperp, hray⟩ := hwit (perronVec T) (perronVec_pos hTpos)
  have hb : b ≤ specGap hsymm (perronValue T) :=
    le_specGap_of_witness hTpos hsymm hx hperp hray
  have hlam : 0 < perronValue T := perronValue_pos hTpos
  have hla : perronValue T ≤ a := perronValue_le_of_rowSum_le hTpos hrow
  have hgap : 0 ≤ specGap hsymm (perronValue T) := specGap_nonneg hsymm _
  rw [matrixSpecRatio_eq hsymm hTpos, specRatio]
  have hla0 : perronValue T ≠ 0 := ne_of_gt hlam
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hexp : specGap hsymm (perronValue T) / perronValue T - b / a
      = (specGap hsymm (perronValue T) * a - b * perronValue T)
        / (perronValue T * a) := by
    field_simp
  have hnum : 0 ≤ specGap hsymm (perronValue T) * a - b * perronValue T := by
    nlinarith [hb, hla, hlam, ha, hgap]
  have hdiff : 0 ≤ specGap hsymm (perronValue T) / perronValue T - b / a := by
    rw [hexp]
    exact div_nonneg hnum (le_of_lt (mul_pos hlam ha))
  linarith

/-! ## §4  The main theorem, with one external hypothesis -/

/-- **The supremum theorem, now conditional on Birkhoff alone.**  The name is
the type: a single external hypothesis, and it is the deep one. -/
theorem congruenceRatio_isLUB_of_birkhoff
    {M : Matrix n n ℝ} {μ : ℝ} {p q : n} (hpq : p ≠ q)
    (hμ0 : 0 < μ) (hμ1 : μ < 1) (hM : M.transpose = M)
    (hpos : ∀ a b, 0 < M a b) (hlo : ∀ a b, μ ≤ M a b) (hhi : ∀ a b, M a b ≤ 1)
    (hpp : M p p = 1) (hqq : M q q = 1) (hpqv : M p q = μ) (hqpv : M q p = μ)
    (hBirkhoff : BirkhoffInterface (matrixSpecRatio (n := n))) :
    IsLUB (congrOrbit matrixSpecRatio M) ((1 - μ) / (1 + μ)) :=
  congruenceRatio_isLUB_of_birkhoff_of_spectralInterface hpq hμ0 hμ1 hM hpos hlo
    hhi hpp hqq hpqv hqpv hBirkhoff matrixSpecRatio_spectralInterface

/-! ## §5  Identity of the object: the `2×2` kernel, symbolically

Discharging an interface is not the same as building the intended function.
`matrixSpecRatio_spectralInterface` says the totalisation satisfies an abstract
contract; it does not say the totalisation *is* the subdominant ratio the paper
computes.  This section closes that gap on the exchangeable `2×2` kernel, and
does so **symbolically in `μ`**, computing both intermediate values rather than
assuming either:

    perronValue (exchangeTwo μ) = 1 + μ
    specGap    (exchangeTwo μ) = 1 - μ
    matrixSpecRatio (exchangeTwo μ) = (1-μ)/(1+μ)

The test has to pass through the totalisation, the Perron choice *and* the
definition of `specGap`; a numerical check at one `μ`, an inequality, or a proof
that assumed either intermediate would not audit what is at stake.

Bounding `specGap` from *above* is what the tree lacked, so §5.1 supplies it in
general: an eigenvector at an eigenvalue other than the Perron one is orthogonal
to the Perron vector, so a Rayleigh bound on that complement bounds every
non-Perron eigenvalue. -/

/-! ### §5.1  An upper bound for `specGap`, in general -/

/-- **Eigenvectors at different eigenvalues are orthogonal.**  Proved from the
symmetry of the kernel by moving it across the pairing, with plain sums. -/
theorem inner_eq_zero_of_eigen_ne {T : Matrix n n ℝ}
    (hsymm : ∀ i j, T i j = T j i) {v w : n → ℝ} {lam e : ℝ}
    (hvE : ∀ i, ∑ j, T i j * v j = lam * v i)
    (hwE : ∀ i, ∑ j, T i j * w j = e * w i) (hne : lam ≠ e) :
    ∑ i, v i * w i = 0 := by
  have h1 : ∑ i, (∑ j, T i j * v j) * w i = lam * ∑ i, v i * w i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [hvE i]; ring
  have h2 : ∑ i, v i * (∑ j, T i j * w j) = e * ∑ i, v i * w i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [hwE i]; ring
  have hswap : ∑ i, (∑ j, T i j * v j) * w i = ∑ i, v i * (∑ j, T i j * w j) := by
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [hsymm a b]; ring
  have heq : lam * ∑ i, v i * w i = e * ∑ i, v i * w i := by
    rw [← h1, hswap, h2]
  have hz : (lam - e) * ∑ i, v i * w i = 0 := by linarith [heq]
  rcases mul_eq_zero.mp hz with h | h
  · exact absurd (sub_eq_zero.mp h) hne
  · exact h

/-- **A Rayleigh bound on the Perron complement bounds every other eigenvalue.**
This is the direction the tree did not have: `norm_act_le_specGap` bounds the
operator *by* `specGap`, and this bounds `specGap` itself. -/
theorem abs_eigen_le_of_quad_bound {T : Matrix n n ℝ}
    (hsymm : ∀ i j, T i j = T j i) {Ω w : n → ℝ} {lam e c : ℝ}
    (hvE : ∀ i, ∑ j, T i j * Ω j = lam * Ω i)
    (hwE : ∀ i, ∑ j, T i j * w j = e * w i)
    (hne : lam ≠ e) (hw0 : ∃ i, w i ≠ 0)
    (hq : ∀ x : n → ℝ, (∑ i, Ω i * x i = 0) →
      |quad T x| ≤ c * (∑ i, x i * x i)) :
    |e| ≤ c := by
  have hperp : ∑ i, Ω i * w i = 0 := inner_eq_zero_of_eigen_ne hsymm hvE hwE hne
  have hpos : 0 < ∑ i, w i * w i := by
    obtain ⟨i, hi⟩ := hw0
    exact Finset.sum_pos' (fun k _ => mul_self_nonneg (w k))
      ⟨i, Finset.mem_univ i, mul_self_pos.mpr hi⟩
  have hquad : quad T w = e * ∑ i, w i * w i := by
    rw [quad_eq_sum_act, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    show w i * act T w i = e * (w i * w i)
    unfold act
    rw [hwE i]; ring
  have h2 := hq w hperp
  rw [hquad, abs_mul, abs_of_pos hpos] at h2
  exact le_of_mul_le_mul_right h2 hpos

/-- **`specGap ≤ c`.**  Every basis vector is either at the Perron eigenvalue,
where the defining `if` contributes `0`, or at another one, where the previous
lemma applies. -/
theorem specGap_le_of_quad_bound {T : Matrix n n ℝ}
    (hsymm : ∀ i j, T i j = T j i) {Ω : n → ℝ} {lam c : ℝ} (hc : 0 ≤ c)
    (hvE : ∀ i, ∑ j, T i j * Ω j = lam * Ω i)
    (hq : ∀ x : n → ℝ, (∑ i, Ω i * x i = 0) →
      |quad T x| ≤ c * (∑ i, x i * x i)) :
    specGap hsymm lam ≤ c := by
  rw [specGap, Finset.sup'_le_iff]
  intro j _
  by_cases h : specEigen hsymm j = lam
  · simpa [h] using hc
  · have hbe := specBasis_eigen hsymm j
    have := abs_eigen_le_of_quad_bound hsymm hvE hbe (Ne.symm h)
      (specBasis_ne_zero hsymm j) hq
    simpa [h] using this

/-! ### §5.2  The exchangeable `2×2` kernel, computed -/

/-- `E_μ`: unit diagonal, `μ` off it. -/
def exchangeTwo (μ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun i j => if i = j then 1 else μ

theorem exchangeTwo_apply (μ : ℝ) (i j : Fin 2) :
    exchangeTwo μ i j = if i = j then 1 else μ := rfl

theorem exchangeTwo_00 (μ : ℝ) : exchangeTwo μ 0 0 = 1 := by
  rw [exchangeTwo_apply, if_pos rfl]

theorem exchangeTwo_11 (μ : ℝ) : exchangeTwo μ 1 1 = 1 := by
  rw [exchangeTwo_apply, if_pos rfl]

theorem exchangeTwo_01 (μ : ℝ) : exchangeTwo μ 0 1 = μ := by
  rw [exchangeTwo_apply, if_neg (by decide : ¬((0 : Fin 2) = 1))]

theorem exchangeTwo_10 (μ : ℝ) : exchangeTwo μ 1 0 = μ := by
  rw [exchangeTwo_apply, if_neg (by decide : ¬((1 : Fin 2) = 0))]

theorem exchangeTwo_symm (μ : ℝ) : ∀ i j, exchangeTwo μ i j = exchangeTwo μ j i := by
  intro i j
  simp only [exchangeTwo_apply]
  by_cases h : i = j
  · rw [h]
  · rw [if_neg h, if_neg (Ne.symm h)]

theorem exchangeTwo_pos {μ : ℝ} (hμ : 0 < μ) : ∀ i j, 0 < exchangeTwo μ i j := by
  intro i j
  rw [exchangeTwo_apply]
  by_cases h : i = j
  · rw [if_pos h]; norm_num
  · rw [if_neg h]; exact hμ

/-- The quadratic form, in closed form. -/
theorem quad_exchangeTwo (μ : ℝ) (x : Fin 2 → ℝ) :
    quad (exchangeTwo μ) x = x 0 * x 0 + x 1 * x 1 + 2 * μ * (x 0 * x 1) := by
  unfold quad
  rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two,
    exchangeTwo_00, exchangeTwo_01, exchangeTwo_10, exchangeTwo_11]
  ring

/-- The constant vector is a strictly positive eigenvector at `1 + μ`. -/
theorem exchangeTwo_eigen_const (μ : ℝ) :
    ∀ i, ∑ j, exchangeTwo μ i j * (fun _ : Fin 2 => (1 : ℝ)) j
      = (1 + μ) * (fun _ : Fin 2 => (1 : ℝ)) i := by
  intro i
  fin_cases i <;>
    simp only [Fin.sum_univ_two, exchangeTwo_00, exchangeTwo_01, exchangeTwo_10,
      exchangeTwo_11] <;> ring

/-- **`perronValue (E_μ) = 1 + μ`**, computed — not assumed.  `perronValue_unique`
does the work: the constant vector is a positive eigenvector, so its eigenvalue
*is* the chosen one. -/
theorem perronValue_exchangeTwo {μ : ℝ} (hμ0 : 0 < μ) :
    perronValue (exchangeTwo μ) = 1 + μ :=
  (perronValue_unique (exchangeTwo_pos hμ0) (fun _ => one_pos)
    (exchangeTwo_eigen_const μ)).symm

/-- The chosen Perron vector is constant. -/
theorem perronVec_exchangeTwo_const {μ : ℝ} (hμ0 : 0 < μ) :
    ∃ c : ℝ, 0 < c ∧ ∀ i, perronVec (exchangeTwo μ) i = c := by
  obtain ⟨-, c, hc, hcw⟩ := pos_eigenvector_unique (exchangeTwo_pos hμ0)
    (fun _ => one_pos) (perronVec_pos (exchangeTwo_pos hμ0))
    (exchangeTwo_eigen_const μ) (perronVec_eigen (exchangeTwo_pos hμ0))
  exact ⟨c, hc, fun i => by simpa using hcw i⟩

/-- On the Perron complement the form is exactly `(1-μ)‖x‖²`. -/
theorem quad_bound_exchangeTwo {μ : ℝ} (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (x : Fin 2 → ℝ) (hperp : ∑ i, perronVec (exchangeTwo μ) i * x i = 0) :
    |quad (exchangeTwo μ) x| ≤ (1 - μ) * (∑ i, x i * x i) := by
  obtain ⟨c, hc, hconst⟩ := perronVec_exchangeTwo_const hμ0
  rw [Fin.sum_univ_two, hconst 0, hconst 1] at hperp
  have hx1 : x 1 = - x 0 := by
    have hz : c * (x 0 + x 1) = 0 := by linarith [hperp]
    rcases mul_eq_zero.mp hz with h | h
    · exact absurd h (ne_of_gt hc)
    · linarith
  rw [quad_exchangeTwo, Fin.sum_univ_two, hx1]
  have habs : |x 0 * x 0 + -x 0 * -x 0 + 2 * μ * (x 0 * -x 0)|
      = (1 - μ) * (x 0 * x 0 + -x 0 * -x 0) := by
    rw [show x 0 * x 0 + -x 0 * -x 0 + 2 * μ * (x 0 * -x 0)
        = (1 - μ) * (x 0 * x 0 + -x 0 * -x 0) from by ring]
    exact abs_of_nonneg (by nlinarith [mul_self_nonneg (x 0)])
  rw [habs]

/-- The antipodal fluctuation on two sites. -/
def altTwo : Fin 2 → ℝ := fun i => if i = 0 then 1 else -1

theorem altTwo_ne_zero : altTwo ≠ 0 := by
  intro h
  have := congrFun h 0
  simp only [altTwo, if_pos rfl, Pi.zero_apply] at this
  exact one_ne_zero this

/-- **`specGap (E_μ) = 1 - μ`**, computed from both sides: the new general upper
bound, and the fluctuation witness of §2 from below. -/
theorem specGap_exchangeTwo {μ : ℝ} (hμ0 : 0 < μ) (hμ1 : μ < 1) :
    specGap (exchangeTwo_symm μ) (perronValue (exchangeTwo μ)) = 1 - μ := by
  refine le_antisymm ?_ ?_
  · exact specGap_le_of_quad_bound (exchangeTwo_symm μ) (by linarith)
      (perronVec_eigen (exchangeTwo_pos hμ0)) (quad_bound_exchangeTwo hμ0 hμ1)
  · obtain ⟨c, hc, hconst⟩ := perronVec_exchangeTwo_const hμ0
    have hperp : ∑ i, perronVec (exchangeTwo μ) i * altTwo i = 0 := by
      rw [Fin.sum_univ_two, hconst 0, hconst 1]
      simp only [altTwo, if_pos rfl, if_neg (by decide : ¬((1 : Fin 2) = 0))]
      ring
    have hray : (1 - μ) * (∑ i, altTwo i * altTwo i) ≤ quad (exchangeTwo μ) altTwo := by
      rw [quad_exchangeTwo, Fin.sum_univ_two]
      simp only [altTwo, if_pos rfl, if_neg (by decide : ¬((1 : Fin 2) = 0))]
      ring_nf
    exact le_specGap_of_witness (exchangeTwo_pos hμ0) (exchangeTwo_symm μ)
      altTwo_ne_zero hperp hray

/-- **THE IDENTITY TEST.**  The totalised ratio, on the exchangeable `2×2`
kernel, is the number the paper computes — symbolically in `μ`, with both
intermediate values proved rather than assumed.  This is what certifies that
`matrixSpecRatio` *is* the subdominant ratio `r` and not merely some function
that happens to satisfy the interface. -/
theorem matrixSpecRatio_exchangeTwo {μ : ℝ} (hμ0 : 0 < μ) (hμ1 : μ < 1) :
    matrixSpecRatio (exchangeTwo μ) = (1 - μ) / (1 + μ) := by
  rw [matrixSpecRatio_eq (exchangeTwo_symm μ) (exchangeTwo_pos hμ0), specRatio,
    specGap_exchangeTwo hμ0 hμ1, perronValue_exchangeTwo hμ0]

end Congruence

end YangMills.OS
