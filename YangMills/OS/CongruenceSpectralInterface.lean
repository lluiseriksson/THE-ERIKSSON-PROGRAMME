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

theorem perronVec_pos {T : Matrix n n ℝ} (hpos : ∀ i j, 0 < T i j) :
    ∀ i, 0 < perronVec T i := by
  classical
  rw [perronVec, dif_pos hpos]
  exact (exists_pos_eigenvector T hpos).choose_spec.choose_spec.1

theorem perronValue_pos {T : Matrix n n ℝ} (hpos : ∀ i j, 0 < T i j) :
    0 < perronValue T := by
  classical
  rw [perronValue, dif_pos hpos]
  exact (exists_pos_eigenvector T hpos).choose_spec.choose_spec.2.2.1

theorem perronVec_eigen {T : Matrix n n ℝ} (hpos : ∀ i j, 0 < T i j) :
    ∀ i, ∑ j, T i j * perronVec T j = perronValue T * perronVec T i := by
  classical
  rw [perronVec, perronValue, dif_pos hpos, dif_pos hpos]
  exact (exists_pos_eigenvector T hpos).choose_spec.choose_spec.2.2.2

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

end Congruence

end YangMills.OS
