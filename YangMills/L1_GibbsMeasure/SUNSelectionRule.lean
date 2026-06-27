/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib
import YangMills.L1_GibbsMeasure.CenterInvariance
import YangMills.ClayCore.SchurMomentVanishing
import YangMills.P8_PhysicalGap.SUN_StateConstruction

/-!
# The SU(N) Wilson-loop centre selection rule — fully concrete

Instantiates the centre selection rule at the **genuine SU(N) Haar measure**:
for the product Haar gauge measure on `SU(n)`-valued configurations, the
Wilson loop of any positively-oriented loop whose length is **not divisible
by `n`** has vanishing expectation.  No instance hypotheses remain — the
left-invariance of `sunHaarProb` is Haar's, the central element is the
verified `scalarCenterElement` (`ω·1`, `ω = e^{2πi/n}`), and `ω^L ≠ 1` is
the proved `rootOfUnity_pow_ne_one_of_not_dvd`.

This ties together the repo's three verified layers: the Schur/centre
machinery (`ClayCore/Schur*`), the product gauge measure
(`L1_GibbsMeasure/GibbsMeasure`), and the new centre invariance
(`CenterInvariance.lean`).  It is the lattice **Z_N N-ality selection rule**
for Wilson loops — the symmetry statement underlying centre-based
confinement criteria (M3-side; nothing here touches M4/M5/Clay).

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills

open MeasureTheory GaugeConfig

variable {d N : ℕ} [NeZero d] [NeZero N]

/-- The **SU(n) Wilson loop**: the matrix trace of the Wilson line of a
closed edge list, for configurations valued in the special unitary group. -/
noncomputable def wilsonLoopSU {n : ℕ}
    (A : GaugeConfig d N ↥(Matrix.specialUnitaryGroup (Fin n) ℂ))
    (es : List (ConcreteEdge d N)) : ℂ :=
  ((wilsonLine A es :
      ↥(Matrix.specialUnitaryGroup (Fin n) ℂ)) : Matrix (Fin n) (Fin n) ℂ).trace

/-- The scalar centre element is central in `SU(n)`. -/
lemma scalarCenterElement_commute (n : ℕ) [NeZero n] :
    ∀ y : ↥(Matrix.specialUnitaryGroup (Fin n) ℂ),
      Commute (scalarCenterElement n) y := by
  intro y
  have hval : ((scalarCenterElement n :
      ↥(Matrix.specialUnitaryGroup (Fin n) ℂ)) : Matrix (Fin n) (Fin n) ℂ)
      = rootOfUnity n • (1 : Matrix (Fin n) (Fin n) ℂ) := rfl
  apply Subtype.ext
  simp only [MulMemClass.coe_mul, hval]
  rw [Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one]

/-- **Eigenvalue identity:** under the centre action by `scalarCenterElement`,
the SU(n) Wilson loop of a positively-oriented loop is multiplied by
`ω^L`. -/
lemma wilsonLoopSU_centerAct {n : ℕ} [NeZero n]
    (A : GaugeConfig d N ↥(Matrix.specialUnitaryGroup (Fin n) ℂ))
    (es : List (ConcreteEdge d N)) (hpos : ∀ e ∈ es, e.sign = true) :
    wilsonLoopSU (centerAct (scalarCenterElement n) A) es
      = rootOfUnity n ^ es.length * wilsonLoopSU A es := by
  unfold wilsonLoopSU
  rw [wilsonLine_center_smul_of_mem (scalarCenterElement_commute n) A _ es
    (fun e he => centerAct_apply_pos (scalarCenterElement n) A e (hpos e he))]
  simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow]
  have hval : ((scalarCenterElement n :
      ↥(Matrix.specialUnitaryGroup (Fin n) ℂ)) : Matrix (Fin n) (Fin n) ℂ)
      = rootOfUnity n • (1 : Matrix (Fin n) (Fin n) ℂ) := rfl
  rw [hval, trace_scalarPow_mul]

/-- **Matrix-valued centre eigenvalue identity:** under the centre action by
`scalarCenterElement`, the whole SU(n) Wilson line of a positively-oriented
edge list is multiplied by `ω^L`, before taking any trace. -/
lemma wilsonLineSU_centerAct_val {n : ℕ} [NeZero n]
    (A : GaugeConfig d N ↥(Matrix.specialUnitaryGroup (Fin n) ℂ))
    (es : List (ConcreteEdge d N)) (hpos : ∀ e ∈ es, e.sign = true) :
    ((wilsonLine (centerAct (scalarCenterElement n) A) es :
        ↥(Matrix.specialUnitaryGroup (Fin n) ℂ)) :
          Matrix (Fin n) (Fin n) ℂ)
      = rootOfUnity n ^ es.length •
        ((wilsonLine A es : ↥(Matrix.specialUnitaryGroup (Fin n) ℂ)) :
          Matrix (Fin n) (Fin n) ℂ) := by
  rw [wilsonLine_center_smul_of_mem (scalarCenterElement_commute n) A _ es
    (fun e he => centerAct_apply_pos (scalarCenterElement n) A e (hpos e he))]
  simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow]
  have hval : ((scalarCenterElement n :
      ↥(Matrix.specialUnitaryGroup (Fin n) ℂ)) : Matrix (Fin n) (Fin n) ℂ)
      = rootOfUnity n • (1 : Matrix (Fin n) (Fin n) ℂ) := rfl
  rw [hval]
  simp [smul_pow]

/-- **The SU(N) Wilson-loop centre selection rule (fully concrete).**
For the product Haar gauge measure on `SU(n)`-valued lattice configurations
and any positively-oriented loop whose length is not divisible by `n`, the
Wilson-loop expectation vanishes:
`∫ W_es dμ_Haar = 0` whenever `n ∤ L`.

This is the lattice `Z_n` N-ality selection rule, with every ingredient
machine-checked: Haar left-invariance, the centre eigenvalue `ω^L`, and the
nondegeneracy `ω^L ≠ 1` for `n ∤ L`. -/
theorem integral_wilsonLoopSU_eq_zero {n : ℕ} [NeZero n]
    (es : List (ConcreteEdge d N)) (hpos : ∀ e ∈ es, e.sign = true)
    (hL : ¬ n ∣ es.length) :
    ∫ A, wilsonLoopSU A es
        ∂(gaugeMeasureFrom (d := d) (N := N) (sunHaarProb n)) = 0 := by
  have hpt : ∀ A, wilsonLoopSU (centerAct (scalarCenterElement n) A) es
      = rootOfUnity n ^ es.length * wilsonLoopSU A es :=
    fun A => wilsonLoopSU_centerAct A es hpos
  have hinv : ∫ A, wilsonLoopSU A es
        ∂(gaugeMeasureFrom (d := d) (N := N) (sunHaarProb n))
      = ∫ A, wilsonLoopSU (centerAct (scalarCenterElement n) A) es
        ∂(gaugeMeasureFrom (d := d) (N := N) (sunHaarProb n)) :=
    (integral_centerAct (sunHaarProb n) (scalarCenterElement n) _).symm
  have hmul : ∫ A, wilsonLoopSU (centerAct (scalarCenterElement n) A) es
        ∂(gaugeMeasureFrom (d := d) (N := N) (sunHaarProb n))
      = rootOfUnity n ^ es.length * ∫ A, wilsonLoopSU A es
        ∂(gaugeMeasureFrom (d := d) (N := N) (sunHaarProb n)) := by
    rw [show (fun A => wilsonLoopSU (centerAct (scalarCenterElement n) A) es)
        = fun A => rootOfUnity n ^ es.length * wilsonLoopSU A es from
      funext hpt]
    exact MeasureTheory.integral_const_mul _ _
  rw [hmul] at hinv
  have hfactor : (1 - rootOfUnity n ^ es.length) *
      ∫ A, wilsonLoopSU A es
        ∂(gaugeMeasureFrom (d := d) (N := N) (sunHaarProb n)) = 0 := by
    linear_combination hinv
  rcases mul_eq_zero.mp hfactor with h1 | h2
  · exact absurd (sub_eq_zero.mp h1).symm
      (rootOfUnity_pow_ne_one_of_not_dvd n es.length hL)
  · exact h2

/-- **Open Wilson-line matrix-coefficient centre selection rule.**
For the product Haar gauge measure on `SU(n)`-valued lattice configurations
and any positively-oriented edge list whose length is not divisible by `n`,
the expectation of every Wilson-line matrix coefficient vanishes.  This is
the open-line, representation-valued form of the same finite-lattice `Z_n`
charge selection used by the traced loop theorem above. -/
theorem integral_wilsonLineSU_entry_eq_zero {n : ℕ} [NeZero n]
    (es : List (ConcreteEdge d N)) (hpos : ∀ e ∈ es, e.sign = true)
    (hL : ¬ n ∣ es.length) (i j : Fin n) :
    ∫ A, (((wilsonLine A es :
          ↥(Matrix.specialUnitaryGroup (Fin n) ℂ)) :
            Matrix (Fin n) (Fin n) ℂ) i j)
        ∂(gaugeMeasureFrom (d := d) (N := N) (sunHaarProb n)) = 0 := by
  let μA := gaugeMeasureFrom (d := d) (N := N) (sunHaarProb n)
  let W : GaugeConfig d N ↥(Matrix.specialUnitaryGroup (Fin n) ℂ) →
      ℂ :=
    fun A => ((wilsonLine A es :
      ↥(Matrix.specialUnitaryGroup (Fin n) ℂ)) :
        Matrix (Fin n) (Fin n) ℂ) i j
  have hpt : ∀ A, W (centerAct (scalarCenterElement n) A)
      = rootOfUnity n ^ es.length * W A := by
    intro A
    dsimp [W]
    rw [wilsonLineSU_centerAct_val A es hpos]
    simp
  have hinv : ∫ A, W A ∂μA
      = ∫ A, W (centerAct (scalarCenterElement n) A) ∂μA := by
    dsimp [μA]
    exact (integral_centerAct (sunHaarProb n) (scalarCenterElement n) W).symm
  have hmul : ∫ A, W (centerAct (scalarCenterElement n) A) ∂μA
      = rootOfUnity n ^ es.length * ∫ A, W A ∂μA := by
    rw [show (fun A => W (centerAct (scalarCenterElement n) A))
        = fun A => rootOfUnity n ^ es.length * W A from funext hpt]
    exact MeasureTheory.integral_const_mul _ _
  rw [hmul] at hinv
  have hfactor : (1 - rootOfUnity n ^ es.length) *
      ∫ A, W A ∂μA = 0 := by
    linear_combination hinv
  rcases mul_eq_zero.mp hfactor with h1 | h2
  · exact absurd (sub_eq_zero.mp h1).symm
      (rootOfUnity_pow_ne_one_of_not_dvd n es.length hL)
  · exact h2

end YangMills
