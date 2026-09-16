import YangMills.RG.BalabanCMP116WilsonOrientedEdgeMixed

/-!
# Norm bounds for mixed oriented Wilson edge variations

At zero time, every first variation is one generator times one unitary
background factor, while every mixed second variation is the symmetric
product of two generators times one unitary background factor.  This module
proves the corresponding absolute and small-background difference bounds.
-/

namespace YangMills.RG

open Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d N Nc : ℕ} [NeZero d] [NeZero N] [NeZero Nc]

/-- First variation at zero, written directly using the oriented background
factor. -/
theorem orientedWilsonFactorFirst_zero_eq
    (U : PhysicalGaugeBackground d N Nc)
    (A : PhysicalGaugeOneCochain d N Nc)
    (e : ConcreteEdge d N) :
    orientedWilsonFactorFirst U A e 0 =
      if e.sign then
        orientedWilsonGenerator A e * orientedWilsonBackgroundFactor U e
      else
        orientedWilsonBackgroundFactor U e * orientedWilsonGenerator A e := by
  cases h : e.sign
  · simp [orientedWilsonFactorFirst, orientedWilsonBackgroundFactor, h,
      physicalMatrixExp_zero_smul]
  · simp [orientedWilsonFactorFirst, orientedWilsonBackgroundFactor, h,
      physicalMatrixExp_zero_smul]

/-- A first edge variation costs exactly one generator scale. -/
theorem norm_orientedWilsonFactorFirst_zero_le
    (U : PhysicalGaugeBackground d N Nc)
    (A : PhysicalGaugeOneCochain d N Nc)
    (e : ConcreteEdge d N) :
    ‖orientedWilsonFactorFirst U A e 0‖ ≤
      ‖orientedWilsonGenerator A e‖ := by
  rw [orientedWilsonFactorFirst_zero_eq]
  cases h : e.sign
  · simp only [h, Bool.false_eq_true, if_false]
    calc
      ‖orientedWilsonBackgroundFactor U e * orientedWilsonGenerator A e‖
          ≤ ‖orientedWilsonBackgroundFactor U e‖ *
              ‖orientedWilsonGenerator A e‖ :=
            Matrix.l2_opNorm_mul _ _
      _ = ‖orientedWilsonGenerator A e‖ := by
        rw [norm_orientedWilsonBackgroundFactor, one_mul]
  · simp only [h, if_true]
    calc
      ‖orientedWilsonGenerator A e * orientedWilsonBackgroundFactor U e‖
          ≤ ‖orientedWilsonGenerator A e‖ *
              ‖orientedWilsonBackgroundFactor U e‖ :=
            Matrix.l2_opNorm_mul _ _
      _ = ‖orientedWilsonGenerator A e‖ := by
        rw [norm_orientedWilsonBackgroundFactor, mul_one]

/-- The first variation changes by at most `ε` times its generator scale. -/
theorem norm_orientedWilsonFactorFirst_zero_sub_trivial_le
    (U : PhysicalGaugeBackground d N Nc) (ε : ℝ)
    (hsmall : PhysicalWilsonSmallBackground U ε)
    (A : PhysicalGaugeOneCochain d N Nc)
    (e : ConcreteEdge d N) :
    ‖orientedWilsonFactorFirst U A e 0 -
        orientedWilsonFactorFirst
          (trivialPhysicalGaugeBackground d N Nc) A e 0‖ ≤
      ε * ‖orientedWilsonGenerator A e‖ := by
  rw [orientedWilsonFactorFirst_zero_eq,
    orientedWilsonFactorFirst_zero_eq]
  cases h : e.sign
  · simp only [h, Bool.false_eq_true, if_false]
    rw [show
      orientedWilsonBackgroundFactor U e * orientedWilsonGenerator A e -
          orientedWilsonBackgroundFactor
              (trivialPhysicalGaugeBackground d N Nc) e *
            orientedWilsonGenerator A e =
        (orientedWilsonBackgroundFactor U e -
          orientedWilsonBackgroundFactor
            (trivialPhysicalGaugeBackground d N Nc) e) *
          orientedWilsonGenerator A e by noncomm_ring]
    calc
      ‖(orientedWilsonBackgroundFactor U e -
            orientedWilsonBackgroundFactor
              (trivialPhysicalGaugeBackground d N Nc) e) *
          orientedWilsonGenerator A e‖
          ≤ ‖orientedWilsonBackgroundFactor U e -
                orientedWilsonBackgroundFactor
                  (trivialPhysicalGaugeBackground d N Nc) e‖ *
              ‖orientedWilsonGenerator A e‖ :=
            Matrix.l2_opNorm_mul _ _
      _ ≤ ε * ‖orientedWilsonGenerator A e‖ := by
        gcongr
        exact norm_orientedWilsonBackgroundFactor_sub_trivial_le
          U ε hsmall e
  · simp only [h, if_true]
    rw [show
      orientedWilsonGenerator A e * orientedWilsonBackgroundFactor U e -
          orientedWilsonGenerator A e *
            orientedWilsonBackgroundFactor
              (trivialPhysicalGaugeBackground d N Nc) e =
        orientedWilsonGenerator A e *
          (orientedWilsonBackgroundFactor U e -
            orientedWilsonBackgroundFactor
              (trivialPhysicalGaugeBackground d N Nc) e) by noncomm_ring]
    calc
      ‖orientedWilsonGenerator A e *
          (orientedWilsonBackgroundFactor U e -
            orientedWilsonBackgroundFactor
              (trivialPhysicalGaugeBackground d N Nc) e)‖
          ≤ ‖orientedWilsonGenerator A e‖ *
              ‖orientedWilsonBackgroundFactor U e -
                orientedWilsonBackgroundFactor
                  (trivialPhysicalGaugeBackground d N Nc) e‖ :=
            Matrix.l2_opNorm_mul _ _
      _ ≤ ‖orientedWilsonGenerator A e‖ * ε := by
        gcongr
        exact norm_orientedWilsonBackgroundFactor_sub_trivial_le
          U ε hsmall e
      _ = ε * ‖orientedWilsonGenerator A e‖ := by ring

/-- The symmetric generator product has norm at most twice the product of
the two generator norms. -/
theorem norm_orientedWilsonMixedGeneratorNumerator_le
    (A B : PhysicalGaugeOneCochain d N Nc)
    (e : ConcreteEdge d N) :
    ‖orientedWilsonGenerator A e * orientedWilsonGenerator B e +
        orientedWilsonGenerator B e * orientedWilsonGenerator A e‖ ≤
      2 * ‖orientedWilsonGenerator A e‖ *
        ‖orientedWilsonGenerator B e‖ := by
  calc
    ‖orientedWilsonGenerator A e * orientedWilsonGenerator B e +
        orientedWilsonGenerator B e * orientedWilsonGenerator A e‖
        ≤ ‖orientedWilsonGenerator A e * orientedWilsonGenerator B e‖ +
          ‖orientedWilsonGenerator B e * orientedWilsonGenerator A e‖ :=
            norm_add_le _ _
    _ ≤ ‖orientedWilsonGenerator A e‖ *
          ‖orientedWilsonGenerator B e‖ +
        ‖orientedWilsonGenerator B e‖ *
          ‖orientedWilsonGenerator A e‖ := by
      gcongr
      · exact Matrix.l2_opNorm_mul _ _
      · exact Matrix.l2_opNorm_mul _ _
    _ = 2 * ‖orientedWilsonGenerator A e‖ *
        ‖orientedWilsonGenerator B e‖ := by ring

/-- Mixed numerator written directly using the oriented background factor. -/
theorem orientedWilsonFactorMixedNumerator_eq
    (U : PhysicalGaugeBackground d N Nc)
    (A B : PhysicalGaugeOneCochain d N Nc)
    (e : ConcreteEdge d N) :
    orientedWilsonFactorMixedNumerator U A B e =
      let mixed :=
        orientedWilsonGenerator A e * orientedWilsonGenerator B e +
          orientedWilsonGenerator B e * orientedWilsonGenerator A e
      if e.sign then
        mixed * orientedWilsonBackgroundFactor U e
      else
        orientedWilsonBackgroundFactor U e * mixed := by
  cases h : e.sign
  · simp [orientedWilsonFactorMixedNumerator,
      orientedWilsonBackgroundFactor, h]
  · simp [orientedWilsonFactorMixedNumerator,
      orientedWilsonBackgroundFactor, h]

/-- A mixed second edge variation costs one product of generator scales. -/
theorem norm_orientedWilsonFactorMixedSecond_le
    (U : PhysicalGaugeBackground d N Nc)
    (A B : PhysicalGaugeOneCochain d N Nc)
    (e : ConcreteEdge d N) :
    ‖orientedWilsonFactorMixedSecond U A B e‖ ≤
      ‖orientedWilsonGenerator A e‖ *
        ‖orientedWilsonGenerator B e‖ := by
  have hnum :
      ‖orientedWilsonFactorMixedNumerator U A B e‖ ≤
        2 * ‖orientedWilsonGenerator A e‖ *
          ‖orientedWilsonGenerator B e‖ := by
    cases h : e.sign
    · simp only [orientedWilsonFactorMixedNumerator, h, Bool.false_eq_true,
        if_false]
      calc
        ‖(orientedWilsonPositiveBase U e)ᴴ *
            (orientedWilsonGenerator A e * orientedWilsonGenerator B e +
              orientedWilsonGenerator B e * orientedWilsonGenerator A e)‖
            ≤ ‖(orientedWilsonPositiveBase U e)ᴴ‖ *
                ‖orientedWilsonGenerator A e * orientedWilsonGenerator B e +
                  orientedWilsonGenerator B e *
                    orientedWilsonGenerator A e‖ :=
              Matrix.l2_opNorm_mul _ _
        _ = 1 *
            ‖orientedWilsonGenerator A e * orientedWilsonGenerator B e +
              orientedWilsonGenerator B e * orientedWilsonGenerator A e‖ := by
              rw [Matrix.l2_opNorm_conjTranspose,
                norm_orientedWilsonPositiveBase]
        _ ≤ 1 * (2 * ‖orientedWilsonGenerator A e‖ *
            ‖orientedWilsonGenerator B e‖) := by
              gcongr
              exact norm_orientedWilsonMixedGeneratorNumerator_le A B e
        _ = 2 * ‖orientedWilsonGenerator A e‖ *
            ‖orientedWilsonGenerator B e‖ := by ring
    · simp only [orientedWilsonFactorMixedNumerator, h, if_true]
      calc
        ‖(orientedWilsonGenerator A e * orientedWilsonGenerator B e +
              orientedWilsonGenerator B e * orientedWilsonGenerator A e) *
            orientedWilsonPositiveBase U e‖
            ≤ ‖orientedWilsonGenerator A e * orientedWilsonGenerator B e +
                  orientedWilsonGenerator B e *
                    orientedWilsonGenerator A e‖ *
                ‖orientedWilsonPositiveBase U e‖ :=
              Matrix.l2_opNorm_mul _ _
        _ = ‖orientedWilsonGenerator A e * orientedWilsonGenerator B e +
              orientedWilsonGenerator B e * orientedWilsonGenerator A e‖ *
            1 := by rw [norm_orientedWilsonPositiveBase]
        _ ≤ (2 * ‖orientedWilsonGenerator A e‖ *
            ‖orientedWilsonGenerator B e‖) * 1 := by
              gcongr
              exact norm_orientedWilsonMixedGeneratorNumerator_le A B e
        _ = 2 * ‖orientedWilsonGenerator A e‖ *
            ‖orientedWilsonGenerator B e‖ := by ring
  unfold orientedWilsonFactorMixedSecond
  calc
    ‖(2 : ℂ)⁻¹ • orientedWilsonFactorMixedNumerator U A B e‖
        = ‖(2 : ℂ)⁻¹‖ *
            ‖orientedWilsonFactorMixedNumerator U A B e‖ := norm_smul _ _
    _ = (1 : ℝ) / 2 *
        ‖orientedWilsonFactorMixedNumerator U A B e‖ := by norm_num
    _ ≤ (1 : ℝ) / 2 *
        (2 * ‖orientedWilsonGenerator A e‖ *
          ‖orientedWilsonGenerator B e‖) := by
            gcongr
    _ = ‖orientedWilsonGenerator A e‖ *
        ‖orientedWilsonGenerator B e‖ := by ring

/-- The mixed second variation changes by at most `ε` times the product of
its two generator scales. -/
theorem norm_orientedWilsonFactorMixedSecond_sub_trivial_le
    (U : PhysicalGaugeBackground d N Nc) (ε : ℝ) (hε : 0 ≤ ε)
    (hsmall : PhysicalWilsonSmallBackground U ε)
    (A B : PhysicalGaugeOneCochain d N Nc)
    (e : ConcreteEdge d N) :
    ‖orientedWilsonFactorMixedSecond U A B e -
        orientedWilsonFactorMixedSecond
          (trivialPhysicalGaugeBackground d N Nc) A B e‖ ≤
      ε * (‖orientedWilsonGenerator A e‖ *
        ‖orientedWilsonGenerator B e‖) := by
  let mixed :=
    orientedWilsonGenerator A e * orientedWilsonGenerator B e +
      orientedWilsonGenerator B e * orientedWilsonGenerator A e
  have hnum :
      ‖orientedWilsonFactorMixedNumerator U A B e -
          orientedWilsonFactorMixedNumerator
            (trivialPhysicalGaugeBackground d N Nc) A B e‖ ≤
        2 * ε * (‖orientedWilsonGenerator A e‖ *
          ‖orientedWilsonGenerator B e‖) := by
    rw [orientedWilsonFactorMixedNumerator_eq,
      orientedWilsonFactorMixedNumerator_eq]
    cases h : e.sign
    · simp only [h, Bool.false_eq_true, if_false]
      rw [show
        orientedWilsonBackgroundFactor U e * mixed -
            orientedWilsonBackgroundFactor
                (trivialPhysicalGaugeBackground d N Nc) e * mixed =
          (orientedWilsonBackgroundFactor U e -
            orientedWilsonBackgroundFactor
              (trivialPhysicalGaugeBackground d N Nc) e) * mixed by
            noncomm_ring]
      calc
        ‖(orientedWilsonBackgroundFactor U e -
              orientedWilsonBackgroundFactor
                (trivialPhysicalGaugeBackground d N Nc) e) * mixed‖
            ≤ ‖orientedWilsonBackgroundFactor U e -
                  orientedWilsonBackgroundFactor
                    (trivialPhysicalGaugeBackground d N Nc) e‖ *
                ‖mixed‖ := Matrix.l2_opNorm_mul _ _
        _ ≤ ε * (2 * ‖orientedWilsonGenerator A e‖ *
            ‖orientedWilsonGenerator B e‖) := by
              gcongr
              · exact norm_orientedWilsonBackgroundFactor_sub_trivial_le
                  U ε hsmall e
              · exact norm_orientedWilsonMixedGeneratorNumerator_le A B e
        _ = 2 * ε * (‖orientedWilsonGenerator A e‖ *
            ‖orientedWilsonGenerator B e‖) := by ring
    · simp only [h, if_true]
      rw [show
        mixed * orientedWilsonBackgroundFactor U e -
            mixed * orientedWilsonBackgroundFactor
              (trivialPhysicalGaugeBackground d N Nc) e =
          mixed * (orientedWilsonBackgroundFactor U e -
            orientedWilsonBackgroundFactor
              (trivialPhysicalGaugeBackground d N Nc) e) by noncomm_ring]
      calc
        ‖mixed * (orientedWilsonBackgroundFactor U e -
            orientedWilsonBackgroundFactor
              (trivialPhysicalGaugeBackground d N Nc) e)‖
            ≤ ‖mixed‖ *
                ‖orientedWilsonBackgroundFactor U e -
                  orientedWilsonBackgroundFactor
                    (trivialPhysicalGaugeBackground d N Nc) e‖ :=
              Matrix.l2_opNorm_mul _ _
        _ ≤ (2 * ‖orientedWilsonGenerator A e‖ *
            ‖orientedWilsonGenerator B e‖) * ε := by
              gcongr
              · exact norm_orientedWilsonMixedGeneratorNumerator_le A B e
              · exact norm_orientedWilsonBackgroundFactor_sub_trivial_le
                  U ε hsmall e
        _ = 2 * ε * (‖orientedWilsonGenerator A e‖ *
            ‖orientedWilsonGenerator B e‖) := by ring
  unfold orientedWilsonFactorMixedSecond
  rw [← smul_sub]
  calc
    ‖(2 : ℂ)⁻¹ •
        (orientedWilsonFactorMixedNumerator U A B e -
          orientedWilsonFactorMixedNumerator
            (trivialPhysicalGaugeBackground d N Nc) A B e)‖
        = ‖(2 : ℂ)⁻¹‖ *
            ‖orientedWilsonFactorMixedNumerator U A B e -
              orientedWilsonFactorMixedNumerator
                (trivialPhysicalGaugeBackground d N Nc) A B e‖ :=
          norm_smul _ _
    _ = (1 : ℝ) / 2 *
        ‖orientedWilsonFactorMixedNumerator U A B e -
          orientedWilsonFactorMixedNumerator
            (trivialPhysicalGaugeBackground d N Nc) A B e‖ := by norm_num
    _ ≤ (1 : ℝ) / 2 *
        (2 * ε * (‖orientedWilsonGenerator A e‖ *
          ‖orientedWilsonGenerator B e‖)) := by
            gcongr
    _ = ε * (‖orientedWilsonGenerator A e‖ *
        ‖orientedWilsonGenerator B e‖) := by ring

end

end YangMills.RG
