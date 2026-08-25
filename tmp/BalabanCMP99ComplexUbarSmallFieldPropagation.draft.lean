import YangMills.RG.BalabanCMP99Eq337PhysicalComplexUbarDeviationRadius
import YangMills.RG.BalabanCMP99ComplexInverseRadius
import YangMills.RG.BalabanCMP99SourceUbarSmallFieldPropagation

/-!
PRE-VALIDATION: this scratch source has no materialized `.olean` and no
compiler or axiom-oracle verdict.

# Propagate a literal complex Ubar link radius

This module derives the small-field estimate for the `SL(N,C)` background
constructed by the source-facing Eq. (3.37) step.  Unlike the physical
`SU(N)` estimate, multiplication by the coarse Wilson line is not isometric:
its explicit `(1 + r)^M` norm remains visible in the output radius.

This is the missing producer needed before a forced finite complex recursion
can be defined without accepting per-scale small-field hypotheses.
-/

namespace YangMills.RG

open YangMills YangMills.GaugeConfig Matrix
open scoped Matrix.Norms.L2Operator BigOperators

noncomputable section

variable {Nc : ℕ} [NeZero Nc]

local instance matrixL2CStarAlgebraForComplexSourcePropagation :
    CStarAlgebra (Matrix (Fin Nc) (Fin Nc) ℂ) where

local instance matrixRealComplexScalarTowerForComplexSourcePropagation :
    IsScalarTower ℝ ℂ (Matrix (Fin Nc) (Fin Nc) ℂ) where
  smul_assoc r c X := by
    ext i j
    exact smul_assoc r c (X i j)

/-- The convex complex Ubar exponent obeys the same Mercator radius as the
unitary exponent.  Determinant one, rather than unitarity, is used only to
package the exponential back into `SL(N,C)` and is irrelevant to this norm
estimate. -/
theorem norm_cmp99UbarSpecialLinearExponent_le_logRadius
    {ι : Type} (s : Finset ι) (w : ι → ℝ)
    (D : ι → Matrix.SpecialLinearGroup (Fin Nc) ℂ)
    (B : MatrixNearLogNoWindingBudget Nc)
    (hdev : ∀ i ∈ s,
      ‖(D i : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ B.δ)
    (hw_nonneg : ∀ i ∈ s, 0 ≤ w i)
    (hw_sum : ∑ i ∈ s, w i = 1) :
    ‖cmp99UbarSpecialLinearExponent s w D‖ ≤ cmp99UbarLogRadius B := by
  unfold cmp99UbarSpecialLinearExponent
  calc
    ‖∑ i ∈ s, w i •
        nearLog ((D i : Matrix (Fin Nc) (Fin Nc) ℂ) - 1)‖
        ≤ ∑ i ∈ s, ‖w i •
          nearLog ((D i : Matrix (Fin Nc) (Fin Nc) ℂ) - 1)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i ∈ s, w i * cmp99UbarLogRadius B := by
      apply Finset.sum_le_sum
      intro i hi
      have hsmul :
          w i • nearLog ((D i : Matrix (Fin Nc) (Fin Nc) ℂ) - 1) =
            (w i : ℂ) •
              nearLog ((D i : Matrix (Fin Nc) (Fin Nc) ℂ) - 1) := by
        ext p q
        simp [RCLike.real_smul_eq_coe_mul]
      rw [hsmul, norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hw_nonneg i hi)]
      exact mul_le_mul_of_nonneg_left
        (norm_nearLog_le_div_of_norm_le B.δ_lt_one (hdev i hi))
        (hw_nonneg i hi)
    _ = cmp99UbarLogRadius B := by
      rw [← Finset.sum_mul, hw_sum, one_mul]

/-- The determinant-one complex exponential factor remains explicitly close
to one.  This is the Banach-algebra estimate and does not use norm one. -/
theorem norm_cmp99UbarSpecialLinearFactorOfDeviationBudget_sub_one_le
    {ι : Type} (s : Finset ι) (w : ι → ℝ)
    (D : ι → Matrix.SpecialLinearGroup (Fin Nc) ℂ)
    (B : MatrixNearLogNoWindingBudget Nc)
    (hdev : ∀ i ∈ s,
      ‖(D i : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ B.δ)
    (hw_nonneg : ∀ i ∈ s, 0 ≤ w i)
    (hw_sum : ∑ i ∈ s, w i = 1)
    (hlog : cmp99UbarLogRadius B < 1) :
    ‖(cmp99UbarSpecialLinearFactorOfDeviationBudget
        s w D B hdev : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤
      cmp99UbarExpRadius B := by
  let Z := cmp99UbarSpecialLinearExponent s w D
  have hZ : ‖Z‖ ≤ cmp99UbarLogRadius B :=
    norm_cmp99UbarSpecialLinearExponent_le_logRadius
      s w D B hdev hw_nonneg hw_sum
  have hZlt : ‖Z‖ < 1 := lt_of_le_of_lt hZ hlog
  have hlog_nonneg : 0 ≤ cmp99UbarLogRadius B :=
    le_trans (norm_nonneg Z) hZ
  have hdenZ : 0 < 1 - ‖Z‖ := sub_pos.mpr hZlt
  have hdenLog : 0 < 1 - cmp99UbarLogRadius B := sub_pos.mpr hlog
  rw [cmp99UbarSpecialLinearFactorOfDeviationBudget_coe]
  change ‖NormedSpace.exp Z - 1‖ ≤ cmp99UbarExpRadius B
  calc
    ‖NormedSpace.exp Z - 1‖
        = ‖(NormedSpace.exp Z - 1 - Z) + Z‖ := by congr 1; abel
    _ ≤ ‖NormedSpace.exp Z - 1 - Z‖ + ‖Z‖ := norm_add_le _ _
    _ ≤ ‖Z‖ ^ 2 / (1 - ‖Z‖) + ‖Z‖ := by
      gcongr
      exact norm_exp_sub_one_sub_self_le hZlt
    _ ≤ cmp99UbarLogRadius B ^ 2 /
          (1 - cmp99UbarLogRadius B) + cmp99UbarLogRadius B := by
      apply add_le_add _ hZ
      calc
        ‖Z‖ ^ 2 / (1 - ‖Z‖) ≤
            cmp99UbarLogRadius B ^ 2 / (1 - ‖Z‖) := by
          exact div_le_div_of_nonneg_right
            (sq_le_sq₀ (norm_nonneg Z) hlog_nonneg |>.2 hZ)
            hdenZ.le
        _ ≤ cmp99UbarLogRadius B ^ 2 /
            (1 - cmp99UbarLogRadius B) := by
          exact div_le_div_of_nonneg_left (sq_nonneg _)
            hdenLog (by linarith)
    _ = cmp99UbarExpRadius B := by
      rw [cmp99UbarExpRadius]
      ring

/-- Exact visible radius after multiplying the complex Ubar factor by its
length-`M` coarse source Wilson line. -/
def cmp99SourceComplexUbarNextLinkRadius
    (M : ℕ) (r : ℝ) (B : MatrixNearLogNoWindingBudget Nc) : ℝ :=
  cmp99UbarExpRadius B * (1 + r) ^ M +
    (M : ℝ) * r * (1 + r) ^ M

/-- Radius on both orientations after paying the non-unitary inverse loss. -/
def cmp99SourceComplexUbarNextOrientedLinkRadius
    (M : ℕ) (r : ℝ) (B : MatrixNearLogNoWindingBudget Nc) : ℝ :=
  let q := cmp99SourceComplexUbarNextLinkRadius M r B
  q / (1 - q)

variable {d M N' : ℕ} [NeZero d] [NeZero M] [NeZero N']

/-- A uniform complex oriented-link radius controls the literal four-path
source deviation without exposing a free deviation family. -/
theorem norm_cmp99SourceComplexLocalizedUbarDeviation_le_uniformRadius_of_linkRadius
    (hd : 2 ≤ d) (hM : 2 ≤ M)
    (background : GaugeConfig d (M * N')
      (Matrix.SpecialLinearGroup (Fin Nc) ℂ))
    (r : ℝ) (hr : 0 ≤ r)
    (hlink : ∀ e,
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ r)
    (b : PhysicalBond d N') (x : FinBox d (M * N'))
    (hx : x ∈ blockOf M N' b.1) :
    ‖(cmp99SourceComplexLocalizedUbarDeviation background b x :
        Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤
      cmp99Eq337SourceComplexUbarUniformDeviationRadius d M r := by
  calc
    _ ≤ cmp99ComplexFourWilsonPathDeviationBudget
        (cmp99SourceComplexUbarFourPaths (Nc := Nc) b x) r :=
      norm_cmp99SourceComplexLocalizedUbarDeviation_le_fourPathBudget
        background r hr hlink b x
    _ ≤ cmp99Eq337SourceComplexUbarUniformDeviationRadius d M r := by
      exact cmp99ComplexFourWilsonPathDeviationBudget_le_uniform
        (cmp99SourceComplexUbarFourPaths (Nc := Nc) b x)
        (d * (M - 1)) r hr
        (cmp99SourceComplexUbarFourPaths_length_le hd hM b x hx)

/-- The generic complex no-winding budget generated by the literal four-path
radius. -/
noncomputable def cmp99SourceComplexUbarNoWindingBudget
    (d M Nc : ℕ) [NeZero Nc] (r : ℝ)
    (hnoWinding :
      cmp99Eq337SourceComplexUbarUniformDeviationRadius d M r <
        cmp99UbarNoWindingThreshold Nc) :
    MatrixNearLogNoWindingBudget Nc :=
  cmp99PhysicalNoWindingBudget
    (cmp99Eq337SourceComplexUbarUniformDeviationRadius d M r) hnoWinding

@[simp] theorem cmp99SourceComplexUbarNoWindingBudget_delta
    (d M Nc : ℕ) [NeZero Nc] (r : ℝ) (hnoWinding) :
    (cmp99SourceComplexUbarNoWindingBudget
      d M Nc r hnoWinding).δ =
      cmp99Eq337SourceComplexUbarUniformDeviationRadius d M r := by
  rfl

/-- The three scalar gates needed by one complex recursive step are jointly
inhabited.  This zero-radius witness is a vacuity check for the future scalar
chain; it is not a claim that the physical Eq. (3.37) input has zero radius. -/
theorem exists_cmp99SourceComplexUbar_zero_step_gates
    (d M Nc : ℕ) [NeZero Nc] :
    ∃ hnoWinding :
        cmp99Eq337SourceComplexUbarUniformDeviationRadius d M 0 <
          cmp99UbarNoWindingThreshold Nc,
      cmp99UbarLogRadius
          (cmp99SourceComplexUbarNoWindingBudget
            d M Nc 0 hnoWinding) < 1 ∧
      cmp99SourceComplexUbarNextLinkRadius M 0
          (cmp99SourceComplexUbarNoWindingBudget
            d M Nc 0 hnoWinding) < 1 ∧
      cmp99SourceComplexUbarNextOrientedLinkRadius M 0
          (cmp99SourceComplexUbarNoWindingBudget
            d M Nc 0 hnoWinding) = 0 := by
  have hthreshold : 0 < cmp99UbarNoWindingThreshold Nc := by
    rw [cmp99UbarNoWindingThreshold]
    positivity
  have hzero :
      cmp99Eq337SourceComplexUbarUniformDeviationRadius d M 0 = 0 := by
    simp [cmp99Eq337SourceComplexUbarUniformDeviationRadius,
      cmp99ComplexFourWilsonUniformDeviationBudget,
      cmp99ComplexFourFactorDeviationBudget]
  have hnoWinding :
      cmp99Eq337SourceComplexUbarUniformDeviationRadius d M 0 <
        cmp99UbarNoWindingThreshold Nc := by
    simpa [hzero] using hthreshold
  refine ⟨hnoWinding, ?_, ?_, ?_⟩
  · simp [cmp99UbarLogRadius,
      cmp99SourceComplexUbarNoWindingBudget_delta, hzero]
  · simp [cmp99SourceComplexUbarNextLinkRadius, cmp99UbarExpRadius,
      cmp99UbarLogRadius, cmp99SourceComplexUbarNoWindingBudget_delta,
      hzero]
  · simp [cmp99SourceComplexUbarNextOrientedLinkRadius,
      cmp99SourceComplexUbarNextLinkRadius, cmp99UbarExpRadius,
      cmp99UbarLogRadius, cmp99SourceComplexUbarNoWindingBudget_delta,
      hzero]

/-- One literal complex source Ubar block is small at the explicit next
radius.  The two terms in the conclusion are respectively the exponential
factor times the coarse-factor norm and the coarse-factor deviation. -/
theorem norm_cmp99SourceComplexLocalizedUbarBlock_sub_one_le
    (background : GaugeConfig d (M * N')
      (Matrix.SpecialLinearGroup (Fin Nc) ℂ))
    (r : ℝ) (hr : 0 ≤ r)
    (hlink : ∀ e,
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ r)
    (B : MatrixNearLogNoWindingBudget Nc)
    (hdev : ∀ b x, x ∈ blockOf M N' b.1 →
      ‖(cmp99SourceComplexLocalizedUbarDeviation background b x :
          Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ B.δ)
    (hlog : cmp99UbarLogRadius B < 1)
    (b : PhysicalBond d N') :
    ‖(cmp99SourceComplexLocalizedUbarBlock background B hdev b :
        Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤
      cmp99SourceComplexUbarNextLinkRadius M r B := by
  let S := blockOf M N' b.1
  let D : FinBox d (M * N') →
      Matrix.SpecialLinearGroup (Fin Nc) ℂ :=
    cmp99SourceComplexLocalizedUbarDeviation background b
  let F := cmp99UbarSpecialLinearFactorOfDeviationBudget S
    (fun _ ↦ cmp99SourceBlockAverageWeight M d) D B (hdev b)
  let C := cmp99SourceBaseCoarseBackground background
    (positiveEdgeOfPhysicalBond b)
  have hF : ‖(F : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤
      cmp99UbarExpRadius B := by
    exact norm_cmp99UbarSpecialLinearFactorOfDeviationBudget_sub_one_le
      S (fun _ ↦ cmp99SourceBlockAverageWeight M d) D B (hdev b)
      (fun _ _ ↦ inv_nonneg.mpr (pow_nonneg (Nat.cast_nonneg M) d))
      (sum_cmp99SourceBlockAverageWeight_blockOf (M := M) b.1) hlog
  have hF_nonneg : 0 ≤ cmp99UbarExpRadius B :=
    le_trans (norm_nonneg ((F : Matrix (Fin Nc) (Fin Nc) ℂ) - 1)) hF
  have hCnorm : ‖(C : Matrix (Fin Nc) (Fin Nc) ℂ)‖ ≤
      (1 + r) ^ M := by
    simpa [C, cmp99SourceBaseCoarseBackground_apply_pos,
      cmp99SourceParallelTransportPath_length] using
      norm_cmp99SpecialLinearWilsonLine_le background
        (cmp99SourceParallelTransportPath
          (G := Matrix.SpecialLinearGroup (Fin Nc) ℂ)
          (blockBasepoint M N' b.1) b.2).edges r hr hlink
  have hCdev : ‖(C : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤
      (M : ℝ) * r * (1 + r) ^ M := by
    simpa [C, cmp99SourceBaseCoarseBackground_apply_pos,
      cmp99SourceParallelTransportPath_length] using
      norm_cmp99SpecialLinearWilsonLine_sub_one_le background
        (cmp99SourceParallelTransportPath
          (G := Matrix.SpecialLinearGroup (Fin Nc) ℂ)
          (blockBasepoint M N' b.1) b.2).edges r hr hlink
  rw [cmp99SourceComplexLocalizedUbarBlock,
    cmp99UbarSpecialLinearBlockOfDeviationBudget_coe]
  change ‖(F : Matrix (Fin Nc) (Fin Nc) ℂ) *
      (C : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ _
  rw [show (F : Matrix (Fin Nc) (Fin Nc) ℂ) *
      (C : Matrix (Fin Nc) (Fin Nc) ℂ) - 1 =
        ((F : Matrix (Fin Nc) (Fin Nc) ℂ) - 1) *
          (C : Matrix (Fin Nc) (Fin Nc) ℂ) +
        ((C : Matrix (Fin Nc) (Fin Nc) ℂ) - 1) by
    noncomm_ring]
  calc
    _ ≤ ‖(F : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ *
          ‖(C : Matrix (Fin Nc) (Fin Nc) ℂ)‖ +
        ‖(C : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ := by
      exact (norm_add_le _ _).trans
        (add_le_add (norm_mul_le _ _) le_rfl)
    _ ≤ cmp99UbarExpRadius B * (1 + r) ^ M +
        (M : ℝ) * r * (1 + r) ^ M := by
      exact add_le_add
        (mul_le_mul hF hCnorm (norm_nonneg _) hF_nonneg) hCdev
    _ = cmp99SourceComplexUbarNextLinkRadius M r B := rfl

/-- The complete positive-bond next complex background inherits the same
explicit radius.  The negative orientation producer remains a separate gate:
inversion in `SL(N,C)` is not an isometry. -/
theorem norm_cmp99SourceComplexLocalizedNextBackground_apply_pos_sub_one_le
    (background : GaugeConfig d (M * N')
      (Matrix.SpecialLinearGroup (Fin Nc) ℂ))
    (r : ℝ) (hr : 0 ≤ r)
    (hlink : ∀ e,
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ r)
    (B : MatrixNearLogNoWindingBudget Nc)
    (hdev : ∀ b x, x ∈ blockOf M N' b.1 →
      ‖(cmp99SourceComplexLocalizedUbarDeviation background b x :
          Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ B.δ)
    (hlog : cmp99UbarLogRadius B < 1)
    (b : PhysicalBond d N') :
    ‖(cmp99SourceComplexLocalizedNextBackground background B hdev
        (positiveEdgeOfPhysicalBond b) :
          Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤
      cmp99SourceComplexUbarNextLinkRadius M r B := by
  rw [cmp99SourceComplexLocalizedNextBackground_apply_pos]
  exact norm_cmp99SourceComplexLocalizedUbarBlock_sub_one_le
    background r hr hlink B hdev hlog b

/-- The complete complex next background is uniformly small on every
oriented link.  The strict positive-edge gate is consumed internally to pay
the exact inverse radius on negative links. -/
theorem norm_cmp99SourceComplexLocalizedNextBackground_sub_one_le
    (background : GaugeConfig d (M * N')
      (Matrix.SpecialLinearGroup (Fin Nc) ℂ))
    (r : ℝ) (hr : 0 ≤ r)
    (hlink : ∀ e,
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ r)
    (B : MatrixNearLogNoWindingBudget Nc)
    (hdev : ∀ b x, x ∈ blockOf M N' b.1 →
      ‖(cmp99SourceComplexLocalizedUbarDeviation background b x :
          Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ B.δ)
    (hlog : cmp99UbarLogRadius B < 1)
    (hq1 : cmp99SourceComplexUbarNextLinkRadius M r B < 1)
    (e : ConcreteEdge d N') :
    ‖(cmp99SourceComplexLocalizedNextBackground background B hdev e :
        Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤
      cmp99SourceComplexUbarNextOrientedLinkRadius M r B := by
  let q := cmp99SourceComplexUbarNextLinkRadius M r B
  have hq0 : 0 ≤ q := by
    have hblock := norm_cmp99SourceComplexLocalizedUbarBlock_sub_one_le
      background r hr hlink B hdev hlog
        ((0, 0) : PhysicalBond d N')
    exact (norm_nonneg
      ((cmp99SourceComplexLocalizedUbarBlock background B hdev
        ((0, 0) : PhysicalBond d N') :
          Matrix (Fin Nc) (Fin Nc) ℂ) - 1)).trans (by
            simpa [q] using hblock)
  have hqden : 0 < 1 - q := sub_pos.mpr hq1
  have hq_le : q ≤ q / (1 - q) := by
    rw [le_div_iff₀ hqden]
    nlinarith
  rcases e with ⟨y, mu, orient⟩
  cases orient with
  | false =>
      rw [cmp99SourceComplexLocalizedNextBackground,
        gaugeConfigOfPositiveBonds_apply_neg]
      simpa [q, cmp99SourceComplexUbarNextOrientedLinkRadius] using
        norm_cmp99SpecialLinear_inv_sub_one_le_div
          (cmp99SourceComplexLocalizedUbarBlock background B hdev (y, mu))
          q hq0 hq1
          (norm_cmp99SourceComplexLocalizedUbarBlock_sub_one_le
            background r hr hlink B hdev hlog (y, mu))
  | true =>
      simpa [q, cmp99SourceComplexUbarNextOrientedLinkRadius] using
        (norm_cmp99SourceComplexLocalizedNextBackground_apply_pos_sub_one_le
          background r hr hlink B hdev hlog (y, mu)).trans hq_le

/-- One generic complex source RG step constructed solely from an oriented
fine-link radius and the literal no-winding gate.  No deviation family or
coarse background is caller data. -/
noncomputable def cmp99SourceComplexLocalizedNextBackgroundOfLinkRadius
    (hd : 2 ≤ d) (hM : 2 ≤ M)
    (background : GaugeConfig d (M * N')
      (Matrix.SpecialLinearGroup (Fin Nc) ℂ))
    (r : ℝ) (hr : 0 ≤ r)
    (hlink : ∀ e,
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ r)
    (hnoWinding :
      cmp99Eq337SourceComplexUbarUniformDeviationRadius d M r <
        cmp99UbarNoWindingThreshold Nc) :
    GaugeConfig d N' (Matrix.SpecialLinearGroup (Fin Nc) ℂ) := by
  let B := cmp99SourceComplexUbarNoWindingBudget
    d M Nc r hnoWinding
  exact cmp99SourceComplexLocalizedNextBackground background B (by
    intro b x hx
    change ‖(cmp99SourceComplexLocalizedUbarDeviation background b x :
      Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ B.δ
    rw [show B.δ =
        cmp99Eq337SourceComplexUbarUniformDeviationRadius d M r by rfl]
    exact
      norm_cmp99SourceComplexLocalizedUbarDeviation_le_uniformRadius_of_linkRadius
        hd hM background r hr hlink b x hx)

/-- The generic source step internally discharges the literal deviation
family and inherits the all-orientation inverse radius. -/
theorem norm_cmp99SourceComplexLocalizedNextBackgroundOfLinkRadius_sub_one_le
    (hd : 2 ≤ d) (hM : 2 ≤ M)
    (background : GaugeConfig d (M * N')
      (Matrix.SpecialLinearGroup (Fin Nc) ℂ))
    (r : ℝ) (hr : 0 ≤ r)
    (hlink : ∀ e,
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ r)
    (hnoWinding :
      cmp99Eq337SourceComplexUbarUniformDeviationRadius d M r <
        cmp99UbarNoWindingThreshold Nc)
    (hlog : cmp99UbarLogRadius
      (cmp99SourceComplexUbarNoWindingBudget d M Nc r hnoWinding) < 1)
    (hq1 : cmp99SourceComplexUbarNextLinkRadius M r
      (cmp99SourceComplexUbarNoWindingBudget d M Nc r hnoWinding) < 1)
    (e : ConcreteEdge d N') :
    ‖(cmp99SourceComplexLocalizedNextBackgroundOfLinkRadius
        hd hM background r hr hlink hnoWinding e :
          Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤
      cmp99SourceComplexUbarNextOrientedLinkRadius M r
        (cmp99SourceComplexUbarNoWindingBudget
          d M Nc r hnoWinding) := by
  let B := cmp99SourceComplexUbarNoWindingBudget
    d M Nc r hnoWinding
  let hdev : ∀ b x, x ∈ blockOf M N' b.1 →
      ‖(cmp99SourceComplexLocalizedUbarDeviation background b x :
          Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ B.δ := by
    intro b x hx
    rw [show B.δ =
        cmp99Eq337SourceComplexUbarUniformDeviationRadius d M r by rfl]
    exact
      norm_cmp99SourceComplexLocalizedUbarDeviation_le_uniformRadius_of_linkRadius
        hd hM background r hr hlink b x hx
  change ‖(cmp99SourceComplexLocalizedNextBackground background B hdev e :
      Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ _
  exact norm_cmp99SourceComplexLocalizedNextBackground_sub_one_le
    background r hr hlink B hdev hlog hq1 e

end

end YangMills.RG
