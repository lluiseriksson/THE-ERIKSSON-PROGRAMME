import Mathlib
import YangMills.RG.BalabanCMP116WilsonHessianUnitaryChart

/-!
# Differential structure of the literal Wilson Hessian

This module extends the physical unitary chart to an ambient real matrix chart.
The extension is used only to obtain a genuine Fréchet second derivative.  On
skew-Hermitian physical directions it is the same matrix curve as the unitary
chart.  The construction makes bilinearity definitional and obtains Hessian
symmetry from analyticity, rather than postulating either property.
-/

namespace YangMills.RG

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

noncomputable section

variable {d N Nc : ℕ} [NeZero d] [NeZero N] [NeZero Nc]

/-- Ambient real matrix coordinates, one matrix per positive physical bond. -/
abbrev PhysicalAmbientMatrixTangent (d N Nc : ℕ) [NeZero N] :=
  PhysicalBond d N → Matrix (Fin Nc) (Fin Nc) ℂ

/-- Evaluation of one physical-bond coordinate as a continuous real-linear
map. -/
def physicalAmbientBondEvalCLM (b : PhysicalBond d N) :
    PhysicalAmbientMatrixTangent d N Nc →L[ℝ] Matrix (Fin Nc) (Fin Nc) ℂ :=
  ContinuousLinearMap.proj b

/-- Conjugate transpose as a continuous real-linear map for the matrix norm
used by the repository. -/
def matrixConjTransposeCLM :
    Matrix (Fin Nc) (Fin Nc) ℂ →L[ℝ] Matrix (Fin Nc) (Fin Nc) ℂ :=
  (Matrix.conjTransposeLinearEquiv (Fin Nc) (Fin Nc) ℝ ℂ).toLinearMap.mkContinuous
    1 fun A => by
      simpa using le_of_eq (Matrix.l2_opNorm_conjTranspose A)

@[simp]
theorem matrixConjTransposeCLM_apply (A : Matrix (Fin Nc) (Fin Nc) ℂ) :
    matrixConjTransposeCLM A = Aᴴ := by
  rfl

/-- One matrix entry as a continuous real-linear functional. -/
def matrixEntryCLM (i j : Fin Nc) :
    Matrix (Fin Nc) (Fin Nc) ℂ →L[ℝ] ℂ :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin Nc => ℂ) j).comp
    (ContinuousLinearMap.proj (R := ℝ)
      (φ := fun _ : Fin Nc => Fin Nc → ℂ) i)

@[simp]
theorem matrixEntryCLM_apply (i j : Fin Nc)
    (A : Matrix (Fin Nc) (Fin Nc) ℂ) : matrixEntryCLM i j A = A i j := by
  rfl

/-- Analyticity of the matrix exponential after evaluation at one physical
bond. -/
theorem analyticAt_physicalMatrixExp_eval
    (Z : PhysicalAmbientMatrixTangent d N Nc) (b : PhysicalBond d N) :
    AnalyticAt ℝ (fun W => physicalMatrixExp (W b)) Z := by
  letI : IsTopologicalRing (Matrix (Fin Nc) (Fin Nc) ℂ) :=
    physicalMatrixTopologicalRing Nc
  have heval : AnalyticAt ℝ
      (fun W : PhysicalAmbientMatrixTangent d N Nc => W b) Z :=
    (physicalAmbientBondEvalCLM b).analyticAt Z
  have hexp : AnalyticAt ℝ
      (fun A : Matrix (Fin Nc) (Fin Nc) ℂ => NormedSpace.exp A) (Z b) :=
    NormedSpace.exp_analytic (Z b)
  simpa only [physicalMatrixExp, Function.comp_apply] using
    hexp.comp (f := fun W : PhysicalAmbientMatrixTangent d N Nc => W b) heval

/-- The varied positive-bond matrix in the ambient chart. -/
def ambientPositiveBondMatrix
    (U : PhysicalGaugeBackground d N Nc)
    (Z : PhysicalAmbientMatrixTangent d N Nc) (b : PhysicalBond d N) :
    Matrix (Fin Nc) (Fin Nc) ℂ :=
  physicalMatrixExp (Z b) * (U (positiveEdgeOfPhysicalBond b)).val

theorem analyticAt_ambientPositiveBondMatrix
    (U : PhysicalGaugeBackground d N Nc)
    (Z : PhysicalAmbientMatrixTangent d N Nc) (b : PhysicalBond d N) :
    AnalyticAt ℝ (fun W => ambientPositiveBondMatrix U W b) Z := by
  exact (analyticAt_physicalMatrixExp_eval Z b).mul analyticAt_const

/-- Oriented edge matrix in the ambient chart.  Negative orientations are
reconstructed by conjugate transpose.  On the physical skew-adjoint chart this
is the inverse of the positive unitary edge. -/
def ambientOrientedEdgeMatrix
    (U : PhysicalGaugeBackground d N Nc)
    (Z : PhysicalAmbientMatrixTangent d N Nc) (e : ConcreteEdge d N) :
    Matrix (Fin Nc) (Fin Nc) ℂ :=
  if e.sign then
    ambientPositiveBondMatrix U Z (physicalBondOfEdge e)
  else
    (ambientPositiveBondMatrix U Z (physicalBondOfEdge e))ᴴ

theorem analyticAt_ambientOrientedEdgeMatrix
    (U : PhysicalGaugeBackground d N Nc)
    (Z : PhysicalAmbientMatrixTangent d N Nc) (e : ConcreteEdge d N) :
    AnalyticAt ℝ (fun W => ambientOrientedEdgeMatrix U W e) Z := by
  by_cases h : e.sign
  · simp only [ambientOrientedEdgeMatrix, h, if_true]
    exact analyticAt_ambientPositiveBondMatrix U Z (physicalBondOfEdge e)
  · simp only [ambientOrientedEdgeMatrix, h, if_false]
    have hpos : AnalyticAt ℝ
        (fun W : PhysicalAmbientMatrixTangent d N Nc =>
          ambientPositiveBondMatrix U W (physicalBondOfEdge e)) Z :=
      analyticAt_ambientPositiveBondMatrix U Z (physicalBondOfEdge e)
    have hstar : AnalyticAt ℝ
        (fun A : Matrix (Fin Nc) (Fin Nc) ℂ => Aᴴ)
        (ambientPositiveBondMatrix U Z (physicalBondOfEdge e)) := by
      simpa only [matrixConjTransposeCLM_apply] using
        matrixConjTransposeCLM.analyticAt
          (ambientPositiveBondMatrix U Z (physicalBondOfEdge e))
    simpa only [Function.comp_apply] using
      hstar.comp
        (f := fun W : PhysicalAmbientMatrixTangent d N Nc =>
          ambientPositiveBondMatrix U W (physicalBondOfEdge e)) hpos

/-- Four-edge plaquette product in the ambient chart. -/
def ambientPlaquetteHolonomy
    (U : PhysicalGaugeBackground d N Nc)
    (Z : PhysicalAmbientMatrixTangent d N Nc)
    (p : ConcretePlaquette d N) : Matrix (Fin Nc) (Fin Nc) ℂ :=
  ((ambientOrientedEdgeMatrix U Z (p.edges 0) *
      ambientOrientedEdgeMatrix U Z (p.edges 1)) *
    ambientOrientedEdgeMatrix U Z (p.edges 2)) *
      ambientOrientedEdgeMatrix U Z (p.edges 3)

theorem analyticAt_ambientPlaquetteHolonomy
    (U : PhysicalGaugeBackground d N Nc)
    (Z : PhysicalAmbientMatrixTangent d N Nc)
    (p : ConcretePlaquette d N) :
    AnalyticAt ℝ (fun W => ambientPlaquetteHolonomy U W p) Z := by
  exact (((analyticAt_ambientOrientedEdgeMatrix U Z (p.edges 0)).mul
    (analyticAt_ambientOrientedEdgeMatrix U Z (p.edges 1))).mul
      (analyticAt_ambientOrientedEdgeMatrix U Z (p.edges 2))).mul
        (analyticAt_ambientOrientedEdgeMatrix U Z (p.edges 3))

/-- Real trace written entrywise, convenient for real analyticity. -/
def ambientTraceReal (A : Matrix (Fin Nc) (Fin Nc) ℂ) : ℝ :=
  ∑ i : Fin Nc, (A i i).re

theorem ambientTraceReal_eq (A : Matrix (Fin Nc) (Fin Nc) ℂ) :
    ambientTraceReal A = (Matrix.trace A).re := by
  simp [ambientTraceReal, Matrix.trace]

theorem analyticAt_ambientTraceReal_comp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → Matrix (Fin Nc) (Fin Nc) ℂ) (x : E)
    (hf : AnalyticAt ℝ f x) :
    AnalyticAt ℝ (fun y => ambientTraceReal (f y)) x := by
  simp only [ambientTraceReal]
  exact Finset.analyticAt_fun_sum Finset.univ (fun i _ => by
      have hentry : AnalyticAt ℝ (fun y => f y i i) x := by
        have he : AnalyticAt ℝ
            (fun A : Matrix (Fin Nc) (Fin Nc) ℂ => A i i) (f x) := by
          simpa only [matrixEntryCLM_apply] using
            (matrixEntryCLM i i).analyticAt (f x)
        simpa only [Function.comp_apply] using he.comp (f := f) hf
      have hre : AnalyticAt ℝ (fun z : ℂ => z.re) (f x i i) := by
        exact Complex.reCLM.analyticAt (f x i i)
      simpa only [Function.comp_apply] using
        hre.comp (f := fun y : E => f y i i) hentry)

/-- One real Wilson plaquette term in ambient matrix coordinates. -/
def ambientWilsonPlaquetteAction
    (U : PhysicalGaugeBackground d N Nc)
    (Z : PhysicalAmbientMatrixTangent d N Nc)
    (p : ConcretePlaquette d N) : ℝ :=
  ambientTraceReal (ambientPlaquetteHolonomy U Z p)

theorem analyticAt_ambientWilsonPlaquetteAction
    (U : PhysicalGaugeBackground d N Nc)
    (Z : PhysicalAmbientMatrixTangent d N Nc)
    (p : ConcretePlaquette d N) :
    AnalyticAt ℝ (fun W => ambientWilsonPlaquetteAction U W p) Z := by
  exact analyticAt_ambientTraceReal_comp _ Z
    (analyticAt_ambientPlaquetteHolonomy U Z p)

/-- Finite Wilson action in the ambient matrix chart. -/
def ambientWilsonAction
    (U : PhysicalGaugeBackground d N Nc)
    (Z : PhysicalAmbientMatrixTangent d N Nc) : ℝ :=
  ∑ p : ConcretePlaquette d N, ambientWilsonPlaquetteAction U Z p

theorem analyticAt_ambientWilsonAction
    (U : PhysicalGaugeBackground d N Nc)
    (Z : PhysicalAmbientMatrixTangent d N Nc) :
    AnalyticAt ℝ (ambientWilsonAction U) Z := by
  exact Finset.analyticAt_fun_sum Finset.univ
    (fun p _ => analyticAt_ambientWilsonPlaquetteAction U Z p)

/-- The literal Fréchet Hessian of the ambient Wilson chart at the physical
background.  No Hessian matrix is supplied as data. -/
def ambientWilsonHessian
    (U : PhysicalGaugeBackground d N Nc) :
    PhysicalAmbientMatrixTangent d N Nc →L[ℝ]
      PhysicalAmbientMatrixTangent d N Nc →L[ℝ] ℝ :=
  fderiv ℝ (fderiv ℝ (ambientWilsonAction U)) 0

/-- Bilinearity in the first direction is inherited from the Fréchet second
derivative. -/
theorem ambientWilsonHessian_add_left
    (U : PhysicalGaugeBackground d N Nc)
    (X Y Z : PhysicalAmbientMatrixTangent d N Nc) :
    ambientWilsonHessian U (X + Y) Z =
      ambientWilsonHessian U X Z + ambientWilsonHessian U Y Z := by
  exact (ambientWilsonHessian U).map_add X Y ▸ rfl

/-- Bilinearity in the second direction is inherited from the inner
continuous linear map. -/
theorem ambientWilsonHessian_add_right
    (U : PhysicalGaugeBackground d N Nc)
    (X Y Z : PhysicalAmbientMatrixTangent d N Nc) :
    ambientWilsonHessian U X (Y + Z) =
      ambientWilsonHessian U X Y + ambientWilsonHessian U X Z := by
  exact (ambientWilsonHessian U X).map_add Y Z

/-- Symmetry of the literal Wilson Hessian follows from analyticity of the
finite-dimensional chart. -/
theorem ambientWilsonHessian_symm
    (U : PhysicalGaugeBackground d N Nc)
    (X Y : PhysicalAmbientMatrixTangent d N Nc) :
    ambientWilsonHessian U X Y = ambientWilsonHessian U Y X := by
  have hc : ContDiffAt ℝ (2 : WithTop ℕ∞) (ambientWilsonAction U) 0 :=
    (analyticAt_ambientWilsonAction U 0).contDiffAt
  have hs : IsSymmSndFDerivAt ℝ (ambientWilsonAction U) 0 :=
    hc.isSymmSndFDerivAt (by norm_num [minSmoothness])
  simpa only [ambientWilsonHessian] using hs.eq X Y

/-- For an everywhere analytic scalar function, the nested directional
derivative along `(t,s) ↦ tX+sY` is its Fréchet Hessian applied to `(X,Y)`. -/
theorem nested_deriv_line_eq_sndFDeriv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (hf : ∀ z, AnalyticAt ℝ f z) (X Y : E) :
    deriv (fun t : ℝ => deriv (fun s : ℝ => f (t • X + s • Y)) 0) 0 =
      (fderiv ℝ (fderiv ℝ f) 0) X Y := by
  have hinner : ∀ t : ℝ,
      deriv (fun s : ℝ => f (t • X + s • Y)) 0 =
        (fderiv ℝ f (t • X)) Y := by
    intro t
    have hline : HasDerivAt (fun s : ℝ => t • X + s • Y) Y 0 := by
      convert (hasDerivAt_const (𝕜 := ℝ) 0 (t • X)).add
        ((hasDerivAt_id (𝕜 := ℝ) 0).smul_const Y) using 1 <;> simp
    have hcomp :=
      (hf (t • X + (0 : ℝ) • Y)).differentiableAt.hasFDerivAt.comp_hasDerivAt
        0 hline
    simpa using hcomp.deriv
  simp_rw [hinner]
  have hc : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) 0) 0 :=
    (hf 0).fderiv.differentiableAt.hasFDerivAt
  have hu : HasFDerivAt (fun _ : E => Y) 0 0 :=
    hasFDerivAt_const (𝕜 := ℝ) Y (0 : E)
  have happ := hc.clm_apply hu
  have happ' : HasFDerivAt (fun z : E => (fderiv ℝ f z) Y)
      ((fderiv ℝ (fderiv ℝ f) 0).flip Y) 0 := by
    convert happ using 1 <;> simp
  have hline0 : HasDerivAt (fun t : ℝ => t • X) X 0 := by
    convert (hasDerivAt_id (𝕜 := ℝ) 0).smul_const X using 1 <;> simp
  have happ0 : HasFDerivAt (fun z : E => (fderiv ℝ f z) Y)
      ((fderiv ℝ (fderiv ℝ f) 0).flip Y) ((0 : ℝ) • X) := by
    simpa using happ'
  exact (happ0.comp_hasDerivAt 0 hline0).deriv

/-- Forget the traceless skew-Hermitian certificate of a physical tangent,
retaining its matrix coordinates in the ambient differential chart. -/
def physicalSuTangentToAmbient
    (X : PhysicalSuMatrixTangent d N Nc) :
    PhysicalAmbientMatrixTangent d N Nc :=
  fun b => (X b).toMatrix

@[simp]
theorem physicalSuTangentToAmbient_apply
    (X : PhysicalSuMatrixTangent d N Nc) (b : PhysicalBond d N) :
    physicalSuTangentToAmbient X b = (X b).toMatrix := rfl

/-- The physical Wilson Hessian is the restriction of the literal ambient
Fréchet Hessian to genuine `su(N)` directions. -/
def physicalWilsonHessian
    (U : PhysicalGaugeBackground d N Nc)
    (X Y : PhysicalSuMatrixTangent d N Nc) : ℝ :=
  ambientWilsonHessian U (physicalSuTangentToAmbient X)
    (physicalSuTangentToAmbient Y)

/-- Symmetry on the physical tangent sector. -/
theorem physicalWilsonHessian_symm
    (U : PhysicalGaugeBackground d N Nc)
    (X Y : PhysicalSuMatrixTangent d N Nc) :
    physicalWilsonHessian U X Y = physicalWilsonHessian U Y X := by
  exact ambientWilsonHessian_symm U _ _

theorem physicalWilsonHessian_add_left
    (U : PhysicalGaugeBackground d N Nc)
    (X Y Z : PhysicalSuMatrixTangent d N Nc) :
    physicalWilsonHessian U (X + Y) Z =
      physicalWilsonHessian U X Z + physicalWilsonHessian U Y Z := by
  simpa only [physicalWilsonHessian, physicalSuTangentToAmbient,
    Pi.add_apply] using
    ambientWilsonHessian_add_left U (physicalSuTangentToAmbient X)
      (physicalSuTangentToAmbient Y) (physicalSuTangentToAmbient Z)

theorem physicalWilsonHessian_add_right
    (U : PhysicalGaugeBackground d N Nc)
    (X Y Z : PhysicalSuMatrixTangent d N Nc) :
    physicalWilsonHessian U X (Y + Z) =
      physicalWilsonHessian U X Y + physicalWilsonHessian U X Z := by
  simpa only [physicalWilsonHessian, physicalSuTangentToAmbient,
    Pi.add_apply] using
    ambientWilsonHessian_add_right U (physicalSuTangentToAmbient X)
      (physicalSuTangentToAmbient Y) (physicalSuTangentToAmbient Z)

/-- The two-parameter physical tangent as an ambient matrix coordinate. -/
def physicalTwoParameterAmbientTangent
    (X Y : PhysicalSuMatrixTangent d N Nc) (t s : ℝ) :
    PhysicalAmbientMatrixTangent d N Nc :=
  fun b => t • (X b).toMatrix + s • (Y b).toMatrix

/-- On every positive physical bond, the ambient chart is literally the same
matrix curve as the concrete unitary left variation. -/
theorem ambientPositiveBondMatrix_twoParameter_eq_unitaryVariation
    (U : PhysicalGaugeBackground d N Nc)
    (X Y : PhysicalSuMatrixTangent d N Nc)
    (b : PhysicalBond d N) (t s : ℝ) :
    ambientPositiveBondMatrix U
        (physicalTwoParameterAmbientTangent X Y t s) b =
      ((physicalSuUnitaryLeftVariation U X Y t s
        (positiveEdgeOfPhysicalBond b)) : UN Nc).val := by
  rfl

/-- The same equality holds for every oriented edge; reversal is conjugate
transpose on the unitary group on both sides. -/
theorem ambientOrientedEdgeMatrix_twoParameter_eq_unitaryVariation
    (U : PhysicalGaugeBackground d N Nc)
    (X Y : PhysicalSuMatrixTangent d N Nc)
    (e : ConcreteEdge d N) (t s : ℝ) :
    ambientOrientedEdgeMatrix U
        (physicalTwoParameterAmbientTangent X Y t s) e =
      ((physicalSuUnitaryLeftVariation U X Y t s e) : UN Nc).val := by
  cases e with
  | mk x i sign =>
      cases sign <;> rfl

/-- Plaquette holonomy in the ambient chart is literally the matrix underlying
the unitary physical holonomy. -/
theorem ambientPlaquetteHolonomy_twoParameter_eq_unitaryVariation
    (U : PhysicalGaugeBackground d N Nc)
    (X Y : PhysicalSuMatrixTangent d N Nc)
    (p : ConcretePlaquette d N) (t s : ℝ) :
    ambientPlaquetteHolonomy U
        (physicalTwoParameterAmbientTangent X Y t s) p =
      (GaugeConfig.plaquetteHolonomy
        (physicalSuUnitaryLeftVariation U X Y t s) p).val := by
  simp only [ambientPlaquetteHolonomy, GaugeConfig.plaquetteHolonomy]
  rw [ambientOrientedEdgeMatrix_twoParameter_eq_unitaryVariation U X Y (p.edges 0),
    ambientOrientedEdgeMatrix_twoParameter_eq_unitaryVariation U X Y (p.edges 1),
    ambientOrientedEdgeMatrix_twoParameter_eq_unitaryVariation U X Y (p.edges 2),
    ambientOrientedEdgeMatrix_twoParameter_eq_unitaryVariation U X Y (p.edges 3)]
  rfl

/-- Equality of each scalar plaquette term on physical two-parameter
directions. -/
theorem ambientWilsonPlaquetteAction_twoParameter_eq_unitaryVariation
    (U : PhysicalGaugeBackground d N Nc)
    (X Y : PhysicalSuMatrixTangent d N Nc)
    (p : ConcretePlaquette d N) (t s : ℝ) :
    ambientWilsonPlaquetteAction U
        (physicalTwoParameterAmbientTangent X Y t s) p =
      unitaryWilsonPlaquetteEnergy
        (GaugeConfig.plaquetteHolonomy
          (physicalSuUnitaryLeftVariation U X Y t s) p) := by
  rw [ambientWilsonPlaquetteAction, ambientTraceReal_eq,
    ambientPlaquetteHolonomy_twoParameter_eq_unitaryVariation]
  rfl

/-- Equality of the complete finite Wilson action on the concrete physical
two-parameter curve. -/
theorem ambientWilsonAction_twoParameter_eq_unitaryVariation
    (U : PhysicalGaugeBackground d N Nc)
    (X Y : PhysicalSuMatrixTangent d N Nc) (t s : ℝ) :
    ambientWilsonAction U (physicalTwoParameterAmbientTangent X Y t s) =
      wilsonAction unitaryWilsonPlaquetteEnergy
        (physicalSuUnitaryLeftVariation U X Y t s) := by
  simp only [ambientWilsonAction, wilsonAction]
  apply Finset.sum_congr rfl
  intro p hp
  exact ambientWilsonPlaquetteAction_twoParameter_eq_unitaryVariation U X Y p t s

/-- The original nested-derivative definition and the analytic ambient chart
differentiate the same scalar two-parameter function. -/
theorem physicalWilsonMixedVariationUnitary_eq_ambientCurve
    (U : PhysicalGaugeBackground d N Nc)
    (X Y : PhysicalSuMatrixTangent d N Nc) :
    physicalWilsonMixedVariationUnitary U X Y =
      deriv (fun t => deriv (fun s =>
        ambientWilsonAction U (physicalTwoParameterAmbientTangent X Y t s)) 0) 0 := by
  simp only [physicalWilsonMixedVariationUnitary, wilsonActionMixedVariation,
    physicalSuUnitaryLeftVariation]
  congr 1
  funext t
  congr 1
  funext s
  exact (ambientWilsonAction_twoParameter_eq_unitaryVariation U X Y t s).symm

/-- Terminal WIL-H1/H2 identity: the original literal nested derivative is
exactly the symmetric Fréchet Hessian restricted to physical `su(N)` tangent
directions. -/
theorem physicalWilsonMixedVariationUnitary_eq_physicalWilsonHessian
    (U : PhysicalGaugeBackground d N Nc)
    (X Y : PhysicalSuMatrixTangent d N Nc) :
    physicalWilsonMixedVariationUnitary U X Y = physicalWilsonHessian U X Y := by
  rw [physicalWilsonMixedVariationUnitary_eq_ambientCurve]
  simpa only [physicalTwoParameterAmbientTangent, physicalSuTangentToAmbient,
    physicalWilsonHessian, ambientWilsonHessian, Pi.add_apply, Pi.smul_apply] using
    nested_deriv_line_eq_sndFDeriv (ambientWilsonAction U)
      (analyticAt_ambientWilsonAction U)
      (physicalSuTangentToAmbient X) (physicalSuTangentToAmbient Y)

theorem physicalWilsonMixedVariationUnitary_symm
    (U : PhysicalGaugeBackground d N Nc)
    (X Y : PhysicalSuMatrixTangent d N Nc) :
    physicalWilsonMixedVariationUnitary U X Y =
      physicalWilsonMixedVariationUnitary U Y X := by
  rw [physicalWilsonMixedVariationUnitary_eq_physicalWilsonHessian,
    physicalWilsonMixedVariationUnitary_eq_physicalWilsonHessian]
  exact physicalWilsonHessian_symm U X Y

theorem physicalWilsonMixedVariationUnitary_add_left
    (U : PhysicalGaugeBackground d N Nc)
    (X Y Z : PhysicalSuMatrixTangent d N Nc) :
    physicalWilsonMixedVariationUnitary U (X + Y) Z =
      physicalWilsonMixedVariationUnitary U X Z +
        physicalWilsonMixedVariationUnitary U Y Z := by
  simp only [physicalWilsonMixedVariationUnitary_eq_physicalWilsonHessian]
  exact physicalWilsonHessian_add_left U X Y Z

end

end YangMills.RG
