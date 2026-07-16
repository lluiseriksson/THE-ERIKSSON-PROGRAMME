import YangMills.RG.BalabanCMP116WilsonHessianExpDerivative
import YangMills.RG.BalabanCMP116WilsonHessianFlatDictionary

/-!
# Exact flat plaquette Hessian

This WIL-H3 module differentiates the literal four-edge Wilson plaquette
factor at the trivial background. It proves that the mixed Hessian is exactly
the real trace inner product of the two oriented plaquette curls. Combined
with the flat coordinate dictionary, this is the local identity underlying
the global `D1* D1` Wilson Hessian.

The calculation is noncommutative before taking the trace: ordered cross
terms are paired only through cyclicity of the matrix trace. No commutativity
of edge tangents is assumed.
-/

open Matrix
open scoped Matrix.Norms.L2Operator

namespace YangMills.RG

noncomputable section

variable {Nc : ℕ} [NeZero Nc]

def traceRealCLM : Matrix (Fin Nc) (Fin Nc) ℂ →L[ℝ] ℝ :=
  ∑ i : Fin Nc, Complex.reCLM.comp (matrixEntryCLM i i)

@[simp]
theorem traceRealCLM_apply (A : Matrix (Fin Nc) (Fin Nc) ℂ) :
    traceRealCLM A = ambientTraceReal A := by
  simp only [traceRealCLM, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.comp_apply, Complex.reCLM_apply]
  unfold ambientTraceReal
  apply Finset.sum_congr rfl
  intro i hi
  rw [matrixEntryCLM_apply]

def fourExpLine (Z : Fin 4 → Matrix (Fin Nc) (Fin Nc) ℂ) (t : ℝ) :
    Matrix (Fin Nc) (Fin Nc) ℂ :=
  physicalMatrixExp (t • Z 0) * (physicalMatrixExp (t • Z 1) *
    (physicalMatrixExp (t • Z 2) * physicalMatrixExp (t • Z 3)))

def fourExpLineFirst (Z : Fin 4 → Matrix (Fin Nc) (Fin Nc) ℂ) (t : ℝ) :
    Matrix (Fin Nc) (Fin Nc) ℂ :=
  (physicalMatrixExp (t • Z 0) * Z 0) *
      (physicalMatrixExp (t • Z 1) *
        (physicalMatrixExp (t • Z 2) * physicalMatrixExp (t • Z 3))) +
    physicalMatrixExp (t • Z 0) *
      ((physicalMatrixExp (t • Z 1) * Z 1) *
          (physicalMatrixExp (t • Z 2) * physicalMatrixExp (t • Z 3)) +
        physicalMatrixExp (t • Z 1) *
          ((physicalMatrixExp (t • Z 2) * Z 2) * physicalMatrixExp (t • Z 3) +
            physicalMatrixExp (t • Z 2) * (physicalMatrixExp (t • Z 3) * Z 3)))

theorem hasDerivAt_fourExpLine (Z : Fin 4 → Matrix (Fin Nc) (Fin Nc) ℂ) (t : ℝ) :
    HasDerivAt (fourExpLine Z) (fourExpLineFirst Z t) t := by
  letI : IsTopologicalRing (Matrix (Fin Nc) (Fin Nc) ℂ) :=
    physicalMatrixTopologicalRing Nc
  have h (i : Fin 4) : HasDerivAt
      (fun u : ℝ => physicalMatrixExp (u • Z i))
      (physicalMatrixExp (t • Z i) * Z i) t := by
    simpa [physicalMatrixExp] using
      (hasDerivAt_exp_smul_const (Z i) t)
  have hraw := (((h 0).mul (h 1)).mul (h 2)).mul (h 3)
  convert hraw using 1
  · funext u
    simp [fourExpLine, mul_assoc]
  · simp [fourExpLineFirst]
    noncomm_ring

theorem hasDerivAt_fourExpLineFirst_trace
    (Z : Fin 4 → Matrix (Fin Nc) (Fin Nc) ℂ) :
    HasDerivAt (fun t => ambientTraceReal (fourExpLineFirst Z t))
      (ambientTraceReal ((∑ i : Fin 4, Z i) * (∑ i : Fin 4, Z i))) 0 := by
  letI : IsTopologicalRing (Matrix (Fin Nc) (Fin Nc) ℂ) :=
    physicalMatrixTopologicalRing Nc
  let E (i : Fin 4) (t : ℝ) := physicalMatrixExp (t • Z i)
  let EX (i : Fin 4) (t : ℝ) := E i t * Z i
  have hE (i : Fin 4) : HasDerivAt (E i) (Z i) 0 := by
    have hh : HasDerivAt (fun u : ℝ => physicalMatrixExp (u • Z i))
        (physicalMatrixExp ((0 : ℝ) • Z i) * Z i) 0 := by
      simpa [physicalMatrixExp] using
        (hasDerivAt_exp_smul_const (Z i) (0 : ℝ))
    have hz : physicalMatrixExp ((0 : ℝ) • Z i) = 1 := by
      have hzero : (0 : ℝ) • Z i =
          (0 : Matrix (Fin Nc) (Fin Nc) ℂ) := zero_smul ℝ (Z i)
      rw [hzero]
      exact physicalMatrixExp_zero
    simpa only [E, hz, one_mul] using hh
  have hEX (i : Fin 4) : HasDerivAt (EX i) (Z i * Z i) 0 := by
    simpa [EX, E] using (hE i).mul_const (Z i)
  have hE23 := (hE 2).mul (hE 3)
  have hT23 := ((hEX 2).mul (hE 3)).add ((hE 2).mul (hEX 3))
  have hE123 := (hE 1).mul hE23
  have hT123 := ((hEX 1).mul hE23).add ((hE 1).mul hT23)
  have hraw := ((hEX 0).mul hE123).add ((hE 0).mul hT123)
  have htrace := (traceRealCLM (Nc := Nc)).hasFDerivAt.comp_hasDerivAt 0 hraw
  have htrace' : HasDerivAt
      (fun t => ambientTraceReal
        ((EX 0 * (E 1 * (E 2 * E 3)) +
          E 0 * (EX 1 * (E 2 * E 3) + E 1 * (EX 2 * E 3 + E 2 * EX 3))) t))
      (ambientTraceReal
        (Z 0 * Z 0 * (E 1 * (E 2 * E 3)) 0 +
          EX 0 0 * (Z 1 * (E 2 * E 3) 0 + E 1 0 * (Z 2 * E 3 0 + E 2 0 * Z 3)) +
          (Z 0 * (EX 1 * (E 2 * E 3) + E 1 * (EX 2 * E 3 + E 2 * EX 3)) 0 +
            E 0 0 *
              (Z 1 * Z 1 * (E 2 * E 3) 0 +
                EX 1 0 * (Z 2 * E 3 0 + E 2 0 * Z 3) +
                (Z 1 * (EX 2 * E 3 + E 2 * EX 3) 0 +
                  E 1 0 *
                    (Z 2 * Z 2 * E 3 0 + EX 2 0 * Z 3 +
                    (Z 2 * EX 3 0 + E 2 0 * (Z 3 * Z 3)))))))) 0 := by
    convert htrace using 1
    · funext t
      exact (traceRealCLM_apply
        ((EX 0 * (E 1 * (E 2 * E 3)) +
          E 0 * (EX 1 * (E 2 * E 3) + E 1 * (EX 2 * E 3 + E 2 * EX 3))) t)).symm
    · exact (traceRealCLM_apply
        (Z 0 * Z 0 * (E 1 * (E 2 * E 3)) 0 +
          EX 0 0 * (Z 1 * (E 2 * E 3) 0 + E 1 0 * (Z 2 * E 3 0 + E 2 0 * Z 3)) +
          (Z 0 * (EX 1 * (E 2 * E 3) + E 1 * (EX 2 * E 3 + E 2 * EX 3)) 0 +
            E 0 0 *
              (Z 1 * Z 1 * (E 2 * E 3) 0 +
                EX 1 0 * (Z 2 * E 3 0 + E 2 0 * Z 3) +
                (Z 1 * (EX 2 * E 3 + E 2 * EX 3) 0 +
                  E 1 0 *
                    (Z 2 * Z 2 * E 3 0 + EX 2 0 * Z 3 +
                      (Z 2 * EX 3 0 + E 2 0 * (Z 3 * Z 3)))))))).symm
  have hEzero (i : Fin 4) : E i 0 = 1 := by
    dsimp [E]
    have hzero : (0 : ℝ) • Z i =
        (0 : Matrix (Fin Nc) (Fin Nc) ℂ) := zero_smul ℝ (Z i)
    rw [hzero, physicalMatrixExp_zero]
  have hEXzero (i : Fin 4) : EX i 0 = Z i := by
    simp [EX, hEzero]
  convert htrace' using 1
  simp only [Pi.mul_apply, Pi.add_apply, hEzero, hEXzero, one_mul, mul_one]
  simp only [Fin.sum_univ_four, ambientTraceReal_eq, add_mul, mul_add,
    Matrix.trace_add, Complex.add_re]
  rw [Matrix.trace_mul_comm (Z 1) (Z 0)]
  rw [Matrix.trace_mul_comm (Z 2) (Z 0)]
  rw [Matrix.trace_mul_comm (Z 2) (Z 1)]
  rw [Matrix.trace_mul_comm (Z 3) (Z 0)]
  rw [Matrix.trace_mul_comm (Z 3) (Z 1)]
  rw [Matrix.trace_mul_comm (Z 3) (Z 2)]
  ring

def fourExpWilsonLine
    (Z : Fin 4 → Matrix (Fin Nc) (Fin Nc) ℂ) (t : ℝ) : ℝ :=
  1 - ambientTraceReal (fourExpLine Z t)

theorem hasDerivAt_fourExpWilsonLine
    (Z : Fin 4 → Matrix (Fin Nc) (Fin Nc) ℂ) (t : ℝ) :
    HasDerivAt (fourExpWilsonLine Z)
      (-ambientTraceReal (fourExpLineFirst Z t)) t := by
  have hraw := (traceRealCLM (Nc := Nc)).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_fourExpLine Z t)
  have htrace : HasDerivAt
      (fun u => ambientTraceReal (fourExpLine Z u))
      (ambientTraceReal (fourExpLineFirst Z t)) t := by
    convert hraw using 1
    · funext u
      exact (traceRealCLM_apply (fourExpLine Z u)).symm
    · exact (traceRealCLM_apply (fourExpLineFirst Z t)).symm
  simpa only [fourExpWilsonLine] using htrace.const_sub (1 : ℝ)

theorem secondDeriv_fourExpWilsonLine_zero
    (Z : Fin 4 → Matrix (Fin Nc) (Fin Nc) ℂ) :
    deriv (fun t => deriv (fourExpWilsonLine Z) t) 0 =
      -ambientTraceReal ((∑ i : Fin 4, Z i) * (∑ i : Fin 4, Z i)) := by
  have hfirst : (fun t => deriv (fourExpWilsonLine Z) t) =
      fun t => -ambientTraceReal (fourExpLineFirst Z t) := by
    funext t
    exact (hasDerivAt_fourExpWilsonLine Z t).deriv
  rw [hfirst]
  exact (hasDerivAt_fourExpLineFirst_trace Z).neg.deriv

theorem secondDeriv_line_eq_sndFDeriv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (hf : ∀ z, AnalyticAt ℝ f z) (X : E) :
    deriv (fun t : ℝ => deriv (fun s : ℝ => f (s • X)) t) 0 =
      (fderiv ℝ (fderiv ℝ f) 0) X X := by
  have hinner : ∀ t : ℝ,
      deriv (fun s : ℝ => f (s • X)) t =
        (fderiv ℝ f (t • X)) X := by
    intro t
    have hline : HasDerivAt (fun s : ℝ => s • X) X t := by
      convert (hasDerivAt_id (𝕜 := ℝ) t).smul_const X using 1 <;> simp
    exact ((hf (t • X)).differentiableAt.hasFDerivAt.comp_hasDerivAt
      t hline).deriv
  simp_rw [hinner]
  have hc : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) 0) 0 :=
    (hf 0).fderiv.differentiableAt.hasFDerivAt
  have hu : HasFDerivAt (fun _ : E => X) 0 0 :=
    hasFDerivAt_const (𝕜 := ℝ) X (0 : E)
  have happ := hc.clm_apply hu
  have happ' : HasFDerivAt (fun z : E => (fderiv ℝ f z) X)
      ((fderiv ℝ (fderiv ℝ f) 0).flip X) 0 := by
    convert happ using 1 <;> simp
  have hline0 : HasDerivAt (fun t : ℝ => t • X) X 0 := by
    convert (hasDerivAt_id (𝕜 := ℝ) 0).smul_const X using 1 <;> simp
  have happ0 : HasFDerivAt (fun z : E => (fderiv ℝ f z) X)
      ((fderiv ℝ (fderiv ℝ f) 0).flip X) ((0 : ℝ) • X) := by
    simpa using happ'
  exact (happ0.comp_hasDerivAt 0 hline0).deriv

theorem ambientOrientedEdgeMatrix_trivial_line
    {d N : ℕ} [NeZero d] [NeZero N]
    (A : PhysicalGaugeOneCochain d N Nc)
    (e : ConcreteEdge d N) (t : ℝ) :
    ambientOrientedEdgeMatrix (trivialPhysicalGaugeBackground d N Nc)
        (t • physicalSuTangentToAmbient
          (physicalCochainToSuMatrixTangent A)) e =
      physicalMatrixExp (t • flatOrientedSuMatrixTangent A e) := by
  rcases e with ⟨x, i, sign⟩
  cases sign
  · simp only [ambientOrientedEdgeMatrix, Bool.false_eq_true, if_false,
      ambientPositiveBondMatrix, trivialPhysicalGaugeBackground,
      physicalBondOfEdge, physicalSuTangentToAmbient,
      physicalCochainToSuMatrixTangent, Pi.smul_apply,
      flatOrientedSuMatrixTangent]
    rw [OneMemClass.coe_one, mul_one]
    rw [physicalMatrixExp_conjTranspose]
    have hskew :
        (((suLieCoordIso Nc).symm (A (x, i))).toMatrix)ᴴ =
          -((suLieCoordIso Nc).symm (A (x, i))).toMatrix := by
      exact (mem_suMatrixSubmodule_iff
        (((suLieCoordIso Nc).symm (A (x, i))).toMatrix)).mp
          (((suLieCoordIso Nc).symm (A (x, i))).property) |>.1
    rw [Matrix.conjTranspose_smul, star_trivial, hskew]
  · simp [ambientOrientedEdgeMatrix, ambientPositiveBondMatrix,
      trivialPhysicalGaugeBackground, physicalSuTangentToAmbient,
      physicalCochainToSuMatrixTangent, flatOrientedSuMatrixTangent]

theorem ambientPlaquetteHolonomy_trivial_line
    {d N : ℕ} [NeZero d] [NeZero N]
    (A : PhysicalGaugeOneCochain d N Nc)
    (p : ConcretePlaquette d N) (t : ℝ) :
    ambientPlaquetteHolonomy (trivialPhysicalGaugeBackground d N Nc)
        (t • physicalSuTangentToAmbient
          (physicalCochainToSuMatrixTangent A)) p =
      fourExpLine (fun k => flatOrientedSuMatrixTangent A (p.edges k)) t := by
  unfold ambientPlaquetteHolonomy fourExpLine
  rw [ambientOrientedEdgeMatrix_trivial_line,
    ambientOrientedEdgeMatrix_trivial_line,
    ambientOrientedEdgeMatrix_trivial_line,
    ambientOrientedEdgeMatrix_trivial_line]
  simp only [mul_assoc]

theorem ambientWilsonPlaquetteAction_trivial_line
    {d N : ℕ} [NeZero d] [NeZero N]
    (A : PhysicalGaugeOneCochain d N Nc)
    (p : ConcretePlaquette d N) (t : ℝ) :
    ambientWilsonPlaquetteAction (trivialPhysicalGaugeBackground d N Nc)
        (t • physicalSuTangentToAmbient
          (physicalCochainToSuMatrixTangent A)) p =
      fourExpWilsonLine
        (fun k => flatOrientedSuMatrixTangent A (p.edges k)) t := by
  unfold ambientWilsonPlaquetteAction fourExpWilsonLine
  rw [ambientPlaquetteHolonomy_trivial_line]

def ambientWilsonPlaquetteHessian
    {d N : ℕ} [NeZero d] [NeZero N]
    (U : PhysicalGaugeBackground d N Nc)
    (p : ConcretePlaquette d N) :
    PhysicalAmbientMatrixTangent d N Nc →L[ℝ]
      PhysicalAmbientMatrixTangent d N Nc →L[ℝ] ℝ :=
  fderiv ℝ
    (fderiv ℝ (fun Z => ambientWilsonPlaquetteAction U Z p)) 0

theorem ambientWilsonPlaquetteHessian_symm
    {d N : ℕ} [NeZero d] [NeZero N]
    (U : PhysicalGaugeBackground d N Nc)
    (p : ConcretePlaquette d N)
    (X Y : PhysicalAmbientMatrixTangent d N Nc) :
    ambientWilsonPlaquetteHessian U p X Y =
      ambientWilsonPlaquetteHessian U p Y X := by
  have hc : ContDiffAt ℝ (2 : WithTop ℕ∞)
      (fun Z => ambientWilsonPlaquetteAction U Z p) 0 :=
    (analyticAt_ambientWilsonPlaquetteAction U 0 p).contDiffAt
  have hs : IsSymmSndFDerivAt ℝ
      (fun Z => ambientWilsonPlaquetteAction U Z p) 0 :=
    hc.isSymmSndFDerivAt (by norm_num [minSmoothness])
  simpa only [ambientWilsonPlaquetteHessian] using hs.eq X Y

theorem physicalCochainToAmbient_add
    {d N : ℕ} [NeZero d] [NeZero N]
    (A B : PhysicalGaugeOneCochain d N Nc) :
    physicalSuTangentToAmbient
        (physicalCochainToSuMatrixTangent (A + B)) =
      physicalSuTangentToAmbient (physicalCochainToSuMatrixTangent A) +
        physicalSuTangentToAmbient (physicalCochainToSuMatrixTangent B) := by
  funext b
  change (((suLieCoordIso Nc).symm ((A + B) b)).toMatrix) =
    (((suLieCoordIso Nc).symm (A b)).toMatrix) +
      (((suLieCoordIso Nc).symm (B b)).toMatrix)
  rw [PiLp.add_apply, map_add]
  rfl

theorem flatOrientedSuMatrixTangent_add
    {d N : ℕ} [NeZero d] [NeZero N]
    (A B : PhysicalGaugeOneCochain d N Nc)
    (e : ConcreteEdge d N) :
    flatOrientedSuMatrixTangent (A + B) e =
      flatOrientedSuMatrixTangent A e +
        flatOrientedSuMatrixTangent B e := by
  rcases e with ⟨x, i, sign⟩
  cases sign
  · simp [flatOrientedSuMatrixTangent, map_add, PiLp.add_apply]
    change
      -((((suLieCoordIso Nc).symm (A (x, i))).toMatrix) +
        (((suLieCoordIso Nc).symm (B (x, i))).toMatrix)) =
      -(((suLieCoordIso Nc).symm (A (x, i))).toMatrix) +
        -(((suLieCoordIso Nc).symm (B (x, i))).toMatrix)
    abel
  · simp [flatOrientedSuMatrixTangent, map_add, PiLp.add_apply]
    rfl

theorem flatPlaquetteSuMatrixCurl_add
    {d N : ℕ} [NeZero d] [NeZero N]
    (A B : PhysicalGaugeOneCochain d N Nc)
    (p : ConcretePlaquette d N) :
    flatPlaquetteSuMatrixCurl (A + B) p =
      flatPlaquetteSuMatrixCurl A p +
        flatPlaquetteSuMatrixCurl B p := by
  simp only [flatPlaquetteSuMatrixCurl, flatOrientedSuMatrixTangent_add,
    Finset.sum_add_distrib]

theorem matrixTraceInner_add_right_local
    (X Y Z : Matrix (Fin Nc) (Fin Nc) ℂ) :
    matrixTraceInner X (Y + Z) =
      matrixTraceInner X Y + matrixTraceInner X Z := by
  rw [matrixTraceInner_comm X (Y + Z), matrixTraceInner_add_left,
    matrixTraceInner_comm Y X, matrixTraceInner_comm Z X]

theorem ambientWilsonPlaquetteHessian_trivial_self
    {d N : ℕ} [NeZero d] [NeZero N]
    (A : PhysicalGaugeOneCochain d N Nc)
    (p : ConcretePlaquette d N) :
    ambientWilsonPlaquetteHessian
        (trivialPhysicalGaugeBackground d N Nc) p
        (physicalSuTangentToAmbient
          (physicalCochainToSuMatrixTangent A))
        (physicalSuTangentToAmbient
          (physicalCochainToSuMatrixTangent A)) =
      matrixTraceInner (flatPlaquetteSuMatrixCurl A p)
        (flatPlaquetteSuMatrixCurl A p) := by
  let X := physicalSuTangentToAmbient
    (physicalCochainToSuMatrixTangent A)
  let f := fun Z : PhysicalAmbientMatrixTangent d N Nc =>
    ambientWilsonPlaquetteAction
      (trivialPhysicalGaugeBackground d N Nc) Z p
  have hsnd := secondDeriv_line_eq_sndFDeriv f
    (fun Z => analyticAt_ambientWilsonPlaquetteAction
      (trivialPhysicalGaugeBackground d N Nc) Z p) X
  have hcurve : (fun t : ℝ => f (t • X)) =
      fourExpWilsonLine
        (fun k => flatOrientedSuMatrixTangent A (p.edges k)) := by
    funext t
    exact ambientWilsonPlaquetteAction_trivial_line A p t
  change ((fderiv ℝ (fderiv ℝ f) 0) X) X =
    matrixTraceInner (flatPlaquetteSuMatrixCurl A p)
      (flatPlaquetteSuMatrixCurl A p)
  rw [← hsnd]
  have hderiv : (fun t => deriv (fun s => f (s • X)) t) =
      fun t => deriv
        (fourExpWilsonLine
          (fun k => flatOrientedSuMatrixTangent A (p.edges k))) t := by
    funext t
    rw [hcurve]
  have hout : deriv (fun t : ℝ => deriv (fun s : ℝ => f (s • X)) t) 0 =
      deriv (fun t : ℝ => deriv
        (fourExpWilsonLine
          (fun k => flatOrientedSuMatrixTangent A (p.edges k))) t) 0 :=
    congrArg (fun g : ℝ → ℝ => deriv g 0) hderiv
  apply Eq.trans hout
  rw [secondDeriv_fourExpWilsonLine_zero]
  change -ambientTraceReal
      (flatPlaquetteSuMatrixCurl A p * flatPlaquetteSuMatrixCurl A p) =
    matrixTraceInner (flatPlaquetteSuMatrixCurl A p)
      (flatPlaquetteSuMatrixCurl A p)
  have hskew :
      (flatPlaquetteSuMatrixCurl A p)ᴴ =
        -flatPlaquetteSuMatrixCurl A p := by
    exact (mem_suMatrixSubmodule_iff (flatPlaquetteSuMatrixCurl A p)).mp
      (flatPlaquetteSuLieCurl A p).property |>.1
  unfold matrixTraceInner
  rw [hskew, neg_mul, Matrix.trace_neg, Complex.neg_re,
    ambientTraceReal_eq]

theorem ambientWilsonPlaquetteHessian_trivial
    {d N : ℕ} [NeZero d] [NeZero N]
    (A B : PhysicalGaugeOneCochain d N Nc)
    (p : ConcretePlaquette d N) :
    ambientWilsonPlaquetteHessian
        (trivialPhysicalGaugeBackground d N Nc) p
        (physicalSuTangentToAmbient
          (physicalCochainToSuMatrixTangent A))
        (physicalSuTangentToAmbient
          (physicalCochainToSuMatrixTangent B)) =
      matrixTraceInner (flatPlaquetteSuMatrixCurl A p)
        (flatPlaquetteSuMatrixCurl B p) := by
  let H := ambientWilsonPlaquetteHessian
    (trivialPhysicalGaugeBackground d N Nc) p
  let XA := physicalSuTangentToAmbient
    (physicalCochainToSuMatrixTangent A)
  let XB := physicalSuTangentToAmbient
    (physicalCochainToSuMatrixTangent B)
  let CA := flatPlaquetteSuMatrixCurl A p
  let CB := flatPlaquetteSuMatrixCurl B p
  have hAA : H XA XA = matrixTraceInner CA CA := by
    exact ambientWilsonPlaquetteHessian_trivial_self A p
  have hBB : H XB XB = matrixTraceInner CB CB := by
    exact ambientWilsonPlaquetteHessian_trivial_self B p
  have hABBA : H XA XB = H XB XA :=
    ambientWilsonPlaquetteHessian_symm
      (trivialPhysicalGaugeBackground d N Nc) p XA XB
  have hinnerABBA : matrixTraceInner CA CB = matrixTraceInner CB CA :=
    matrixTraceInner_comm CA CB
  have hsum :
      H (XA + XB) (XA + XB) =
        matrixTraceInner (CA + CB) (CA + CB) := by
    have h := ambientWilsonPlaquetteHessian_trivial_self (A + B) p
    rw [physicalCochainToAmbient_add, flatPlaquetteSuMatrixCurl_add] at h
    exact h
  have hHexpand :
      H (XA + XB) (XA + XB) =
        H XA XA + H XA XB + H XB XA + H XB XB := by
    change
      (ambientWilsonPlaquetteHessian
        (trivialPhysicalGaugeBackground d N Nc) p) (XA + XB) (XA + XB) = _
    dsimp [H]
    simp only [ContinuousLinearMap.map_add, ContinuousLinearMap.add_apply]
    ring
  have hIexpand :
      matrixTraceInner (CA + CB) (CA + CB) =
        matrixTraceInner CA CA + matrixTraceInner CA CB +
          matrixTraceInner CB CA + matrixTraceInner CB CB := by
    rw [matrixTraceInner_add_left, matrixTraceInner_add_right_local,
      matrixTraceInner_add_right_local]
    ring
  rw [hHexpand, hIexpand] at hsum
  linarith

end

end YangMills.RG
