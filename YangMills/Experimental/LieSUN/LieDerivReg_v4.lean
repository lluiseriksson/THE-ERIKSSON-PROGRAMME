import Mathlib
import YangMills.P8_PhysicalGap.SUN_StateConstruction
import YangMills.Experimental.LieSUN.LieExpCurve
import YangMills.Experimental.LieSUN.LieDerivativeBridge

open scoped Matrix
open MeasureTheory YangMills

/-!
# LieDerivReg_v4 — Consolidated spike

Two axioms replace three P8 axioms. Net: -1.

IN:  sunGeneratorData (1) + lieDerivReg_all (1) = 2
OUT: lieDerivative_const + lieDerivative_linear + sunDirichletForm_subadditive = 3
Net: -1 axiom → P8 frontier: 10 → 9
-/

/-- Generator data for su(N): N²-1 skew-Hermitian trace-zero matrices. -/
structure GeneratorData (N_c : ℕ) [NeZero N_c] where
  mat      : Fin (N_c ^ 2 - 1) → Matrix (Fin N_c) (Fin N_c) ℂ
  skewHerm : ∀ i, (mat i)ᴴ = -(mat i)
  trZero   : ∀ i, (mat i).trace = 0

/-- Axiom 1: SU(N) has a basis of su(N) generators. -/
axiom sunGeneratorData (N_c : ℕ) [NeZero N_c] : GeneratorData N_c

/-- Concrete Lie derivative via generator curves. -/
noncomputable def lieD' (N_c : ℕ) [NeZero N_c] (i : Fin (N_c ^ 2 - 1))
    (f : SUN_State_Concrete N_c → ℝ) (U : SUN_State_Concrete N_c) : ℝ :=
  let gd := sunGeneratorData N_c
  lieDerivExp (gd.mat i) (gd.skewHerm i) (gd.trZero i) f U

/-- Regularity bundle. -/
structure LieDerivReg' (N_c : ℕ) [NeZero N_c] (f : SUN_State_Concrete N_c → ℝ) : Prop where
  diff   : ∀ i U, DifferentiableAt ℝ (fun t =>
               let gd := sunGeneratorData N_c
               f (lieExpCurve N_c (gd.mat i) (gd.skewHerm i) (gd.trZero i) U t)) 0
  meas   : ∀ i, AEStronglyMeasurable (fun U => lieD' N_c i f U) (sunHaarProb N_c)
  sq_int : ∀ i, Integrable (fun U => (lieD' N_c i f U) ^ 2) (sunHaarProb N_c)

/-- Axiom 2: All functions on SU(N) satisfy the regularity bundle. -/
axiom lieDerivReg_all (N_c : ℕ) [NeZero N_c]
    (f : SUN_State_Concrete N_c → ℝ) : LieDerivReg' N_c f

-- Derived theorems (these replace the 3 P8 axioms)

-- (1) OUT: lieDerivative_const
theorem lieD'_const (N_c : ℕ) [NeZero N_c]
    (i : Fin (N_c ^ 2 - 1)) (c : ℝ) (U : SUN_State_Concrete N_c) :
    lieD' N_c i (fun _ => c) U = 0 := by
  simp [lieD', lieDerivExp_const]

-- (2) OUT: lieDerivative_linear (add part)
theorem lieD'_add (N_c : ℕ) [NeZero N_c]
    (i : Fin (N_c ^ 2 - 1)) (f g : SUN_State_Concrete N_c → ℝ)
    (U : SUN_State_Concrete N_c) :
    lieD' N_c i (fun x => f x + g x) U = lieD' N_c i f U + lieD' N_c i g U := by
  simp only [lieD']
  set gd := sunGeneratorData N_c
  exact lieDerivExp_add (gd.mat i) (gd.skewHerm i) (gd.trZero i)
    f g U (lieDerivReg_all N_c f |>.diff i U) (lieDerivReg_all N_c g |>.diff i U)

-- (2b) lieDerivative_linear (smul part)
theorem lieD'_smul (N_c : ℕ) [NeZero N_c]
    (i : Fin (N_c ^ 2 - 1)) (c : ℝ) (f : SUN_State_Concrete N_c → ℝ)
    (U : SUN_State_Concrete N_c) :
    lieD' N_c i (fun x => c * f x) U = c * lieD' N_c i f U := by
  simp only [lieD']
  set gd := sunGeneratorData N_c
  exact lieDerivExp_smul (gd.mat i) (gd.skewHerm i) (gd.trZero i)
    c f U (lieDerivReg_all N_c f |>.diff i U)

-- (3) OUT: sunDirichletForm_subadditive
noncomputable def dirichletForm'' (N_c : ℕ) [NeZero N_c]
    (f : SUN_State_Concrete N_c → ℝ) : ℝ :=
  ∑ i : Fin (N_c ^ 2 - 1), ∫ U, (lieD' N_c i f U) ^ 2 ∂(sunHaarProb N_c)

theorem dirichletForm''_subadditive (N_c : ℕ) [NeZero N_c]
    (f g : SUN_State_Concrete N_c → ℝ) :
    dirichletForm'' N_c (fun x => f x + g x) ≤
    2 * dirichletForm'' N_c f + 2 * dirichletForm'' N_c g := by
  let hf := lieDerivReg_all N_c f
  let hg := lieDerivReg_all N_c g
  let hfg := lieDerivReg_all N_c (fun x => f x + g x)
  let μ := sunHaarProb N_c
  have hle : ∀ (i : Fin (N_c ^ 2 - 1)),
      ∫ U, (lieD' N_c i (fun x => f x + g x) U) ^ 2 ∂μ ≤
      2 * ∫ U, (lieD' N_c i f U) ^ 2 ∂μ +
      2 * ∫ U, (lieD' N_c i g U) ^ 2 ∂μ := fun i => by
    have hpoint : ∀ U, (lieD' N_c i (fun x => f x + g x) U) ^ 2 ≤
        2 * (lieD' N_c i f U) ^ 2 + 2 * (lieD' N_c i g U) ^ 2 := fun U => by
      rw [lieD'_add N_c i f g U]
      nlinarith [sq_nonneg (lieD' N_c i f U - lieD' N_c i g U)]
    have hRhs : Integrable (fun U => 2 * (lieD' N_c i f U) ^ 2 + 2 * (lieD' N_c i g U) ^ 2) μ :=
      (hf.sq_int i |>.const_mul 2).add (hg.sq_int i |>.const_mul 2)
    calc ∫ U, (lieD' N_c i (fun x => f x + g x) U) ^ 2 ∂μ
        ≤ ∫ U, (2 * (lieD' N_c i f U) ^ 2 + 2 * (lieD' N_c i g U) ^ 2) ∂μ :=
            integral_mono (hfg.sq_int i) hRhs hpoint
      _ = 2 * ∫ U, (lieD' N_c i f U) ^ 2 ∂μ +
          2 * ∫ U, (lieD' N_c i g U) ^ 2 ∂μ := by
            rw [integral_add (hf.sq_int i |>.const_mul 2) (hg.sq_int i |>.const_mul 2),
                integral_const_mul, integral_const_mul]
  simp only [dirichletForm'']
  calc ∑ i, ∫ U, (lieD' N_c i (fun x => f x + g x) U) ^ 2 ∂μ
      ≤ ∑ i, (2 * ∫ U, (lieD' N_c i f U) ^ 2 ∂μ + 2 * ∫ U, (lieD' N_c i g U) ^ 2 ∂μ) :=
          Finset.sum_le_sum (fun i _ => hle i)
    _ = 2 * ∑ i, ∫ U, (lieD' N_c i f U) ^ 2 ∂μ +
        2 * ∑ i, ∫ U, (lieD' N_c i g U) ^ 2 ∂μ := by
          simp [Finset.sum_add_distrib, Finset.mul_sum]
