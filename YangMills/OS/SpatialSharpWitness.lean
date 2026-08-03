/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson
-/
import YangMills.OS.SpatialRing

/-!
# The sharp two-site witness for the spatial-ring constant

This module treats only physical size `N = 2` (the repository parameter
`L = 1`) and spatial coupling `gamma = 0`.  It folds the repository's exact
kernel `symWeighted (spatialWeightRing 0) beta` over the two global-flip
orbits, computes the resulting even and odd `2 x 2` blocks, and records the
finite algebra that makes `tanh beta` sharp.

No general spectrum, Clifford algebra, Jordan--Wigner transform, or uniform
upper bound is constructed or claimed here.
-/

namespace YangMills.OS

open scoped Matrix.Norms.L2Operator

/-! ## The exact physical orbit folds -/

/-- The two representatives `(0,0)` and `(0,1)` of the global-flip orbits on
two-spin configurations. -/
def n2OrbitRep (i : Fin 2) (j : Fin 2) : Fin 2 :=
  if j = 0 then 0 else i

/-- The exact repository transfer kernel at physical size `N = 2` and
`gamma = 0`. -/
noncomputable def n2TransferKernel (beta : ℝ)
    (sigma tau : Fin 2 → Fin 2) : ℝ :=
  symWeighted (spatialWeightRing 0) beta sigma tau

/-- The physical flip-even block in the normalized orbit basis. -/
noncomputable def n2EvenBlock (beta : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j =>
    n2TransferKernel beta (n2OrbitRep i) (n2OrbitRep j) +
      n2TransferKernel beta (n2OrbitRep i) (flipCfg (n2OrbitRep j))

/-- The physical flip-odd block in the normalized orbit basis. -/
noncomputable def n2OddBlock (beta : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j =>
    n2TransferKernel beta (n2OrbitRep i) (n2OrbitRep j) -
      n2TransferKernel beta (n2OrbitRep i) (flipCfg (n2OrbitRep j))

/-- Closed form of the exact even orbit fold. -/
theorem n2EvenBlock_closedForm (beta : ℝ) :
    n2EvenBlock beta =
      !![2 * Real.cosh (2 * beta), 2;
         2, 2 * Real.cosh (2 * beta)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [n2EvenBlock, n2TransferKernel, n2OrbitRep, symWeighted,
      spatialWeightRing, spatialKernel, flipCfg, z2Flip, z2Bond, z2Sign,
      Fin.prod_univ_two, Real.cosh_eq, pow_two, ← Real.exp_add] <;> ring_nf

/-- Closed form of the exact odd orbit fold. -/
theorem n2OddBlock_closedForm (beta : ℝ) :
    n2OddBlock beta =
      !![2 * Real.sinh (2 * beta), 0;
         0, 2 * Real.sinh (2 * beta)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [n2OddBlock, n2TransferKernel, n2OrbitRep, symWeighted,
      spatialWeightRing, spatialKernel, flipCfg, z2Flip, z2Bond, z2Sign,
      Fin.prod_univ_two, Real.sinh_eq, pow_two, ← Real.exp_add] <;> ring_nf

/-! ## Exact L2 operator norms of the two blocks -/

/-- The real Hadamard rotation used only to diagonalize the explicit even
`2 x 2` block. -/
noncomputable def n2Hadamard : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.sqrt 2 / 2, Real.sqrt 2 / 2;
     Real.sqrt 2 / 2, -Real.sqrt 2 / 2]

/-- The two diagonal entries obtained by the explicit Hadamard rotation. -/
noncomputable def n2EvenDiagonal (beta : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.diagonal
    ![2 * (Real.cosh (2 * beta) + 1),
      2 * (Real.cosh (2 * beta) - 1)]

theorem n2Hadamard_mem_unitary :
    n2Hadamard ∈ Matrix.unitaryGroup (Fin 2) ℝ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [n2Hadamard, Matrix.mul_apply, Fin.sum_univ_two] <;>
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

/-- Direct two-by-two diagonalization of the even block. -/
theorem n2EvenBlock_hadamard (beta : ℝ) :
    n2EvenBlock beta = n2Hadamard * n2EvenDiagonal beta * n2Hadamard := by
  rw [n2EvenBlock_closedForm]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [n2Hadamard, n2EvenDiagonal, Matrix.mul_apply, Matrix.vecMul,
      dotProduct, Fin.sum_univ_two] <;>
    ring_nf <;> rw [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

/-- The reverse two-by-two rotation, recorded explicitly to avoid any general
spectral infrastructure. -/
theorem n2EvenDiagonal_hadamard (beta : ℝ) :
    n2EvenDiagonal beta = n2Hadamard * n2EvenBlock beta * n2Hadamard := by
  rw [n2EvenBlock_closedForm]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [n2Hadamard, n2EvenDiagonal, Matrix.mul_apply, Fin.sum_univ_two] <;>
    ring_nf <;> rw [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)] <;> ring

theorem n2Hadamard_norm : ‖n2Hadamard‖ = 1 := by
  have hstar : star n2Hadamard * n2Hadamard = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp n2Hadamard_mem_unitary
  have hsq := Matrix.l2_opNorm_conjTranspose_mul_self n2Hadamard
  have hone : ‖(1 : Matrix (Fin 2) (Fin 2) ℝ)‖ = 1 := by
    rw [show (1 : Matrix (Fin 2) (Fin 2) ℝ) =
        Matrix.diagonal (fun _ : Fin 2 => 1) by ext i j; simp]
    rw [Matrix.l2_opNorm_diagonal]
    simp
  rw [show n2Hadamard.conjTranspose * n2Hadamard = 1 by simpa using hstar, hone] at hsq
  nlinarith [norm_nonneg n2Hadamard]

theorem n2EvenDiagonal_norm (beta : ℝ) :
    ‖n2EvenDiagonal beta‖ = 2 * (Real.cosh (2 * beta) + 1) := by
  rw [n2EvenDiagonal, Matrix.l2_opNorm_diagonal]
  let dplus : ℝ := 2 * (Real.cosh (2 * beta) + 1)
  let dminus : ℝ := 2 * (Real.cosh (2 * beta) - 1)
  have hcosh : 1 ≤ Real.cosh (2 * beta) := Real.one_le_cosh _
  have hdplus : 0 ≤ dplus := by unfold dplus; linarith
  have hdminus : 0 ≤ dminus := by unfold dminus; linarith
  have hdle : dminus ≤ dplus := by unfold dminus dplus; linarith
  change ‖![dplus, dminus]‖ = dplus
  apply le_antisymm
  · refine (pi_norm_le_iff_of_nonneg hdplus).2 ?_
    intro i
    fin_cases i
    · simp [abs_of_nonneg hdplus]
    · simpa [abs_of_nonneg hdminus] using hdle
  · have h := norm_le_pi_norm ![dplus, dminus] (0 : Fin 2)
    simpa [abs_of_nonneg hdplus] using h

/-- Exact L2 operator norm of the physical even block. -/
theorem n2EvenBlock_norm (beta : ℝ) :
    ‖n2EvenBlock beta‖ = 2 * (Real.cosh (2 * beta) + 1) := by
  have hup : ‖n2EvenBlock beta‖ ≤ ‖n2EvenDiagonal beta‖ := by
    calc
      ‖n2EvenBlock beta‖ =
          ‖n2Hadamard * n2EvenDiagonal beta * n2Hadamard‖ :=
            congrArg norm (n2EvenBlock_hadamard beta)
      _ ≤ ‖n2Hadamard * n2EvenDiagonal beta‖ * ‖n2Hadamard‖ :=
            Matrix.l2_opNorm_mul _ _
      _ ≤ (‖n2Hadamard‖ * ‖n2EvenDiagonal beta‖) * ‖n2Hadamard‖ :=
            mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _)
      _ = ‖n2EvenDiagonal beta‖ := by rw [n2Hadamard_norm]; ring
  have hdown : ‖n2EvenDiagonal beta‖ ≤ ‖n2EvenBlock beta‖ := by
    calc
      ‖n2EvenDiagonal beta‖ =
          ‖n2Hadamard * n2EvenBlock beta * n2Hadamard‖ :=
            congrArg norm (n2EvenDiagonal_hadamard beta)
      _ ≤ ‖n2Hadamard * n2EvenBlock beta‖ * ‖n2Hadamard‖ :=
            Matrix.l2_opNorm_mul _ _
      _ ≤ (‖n2Hadamard‖ * ‖n2EvenBlock beta‖) * ‖n2Hadamard‖ :=
            mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _)
      _ = ‖n2EvenBlock beta‖ := by rw [n2Hadamard_norm]; ring
  rw [← n2EvenDiagonal_norm beta]
  exact le_antisymm hup hdown

theorem n2OddBlock_diagonal (beta : ℝ) :
    n2OddBlock beta = Matrix.diagonal (fun _ : Fin 2 => 2 * Real.sinh (2 * beta)) := by
  rw [n2OddBlock_closedForm]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- Exact L2 operator norm of the physical odd block. -/
theorem n2OddBlock_norm {beta : ℝ} (hbeta : 0 < beta) :
    ‖n2OddBlock beta‖ = 2 * Real.sinh (2 * beta) := by
  rw [n2OddBlock_diagonal, Matrix.l2_opNorm_diagonal]
  have hs : 0 ≤ Real.sinh (2 * beta) :=
    le_of_lt (Real.sinh_pos_iff.mpr (by linarith))
  have hsinh : 0 ≤ 2 * Real.sinh (2 * beta) := by positivity
  apply le_antisymm
  · refine (pi_norm_le_iff_of_nonneg hsinh).2 ?_
    intro i
    simp [abs_of_nonneg hs]
  · have h := norm_le_pi_norm (fun _ : Fin 2 => 2 * Real.sinh (2 * beta)) (0 : Fin 2)
    convert h using 1 <;> simp [abs_of_nonneg hs]

/-! ## The finite algebraic sharpness identity -/

/-- The two explicit spectral scales read from the closed blocks. -/
noncomputable def n2EvenScale (beta : ℝ) : ℝ :=
  2 * (Real.cosh (2 * beta) + 1)

noncomputable def n2OddScale (beta : ℝ) : ℝ :=
  2 * Real.sinh (2 * beta)

/-- The exact quotient of the two explicit two-site scales is `tanh beta`.
This lemma assumes only `beta > 0`; the equality itself is finite hyperbolic
algebra and does not assume the desired conclusion in any form. -/
theorem n2_scale_ratio_eq_tanh {beta : ℝ} (hbeta : 0 < beta) :
    n2OddScale beta / n2EvenScale beta = Real.tanh beta := by
  have hcosh : Real.cosh beta ≠ 0 := ne_of_gt (Real.cosh_pos beta)
  have hden : Real.cosh (2 * beta) + 1 ≠ 0 := by
    have hc := Real.one_le_cosh (2 * beta)
    linarith
  rw [n2OddScale, n2EvenScale, Real.tanh_eq_sinh_div_cosh,
    Real.sinh_two_mul, Real.cosh_two_mul]
  field_simp
  nlinarith [cosh_sq_sub_sinh_sq' beta]

/-- The campaign's candidate constant specialized exactly to `gamma = 0`. -/
noncomputable def n2CandidateQ (beta : ℝ) : ℝ :=
  Real.tanh beta * Real.exp (2 * (0 : ℝ))

theorem n2CandidateQ_eq_tanh (beta : ℝ) : n2CandidateQ beta = Real.tanh beta := by
  simp [n2CandidateQ]

/-- **Pre-registered sharp witness.**  At physical size `N = 2`, `gamma = 0`,
and `beta > 0`, the quotient of the exact odd/even L2 operator norms is the
campaign constant `q = tanh beta * exp (2 * 0) = tanh beta`. -/
theorem n2_sharp_norm_ratio {beta : ℝ} (hbeta : 0 < beta) :
    ‖n2OddBlock beta‖ / ‖n2EvenBlock beta‖ =
        Real.sinh (2 * beta) / (Real.cosh (2 * beta) + 1) ∧
    Real.sinh (2 * beta) / (Real.cosh (2 * beta) + 1) =
        n2CandidateQ beta ∧
    n2CandidateQ beta = Real.tanh beta := by
  rw [n2OddBlock_norm hbeta, n2EvenBlock_norm beta]
  have hden : Real.cosh (2 * beta) + 1 ≠ 0 := by
    have hc := Real.one_le_cosh (2 * beta)
    linarith
  constructor
  · field_simp
  constructor
  · rw [n2CandidateQ_eq_tanh]
    have hscale := n2_scale_ratio_eq_tanh hbeta
    rw [n2OddScale, n2EvenScale] at hscale
    calc
      Real.sinh (2 * beta) / (Real.cosh (2 * beta) + 1) =
          (2 * Real.sinh (2 * beta)) /
            (2 * (Real.cosh (2 * beta) + 1)) := by field_simp
      _ = Real.tanh beta := hscale
  · exact n2CandidateQ_eq_tanh beta

/-- Consequently no constant strictly below `q` can bound even this one
physical quotient, hence no such constant can be a uniform bound in `N`. -/
theorem n2_no_strictly_smaller_constant {beta c : ℝ}
    (hbeta : 0 < beta) (hc : c < n2CandidateQ beta) :
    ¬ ‖n2OddBlock beta‖ / ‖n2EvenBlock beta‖ ≤ c := by
  intro hbound
  have hratio := (n2_sharp_norm_ratio hbeta).1
  have hq := (n2_sharp_norm_ratio hbeta).2.1
  linarith

/-- The `(0,0)` entry of `q E_2 - O_2`, with `q = tanh beta`, is negative
and has the exact value `-2 tanh beta`. -/
theorem n2_qEven_sub_odd_entry {beta : ℝ} (hbeta : 0 < beta) :
    (Real.tanh beta • n2EvenBlock beta - n2OddBlock beta) 0 0 =
      -2 * Real.tanh beta := by
  rw [n2EvenBlock_closedForm, n2OddBlock_closedForm]
  change Real.tanh beta * (2 * Real.cosh (2 * beta)) -
      2 * Real.sinh (2 * beta) = -2 * Real.tanh beta
  have hcosh : Real.cosh beta ≠ 0 := ne_of_gt (Real.cosh_pos beta)
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_two_mul, Real.cosh_two_mul]
  field_simp
  nlinarith [cosh_sq_sub_sinh_sq' beta]

/-- The exact scalar counterexample to form domination: the first physical
even-orbit basis vector gives a negative value for `q E_2 - O_2`. -/
theorem n2_form_domination_fails {beta : ℝ} (hbeta : 0 < beta) :
    (Real.tanh beta • n2EvenBlock beta - n2OddBlock beta) 0 0 < 0 := by
  rw [n2_qEven_sub_odd_entry hbeta]
  have htanh : 0 < Real.tanh beta := z2_tanh_pos hbeta
  linarith

end YangMills.OS
