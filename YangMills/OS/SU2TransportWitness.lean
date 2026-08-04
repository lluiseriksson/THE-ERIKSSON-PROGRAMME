/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson
-/
import YangMills.ClayCore.SchurTwoSitePhase
import YangMills.L0_Lattice.SU2Basic
import YangMills.OS.DobrushinTransport

/-!
# An exact SU(2)-inhabited witness for the abstract transport theorem

`Dobrushin.abstract_uniform_gap` is finite-dimensional: its slice type must be
finite.  This module therefore does not pretend that the whole compact group
`SU(2)` is finite.  Instead it builds a two-point finite carrier whose points
*contain actual bundled elements of* `Matrix.specialUnitaryGroup (Fin 2) ℂ`.
The two holonomies are the identity and the diagonal phase `diag(I,-I)`.

The transfer kernel is the exact two-state heat-mode kernel with rate
`exp (-3t/4)`, the fundamental `SU(2)` Casimir heat factor.  All facts consumed
by the published transport endpoint are proved here: the two matrices really
are special unitary, the carrier points are distinct, the kernel is symmetric,
the constant boundary vector is fixed, every band covariance has an exact
closed form, and the fluctuation sector is nonzero.

Scope: this is an exact finite witness for the transport *interface*.  It is
not a construction of the full continuous `SU(2)` heat-kernel operator and it
does not add a Yang--Mills corollary to the Dobrushin--Ising theorem.
-/

noncomputable section

namespace YangMills.OS.Dobrushin.SU2Transport

open Finset
open scoped RealInnerProductSpace

/-- The nonidentity holonomy used by the finite carrier: `diag(I,-I)`, bundled
as a genuine element of `SU(2)` by the existing determinant and unitarity
proofs in `SchurTwoSitePhase`. -/
def phaseHolonomy : YangMills.SU2 :=
  YangMills.ClayCore.twoSiteSU (0 : Fin 2) (1 : Fin 2) (by decide)

/-- The two exact `SU(2)` holonomies underlying the witness. -/
def holonomy (i : Fin 2) : YangMills.SU2 :=
  if i = 0 then 1 else phaseHolonomy

/-- Every witness holonomy satisfies the unitary half of `SU(2)` membership. -/
theorem holonomy_unitary (i : Fin 2) :
    (holonomy i).val ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
  (Matrix.mem_specialUnitaryGroup_iff.mp (holonomy i).property).1

/-- Every witness holonomy has determinant exactly one. -/
theorem holonomy_det (i : Fin 2) : Matrix.det (holonomy i).val = 1 :=
  (Matrix.mem_specialUnitaryGroup_iff.mp (holonomy i).property).2

/-- The phase point is not the identity; the `(0,0)` entry is `I`, not `1`. -/
theorem phaseHolonomy_ne_one : phaseHolonomy ≠ (1 : YangMills.SU2) := by
  intro h
  have h00 := congrArg (fun g : YangMills.SU2 => g.val 0 0) h
  simp [phaseHolonomy, YangMills.ClayCore.twoSiteSU_val,
    YangMills.ClayCore.twoSitePhase, YangMills.ClayCore.twoSiteVec] at h00
  have him := congrArg Complex.im h00
  norm_num at him

/-- The two labels select two distinct actual `SU(2)` elements. -/
theorem holonomy_injective : Function.Injective holonomy := by
  intro i j hij
  fin_cases i <;> fin_cases j
  · rfl
  · exact False.elim (phaseHolonomy_ne_one (by simpa [holonomy] using hij.symm))
  · exact False.elim (phaseHolonomy_ne_one (by simpa [holonomy] using hij))
  · rfl

/-- A finite state is a label together with an actual `SU(2)` holonomy and the
exact equation identifying which holonomy it is. -/
def Carrier := Σ i : Fin 2, {g : YangMills.SU2 // g = holonomy i}

/-- Canonical equivalence between the two labels and the `SU(2)`-valued
carrier.  This equivalence supplies the finite enumeration used in every sum. -/
def carrierEquiv : Fin 2 ≃ Carrier where
  toFun i := ⟨i, ⟨holonomy i, rfl⟩⟩
  invFun x := x.1
  left_inv _ := rfl
  right_inv := by
    rintro ⟨i, ⟨g, hg⟩⟩
    subst g
    rfl

instance : Fintype Carrier := Fintype.ofEquiv (Fin 2) carrierEquiv
noncomputable instance : DecidableEq Carrier := Classical.decEq Carrier
instance : Nonempty Carrier := ⟨carrierEquiv 0⟩

/-- The actual bundled `SU(2)` matrix carried by a finite state. -/
def Carrier.matrix (x : Carrier) : YangMills.SU2 := x.2.1

@[simp] theorem carrier_matrix_eq (x : Carrier) : x.matrix = holonomy x.1 :=
  x.2.2

@[simp] theorem carrierEquiv_label (i : Fin 2) : (carrierEquiv i).1 = i := rfl

/-- Two carrier states are equal as soon as their finite labels are equal;
the holonomy fiber over each label is a singleton by construction. -/
theorem Carrier.ext {x y : Carrier} (h : x.1 = y.1) : x = y := by
  apply carrierEquiv.symm.injective
  exact h

/-- Exact enumeration of any scalar sum over the `SU(2)` carrier. -/
theorem sum_carrier {R : Type*} [AddCommMonoid R] (F : Carrier → R) :
    ∑ x : Carrier, F x = F (carrierEquiv 0) + F (carrierEquiv 1) := by
  calc
    ∑ x : Carrier, F x = ∑ i : Fin 2, F (carrierEquiv i) := by
      exact Fintype.sum_equiv carrierEquiv.symm F
        (fun i : Fin 2 => F (carrierEquiv i)) (fun x => by simp)
    _ = F (carrierEquiv 0) + F (carrierEquiv 1) := Fin.sum_univ_two _

/-- The fundamental `SU(2)` heat-mode rate, corresponding to Casimir `3/4`. -/
def heatRate (t : ℝ) : ℝ := Real.exp (-(3 * t / 4))

theorem heatRate_pos (t : ℝ) : 0 < heatRate t := Real.exp_pos _

theorem heatRate_lt_one {t : ℝ} (ht : 0 < t) : heatRate t < 1 := by
  apply Real.exp_lt_one_iff.mpr
  dsimp [heatRate]
  linarith

/-- The exact two-state kernel, now indexed by states that carry actual
`SU(2)` holonomies. -/
def kernel (r : ℝ) : Matrix Carrier Carrier ℝ :=
  fun x y => wKernel r x.1 y.1

theorem kernel_symm (r : ℝ) : ∀ x y, kernel r x y = kernel r y x := by
  intro x y
  exact wKernel_symm r x.1 y.1

theorem kernel_row (r : ℝ) :
    ∀ x : Carrier, ∑ y, kernel r x y * (1 : ℝ) = 1 := by
  intro x
  rw [sum_carrier]
  simpa [kernel, Fin.sum_univ_two] using wKernel_row r x.1

/-- Matrix powers retain the same two-state form, with rate `r^n`. -/
theorem kernel_pow (r : ℝ) : ∀ n : ℕ, ∀ x y : Carrier,
    (kernel r ^ n) x y = wKernel (r ^ n) x.1 y.1 := by
  intro n
  induction n with
  | zero =>
      intro x y
      rw [pow_zero, pow_zero]
      simp only [Matrix.one_apply]
      by_cases h : x.1 = y.1
      · have hxy : x = y := Carrier.ext h
        rw [if_pos hxy]
        simp [wKernel, h]
      · have hxy : x ≠ y := fun hxy => h (congrArg Sigma.fst hxy)
        rw [if_neg hxy]
        simp [wKernel, h]
  | succ n ih =>
      intro x y
      rw [pow_succ, Matrix.mul_apply]
      simp_rw [ih]
      rw [sum_carrier]
      have hpow := congrArg
        (fun A : Matrix (Fin 2) (Fin 2) ℝ => A x.1 y.1)
        (wKernel_pow r (n + 1))
      change ((wKernel r) ^ (n + 1)) x.1 y.1 =
        wKernel (r ^ (n + 1)) x.1 y.1 at hpow
      rw [pow_succ, Matrix.mul_apply, wKernel_pow r n,
        Fin.sum_univ_two] at hpow
      simpa [kernel] using hpow

/-- Closed form of every band covariance on the genuine `SU(2)` carrier. -/
theorem kernel_bandCov (r : ℝ) (n : ℕ) (f : Carrier → ℝ) :
    bandCov (kernel r) (fun _ => 1) n f f =
      ((f (carrierEquiv 0) - f (carrierEquiv 1)) / 2) ^ 2 * r ^ n := by
  unfold bandCov
  rw [band_pair (kernel r) (fun _ => 1) n f f]
  simp_rw [kernel_pow r n]
  unfold bandE
  simp_rw [sum_carrier]
  have h00 : wKernel (r ^ n) 0 0 = (1 + r ^ n) / 2 := if_pos rfl
  have h11 : wKernel (r ^ n) 1 1 = (1 + r ^ n) / 2 := if_pos rfl
  have h01 : wKernel (r ^ n) 0 1 = (1 - r ^ n) / 2 := if_neg (by decide)
  have h10 : wKernel (r ^ n) 1 0 = (1 - r ^ n) / 2 := if_neg (by decide)
  simp only [carrierEquiv_label, mul_one]
  rw [h00, h01, h10, h11]
  ring

/-- The exact covariance identity immediately discharges the decay premise;
the desired property is not loaded as a hypothesis. -/
theorem kernel_bandDecay {r : ℝ} (hr : 0 ≤ r) (n : ℕ) (f : Carrier → ℝ) :
    |bandCov (kernel r) (fun _ => 1) n f f| ≤
      ((f (carrierEquiv 0) - f (carrierEquiv 1)) / 2) ^ 2 * r ^ n := by
  rw [kernel_bandCov]
  exact le_of_eq (abs_of_nonneg (mul_nonneg (sq_nonneg _) (pow_nonneg hr n)))

/-- The exact sign observable on the two distinct `SU(2)` carrier points. -/
def signVector : EuclideanSpace ℝ Carrier :=
  WithLp.toLp 2 fun x => if x.1 = 0 then 1 else -1

@[simp] theorem signVector_zero : signVector (carrierEquiv 0) = 1 := by
  simp [signVector]

@[simp] theorem signVector_one : signVector (carrierEquiv 1) = -1 := by
  simp [signVector]

theorem signVector_ne_zero : signVector ≠ 0 := by
  intro h
  have h0 := congrArg (fun v : EuclideanSpace ℝ Carrier => v (carrierEquiv 0)) h
  norm_num at h0

/-- The sign observable is exactly orthogonal to the constant vacuum. -/
theorem inner_vac_sign :
    ⟪vacOf (fun _ : Carrier => (1 : ℝ)), signVector⟫ = 0 := by
  have hvac (x : Carrier) :
      vacOf (fun _ : Carrier => (1 : ℝ)) x = 1 / Real.sqrt 2 := by
    change 1 / Real.sqrt (∑ _y : Carrier, (1 : ℝ) * 1) = _
    rw [sum_carrier]
    norm_num
  rw [inner_eq_sum, sum_carrier, hvac, hvac,
    signVector_zero, signVector_one]
  ring

/-- Decisive nontriviality identity: the projected transfer operator sends
the exact sign fluctuation to `r` times itself (shown at the zero state). -/
theorem projected_apply_sign_zero (r : ℝ) :
    projectedTransfer (opOf (kernel r))
      (vacOf (fun _ : Carrier => (1 : ℝ))) signVector (carrierEquiv 0) = r := by
  rw [projectedTransfer_apply, inner_vac_sign, zero_smul]
  have hsub :
      (opOf (kernel r) signVector -
        (0 : EuclideanSpace ℝ Carrier)) (carrierEquiv 0) =
        opOf (kernel r) signVector (carrierEquiv 0) := by
    rw [sub_zero]
  rw [hsub, opOf_apply, sum_carrier, signVector_zero, signVector_one]
  have h00 : wKernel r 0 0 = (1 + r) / 2 := if_pos rfl
  have h01 : wKernel r 0 1 = (1 - r) / 2 := if_neg (by decide)
  simp only [kernel, carrierEquiv_label]
  rw [h00, h01]
  ring

/-- The fluctuation sector is exactly nonzero whenever the heat rate is. -/
theorem projected_ne_zero (r : ℝ) (hr : r ≠ 0) :
    projectedTransfer (opOf (kernel r))
      (vacOf (fun _ : Carrier => (1 : ℝ))) ≠ 0 := by
  intro hzero
  have happ := projected_apply_sign_zero r
  rw [hzero] at happ
  norm_num at happ
  exact hr happ.symm

/-- **Exact SU(2) transport witness.**  For every positive heat time, the
finite carrier contains two distinct genuine `SU(2)` holonomies and satisfies
every premise of `abstract_uniform_gap` at the exact fundamental heat rate
`exp(-3t/4)`.  The theorem fires end-to-end, while the exact sign identity
proves that its projected transfer operator is not zero. -/
theorem exact_transport_witness {t : ℝ} (ht : 0 < t) :
    (∃ m : ℝ, 0 < m ∧
      ‖projectedTransfer (opOf (kernel (heatRate t)))
        (vacOf (fun _ : Carrier => (1 : ℝ)))‖ ≤ Real.exp (-m))
    ∧ projectedTransfer (opOf (kernel (heatRate t)))
        (vacOf (fun _ : Carrier => (1 : ℝ))) ≠ 0 := by
  have hr0 : 0 < heatRate t := heatRate_pos t
  have hr1 : heatRate t < 1 := heatRate_lt_one ht
  constructor
  · obtain ⟨m, hm, hall⟩ := abstract_uniform_gap (ι := Unit)
      (Xs := fun _ => Carrier)
      (fun _ => kernel (heatRate t)) (fun _ => fun _ => (1 : ℝ))
      (fun _ => kernel_symm (heatRate t)) (fun _ => fun _ => one_pos)
      (fun _ => kernel_row (heatRate t)) hr0 hr1
      (fun _ => fun f =>
        ⟨((f (carrierEquiv 0) - f (carrierEquiv 1)) / 2) ^ 2,
          fun n => kernel_bandDecay hr0.le n f⟩)
    exact ⟨m, hm, hall ()⟩
  · exact projected_ne_zero (heatRate t) hr0.ne'

end YangMills.OS.Dobrushin.SU2Transport

end
