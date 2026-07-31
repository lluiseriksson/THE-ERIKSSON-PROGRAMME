import YangMills.L0_Lattice.SU2Basic
import YangMills.ClayCore.ContinuousUnitaryRep
import YangMills.ClayCore.SchurNormSquared
import YangMills.ClayCore.SchurPhysicalBridge
import YangMills.SU2ThetaPrism.Combinatorics

/-!
# Concrete SU(2) data on the abstract theta-prism cell

No definition in this file is a `GaugeConfig`, a physical plaquette, or a
continuous reflection splitting.
-/

noncomputable section

open Matrix Complex

namespace YangMills.SU2ThetaPrism

/-- The eight group variables of the abstract cell. -/
structure CellConfiguration where
  A : Branch → SU2
  B : Branch → SU2
  s : SU2
  t : SU2

/-- Point reflection swaps the two branch families and reverses the two
transversals. -/
def reflect (c : CellConfiguration) : CellConfiguration where
  A := c.B
  B := c.A
  s := c.s⁻¹
  t := c.t⁻¹

@[simp] theorem reflect_A (c : CellConfiguration) (i : Branch) :
    (reflect c).A i = c.B i := rfl

@[simp] theorem reflect_B (c : CellConfiguration) (i : Branch) :
    (reflect c).B i = c.A i := rfl

@[simp] theorem reflect_s (c : CellConfiguration) : (reflect c).s = c.s⁻¹ := rfl
@[simp] theorem reflect_t (c : CellConfiguration) : (reflect c).t = c.t⁻¹ := rfl

theorem reflect_involutive : Function.Involutive reflect := by
  intro c
  cases c
  simp [reflect]

/-- Registered branch holonomy `s A_i t⁻¹ B_i⁻¹`. -/
def holonomy (c : CellConfiguration) (i : Branch) : SU2 :=
  c.s * c.A i * c.t⁻¹ * (c.B i)⁻¹

/-- The reflection identity is derived from the concrete cell definitions. -/
theorem holonomy_reflect (c : CellConfiguration) (i : Branch) :
    holonomy (reflect c) i = c.s⁻¹ * (holonomy c i)⁻¹ * c.s := by
  simp [holonomy, reflect, mul_assoc]

/-- Relative upper-branch variable `A0⁻¹ A1`. -/
def relativeU (c : CellConfiguration) : SU2 :=
  (c.A 0)⁻¹ * c.A 1

/-- Relative upper-branch variable `A0⁻¹ A2`. -/
def relativeV (c : CellConfiguration) : SU2 :=
  (c.A 0)⁻¹ * c.A 2

/-- Fundamental SU(2) character, concretely the matrix trace. -/
def chi (g : SU2) : ℂ :=
  g.val.trace

@[simp] theorem chi_one : chi (1 : SU2) = 2 := by
  simp [chi, Matrix.trace_one]

/-- The concrete defining representation, constructed locally to avoid
importing any lattice or physical-state layer. -/
def fundamentalRep :
    YangMills.ClayCore.ContinuousUnitaryMatrixRep SU2 (Fin 2) where
  toMonoidHom :=
    { toFun := fun U => ⟨U.val, U.property.1⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  continuous_toFun :=
    Continuous.subtype_mk continuous_subtype_val (fun U => U.property.1)

/-- Character invariance under simultaneous conjugation in the locally
constructed fundamental representation. -/
theorem chi_conj (h g : SU2) :
    chi (h * g * h⁻¹) = chi g := by
  simpa [chi] using
    (YangMills.ClayCore.ContinuousUnitaryMatrixRep.character_conj
      fundamentalRep h g)

/-- Characters commute across a two-factor product. -/
theorem chi_mul_comm (g h : SU2) : chi (g * h) = chi (h * g) := by
  have hc := chi_conj g (h * g)
  simpa [mul_assoc] using hc

/-- Reality of the SU(2) fundamental trace is isolated as a named analytic
brick.  It is not definitionally built into `chi`. -/
structure TraceRealityCertificate : Prop where
  star_chi : ∀ g : SU2, star (chi g) = chi g

/-- The inverse of a determinant-one two-by-two matrix has the same trace.
This proof is kept local instead of importing the draft PR #39 lemma. -/
theorem chi_inv_concrete (g : SU2) : chi g⁻¹ = chi g := by
  have hg_right := congrArg Subtype.val (mul_inv_cancel g)
  change g.val * (g⁻¹).val = (1 : Matrix (Fin 2) (Fin 2) ℂ) at hg_right
  have hg_det : Matrix.det g.val = 1 := g.property.2
  have hadj_left : Matrix.adjugate g.val * g.val = 1 := by
    rw [Matrix.adjugate_mul, hg_det, one_smul]
  have hinv : (g⁻¹).val = Matrix.adjugate g.val := by
    calc
      (g⁻¹).val = 1 * (g⁻¹).val := by simp
      _ = (Matrix.adjugate g.val * g.val) * (g⁻¹).val := by rw [hadj_left]
      _ = Matrix.adjugate g.val * (g.val * (g⁻¹).val) :=
        Matrix.mul_assoc _ _ _
      _ = Matrix.adjugate g.val := by rw [hg_right, Matrix.mul_one]
  change Matrix.trace (g⁻¹).val = Matrix.trace g.val
  rw [hinv, Matrix.adjugate_fin_two]
  simp [Matrix.trace_fin_two, add_comm]

/-- Concrete SU(2) trace reality, derived from determinant one and unitarity. -/
theorem chi_star_eq (g : SU2) : star (chi g) = chi g := by
  change star g.val.trace = g.val.trace
  rw [← YangMills.trace_inv_eq_star_trace_SU g]
  exact chi_inv_concrete g

/-- A concrete inhabitant of the former trace-reality input. -/
def traceRealityConcrete : TraceRealityCertificate :=
  ⟨chi_star_eq⟩

theorem chi_inv (reality : TraceRealityCertificate) (g : SU2) :
    chi g⁻¹ = chi g := by
  have hinv : (g⁻¹ : SU2).val = star g.val := rfl
  rw [chi, hinv]
  rw [show (star g.val).trace = star g.val.trace by
    rw [show (star g.val : Matrix (Fin 2) (Fin 2) ℂ) = g.valᴴ from rfl]
    exact Matrix.trace_conjTranspose g.val]
  exact reality.star_chi g

/-- Real Wilson factor used in the registered weight.  Once trace reality is
discharged this is exactly the exponential of `(beta/2) chi`. -/
def branchWeight (beta : ℝ) (g : SU2) : ℝ :=
  Real.exp ((beta / 2) * (chi g).re)

/-- Product of the three registered branch factors. -/
def cellWeight (beta : ℝ) (c : CellConfiguration) : ℝ :=
  ∏ i : Branch, branchWeight beta (holonomy c i)

theorem branchWeight_conj_inv (reality : TraceRealityCertificate)
    (beta : ℝ) (s g : SU2) :
    branchWeight beta (s⁻¹ * g⁻¹ * s) = branchWeight beta g := by
  simp only [branchWeight]
  have hconj : chi (s⁻¹ * g⁻¹ * s) = chi g⁻¹ := by
    simpa using chi_conj s⁻¹ g⁻¹
  rw [hconj]
  rw [chi_inv reality]

theorem cellWeight_reflection_invariant (reality : TraceRealityCertificate)
    (beta : ℝ) (c : CellConfiguration) :
    cellWeight beta (reflect c) = cellWeight beta c := by
  unfold cellWeight
  apply Finset.prod_congr rfl
  intro i _
  rw [holonomy_reflect]
  exact branchWeight_conj_inv reality beta c.s (holonomy c i)

/-- A separate bound certificate avoids hiding the analytic SU(2) trace bound
inside the definition of the weight. -/
structure CharacterBoundCertificate : Prop where
  abs_re_chi_le_two : ∀ g : SU2, |(chi g).re| ≤ 2

/-- A concrete inhabitant of the sharp fundamental-character bound. -/
def characterBoundConcrete : CharacterBoundCertificate := by
  constructor
  intro g
  simpa [chi, YangMills.fundamentalObservable] using
    (YangMills.fundamentalObservable_bounded 2 g)

theorem branchWeight_le_exp_abs (bound : CharacterBoundCertificate)
    (beta : ℝ) (g : SU2) :
    branchWeight beta g ≤ Real.exp |beta| := by
  apply Real.exp_le_exp.mpr
  have hb := bound.abs_re_chi_le_two g
  have hhalf : |(beta / 2) * (chi g).re| ≤ |beta| := by
    calc
      |(beta / 2) * (chi g).re| = |beta / 2| * |(chi g).re| := abs_mul _ _
      _ ≤ |beta / 2| * 2 :=
        mul_le_mul_of_nonneg_left hb (abs_nonneg (beta / 2))
      _ = |beta| := by rw [abs_div]; norm_num
  exact le_trans (le_abs_self _) hhalf

theorem cellWeight_nonnegative (beta : ℝ) (c : CellConfiguration) :
    0 ≤ cellWeight beta c := by
  exact Finset.prod_nonneg fun _ _ => (Real.exp_pos _).le

theorem cellWeight_le_exp_three_abs (bound : CharacterBoundCertificate)
    (beta : ℝ) (c : CellConfiguration) :
    cellWeight beta c ≤ Real.exp (3 * |beta|) := by
  calc
    cellWeight beta c ≤ ∏ _i : Branch, Real.exp |beta| := by
      exact Finset.prod_le_prod (fun _ _ => (Real.exp_pos _).le)
        (fun i _ => branchWeight_le_exp_abs bound beta (holonomy c i))
    _ = (Real.exp |beta|) ^ 3 := by simp [Finset.prod_const]
    _ = Real.exp (3 * |beta|) := by
      rw [show 3 * |beta| = |beta| + |beta| + |beta| by ring,
        Real.exp_add, Real.exp_add]
      ring

end YangMills.SU2ThetaPrism
