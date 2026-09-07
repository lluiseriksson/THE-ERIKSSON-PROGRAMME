import YangMills.RG.BalabanCMP89NeumannReflectionOrbitAlgebra
import Mathlib.Data.Int.DivMod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
PRE-VALIDATION: source present, .olean not materialized, not compiler-verified.

Independent R2 image-family coverage, using only the already sealed printed
one-coordinate orbit. Not dependent on the finite-Q draft currently in HOT.
The original coordinate lies in the HALF-OPEN integer interval [0,m).
Period 2*m is distinct from the generated block-owner divisor B=M^depth.
This is an exact index bijection, not summability or a Green inverse.
-/

namespace YangMills.RG

def neumannImageIntervalPoint (m : ℤ) := {n : ℤ // 0 ≤ n ∧ n < m}

theorem neumannOrbitFalse_periodQuotient
    (m : ℤ) (hm : 0 < m) (n : neumannImageIntervalPoint m) (k : ℤ) :
    cmp89NeumannReflectionOrbit m n.1 k false / (2 * m) = k := by
  rw [Int.ediv_eq_iff_of_pos (by omega : 0 < 2 * m)]
  simp only [cmp89NeumannReflectionOrbit_false]
  have hn0 := n.2.1
  have hn1 := n.2.2
  constructor <;> nlinarith

theorem neumannOrbitTrue_periodQuotient
    (m : ℤ) (hm : 0 < m) (n : neumannImageIntervalPoint m) (k : ℤ) :
    cmp89NeumannReflectionOrbit m n.1 k true / (2 * m) = k - 1 := by
  rw [Int.ediv_eq_iff_of_pos (by omega : 0 < 2 * m)]
  simp only [cmp89NeumannReflectionOrbit_true]
  have hn0 := n.2.1
  have hn1 := n.2.2
  constructor <;> nlinarith

theorem neumannOrbitFalse_periodRemainder
    (m : ℤ) (hm : 0 < m) (n : neumannImageIntervalPoint m) (k : ℤ) :
    cmp89NeumannReflectionOrbit m n.1 k false % (2 * m) = n.1 := by
  have h := Int.ediv_mul_add_emod
    (cmp89NeumannReflectionOrbit m n.1 k false) (2 * m)
  rw [neumannOrbitFalse_periodQuotient m hm n k] at h
  simp only [cmp89NeumannReflectionOrbit_false] at h
  nlinarith

theorem neumannOrbitTrue_periodRemainder
    (m : ℤ) (hm : 0 < m) (n : neumannImageIntervalPoint m) (k : ℤ) :
    cmp89NeumannReflectionOrbit m n.1 k true % (2 * m) = 2 * m - n.1 - 1 := by
  have h := Int.ediv_mul_add_emod
    (cmp89NeumannReflectionOrbit m n.1 k true) (2 * m)
  rw [neumannOrbitTrue_periodQuotient m hm n k] at h
  simp only [cmp89NeumannReflectionOrbit_true] at h
  nlinarith

/-- Unlike fixed-image injectivity, this varies translation, parity and the
original coordinate together. The half-open interval is portante. -/
theorem neumannImageIntervalFamily_injective (m : ℤ) (hm : 0 < m) :
    Function.Injective (fun p : ℤ × Bool × neumannImageIntervalPoint m =>
      cmp89NeumannReflectionOrbit m p.2.2.1 p.1 p.2.1) := by
  rintro ⟨k, b, n⟩ ⟨l, c, v⟩ he
  have hq := congrArg (fun u : ℤ => u / (2 * m)) he
  have hr := congrArg (fun u : ℤ => u % (2 * m)) he
  cases b <;> cases c
  · rw [neumannOrbitFalse_periodQuotient m hm n k,
      neumannOrbitFalse_periodQuotient m hm v l] at hq
    rw [neumannOrbitFalse_periodRemainder m hm n k,
      neumannOrbitFalse_periodRemainder m hm v l] at hr
    exact Prod.ext hq (Prod.ext rfl (Subtype.ext hr))
  · rw [neumannOrbitFalse_periodRemainder m hm n k,
      neumannOrbitTrue_periodRemainder m hm v l] at hr
    have hn := n.2
    have hv := v.2
    exfalso
    omega
  · rw [neumannOrbitTrue_periodRemainder m hm n k,
      neumannOrbitFalse_periodRemainder m hm v l] at hr
    have hn := n.2
    have hv := v.2
    exfalso
    omega
  · rw [neumannOrbitTrue_periodQuotient m hm n k,
      neumannOrbitTrue_periodQuotient m hm v l] at hq
    rw [neumannOrbitTrue_periodRemainder m hm n k,
      neumannOrbitTrue_periodRemainder m hm v l] at hr
    exact Prod.ext (by omega) (Prod.ext rfl (Subtype.ext (by omega)))

/-- Constructed coverage of ALL integers, including negative translations;
the reflected branch uses quotient q+1, with no endpoint clipping. -/
theorem neumannImageIntervalFamily_surjective (m : ℤ) (hm : 0 < m) :
    Function.Surjective (fun p : ℤ × Bool × neumannImageIntervalPoint m =>
      cmp89NeumannReflectionOrbit m p.2.2.1 p.1 p.2.1) := by
  intro u
  have hm2 : 0 < 2 * m := by omega
  have hr0 := Int.emod_nonneg u (ne_of_gt hm2)
  have hr1 := Int.emod_lt_of_pos u hm2
  have hu := Int.ediv_mul_add_emod u (2 * m)
  by_cases hr : u % (2 * m) < m
  · refine ⟨⟨u / (2 * m), false, ⟨u % (2 * m), hr0, hr⟩⟩, ?_⟩
    simp only [cmp89NeumannReflectionOrbit_false]
    nlinarith
  · have hn0 : 0 ≤ 2 * m - u % (2 * m) - 1 := by omega
    have hn1 : 2 * m - u % (2 * m) - 1 < m := by omega
    refine ⟨⟨u / (2 * m) + 1, true,
      ⟨2 * m - u % (2 * m) - 1, hn0, hn1⟩⟩, ?_⟩
    simp only [cmp89NeumannReflectionOrbit_true]
    nlinarith

theorem neumannImageIntervalFamily_bijective (m : ℤ) (hm : 0 < m) :
    Function.Bijective (fun p : ℤ × Bool × neumannImageIntervalPoint m =>
      cmp89NeumannReflectionOrbit m p.2.2.1 p.1 p.2.1) :=
  ⟨neumannImageIntervalFamily_injective m hm,
    neumannImageIntervalFamily_surjective m hm⟩

end YangMills.RG

#print axioms YangMills.RG.neumannOrbitFalse_periodQuotient
#print axioms YangMills.RG.neumannOrbitTrue_periodQuotient
#print axioms YangMills.RG.neumannOrbitFalse_periodRemainder
#print axioms YangMills.RG.neumannOrbitTrue_periodRemainder
#print axioms YangMills.RG.neumannImageIntervalFamily_injective
#print axioms YangMills.RG.neumannImageIntervalFamily_surjective
#print axioms YangMills.RG.neumannImageIntervalFamily_bijective
