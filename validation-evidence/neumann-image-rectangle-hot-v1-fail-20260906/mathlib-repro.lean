import Mathlib.Logic.Equiv.Prod
import Mathlib.Data.Int.DivMod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
PRE-VALIDATION: promoted source present, .olean not materialized, not compiler-verified.
Exact draft proof bodies passed HOT at99d0767ec (ledger1139); no cold seal yet.
The full family varies translation, parity and the original point in [0,m).
Its period 2*m is not the generated owner divisor M^depth.
This is a one-dimensional index bijection, not summability or a Green inverse.
-/

namespace YangMills.RG

def cmp89NeumannReflectionOrbit (m n k : ℤ) (reflected : Bool) : ℤ :=
  if reflected then 2 * k * m - n - 1 else 2 * k * m + n

@[simp] theorem cmp89NeumannReflectionOrbit_false (m n k : ℤ) :
    cmp89NeumannReflectionOrbit m n k false = 2 * k * m + n := by
  rfl

@[simp] theorem cmp89NeumannReflectionOrbit_true (m n k : ℤ) :
    cmp89NeumannReflectionOrbit m n k true = 2 * k * m - n - 1 := by
  rfl

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
  simp only [cmp89NeumannReflectionOrbit_false] at h ⊢
  nlinarith

theorem neumannOrbitTrue_periodRemainder
    (m : ℤ) (hm : 0 < m) (n : neumannImageIntervalPoint m) (k : ℤ) :
    cmp89NeumannReflectionOrbit m n.1 k true % (2 * m) = 2 * m - n.1 - 1 := by
  have h := Int.ediv_mul_add_emod
    (cmp89NeumannReflectionOrbit m n.1 k true) (2 * m)
  rw [neumannOrbitTrue_periodQuotient m hm n k] at h
  simp only [cmp89NeumannReflectionOrbit_true] at h ⊢
  nlinarith

/-- Unlike fixed-image injectivity, this varies translation, parity and the
original coordinate together. The half-open interval is portante. -/
theorem neumannImageIntervalFamily_injective (m : ℤ) (hm : 0 < m) :
    Function.Injective (fun p : ℤ × Bool × neumannImageIntervalPoint m =>
      cmp89NeumannReflectionOrbit m p.2.2.1 p.1 p.2.1) := by
  rintro ⟨k, b, n⟩ ⟨l, c, v⟩ he
  change cmp89NeumannReflectionOrbit m n.1 k b =
    cmp89NeumannReflectionOrbit m v.1 l c at he
  have hq := congrArg (fun u : ℤ => u / (2 * m)) he
  have hr := congrArg (fun u : ℤ => u % (2 * m)) he
  change cmp89NeumannReflectionOrbit m n.1 k b / (2 * m) =
    cmp89NeumannReflectionOrbit m v.1 l c / (2 * m) at hq
  change cmp89NeumannReflectionOrbit m n.1 k b % (2 * m) =
    cmp89NeumannReflectionOrbit m v.1 l c % (2 * m) at hr
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
    have hk : k = l := by omega
    have hn : n.1 = v.1 := by omega
    exact Prod.ext hk (Prod.ext rfl (Subtype.ext hn))

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

namespace YangMills.RG
variable {d : ℕ}
abbrev CMP89NeumannReflectionBranch (d : ℕ) := Fin d → Bool

def cmp89NeumannReflectionImage {d : ℕ}
    (m n k : Fin d → ℤ) (branch : CMP89NeumannReflectionBranch d) :
    Fin d → ℤ :=
  fun mu => cmp89NeumannReflectionOrbit (m mu) (n mu) (k mu) (branch mu)

@[simp] theorem cmp89NeumannReflectionImage_apply {d : ℕ}
    (m n k : Fin d → ℤ) (branch : CMP89NeumannReflectionBranch d)
    (mu : Fin d) :
    cmp89NeumannReflectionImage m n k branch mu =
      cmp89NeumannReflectionOrbit (m mu) (n mu) (k mu) (branch mu) := by
  rfl

def cmp89SourceNeumannBlockIntegerRectangle {d : ℕ} (m : Fin d → ℤ) :
    Set (Fin d → ℤ) :=
  {n | ∀ mu, 0 ≤ n mu ∧ n mu < m mu}

abbrev CMP89SourceNeumannIntegerRectanglePoint (m : Fin d → ℤ) :=
  {n : Fin d → ℤ // n ∈ cmp89SourceNeumannBlockIntegerRectangle m}

end YangMills.RG

/-!
PRE-VALIDATION: source present, .olean not materialized, not compiler-verified.

R2a rectangular image-family coverage. The source carrier is the literal
CMP89 half-open rectangle, not a separately chosen coordinate subtype.
All coordinate side lengths are positive. Period 2*m is unrelated to the
generated block divisor M^depth. No summability or Green inverse is asserted.
Prepared while the interval promotion cold gate runs; do not execute before
that dependency is sealed. Proof assembly uses existing Mathlib equivalences.
-/

namespace YangMills.RG

noncomputable section

/-- Definitional packaging of the literal rectangle as its bounded coordinates. -/
def neumannImageRectangleCoordinateEquiv {d : ℕ} (m : Fin d → ℤ) :
    CMP89SourceNeumannIntegerRectanglePoint m ≃
      (∀ mu : Fin d, neumannImageIntervalPoint (m mu)) :=
  Equiv.subtypePiEquivPi

/-- Assemble the translation, parity and original point coordinatewise.
This changes only the packaging, not a coordinate or the image convention. -/
def neumannImageRectangleIndexEquiv {d : ℕ} (m : Fin d → ℤ) :
    ((Fin d → ℤ) × CMP89NeumannReflectionBranch d ×
      CMP89SourceNeumannIntegerRectanglePoint m) ≃
      (∀ mu : Fin d, ℤ × Bool × neumannImageIntervalPoint (m mu)) :=
  let e1 := (Equiv.refl (Fin d → ℤ)).prodCongr
    ((Equiv.refl (CMP89NeumannReflectionBranch d)).prodCongr
      (neumannImageRectangleCoordinateEquiv m))
  let e2 := (Equiv.refl (Fin d → ℤ)).prodCongr
    (Equiv.arrowProdEquivProdArrow (Fin d) (fun _ => Bool)
      (fun mu => neumannImageIntervalPoint (m mu))).symm
  let e3 := (Equiv.arrowProdEquivProdArrow (Fin d) (fun _ => ℤ)
    (fun mu => Bool × neumannImageIntervalPoint (m mu))).symm
  (e1.trans e2).trans e3

theorem neumannImageRectangleIndexEquiv_apply {d : ℕ}
    (m : Fin d → ℤ)
    (p : (Fin d → ℤ) × CMP89NeumannReflectionBranch d ×
      CMP89SourceNeumannIntegerRectanglePoint m) (mu : Fin d) :
    neumannImageRectangleIndexEquiv m p mu =
      (p.1 mu, p.2.1 mu, ⟨p.2.2.1 mu, p.2.2.2 mu⟩) := rfl

/-- The interval image equivalences generate coverage of all integer vectors.
The target is not clipped to the original rectangle. -/
def neumannImageRectangleFamilyEquiv {d : ℕ}
    (m : Fin d → ℤ) (hm : ∀ mu, 0 < m mu) :
    ((Fin d → ℤ) × CMP89NeumannReflectionBranch d ×
      CMP89SourceNeumannIntegerRectanglePoint m) ≃ (Fin d → ℤ) :=
  (neumannImageRectangleIndexEquiv m).trans
    (Equiv.piCongrRight (fun mu : Fin d =>
      Equiv.ofBijective
        (fun p : ℤ × Bool × neumannImageIntervalPoint (m mu) =>
          cmp89NeumannReflectionOrbit (m mu) p.2.2.1 p.1 p.2.1)
        (neumannImageIntervalFamily_bijective (m mu) (hm mu))))

/-- The constructed equivalence is exactly the printed image, not a free map. -/
theorem neumannImageRectangleFamilyEquiv_apply {d : ℕ}
    (m : Fin d → ℤ) (hm : ∀ mu, 0 < m mu)
    (p : (Fin d → ℤ) × CMP89NeumannReflectionBranch d ×
      CMP89SourceNeumannIntegerRectanglePoint m) :
    neumannImageRectangleFamilyEquiv m hm p =
      cmp89NeumannReflectionImage m p.2.2.1 p.1 p.2.1 := rfl

theorem neumannImageRectangleFamily_bijective {d : ℕ}
    (m : Fin d → ℤ) (hm : ∀ mu, 0 < m mu) :
    Function.Bijective
      (fun p : (Fin d → ℤ) × CMP89NeumannReflectionBranch d ×
        CMP89SourceNeumannIntegerRectanglePoint m =>
        cmp89NeumannReflectionImage m p.2.2.1 p.1 p.2.1) :=
  (neumannImageRectangleFamilyEquiv m hm).bijective

/-- Varying translation/parity at one fixed original point is injective.
This is the orientation needed to restrict a summable full-lattice kernel. -/
theorem neumannImageRectangle_fixedPoint_injective {d : ℕ}
    (m : Fin d → ℤ) (hm : ∀ mu, 0 < m mu)
    (n : CMP89SourceNeumannIntegerRectanglePoint m) :
    Function.Injective (fun p : (Fin d → ℤ) × CMP89NeumannReflectionBranch d =>
      cmp89NeumannReflectionImage m n.1 p.1 p.2) := by
  intro p q he
  have hfull : (p.1, p.2, n) = (q.1, q.2, n) :=
    (neumannImageRectangleFamily_bijective m hm).1 he
  have hk : p.1 = q.1 := congrArg
    (fun a : (Fin d → ℤ) × CMP89NeumannReflectionBranch d ×
      CMP89SourceNeumannIntegerRectanglePoint m => a.1) hfull
  have hb : p.2 = q.2 := congrArg
    (fun a : (Fin d → ℤ) × CMP89NeumannReflectionBranch d ×
      CMP89SourceNeumannIntegerRectanglePoint m => a.2.1) hfull
  exact Prod.ext hk hb

end
end YangMills.RG

#print axioms YangMills.RG.neumannImageRectangleCoordinateEquiv
#print axioms YangMills.RG.neumannImageRectangleIndexEquiv_apply
#print axioms YangMills.RG.neumannImageRectangleFamilyEquiv_apply
#print axioms YangMills.RG.neumannImageRectangleFamily_bijective
#print axioms YangMills.RG.neumannImageRectangle_fixedPoint_injective
