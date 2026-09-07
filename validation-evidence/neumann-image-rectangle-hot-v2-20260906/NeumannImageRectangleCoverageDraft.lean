import YangMills.RG.NeumannImageIntervalCoverage
import YangMills.RG.BalabanCMP89NeumannReflectionRepresentation
import Mathlib.Logic.Equiv.Prod

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
  Equiv.subtypePiEquivPi (β := fun _ : Fin d => ℤ)
    (p := fun mu n => 0 ≤ n ∧ n < m mu)

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
