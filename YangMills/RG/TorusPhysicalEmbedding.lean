import YangMills.RG.TorusCountingParseval
import YangMills.RG.PhysicalGaugeCochains

/-! Constructed real-linear embeddings into the actual physical one-cochain
space, with the counting L2 norm proved exactly. No curl/divergence identity
or physical coercivity conclusion is asserted here. -/

namespace YangMills.RG

open scoped BigOperators RealInnerProductSpace

variable {d n Nc : ℕ} [NeZero n]

private theorem sunCoord_two_le (hNc : 2 ≤ Nc) : 2 ≤ Nc ^ 2 - 1 := by
  have hsq : 4 ≤ Nc ^ 2 := by nlinarith
  omega

noncomputable def sunComplexPlane (hNc : 2 ≤ Nc) (z : ℂ) : SUNLieCoord Nc :=
  EuclideanSpace.single ⟨0, by have := sunCoord_two_le hNc; omega⟩ z.re +
  EuclideanSpace.single ⟨1, by have := sunCoord_two_le hNc; omega⟩ z.im

@[simp] theorem sunComplexPlane_apply_zero (hNc : 2 ≤ Nc) (z : ℂ) :
    sunComplexPlane hNc z ⟨0, by have := sunCoord_two_le hNc; omega⟩ = z.re := by
  simp [sunComplexPlane, EuclideanSpace.single_apply]

@[simp] theorem sunComplexPlane_apply_one (hNc : 2 ≤ Nc) (z : ℂ) :
    sunComplexPlane hNc z ⟨1, by have := sunCoord_two_le hNc; omega⟩ = z.im := by
  simp [sunComplexPlane, EuclideanSpace.single_apply]

theorem sunComplexPlane_norm_sq (hNc : 2 ≤ Nc) (z : ℂ) :
    ‖sunComplexPlane hNc z‖ ^ 2 = ‖z‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  simp [sunComplexPlane, inner_add_left, inner_add_right,
    EuclideanSpace.inner_single_left, EuclideanSpace.single_apply,
    ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, pow_two]

noncomputable def finBoxZModEquiv (d n : ℕ) [NeZero n] :
    FinBox d n ≃ (Fin d → ZMod n) :=
  Equiv.piCongrRight (fun _ => (ZMod.finEquiv n).toEquiv)

/-- Put the real and imaginary parts in two distinct internal coordinates,
    at exactly one positively oriented bond direction. -/
noncomputable def torusPhysicalEmbed (hNc : 2 ≤ Nc) (j : Fin d)
    (f : (Fin d → ZMod n) → ℂ) : PhysicalGaugeOneCochain d n Nc :=
  WithLp.toLp 2 (fun e => if e.2 = j then
    sunComplexPlane hNc (f (finBoxZModEquiv d n e.1)) else 0)

theorem torusPhysicalEmbed_add (hNc : 2 ≤ Nc) (j : Fin d)
    (f g : (Fin d → ZMod n) → ℂ) :
    torusPhysicalEmbed hNc j (f + g) =
      torusPhysicalEmbed hNc j f + torusPhysicalEmbed hNc j g := by
  ext e i
  by_cases h : e.2 = j
  · simp [torusPhysicalEmbed, h, sunComplexPlane, EuclideanSpace.single_apply]
    split_ifs <;> simp_all <;> ring
  · simp [torusPhysicalEmbed, h]

theorem torusPhysicalEmbed_smul (hNc : 2 ≤ Nc) (j : Fin d) (r : ℝ)
    (f : (Fin d → ZMod n) → ℂ) :
    torusPhysicalEmbed hNc j (r • f) = r • torusPhysicalEmbed hNc j f := by
  ext e i
  by_cases h : e.2 = j
  · simp [torusPhysicalEmbed, h, sunComplexPlane, EuclideanSpace.single_apply]
    split_ifs <;> simp_all <;> ring
  · simp [torusPhysicalEmbed, h]

theorem torusPhysicalEmbed_norm_sq (hNc : 2 ≤ Nc) (j : Fin d)
    (f : (Fin d → ZMod n) → ℂ) :
    ‖torusPhysicalEmbed hNc j f‖ ^ 2 = countingL2Mass f := by
  classical
  rw [PiLp.norm_sq_eq_of_L2]
  change (∑ e : FinBox d n × Fin d,
    ‖if e.2 = j then sunComplexPlane hNc (f (finBoxZModEquiv d n e.1)) else 0‖ ^ 2) = _
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, norm_zero, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sunComplexPlane_norm_sq]
  exact Equiv.sum_comp (finBoxZModEquiv d n) (fun x => ‖f x‖ ^ 2)

theorem torusPhysicalEmbed_injective (hNc : 2 ≤ Nc) (j : Fin d) :
    Function.Injective (torusPhysicalEmbed (n := n) hNc j) := by
  intro f g h
  funext x
  let y := (finBoxZModEquiv d n).symm x
  have hy : finBoxZModEquiv d n y = x := (finBoxZModEquiv d n).apply_symm_apply x
  have hz := congrArg (fun A : PhysicalGaugeOneCochain d n Nc =>
    A (y, j)) h
  have hp : sunComplexPlane hNc (f x) = sunComplexPlane hNc (g x) := by
    simpa [torusPhysicalEmbed, hy] using hz
  apply Complex.ext
  · simpa using congrArg (fun v : SUNLieCoord Nc =>
      v ⟨0, by have := sunCoord_two_le hNc; omega⟩) hp
  · simpa using congrArg (fun v : SUNLieCoord Nc =>
      v ⟨1, by have := sunCoord_two_le hNc; omega⟩) hp

theorem centeredFourier_physical_norm_sq (hNc : 2 ≤ Nc) (j : Fin d)
    (R : ℕ) (hR : 2 * R < n) (c : (Fin d → Fin (2 * R + 1)) → ℂ) :
    ‖torusPhysicalEmbed hNc j
      (fun x => ∑ k, c k * centeredFourierProfile (d := d) (n := n) R k x)‖ ^ 2 =
      (n ^ d : ℝ) * ∑ k, ‖c k‖ ^ 2 := by
  rw [torusPhysicalEmbed_norm_sq, centeredFourier_counting_mass R hR c]

end YangMills.RG
