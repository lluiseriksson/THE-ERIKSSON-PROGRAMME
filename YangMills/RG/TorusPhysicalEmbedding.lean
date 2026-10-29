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
  classical
  let a : Fin (Nc ^ 2 - 1) := ⟨0, by have := sunCoord_two_le hNc; omega⟩
  let b : Fin (Nc ^ 2 - 1) := ⟨1, by have := sunCoord_two_le hNc; omega⟩
  have hpt (i : Fin (Nc ^ 2 - 1)) :
      (sunComplexPlane hNc z i) ^ 2 =
        (if i = a then z.re ^ 2 else 0) + (if i = b then z.im ^ 2 else 0) := by
    by_cases h0 : i.val = 0 <;> by_cases h1 : i.val = 1 <;>
      simp [sunComplexPlane, EuclideanSpace.single_apply, Fin.ext_iff, a, b, h0, h1] <;>
      omega
  rw [EuclideanSpace.real_norm_sq_eq]
  simp_rw [hpt]
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [← Complex.normSq_eq_norm_sq]
  simp [Complex.normSq_apply, pow_two]
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
  · simp [torusPhysicalEmbed, h, sunComplexPlane, EuclideanSpace.single_apply] <;>
      split_ifs <;> simp_all
  · simp [torusPhysicalEmbed, h]

theorem torusPhysicalEmbed_smul (hNc : 2 ≤ Nc) (j : Fin d) (r : ℝ)
    (f : (Fin d → ZMod n) → ℂ) :
    torusPhysicalEmbed hNc j (r • f) = r • torusPhysicalEmbed hNc j f := by
  ext e i
  by_cases h : e.2 = j
  · simp [torusPhysicalEmbed, h, sunComplexPlane, EuclideanSpace.single_apply]
  · simp [torusPhysicalEmbed, h]

theorem torusPhysicalEmbed_norm_sq (hNc : 2 ≤ Nc) (j : Fin d)
    (f : (Fin d → ZMod n) → ℂ) :
    ‖torusPhysicalEmbed hNc j f‖ ^ 2 = countingL2Mass f := by
  classical
  rw [PiLp.norm_sq_eq_of_L2]
  change (∑ e : FinBox d n × Fin d,
    ‖if e.2 = j then sunComplexPlane hNc (f (finBoxZModEquiv d n e.1)) else 0‖ ^ 2) = _
  rw [Fintype.sum_prod_type]
  have hn (x : FinBox d n) (i : Fin d) :
      ‖if i = j then sunComplexPlane hNc (f (finBoxZModEquiv d n x)) else 0‖ ^ 2 =
        if i = j then ‖f (finBoxZModEquiv d n x)‖ ^ 2 else 0 := by
    by_cases h : i = j <;> simp [h, sunComplexPlane_norm_sq]
  simp_rw [hn]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
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
