import YangMills.RG.TorusPhysicalEmbedding

/-! Exact wraparound shift transport and the actual flat curl/divergence of
    the constructed embedding. The full unordered-plaquette energy sum remains
    a separate obligation. -/
namespace YangMills.RG
open scoped BigOperators
variable {d n Nc : ℕ} [NeZero n]

theorem finBoxZModEquiv_apply (x : FinBox d n) (i : Fin d) :
    finBoxZModEquiv d n x i = ((x i).val : ZMod n) := by
  cases n with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ m =>
    change (x i) = ((x i).val : Fin (m + 1))
    apply Fin.ext
    simp [Fin.val_natCast, Nat.mod_eq_of_lt (x i).isLt]

theorem finBoxZModEquiv_shift (x : FinBox d n) (i : Fin d) :
    finBoxZModEquiv d n (x.shift i) =
      finBoxZModEquiv d n x + Pi.single i (1 : ZMod n) := by
  funext k
  rw [finBoxZModEquiv_apply, Pi.add_apply, finBoxZModEquiv_apply]
  by_cases h : k = i
  · subst k
    simp [FinBox.shift, Pi.single_apply, ZMod.natCast_mod]
  · simp [FinBox.shift, h, Pi.single_apply]

theorem finBoxZModEquiv_shiftBack (x : FinBox d n) (i : Fin d) :
    finBoxZModEquiv d n (x.shiftBack i) =
      finBoxZModEquiv d n x - Pi.single i (1 : ZMod n) := by
  have h := finBoxZModEquiv_shift (x.shiftBack i) i
  rw [FinBox.shift_shiftBack] at h
  exact eq_sub_iff_add_eq.mpr h.symm

theorem sunComplexPlane_sub (hNc : 2 ≤ Nc) (z w : ℂ) :
    sunComplexPlane hNc (z - w) = sunComplexPlane hNc z - sunComplexPlane hNc w := by
  ext i
  simp [sunComplexPlane, EuclideanSpace.single_apply] <;>
    split_ifs <;> simp_all <;> ring

variable [NeZero Nc]

theorem torusPhysicalEmbed_flat_div_apply (hNc : 2 ≤ Nc) (ρ : SUNAdjointModel Nc)
    (j : Fin d) (f : (Fin d → ZMod n) → ℂ) (x : FinBox d n) :
    gaugeConstraintQCLM ρ (trivialPhysicalGaugeBackground d n Nc)
      (torusPhysicalEmbed hNc j f) x =
    sunComplexPlane hNc (f (finBoxZModEquiv d n x) -
      f (finBoxZModEquiv d n x - Pi.single j (1 : ZMod n))) := by
  rw [gaugeConstraintQCLM_trivial_apply]
  have hterm (i : Fin d) :
      torusPhysicalEmbed hNc j f (x, i) -
        torusPhysicalEmbed hNc j f (x.shiftBack i, i) =
      if i = j then sunComplexPlane hNc (f (finBoxZModEquiv d n x)) -
        sunComplexPlane hNc (f (finBoxZModEquiv d n x - Pi.single j (1 : ZMod n)))
      else 0 := by
    by_cases h : i = j
    · subst i
      simp [torusPhysicalEmbed, finBoxZModEquiv_shiftBack]
    · simp [torusPhysicalEmbed, h]
  simp_rw [hterm]
  rw [Finset.sum_ite_eq' Finset.univ j]
  simp only [Finset.mem_univ, if_true, sunComplexPlane_sub]

theorem torusPhysicalEmbed_flat_curl_apply (hNc : 2 ≤ Nc) (ρ : SUNAdjointModel Nc)
    (j : Fin d) (f : (Fin d → ZMod n) → ℂ) (p : ConcretePlaquette d n) :
    covariantD1CLM ρ (trivialPhysicalGaugeBackground d n Nc)
      (torusPhysicalEmbed hNc j f) p =
    (if p.dir1 = j then sunComplexPlane hNc
      (f (finBoxZModEquiv d n p.site) -
        f (finBoxZModEquiv d n p.site + Pi.single p.dir2 (1 : ZMod n))) else 0) +
    (if p.dir2 = j then sunComplexPlane hNc
      (f (finBoxZModEquiv d n p.site + Pi.single p.dir1 (1 : ZMod n)) -
        f (finBoxZModEquiv d n p.site)) else 0) := by
  rw [covariantD1CLM_trivial_apply]
  by_cases h1 : p.dir1 = j <;> by_cases h2 : p.dir2 = j <;>
    simp [torusPhysicalEmbed, h1, h2, finBoxZModEquiv_shift, sunComplexPlane_sub] <;> abel

theorem torusPhysicalEmbed_flat_div_norm_sq (hNc : 2 ≤ Nc) (ρ : SUNAdjointModel Nc)
    (j : Fin d) (f : (Fin d → ZMod n) → ℂ) :
    ‖gaugeConstraintQCLM ρ (trivialPhysicalGaugeBackground d n Nc)
      (torusPhysicalEmbed hNc j f)‖ ^ 2 =
      backwardShiftEnergy f (Pi.single j (1 : ZMod n)) := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp_rw [torusPhysicalEmbed_flat_div_apply, sunComplexPlane_norm_sq]
  exact Equiv.sum_comp (finBoxZModEquiv d n)
    (fun x => ‖f x - f (x - Pi.single j (1 : ZMod n))‖ ^ 2)

end YangMills.RG
