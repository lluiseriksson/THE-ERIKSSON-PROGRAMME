import YangMills.RG.NormalizedCoexactRealPacket

/-! Actual normalized packet amplitudes and spatial-mean weighted energy.
This is a concrete packet diagonal calculation, not yet an operator trace. -/
namespace YangMills.RG
open scoped BigOperators RealInnerProductSpace

section Character
variable {D n Nc : ℕ} [NeZero D] [NeZero n] [NeZero Nc]

theorem backward_character_amplitude (chi : AddChar (Fin D → ZMod n) ℂ)
    (z : ℂ) (j : Fin D) :
    torusBackwardDifference j (fun x => z * chi x) =
      fun x => (z * (1 - chi (-Pi.single j (1 : ZMod n)))) * chi x := by
  funext x
  change z * chi x - z * chi (x - Pi.single j (1 : ZMod n)) = _
  simp only [sub_eq_add_neg, AddChar.map_add_eq_mul]
  ring

noncomputable def coexactCharacterAmplitude
    (chi : AddChar (Fin D → ZMod n) ℂ) (i j : Fin D) (z : ℂ) (l : Fin D) : ℂ :=
  (if l = i then z * (1 - chi (-Pi.single j (1 : ZMod n))) else 0) -
    (if l = j then z * (1 - chi (-Pi.single i (1 : ZMod n))) else 0)

theorem coexact_character_polarized (hNc : 2 ≤ Nc) (i j : Fin D)
    (chi : AddChar (Fin D → ZMod n) ℂ) (z : ℂ) :
    coexactFlatMap hNc i j (fun x => z * chi x) =
      polarizedPhysicalCharacter hNc chi (coexactCharacterAmplitude chi i j z) := by
  classical
  have hz : sunComplexPlane hNc (0 : ℂ) = 0 := by
    apply PiLp.ext
    intro a
    simp [sunComplexPlane, EuclideanSpace.single_apply]
  rw [coexactFlatMap_apply, backward_character_amplitude, backward_character_amplitude]
  apply PiLp.ext
  intro e
  change (if e.2 = i then sunComplexPlane hNc
      ((z * (1 - chi (-Pi.single j (1 : ZMod n)))) * chi (finBoxZModEquiv D n e.1))
      else 0) -
    (if e.2 = j then sunComplexPlane hNc
      ((z * (1 - chi (-Pi.single i (1 : ZMod n)))) * chi (finBoxZModEquiv D n e.1))
      else 0) =
    sunComplexPlane hNc (((if e.2 = i then
      z * (1 - chi (-Pi.single j (1 : ZMod n))) else 0) -
      (if e.2 = j then z * (1 - chi (-Pi.single i (1 : ZMod n))) else 0)) *
        chi (finBoxZModEquiv D n e.1))
  rw [sub_mul, sunComplexPlane_sub]
  by_cases hi : e.2 = i <;> by_cases hj : e.2 = j <;>
    simp [hi, hj, hz] <;> split_ifs <;> simp_all [hz]
end Character

variable {d n Nc : ℕ} [NeZero n] [NeZero Nc]

theorem normalizedPacket_scalar_profile (R : ℕ) (k : CoexactPositiveIndex d R)
    (q : Bool) :
    characterSynthesis (positiveCoexactCharacter (n := n) R)
      (fun a => (Pi.single k (coexactQuadraturePhase q) : CoexactPositiveIndex d R → ℂ) a /
        (positiveCoexactNormalization (n := n) R a : ℂ)) =
      fun x => (coexactQuadraturePhase q / (positiveCoexactNormalization (n := n) R k : ℂ)) *
        positiveCoexactCharacter (n := n) R k x := by
  classical
  funext x
  unfold characterSynthesis
  rw [Finset.sum_eq_single k]
  · simp
  · intro b _ hb
    simp [Pi.single_apply, hb, Ne.symm hb]
  · simp

noncomputable def normalizedPacketAmplitude (R : ℕ)
    (p : CoexactPositiveIndex d R × Bool) : Fin (d + 2) → ℂ :=
  coexactCharacterAmplitude (positiveCoexactCharacter (n := n) R p.1)
    (0 : Fin (d + 2)) (Fin.succ 0)
    (coexactQuadraturePhase p.2 / (positiveCoexactNormalization (n := n) R p.1 : ℂ))

theorem normalizedRealPacket_eq_polarized (hNc : 2 ≤ Nc) (R : ℕ)
    (p : CoexactPositiveIndex d R × Bool) :
    normalizedCoexactRealPacket (n := n) hNc R p =
      polarizedPhysicalCharacter hNc (positiveCoexactCharacter (n := n) R p.1)
        (normalizedPacketAmplitude (n := n) R p) := by
  classical
  unfold normalizedCoexactRealPacket normalizedCoexactSynthesis
  rw [normalizedPacket_scalar_profile]
  exact coexact_character_polarized hNc _ _ _ _

theorem normalizedRealPacket_weighted_energy (hNc : 2 ≤ Nc) (R : ℕ)
    (p : CoexactPositiveIndex d R × Bool) (w : PhysicalGradientIndex (d + 2) n → ℝ) :
    inner ℝ (normalizedCoexactRealPacket (n := n) hNc R p)
      (componentwiseWeightedRepairCLM w (normalizedCoexactRealPacket (n := n) hNc R p)) =
      ∑ i : Fin (d + 2), ∑ l : Fin (d + 2),
        (‖normalizedPacketAmplitude (n := n) R p l‖ ^ 2 *
          ‖positiveCoexactCharacter (n := n) R p.1 (Pi.single i (1 : ZMod n)) - 1‖ ^ 2) *
            ∑ x : FinBox (d + 2) n, w (i, (x, l)) := by
  rw [normalizedRealPacket_eq_polarized]
  exact polarizedCharacter_weightedRepair_energy hNc _ _ w

theorem normalizedPacket_amplitude_mass (hNc : 2 ≤ Nc) (R : ℕ) (hR : 2 * R < n)
    (p : CoexactPositiveIndex d R × Bool) :
    (n : ℝ)^(d + 2) * ∑ l, ‖normalizedPacketAmplitude (n := n) R p l‖ ^ 2 = 1 := by
  have h := normalizedCoexactRealPacket_gram (n := n) hNc R hR p p
  rw [real_inner_self_eq_norm_sq, if_pos rfl,
    normalizedRealPacket_eq_polarized, polarizedCharacter_norm_sq] at h
  exact h

theorem normalizedRealPacket_mean_upper (hNc : 2 ≤ Nc) (R : ℕ) (hR : 2 * R < n)
    (p : CoexactPositiveIndex d R × Bool) (w : PhysicalGradientIndex (d + 2) n → ℝ)
    (M : ℝ) (hw : ∀ i l, ∑ x : FinBox (d + 2) n, w (i, (x, l)) ≤ (n : ℝ)^(d + 2) * M) :
    inner ℝ (normalizedCoexactRealPacket (n := n) hNc R p)
      (componentwiseWeightedRepairCLM w (normalizedCoexactRealPacket (n := n) hNc R p)) ≤
      M * ∑ i : Fin (d + 2),
        ‖positiveCoexactCharacter (n := n) R p.1 (Pi.single i (1 : ZMod n)) - 1‖ ^ 2 := by
  classical
  let chi := positiveCoexactCharacter (n := n) R p.1
  let a := normalizedPacketAmplitude (n := n) R p
  let v : ℝ := (n : ℝ)^(d + 2)
  let b (i : Fin (d + 2)) : ℝ := ‖chi (Pi.single i (1 : ZMod n)) - 1‖ ^ 2
  have hm : v * ∑ l, ‖a l‖ ^ 2 = 1 := normalizedPacket_amplitude_mass hNc R hR p
  have ha : (∑ i : Fin (d + 2), ∑ l : Fin (d + 2),
      (‖a l‖ ^ 2 * b i) * (v * M)) = M * ∑ i, b i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    calc
      _ = (∑ l, ‖a l‖ ^ 2) * (b i * (v * M)) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro l _
        ring
      _ = ((v * ∑ l, ‖a l‖ ^ 2) * M) * b i := by ring
      _ = M * b i := by rw [hm]; ring
  rw [normalizedRealPacket_eq_polarized]
  exact (polarizedCharacter_mean_upper hNc chi a w M hw).trans (le_of_eq ha)

theorem normalizedPacket_weightedDiagonal_upper (hNc : 2 ≤ Nc) (R : ℕ) (hR : 2 * R < n)
    (w : PhysicalGradientIndex (d + 2) n → ℝ) (M : ℝ)
    (hw : ∀ i l, ∑ x : FinBox (d + 2) n, w (i, (x, l)) ≤ (n : ℝ)^(d + 2) * M) :
    (∑ p : CoexactPositiveIndex d R × Bool,
      inner ℝ (normalizedCoexactRealPacket (n := n) hNc R p)
        (componentwiseWeightedRepairCLM w (normalizedCoexactRealPacket (n := n) hNc R p))) ≤
      ∑ p : CoexactPositiveIndex d R × Bool, M * ∑ i : Fin (d + 2),
        ‖positiveCoexactCharacter (n := n) R p.1 (Pi.single i (1 : ZMod n)) - 1‖ ^ 2 := by
  exact Finset.sum_le_sum (fun p _ => normalizedRealPacket_mean_upper hNc R hR p w M hw)
end YangMills.RG
