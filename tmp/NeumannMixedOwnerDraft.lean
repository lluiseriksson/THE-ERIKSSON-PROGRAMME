import YangMills.RG.NeumannMixedBranchPackaging
import YangMills.RG.NeumannIntegerImageCountingKernel

/-!
PRE-VALIDATION: source present; .olean not materialized and compiler result
not verified. M2 owner transport at the SAME packaged mixed index.
B is the positive fine-site block side; m is in block units and B*m is
the fine side. FULL still requires the physical carrier classification.
No Green equation, operator invariance, summability or uniform B0 claim.
-/

namespace YangMills.RG

def neumannMixedOrbit (full : Bool) (m n k : ℤ) :
    neumannMixedBranch full → ℤ :=
  match full with
  | true => fun _ => n + m * k
  | false => fun b => cmp89NeumannReflectionOrbit m n k b

theorem neumannMixedOrbit_pack
    (full : Bool) (m : ℤ) (n : neumannImageIntervalPoint m)
    (k : ℤ) (b : neumannMixedBranch full) :
    neumannMixedCoordinateImage full m
      (neumannMixedInsertSource full m n
        (neumannMixedFixedCoordinatePack full (k, b))) =
      neumannMixedOrbit full m n.1 k b := by
  cases full <;> rfl

def neumannMixedImage {d : ℕ} (full : Fin d → Bool)
    (m n k : Fin d → ℤ) (b : ∀ mu : Fin d, neumannMixedBranch (full mu)) :
    Fin d → ℤ :=
  fun mu => neumannMixedOrbit (full mu) (m mu) (n mu) (k mu) (b mu)

theorem neumannMixedImage_pack {d : ℕ}
    (full : Fin d → Bool) (m : Fin d → ℤ)
    (n : ∀ mu : Fin d, neumannImageIntervalPoint (m mu))
    (p : (Fin d → ℤ) × (∀ mu : Fin d, neumannMixedBranch (full mu))) :
    neumannMixedFixedSourceImage full m n
      (neumannMixedGlobalFixedIndexEquiv full p) =
      neumannMixedImage full m (fun mu => (n mu).1) p.1 p.2 := by
  funext mu
  exact neumannMixedOrbit_pack (full mu) (m mu) (n mu) (p.1 mu) (p.2 mu)

theorem neumannMixedOrbit_owner
    (full : Bool) (B m n k : ℤ) (hB : 0 < B)
    (b : neumannMixedBranch full) :
    neumannMixedOrbit full (B * m) n k b / B =
      neumannMixedOrbit full m (n / B) k b := by
  cases full
  · change Bool at b
    cases b
    · exact neumannIntegerTranslatedOwner B m n k hB
    · exact neumannIntegerReflectedOwner B m n k hB
  · change (n + (B * m) * k) / B = n / B + m * k
    have he : n + (B * m) * k = n + B * (k * m) := by ring
    rw [he, neumannIntegerPeriodicOwner B m n k hB]
    ring

theorem neumannMixedImage_owner {d : ℕ}
    (full : Fin d → Bool) (B : ℤ) (hB : 0 < B)
    (m n k : Fin d → ℤ) (b : ∀ mu : Fin d, neumannMixedBranch (full mu)) :
    neumannIntegerBlockOwner B
      (neumannMixedImage full (fun mu => B * m mu) n k b) =
      neumannMixedImage full m (neumannIntegerBlockOwner B n) k b := by
  funext mu
  exact neumannMixedOrbit_owner (full mu) B (m mu) (n mu) (k mu) hB (b mu)

/-- Injectivity in the source for one COMMON image; not coverage. -/
theorem neumannMixedImage_source_injective {d : ℕ}
    (full : Fin d → Bool) (m k : Fin d → ℤ)
    (b : ∀ mu : Fin d, neumannMixedBranch (full mu)) :
    Function.Injective (fun n : Fin d → ℤ => neumannMixedImage full m n k b) := by
  intro x y he
  funext mu
  have hi := congrFun he mu
  change neumannMixedOrbit (full mu) (m mu) (x mu) (k mu) (b mu) =
    neumannMixedOrbit (full mu) (m mu) (y mu) (k mu) (b mu) at hi
  have coord : ∀ (f : Bool) (bb : neumannMixedBranch f) (xx yy : ℤ),
      neumannMixedOrbit f (m mu) xx (k mu) bb =
        neumannMixedOrbit f (m mu) yy (k mu) bb → xx = yy := by
    intro f bb xx yy hh
    cases f
    · change Bool at bb
      cases bb
      · change 2 * k mu * m mu + xx = 2 * k mu * m mu + yy at hh
        omega
      · change 2 * k mu * m mu - xx - 1 = 2 * k mu * m mu - yy - 1 at hh
        omega
    · change xx + m mu * k mu = yy + m mu * k mu at hh
      omega
  exact coord (full mu) (b mu) (x mu) (y mu) hi

theorem neumannMixedImage_owner_eq_iff {d : ℕ}
    (full : Fin d → Bool) (B : ℤ) (hB : 0 < B)
    (m x y k : Fin d → ℤ) (b : ∀ mu : Fin d, neumannMixedBranch (full mu)) :
    neumannIntegerBlockOwner B
        (neumannMixedImage full (fun mu => B * m mu) x k b) =
      neumannIntegerBlockOwner B
        (neumannMixedImage full (fun mu => B * m mu) y k b) ↔
      neumannIntegerBlockOwner B x = neumannIntegerBlockOwner B y := by
  rw [neumannMixedImage_owner full B hB, neumannMixedImage_owner full B hB]
  exact (neumannMixedImage_source_injective full m k b).eq_iff

/-- The coefficient c is preserved literally; no fibre count is inserted. -/
theorem neumannMixedCountingIndicator_image {d : ℕ}
    {V : Type*} [Zero V] [SMul ℝ V]
    (full : Fin d → Bool) (B : ℤ) (hB : 0 < B)
    (m source target k : Fin d → ℤ)
    (b : ∀ mu : Fin d, neumannMixedBranch (full mu)) (c : ℝ) (v : V) :
    (if neumannIntegerBlockOwner B
          (neumannMixedImage full (fun mu => B * m mu) target k b) =
        neumannIntegerBlockOwner B
          (neumannMixedImage full (fun mu => B * m mu) source k b)
      then c • v else 0) =
      (if neumannIntegerBlockOwner B target = neumannIntegerBlockOwner B source
        then c • v else 0) := by
  exact if_congr (neumannMixedImage_owner_eq_iff full B hB m target source k b) rfl rfl

end YangMills.RG

#print axioms YangMills.RG.neumannMixedOrbit_pack
#print axioms YangMills.RG.neumannMixedImage_pack
#print axioms YangMills.RG.neumannMixedOrbit_owner
#print axioms YangMills.RG.neumannMixedImage_owner
#print axioms YangMills.RG.neumannMixedImage_source_injective
#print axioms YangMills.RG.neumannMixedImage_owner_eq_iff
#print axioms YangMills.RG.neumannMixedCountingIndicator_image

