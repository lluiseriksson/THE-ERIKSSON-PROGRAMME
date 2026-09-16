import YangMills.RG.NeumannMixedOwnerTransport
import YangMills.RG.NeumannPhysicalPeriodicSeries
import YangMills.RG.NeumannBoundaryImageSeriesReindex

/-!
Compiler-verified in a fresh Colab checkout at source
`fa898ff5d8bf724fa4b6e629da7260383ef54ecc`; ledger1224 records
the independently verified cold archive and seven exact audits.
M4 index algebra on the SAME mixed family. FULL directions
retain one branch. PROPER reflection requires the explicit false flag.
These totalized tsum identities do not prove convergence or physical
endpoint covariance. Physical flags and block alignment remain downstream.
-/

namespace YangMills.RG
noncomputable section

def neumannMixedBranchFlip (full : Bool) :
    neumannMixedBranch full → neumannMixedBranch full :=
  match full with
  | false => Bool.not
  | true => id

theorem neumannMixedBranchFlip_involutive (full : Bool) :
    Function.Involutive (neumannMixedBranchFlip full) := by
  cases full
  · intro b
    change Bool at b
    cases b <;> rfl
  · intro b
    rfl

def neumannMixedProperBranchEquiv {d : ℕ} (full : Fin d → Bool) (mu : Fin d) :
    (∀ i, neumannMixedBranch (full i)) ≃ (∀ i, neumannMixedBranch (full i)) where
  toFun b i := if i = mu then neumannMixedBranchFlip (full i) (b i) else b i
  invFun b i := if i = mu then neumannMixedBranchFlip (full i) (b i) else b i
  left_inv := by
    intro b
    funext i
    by_cases hi : i = mu
    · simp only [hi, if_true, neumannMixedBranchFlip_involutive (full i) (b i)]
    · simp only [hi, if_false]
  right_inv := by
    intro b
    funext i
    by_cases hi : i = mu
    · simp only [hi, if_true, neumannMixedBranchFlip_involutive (full i) (b i)]
    · simp only [hi, if_false]

def neumannMixedPeriodicIndexEquiv {d : ℕ} (full : Fin d → Bool) (mu : Fin d) :
    ((Fin d → ℤ) × (∀ i, neumannMixedBranch (full i))) ≃
      ((Fin d → ℤ) × (∀ i, neumannMixedBranch (full i))) :=
  (neumannPeriodicTranslateIndexEquiv (fun i => if i = mu then 1 else 0)).prodCongr
    (Equiv.refl _)

def neumannMixedProperIndexEquiv {d : ℕ} (full : Fin d → Bool)
    (mu : Fin d) (c : ℤ) :
    ((Fin d → ℤ) × (∀ i, neumannMixedBranch (full i))) ≃
      ((Fin d → ℤ) × (∀ i, neumannMixedBranch (full i))) :=
  (neumannBoundaryIntegerIndexEquiv mu c).prodCongr
    (neumannMixedProperBranchEquiv full mu)

theorem neumannMixedOrbit_full_shift (full : Bool) (hfull : full = true)
    (m n k : ℤ) (b : neumannMixedBranch full) :
    neumannMixedOrbit full m n (k - 1) b = neumannMixedOrbit full m n k b - m := by
  subst full
  change n + m * (k - 1) = (n + m * k) - m
  ring

theorem neumannMixedOrbit_proper_reflect (full : Bool) (hproper : full = false)
    (m n k c : ℤ) (b : neumannMixedBranch full) :
    neumannMixedOrbit full m n (c - k) (neumannMixedBranchFlip full b) =
      2 * c * m - 1 - neumannMixedOrbit full m n k b := by
  subst full
  change Bool at b
  cases b <;> simp [neumannMixedBranchFlip, neumannMixedOrbit,
    cmp89NeumannReflectionOrbit] <;> ring

theorem neumannMixedImage_periodicIndex {d : ℕ}
    (full : Fin d → Bool) (mu : Fin d) (hfull : full mu = true)
    (m n : Fin d → ℤ)
    (p : (Fin d → ℤ) × (∀ i, neumannMixedBranch (full i))) :
    neumannMixedImage full m n (neumannMixedPeriodicIndexEquiv full mu p).1
      (neumannMixedPeriodicIndexEquiv full mu p).2 =
        (fun i => if i = mu then neumannMixedImage full m n p.1 p.2 i - m mu
          else neumannMixedImage full m n p.1 p.2 i) := by
  funext i
  change neumannMixedOrbit (full i) (m i) (n i)
    (p.1 i - (if i = mu then 1 else 0)) (p.2 i) =
      if i = mu then neumannMixedOrbit (full i) (m i) (n i) (p.1 i) (p.2 i) - m mu
      else neumannMixedOrbit (full i) (m i) (n i) (p.1 i) (p.2 i)
  by_cases hi : i = mu
  · subst i
    simp only [if_true]
    exact neumannMixedOrbit_full_shift (full mu) hfull (m mu) (n mu) (p.1 mu) (p.2 mu)
  · simp only [hi, if_false, sub_zero]

theorem neumannMixedImage_properIndex {d : ℕ}
    (full : Fin d → Bool) (mu : Fin d) (hproper : full mu = false)
    (c : ℤ) (m n : Fin d → ℤ)
    (p : (Fin d → ℤ) × (∀ i, neumannMixedBranch (full i))) :
    neumannMixedImage full m n (neumannMixedProperIndexEquiv full mu c p).1
      (neumannMixedProperIndexEquiv full mu c p).2 =
        (fun i => if i = mu then 2*c*m mu-1-neumannMixedImage full m n p.1 p.2 i
          else neumannMixedImage full m n p.1 p.2 i) := by
  funext i
  change neumannMixedOrbit (full i) (m i) (n i)
    (if i = mu then c - p.1 i else p.1 i)
    (if i = mu then neumannMixedBranchFlip (full i) (p.2 i) else p.2 i) =
      if i = mu then 2*c*m mu-1-neumannMixedOrbit (full i) (m i) (n i) (p.1 i) (p.2 i)
      else neumannMixedOrbit (full i) (m i) (n i) (p.1 i) (p.2 i)
  by_cases hi : i = mu
  · subst i
    simp only [if_true]
    exact neumannMixedOrbit_proper_reflect (full mu) hproper (m mu) (n mu) (p.1 mu) c (p.2 mu)
  · simp only [hi, if_false]

theorem neumannMixedImage_periodic_tsum {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    (full : Fin d → Bool) (mu : Fin d) (hfull : full mu = true)
    (m n : Fin d → ℤ) (F : (Fin d → ℤ) → E) :
    (∑' p : (Fin d → ℤ) × (∀ i, neumannMixedBranch (full i)),
      F (fun i => if i = mu then neumannMixedImage full m n p.1 p.2 i - m mu
        else neumannMixedImage full m n p.1 p.2 i)) =
    ∑' p : (Fin d → ℤ) × (∀ i, neumannMixedBranch (full i)),
      F (neumannMixedImage full m n p.1 p.2) := by
  calc
    _ = ∑' p, F (neumannMixedImage full m n
        (neumannMixedPeriodicIndexEquiv full mu p).1
        (neumannMixedPeriodicIndexEquiv full mu p).2) := by
      apply tsum_congr
      intro p
      exact congrArg F (neumannMixedImage_periodicIndex full mu hfull m n p).symm
    _ = _ := (neumannMixedPeriodicIndexEquiv full mu).tsum_eq
      (fun p => F (neumannMixedImage full m n p.1 p.2))

theorem neumannMixedImage_proper_tsum {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    (full : Fin d → Bool) (mu : Fin d) (hproper : full mu = false)
    (c : ℤ) (m n : Fin d → ℤ) (F : (Fin d → ℤ) → E) :
    (∑' p : (Fin d → ℤ) × (∀ i, neumannMixedBranch (full i)),
      F (fun i => if i = mu then 2*c*m mu-1-neumannMixedImage full m n p.1 p.2 i
        else neumannMixedImage full m n p.1 p.2 i)) =
    ∑' p : (Fin d → ℤ) × (∀ i, neumannMixedBranch (full i)),
      F (neumannMixedImage full m n p.1 p.2) := by
  calc
    _ = ∑' p, F (neumannMixedImage full m n
        (neumannMixedProperIndexEquiv full mu c p).1
        (neumannMixedProperIndexEquiv full mu c p).2) := by
      apply tsum_congr
      intro p
      exact congrArg F (neumannMixedImage_properIndex full mu hproper c m n p).symm
    _ = _ := (neumannMixedProperIndexEquiv full mu c).tsum_eq
      (fun p => F (neumannMixedImage full m n p.1 p.2))

end
end YangMills.RG
