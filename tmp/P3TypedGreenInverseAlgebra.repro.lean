import Mathlib

noncomputable section

variable {H K : Type*}
variable [NormedAddCommGroup H] [NormedSpace ℝ H]
variable [NormedAddCommGroup K] [NormedSpace ℝ K]

/-- Mathlib-only reproduction of the right-bracket normalization used by the
typed CMP85 Green inverse calculation. -/
example
    (P S C : K →L[ℝ] K) (Qdag : K →L[ℝ] H)
    (b beta : ℝ) (y : K)
    (h :
      beta • Qdag (P y) - b • Qdag y + b ^ 2 • Qdag (C y) +
          b ^ 2 • (beta • Qdag (P (S (C y))) - b • Qdag (S (C y))) =
        Qdag 0) :
    let E := beta • P - b • ContinuousLinearMap.id ℝ K
    Qdag (E y) + b ^ 2 • Qdag (C y) + b ^ 2 • Qdag (E (S (C y))) = 0 := by
  let E := beta • P - b • ContinuousLinearMap.id ℝ K
  simpa only [E, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
    map_sub, map_smul, map_zero, smul_smul] using h

/-- The right-inverse endpoint is additive normalization, not a definitional
unfolding of the local aliases. -/
example (x a b c : H) (h : a + b + c = 0) : x + b + a + c = x := by
  simpa only [add_zero, add_assoc, add_comm, add_left_comm] using
    congrArg (fun z : H => x + z) h

/-- The left-inverse endpoint has the bracket order already used by the
certificate and needs only reassociation. -/
example (x a b c : H) (h : a + b + c = 0) : x + a + b + c = x := by
  simpa only [add_zero, add_assoc] using congrArg (fun z : H => x + z) h

/-- Exact right-inverse endpoint: unfold the Green sandwich and distribute the
common scalar before additive normalization. -/
example
    (Q : H →L[ℝ] K) (Qdag : K →L[ℝ] H) (G : H →L[ℝ] H)
    (E C : K →L[ℝ] K) (b : ℝ) (x : H) (y : K)
    (h : Qdag (E y) + b ^ 2 • Qdag (C y) +
        b ^ 2 • Qdag (E ((Q.comp (G.comp Qdag)) (C y))) = 0) :
    x + (Qdag (E y) + b ^ 2 •
        (Qdag (C y) + Qdag (E (Q (G (Qdag (C y))))))) = x := by
  simpa only [ContinuousLinearMap.comp_apply, smul_add, add_zero, add_assoc,
    add_comm, add_left_comm] using congrArg (fun z : H => x + z) h

/-- Exact left-inverse endpoint, including the source order exposed by the
candidate expansion. -/
example
    (Q : H →L[ℝ] K) (Qdag : K →L[ℝ] H) (G : H →L[ℝ] H)
    (E C : K →L[ℝ] K) (b : ℝ) (x : H) (y : K)
    (h : G (Qdag (E y)) + b ^ 2 • G (Qdag (C y)) +
        b ^ 2 • G (Qdag (C ((Q.comp (G.comp Qdag)) (E y)))) = 0) :
    x + b ^ 2 • G (Qdag (C y)) +
        (G (Qdag (E y)) +
          b ^ 2 • G (Qdag (C (Q (G (Qdag (E y))))))) = x := by
  simpa only [ContinuousLinearMap.comp_apply, smul_add, add_zero, add_assoc,
    add_comm, add_left_comm] using congrArg (fun z : H => x + z) h

end
