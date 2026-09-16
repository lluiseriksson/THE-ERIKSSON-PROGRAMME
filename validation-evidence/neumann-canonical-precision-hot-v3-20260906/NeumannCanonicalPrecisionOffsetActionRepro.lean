import Mathlib

/-! PRE-VALIDATION: source present; .olean not materialized and compiler
verification pending. Generic pointwise evaluation step only. -/

noncomputable section

example {ι V : Type*} [Fintype ι] [NormedAddCommGroup V]
    [NormedSpace ℝ V]
    (D Q R : (PiLp 2 (fun _ : ι => V)) →L[ℝ] (PiLp 2 (fun _ : ι => V)))
    (a mass : ℝ) (h : Q = R)
    (f : PiLp 2 (fun _ : ι => V)) (x : ι) :
    ((D + mass ^ 2 • ContinuousLinearMap.id ℝ (PiLp 2 (fun _ : ι => V))) +
      a • Q) f x = D f x + mass ^ 2 • f x + a • R f x := by
  change D f x + mass ^ 2 • f x + a • Q f x = _
  rw [h]

-- Exact residual coercion exposed by the failed physical transcript.
example {ι V : Type*} [Fintype ι] [NormedAddCommGroup V]
    [NormedSpace ℝ V]
    (D : (PiLp 2 (fun _ : ι => V)) →L[ℝ] (PiLp 2 (fun _ : ι => V)))
    (f : PiLp 2 (fun _ : ι => V)) (x : ι) :
    (WithLp.equiv 2 ((i : ι) → (fun _ => V) i)) (D f) x = (D f).ofLp x := by
  rfl

end
