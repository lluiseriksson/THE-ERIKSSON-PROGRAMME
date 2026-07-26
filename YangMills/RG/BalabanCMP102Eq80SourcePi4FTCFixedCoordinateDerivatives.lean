/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80SourcePi4FTCBranchRecursion

/-!
# Fixed coordinate derivatives along an FTC branch

An FTC fiber fixes both a coordinate and its interpolation value.  Recording
only the coordinate is insufficient for a literal description of the current
functional.  The definitions below retain pairs `(d,t)` in reverse
chronological order, exactly as fibers are entered.

The terminal theorem identifies this literal nested derivative with the
corresponding arbitrary-order Fréchet derivative at a point that remembers
all recorded values.  Pairwise distinctness is essential: it is what makes a
later coordinate line preserve every earlier fixed value.
-/

namespace YangMills.RG

noncomputable section

/-- The literal functional obtained after successively entering the recorded
coordinate fibers.  The newest fiber is stored at the head. -/
noncomputable def cmp116FixedWeakeningCoordinateDerivatives
    {D : Type*} [DecidableEq D]
    (f : (D → ℝ) → ℝ) : List (D × ℝ) → (D → ℝ) → ℝ
  | [] => f
  | (d, t) :: history =>
      cmp116RealWeakeningCoordinateDerivative
        (cmp116FixedWeakeningCoordinateDerivatives f history) d t

/-- Canonical coordinate directions in the same reverse-chronological order
as a fixed derivative history. -/
def cmp116FixedWeakeningCoordinateDirections
    {D : Type*} [DecidableEq D] :
    (history : List (D × ℝ)) →
      Fin history.length → (D → ℝ)
  | [] => Fin.elim0
  | (d, _) :: history =>
      Fin.cons (Pi.single d 1)
        (cmp116FixedWeakeningCoordinateDirections history)

@[simp] theorem cmp116FixedWeakeningCoordinateDirections_cons_zero
    {D : Type*} [DecidableEq D]
    (d : D) (t : ℝ) (history : List (D × ℝ)) :
    cmp116FixedWeakeningCoordinateDirections ((d, t) :: history) 0 =
      Pi.single d 1 := by
  rfl

@[simp] theorem cmp116FixedWeakeningCoordinateDirections_cons_tail
    {D : Type*} [DecidableEq D]
    (d : D) (t : ℝ) (history : List (D × ℝ)) :
    Fin.tail
      (cmp116FixedWeakeningCoordinateDirections ((d, t) :: history)) =
        cmp116FixedWeakeningCoordinateDirections history := by
  rfl

set_option maxHeartbeats 4000000 in
/-- A literal nested coordinate derivative is the arbitrary-order Fréchet
derivative in the recorded coordinate directions. -/
theorem cmp116FixedWeakeningCoordinateDerivatives_eq_iteratedFDeriv
    {D : Type*} [Fintype D] [DecidableEq D]
    (f : (D → ℝ) → ℝ) (history : List (D × ℝ))
    (sigma : D → ℝ)
    (hnodup : (history.map Prod.fst).Nodup)
    (hvalues : ∀ p ∈ history, sigma p.1 = p.2)
    (hf : ContDiff ℝ history.length f) :
    cmp116FixedWeakeningCoordinateDerivatives f history sigma =
      iteratedFDeriv ℝ history.length f sigma
        (cmp116FixedWeakeningCoordinateDirections history) := by
  induction history generalizing sigma with
  | nil =>
      change f sigma =
        iteratedFDeriv ℝ 0 f sigma (Fin.elim0)
      rfl
  | cons p history ih =>
      rcases p with ⟨d, t⟩
      have hdnot : d ∉ history.map Prod.fst := by
        simpa using (List.nodup_cons.mp hnodup).1
      have htailNodup : (history.map Prod.fst).Nodup := by
        simpa using (List.nodup_cons.mp hnodup).2
      have hsigma : sigma d = t := hvalues (d, t) (by simp)
      have htailValues :
          ∀ p ∈ history, sigma p.1 = p.2 := by
        intro p hp
        exact hvalues p (by simp [hp])
      have hfTail : ContDiff ℝ history.length f :=
        hf.of_le (by simp)
      have hfSucc : ContDiff ℝ (history.length + 1) f := by
        simpa using hf
      have hcurve :
          (fun u =>
            cmp116FixedWeakeningCoordinateDerivatives f history
              (Function.update sigma d u)) =
            fun u =>
              iteratedFDeriv ℝ history.length f
                (Function.update sigma d u)
                (cmp116FixedWeakeningCoordinateDirections history) := by
        funext u
        apply ih (Function.update sigma d u) htailNodup
        · intro p hp
          rw [Function.update_of_ne]
          · exact htailValues p hp
          · intro h
            subst d
            exact hdnot (List.mem_map.mpr ⟨p, hp, rfl⟩)
        · exact hfTail
      have hjetCont :
          ContDiff ℝ 1 (iteratedFDeriv ℝ history.length f) := by
        apply ContDiff.iteratedFDeriv_right'
        simpa [add_comm] using hfSucc
      have hfullDiff :
          DifferentiableAt ℝ
            (iteratedFDeriv ℝ history.length f) sigma :=
        (hjetCont.differentiable one_ne_zero sigma)
      let eval :=
        ContinuousMultilinearMap.apply ℝ
          (fun _ : Fin history.length => D → ℝ) ℝ
          (cmp116FixedWeakeningCoordinateDirections history)
      have heval :
          HasFDerivAt
            (fun x =>
              iteratedFDeriv ℝ history.length f x
                (cmp116FixedWeakeningCoordinateDirections history))
            (eval.comp
              (fderiv ℝ (iteratedFDeriv ℝ history.length f) sigma))
            sigma :=
        eval.hasFDerivAt.comp sigma hfullDiff.hasFDerivAt
      have hupdate : Function.update sigma d t = sigma := by
        rw [← hsigma]
        exact Function.update_eq_self d sigma
      have heval' :
          HasFDerivAt
            (fun x =>
              iteratedFDeriv ℝ history.length f x
                (cmp116FixedWeakeningCoordinateDirections history))
            (eval.comp
              (fderiv ℝ (iteratedFDeriv ℝ history.length f) sigma))
            (Function.update sigma d t) := by
        simpa [hupdate] using heval
      have hline :=
        heval'.comp t (hasDerivAt_update sigma d t).hasFDerivAt
      have hderiv :
          deriv
              (fun u =>
                iteratedFDeriv ℝ history.length f
                  (Function.update sigma d u)
                  (cmp116FixedWeakeningCoordinateDirections history)) t =
            (eval.comp
              (fderiv ℝ (iteratedFDeriv ℝ history.length f) sigma))
                (Pi.single d 1) := by
        simpa [Function.comp_def] using hline.hasDerivAt.deriv
      rw [cmp116FixedWeakeningCoordinateDerivatives,
        cmp116RealWeakeningCoordinateDerivative, hcurve]
      rw [hderiv]
      change
        (eval.comp
            (fderiv ℝ (iteratedFDeriv ℝ history.length f) sigma))
              (Pi.single d 1) =
          iteratedFDeriv ℝ (history.length + 1) f sigma
            (Fin.cons (Pi.single d 1)
              (cmp116FixedWeakeningCoordinateDirections history))
      rw [iteratedFDeriv_succ_apply_left]
      rfl

end

end YangMills.RG
