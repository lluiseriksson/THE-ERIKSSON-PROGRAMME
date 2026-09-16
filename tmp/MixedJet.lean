import Mathlib.Analysis.Analytic.IteratedFDeriv

noncomputable section

variable {H E : Type*}
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

def jointHJet (F : H × E → ℝ) (n : ℕ) (h : H)
    (v : Fin n → H) (x : E) : ℝ :=
  iteratedFDeriv ℝ n F (h, x) (fun i => (v i, 0))

theorem iteratedFDeriv_slice_eq_jointHJet
    (F : H × E → ℝ) (hF : ContDiff ℝ ⊤ F)
    (n : ℕ) (h : H) (v : Fin n → H) (x : E) :
    iteratedFDeriv ℝ n (fun y : H => F (y, x)) h v =
      jointHJet F n h v x := by
  let eH : H →L[ℝ] H × E := ContinuousLinearMap.inl ℝ H E
  let Fshift : H × E → ℝ := fun p => F (p + (0, x))
  have hshift : ContDiff ℝ ⊤ Fshift := by
    exact hF.comp (contDiff_id.add contDiff_const)
  have hcomp :=
    eH.iteratedFDeriv_comp_right hshift h (i := n) (by simp)
  have htrans :=
    iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := F)
      n (0, x) (eH h)
  have heval := congrArg (fun T => T v) hcomp
  have htransEval :=
    congrArg (fun T => T (fun i => eH (v i))) htrans
  unfold jointHJet
  simpa [Fshift, eH, Function.comp_def] using heval.trans htransEval

example (F : H × E → ℝ) (hF : ContDiff ℝ ⊤ F)
    (n : ℕ) (h : H) (v : Fin n → H) :
    Differentiable ℝ (jointHJet F n h v) := by
  unfold jointHJet
  have hjet : Differentiable ℝ (iteratedFDeriv ℝ n F) :=
    hF.differentiable_iteratedFDeriv (by simp)
  have hpath : Differentiable ℝ (fun x : E => (h, x)) := by
    fun_prop
  exact
    (ContinuousMultilinearMap.apply ℝ
      (fun _ : Fin n => H × E) ℝ
      (fun i => (v i, 0))).differentiable.comp
        (hjet.comp hpath)

example (F : H × E → ℝ) (hF : ContDiff ℝ ⊤ F)
    (n : ℕ) (h : H) (v : Fin n → H) :
    fderiv ℝ (jointHJet F n h v) 0 =
      (ContinuousMultilinearMap.apply ℝ
        (fun _ : Fin n => H × E) ℝ
        (fun i => (v i, 0))).comp
        ((fderiv ℝ (iteratedFDeriv ℝ n F) (h, 0)).comp
          ((0 : E →L[ℝ] H).prod (1 : E →L[ℝ] E))) := by
  unfold jointHJet
  have hjet : Differentiable ℝ (iteratedFDeriv ℝ n F) :=
    hF.differentiable_iteratedFDeriv (by simp)
  have hpath : HasFDerivAt (fun x : E => (h, x))
      ((0 : E →L[ℝ] H).prod (1 : E →L[ℝ] E)) 0 :=
    (hasFDerivAt_const (x := (0 : E)) h).prodMk
      (hasFDerivAt_id (𝕜 := ℝ) (x := (0 : E)))
  have hcomp :=
    hjet.differentiableAt.hasFDerivAt.comp (0 : E) hpath
  have heval :=
    (ContinuousMultilinearMap.apply ℝ
      (fun _ : Fin n => H × E) ℝ
      (fun i => (v i, 0))).hasFDerivAt.comp (0 : E) hcomp
  simpa using heval.fderiv

theorem fderiv_jointHJet_eq_zero
    (F : H × E → ℝ) (hF : ContDiff ℝ ⊤ F)
    (hpartial : ∀ h : H, ∀ a : E,
      fderiv ℝ F (h, 0) (0, a) = 0)
    (n : ℕ) (h : H) (v : Fin n → H) :
    fderiv ℝ (jointHJet F n h v) 0 = 0 := by
  rw [show fderiv ℝ (jointHJet F n h v) 0 =
      (ContinuousMultilinearMap.apply ℝ
        (fun _ : Fin n => H × E) ℝ
        (fun i => (v i, 0))).comp
        ((fderiv ℝ (iteratedFDeriv ℝ n F) (h, 0)).comp
          ((0 : E →L[ℝ] H).prod (1 : E →L[ℝ] E))) by
    unfold jointHJet
    have hjet : Differentiable ℝ (iteratedFDeriv ℝ n F) :=
      hF.differentiable_iteratedFDeriv (by simp)
    have hpath : HasFDerivAt (fun x : E => (h, x))
        ((0 : E →L[ℝ] H).prod (1 : E →L[ℝ] E)) 0 :=
      (hasFDerivAt_const (x := (0 : E)) h).prodMk
        (hasFDerivAt_id (𝕜 := ℝ) (x := (0 : E)))
    have hcomp :=
      hjet.differentiableAt.hasFDerivAt.comp (0 : E) hpath
    have heval :=
      (ContinuousMultilinearMap.apply ℝ
        (fun _ : Fin n => H × E) ℝ
        (fun i => (v i, 0))).hasFDerivAt.comp (0 : E) hcomp
    simpa using heval.fderiv]
  ext a
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.zero_apply, ContinuousLinearMap.one_apply,
    ContinuousMultilinearMap.apply_apply, fderiv_iteratedFDeriv,
    Function.comp_apply, continuousMultilinearCurryLeftEquiv_apply,
    ContinuousMultilinearMap.curryLeft_apply]
  change
    iteratedFDeriv ℝ (n + 1) F (h, 0)
      (Fin.cons (0, a) (fun i => (v i, 0))) = 0
  have hperm :=
    hF.contDiffAt.iteratedFDeriv_comp_perm
      (x := (h, (0 : E)))
      (Fin.cons (0, a) (fun i => (v i, 0)))
      (finRotate (n + 1))
  have hrotate :
      (Fin.cons (0, a) (fun i => (v i, 0))) ∘
          (finRotate (n + 1)) =
        Fin.snoc (fun i => (v i, 0)) (0, a) := by
    funext i
    simpa [Function.comp_def] using
      congrFun
        (Fin.snoc_eq_cons_rotate (fun i => (v i, 0)) (0, a)).symm i
  rw [hrotate] at hperm
  rw [← hperm]
  rw [iteratedFDeriv_succ_apply_right]
  simp only [Fin.init_snoc, Fin.snoc_last]
  let eH : H →L[ℝ] H × E := ContinuousLinearMap.inl ℝ H E
  have hc : ContDiff ℝ ⊤ (fderiv ℝ F) :=
    hF.fderiv_right (by simp)
  have hrestrict :=
    eH.iteratedFDeriv_comp_right hc h (i := n) (by simp)
  have happly :=
    iteratedFDeriv_clm_apply_const_apply
      (c := fun y : H => fderiv ℝ F (eH y))
      (hc := hc.comp eH.contDiff) (i := n) (by simp)
      (x := h) (u := (0, a)) (m := v)
  have hreval :=
    congrArg (fun T => T v (0, a)) hrestrict
  have hreval' :
      ((iteratedFDeriv ℝ n
          (fun y : H => fderiv ℝ F (eH y)) h) v) (0, a) =
        ((iteratedFDeriv ℝ n (fderiv ℝ F) (h, 0))
          (fun i => (v i, 0))) (0, a) := by
    simpa [eH, Function.comp_def] using hreval
  rw [← hreval']
  rw [← happly]
  have hzero :
      (fun y : H => fderiv ℝ F (eH y) (0, a)) =
        (fun _ : H => 0) := by
    funext y
    exact hpartial y a
  rw [hzero]
  simp
