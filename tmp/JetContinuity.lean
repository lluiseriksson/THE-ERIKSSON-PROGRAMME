import YangMills.RG.BalabanCMP102Eq80ParametricIntervalFirstOrder

open YangMills.RG

noncomputable section

variable {H E T : Type*}
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace T]

theorem fderiv_partial_at
    (F : H × E → ℝ) (hF : ContDiff ℝ ⊤ F)
    (n : ℕ) (h : H) (v : Fin n → H) (x : E) :
    fderiv ℝ (cmp102PartialPropagatorJet F n h v) x =
      (ContinuousMultilinearMap.apply ℝ
        (fun _ : Fin n => H × E) ℝ
        (fun i => (v i, 0))).comp
        ((fderiv ℝ (iteratedFDeriv ℝ n F) (h, x)).comp
          ((0 : E →L[ℝ] H).prod (1 : E →L[ℝ] E))) := by
  unfold cmp102PartialPropagatorJet
  have hjet : Differentiable ℝ (iteratedFDeriv ℝ n F) :=
    hF.differentiable_iteratedFDeriv (by simp)
  have hpath : HasFDerivAt (fun y : E => (h, y))
      ((0 : E →L[ℝ] H).prod (1 : E →L[ℝ] E)) x :=
    (hasFDerivAt_const (x := x) h).prodMk
      (hasFDerivAt_id (𝕜 := ℝ) (x := x))
  have hcomp :=
    hjet.differentiableAt.hasFDerivAt.comp x hpath
  have heval :=
    (ContinuousMultilinearMap.apply ℝ
      (fun _ : Fin n => H × E) ℝ
      (fun i => (v i, 0))).hasFDerivAt.comp x hcomp
  simpa using heval.fderiv

noncomputable def jetFieldDeriv
    (F : H × E → ℝ) (n : ℕ) (h : H)
    (v : Fin n → H) (x : E) : E →L[ℝ] ℝ :=
  ((continuousMultilinearCurryRightEquiv' ℝ n (H × E) ℝ)
      (iteratedFDeriv ℝ (n + 1) F (h, x))
      (fun i => (v i, 0))).comp
      ((0 : E →L[ℝ] H).prod (1 : E →L[ℝ] E))

theorem continuous_jetFieldDeriv_comp
    (F : H × E → ℝ) (hF : ContDiff ℝ ⊤ F)
    (n : ℕ) (h : T → H) (v : T → Fin n → H)
    (x : T → E)
    (hh : Continuous h) (hv : ∀ i, Continuous fun t => v t i)
    (hx : Continuous x) :
    Continuous fun t => jetFieldDeriv F n (h t) (v t) (x t) := by
  unfold jetFieldDeriv
  have hfd :
      Continuous (iteratedFDeriv ℝ (n + 1) F) :=
    hF.continuous_iteratedFDeriv (by simp)
  fun_prop

theorem fderiv_partial_eq_jetFieldDeriv
    (F : H × E → ℝ) (hF : ContDiff ℝ ⊤ F)
    (n : ℕ) (h : H) (v : Fin n → H) (x : E) :
    fderiv ℝ (cmp102PartialPropagatorJet F n h v) x =
      jetFieldDeriv F n h v x := by
  rw [fderiv_partial_at F hF n h v x]
  ext a
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.zero_apply, ContinuousLinearMap.one_apply,
    ContinuousMultilinearMap.apply_apply, fderiv_iteratedFDeriv,
    Function.comp_apply, continuousMultilinearCurryLeftEquiv_apply]
  unfold jetFieldDeriv
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.zero_apply, ContinuousLinearMap.one_apply,
    ContinuousMultilinearMap.curryRight_apply]
  have hperm :=
    hF.contDiffAt.iteratedFDeriv_comp_perm
      (x := (h, x))
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
  exact hperm.symm
