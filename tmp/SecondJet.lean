import YangMills.RG.BalabanCMP102Eq80SourcePi4ConnectedDomainFieldDerivative

open scoped RealInnerProductSpace

noncomputable section

variable {H E : Type*}
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

#check ContinuousLinearMap.precompR
#check ContinuousLinearMap.precompL
#check ContDiff.iteratedFDeriv_right
#check LinearIsometryEquiv.toContinuousLinearEquiv
#check LinearIsometryEquiv.toLinearIsometry
#check LinearIsometry.toContinuousLinearMap

noncomputable def extractFirst
    (n : ℕ) (v : Fin n → H) :
    ((H × E) [×(n + 1)]→L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) :=
  let incl : E →L[ℝ] H × E :=
    (0 : E →L[ℝ] H).prod (1 : E →L[ℝ] E)
  ((ContinuousLinearMap.compL ℝ E (H × E) ℝ).flip incl).comp
    ((ContinuousMultilinearMap.apply ℝ
      (fun _ : Fin n => H × E) ((H × E) →L[ℝ] ℝ)
      (fun i => (v i, 0))).comp
      (LinearIsometry.toContinuousLinearMap
        (LinearIsometryEquiv.toLinearIsometry
          (continuousMultilinearCurryRightEquiv' ℝ n (H × E) ℝ))))

theorem extractFirst_apply
    (n : ℕ) (v : Fin n → H)
    (L : (H × E) [×(n + 1)]→L[ℝ] ℝ) :
    extractFirst n v L =
      (((continuousMultilinearCurryRightEquiv' ℝ n (H × E) ℝ) L)
        (fun i => (v i, 0))).comp
        ((0 : E →L[ℝ] H).prod (1 : E →L[ℝ] E)) := by
  rfl

noncomputable def testSecond
    (F : H × E → ℝ) (n : ℕ) (h : H)
    (v : Fin n → H) (x : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  let incl : E →L[ℝ] H × E :=
    (0 : E →L[ℝ] H).prod (1 : E →L[ℝ] E)
  let raw : (H × E) →L[ℝ] (H × E) →L[ℝ] ℝ :=
    ((continuousMultilinearCurryRightEquiv' ℝ n (H × E)
        ((H × E) →L[ℝ] ℝ))
      ((continuousMultilinearCurryRightEquiv' ℝ (n + 1)
          (H × E) ℝ)
      (iteratedFDeriv ℝ (n + 2) F (h, x))))
      (fun i => (v i, 0))
  let post : ((H × E) →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) :=
    (ContinuousLinearMap.compL ℝ E (H × E) ℝ).flip incl
  post.comp (raw.flip.comp incl)

#check testSecond

theorem testSecond_apply
    (F : H × E → ℝ) (n : ℕ) (h : H)
    (v : Fin n → H) (x a b : E) :
    testSecond F n h v x a b =
      iteratedFDeriv ℝ (n + 2) F (h, x)
        (Fin.snoc (Fin.snoc (fun i => (v i, 0)) (0, b)) (0, a)) := by
  simp [testSecond]

theorem test_first_eq_extract
    (F : H × E → ℝ) (n : ℕ) (h : H)
    (v : Fin n → H) (x : E) :
    YangMills.RG.cmp102PartialPropagatorJetFieldDerivative F n h v x =
      extractFirst n v (iteratedFDeriv ℝ (n + 1) F (h, x)) := by
  rfl

theorem hasFDerivAt_test_first
    (F : H × E → ℝ) (hF : ContDiff ℝ ⊤ F)
    (n : ℕ) (h : H) (v : Fin n → H) (x : E) :
    HasFDerivAt
      (YangMills.RG.cmp102PartialPropagatorJetFieldDerivative F n h v)
      (testSecond F n h v x) x := by
  let incl : E →L[ℝ] H × E :=
    (0 : E →L[ℝ] H).prod (1 : E →L[ℝ] E)
  have hjet : Differentiable ℝ (iteratedFDeriv ℝ (n + 1) F) :=
    hF.differentiable_iteratedFDeriv (by simp)
  have hpath : HasFDerivAt (fun y : E => (h, y)) incl x :=
    (hasFDerivAt_const (x := x) h).prodMk
      (hasFDerivAt_id (𝕜 := ℝ) (x := x))
  have hcomp :=
    hjet.differentiableAt.hasFDerivAt.comp x hpath
  have hext :=
    (extractFirst n v).hasFDerivAt.comp x hcomp
  have hfun :
      (⇑(extractFirst n v) ∘
        iteratedFDeriv ℝ (n + 1) F ∘ fun y : E => (h, y)) =
        YangMills.RG.cmp102PartialPropagatorJetFieldDerivative F n h v := by
    funext y
    exact (test_first_eq_extract F n h v y).symm
  rw [hfun] at hext
  convert hext using 1
  ext a b
  simp only [ContinuousLinearMap.comp_apply, extractFirst_apply,
    fderiv_iteratedFDeriv, Function.comp_apply,
    continuousMultilinearCurryLeftEquiv_apply]
  rw [testSecond_apply]
  have hperm :=
    hF.contDiffAt.iteratedFDeriv_comp_perm
      (x := (h, x))
      (Fin.cons (0, a)
        (Fin.snoc (fun i => (v i, 0)) (0, b)))
      (finRotate (n + 2))
  have hrotate :
      (Fin.cons (0, a)
          (Fin.snoc (fun i => (v i, 0)) (0, b))) ∘
          (finRotate (n + 2)) =
        Fin.snoc
          (Fin.snoc (fun i => (v i, 0)) (0, b)) (0, a) := by
    funext i
    simpa [Function.comp_def] using
      congrFun
        (Fin.snoc_eq_cons_rotate
          (Fin.snoc (fun i => (v i, 0)) (0, b)) (0, a)).symm i
  rw [hrotate] at hperm
  simpa [incl, continuousMultilinearCurryLeftEquiv_apply,
    continuousMultilinearCurryRightEquiv_apply'] using hperm

variable {T : Type*} [TopologicalSpace T]

set_option synthInstance.maxHeartbeats 200000 in
theorem continuous_testSecond_comp
    (F : H × E → ℝ) (hF : ContDiff ℝ ⊤ F)
    (n : ℕ) (h : T → H) (v : T → Fin n → H)
    (x : T → E)
    (hh : Continuous h) (hv : ∀ i, Continuous fun t => v t i)
    (hx : Continuous x) :
    Continuous fun t => testSecond F n (h t) (v t) (x t) := by
  let incl : E →L[ℝ] H × E :=
    (0 : E →L[ℝ] H).prod (1 : E →L[ℝ] E)
  let raw : T → (H × E) →L[ℝ] (H × E) →L[ℝ] ℝ :=
    fun t =>
      ((continuousMultilinearCurryRightEquiv' ℝ n (H × E)
          ((H × E) →L[ℝ] ℝ))
        ((continuousMultilinearCurryRightEquiv' ℝ (n + 1)
            (H × E) ℝ)
          (iteratedFDeriv ℝ (n + 2) F (h t, x t))))
        (fun i => (v t i, 0))
  let post : ((H × E) →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) :=
    (ContinuousLinearMap.compL ℝ E (H × E) ℝ).flip incl
  have hfd : Continuous (iteratedFDeriv ℝ (n + 2) F) :=
    hF.continuous_iteratedFDeriv (by simp)
  have hraw : Continuous raw := by
    dsimp [raw]
    fun_prop
  have hflip : Continuous fun t => (raw t).flip :=
    (ContinuousLinearMap.flipₗᵢ ℝ (H × E) (H × E) ℝ).continuous.comp hraw
  have hrestricted :
      Continuous fun t => (raw t).flip.comp incl :=
    hflip.clm_comp_const incl
  have hresult :
      Continuous fun t => post.comp ((raw t).flip.comp incl) :=
    hrestricted.const_clm_comp post
  simpa [testSecond, raw, incl, post] using hresult

end
