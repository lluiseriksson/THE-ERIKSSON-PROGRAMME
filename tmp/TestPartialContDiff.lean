import YangMills.RG.BalabanCMP102Eq80SourcePi4SecondFieldDerivative

open YangMills.RG

variable {H E : Type*}
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

example (F : H × E → ℝ) (hF : ContDiff ℝ ⊤ F)
    (n : ℕ) (h : H) (v : Fin n → H) :
    ContDiff ℝ ⊤ (cmp102PartialPropagatorJet F n h v) := by
  unfold cmp102PartialPropagatorJet
  have hfd : ContDiff ℝ ⊤ (iteratedFDeriv ℝ n F) :=
    hF.iteratedFDeriv_right (m := ⊤) (by simp)
  let ev :=
    ContinuousMultilinearMap.apply ℝ
      (fun _ : Fin n => H × E) ℝ (fun i => (v i, 0))
  exact ev.contDiff.comp (hfd.comp (contDiff_const.prodMk contDiff_id))

example (F : H × E → ℝ) (hF : ContDiff ℝ ⊤ F)
    (n : ℕ) (h : H) (v : Fin n → H) :
    ContDiff ℝ ⊤
      (cmp102PartialPropagatorJetFieldDerivative F n h v) := by
  have hg : ContDiff ℝ ⊤ (cmp102PartialPropagatorJet F n h v) := by
    unfold cmp102PartialPropagatorJet
    have hfd : ContDiff ℝ ⊤ (iteratedFDeriv ℝ n F) :=
      hF.iteratedFDeriv_right (m := ⊤) (by simp)
    let ev :=
      ContinuousMultilinearMap.apply ℝ
        (fun _ : Fin n => H × E) ℝ (fun i => (v i, 0))
    exact ev.contDiff.comp
      (hfd.comp (contDiff_const.prodMk contDiff_id))
  have heq :
      cmp102PartialPropagatorJetFieldDerivative F n h v =
        fderiv ℝ (cmp102PartialPropagatorJet F n h v) := by
    funext x
    exact (fderiv_cmp102PartialPropagatorJet_eq_fieldDerivative
      F hF n h v x).symm
  rw [heq]
  exact hg.fderiv_right (by simp)

example (F : H × E → ℝ) (hF : ContDiff ℝ ⊤ F)
    (n : ℕ) (h : H) (v : Fin n → H) :
    ContDiff ℝ ⊤
      (cmp102PartialPropagatorJetSecondFieldDerivative F n h v) := by
  have hg : ContDiff ℝ ⊤
      (cmp102PartialPropagatorJetFieldDerivative F n h v) := by
    have hg0 : ContDiff ℝ ⊤ (cmp102PartialPropagatorJet F n h v) := by
      unfold cmp102PartialPropagatorJet
      have hfd : ContDiff ℝ ⊤ (iteratedFDeriv ℝ n F) :=
        hF.iteratedFDeriv_right (m := ⊤) (by simp)
      let ev :=
        ContinuousMultilinearMap.apply ℝ
          (fun _ : Fin n => H × E) ℝ (fun i => (v i, 0))
      exact ev.contDiff.comp
        (hfd.comp (contDiff_const.prodMk contDiff_id))
    have heq :
        cmp102PartialPropagatorJetFieldDerivative F n h v =
          fderiv ℝ (cmp102PartialPropagatorJet F n h v) := by
      funext x
      exact (fderiv_cmp102PartialPropagatorJet_eq_fieldDerivative
        F hF n h v x).symm
    rw [heq]
    exact hg0.fderiv_right (by simp)
  have heq :
      cmp102PartialPropagatorJetSecondFieldDerivative F n h v =
        fderiv ℝ (cmp102PartialPropagatorJetFieldDerivative F n h v) := by
    funext x
    exact (cmp102PartialPropagatorJetFieldDerivative_hasFDerivAt
      F hF n h v x).fderiv.symm
  rw [heq]
  exact hg.fderiv_right (by simp)
