import YangMills.ClayCore.BalabanRG.HaarLSIReduction
import YangMills.P8_PhysicalGap.BalabanToLSI

namespace YangMills
namespace ClayCore

noncomputable section

/-- Analytic target: the Haar measure on `SU(N_c)` satisfies a real LSI witness. -/
def HaarLSIAnalyticTarget (N_c : ℕ) [NeZero N_c] : Prop :=
  ∃ α_haar : ℝ, 0 < α_haar ∧
    LogSobolevInequality
      (YangMills.sunHaarProb N_c)
      (YangMills.sunDirichletForm N_c)
      α_haar

/-- P8 already provides the analytic Haar-LSI target once `N_c ≥ 2`. -/
theorem analytic_haar_lsi_target_from_p8
    (N_c : ℕ)
    [NeZero N_c]
    (hN_c : 2 ≤ N_c) :
    HaarLSIAnalyticTarget N_c := by
  simpa [HaarLSIAnalyticTarget] using YangMills.sun_haar_lsi N_c hN_c

/-- The analytic target projects to the weak legacy target currently consumed upstairs. -/
theorem haar_lsi_target_of_analytic_target
    (N_c : ℕ)
    [NeZero N_c]
    (h : HaarLSIAnalyticTarget N_c) :
    HaarLSITarget N_c := by
  rcases h with ⟨α_haar, hα_haar, _⟩
  exact ⟨α_haar, hα_haar⟩

end

end YangMills.ClayCore
