import YangMills.ClayCore.BalabanRG.HaarLSIReduction
import YangMills.ClayCore.BalabanRG.HaarLSIAnalyticTarget
import YangMills.ClayCore.BalabanRG.LSIRateLowerBound
import YangMills.ClayCore.BalabanRG.UniformLSITransfer
import YangMills.ClayCore.BalabanRG.KPWeightedToLSIBridge

namespace YangMills
namespace ClayCore

/-
HaarLSIBridge — puente honesto entre el frente LSI interno y la LSI de Haar.

Esta versión deja explícita la factorización correcta del cuello de botella:

1. P8 ya aterriza un target analítico real:
     HaarLSIAnalyticTarget n

2. Ese target analítico proyecta al target débil legacy:
     HaarLSIAnalyticTarget n -> HaarLSITarget n

3. La vía RG ya produce exactamente:
     SpecialUnitaryUniformLSIPackageTarget n
   mediante un witness real de `ClayCoreLSI`.

Por tanto, el único gap vivo que queda aislado aquí es:

     HaarLSIFromUniformLSITransfer n :
       SpecialUnitaryUniformLSIPackageTarget n -> HaarLSITarget n

y, de forma más fuerte y ya alineada con P8:

     HaarLSIFromUniformLSIAnalyticTransfer n :
       SpecialUnitaryUniformLSIPackageTarget n -> HaarLSIAnalyticTarget n
-/

noncomputable section

/-- Interfaz abstracta honesta para un paquete uniforme-LSI extraído del frente RG. -/
def SpecialUnitaryUniformLSIPackageTarget (n : ℕ) [NeZero n] : Prop :=
  ∃ d : ℕ, ∃ c : ℝ, 0 < c ∧ ClayCoreLSI d n c

/-- Gap honesto legacy del puente uniforme→Haar. -/
def HaarLSIFromUniformLSITransfer (n : ℕ) [NeZero n] : Prop :=
  SpecialUnitaryUniformLSIPackageTarget n → HaarLSITarget n

/-- Versión fuerte y ya alineada con el target analítico real de P8. -/
def HaarLSIFromUniformLSIAnalyticTransfer (n : ℕ) [NeZero n] : Prop :=
  SpecialUnitaryUniformLSIPackageTarget n → HaarLSIAnalyticTarget n

/-- Un witness explícito de `ClayCoreLSI` ya produce el target abstracto del puente. -/
theorem abstract_uniform_target_of_clay_core_lsi
    {d n : ℕ} [NeZero n] {c : ℝ}
    (hc : 0 < c) (hlsi : ClayCoreLSI d n c) :
    SpecialUnitaryUniformLSIPackageTarget n := by
  exact ⟨d, c, hc, hlsi⟩

/-- Un paquete RG real ya produce el target abstracto honesto del puente uniforme→Haar. -/
theorem abstract_uniform_target_of_pkg
    {d n : ℕ} [NeZero n]
    (pkg : BalabanRGPackage d n) :
    SpecialUnitaryUniformLSIPackageTarget n := by
  obtain ⟨c, hc, hlsi⟩ := uniform_lsi_of_balaban_rg_package pkg
  exact ⟨d, c, hc, hlsi⟩

/-- Eliminación directa del target fuerte hacia el target analítico real. -/
theorem analytic_haar_lsi_target_of_uniform_lsi
    (n : ℕ) [NeZero n]
    (tr : HaarLSIFromUniformLSIAnalyticTransfer n)
    (hlsi : SpecialUnitaryUniformLSIPackageTarget n) :
    HaarLSIAnalyticTarget n := by
  exact tr hlsi

/-- El transfer fuerte induce automáticamente el transfer débil legacy. -/
theorem weak_uniform_transfer_of_analytic_transfer
    (n : ℕ) [NeZero n]
    (tr : HaarLSIFromUniformLSIAnalyticTransfer n) :
    HaarLSIFromUniformLSITransfer n := by
  intro hlsi
  exact haar_lsi_target_of_analytic_target n (tr hlsi)

/-- Eliminación directa del puente uniforme→Haar una vez se suministre honestamente. -/
theorem haar_lsi_target_of_uniform_lsi
    (n : ℕ) [NeZero n]
    (tr : HaarLSIFromUniformLSITransfer n)
    (hlsi : SpecialUnitaryUniformLSIPackageTarget n) :
    HaarLSITarget n := by
  exact tr hlsi

/-- Eliminación del transfer fuerte, compuesta con la proyección al target legacy. -/
theorem haar_lsi_target_of_uniform_lsi_via_analytic
    (n : ℕ) [NeZero n]
    (tr : HaarLSIFromUniformLSIAnalyticTransfer n)
    (hlsi : SpecialUnitaryUniformLSIPackageTarget n) :
    HaarLSITarget n := by
  exact haar_lsi_target_of_analytic_target n
    (analytic_haar_lsi_target_of_uniform_lsi n tr hlsi)

/-- Registro conjunto del frente LSI: la vía geométrica y la vía analítica interna
quedan separadas como puentes honestos. -/
theorem haar_lsi_front_two_route_registry
    (n : ℕ) [NeZero n]
    (hRicci : HaarLSIFromRicciTransfer n)
    (hUniform : HaarLSIFromUniformLSITransfer n) :
    HaarLSIFromRicciTransfer n ∧ HaarLSIFromUniformLSITransfer n := by
  exact ⟨hRicci, hUniform⟩

/-- Registro ampliado: además del target débil, se hace visible el transfer analítico fuerte. -/
theorem haar_lsi_front_three_route_registry
    (n : ℕ) [NeZero n]
    (hRicci : HaarLSIFromRicciTransfer n)
    (hUniform : HaarLSIFromUniformLSITransfer n)
    (hAnalytic : HaarLSIFromUniformLSIAnalyticTransfer n) :
    HaarLSIFromRicciTransfer n ∧
      HaarLSIFromUniformLSITransfer n ∧
      HaarLSIFromUniformLSIAnalyticTransfer n := by
  exact ⟨hRicci, ⟨hUniform, hAnalytic⟩⟩

end

end YangMills.ClayCore
