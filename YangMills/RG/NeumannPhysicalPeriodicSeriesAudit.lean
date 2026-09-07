import YangMills.RG.NeumannPhysicalPeriodicSeries
import YangMills.RG.NeumannPhysicalPeriodicSummability

/-!
# PRE-VALIDATION: promoted physical periodic series and convergence audit
Source present; production .olean not materialized; result not compiler-verified.
The five exact draft declarations passed HOT (ledger1208). This audit and
the promoted modules still require their own cold gate. No mixed inverse,
uniform B0, source equation, window15 or terminal field is claimed here.
-/

#print axioms YangMills.RG.neumannPeriodicTranslate_tsum_reindex
#print axioms YangMills.RG.neumannPhysicalGreen_periodicImage_tsum
#print axioms YangMills.RG.neumannPeriodicSourceDifference_injective
#print axioms YangMills.RG.summable_neumannPeriodicSource_of_decay
#print axioms YangMills.RG.summable_neumannActualFullGreen_periodicSource
