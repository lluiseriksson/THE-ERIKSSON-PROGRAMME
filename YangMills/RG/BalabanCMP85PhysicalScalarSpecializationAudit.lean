import YangMills.RG.BalabanCMP85PhysicalScalarSpecialization



/-!
axiom audit for the physical P3 scalar specialization.

PRE-VALIDATION: this module's source is present, its `.olean` has not yet
been materialized, and its result has not yet been verified by the compiler.
-/

open YangMills.RG

#print axioms YangMills.RG.CMP85PositiveCoarseStep.nextPrefix
#print axioms YangMills.RG.cmp85RecurrenceB_eq_sourceCurrentWeighted
#print axioms YangMills.RG.cmp85RecurrenceC_eq_sourceStepWeighted
#print axioms YangMills.RG.cmp85RecurrenceBeta_eq_sourceNextWeighted
