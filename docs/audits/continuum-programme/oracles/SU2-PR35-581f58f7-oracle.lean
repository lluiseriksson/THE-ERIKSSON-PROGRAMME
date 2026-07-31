import YangMills.OS.SU2WilsonReflectionEndpoint

/-!
Independent declaration oracle for PR 35 at
`581f58f71610c3c73243f66d97116022ead1aa9a`.

This oracle checks only the producer's declared abstract cut and one-plaquette
endpoint. It does not assert an assembly map from `GaugeConfig`.
-/

#check YangMills.OS.SU2CutConfig
#check YangMills.OS.reflectSU2Cut
#check YangMills.OS.su2OnePlaquetteCutWeight_splitting
#check YangMills.OS.su2OnePlaquetteReflectedPairing_eq_kernelIntegralForm
#check YangMills.OS.su2WilsonCrossing_isHaarPSDKernel
#check YangMills.OS.su2OnePlaquette_reflection_positive
#check YangMills.OS.su2TraceObservable_haar_mean_zero

#print axioms YangMills.OS.su2WilsonExponent_finiteRank
#print axioms YangMills.OS.su2WilsonTaylor_isHaarPSDKernel
#print axioms YangMills.OS.su2WilsonCrossing_isHaarPSDKernel
#print axioms YangMills.OS.reflectSU2Cut_involutive
#print axioms YangMills.OS.su2WilsonCrossingKernel_dressed
#print axioms YangMills.OS.su2OnePlaquetteCutWeight_splitting
#print axioms YangMills.OS.su2OnePlaquetteReflectedPairing_eq_kernelIntegralForm
#print axioms YangMills.OS.su2TraceObservable_haar_mean_zero
#print axioms YangMills.OS.su2OnePlaquette_reflection_positive
#print axioms YangMills.OS.su2WilsonCrossingKernel_nonconstant
#print axioms YangMills.OS.su2OnePlaquette_constant_pairing_strict
