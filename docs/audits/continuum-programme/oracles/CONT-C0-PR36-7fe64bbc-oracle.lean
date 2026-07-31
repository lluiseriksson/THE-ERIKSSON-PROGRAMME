import YangMills.Continuum.RegimeObstruction
import YangMills.Continuum.CorrelationGeometry
import YangMills.Continuum.TwoPointFactorization

/-!
Independent declaration oracle for PR 36 at
`7fe64bbced729337f6a1060d731e661384863c42`.

The checks deliberately distinguish proved transport from the still-open law,
tightness, physical-scale, renormalisation, and fluctuation obligations.
-/

#check YangMills.Continuum.GibbsStateSequence.state
#check YangMills.Continuum.HasWeakLimit
#check YangMills.Continuum.weakLimitValue
#check YangMills.Continuum.CandidateLawRealization
#check YangMills.Continuum.UniformlyTight
#check YangMills.Continuum.HasFluctuatingLimit
#check YangMills.Continuum.GeometricScalingCompatibility
#check YangMills.Continuum.ScaleConventionCompatible

#print axioms YangMills.Continuum.weakLimit_unique
#print axioms YangMills.Continuum.tendsto_weakLimitValue
#print axioms YangMills.Continuum.hasWeakLimit_constantCoupling_identity
#print axioms YangMills.Continuum.hasWeakLimit_constantCoupling_pointCylinder
#print axioms YangMills.Continuum.weakLimit_reflectionPositive
#print axioms YangMills.WindowPolymer.no_asymptotically_free_scaling_in_KP_regime
#print axioms YangMills.Continuum.tendsto_axisPairPhysicalSeparation_reciprocal
#print axioms YangMills.Continuum.tendsto_d4ScaleIndexedTruncatedCorrelation_zero
#print axioms YangMills.Continuum.tendsto_d4ScaleIndexedTwoPointData
#print axioms YangMills.Continuum.exampleD4_twoPoint_connected_tendsto_zero
