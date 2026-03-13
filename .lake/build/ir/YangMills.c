// Lean compiler output
// Module: YangMills
// Imports: public import Init public import YangMills.L0_Lattice.FiniteLattice public import YangMills.L0_Lattice.GaugeConfigurations public import YangMills.L0_Lattice.WilsonAction public import YangMills.L0_Lattice.GaugeInvariance public import YangMills.L0_Lattice.SU2Basic public import YangMills.L0_Lattice.FiniteLatticeGeometryInstance public import YangMills.L1_GibbsMeasure.GibbsMeasure public import YangMills.L1_GibbsMeasure.Expectation public import YangMills.L1_GibbsMeasure.Correlations public import YangMills.L2_Balaban.SmallLargeDecomposition public import YangMills.L2_Balaban.RGFlow public import YangMills.L2_Balaban.Measurability public import YangMills.L3_RGIteration.BlockSpin public import YangMills.L3_RGIteration.GaugeInvarianceMeasure public import YangMills.L3_RGIteration.GaugeMeasureInvariance public import YangMills.L4_LargeField.Suppression public import YangMills.L4_WilsonLoops.WilsonLoop public import YangMills.L4_TransferMatrix.TransferMatrix public import YangMills.L5_MassGap.MassGap public import YangMills.L6_FeynmanKac.FeynmanKac public import YangMills.L6_OS.OsterwalderSchrader public import YangMills.L7_Continuum.ContinuumLimit public import YangMills.L8_Terminal.ClayTheorem public import YangMills.P2_MaxEntClustering.PetzFidelity public import YangMills.P2_MaxEntClustering.LocalObservableAlgebras public import YangMills.P2_MaxEntClustering.MaxEntStates public import YangMills.P2_MaxEntClustering.RecoveryChannels public import YangMills.P2_MaxEntClustering.ClusteringBridge public import YangMills.P3_BalabanRG.CorrelationNorms public import YangMills.P3_BalabanRG.CorrelationNorms
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_YangMills_YangMills_L0__Lattice_FiniteLattice(uint8_t builtin);
lean_object* initialize_YangMills_YangMills_L0__Lattice_GaugeConfigurations(uint8_t builtin);
lean_object* initialize_YangMills_YangMills_L0__Lattice_WilsonAction(uint8_t builtin);
lean_object* initialize_YangMills_YangMills_L0__Lattice_GaugeInvariance(uint8_t builtin);
lean_object* initialize_YangMills_YangMills_L0__Lattice_SU2Basic(uint8_t builtin);
lean_object* initialize_YangMills_YangMills_L0__Lattice_FiniteLatticeGeometryInstance(uint8_t builtin);
lean_object* initialize_YangMills_YangMills_L1__GibbsMeasure_GibbsMeasure(uint8_t builtin);
lean_object* initialize_YangMills_YangMills_L1__GibbsMeasure_Expectation(uint8_t builtin);
lean_object* initialize_YangMills_YangMills_L1__GibbsMeasure_Correlations(uint8_t builtin);
lean_object* initialize_YangMills_YangMills_L2__Balaban_SmallLargeDecomposition(uint8_t builtin);
lean_object* initialize_YangMills_YangMills_L2__Balaban_RGFlow(uint8_t builtin);
lean_object* initialize_YangMills_YangMills_L2__Balaban_Measurability(uint8_t builtin);
lean_object* initialize_YangMills_YangMills_L3__RGIteration_BlockSpin(uint8_t builtin);
lean_object* initialize_YangMills_YangMills_L3__RGIteration_GaugeInvarianceMeasure(uint8_t builtin);
lean_object* initialize_YangMills_YangMills_L3__RGIteration_GaugeMeasureInvariance(uint8_t builtin);
lean_object* initialize_YangMills_YangMills_L4__LargeField_Suppression(uint8_t builtin);
lean_object* initialize_YangMills_YangMills_L4__WilsonLoops_WilsonLoop(uint8_t builtin);
lean_object* initialize_YangMills_YangMills_L4__TransferMatrix_TransferMatrix(uint8_t builtin);
lean_object* initialize_YangMills_YangMills_L5__MassGap_MassGap(uint8_t builtin);
lean_object* initialize_YangMills_YangMills_L6__FeynmanKac_FeynmanKac(uint8_t builtin);
lean_object* initialize_YangMills_YangMills_L6__OS_OsterwalderSchrader(uint8_t builtin);
lean_object* initialize_YangMills_YangMills_L7__Continuum_ContinuumLimit(uint8_t builtin);
lean_object* initialize_YangMills_YangMills_L8__Terminal_ClayTheorem(uint8_t builtin);
lean_object* initialize_YangMills_YangMills_P2__MaxEntClustering_PetzFidelity(uint8_t builtin);
lean_object* initialize_YangMills_YangMills_P2__MaxEntClustering_LocalObservableAlgebras(uint8_t builtin);
lean_object* initialize_YangMills_YangMills_P2__MaxEntClustering_MaxEntStates(uint8_t builtin);
lean_object* initialize_YangMills_YangMills_P2__MaxEntClustering_RecoveryChannels(uint8_t builtin);
lean_object* initialize_YangMills_YangMills_P2__MaxEntClustering_ClusteringBridge(uint8_t builtin);
lean_object* initialize_YangMills_YangMills_P3__BalabanRG_CorrelationNorms(uint8_t builtin);
lean_object* initialize_YangMills_YangMills_P3__BalabanRG_CorrelationNorms(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_YangMills_YangMills(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_YangMills_YangMills_L0__Lattice_FiniteLattice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_YangMills_YangMills_L0__Lattice_GaugeConfigurations(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_YangMills_YangMills_L0__Lattice_WilsonAction(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_YangMills_YangMills_L0__Lattice_GaugeInvariance(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_YangMills_YangMills_L0__Lattice_SU2Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_YangMills_YangMills_L0__Lattice_FiniteLatticeGeometryInstance(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_YangMills_YangMills_L1__GibbsMeasure_GibbsMeasure(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_YangMills_YangMills_L1__GibbsMeasure_Expectation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_YangMills_YangMills_L1__GibbsMeasure_Correlations(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_YangMills_YangMills_L2__Balaban_SmallLargeDecomposition(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_YangMills_YangMills_L2__Balaban_RGFlow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_YangMills_YangMills_L2__Balaban_Measurability(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_YangMills_YangMills_L3__RGIteration_BlockSpin(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_YangMills_YangMills_L3__RGIteration_GaugeInvarianceMeasure(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_YangMills_YangMills_L3__RGIteration_GaugeMeasureInvariance(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_YangMills_YangMills_L4__LargeField_Suppression(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_YangMills_YangMills_L4__WilsonLoops_WilsonLoop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_YangMills_YangMills_L4__TransferMatrix_TransferMatrix(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_YangMills_YangMills_L5__MassGap_MassGap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_YangMills_YangMills_L6__FeynmanKac_FeynmanKac(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_YangMills_YangMills_L6__OS_OsterwalderSchrader(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_YangMills_YangMills_L7__Continuum_ContinuumLimit(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_YangMills_YangMills_L8__Terminal_ClayTheorem(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_YangMills_YangMills_P2__MaxEntClustering_PetzFidelity(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_YangMills_YangMills_P2__MaxEntClustering_LocalObservableAlgebras(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_YangMills_YangMills_P2__MaxEntClustering_MaxEntStates(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_YangMills_YangMills_P2__MaxEntClustering_RecoveryChannels(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_YangMills_YangMills_P2__MaxEntClustering_ClusteringBridge(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_YangMills_YangMills_P3__BalabanRG_CorrelationNorms(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_YangMills_YangMills_P3__BalabanRG_CorrelationNorms(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
