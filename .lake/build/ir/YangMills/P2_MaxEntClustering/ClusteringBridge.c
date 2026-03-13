// Lean compiler output
// Module: YangMills.P2_MaxEntClustering.ClusteringBridge
// Imports: public import Init public import Mathlib public import YangMills.P2_MaxEntClustering.PetzFidelity public import YangMills.P2_MaxEntClustering.LocalObservableAlgebras public import YangMills.P2_MaxEntClustering.MaxEntStates public import YangMills.P2_MaxEntClustering.RecoveryChannels public import YangMills.L6_OS.OsterwalderSchrader
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
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_YangMills_YangMills_P2__MaxEntClustering_PetzFidelity(uint8_t builtin);
lean_object* initialize_YangMills_YangMills_P2__MaxEntClustering_LocalObservableAlgebras(uint8_t builtin);
lean_object* initialize_YangMills_YangMills_P2__MaxEntClustering_MaxEntStates(uint8_t builtin);
lean_object* initialize_YangMills_YangMills_P2__MaxEntClustering_RecoveryChannels(uint8_t builtin);
lean_object* initialize_YangMills_YangMills_L6__OS_OsterwalderSchrader(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_YangMills_YangMills_P2__MaxEntClustering_ClusteringBridge(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib(builtin);
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
res = initialize_YangMills_YangMills_L6__OS_OsterwalderSchrader(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
