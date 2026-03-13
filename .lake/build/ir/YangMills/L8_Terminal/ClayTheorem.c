// Lean compiler output
// Module: YangMills.L8_Terminal.ClayTheorem
// Imports: public import Init public import YangMills.L5_MassGap.MassGap public import YangMills.L6_FeynmanKac.FeynmanKac public import YangMills.L6_OS.OsterwalderSchrader public import YangMills.L7_Continuum.ContinuumLimit
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
lean_object* initialize_YangMills_YangMills_L5__MassGap_MassGap(uint8_t builtin);
lean_object* initialize_YangMills_YangMills_L6__FeynmanKac_FeynmanKac(uint8_t builtin);
lean_object* initialize_YangMills_YangMills_L6__OS_OsterwalderSchrader(uint8_t builtin);
lean_object* initialize_YangMills_YangMills_L7__Continuum_ContinuumLimit(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_YangMills_YangMills_L8__Terminal_ClayTheorem(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
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
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
