// Lean compiler output
// Module: YangMills.P6_AsymptoticFreedom.AsymptoticFreedomDischarge
// Imports: public import Init public import Mathlib public import YangMills.P4_Continuum.Phase4Assembly public import YangMills.P5_KPDecay.DecayFromRG public import YangMills.P6_AsymptoticFreedom.CouplingConvergence
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
lean_object* initialize_YangMills_YangMills_P4__Continuum_Phase4Assembly(uint8_t builtin);
lean_object* initialize_YangMills_YangMills_P5__KPDecay_DecayFromRG(uint8_t builtin);
lean_object* initialize_YangMills_YangMills_P6__AsymptoticFreedom_CouplingConvergence(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_YangMills_YangMills_P6__AsymptoticFreedom_AsymptoticFreedomDischarge(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_YangMills_YangMills_P4__Continuum_Phase4Assembly(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_YangMills_YangMills_P5__KPDecay_DecayFromRG(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_YangMills_YangMills_P6__AsymptoticFreedom_CouplingConvergence(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
