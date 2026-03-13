// Lean compiler output
// Module: YangMills.P2_MaxEntClustering.RecoveryChannels
// Imports: public import Init public import Mathlib public import YangMills.P2_MaxEntClustering.PetzFidelity public import YangMills.P2_MaxEntClustering.MaxEntStates
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
LEAN_EXPORT lean_object* lp_YangMills_YangMills_applyRecovery___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_YangMills_YangMills_applyRecovery(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_YangMills_YangMills_applyRecovery___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_YangMills_YangMills_applyRecovery___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_YangMills_YangMills_applyRecovery(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_1(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_YangMills_YangMills_applyRecovery___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_YangMills_YangMills_applyRecovery(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_YangMills_YangMills_P2__MaxEntClustering_PetzFidelity(uint8_t builtin);
lean_object* initialize_YangMills_YangMills_P2__MaxEntClustering_MaxEntStates(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_YangMills_YangMills_P2__MaxEntClustering_RecoveryChannels(uint8_t builtin) {
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
res = initialize_YangMills_YangMills_P2__MaxEntClustering_MaxEntStates(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
