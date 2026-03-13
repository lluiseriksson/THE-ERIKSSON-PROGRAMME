// Lean compiler output
// Module: YangMills.P3_BalabanRG.CorrelationNorms
// Imports: public import Init public import Mathlib public import YangMills.L4_WilsonLoops.WilsonLoop public import YangMills.L5_MassGap.MassGap public import YangMills.L3_RGIteration.BlockSpin public import YangMills.L7_Continuum.ContinuumLimit
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
lean_object* initialize_YangMills_YangMills_L4__WilsonLoops_WilsonLoop(uint8_t builtin);
lean_object* initialize_YangMills_YangMills_L5__MassGap_MassGap(uint8_t builtin);
lean_object* initialize_YangMills_YangMills_L3__RGIteration_BlockSpin(uint8_t builtin);
lean_object* initialize_YangMills_YangMills_L7__Continuum_ContinuumLimit(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_YangMills_YangMills_P3__BalabanRG_CorrelationNorms(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_YangMills_YangMills_L4__WilsonLoops_WilsonLoop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_YangMills_YangMills_L5__MassGap_MassGap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_YangMills_YangMills_L3__RGIteration_BlockSpin(builtin);
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
