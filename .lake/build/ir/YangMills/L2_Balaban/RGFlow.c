// Lean compiler output
// Module: YangMills.L2_Balaban.RGFlow
// Imports: public import Init public import Mathlib public import YangMills.L0_Lattice.FiniteLattice public import YangMills.L0_Lattice.GaugeConfigurations public import YangMills.L0_Lattice.WilsonAction public import YangMills.L1_GibbsMeasure.GibbsMeasure public import YangMills.L2_Balaban.SmallLargeDecomposition public import YangMills.L2_Balaban.Measurability
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
lean_object* initialize_YangMills_YangMills_L0__Lattice_FiniteLattice(uint8_t builtin);
lean_object* initialize_YangMills_YangMills_L0__Lattice_GaugeConfigurations(uint8_t builtin);
lean_object* initialize_YangMills_YangMills_L0__Lattice_WilsonAction(uint8_t builtin);
lean_object* initialize_YangMills_YangMills_L1__GibbsMeasure_GibbsMeasure(uint8_t builtin);
lean_object* initialize_YangMills_YangMills_L2__Balaban_SmallLargeDecomposition(uint8_t builtin);
lean_object* initialize_YangMills_YangMills_L2__Balaban_Measurability(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_YangMills_YangMills_L2__Balaban_RGFlow(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib(builtin);
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
res = initialize_YangMills_YangMills_L1__GibbsMeasure_GibbsMeasure(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_YangMills_YangMills_L2__Balaban_SmallLargeDecomposition(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_YangMills_YangMills_L2__Balaban_Measurability(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
