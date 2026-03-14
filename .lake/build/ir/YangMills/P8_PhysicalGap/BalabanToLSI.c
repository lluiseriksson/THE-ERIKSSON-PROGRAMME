// Lean compiler output
// Module: YangMills.P8_PhysicalGap.BalabanToLSI
// Imports: public import Init public import Mathlib public import YangMills.P8_PhysicalGap.LSItoSpectralGap public import YangMills.L0_Lattice.WilsonAction
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
LEAN_EXPORT lean_object* lp_YangMills_YangMills_instMeasurableSpaceSUN__State(lean_object*);
LEAN_EXPORT lean_object* lp_YangMills_YangMills_instMeasurableSpaceSUN__State___boxed(lean_object*);
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
LEAN_EXPORT lean_object* lp_YangMills_YangMills_sunDirichletForm(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_YangMills_YangMills_sunDirichletForm___boxed(lean_object*, lean_object*);
static lean_once_cell_t lp_YangMills_YangMills_sunGibbsFamily___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_YangMills_YangMills_sunGibbsFamily___lam__0___closed__0;
LEAN_EXPORT lean_object* lp_YangMills_YangMills_sunGibbsFamily___lam__0(lean_object*);
static const lean_closure_object lp_YangMills_YangMills_sunGibbsFamily___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_YangMills_YangMills_sunGibbsFamily___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_YangMills_YangMills_sunGibbsFamily___closed__0 = (const lean_object*)&lp_YangMills_YangMills_sunGibbsFamily___closed__0_value;
LEAN_EXPORT lean_object* lp_YangMills_YangMills_sunGibbsFamily(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_YangMills_YangMills_sunGibbsFamily___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_YangMills_YangMills_instMeasurableSpaceSUN__State(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_YangMills_YangMills_instMeasurableSpaceSUN__State___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_YangMills_YangMills_instMeasurableSpaceSUN__State(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_YangMills_YangMills_sunDirichletForm(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
return x_3;
}
}
LEAN_EXPORT lean_object* lp_YangMills_YangMills_sunDirichletForm___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_YangMills_YangMills_sunDirichletForm(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_lp_YangMills_YangMills_sunGibbsFamily___lam__0___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_YangMills_YangMills_sunGibbsFamily___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_obj_once(&lp_YangMills_YangMills_sunGibbsFamily___lam__0___closed__0, &lp_YangMills_YangMills_sunGibbsFamily___lam__0___closed__0_once, _init_lp_YangMills_YangMills_sunGibbsFamily___lam__0___closed__0);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_YangMills_YangMills_sunGibbsFamily(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = ((lean_object*)(lp_YangMills_YangMills_sunGibbsFamily___closed__0));
return x_5;
}
}
LEAN_EXPORT lean_object* lp_YangMills_YangMills_sunGibbsFamily___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_YangMills_YangMills_sunGibbsFamily(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_YangMills_YangMills_P8__PhysicalGap_LSItoSpectralGap(uint8_t builtin);
lean_object* initialize_YangMills_YangMills_L0__Lattice_WilsonAction(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_YangMills_YangMills_P8__PhysicalGap_BalabanToLSI(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_YangMills_YangMills_P8__PhysicalGap_LSItoSpectralGap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_YangMills_YangMills_L0__Lattice_WilsonAction(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
