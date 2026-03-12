// Lean compiler output
// Module: YangMills.L0_Lattice.SU2Basic
// Imports: public import Init public import Mathlib
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
LEAN_EXPORT lean_object* lp_YangMills_YangMills_SU2;
lean_object* lp_mathlib_Complex_instStarRing___lam__0(lean_object*);
static const lean_closure_object lp_YangMills_YangMills_instGroupSubtypeMatrixFinOfNatNatComplexMemSubmonoidSU2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib_Complex_instStarRing___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_YangMills_YangMills_instGroupSubtypeMatrixFinOfNatNatComplexMemSubmonoidSU2___closed__0 = (const lean_object*)&lp_YangMills_YangMills_instGroupSubtypeMatrixFinOfNatNatComplexMemSubmonoidSU2___closed__0_value;
lean_object* l_instDecidableEqFin___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_YangMills_YangMills_instGroupSubtypeMatrixFinOfNatNatComplexMemSubmonoidSU2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instDecidableEqFin___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1))} };
static const lean_object* lp_YangMills_YangMills_instGroupSubtypeMatrixFinOfNatNatComplexMemSubmonoidSU2___closed__1 = (const lean_object*)&lp_YangMills_YangMills_instGroupSubtypeMatrixFinOfNatNatComplexMemSubmonoidSU2___closed__1_value;
lean_object* l_List_finRange(lean_object*);
static lean_once_cell_t lp_YangMills_YangMills_instGroupSubtypeMatrixFinOfNatNatComplexMemSubmonoidSU2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_YangMills_YangMills_instGroupSubtypeMatrixFinOfNatNatComplexMemSubmonoidSU2___closed__2;
extern lean_object* lp_mathlib_Complex_commRing;
lean_object* lp_mathlib_Matrix_instGroupSubtypeMemSubmonoidSpecialUnitaryGroup___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_YangMills_YangMills_instGroupSubtypeMatrixFinOfNatNatComplexMemSubmonoidSU2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_YangMills_YangMills_instGroupSubtypeMatrixFinOfNatNatComplexMemSubmonoidSU2___closed__3;
LEAN_EXPORT lean_object* lp_YangMills_YangMills_instGroupSubtypeMatrixFinOfNatNatComplexMemSubmonoidSU2;
static lean_object* _init_lp_YangMills_YangMills_SU2(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_lp_YangMills_YangMills_instGroupSubtypeMatrixFinOfNatNatComplexMemSubmonoidSU2___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = l_List_finRange(x_1);
return x_2;
}
}
static lean_object* _init_lp_YangMills_YangMills_instGroupSubtypeMatrixFinOfNatNatComplexMemSubmonoidSU2___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = ((lean_object*)(lp_YangMills_YangMills_instGroupSubtypeMatrixFinOfNatNatComplexMemSubmonoidSU2___closed__0));
x_2 = lp_mathlib_Complex_commRing;
x_3 = lean_obj_once(&lp_YangMills_YangMills_instGroupSubtypeMatrixFinOfNatNatComplexMemSubmonoidSU2___closed__2, &lp_YangMills_YangMills_instGroupSubtypeMatrixFinOfNatNatComplexMemSubmonoidSU2___closed__2_once, _init_lp_YangMills_YangMills_instGroupSubtypeMatrixFinOfNatNatComplexMemSubmonoidSU2___closed__2);
x_4 = ((lean_object*)(lp_YangMills_YangMills_instGroupSubtypeMatrixFinOfNatNatComplexMemSubmonoidSU2___closed__1));
x_5 = lp_mathlib_Matrix_instGroupSubtypeMemSubmonoidSpecialUnitaryGroup___redArg(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_lp_YangMills_YangMills_instGroupSubtypeMatrixFinOfNatNatComplexMemSubmonoidSU2(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&lp_YangMills_YangMills_instGroupSubtypeMatrixFinOfNatNatComplexMemSubmonoidSU2___closed__3, &lp_YangMills_YangMills_instGroupSubtypeMatrixFinOfNatNatComplexMemSubmonoidSU2___closed__3_once, _init_lp_YangMills_YangMills_instGroupSubtypeMatrixFinOfNatNatComplexMemSubmonoidSU2___closed__3);
return x_1;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_YangMills_YangMills_L0__Lattice_SU2Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_YangMills_YangMills_SU2 = _init_lp_YangMills_YangMills_SU2();
lean_mark_persistent(lp_YangMills_YangMills_SU2);
lp_YangMills_YangMills_instGroupSubtypeMatrixFinOfNatNatComplexMemSubmonoidSU2 = _init_lp_YangMills_YangMills_instGroupSubtypeMatrixFinOfNatNatComplexMemSubmonoidSU2();
lean_mark_persistent(lp_YangMills_YangMills_instGroupSubtypeMatrixFinOfNatNatComplexMemSubmonoidSU2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
