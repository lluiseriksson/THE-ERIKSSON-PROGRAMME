// Lean compiler output
// Module: YangMills.P6_AsymptoticFreedom.BetaFunction
// Imports: public import Init public import Mathlib public import YangMills.P4_Continuum.Phase4Assembly
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_YangMills_YangMills_InvCouplingSeq(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_YangMills_YangMills_InvCouplingSeq___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_YangMills___private_YangMills_P6__AsymptoticFreedom_BetaFunction_0__YangMills_InvCouplingSeq_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_YangMills___private_YangMills_P6__AsymptoticFreedom_BetaFunction_0__YangMills_InvCouplingSeq_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_YangMills___private_YangMills_P6__AsymptoticFreedom_BetaFunction_0__YangMills_InvCouplingSeq_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_YangMills___private_YangMills_P6__AsymptoticFreedom_BetaFunction_0__YangMills_InvCouplingSeq_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_YangMills_YangMills_InvCouplingSeq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_4, x_5);
if (x_6 == 1)
{
lean_dec(x_2);
lean_dec(x_1);
lean_inc(x_3);
return x_3;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_4, x_7);
lean_inc(x_2);
lean_inc(x_1);
x_9 = lp_YangMills_YangMills_InvCouplingSeq(x_1, x_2, x_3, x_8);
x_10 = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(x_10, 0, x_9);
lean_closure_set(x_10, 1, x_1);
x_11 = lean_apply_1(x_2, x_8);
x_12 = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(x_12, 0, x_10);
lean_closure_set(x_12, 1, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* lp_YangMills_YangMills_InvCouplingSeq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_YangMills_YangMills_InvCouplingSeq(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_YangMills___private_YangMills_P6__AsymptoticFreedom_BetaFunction_0__YangMills_InvCouplingSeq_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_1, x_4);
if (x_5 == 1)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_box(0);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_2);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_1, x_8);
x_10 = lean_apply_1(x_3, x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* lp_YangMills___private_YangMills_P6__AsymptoticFreedom_BetaFunction_0__YangMills_InvCouplingSeq_match__1_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_YangMills___private_YangMills_P6__AsymptoticFreedom_BetaFunction_0__YangMills_InvCouplingSeq_match__1_splitter___redArg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_YangMills___private_YangMills_P6__AsymptoticFreedom_BetaFunction_0__YangMills_InvCouplingSeq_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_YangMills___private_YangMills_P6__AsymptoticFreedom_BetaFunction_0__YangMills_InvCouplingSeq_match__1_splitter___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_YangMills___private_YangMills_P6__AsymptoticFreedom_BetaFunction_0__YangMills_InvCouplingSeq_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_YangMills___private_YangMills_P6__AsymptoticFreedom_BetaFunction_0__YangMills_InvCouplingSeq_match__1_splitter(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_YangMills_YangMills_P4__Continuum_Phase4Assembly(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_YangMills_YangMills_P6__AsymptoticFreedom_BetaFunction(uint8_t builtin) {
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
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
