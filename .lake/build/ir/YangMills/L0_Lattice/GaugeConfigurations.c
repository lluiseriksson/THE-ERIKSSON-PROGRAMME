// Lean compiler output
// Module: YangMills.L0_Lattice.GaugeConfigurations
// Imports: public import Init public import Mathlib public import YangMills.L0_Lattice.FiniteLattice
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
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_YangMills_YangMills_succ4(lean_object*);
LEAN_EXPORT lean_object* lp_YangMills_YangMills_succ4___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_YangMills_YangMills_GaugeConfig_instCoeFunForallE___lam__0(lean_object*, lean_object*);
static const lean_closure_object lp_YangMills_YangMills_GaugeConfig_instCoeFunForallE___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_YangMills_YangMills_GaugeConfig_instCoeFunForallE___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_YangMills_YangMills_GaugeConfig_instCoeFunForallE___closed__0 = (const lean_object*)&lp_YangMills_YangMills_GaugeConfig_instCoeFunForallE___closed__0_value;
LEAN_EXPORT lean_object* lp_YangMills_YangMills_GaugeConfig_instCoeFunForallE(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_YangMills_YangMills_GaugeConfig_instCoeFunForallE___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_YangMills_YangMills_GaugeConfig_plaquetteHolonomy___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_YangMills_YangMills_GaugeConfig_plaquetteHolonomy___redArg___closed__0;
static lean_once_cell_t lp_YangMills_YangMills_GaugeConfig_plaquetteHolonomy___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_YangMills_YangMills_GaugeConfig_plaquetteHolonomy___redArg___closed__1;
static lean_once_cell_t lp_YangMills_YangMills_GaugeConfig_plaquetteHolonomy___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_YangMills_YangMills_GaugeConfig_plaquetteHolonomy___redArg___closed__2;
static lean_once_cell_t lp_YangMills_YangMills_GaugeConfig_plaquetteHolonomy___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_YangMills_YangMills_GaugeConfig_plaquetteHolonomy___redArg___closed__3;
lean_object* lp_mathlib_Monoid_toMulOneClass___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_YangMills_YangMills_GaugeConfig_plaquetteHolonomy___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_YangMills_YangMills_GaugeConfig_plaquetteHolonomy___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_YangMills_YangMills_GaugeConfig_plaquetteHolonomy(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_YangMills_YangMills_GaugeConfig_plaquetteHolonomy___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_YangMills_YangMills_GaugeConfig_gaugeAct___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_DivInvOneMonoid_toInvOneClass___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_YangMills_YangMills_GaugeConfig_gaugeAct___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_YangMills_YangMills_GaugeConfig_gaugeAct___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_YangMills_YangMills_GaugeConfig_gaugeAct(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_YangMills_YangMills_GaugeConfig_gaugeAct___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_YangMills_YangMills_succ4(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_unsigned_to_nat(4u);
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_nat_add(x_1, x_3);
x_5 = lean_nat_mod(x_4, x_2);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_YangMills_YangMills_succ4___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_YangMills_YangMills_succ4(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_YangMills_YangMills_GaugeConfig_instCoeFunForallE___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_YangMills_YangMills_GaugeConfig_instCoeFunForallE(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = ((lean_object*)(lp_YangMills_YangMills_GaugeConfig_instCoeFunForallE___closed__0));
return x_6;
}
}
LEAN_EXPORT lean_object* lp_YangMills_YangMills_GaugeConfig_instCoeFunForallE___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lp_YangMills_YangMills_GaugeConfig_instCoeFunForallE(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
static lean_object* _init_lp_YangMills_YangMills_GaugeConfig_plaquetteHolonomy___redArg___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_nat_mod(x_2, x_1);
return x_3;
}
}
static lean_object* _init_lp_YangMills_YangMills_GaugeConfig_plaquetteHolonomy___redArg___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_mod(x_2, x_1);
return x_3;
}
}
static lean_object* _init_lp_YangMills_YangMills_GaugeConfig_plaquetteHolonomy___redArg___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(2u);
x_3 = lean_nat_mod(x_2, x_1);
return x_3;
}
}
static lean_object* _init_lp_YangMills_YangMills_GaugeConfig_plaquetteHolonomy___redArg___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(3u);
x_3 = lean_nat_mod(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_YangMills_YangMills_GaugeConfig_plaquetteHolonomy___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lp_mathlib_Monoid_toMulOneClass___redArg(x_5);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec_ref(x_6);
x_8 = lean_ctor_get(x_2, 6);
lean_inc(x_8);
lean_dec_ref(x_2);
x_9 = lean_obj_once(&lp_YangMills_YangMills_GaugeConfig_plaquetteHolonomy___redArg___closed__0, &lp_YangMills_YangMills_GaugeConfig_plaquetteHolonomy___redArg___closed__0_once, _init_lp_YangMills_YangMills_GaugeConfig_plaquetteHolonomy___redArg___closed__0);
lean_inc(x_8);
lean_inc(x_4);
x_10 = lean_apply_2(x_8, x_4, x_9);
lean_inc(x_3);
x_11 = lean_apply_1(x_3, x_10);
x_12 = lean_obj_once(&lp_YangMills_YangMills_GaugeConfig_plaquetteHolonomy___redArg___closed__1, &lp_YangMills_YangMills_GaugeConfig_plaquetteHolonomy___redArg___closed__1_once, _init_lp_YangMills_YangMills_GaugeConfig_plaquetteHolonomy___redArg___closed__1);
lean_inc(x_8);
lean_inc(x_4);
x_13 = lean_apply_2(x_8, x_4, x_12);
lean_inc(x_3);
x_14 = lean_apply_1(x_3, x_13);
lean_inc(x_7);
x_15 = lean_apply_2(x_7, x_11, x_14);
x_16 = lean_obj_once(&lp_YangMills_YangMills_GaugeConfig_plaquetteHolonomy___redArg___closed__2, &lp_YangMills_YangMills_GaugeConfig_plaquetteHolonomy___redArg___closed__2_once, _init_lp_YangMills_YangMills_GaugeConfig_plaquetteHolonomy___redArg___closed__2);
lean_inc(x_8);
lean_inc(x_4);
x_17 = lean_apply_2(x_8, x_4, x_16);
lean_inc(x_3);
x_18 = lean_apply_1(x_3, x_17);
lean_inc(x_7);
x_19 = lean_apply_2(x_7, x_15, x_18);
x_20 = lean_obj_once(&lp_YangMills_YangMills_GaugeConfig_plaquetteHolonomy___redArg___closed__3, &lp_YangMills_YangMills_GaugeConfig_plaquetteHolonomy___redArg___closed__3_once, _init_lp_YangMills_YangMills_GaugeConfig_plaquetteHolonomy___redArg___closed__3);
x_21 = lean_apply_2(x_8, x_4, x_20);
x_22 = lean_apply_1(x_3, x_21);
x_23 = lean_apply_2(x_7, x_19, x_22);
return x_23;
}
}
LEAN_EXPORT lean_object* lp_YangMills_YangMills_GaugeConfig_plaquetteHolonomy___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_YangMills_YangMills_GaugeConfig_plaquetteHolonomy___redArg(x_1, x_2, x_3, x_4);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_YangMills_YangMills_GaugeConfig_plaquetteHolonomy(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lp_YangMills_YangMills_GaugeConfig_plaquetteHolonomy___redArg(x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* lp_YangMills_YangMills_GaugeConfig_plaquetteHolonomy___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lp_YangMills_YangMills_GaugeConfig_plaquetteHolonomy(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* lp_YangMills_YangMills_GaugeConfig_gaugeAct___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_7 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_7);
x_8 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_8);
lean_dec_ref(x_1);
lean_inc(x_6);
x_9 = lean_apply_1(x_7, x_6);
lean_inc(x_2);
x_10 = lean_apply_1(x_2, x_9);
lean_inc(x_6);
x_11 = lean_apply_1(x_3, x_6);
lean_inc(x_4);
x_12 = lean_apply_2(x_4, x_10, x_11);
x_13 = lean_apply_1(x_8, x_6);
x_14 = lean_apply_1(x_2, x_13);
x_15 = lean_apply_1(x_5, x_14);
x_16 = lean_apply_2(x_4, x_12, x_15);
return x_16;
}
}
LEAN_EXPORT lean_object* lp_YangMills_YangMills_GaugeConfig_gaugeAct___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lp_mathlib_Monoid_toMulOneClass___redArg(x_5);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec_ref(x_6);
x_8 = lp_mathlib_DivInvOneMonoid_toInvOneClass___redArg(x_1);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec_ref(x_8);
x_10 = lean_alloc_closure((void*)(lp_YangMills_YangMills_GaugeConfig_gaugeAct___redArg___lam__0), 6, 5);
lean_closure_set(x_10, 0, x_2);
lean_closure_set(x_10, 1, x_3);
lean_closure_set(x_10, 2, x_4);
lean_closure_set(x_10, 3, x_7);
lean_closure_set(x_10, 4, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* lp_YangMills_YangMills_GaugeConfig_gaugeAct___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_YangMills_YangMills_GaugeConfig_gaugeAct___redArg(x_1, x_2, x_3, x_4);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_YangMills_YangMills_GaugeConfig_gaugeAct(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lp_YangMills_YangMills_GaugeConfig_gaugeAct___redArg(x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* lp_YangMills_YangMills_GaugeConfig_gaugeAct___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lp_YangMills_YangMills_GaugeConfig_gaugeAct(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_YangMills_YangMills_L0__Lattice_FiniteLattice(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_YangMills_YangMills_L0__Lattice_GaugeConfigurations(uint8_t builtin) {
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
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
