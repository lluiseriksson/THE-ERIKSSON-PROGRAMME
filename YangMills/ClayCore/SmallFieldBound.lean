import YangMills.ClayCore.BalabanH1H2H3
namespace YangMills
open Real

/-- Constants characterising a Balaban small-field activity bound. -/
structure SmallFieldConstants where
  E0 : Real
  hE0 : 0 < E0
  kappa : Real
  hkappa : 0 < kappa
  g_bar : Real
  hg_pos : 0 < g_bar
  hg_lt1 : g_bar < 1

/-- A quantitative small-field activity bound in the sense of Balaban CMP 116. -/
structure SmallFieldActivityBound (N_c : Nat) [NeZero N_c] where
  consts : SmallFieldConstants
  activity : Nat -> Real
  hact_nn : forall (n : Nat), 0 <= activity n
  hact_bd : forall (n : Nat),
    activity n <= consts.E0 * consts.g_bar ^ 2 * Real.exp (-consts.kappa * n)

/-- Given a small-field activity bound, produce the corresponding BalabanH1. -/
noncomputable def h1_of_small_field_bound {N_c : Nat} [NeZero N_c]
    (sfb : SmallFieldActivityBound N_c) : BalabanH1 N_c :=
  { E0 := sfb.consts.E0
  , hE0 := sfb.consts.hE0
  , kappa := sfb.consts.kappa
  , hkappa := sfb.consts.hkappa
  , g_bar := sfb.consts.g_bar
  , hg_pos := sfb.consts.hg_pos
  , hg_lt1 := sfb.consts.hg_lt1
  , h_sf := fun n => ⟨sfb.activity n, sfb.hact_nn n, sfb.hact_bd n⟩ }

/-- The Balaban H1 hypothesis is discharged by any small-field activity bound. -/
theorem h1_from_small_field {N_c : Nat} [NeZero N_c]
    (sfb : SmallFieldActivityBound N_c) :
    exists h1 : BalabanH1 N_c,
      (h1.E0 = sfb.consts.E0) ∧ (h1.g_bar = sfb.consts.g_bar) ∧
      (h1.kappa = sfb.consts.kappa) :=
  ⟨h1_of_small_field_bound sfb, rfl, rfl, rfl⟩

end YangMills
