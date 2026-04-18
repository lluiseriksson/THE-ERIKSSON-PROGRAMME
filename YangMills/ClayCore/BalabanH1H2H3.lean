import YangMills.ClayCore.KPSmallness
import YangMills.ClayCore.CouplingControl
namespace YangMills
open Real
structure BalabanH1 (N_c : Nat) [NeZero N_c] where
  E0 : Real
  hE0 : 0 < E0
  kappa : Real
  hkappa : 0 < kappa
  g_bar : Real
  hg_pos : 0 < g_bar
  hg_lt1 : g_bar < 1
  h_sf : forall (n : Nat), exists R : Real,
    0 <= R /\ R <= E0 * g_bar ^ 2 * Real.exp (-kappa * n)
structure BalabanH2 (N_c : Nat) [NeZero N_c] where
  p0 : Real
  hp0 : 0 < p0
  kappa : Real
  hkappa : 0 < kappa
  g_bar : Real
  hg_pos : 0 < g_bar
  h_lf : forall (n : Nat), exists R : Real,
    0 <= R /\ R <= Real.exp (-p0) * Real.exp (-kappa * n)
structure BalabanH3 where
  h_local : True
structure BalabanHyps (N_c : Nat) [NeZero N_c] where
  h1 : BalabanH1 N_c
  h2 : BalabanH2 N_c
  h3 : BalabanH3
  hg_eq : h1.g_bar = h2.g_bar
  hk_eq : h1.kappa = h2.kappa
  hlf_le : Real.exp (-h2.p0) <= h1.E0 * h1.g_bar ^ 2
theorem balaban_combined_bound {N_c : Nat} [NeZero N_c]
    (hyps : BalabanHyps N_c) (n : Nat) :
    exists R : Real, 0 <= R /\
    R <= 2 * hyps.h1.E0 * hyps.h1.g_bar ^ 2 * Real.exp (-hyps.h1.kappa * n) := by
  obtain ⟨Rsf, hRsf_nn, hRsf_bd⟩ := hyps.h1.h_sf n
  obtain ⟨Rlf, hRlf_nn, hRlf_bd⟩ := hyps.h2.h_lf n
  refine ⟨Rsf + Rlf, by linarith, ?_⟩
  have step2 : Real.exp (-hyps.h2.p0) * Real.exp (-hyps.h2.kappa * n) <=
      hyps.h1.E0 * hyps.h1.g_bar ^ 2 * Real.exp (-hyps.h1.kappa * n) := by
    rw [hyps.hk_eq]
    exact mul_le_mul_of_nonneg_right hyps.hlf_le (Real.exp_nonneg _)
  linarith
noncomputable def polymerBound_of_balaban {N_c : Nat} [NeZero N_c]
    (hyps : BalabanHyps N_c) : PolymerActivityBound where
  dim := 4
  A₀ := 2 * hyps.h1.E0
  hA₀ := by linarith [hyps.h1.hE0]
  r := hyps.h1.g_bar
  hr_pos := hyps.h1.hg_pos
  hr_lt_one := hyps.h1.hg_lt1
  C_anim := (2 * 4) ^ 3
  hC := by norm_num
theorem balaban_to_polymer_bound {N_c : Nat} [NeZero N_c]
    (hyps : BalabanHyps N_c) : exists pab : PolymerActivityBound,
    pab.r = hyps.h1.g_bar :=
  ⟨polymerBound_of_balaban hyps, rfl⟩
end YangMills
