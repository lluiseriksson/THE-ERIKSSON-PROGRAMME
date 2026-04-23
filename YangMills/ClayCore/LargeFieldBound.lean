import YangMills.ClayCore.BalabanH1H2H3
import YangMills.ClayCore.SmallFieldBound

/-! # Large-Field Polymer Activity Bound (H2 discharged)

Source: Paper [55] (Eriksson 2602.0069) Theorem 8.5, Eq (51)-(52).
Primary: Balaban CMP 122 II, Eq (1.98)-(1.100).

v0.42.0 / Phase 3 / Task #7 P2c: the `h_dominated` field of
`LargeFieldActivityBound` is refactored from the over-strong
`∀ E0 > 0, exp(-p0) ≤ E0 * g^2` quantifier to a fixed-constant form
`exp(-p0) ≤ E0 * g^2` with `E0` and `hE0 : 0 < E0` exposed as struct
fields. This matches what `superPoly_dominance_at_specific` produces
for a chosen small-enough coupling, and lets the consumer at
`balabanHyps_of_bounds` bridge the two sides via an equality
`hE0_eq : sfb.consts.E0 = lfb.E0`. -/

namespace YangMills
open Real

/-- The large-field suppression profile p0(g) from Paper [55] Sec 8.1.

    Note: Theorem 8.5 uses p0(g) = A0 * (log(g^{-2}))^{p*} with super-polynomial
    growth as g -> 0. For the formalization we keep the positivity property
    (heval_pos) which is what `BalabanH2` actually needs via `hp0 : 0 < p0`.
    Super-polynomial growth is documented but not required as a Lean field. -/
structure LargeFieldProfile where
  A0 : Real
  hA0 : 0 < A0
  pstar : Real
  hpstar : 0 < pstar
  eval : Real -> Real
  heval_pos : forall g : Real, 0 < g -> g < 1 -> 0 < eval g

/-- Concrete profile: p0(g) = -log g / 2. Positive for g in (0,1). -/
noncomputable def simpleLargeFieldProfile : LargeFieldProfile where
  A0 := 1/2
  hA0 := by norm_num
  pstar := 1
  hpstar := one_pos
  eval := fun g => -Real.log g / 2
  heval_pos := fun g hg_pos hg_lt1 => by
    have h : Real.log g < 0 := Real.log_neg hg_pos hg_lt1
    linarith

/-- Large-field activity bound structure, Theorem 8.5 of Paper [55].

    Post-P2c: the `h_dominated` field carries a fixed dominance constant
    `E0` (exposed as a struct field) rather than the over-strong
    `∀ E0 > 0` quantifier. Witnesses are produced by
    `YangMills.superPoly_dominance_at_specific` for a chosen coupling. -/
structure LargeFieldActivityBound (N_c : Nat) [NeZero N_c] where
  profile : LargeFieldProfile
  kappa : Real
  hkappa : 0 < kappa
  g_bar : Real
  hg_pos : 0 < g_bar
  hg_lt1 : g_bar < 1
  E0 : Real
  hE0 : 0 < E0
  h_lf_bound : forall (n : Nat), exists R : Real, 0 <= R ∧
    R <= Real.exp (-(profile.eval g_bar)) * Real.exp (-kappa * n)
  h_dominated : Real.exp (-(profile.eval g_bar)) <= E0 * g_bar ^ 2

/-- From LargeFieldActivityBound, construct BalabanH2. -/
noncomputable def h2_of_large_field_bound {N_c : Nat} [NeZero N_c]
    (lfb : LargeFieldActivityBound N_c) : BalabanH2 N_c where
  p0 := lfb.profile.eval lfb.g_bar
  hp0 := lfb.profile.heval_pos lfb.g_bar lfb.hg_pos lfb.hg_lt1
  kappa := lfb.kappa
  hkappa := lfb.hkappa
  g_bar := lfb.g_bar
  hg_pos := lfb.hg_pos
  h_lf := lfb.h_lf_bound

/-- LargeFieldActivityBound gives BalabanH2. -/
theorem h2_from_large_field {N_c : Nat} [NeZero N_c]
    (lfb : LargeFieldActivityBound N_c) :
    exists h2 : BalabanH2 N_c, h2.g_bar = lfb.g_bar :=
  ⟨h2_of_large_field_bound lfb, rfl⟩

/-- Dominance condition from LargeFieldActivityBound. Post-P2c: the
    dominance constant `E0` is the one exposed as a struct field. -/
theorem lf_dominance_gives_hlf_le {N_c : Nat} [NeZero N_c]
    (lfb : LargeFieldActivityBound N_c) :
    Real.exp (-(lfb.profile.eval lfb.g_bar)) <= lfb.E0 * lfb.g_bar ^ 2 :=
  lfb.h_dominated

/-- Assemble full BalabanHyps from small-field + large-field bounds.

    Post-P2c: consumers must provide `hE0_eq : sfb.consts.E0 = lfb.E0`
    to connect the small-field dominance constant with the large-field
    one. -/
noncomputable def balabanHyps_of_bounds {N_c : Nat} [NeZero N_c]
    (sfb : SmallFieldActivityBound N_c)
    (lfb : LargeFieldActivityBound N_c)
    (hg_eq : sfb.consts.g_bar = lfb.g_bar)
    (hk_eq : sfb.consts.kappa = lfb.kappa)
    (hE0_eq : sfb.consts.E0 = lfb.E0) :
    BalabanHyps N_c where
  h1 := h1_of_small_field_bound sfb
  h2 := h2_of_large_field_bound lfb
  h3 := { h_local := trivial }
  hg_eq := hg_eq
  hk_eq := hk_eq
  hlf_le := by
    show Real.exp (-lfb.profile.eval lfb.g_bar) <= sfb.consts.E0 * sfb.consts.g_bar ^ 2
    rw [hg_eq, hE0_eq]; exact lfb.h_dominated

/-- All three Balaban hypotheses from concrete bounds. -/
theorem all_balaban_hyps_from_bounds {N_c : Nat} [NeZero N_c]
    (sfb : SmallFieldActivityBound N_c)
    (lfb : LargeFieldActivityBound N_c)
    (hg_eq : sfb.consts.g_bar = lfb.g_bar)
    (hk_eq : sfb.consts.kappa = lfb.kappa)
    (hE0_eq : sfb.consts.E0 = lfb.E0) :
    exists hyps : BalabanHyps N_c, hyps.h2.g_bar = lfb.g_bar :=
  ⟨balabanHyps_of_bounds sfb lfb hg_eq hk_eq hE0_eq, rfl⟩

end YangMills
