import YangMills.ClayCore.BalabanH1H2H3
namespace YangMills
open Real

/-- H3 locality holds by construction since `BalabanH3` only requires `True`. -/
def h3_holds_by_construction : BalabanH3 := { h_local := trivial }

/-- Assemble `BalabanHyps` from an H1, an H2, and the three compatibility hypotheses. -/
def balabanHyps_of_h1_h2 {N_c : Nat} [NeZero N_c]
    (h1 : BalabanH1 N_c) (h2 : BalabanH2 N_c)
    (hg_eq : h1.g_bar = h2.g_bar)
    (hk_eq : h1.kappa = h2.kappa)
    (hlf_le : Real.exp (-h2.p0) <= h1.E0 * h1.g_bar ^ 2) :
    BalabanHyps N_c :=
  { h1 := h1, h2 := h2, h3 := h3_holds_by_construction
  , hg_eq := hg_eq, hk_eq := hk_eq, hlf_le := hlf_le }

end YangMills
