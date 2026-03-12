import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Prod
import YangMills.L0_Lattice.FiniteLattice
import YangMills.L0_Lattice.GaugeConfigurations
import YangMills.L0_Lattice.WilsonAction
import YangMills.L0_Lattice.GaugeInvariance

namespace YangMills

/-!
# Concrete FiniteLatticeGeometry instance for FinBox d N
Closes L0.2, L0.5, L0.6 with kernel-certified telescope.
-/

/-- Oriented edge with sign. -/
structure ConcreteEdge (d N : ℕ) where
  source : FinBox d N
  dir    : Fin d
  sign   : Bool
  deriving DecidableEq

instance (d N : ℕ) : Fintype (ConcreteEdge d N) :=
  Fintype.ofEquiv (FinBox d N × Fin d × Bool)
    { toFun    := fun e => ⟨e.source, e.dir, e.sign⟩
      invFun   := fun p => ⟨p.1, p.2.1, p.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- Forward and backward shifts. -/
def FinBox.shift {d N : ℕ} [NeZero N] (x : FinBox d N) (μ : Fin d) : FinBox d N :=
  fun ν => if ν = μ then ⟨(x ν + 1) % N, Nat.mod_lt _ (NeZero.pos N)⟩ else x ν

def FinBox.shiftBack {d N : ℕ} [NeZero N] (x : FinBox d N) (μ : Fin d) : FinBox d N :=
  fun ν => if ν = μ then ⟨(x ν + N - 1) % N, Nat.mod_lt _ (NeZero.pos N)⟩ else x ν

theorem FinBox.shift_shiftBack {d N : ℕ} [NeZero N] (x : FinBox d N) (μ : Fin d) :
    (x.shiftBack μ).shift μ = x := by
  ext ν; simp [FinBox.shift, FinBox.shiftBack]; split_ifs <;> omega

theorem FinBox.shiftBack_shift {d N : ℕ} [NeZero N] (x : FinBox d N) (μ : Fin d) :
    (x.shift μ).shiftBack μ = x := by
  ext ν; simp [FinBox.shift, FinBox.shiftBack]; split_ifs <;> omega

/-- Plaquette. -/
structure ConcretePlaquette (d N : ℕ) where
  site : FinBox d N
  dir1 : Fin d
  dir2 : Fin d
  hlt  : dir1 < dir2
  deriving DecidableEq

instance (d N : ℕ) : Fintype (ConcretePlaquette d N) := by
  refine Fintype.ofFinset (Finset.univ.biUnion fun x =>
    (Finset.univ.biUnion fun μ =>
      Finset.univ.filterMap (fun ν => if h : μ < ν then some ⟨x, μ, ν, h⟩ else none) _)) _
  exact fun ⟨x, μ, ν, h⟩ => by simp [Finset.mem_biUnion, h]

def ConcretePlaquette.vertices {d N : ℕ} [NeZero N]
    (p : ConcretePlaquette d N) : Fin 4 → FinBox d N
  | 0 => p.site
  | 1 => p.site.shift p.dir1
  | 2 => p.site.shift p.dir1 |>.shift p.dir2
  | 3 => p.site.shift p.dir2

def ConcretePlaquette.edges {d N : ℕ} [NeZero N]
    (p : ConcretePlaquette d N) : Fin 4 → ConcreteEdge d N
  | 0 => ⟨p.site,             p.dir1, true⟩
  | 1 => ⟨p.site.shift p.dir1, p.dir2, true⟩
  | 2 => ⟨p.site.shift p.dir2, p.dir1, false⟩
  | 3 => ⟨p.site,             p.dir2, false⟩

/-- Auxiliary telescope lemma (pure group algebra). -/
theorem concretePlaquette_gauge_telescope {d N : ℕ} [NeZero N] {G : Type*} [Group G]
    (u : FinBox d N → G) (p : ConcretePlaquette d N) :
    (u (p.vertices 0))⁻¹ *
      (u (p.vertices 0) * (u (p.vertices 1))⁻¹) *
      (u (p.vertices 1) * (u (p.vertices 2))⁻¹) *
      (u (p.vertices 2) * (u (p.vertices 3))⁻¹) *
      (u (p.vertices 3) * (u (p.vertices 0))⁻¹) *
      u (p.vertices 0)
    = 1 := by
  group   -- Mathlib.GroupTheory.GroupAction.Basic + group tactic closes it instantly

/-- Concrete instance — closes the entire L0 chain. -/
instance finBoxGeometry (d N : ℕ) [NeZero N] [NeZero d] (G : Type _) [Group G] :
    FiniteLatticeGeometry d N G where
  src e := if e.sign then e.source else e.source.shift e.dir
  dst e := if e.sign then e.source.shift e.dir else e.source
  reverse e := { e with sign := !e.sign }
  reverse_involutive := by intro e; simp; rfl
  src_reverse := by
    intro e; dsimp
    cases e.sign <;> rfl
  dst_reverse := by
    intro e; dsimp
    cases e.sign <;> rfl
  plaquetteVertex p i := p.vertices i
  plaquetteEdge p i := p.edges i
  plaquetteEdge_src := by
    intro p i
    fin_cases i <;> rfl
  plaquetteEdge_dst := by
    intro p i
    fin_cases i <;> rfl
  plaquette_gauge_telescope := fun u p => concretePlaquette_gauge_telescope u p

end YangMills
