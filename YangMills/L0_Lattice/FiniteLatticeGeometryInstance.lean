import Mathlib
import YangMills.L0_Lattice.FiniteLattice
import YangMills.L0_Lattice.GaugeConfigurations
import YangMills.L0_Lattice.WilsonAction
import YangMills.L0_Lattice.GaugeInvariance

namespace YangMills

private lemma shift_shiftBack_lem (k N : ℕ) (hN : 0 < N) (hk : k < N) :
    ((k + N - 1) % N + 1) % N = k := by
  obtain rfl | hk0 := Nat.eq_zero_or_pos k
  · rw [Nat.zero_add, Nat.mod_eq_of_lt (by omega : N - 1 < N)]
    rw [show N - 1 + 1 = N from by omega, Nat.mod_self]
  · rw [show k + N - 1 = (k - 1) + N from by omega]
    rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : k - 1 < N)]
    rw [show k - 1 + 1 = k from by omega, Nat.mod_eq_of_lt hk]

private lemma shiftBack_shift_lem (k N : ℕ) (hN : 0 < N) (hk : k < N) :
    ((k + 1) % N + N - 1) % N = k := by
  by_cases hk2 : k + 1 = N
  · rw [hk2, Nat.mod_self, Nat.zero_add]
    rw [Nat.mod_eq_of_lt (by omega : N - 1 < N)]; omega
  · rw [Nat.mod_eq_of_lt (by omega : k + 1 < N)]
    rw [show k + 1 + N - 1 = k + N from by omega]
    rw [Nat.add_mod_right, Nat.mod_eq_of_lt hk]

structure ConcreteEdge (d N : ℕ) where
  source : FinBox d N
  dir    : Fin d
  sign   : Bool
  deriving DecidableEq

instance instFintypeConcreteEdge (d N : ℕ) : Fintype (ConcreteEdge d N) :=
  Fintype.ofEquiv (FinBox d N × Fin d × Bool)
    { toFun    := fun ⟨s, mu, b⟩ => ⟨s, mu, b⟩
      invFun   := fun e => ⟨e.source, e.dir, e.sign⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

def FinBox.shift {d N : ℕ} [NeZero N] (x : FinBox d N) (i : Fin d) : FinBox d N :=
  fun j => if j = i then ⟨(x i + 1) % N, Nat.mod_lt _ (NeZero.pos N)⟩ else x j

def FinBox.shiftBack {d N : ℕ} [NeZero N] (x : FinBox d N) (i : Fin d) : FinBox d N :=
  fun j => if j = i then ⟨(x i + N - 1) % N, Nat.mod_lt _ (NeZero.pos N)⟩ else x j

theorem FinBox.shift_shiftBack {d N : ℕ} [NeZero N] (x : FinBox d N) (i : Fin d) :
    (x.shiftBack i).shift i = x := by
  funext j; simp only [FinBox.shift, FinBox.shiftBack]
  by_cases h : j = i
  · simp only [h, ite_true]
    exact Fin.ext (shift_shiftBack_lem (x i).val N (NeZero.pos N) (x i).isLt)
  · simp only [h, ite_false]

theorem FinBox.shiftBack_shift {d N : ℕ} [NeZero N] (x : FinBox d N) (i : Fin d) :
    (x.shift i).shiftBack i = x := by
  funext j; simp only [FinBox.shift, FinBox.shiftBack]
  by_cases h : j = i
  · simp only [h, ite_true]
    exact Fin.ext (shiftBack_shift_lem (x i).val N (NeZero.pos N) (x i).isLt)
  · simp only [h, ite_false]

theorem FinBox.shift_comm {d N : ℕ} [NeZero N] (x : FinBox d N)
    (i j : Fin d) (h : i ≠ j) :
    (x.shift i).shift j = (x.shift j).shift i := by
  funext k; simp only [FinBox.shift]
  by_cases hk1 : k = j <;> by_cases hk2 : k = i <;> simp_all

theorem FinBox.shift_bijective {d N : ℕ} [NeZero N] (i : Fin d) :
    Function.Bijective (fun x : FinBox d N => x.shift i) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨fun x : FinBox d N => x.shiftBack i,
      fun x => FinBox.shiftBack_shift x i,
      fun x => FinBox.shift_shiftBack x i⟩

theorem FinBox.shiftBack_bijective {d N : ℕ} [NeZero N] (i : Fin d) :
    Function.Bijective (fun x : FinBox d N => x.shiftBack i) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨fun x : FinBox d N => x.shift i,
      fun x => FinBox.shift_shiftBack x i,
      fun x => FinBox.shiftBack_shift x i⟩

theorem FinBox.sum_shift {d N : ℕ} [NeZero N]
    {M : Type*} [AddCommMonoid M]
    (f : FinBox d N → M) (i : Fin d) :
    (∑ x : FinBox d N, f (x.shift i)) = ∑ x, f x :=
  (FinBox.shift_bijective i).sum_comp f

theorem FinBox.sum_shiftBack {d N : ℕ} [NeZero N]
    {M : Type*} [AddCommMonoid M]
    (f : FinBox d N → M) (i : Fin d) :
    (∑ x : FinBox d N, f (x.shiftBack i)) = ∑ x, f x :=
  (FinBox.shiftBack_bijective i).sum_comp f

theorem FinBox.shift_shiftBack_comm {d N : ℕ} [NeZero N]
    (x : FinBox d N) (i j : Fin d) :
    (x.shift i).shiftBack j = (x.shiftBack j).shift i := by
  by_cases hij : i = j
  · subst j
    rw [FinBox.shiftBack_shift, FinBox.shift_shiftBack]
  · funext k
    simp only [FinBox.shift, FinBox.shiftBack]
    by_cases hki : k = i <;>
      by_cases hkj : k = j <;>
      simp_all

/-- Iterating a positive shift advances the shifted coordinate modulo the
periodic side length. -/
theorem FinBox.iter_shift_apply_self {d N : ℕ} [NeZero N]
    (x : FinBox d N) (i : Fin d) (k : ℕ) :
    (((fun y : FinBox d N => y.shift i)^[k] x) i).val =
      ((x i).val + k) % N := by
  induction k with
  | zero =>
      simp [Nat.mod_eq_of_lt (x i).isLt]
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      have hstep :
          ((((fun y : FinBox d N => y.shift i)^[k] x).shift i) i).val =
            (((((fun y : FinBox d N => y.shift i)^[k] x) i).val + 1) % N) := by
        simp [FinBox.shift]
      rw [hstep, ih, Nat.mod_add_mod, Nat.add_assoc]

/-- Iterating a positive shift leaves all other coordinates fixed. -/
theorem FinBox.iter_shift_apply_ne {d N : ℕ} [NeZero N]
    (x : FinBox d N) (i : Fin d) (k : ℕ) {j : Fin d} (h : j ≠ i) :
    ((fun y : FinBox d N => y.shift i)^[k] x) j = x j := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      show (((fun y : FinBox d N => y.shift i)^[k] x).shift i) j = _
      rw [FinBox.shift, if_neg h, ih]

/-- A function on a periodic box that is invariant under every positive
coordinate shift is constant on the whole torus. -/
theorem FinBox.eq_default_of_shift_invariant {d N : ℕ} [NeZero N]
    {α : Type*} (f : FinBox d N → α)
    (hshift : ∀ (x : FinBox d N) (i : Fin d), f (x.shift i) = f x) :
    ∀ x : FinBox d N, f x = f (default : FinBox d N) := by
  intro x
  let setCoords : Finset (Fin d) → FinBox d N :=
    fun S j => if j ∈ S then x j else (default : FinBox d N) j
  have hstep : ∀ (S : Finset (Fin d)) (i : Fin d), i ∉ S →
      f (setCoords (insert i S)) = f (setCoords S) := by
    intro S i hiS
    let y : FinBox d N := setCoords S
    have hiter : ∀ k : ℕ,
        f (((fun z : FinBox d N => z.shift i)^[k] y)) = f y := by
      intro k
      induction k with
      | zero =>
          simp
      | succ k ih =>
          rw [Function.iterate_succ_apply']
          rw [hshift]
          exact ih
    have htarget :
        ((fun z : FinBox d N => z.shift i)^[(x i).val] y) =
          setCoords (insert i S) := by
      funext j
      by_cases hji : j = i
      · subst j
        rw [show setCoords (insert i S) i = x i by simp [setCoords]]
        apply Fin.ext
        change ((((fun z : FinBox d N => z.shift i)^[(x i).val] y) i).val =
          (x i).val)
        rw [FinBox.iter_shift_apply_self]
        have hyi : (y i).val = 0 := by
          simp only [y, setCoords, if_neg hiS]
          rfl
        rw [hyi, Nat.zero_add]
        exact Nat.mod_eq_of_lt (x i).isLt
      · rw [FinBox.iter_shift_apply_ne _ _ _ hji]
        simp [y, setCoords, hji]
    rw [← htarget]
    exact hiter (x i).val
  have hconst : ∀ S : Finset (Fin d), f (setCoords S) = f (default : FinBox d N) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
        simp [setCoords]
    | insert i S hiS ih =>
        calc
          f (setCoords (insert i S)) = f (setCoords S) := hstep S i hiS
          _ = f (default : FinBox d N) := ih
  simpa [setCoords] using hconst Finset.univ

structure ConcretePlaquette (d N : ℕ) where
  site : FinBox d N
  dir1 : Fin d
  dir2 : Fin d
  hlt  : dir1 < dir2
  deriving DecidableEq

instance instFintypeConcretePlaquette (d N : ℕ) : Fintype (ConcretePlaquette d N) where
  elems := Finset.univ.biUnion fun x =>
    Finset.univ.biUnion fun i : Fin d =>
      Finset.univ.biUnion fun j : Fin d =>
        if h : i < j then ({⟨x, i, j, h⟩} : Finset (ConcretePlaquette d N)) else ∅
  complete := fun ⟨x, i, j, h⟩ => by
    apply Finset.mem_biUnion.mpr
    exact ⟨x, Finset.mem_univ _, Finset.mem_biUnion.mpr
      ⟨i, Finset.mem_univ _, Finset.mem_biUnion.mpr
        ⟨j, Finset.mem_univ _, by simp [h]⟩⟩⟩

def ConcretePlaquette.vertices {d N : ℕ} [NeZero N]
    (p : ConcretePlaquette d N) : Fin 4 → FinBox d N
  | ⟨0, _⟩ => p.site
  | ⟨1, _⟩ => p.site.shift p.dir1
  | ⟨2, _⟩ => (p.site.shift p.dir1).shift p.dir2
  | ⟨3, _⟩ => p.site.shift p.dir2

def ConcretePlaquette.edges {d N : ℕ} [NeZero N]
    (p : ConcretePlaquette d N) : Fin 4 → ConcreteEdge d N
  | ⟨0, _⟩ => ⟨p.site,              p.dir1, true⟩
  | ⟨1, _⟩ => ⟨p.site.shift p.dir1, p.dir2, true⟩
  | ⟨2, _⟩ => ⟨p.site.shift p.dir2, p.dir1, false⟩
  | ⟨3, _⟩ => ⟨p.site,              p.dir2, false⟩

theorem concretePlaquette_gauge_telescope {d N : ℕ} [NeZero N] {G : Type*} [Group G]
    (u : FinBox d N → G) (p : ConcretePlaquette d N) :
    (u (p.vertices 0))⁻¹ *
      (u (p.vertices 0) * (u (p.vertices 1))⁻¹) *
      (u (p.vertices 1) * (u (p.vertices 2))⁻¹) *
      (u (p.vertices 2) * (u (p.vertices 3))⁻¹) *
      (u (p.vertices 3) * (u (p.vertices 0))⁻¹) *
      u (p.vertices 0) = 1 := by group

def ConcreteEdge.srcV {d N : ℕ} [NeZero N] (e : ConcreteEdge d N) : FinBox d N :=
  if e.sign then e.source else e.source.shift e.dir

def ConcreteEdge.dstV {d N : ℕ} [NeZero N] (e : ConcreteEdge d N) : FinBox d N :=
  if e.sign then e.source.shift e.dir else e.source

instance finBoxGeometry (d N : ℕ) [NeZero N] [NeZero d] (G : Type*) [Group G] :
    FiniteLatticeGeometry d N G where
  E := ConcreteEdge d N
  P := ConcretePlaquette d N
  fintypeE := instFintypeConcreteEdge d N
  fintypeP := instFintypeConcretePlaquette d N
  src e := e.srcV
  dst e := e.dstV
  reverse e := { e with sign := !e.sign }
  reverse_involutive e := by simp [Bool.not_not]
  src_reverse e := by simp only [ConcreteEdge.srcV, ConcreteEdge.dstV]; cases e.sign <;> rfl
  dst_reverse e := by simp only [ConcreteEdge.srcV, ConcreteEdge.dstV]; cases e.sign <;> rfl
  plaquetteVertex p i := p.vertices i
  plaquetteEdge p i := p.edges i
  plaquetteEdge_src p i := by
    fin_cases i
    · simp [ConcretePlaquette.edges, ConcretePlaquette.vertices, ConcreteEdge.srcV]
    · simp [ConcretePlaquette.edges, ConcretePlaquette.vertices, ConcreteEdge.srcV]
    · simpa [ConcretePlaquette.edges, ConcretePlaquette.vertices, ConcreteEdge.srcV]
        using (FinBox.shift_comm p.site p.dir1 p.dir2 (Fin.ne_of_lt p.hlt)).symm
    · simp [ConcretePlaquette.edges, ConcretePlaquette.vertices, ConcreteEdge.srcV]
  plaquetteEdge_dst p i := by
    fin_cases i <;>
      simp [ConcretePlaquette.edges, ConcretePlaquette.vertices, ConcreteEdge.dstV, succ4]
  plaquette_gauge_telescope u p := concretePlaquette_gauge_telescope u p

end YangMills
