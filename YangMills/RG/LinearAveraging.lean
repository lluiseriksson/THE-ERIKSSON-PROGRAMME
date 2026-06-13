/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib
import YangMills.RG.BlockLattice
import YangMills.L0_Lattice.FiniteLatticeGeometryInstance

/-!
# The linear block-averaging operator Q (gauge-RG campaign, brick B3-linear)

`docs/BALABAN-RG-PLAN.md` B3 (linear / small-field part).  Bałaban's
renormalization group is built on an averaging operation; for the
Gaussian (abelian / small-field) prototype it is the LINEAR operator
`Q`, and the full non-abelian averaging `Ū` is its exponential lift.

**Source.** T. Bałaban, *Propagators and Renormalization Transformations
for Lattice Gauge Theories. I*, Commun. Math. Phys. **95** (1984) 17–40,
equations (1.6)–(1.8): on the block `B(y) = {x : yμ ≤ xμ < yμ + L}`, the
averaging of an additive bond field `A` is
`B_c = L^{-d} Σ_{x ∈ B(c₋)} A(Γ_{c,x})`, where `A(Γ) = Σ_{b∈Γ} A_b` is
the line integral and `Γ_{c,x}` is the length-`L` straight path in the
bond direction starting at `x`.  This is the small-field linearisation
of the non-abelian averaging operator of CMP 98 eqs (14)–(15)
(`log Ū(e^{iA}) = QA + O(‖A‖²)`).

**Strategy / framing.** Lluis Eriksson, *The Balaban–Dimock Structural
Package* (ai.viXra:2602.0069); *Exponential Clustering and Mass Gap …
via Balaban's Renormalization Group* (ai.viXra:2602.0088).

`Q` acts on additive bond fields valued in any real vector space `V`
(the Lie algebra in the gauge application).  This brick: the definition
and its **linearity** — the defining algebraic property, reused wherever
`Q` appears.  Oracle target: `[propext, Classical.choice, Quot.sound]`.
No sorry, no axioms.
-/

namespace YangMills.RG

variable {d : ℕ}

/-- `NeZero` propagates through the block product `L · N'`. -/
instance instNeZeroBlockMul (L N' : ℕ) [NeZero L] [NeZero N'] :
    NeZero (L * N') :=
  ⟨Nat.mul_ne_zero (NeZero.ne L) (NeZero.ne N')⟩

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The **fine-lattice line integral** `A(Γ_{c,x})` (Bałaban CMP 95
eq (1.7)–(1.8)): the sum of the additive bond field `A` over the
length-`L` straight fine path in direction `μ` starting at fine site
`x` — the `L` positively-oriented fine bonds
`⟨shiftᵏ x, μ, +⟩`, `k = 0,…,L-1`. -/
def fineLineSum (L N' : ℕ) [NeZero L] [NeZero N']
    (A : ConcreteEdge d (L * N') → V) (μ : Fin d)
    (x : FinBox d (L * N')) : V :=
  ∑ k ∈ Finset.range L,
    A ⟨(fun y => FinBox.shift y μ)^[k] x, μ, true⟩

open scoped Classical in
/-- **The linear block-averaging operator `Q`** (Bałaban CMP 95
eq (1.8)): the `L^{-d}`-normalised average over the source block of the
fine line integral in the coarse bond's direction. -/
noncomputable def linAvg (L N' : ℕ) [NeZero L] [NeZero N']
    (A : ConcreteEdge d (L * N') → V) (c : ConcreteEdge d N') : V :=
  (L ^ d : ℝ)⁻¹ • ∑ x ∈ blockOf L N' c.source, fineLineSum L N' A c.dir x

theorem fineLineSum_add (L N' : ℕ) [NeZero L] [NeZero N']
    (A A' : ConcreteEdge d (L * N') → V) (μ : Fin d)
    (x : FinBox d (L * N')) :
    fineLineSum L N' (A + A') μ x
      = fineLineSum L N' A μ x + fineLineSum L N' A' μ x := by
  simp only [fineLineSum, Pi.add_apply]
  rw [← Finset.sum_add_distrib]

open scoped Classical in
/-- **`Q` is additive** (Bałaban CMP 95: `Q` is the linear averaging). -/
theorem linAvg_add (L N' : ℕ) [NeZero L] [NeZero N']
    (A A' : ConcreteEdge d (L * N') → V) (c : ConcreteEdge d N') :
    linAvg L N' (A + A') c = linAvg L N' A c + linAvg L N' A' c := by
  simp only [linAvg]
  rw [Finset.sum_congr rfl fun x _ => fineLineSum_add L N' A A' c.dir x,
    Finset.sum_add_distrib, smul_add]

theorem fineLineSum_smul (L N' : ℕ) [NeZero L] [NeZero N']
    (r : ℝ) (A : ConcreteEdge d (L * N') → V) (μ : Fin d)
    (x : FinBox d (L * N')) :
    fineLineSum L N' (r • A) μ x = r • fineLineSum L N' A μ x := by
  simp only [fineLineSum, Pi.smul_apply, Finset.smul_sum]

open scoped Classical in
/-- **`Q` is homogeneous** (Bałaban CMP 95: `Q` is the linear averaging). -/
theorem linAvg_smul (L N' : ℕ) [NeZero L] [NeZero N']
    (r : ℝ) (A : ConcreteEdge d (L * N') → V) (c : ConcreteEdge d N') :
    linAvg L N' (r • A) c = r • linAvg L N' A c := by
  simp only [linAvg]
  rw [Finset.sum_congr rfl fun x _ => fineLineSum_smul L N' r A c.dir x,
    ← Finset.smul_sum, smul_comm]

/-- **The fine line integral is local** (Bałaban CMP 95: `A(Γ_{c,x})`
reads only the bonds on its straight path): if two bond fields agree on
the `L` positively-oriented bonds of the length-`L` line in direction
`μ` from `x`, their line integrals agree. -/
theorem fineLineSum_congr (L N' : ℕ) [NeZero L] [NeZero N']
    (A A' : ConcreteEdge d (L * N') → V) (μ : Fin d) (x : FinBox d (L * N'))
    (h : ∀ k < L,
      A ⟨(fun y => FinBox.shift y μ)^[k] x, μ, true⟩
        = A' ⟨(fun y => FinBox.shift y μ)^[k] x, μ, true⟩) :
    fineLineSum L N' A μ x = fineLineSum L N' A' μ x := by
  refine Finset.sum_congr rfl fun k hk => ?_
  exact h k (Finset.mem_range.mp hk)

open scoped Classical in
/-- **The linear averaging operator `Q` is LOCAL** (the locality the
renormalization-group cluster expansion relies on, Bałaban CMP 116):
`linAvg A c` depends only on the values of `A` on the fine bonds
`⟨shiftᵏ x, c.dir, +⟩` (`x ∈` the source block of `c`, `k < L`) — i.e.
on the fine links inside the coarse bond's block.  If two bond fields
agree on those bonds, their averages at `c` agree. -/
theorem linAvg_congr (L N' : ℕ) [NeZero L] [NeZero N']
    (A A' : ConcreteEdge d (L * N') → V) (c : ConcreteEdge d N')
    (h : ∀ x ∈ blockOf L N' c.source, ∀ k < L,
      A ⟨(fun y => FinBox.shift y c.dir)^[k] x, c.dir, true⟩
        = A' ⟨(fun y => FinBox.shift y c.dir)^[k] x, c.dir, true⟩) :
    linAvg L N' A c = linAvg L N' A' c := by
  simp only [linAvg]
  refine congrArg _ (Finset.sum_congr rfl fun x hx => ?_)
  exact fineLineSum_congr L N' A A' c.dir x (h x hx)

end YangMills.RG
