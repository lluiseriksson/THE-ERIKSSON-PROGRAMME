import Mathlib
import YangMills.L0_Lattice.WilsonAction
import YangMills.RG.PhysicalGaugeCochains

/-!
# Literal two-parameter Wilson variations on physical positive bonds

This is the axiom-free starting point of the CMP116 interacting-Hessian
campaign.  It constructs an honest group-valued gauge configuration for every
pair of real parameters, starting from one independent group coordinate per
positively oriented physical bond.  Reversed edges are reconstructed by
inversion, so the defining `GaugeConfig` orientation law holds by construction.

The mixed Wilson variation is then the literal iterated derivative

`∂ₜ ∂ₛ S_W(U(t,s)) |_(0,0)`.

No Hessian matrix, kernel estimate, random-walk expansion, or exponential chart
is postulated here.  In particular, this module does not import the experimental
`LieSUN` files, whose current `SU(N)` exponential path uses a local axiom for
`det (exp X) = exp (trace X)`.
-/

namespace YangMills.RG

open scoped BigOperators

noncomputable section

variable {d N : ℕ} [NeZero d] [NeZero N]
variable {G : Type*} [Group G]

/-- The positively oriented concrete edge represented by a physical bond. -/
def positiveEdgeOfPhysicalBond (b : PhysicalBond d N) : ConcreteEdge d N :=
  ConcreteEdge.mk b.1 b.2 true

omit [NeZero d] in
@[simp]
theorem physicalBondOfEdge_positiveEdgeOfPhysicalBond (b : PhysicalBond d N) :
    physicalBondOfEdge (positiveEdgeOfPhysicalBond b) = b := by
  cases b
  rfl

/-- Reconstruct an oriented gauge configuration from one group element per
positive physical bond.  Negative orientations are not independent data. -/
def gaugeConfigOfPositiveBonds (V : PhysicalBond d N → G) : GaugeConfig d N G where
  toFun := fun e =>
    if e.sign then V (physicalBondOfEdge e) else (V (physicalBondOfEdge e))⁻¹
  map_reverse := by
    intro e
    cases e with
    | mk x i sign =>
        change
          (if !sign then V (x, i) else (V (x, i))⁻¹) =
            (if sign then V (x, i) else (V (x, i))⁻¹)⁻¹
        cases sign <;> simp

/-- Extensionality for physical gauge configurations. -/
theorem gaugeConfig_ext {A B : GaugeConfig d N G}
    (h : ∀ e, A e = B e) : A = B := by
  cases A with
  | mk f hf =>
      cases B with
      | mk g hg =>
          have hfg : f = g := funext h
          subst g
          rfl

@[simp]
theorem gaugeConfigOfPositiveBonds_apply_pos
    (V : PhysicalBond d N → G) (b : PhysicalBond d N) :
    gaugeConfigOfPositiveBonds V (positiveEdgeOfPhysicalBond b) = V b := by
  cases b
  simp [gaugeConfigOfPositiveBonds, positiveEdgeOfPhysicalBond, physicalBondOfEdge]

@[simp]
theorem gaugeConfigOfPositiveBonds_apply_neg
    (V : PhysicalBond d N → G) (x : FinBox d N) (i : Fin d) :
    gaugeConfigOfPositiveBonds V (ConcreteEdge.mk x i false) = (V (x, i))⁻¹ := by
  simp [gaugeConfigOfPositiveBonds, physicalBondOfEdge]

/-- A two-parameter left variation of a physical background.  The increment is
specified only on positive bonds.  This fixes the convention

`U_b(t,s) = increment b t s * U_b`

and reconstructs every reversed edge from the inverse positive edge. -/
def physicalLeftVariation
    (U : GaugeConfig d N G)
    (increment : PhysicalBond d N → ℝ → ℝ → G)
    (t s : ℝ) : GaugeConfig d N G :=
  gaugeConfigOfPositiveBonds fun b =>
    increment b t s * U (positiveEdgeOfPhysicalBond b)

@[simp]
theorem physicalLeftVariation_apply_pos
    (U : GaugeConfig d N G)
    (increment : PhysicalBond d N → ℝ → ℝ → G)
    (b : PhysicalBond d N) (t s : ℝ) :
    physicalLeftVariation U increment t s (positiveEdgeOfPhysicalBond b) =
      increment b t s * U (positiveEdgeOfPhysicalBond b) := by
  simp [physicalLeftVariation]

theorem physicalLeftVariation_apply_neg
    (U : GaugeConfig d N G)
    (increment : PhysicalBond d N → ℝ → ℝ → G)
    (x : FinBox d N) (i : Fin d) (t s : ℝ) :
    physicalLeftVariation U increment t s (ConcreteEdge.mk x i false) =
      (increment (x, i) t s * U (ConcreteEdge.mk x i true))⁻¹ := by
  simp [physicalLeftVariation, positiveEdgeOfPhysicalBond]

/-- If every increment is the identity at the origin, the two-parameter
variation passes exactly through the supplied physical background. -/
theorem physicalLeftVariation_zero_zero
    (U : GaugeConfig d N G)
    (increment : PhysicalBond d N → ℝ → ℝ → G)
    (hzero : ∀ b, increment b 0 0 = 1) :
    physicalLeftVariation U increment 0 0 = U := by
  apply gaugeConfig_ext
  intro e
  cases e with
  | mk x i sign =>
      cases sign
      · rw [physicalLeftVariation_apply_neg, hzero, one_mul]
        have hU := U.map_reverse (ConcreteEdge.mk x i true)
        change U (ConcreteEdge.mk x i false) =
          (U (ConcreteEdge.mk x i true))⁻¹ at hU
        exact hU.symm
      · change increment (x, i) 0 0 * U (ConcreteEdge.mk x i true) =
          U (ConcreteEdge.mk x i true)
        rw [hzero, one_mul]

/-- The physical positive-bond support of one oriented plaquette. -/
def plaquettePhysicalBondSupport (p : ConcretePlaquette d N) :
    Finset (PhysicalBond d N) :=
  Finset.univ.image fun k : Fin 4 => physicalBondOfEdge (p.edges k)

omit [NeZero d] in
theorem physicalBondOfEdge_mem_plaquettePhysicalBondSupport
    (p : ConcretePlaquette d N) (k : Fin 4) :
    physicalBondOfEdge (p.edges k) ∈ plaquettePhysicalBondSupport p := by
  exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩

/-- If the increment is the identity on the four physical bonds of a
plaquette, every oriented edge value on that plaquette is unchanged. -/
theorem physicalLeftVariation_plaquetteEdge_eq_of_one
    (U : GaugeConfig d N G)
    (increment : PhysicalBond d N → ℝ → ℝ → G)
    (p : ConcretePlaquette d N) (t s : ℝ)
    (hone : ∀ b ∈ plaquettePhysicalBondSupport p, increment b t s = 1)
    (k : Fin 4) :
    physicalLeftVariation U increment t s (p.edges k) = U (p.edges k) := by
  have hk := hone (physicalBondOfEdge (p.edges k))
    (physicalBondOfEdge_mem_plaquettePhysicalBondSupport p k)
  generalize he : p.edges k = e at hk ⊢
  cases e with
  | mk x i sign =>
      cases sign
      · change increment (x, i) t s = 1 at hk
        rw [physicalLeftVariation_apply_neg, hk, one_mul]
        have hU := U.map_reverse (ConcreteEdge.mk x i true)
        change U (ConcreteEdge.mk x i false) =
          (U (ConcreteEdge.mk x i true))⁻¹ at hU
        exact hU.symm
      · change increment (x, i) t s = 1 at hk
        change increment (x, i) t s * U (ConcreteEdge.mk x i true) =
          U (ConcreteEdge.mk x i true)
        rw [hk, one_mul]

/-- Two physical left variations agree on an oriented plaquette edge whenever
their positive-bond increments agree on that plaquette's support. -/
theorem physicalLeftVariation_plaquetteEdge_eq_of_eqOn
    (U : GaugeConfig d N G)
    (increment increment' : PhysicalBond d N → ℝ → ℝ → G)
    (p : ConcretePlaquette d N) (t s t' s' : ℝ)
    (heq : ∀ b ∈ plaquettePhysicalBondSupport p,
      increment b t s = increment' b t' s')
    (k : Fin 4) :
    physicalLeftVariation U increment t s (p.edges k) =
      physicalLeftVariation U increment' t' s' (p.edges k) := by
  have hk := heq (physicalBondOfEdge (p.edges k))
    (physicalBondOfEdge_mem_plaquettePhysicalBondSupport p k)
  generalize hedge : p.edges k = e at hk ⊢
  cases e with
  | mk x i sign =>
      cases sign
      · change increment (x, i) t s = increment' (x, i) t' s' at hk
        rw [physicalLeftVariation_apply_neg,
          physicalLeftVariation_apply_neg, hk]
      · change increment (x, i) t s = increment' (x, i) t' s' at hk
        change increment (x, i) t s * U (ConcreteEdge.mk x i true) =
          increment' (x, i) t' s' * U (ConcreteEdge.mk x i true)
        rw [hk]

/-- Plaquette holonomy is unchanged when the increment is the identity on the
plaquette's physical bond support. -/
theorem plaquetteHolonomy_physicalLeftVariation_eq_of_one
    (U : GaugeConfig d N G)
    (increment : PhysicalBond d N → ℝ → ℝ → G)
    (p : ConcretePlaquette d N) (t s : ℝ)
    (hone : ∀ b ∈ plaquettePhysicalBondSupport p, increment b t s = 1) :
    GaugeConfig.plaquetteHolonomy (physicalLeftVariation U increment t s) p =
      GaugeConfig.plaquetteHolonomy U p := by
  simp only [GaugeConfig.plaquetteHolonomy]
  change
    physicalLeftVariation U increment t s (p.edges 0) *
          physicalLeftVariation U increment t s (p.edges 1) *
        physicalLeftVariation U increment t s (p.edges 2) *
      physicalLeftVariation U increment t s (p.edges 3) =
    U (p.edges 0) * U (p.edges 1) * U (p.edges 2) * U (p.edges 3)
  rw [physicalLeftVariation_plaquetteEdge_eq_of_one U increment p t s hone 0,
    physicalLeftVariation_plaquetteEdge_eq_of_one U increment p t s hone 1,
    physicalLeftVariation_plaquetteEdge_eq_of_one U increment p t s hone 2,
    physicalLeftVariation_plaquetteEdge_eq_of_one U increment p t s hone 3]

/-- Plaquette holonomies depend only on the increments on the four physical
bonds supporting that plaquette. -/
theorem plaquetteHolonomy_physicalLeftVariation_eq_of_eqOn
    (U : GaugeConfig d N G)
    (increment increment' : PhysicalBond d N → ℝ → ℝ → G)
    (p : ConcretePlaquette d N) (t s t' s' : ℝ)
    (heq : ∀ b ∈ plaquettePhysicalBondSupport p,
      increment b t s = increment' b t' s') :
    GaugeConfig.plaquetteHolonomy (physicalLeftVariation U increment t s) p =
      GaugeConfig.plaquetteHolonomy (physicalLeftVariation U increment' t' s') p := by
  simp only [GaugeConfig.plaquetteHolonomy]
  change
    physicalLeftVariation U increment t s (p.edges 0) *
          physicalLeftVariation U increment t s (p.edges 1) *
        physicalLeftVariation U increment t s (p.edges 2) *
      physicalLeftVariation U increment t s (p.edges 3) =
    physicalLeftVariation U increment' t' s' (p.edges 0) *
          physicalLeftVariation U increment' t' s' (p.edges 1) *
        physicalLeftVariation U increment' t' s' (p.edges 2) *
      physicalLeftVariation U increment' t' s' (p.edges 3)
  rw [physicalLeftVariation_plaquetteEdge_eq_of_eqOn
      U increment increment' p t s t' s' heq 0,
    physicalLeftVariation_plaquetteEdge_eq_of_eqOn
      U increment increment' p t s t' s' heq 1,
    physicalLeftVariation_plaquetteEdge_eq_of_eqOn
      U increment increment' p t s t' s' heq 2,
    physicalLeftVariation_plaquetteEdge_eq_of_eqOn
      U increment increment' p t s t' s' heq 3]

/-- Local Wilson contribution of one plaquette along a two-parameter physical
variation. -/
def plaquetteWilsonVariation
    (plaquetteEnergy : G → ℝ)
    (U : GaugeConfig d N G)
    (increment : PhysicalBond d N → ℝ → ℝ → G)
    (p : ConcretePlaquette d N) (t s : ℝ) : ℝ :=
  plaquetteEnergy
    (GaugeConfig.plaquetteHolonomy (physicalLeftVariation U increment t s) p)

/-- Literal mixed second variation of one Wilson plaquette term. -/
def plaquetteWilsonMixedVariation
    (plaquetteEnergy : G → ℝ)
    (U : GaugeConfig d N G)
    (increment : PhysicalBond d N → ℝ → ℝ → G)
    (p : ConcretePlaquette d N) : ℝ :=
  deriv (fun t => deriv (fun s =>
    plaquetteWilsonVariation plaquetteEnergy U increment p t s) 0) 0

/-- Literal mixed second variation of the complete finite Wilson action. -/
def wilsonActionMixedVariation
    (plaquetteEnergy : G → ℝ)
    (U : GaugeConfig d N G)
    (increment : PhysicalBond d N → ℝ → ℝ → G) : ℝ :=
  deriv (fun t => deriv (fun s =>
    wilsonAction plaquetteEnergy (physicalLeftVariation U increment t s)) 0) 0

/-- Exact locality at the level preceding differentiation: increments supported
away from a plaquette leave its Wilson contribution constant. -/
theorem plaquetteWilsonVariation_eq_of_one_on_support
    (plaquetteEnergy : G → ℝ)
    (U : GaugeConfig d N G)
    (increment : PhysicalBond d N → ℝ → ℝ → G)
    (p : ConcretePlaquette d N)
    (hone : ∀ b ∈ plaquettePhysicalBondSupport p,
      ∀ t s, increment b t s = 1) (t s : ℝ) :
    plaquetteWilsonVariation plaquetteEnergy U increment p t s =
      plaquetteEnergy (GaugeConfig.plaquetteHolonomy U p) := by
  rw [plaquetteWilsonVariation,
    plaquetteHolonomy_physicalLeftVariation_eq_of_one U increment p t s]
  exact fun b hb => hone b hb t s

/-- A plaquette whose physical bond support misses the complete variation has
zero literal mixed second variation. -/
theorem plaquetteWilsonMixedVariation_eq_zero_of_one_on_support
    (plaquetteEnergy : G → ℝ)
    (U : GaugeConfig d N G)
    (increment : PhysicalBond d N → ℝ → ℝ → G)
    (p : ConcretePlaquette d N)
    (hone : ∀ b ∈ plaquettePhysicalBondSupport p,
      ∀ t s, increment b t s = 1) :
    plaquetteWilsonMixedVariation plaquetteEnergy U increment p = 0 := by
  simp only [plaquetteWilsonMixedVariation]
  have hfun :
      (fun t => deriv (fun s =>
        plaquetteWilsonVariation plaquetteEnergy U increment p t s) 0) =
        fun _ => 0 := by
    funext t
    have hs :
        (fun s => plaquetteWilsonVariation plaquetteEnergy U increment p t s) =
          fun _ => plaquetteEnergy (GaugeConfig.plaquetteHolonomy U p) := by
      funext s
      exact plaquetteWilsonVariation_eq_of_one_on_support
        plaquetteEnergy U increment p hone t s
    rw [hs]
    exact deriv_const 0 _
  rw [hfun]
  exact deriv_const 0 0

/-- If the increment restricted to a plaquette is independent of the first
parameter, then the plaquette's literal mixed variation vanishes.  This is the
first support-locality statement for the future Hessian kernel. -/
theorem plaquetteWilsonMixedVariation_eq_zero_of_t_independent_on_support
    (plaquetteEnergy : G → ℝ)
    (U : GaugeConfig d N G)
    (increment : PhysicalBond d N → ℝ → ℝ → G)
    (p : ConcretePlaquette d N)
    (ht : ∀ b ∈ plaquettePhysicalBondSupport p,
      ∀ t s, increment b t s = increment b 0 s) :
    plaquetteWilsonMixedVariation plaquetteEnergy U increment p = 0 := by
  simp only [plaquetteWilsonMixedVariation]
  have houter :
      (fun t => deriv (fun s =>
        plaquetteWilsonVariation plaquetteEnergy U increment p t s) 0) =
      fun _ => deriv (fun s =>
        plaquetteWilsonVariation plaquetteEnergy U increment p 0 s) 0 := by
    funext t
    congr 1
    funext s
    unfold plaquetteWilsonVariation
    rw [plaquetteHolonomy_physicalLeftVariation_eq_of_eqOn
      U increment increment p t s 0 s]
    exact fun b hb => ht b hb t s
  rw [houter]
  exact deriv_const 0 _

/-- If the increment restricted to a plaquette is independent of the second
parameter, then the plaquette's literal mixed variation vanishes. -/
theorem plaquetteWilsonMixedVariation_eq_zero_of_s_independent_on_support
    (plaquetteEnergy : G → ℝ)
    (U : GaugeConfig d N G)
    (increment : PhysicalBond d N → ℝ → ℝ → G)
    (p : ConcretePlaquette d N)
    (hs : ∀ b ∈ plaquettePhysicalBondSupport p,
      ∀ t s, increment b t s = increment b t 0) :
    plaquetteWilsonMixedVariation plaquetteEnergy U increment p = 0 := by
  simp only [plaquetteWilsonMixedVariation]
  have hinner :
      (fun t => deriv (fun s =>
        plaquetteWilsonVariation plaquetteEnergy U increment p t s) 0) =
      fun _ => 0 := by
    funext t
    have hcurve :
        (fun s => plaquetteWilsonVariation plaquetteEnergy U increment p t s) =
        fun _ => plaquetteWilsonVariation plaquetteEnergy U increment p t 0 := by
      funext s
      unfold plaquetteWilsonVariation
      rw [plaquetteHolonomy_physicalLeftVariation_eq_of_eqOn
        U increment increment p t s t 0]
      exact fun b hb => hs b hb t s
    rw [hcurve]
    exact deriv_const 0 _
  rw [hinner]
  exact deriv_const 0 0

end

end YangMills.RG
