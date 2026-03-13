import Mathlib
import YangMills.P2_MaxEntClustering.PetzFidelity
import YangMills.L0_Lattice.GaugeConfigurations
import YangMills.L0_Lattice.GaugeInvariance
import YangMills.L0_Lattice.FiniteLatticeGeometryInstance

namespace YangMills

/-! ## P2.2: Local gauge-invariant observable algebras

This file formalizes the algebraic quantum field theory (AQFT) interface
for the Yang-Mills lattice: local observables, gauge invariance, and
the isotone net of gauge-invariant local algebras.

The key objects are:
- `localAlgebra eval Λ` — real observables supported on finite region Λ
- `gaugeInvariantAlgebra` — observables invariant under all gauge transforms
- `localGaugeInvariantAlgebra eval Λ` — physical observables: local AND gauge-invariant
- `restrictState` — restriction of a state to a local algebra
- `AgreeOnLocalAlgebra` — two states agree on a region

This is the AQFT net of local algebras needed for P2.3 MaxEntStates
and the Fawzi-Renner clustering bridge P2.5.
-/

section LocalObservables

variable {d N : ℕ} [NeZero d] [NeZero N]
variable {G : Type*} [Group G] [FiniteLatticeGeometry d N G]
variable {E : Type*} (eval : GaugeConfig d N G → E → G)

/-- An observable is local in region Λ if it depends only on edge values in Λ. -/
def IsLocalObservable (Λ : Set E) (f : GaugeConfig d N G → ℝ) : Prop :=
  ∀ U V : GaugeConfig d N G, (∀ e ∈ Λ, eval U e = eval V e) → f U = f V

/-- The local algebra A(Λ): real-valued observables supported in region Λ. -/
def localAlgebra (Λ : Set E) : Subalgebra ℝ (GaugeConfig d N G → ℝ) where
  carrier := {f | IsLocalObservable eval Λ f}
  mul_mem' := fun hf hg U V h => by
    simp only [Pi.mul_apply]; rw [hf U V h, hg U V h]
  one_mem' := fun U V _ => rfl
  add_mem' := fun hf hg U V h => by
    simp only [Pi.add_apply]; rw [hf U V h, hg U V h]
  zero_mem' := fun U V _ => rfl
  algebraMap_mem' := fun r U V _ => rfl

/-- Isotony: if Λ₁ ⊆ Λ₂ then A(Λ₁) ⊆ A(Λ₂). -/
lemma localAlgebra_isotony {Λ₁ Λ₂ : Set E} (h : Λ₁ ⊆ Λ₂) :
    localAlgebra eval Λ₁ ≤ localAlgebra eval Λ₂ :=
  fun f hf U V hUV => hf U V (fun e he => hUV e (h he))

/-- The standard locality evaluator: edge values of a gauge configuration. -/
def stdEval : GaugeConfig d N G → FiniteLatticeGeometry.E d N G → G :=
  fun U e => U.toFun e

/-- Local algebra with standard edge evaluator. -/
def stdLocalAlgebra (Λ : Set (FiniteLatticeGeometry.E d N G)) :
    Subalgebra ℝ (GaugeConfig d N G → ℝ) :=
  localAlgebra stdEval Λ

end LocalObservables

section GaugeInvariantObservables

variable {d N : ℕ} [NeZero d] [NeZero N]
variable {G : Type*} [Group G] [FiniteLatticeGeometry d N G]
variable {E : Type*} (eval : GaugeConfig d N G → E → G)

/-- An observable is gauge-invariant if gauge transforms leave it unchanged. -/
def IsGaugeInvariantObs (f : GaugeConfig d N G → ℝ) : Prop :=
  ∀ (u : GaugeTransform d N G) (U : GaugeConfig d N G),
    f (GaugeConfig.gaugeAct u U) = f U

/-- The gauge-invariant subalgebra of all observables. -/
def gaugeInvariantAlgebra : Subalgebra ℝ (GaugeConfig d N G → ℝ) where
  carrier := {f | IsGaugeInvariantObs f}
  mul_mem' := fun hf hg u U => by simp only [Pi.mul_apply]; rw [hf u U, hg u U]
  one_mem' := fun u U => rfl
  add_mem' := fun hf hg u U => by simp only [Pi.add_apply]; rw [hf u U, hg u U]
  zero_mem' := fun u U => rfl
  algebraMap_mem' := fun r u U => rfl

/-- The physical algebra A_phys(Λ): local AND gauge-invariant observables. -/
def localGaugeInvariantAlgebra (Λ : Set E) :
    Subalgebra ℝ (GaugeConfig d N G → ℝ) where
  carrier := (localAlgebra eval Λ).carrier ∩ gaugeInvariantAlgebra.carrier
  mul_mem' := fun ⟨hl1, hg1⟩ ⟨hl2, hg2⟩ =>
    ⟨(localAlgebra eval Λ).mul_mem hl1 hl2, gaugeInvariantAlgebra.mul_mem hg1 hg2⟩
  one_mem' :=
    ⟨(localAlgebra eval Λ).one_mem, gaugeInvariantAlgebra.one_mem⟩
  add_mem' := fun ⟨hl1, hg1⟩ ⟨hl2, hg2⟩ =>
    ⟨(localAlgebra eval Λ).add_mem hl1 hl2, gaugeInvariantAlgebra.add_mem hg1 hg2⟩
  zero_mem' :=
    ⟨(localAlgebra eval Λ).zero_mem, gaugeInvariantAlgebra.zero_mem⟩
  algebraMap_mem' r :=
    ⟨(localAlgebra eval Λ).algebraMap_mem r, gaugeInvariantAlgebra.algebraMap_mem r⟩

/-- Isotony of the physical algebra. -/
lemma localGaugeInvariantAlgebra_isotony {Λ₁ Λ₂ : Set E} (h : Λ₁ ⊆ Λ₂) :
    localGaugeInvariantAlgebra eval Λ₁ ≤ localGaugeInvariantAlgebra eval Λ₂ :=
  fun f ⟨hloc, hgauge⟩ =>
    ⟨localAlgebra_isotony eval h hloc, hgauge⟩

/-- Every element of the physical algebra is gauge-invariant. -/
lemma localGaugeInvariantAlgebra_isGaugeInvariant (Λ : Set E)
    {f : GaugeConfig d N G → ℝ}
    (hf : f ∈ localGaugeInvariantAlgebra eval Λ) :
    IsGaugeInvariantObs f := hf.2

end GaugeInvariantObservables

section StateRestriction

variable {d N : ℕ} [NeZero d] [NeZero N]
variable {G : Type*} [Group G] [FiniteLatticeGeometry d N G]

/-- A real linear state on the observable algebra. -/
abbrev ObservableState := (GaugeConfig d N G → ℝ) →ₗ[ℝ] ℝ

/-- Restriction of a state to a local algebra. -/
noncomputable def restrictState
    (ω : ObservableState (d := d) (N := N) (G := G))
    (A : Subalgebra ℝ (GaugeConfig d N G → ℝ)) :
    A →ₗ[ℝ] ℝ :=
  ω.comp A.toSubmodule.subtype

/-- Two states agree on a local algebra if their restrictions coincide. -/
def AgreeOnLocalAlgebra
    (ω₁ ω₂ : ObservableState (d := d) (N := N) (G := G))
    (A : Subalgebra ℝ (GaugeConfig d N G → ℝ)) : Prop :=
  restrictState ω₁ A = restrictState ω₂ A

/-- Agreement is an equivalence relation. -/
lemma agreeOnLocalAlgebra_refl
    (ω : ObservableState (d := d) (N := N) (G := G))
    (A : Subalgebra ℝ (GaugeConfig d N G → ℝ)) :
    AgreeOnLocalAlgebra ω ω A := rfl

lemma agreeOnLocalAlgebra_symm
    {ω₁ ω₂ : ObservableState (d := d) (N := N) (G := G)}
    {A : Subalgebra ℝ (GaugeConfig d N G → ℝ)}
    (h : AgreeOnLocalAlgebra ω₁ ω₂ A) :
    AgreeOnLocalAlgebra ω₂ ω₁ A := h.symm

lemma agreeOnLocalAlgebra_trans
    {ω₁ ω₂ ω₃ : ObservableState (d := d) (N := N) (G := G)}
    {A : Subalgebra ℝ (GaugeConfig d N G → ℝ)}
    (h₁₂ : AgreeOnLocalAlgebra ω₁ ω₂ A)
    (h₂₃ : AgreeOnLocalAlgebra ω₂ ω₃ A) :
    AgreeOnLocalAlgebra ω₁ ω₃ A := h₁₂.trans h₂₃

end StateRestriction

end YangMills
