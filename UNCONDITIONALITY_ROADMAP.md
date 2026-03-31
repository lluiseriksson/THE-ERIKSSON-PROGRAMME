# UNCONDITIONALITY_ROADMAP.md
<!-- Version: v0.1.0 — 2026-03-31 -->
<!-- Grounded in: YangMills-Bloque4.pdf (Eriksson, February 2026) -->

## Status

`YangMills.clay_millennium_yangMills` currently depends on:

```
[propext, Classical.choice, Quot.sound, YangMills.yangMills_continuum_mass_gap]
```

Full unconditionality means: `[propext, Classical.choice, Quot.sound]` only.
The one remaining obstruction is `yangMills_continuum_mass_gap`.

---

## What the Axiom Encodes

```lean
axiom yangMills_continuum_mass_gap :
    ∃ m_lat : LatticeMassProfile, HasContinuumMassGap m_lat

-- where:
def HasContinuumMassGap (m_lat : LatticeMassProfile) : Prop :=
  ∃ m_phys : ℝ, 0 < m_phys ∧
    Filter.Tendsto (renormalizedMass m_lat) Filter.atTop (nhds m_phys)
```

This is **Theorem 1.1 (Lattice Mass Gap)** of Bloque4:
> For each N ≥ 2, there exists η₀ > 0 such that for all η ∈ (0, η₀] and all
> L_phys > 0, the Wilson lattice Yang-Mills measure μ_η satisfies:
> |Cov_{μ_η}(O(0), O(x))| ≤ C e^{-m|x|/a_*}, m > 0, a_* ~ Λ_YM^{-1}.

The Lean type `LatticeMassProfile` encodes the lattice mass sequence,
and `renormalizedMass` encodes m(η_j, L_{phys,j}).

---

## Proof Structure (Bloque4 §§ 3-7)

The proof of Theorem 1.1 assembles three independent ingredients:

```
yangMills_continuum_mass_gap
    ├── [A] Balaban's RG Framework (§3, Thms 3.1 + Props 3.2-3.6)
    │       ∃ effective density ρ_k with polymer decomposition
    │       + coupling control (§4, Prop 4.1): g_k ≤ γ₀ < γ for all k
    │
    ├── [B] Terminal KP Bound (§5.3, Thm 5.3) ← PAPER [1]
    │       sup_ℓ Σ_{X∋ℓ} ‖e^{R_*(X)} - 1‖_∞ e^{a|X|} e^{κ d_{k_*}(X)} ≤ δ < 1
    │       Derives from: Balaban CMP 1984-1989 activity bounds
    │                     + audited notation bridge [Paper 2]
    │
    └── [C] Multiscale Correlator Decoupling (§6, Props 6.1 + Thm 6.3)
            Telescoping identity: Cov_{μ_η}(F,G) = Cov_{μ_{a_*}}(F̃,G̃) + Σ R_k(F,G)
            UV suppression: |Σ_k R_k| ≤ C' ‖F‖ ‖G‖ e^{-c₀ R/a_*}

Assembly (§7, Thm 7.1): m = min(m_*, c₀) > 0. □
```

---

## Missing Formalization by Module

### Module BF-A: Balaban RG Framework
**Mathematical content**: Balaban's inductive representation (Thm 3.1), polymer
bounds (Prop 3.2), UV stability (Prop 3.3), R-operation (Prop 3.4), analyticity
of β-function (Prop 3.6), coupling control (Prop 4.1).

**Status**: Partially formalized as black-box axioms in `P8_PhysicalGap`.
These axioms are **dead** (not yet in the dependency chain of the final theorem).

**Estimated scope**: Large. Balaban's CMP 1984-1989 series spans 6 papers.
Abstraction level: can formalize as parametrized axioms on `EffectiveDensity`.

**Key Lean challenge**: Formalizing the Banach-algebra-valued polymer calculus.

### Module BF-B: Terminal KP Bound  ← HARDEST STEP
**Mathematical content**: Thm 5.3 of Bloque4. Proves that polymer activities
at the terminal scale satisfy Kotecký-Preiss smallness (Eq. 12).

**Grounding in Paper [1]**: "The terminal Kotecký-Preiss bound from primary
sources and an explicit assembly map for the 4D SU(N) Yang-Mills programme."
Paper [1] derives (12) from explicit activity bounds in Balaban CMP [7,8,9,10]
via the audited notation bridge Paper [2].

**Status**: NOT YET FORMALIZED. This is the core mathematical difficulty.
No Lean infrastructure exists for: abstract polymer models, KP convergence
criteria, hard-core polymer gas, terminal lattice cluster expansion.

**Lean prerequisites** (all missing):
  - Abstract polymer gas definition (connected polymers, activities)
  - Kotecký-Preiss convergence criterion
  - KP → exponential clustering implication (Prop A.1)
  - Activity bound extraction from Balaban's explicit formulas
  - Lattice animal enumeration (Lem C.1) — likely provable in Lean/Mathlib
  - Oscillation bound (Prop 5.1) — uses polymer bound + lattice animal bound

**Mathlib infrastructure available**:
  - `Filter.Tendsto` — used in current repo
  - `MeasureTheory.Measure` — for the polymer gas measure
  - `Finset.sum` — for finite-volume cluster sums
  - `Real.exp` — for activity bounds

### Module BF-C: Multiscale Telescoping and UV Suppression
**Mathematical content**: Prop 6.1 (telescoping identity), Lem 6.2 (single-scale
error), Thm 6.3 (UV suppression), Assembly Thm 7.1.

**Status**: NOT YET FORMALIZED.

**Formalization feasibility**: MEDIUM.
- Prop 6.1 is a formal identity in conditional expectations (law of total covariance).
  This can be formalized once the Balaban measure framework is in place.
- Lem 6.2 uses Green's function decay (Lem B.1 = random walk bounds).
- Thm 6.3 is a geometric series argument — straightforward once Lem 6.2 is proved.
- Assembly (Thm 7.1) is 10 lines once the ingredients exist.

**Key Lean challenge**: Formalizing conditional covariance with respect to
σ-algebras on gauge field configurations.

---

## Dependency DAG for Unconditionality

```
[GOAL] Remove yangMills_continuum_mass_gap from #print axioms output
         │
         ├── Prove yangMills_continuum_mass_gap from:
         │
         ├── [BF-A] RG Framework (Balaban black box)
         │     Lean node: balabanRG_inductive_representation
         │     Lean node: balabanRG_polymer_bounds
         │     Lean node: couplingControl_gk_small
         │     Status: Dead axioms in P8_PhysicalGap (need connecting)
         │
         ├── [BF-B] Terminal KP Bound  ← HARDEST
         │     Lean node: terminal_kp_bound  (to be created)
         │     Depends on:
         │       - polymer_gas_definition
         │       - koteckyPreiss_criterion
         │       - balabanActivityBounds (from [7,8,9,10])
         │       - notationBridge (from Paper [2])
         │
         ├── [BF-C] Terminal Clustering
         │     Lean node: terminal_exponential_clustering
         │     Depends on: BF-B + latticeAnimal_bound
         │
         ├── [BF-D] Multiscale Assembly
         │     Lean node: multiscale_telescoping
         │     Lean node: uv_suppression
         │     Lean node: mass_gap_assembly
         │     Depends on: BF-A + BF-B + BF-C + randomWalk_green_decay
         │
         └── [RESULT] yangMills_continuum_mass_gap proved as theorem
```

---

## Ranked Campaign Plan

### Route 1: Shortest Plausible Route (estimate: 6-12 months intense work)
1. Formalize abstract polymer gas + KP criterion in Lean (1-2 months)
2. Formalize lattice animal bound (Lem C.1) — likely < 1 week in Mathlib
3. Formalize terminal clustering implication (Prop A.1) (2-4 weeks)
4. Extract explicit KP bound from Balaban's [7] Eq (2.38) + [10] Eqs (1.98-1.99)
   using existing P8_PhysicalGap axioms as scaffolding (2-3 months)
5. Formalize multiscale telescoping (Prop 6.1) (1-2 months)
6. Formalize UV suppression (Thm 6.3) (2-4 weeks)
7. Assembly (Thm 7.1) (1 week)

**Risk**: Step 4 (KP bound from Balaban) is the highest-risk step.
The explicit activity bounds in Balaban [7,8,9,10] are analytically complex.

### Route 2: Highest-Confidence Route (estimate: 18-36 months)
1. Add all Balaban RG framework to live dependency chain by proving
   coupling control (Prop 4.1) in Lean using P8_PhysicalGap axioms
2. Add formal polymer model from Kotecký-Preiss [3] (1986 paper)
3. Prove Prop A.1 (KP → exponential clustering) abstractly
4. Prove KP bound from Balaban primary sources with explicit constants
5. Prove multiscale decoupling
6. Assembly

**Advantage**: Each step is independently verifiable before the next.

### Route 3: Deepest Route — Full Balaban Formalization (estimate: 5-10 years)
Formalize Balaban's entire 6-paper CMP series in Lean. This would
remove the need for ANY black-box axiom, making the Lean proof
fully self-contained. This is a major research programme.

---

## What Is Definitely Formalizable Today (Mathlib-Ready)

1. **Lattice animal bound (Lem C.1)**:
   `∑_{X∋0, X connected} e^{-κ d(X)} ≤ (1 - (2de)^{e^{-κ}})^{-1}`
   — Pure combinatorics. Provable from `Finset.card_le_card` + geometric series.

2. **Abstract KP criterion implication (Prop A.1)**:
   Once polymer gas is defined abstractly, the implication
   "KP bound ⟹ exponential clustering" is a formal argument.
   Mathlib has `tsum` and `Real.exp` already.

3. **Multiscale telescoping identity (Prop 6.1)**:
   This is the law of total covariance iterated. Provable from
   `MeasureTheory.condExp` + algebraic manipulations.

4. **UV geometric series bound (Thm 6.3)**:
   Pure analysis: Σ e^{-κL^j} = geometric series. Easy in Lean/Mathlib.

5. **Assembly (Thm 7.1)**:
   Immediate combination of Thms 5.5 and 6.3. 10 lines once proved.

---

## What Remains Mathematically Hard

1. **Activity bounds from Balaban [7] Eq (2.38)**:
   Requires controlling the polymer expansion at scale a_{k_*}.
   Depends on all of Balaban's inductive construction.
   NOT provable from existing Lean infrastructure.

2. **Coupling control (Prop 4.1)**:
   The Cauchy bound argument on β_{k+1}(g_k) requires analyticity
   of the effective action in h = g_k^2. Balaban's [6] §§4-5.
   Analyticity of a measure-derived function is hard in Lean.

3. **Large-field suppression (Prop 3.2, R-term bound)**:
   Requires the full R-operation theory from Balaban [9,10].
   No Lean infrastructure for multi-scale integrals.

---

## Immediate Next Actions (What Can Be Done Now)

### Action 1: Create polymer gas definition module
File: `YangMills/L5_Polymer/AbstractPolymerGas.lean`
Content: define `HardCorePolymerGas`, `KoteckyPreissCondition`,
state Prop A.1 as an axiom first, with the intent to prove it.

### Action 2: State the KP bound explicitly
File: `YangMills/L6_Terminal/TerminalKPBound.lean`
Content: `axiom terminal_kp_bound : ∀ (γ₀ κ a δ : ℝ), ∃ ...`
This makes the remaining assumption more transparent than
the current `yangMills_continuum_mass_gap` which hides it.

### Action 3: Connect P8_PhysicalGap to live chain
Check whether the 9 dead axioms in P8_PhysicalGap, combined
with terminal_kp_bound, can PROVE yangMills_continuum_mass_gap.
If yes, this reduces 1 live axiom to N more-atomic live axioms
(valuable if N axioms are each closer to Mathlib/provable).
If no, the split is pure accounting.

### Action 4: Prove lattice animal bound
File: `YangMills/L5_Polymer/LatticeAnimalBound.lean`
Content: formal proof of Lem C.1 from the paper.
This is Mathlib-ready and removes one ingredient from the axiom list.

---

## Verdict

**Is the repo fully unconditional?** NO.

**Exact obstruction**: `YangMills.yangMills_continuum_mass_gap`
which encodes the continuum mass gap existence (Thm 1.1 of Bloque4).

**Closest formalizable step**: Lattice animal bound (Lem C.1) and
abstract KP → clustering implication (Prop A.1). These can be
proved in Lean with moderate effort and would remove 2 sub-ingredients
from the axiom's dependency when the full proof is eventually assembled.

**Core remaining obstruction**: Terminal KP bound (Thm 5.3 of Bloque4,
proved in companion Paper [1]). This is mathematically established
(pending the companion paper) but not yet formalized in Lean.
