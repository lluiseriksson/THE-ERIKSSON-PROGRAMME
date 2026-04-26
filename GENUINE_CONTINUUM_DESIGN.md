# GENUINE_CONTINUUM_DESIGN.md

**Author**: Cowork agent (Claude), design pass 2026-04-25
**Subject**: design sketch for `ClayYangMillsPhysicalStrong_Genuine` — a
predicate that requires a **physical** lattice-spacing convention rather
than the coordinated artifact currently used by the project.
**Status**: strategic design proposal. **Not committed Lean code.**
Requires Lluis approval before implementation.

This document responds to action 3 of `COWORK_FINDINGS.md` Finding 004.

---

## 0. The problem

The current `ClayYangMillsPhysicalStrong` predicate combines:

```lean
IsYangMillsMassProfile m_lat   -- physical: bounds Wilson correlators
HasContinuumMassGap m_lat      -- formal: renormalised mass converges
```

The `HasContinuumMassGap` half is satisfied via:

```lean
def latticeSpacing (N : ℕ) : ℝ := 1 / (N + 1)
def renormalizedMass (m_lat : LatticeMassProfile) (N : ℕ) : ℝ :=
  m_lat N / latticeSpacing N

def HasContinuumMassGap (m_lat : LatticeMassProfile) : Prop :=
  ∃ m_phys : ℝ, 0 < m_phys ∧
    Tendsto (renormalizedMass m_lat) atTop (𝓝 m_phys)
```

The witness used by `connectedCorrDecay_implies_physicalStrong` is:

```lean
def constantMassProfile (m : ℝ) : LatticeMassProfile := fun N => m / (N + 1)
```

(Despite the name, this is **not constant** in `N` — it scales as `1/(N+1)`,
which is precisely the inverse of `latticeSpacing N`.)

So `renormalizedMass (constantMassProfile m) N = (m/(N+1)) / (1/(N+1)) = m`,
which trivially converges to `m`. `HasContinuumMassGap (constantMassProfile m)`
is satisfied for any `m > 0` because the two definitions are coordinated.

**This satisfies the structural requirement of `ClayYangMillsPhysicalStrong`
in Lean but does not establish a continuum mass gap of the physical
theory.**

---

## 1. What a genuine continuum-mass-gap predicate would look like

A genuine version would require:

1. The lattice spacing to follow a **physically meaningful** scaling,
   not the coordinated artifact `1/(N+1)`. In lattice gauge theory the
   natural scaling is via the **renormalisation group**: `a(g) = (1/Λ) ·
   exp(-1/(2 b_0 g²))` for SU(N_c), where `Λ` is the lattice scale and
   `b_0 = 11 N_c / (48 π²)` is the one-loop β-function coefficient
   (asymptotic freedom).
2. The mass profile to be the **physical** lattice mass at the given
   coupling/spacing, **not** a coordinated artifact.
3. The convergence of `m_lat / a` to a positive limit as `a → 0` to
   correspond to the renormalisation flow of the physical theory.

In the literature this is the **continuum limit** in the Wilson sense:
take `g(a) → 0` such that the lattice spacing `a → 0` while a physical
observable (e.g. the string tension, the lowest glueball mass) stays
fixed.

---

## 2. Proposed Lean structure

```lean
namespace YangMills

/-- A physical lattice spacing scheme: not just an arbitrary positive
    function of `N`, but one that follows the renormalisation-group
    scaling of asymptotic freedom for SU(N_c) Yang-Mills.

    Specifically, with one-loop β-function coefficient
    `b_0 = 11 N_c / (48 π²) > 0`, the lattice spacing satisfies:

        a(g) = (1 / Λ) · exp(-1 / (2 · b_0 · g²))

    parameterised by the lattice coupling `g(N)` which itself runs
    according to the lattice β-function. -/
structure PhysicalLatticeScheme (N_c : ℕ) [NeZero N_c] where
  /-- The lattice spacing as a function of resolution `N`. -/
  a : ℕ → ℝ
  /-- Strict positivity. -/
  ha_pos : ∀ N, 0 < a N
  /-- The lattice spacing tends to zero as resolution increases
      (continuum limit). -/
  ha_tends_zero : Tendsto a atTop (𝓝 0)
  /-- The lattice coupling at each resolution. -/
  g : ℕ → ℝ
  /-- Strict positivity of the coupling. -/
  hg_pos : ∀ N, 0 < g N
  /-- Asymptotic freedom: `g(N) → 0` as `N → ∞`. -/
  hg_asymp_free : Tendsto g atTop (𝓝 0)
  /-- The relation `a(N) = (1/Λ) · exp(-1/(2 b_0 g(N)²))`, possibly up
      to higher-loop corrections that are subleading. -/
  ha_g_relation : ∃ Λ : ℝ, 0 < Λ ∧
    Tendsto (fun N => a N * Real.exp (1 / (2 * b0 N_c * (g N)^2)))
      atTop (𝓝 (1 / Λ))

/-- One-loop β-function coefficient for SU(N_c). -/
noncomputable def b0 (N_c : ℕ) : ℝ := (11 : ℝ) * N_c / (48 * Real.pi ^ 2)

/-- Genuine continuum mass gap: the lattice mass `m_lat N` divided by the
    physical lattice spacing `scheme.a N` converges to a positive limit. -/
def HasContinuumMassGap_Genuine
    {N_c : ℕ} [NeZero N_c]
    (scheme : PhysicalLatticeScheme N_c)
    (m_lat : LatticeMassProfile) : Prop :=
  ∃ m_phys : ℝ, 0 < m_phys ∧
    Tendsto (fun N => m_lat N / scheme.a N) atTop (𝓝 m_phys)

/-- Genuine non-vacuous Clay-Millennium-grade predicate. -/
def ClayYangMillsPhysicalStrong_Genuine
    {N_c : ℕ} [NeZero N_c] {d : ℕ} [NeZero d]
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ)
    (F : G → ℝ)
    (distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ)
    (scheme : PhysicalLatticeScheme N_c) : Prop :=
  ∃ m_lat : LatticeMassProfile,
    IsYangMillsMassProfile μ plaquetteEnergy β F distP m_lat ∧
    HasContinuumMassGap_Genuine scheme m_lat

end YangMills
```

---

## 3. Where this would live in the repository

- `YangMills/L7_Continuum/PhysicalScheme.lean` — new file.
- `YangMills/L7_Continuum/ContinuumLimit.lean` — extended to include
  `HasContinuumMassGap_Genuine` alongside the existing
  `HasContinuumMassGap`. The existing predicate is preserved for
  backwards compatibility.
- `YangMills/L8_Terminal/ClayPhysical.lean` — extended to include
  `ClayYangMillsPhysicalStrong_Genuine` alongside the existing
  `ClayYangMillsPhysicalStrong`.

The relationship between the two:

```lean
-- Genuine implies formal: any physical scheme is also a "lattice spacing
-- function", so a genuine continuum mass gap implies the formal one.
theorem hasContinuumMassGap_of_Genuine
    {N_c : ℕ} [NeZero N_c]
    (scheme : PhysicalLatticeScheme N_c)
    (m_lat : LatticeMassProfile)
    (h : HasContinuumMassGap_Genuine scheme m_lat) :
    HasContinuumMassGap m_lat := by
  -- Pointwise comparison: scheme.a N is one valid lattice spacing
  -- function. The original HasContinuumMassGap uses 1/(N+1); we'd need
  -- to either:
  --   (a) generalise HasContinuumMassGap to take a spacing function as
  --       parameter, or
  --   (b) prove that any (m_phys, scheme.a) pair re-scales into a
  --       (m_phys', latticeSpacing) pair via change of resolution
  --       parameterisation.
  -- (a) is cleaner; (b) is more invasive.
  sorry  -- design choice required

-- Formal does NOT imply genuine.
-- The constant profile witness for HasContinuumMassGap exhibits that
-- HasContinuumMassGap is satisfiable without any physical scheme, hence
-- there is no implication in the reverse direction.
```

The non-implication direction is the substantive content: it documents
that the formal predicate is genuinely weaker than the genuine one.

---

## 4. What it would take to produce a witness

For SU(N_c) lattice Yang-Mills at small `β`, a genuine witness of
`ClayYangMillsPhysicalStrong_Genuine` would require:

1. **A lattice β-function recursion** for the running coupling `g(N)`
   such that `g(N) → 0`. Phase 6 of the project's roadmap
   (`HasAsymptoticFreedomControl`) is the framework target. Lean
   skeleton already exists (`P6_AsymptoticFreedom/`), but the actual
   recursion is gated on Balaban CMP 116/119/122 estimates which are
   among the project's hardest open analytic targets.
2. **A physical mass profile** `m_lat N` derived from the F3 cluster
   expansion at resolution `N` (i.e. with coupling `g(N)`), via
   `m_lat N := kpParameter (4 N_c · β(g(N)))` or similar — but
   parameterised by `g(N)` running to 0 rather than fixed `β`.
3. **The convergence proof**: combining (1) and (2), show that
   `m_lat(N) / scheme.a(N)` converges to a positive number. Under
   asymptotic freedom this is the **dimensional transmutation**
   miracle: the physical mass is finite even though both `m_lat(N)`
   and `scheme.a(N)` go to zero, with their ratio governed by the
   anomalous dimension.

The **dimensional transmutation** computation is the heart of why the
Yang-Mills mass gap is hard. It is not in the F3 cluster-expansion
chain; it is in the renormalisation-group flow that the cluster
expansion does **not** address.

This is why I rate this as **out of scope for the project's near-term
horizon** even after both F3 packages close.

---

## 5. Recommendation

Three options for Lluis:

### Option A — Implement now, mark as aspirational

Add `PhysicalLatticeScheme`, `HasContinuumMassGap_Genuine`,
`ClayYangMillsPhysicalStrong_Genuine` to the codebase as **named
predicates with no witness**. Add an `axiom` for the genuine version
that says "no current chain produces this", as documentation.

Pro: makes the distinction visible at the type level; future readers
cannot confuse the two.

Con: introduces a new (named, never-discharged) axiom — would violate
HR3 even though it's "just for documentation". Probably not the right
move.

### Option B — Document only, do not add Lean predicate

Keep the document this file you are reading, plus the Finding 004 in
`COWORK_FINDINGS.md`, plus the caveats now added in
`STATE_OF_THE_PROJECT.md` and `MATHEMATICAL_REVIEWERS_COMPANION.md`.
Do not add a new Lean predicate.

Pro: zero changes to the codebase; honest in narrative; preserves the
0-axiom invariant.

Con: external readers who skim only the Lean code won't see the
caveat unless they read the strategic docs.

### Option C — Refactor `HasContinuumMassGap` to take a spacing scheme

Change the existing `HasContinuumMassGap` from

```lean
def HasContinuumMassGap (m_lat : LatticeMassProfile) : Prop := ...
```

to

```lean
def HasContinuumMassGap (scheme : LatticeSpacingScheme) (m_lat : LatticeMassProfile) : Prop := ...
```

with the existing artifact `latticeSpacing N = 1/(N+1)` exposed as
`coordinatedScheme : LatticeSpacingScheme`. Existing call sites carry
the coordinated scheme as input; the genuine version becomes the
specialisation to a physical scheme.

Pro: makes the distinction first-class in the type signature; downstream
witnesses must declare which scheme they use; impossible to confuse
the two going forward.

Con: substantial refactor across `L7_Continuum` and `L8_Terminal`.
~300-500 LOC of mechanical updates plus careful audit of each
`HasContinuumMassGap` consumer.

### My recommendation

**Option B** for now, **Option C eventually**.

Rationale:
- The 0-axiom invariant is more valuable than the type-level
  distinction for the project's current phase.
- The strategic docs (this file + Finding 004 + the new paragraphs in
  STATE_OF_THE_PROJECT and MATHEMATICAL_REVIEWERS_COMPANION) are
  sufficient to prevent miscommunication with external reviewers.
- Once both F3 packages close (after Priority 1.2 and Priority 2-3
  in `CODEX_CONSTRAINT_CONTRACT.md`), and the project is **claiming
  end-to-end** the Clay mass-gap target, **then** Option C should be
  done as a "honesty refactor" that ships alongside the announcement.
  At that point, ~400 LOC of refactor is small change next to the
  visibility of the announcement.

---

## 6. Next actions (if Lluis approves Option B)

- [x] Finding 004 filed.
- [x] STATE_OF_THE_PROJECT.md updated (action 1 of Finding 004).
- [x] MATHEMATICAL_REVIEWERS_COMPANION.md updated (action 2).
- [x] This design document committed to repo.
- [ ] No Lean changes.

If Lluis approves Option C, it becomes a future Priority item to file
in `CODEX_CONSTRAINT_CONTRACT.md` §4 — likely Priority 4.x, after the
F3 packages close and before any external announcement.

---

*Design pass complete 2026-04-25 by Cowork agent.*
