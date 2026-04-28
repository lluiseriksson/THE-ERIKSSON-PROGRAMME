# Mathematical Reviewer's Companion

**Audience**: mathematicians and theoretical physicists evaluating the
THE-ERIKSSON-PROGRAMME formal Yang–Mills project, who are **not Lean
specialists** and want to assess the mathematical content without
opening the proof assistant.

**Scope**: focuses on releases v1.79.0 through v1.83.0 (2026-04-25),
which packaged the F3-frontier route from polymer counts to the Clay
mass-gap structure. Earlier work (L1, L2.4-L2.6) is summarised in
context.

**Style**: each Lean declaration is paired with a one-paragraph
mathematical translation. References to primary literature are
explicit. The companion does not require trust in the Lean
formalisation; it is a self-contained mathematical exposition.

---

## 1. The setting

Fix `N_c ≥ 1` (gauge-group rank), a finite lattice
`Λ ⊂ ℤ^d` of dimension `d ≥ 2` and side length `L`, and the inverse
coupling `β > 0`.

**Wilson-Gibbs measure**. The lattice gauge configurations are maps
from edges of `Λ` to `SU(N_c)`. The Wilson plaquette energy at a
plaquette `p` evaluated on a configuration `U` is

```
E_p(U) := Re(tr(U_p))
```

where `U_p` is the holonomy around the plaquette. The Wilson-Gibbs
weight is `exp(-β · ∑_p E_p(U))`, normalised by the partition
function `Z(β)`. The reference measure is the product of `SU(N_c)`
Haar measures over all edges; we denote the resulting normalised
measure on configurations by `μ_{β,Λ}`.

**Connected correlator**. For `F : SU(N_c) → ℝ` a class function and
`p, q` two plaquettes,

```
⟨F_p; F_q⟩_β := ⟨F(U_p) · F(U_q)⟩_β − ⟨F(U_p)⟩_β · ⟨F(U_q)⟩_β
```

(the connected two-point function). The mass-gap statement asserts
exponential decay of `|⟨F_p; F_q⟩|` in the lattice distance between
`p` and `q`.

## 2. The target object: `ClayYangMillsMassGap N_c`

In Lean:

```lean
structure ClayYangMillsMassGap (N_c : ℕ) [NeZero N_c] : Type where
  m : ℝ
  hm : 0 < m
  C : ℝ
  hC : 0 < C
  hbound :
    ∀ {d : ℕ} [NeZero d] {L : ℕ} [NeZero L] (β : ℝ) (_hβ : 0 < β)
      (F : SU(N_c) → ℝ) (_hF_bdd : ∀ U, |F U| ≤ 1)
      (p q : Plaquette d L),
      1 ≤ siteLatticeDist p q →
      |wilsonConnectedCorr ... β F p q| ≤ C · exp(-m · siteLatticeDist p q)
```

**Mathematical reading**. An inhabitant of `ClayYangMillsMassGap N_c`
is a pair of positive constants `(m, C)` together with a proof that
for every dimension `d`, every finite volume `L`, every positive `β`,
and every uniformly bounded class observable `F`, the Wilson connected
correlator decays exponentially in the lattice distance with rate `m`
and prefactor `C`.

This is the **lattice-level** mass-gap statement. The full Clay
Millennium statement requires the continuum limit (`a → 0`,
Osterwalder-Schrader axioms, Wightman reconstruction) which is
**outside the scope** of this lattice formalisation. The lattice
mass gap is the input to a continuum extension; it is not the
Clay theorem.

## 3. Two existing inhabitants

### 3.1 `clayYangMillsTheorem_trivial`

Audited as vacuous in `L8_Terminal/ClayTrivialityAudit.lean`. The
weak endpoint `ClayYangMillsTheorem := ∃ m_phys, 0 < m_phys` is
logically equivalent to `True` and is satisfied by `⟨1, one_pos⟩`.
Mentioned here only for completeness; it is not the mass-gap
statement.

### 3.2 `u1_clay_yangMills_mass_gap_unconditional`

In `AbelianU1Unconditional.lean` (file misnamed; see
`COWORK_FINDINGS.md` Finding 003). For `N_c = 1`,
`SU(1) = {1}` is the trivial group, so the Wilson connected
correlator vanishes identically:

```
⟨F_p; F_q⟩ = F(1) · F(1) − F(1) · F(1) = 0
```

The bound `|0| ≤ C · exp(-m · dist)` holds for any positive `C, m`.
The construction picks `m = -log(1/2) / 2 = log 2 / 2` and `C = 1`.

**Status**: Lean-level real, physics-level degenerate. N_c = 1 is the
trivial gauge group with no gauge dynamics; this is **not** the
abelian QED-like U(1) (which uses `unitaryGroup (Fin 1)`, the unit
circle).

The first physically non-trivial Clay-grade witness still requires
`N_c ≥ 2`. That is the open work.

## 3.3 Reading `FORMAL_KERNEL` rows with vacuity caveats

`FORMAL_KERNEL` means Lean has verified the stated artifact without
project-specific assumptions.  It does **not** automatically mean the artifact
has the physical or representation-theoretic content an external reader may
expect from its informal name.  The project therefore tracks a separate
`vacuity_flag` column in `UNCONDITIONALITY_LEDGER.md` Tier 1 and Tier 2.

The rule of thumb is:

```
FORMAL_KERNEL + vacuity caveat = real Lean theorem, limited mathematical payload.
```

Current examples:

- `NC1-WITNESS`: formally real for `N_c = 1`, but `SU(1)` is the trivial
  group.  Do not read it as evidence for `SU(N)` Yang-Mills with `N >= 2`.
- `EXP-SUN-GEN`: formally retires generator-data axioms in the current
  experimental API, but the witness is the zero matrix family.  Do not read it
  as a Pauli/Gell-Mann/general `su(N)` generator basis.
- Weak Clay endpoint canaries: useful audit tripwires, but the endpoint
  `∃ m_phys, 0 < m_phys` is trivially inhabited.
- Structural Balaban / OS-style carriers described in `KNOWN_ISSUES.md`:
  useful shape control, but carrier inhabitation is not the analytic Wilson,
  Gibbs, RG, or OS reconstruction theorem itself.
- `ClayCoreLSI`: the named carrier is an arithmetic existential; the real
  analytic target is the transfer to a genuine `DLR_LSI` statement for
  physical `SU(N)` data.
- Triple-view L42/L43/L44 characterisations: structurally useful, but the
  constants are anchors rather than derived confinement data.
- `CONTINUUM-COORDSCALE`: explicitly `INVALID-AS-CONTINUUM`; do not count it
  as progress toward the continuum limit.

When citing this repository externally, cite both the formal status and the
vacuity flag/caveat.  For example: "oracle-clean for the degenerate `SU(1)`
case, `vacuity_flag = trivial-group`" is accurate; "unconditional Yang-Mills
mass gap for physical `SU(N)`" is not.

## 4. The route to the open `N_c ≥ 2` witness — F3 frontier

The strategy is the standard **high-temperature cluster expansion**
of lattice gauge theory (Osterwalder–Seiler 1978; Brydges 1986;
Seiler 1982). The argument decomposes the connected correlator
`⟨F_p; F_q⟩` as a sum over **polymers** — connected sets of plaquettes
containing both `p` and `q` — weighted by **truncated activities**.
Convergence is controlled by:

1. The **Mayer/Ursell truncated activity** decays geometrically in
   polymer size: `|K(Y)| ≤ A_0 · r^|Y|` for some `r < 1`, `A_0 > 0`.
2. The **count of polymers** of size `m` containing two fixed points
   grows at most as `C_conn · K_count^m` for some `K_count`.
3. The **smallness condition** `r · K_count < 1` ensures the
   geometric series converges, giving exponential decay of the
   correlator.

This is what the Lean releases v1.79–v1.83 package.

### 4.1 v1.79.0 — `ShiftedConnectingClusterCountBoundExp`

```lean
def ShiftedConnectingClusterCountBoundExp (C_conn K : ℝ) : Prop :=
  ∀ {d L} [NeZero d] [NeZero L] (p q : Plaquette d L) (n : ℕ),
    n ∈ range(|Plaquette d L| + 1) →
    1 ≤ siteLatticeDist p q →
    #{Y connected polymer | p,q ∈ Y, |Y| = n + ⌈d(p,q)⌉}
      ≤ C_conn · K^n
```

**Mathematical reading**. This is the **Klarner / Madras–Slade
lattice-animal count** (Klarner 1967, Madras–Slade 1993 ch. 3),
specialised to connected polymers anchored at two distinguished
points. The bound is exponential in the **excess size** `n` (over
the minimum `⌈d(p,q)⌉` forced by connectivity).

The classical estimate: in `ℤ^d`, the number of connected animals of
size `m` containing the origin is at most `λ_d^m` where `λ_d ∈ (d,
2d-1)` is the **connective constant**. For our setting with two
anchored points the bound is comparable. For `d = 4` (physical
Yang–Mills), `K = 7 = 2·4 - 1` is the standard upper bound.

**Status as of 2026-04-25**: this is a **declared interface** in
Lean. The witness — i.e. an actual proof of the bound for the
`ConcretePlaquette d L` adjacency graph — is open work
(`BLUEPRINT_F3Count.md` §−1, ~150 LOC of induction).

### 4.2 v1.80.0 — `clusterPrefactorExp`

```lean
noncomputable def clusterPrefactorExp (r K C_conn A₀ : ℝ) : ℝ :=
  C_conn · A₀ · ∑' n : ℕ, K^n · r^n
```

**Mathematical reading**. The constant prefactor that appears in
front of the geometric decay envelope. Under the smallness
hypothesis `K · r < 1`, the tsum equals `1 / (1 − K·r)`, giving the
familiar Kotecký–Preiss form `A_0 · C_conn / (1 − r·K)`.

The Lean version uses the tsum form rather than the closed
geometric-series form to avoid having to discharge `1 − K·r > 0` at
the definition site; this comes for free when the smallness
hypothesis is supplied.

### 4.3 v1.81.0 — `clusterCorrelatorBound_of_truncatedActivities_ceil_exp`

The bridge theorem connecting the cluster count + activity bound to
the cluster correlator bound:

```
ClusterCorrelatorBound N_c r (clusterPrefactorExp r K C_conn A₀)
```

is produced from:

- `(T β F p q).K_bound Y ≤ A_0 · r^|Y|` (the Mayer activity bound)
- `count(n) ≤ C_conn · K^n` (the count bound)
- `0 < r`, `r < 1`, `0 < K`, `K · r < 1` (positivity + smallness)

**Mathematical reading**. This is the standard cluster-expansion
**term-by-term** bound:

```
Σ over polymers Y, p,q ∈ Y |K(Y)| · ... ≤ Σ_{n} count(n) · A_0 · r^{n + ⌈d(p,q)⌉}
                                         ≤ Σ_n C_conn · K^n · A_0 · r^{n + ⌈d(p,q)⌉}
                                         = A_0 · r^{⌈d(p,q)⌉} · C_conn · Σ_n (Kr)^n
                                         = clusterPrefactorExp r K C_conn A_0 · r^{⌈d(p,q)⌉}
```

The exponential decay rate `r^⌈d(p,q)⌉` is converted to
`exp(-m · d(p,q))` via the identity
`r^x ≤ exp(-(-log r / 2) · x · 2) = exp(-2(-log r / 2) · x)`
(`rpow_le_exp_kpParameter`). The mass gap is therefore
`m = kpParameter(r) := -log(r) / 2 > 0` for `r < 1`.

### 4.4 v1.82.0 — `ShiftedF3MayerCountPackageExp` and the Clay endpoint

The unified assembly object:

```lean
structure ShiftedF3MayerCountPackageExp where
  C_conn, K, A₀ : ℝ
  hC, hK, hA, hKr_lt1 : (positivity + smallness)
  data    : ConnectedCardDecayMayerData N_c wab.r A₀ ...    -- F3-Mayer fills
  h_count : ShiftedConnectingClusterCountBoundExp C_conn K   -- F3-Count fills
```

with terminal endpoint:

```lean
clayMassGap_of_shiftedF3MayerCountPackageExp :
  ShiftedF3MayerCountPackageExp N_c wab → ClayYangMillsMassGap N_c
```

**Mathematical reading**. Once both the Mayer-side activity package
and the Count-side animal-count package are produced, with
constants satisfying `K · wab.r < 1`, the Clay mass-gap structure
is constructed mechanically with `m = kpParameter(wab.r)` and
`C = clusterPrefactorExp wab.r K C_conn A_0`.

This is the **single endpoint** the closure target needs to feed.
Everything from polymer-count + activity-decay to a positive mass
gap is now packaged.

### 4.5 v1.83.0 — Physical d = 4 specialisation

`physicalClusterCorrelatorBound_of_expCountBound_mayerData_ceil` is
the same machinery instantiated at `d = 4`, the physical lattice
dimension. No new mathematical content; just ergonomic specialisation.

## 5. The remaining open theorems

### 5.1 The lattice-animal count witness

**Statement**:
```
For each d ≥ 2, the number of connected polymers Y in
ConcretePlaquette d L containing two fixed plaquettes p, q with
|Y| = n + ⌈d(p,q)⌉ is at most (2d-1)^n.
```

**Reference**: Klarner 1967 (cell-growth problems), Madras–Slade
1993 ch. 3 (self-avoiding walk and animal counts), Pfister 1991
(Statistical mechanics of polymer models).

**Proof sketch**: enumerate connected polymers anchored at `p` via
their breadth-first-search spanning trees. At each step, the new
plaquette is one of at most `2d - 1` "fresh" neighbours of the
current frontier. This gives `count(m) ≤ (2d-1)^(m-1) · 2d` (~ `(2d-1)^m`)
for connected anchored polymers of size `m`. Restricting to those
also containing `q` is a further filter; the bound is preserved.

**Estimated Lean LOC**: ~150. Direct induction on `m`; no
infrastructure beyond standard `SimpleGraph`/`Finset` API.

### 5.2 The Brydges–Kennedy estimate

**Statement**:
```
For the truncated activity K(Y) of the Wilson-Gibbs cluster expansion
in SU(N_c) at inverse coupling β, with Y a connected polymer:
|K(Y)| ≤ ‖w̃‖_∞^|Y|
where w̃ is the normalised plaquette fluctuation.
```

**Reference**: Brydges–Kennedy 1987 (Mayer expansions and the
Hamilton-Jacobi equation), Battle–Federbush 1984 (random walks in
cluster expansions), Seiler 1982 (Gauge theories as a problem of
constructive QFT) ch. 4.

**Proof sketch**: the BK random-walk interpolation formula expresses
`K(Y)` as an integral of a derivative of the cluster average over a
unit cube, weighted by a sum over **trees on Y** (Cayley) rather than
**partitions of Y** (Bell number). The tree weighting cancels the
factorial blowup that naive Möbius inversion would introduce, and
the zero-mean property `∫ w̃ dHaar = 0` (already proved in the
project as `plaquetteFluctuationNorm_mean_zero`) eliminates
single-plaquette contributions. The result is the bound
`|K(Y)| ≤ ‖w̃‖_∞^|Y|` with no factorial factor.

For SU(N_c) Wilson with the normalised fluctuation:
`‖w̃‖_∞ ≤ 4 N_c · β` for `β < log(2) / N_c` (high-temperature regime).

**Estimated Lean LOC**: ~600 across 4 files
(`MayerInterpolation.lean`, `HaarFactorization.lean`,
`BrydgesKennedyEstimate.lean`, `PhysicalConnectedCardDecayWitness.lean`).
This is the analytic boss of the F3 frontier.

### 5.3 Combined regime

When both 5.1 and 5.2 land, with `K = 7` (d=4), `A_0 = 1`,
`r = 4 N_c · β`, the smallness constraint becomes:

```
K · r < 1 ⇔ 4 N_c · β · 7 < 1 ⇔ β < 1 / (28 N_c)
```

For physical N_c = 3 (SU(3) QCD): **β < 1/84 ≈ 0.012**. This is the
high-temperature / weak-coupling regime — historically the regime
where the cluster expansion is known to converge and the mass gap is
provable by this technique. The lattice mass gap `m = kpParameter(r) =
-log(4 N_c β) / 2` is positive and well-defined in this regime.

## 6. What the formalisation does and does not establish

### 6.1 Does establish (when 5.1 + 5.2 land)

For SU(N_c) lattice Yang–Mills at sufficiently small β, **a strictly
positive lattice mass gap** in the form

```
|⟨F_p; F_q⟩_β| ≤ C · exp(-m · dist(p,q))
```

uniformly in dimension `d`, finite volume `L`, and bounded class
observable `F`. This is a non-trivial mathematical theorem with a
fully checked machine proof.

### 6.2 Does not establish

- The **continuum limit**. Taking `a → 0`, recovering Wightman /
  Osterwalder-Schrader axioms, controlling the renormalisation flow
  via Balaban-style RG — none of this is in scope. The lattice
  mass gap is necessary input for a continuum extension; it is not
  itself the continuum theorem.

  **Important caveat**: the v1.84.0 release added endpoints producing
  `ClayYangMillsPhysicalStrong`, which is defined as the conjunction
  of `IsYangMillsMassProfile m_lat` (the mass profile bounds Wilson
  correlators — genuine) **and** `HasContinuumMassGap m_lat` (the
  renormalised mass converges — formal). The latter is satisfied
  via an architectural coordination of the repository: with
  `latticeSpacing N = 1/(N+1)` and the chosen profile
  `constantMassProfile m N = m/(N+1)`, the renormalised mass
  `m_lat / latticeSpacing` is identically equal to the constant `m`
  and so trivially converges. **The v1.84.0 chain therefore reaches
  `ClayYangMillsPhysicalStrong` via a coordinated convention for
  the continuum half**, not via genuine continuum-limit analysis.
  External descriptions of the chain should include this qualifier.
  See `COWORK_FINDINGS.md` Finding 004 for the full analysis.

- The **non-perturbative regime** `β > β_c`. The cluster expansion
  diverges at strong coupling; the technique here is fundamentally
  high-temperature. A proof of the mass gap throughout the
  confining phase requires different tools (reflection positivity,
  Wilson loops, large-N expansion).
- **Glueball spectrum, asymptotic freedom, confinement
  qualitatively**. These are physics outputs that lie downstream
  of the bound proved here.

### 6.3 What the Clay Millennium statement requires beyond this

The Clay statement (Jaffe–Witten 2000 problem description) requires:

1. Construction of a Yang-Mills measure on `ℝ^4` satisfying the
   Wightman axioms.
2. Proof that the spectrum of the resulting Hamiltonian has a gap.

The lattice mass gap proved here is a **lower bound** on the
spectrum **at the lattice level**. The continuum extension (1)
plus the spectrum interpretation (2) are separate and substantially
larger projects.

This formalisation does **not claim** to solve the Clay Millennium
problem. It claims to formalise a known piece of the puzzle — the
high-temperature lattice mass gap — with a fully checked machine
proof modulo two well-understood open theorems (the Klarner count
and the Brydges–Kennedy estimate).

## 7. References for review

Primary sources in increasing technicality:

- Wilson, *Confinement of quarks*, Phys. Rev. D **10** (1974) — the
  lattice gauge theory.
- Osterwalder & Seiler, *Gauge field theories on a lattice*,
  Ann. Physics **110** (1978) — character expansion + small-β.
- Seiler, *Gauge Theories as a Problem of Constructive Quantum
  Field Theory and Statistical Mechanics*, Lecture Notes in Physics
  **159** (1982) — comprehensive monograph.
- Kotecký & Preiss, *Cluster expansion for abstract polymer
  models*, CMP **103** (1986) — the convergence criterion.
- Brydges & Kennedy, *Mayer expansions and the Hamilton-Jacobi
  equation*, JSP **48** (1987) — the random-walk estimate that
  v1.83+5.2 will eventually formalise.
- Brydges, *A short course on cluster expansions*, Les Houches
  (1986) — the standard pedagogical reference.
- Balaban, *Large field renormalization II*, CMP **122** (1989) —
  the renormalisation framework.
- Klarner, *Cell-growth problems*, Canad. J. Math. **19** (1967) —
  the lattice-animal counting argument.
- Madras & Slade, *The Self-Avoiding Walk*, Birkhäuser (1993) —
  comprehensive treatment of related combinatorial bounds.
- Jaffe & Witten, *Quantum Yang–Mills Theory*, Clay Millennium
  Problem description (2000) — the target statement.

## 8. How to verify the Lean formalisation

For a reviewer who wants to verify rather than trust:

1. Clone the repository at the version tag of interest (currently
   v1.83.0).
2. Install Lean 4 (`leanprover/lean4:v4.29.0-rc6`) and Mathlib
   `master` per `lean-toolchain` and `lakefile.lean`.
3. Run `lake build YangMills`. This compiles the entire formalisation
   (~30 minutes on a 2024 laptop).
4. For any specific theorem `T`, run `#print axioms T` in a Lean
   environment. The expected output is
   `[propext, Classical.choice, Quot.sound]` — the three foundational
   axioms of Lean 4 plus Mathlib's Classical choice. Any other axiom
   in the output indicates an explicit project assumption (currently:
   none in non-Experimental files).

For the open theorems (5.1 and 5.2), the Lean files do not yet exist.
The mathematical content above is what the Lean formalisation will
need to encode.

---

*This companion is a self-contained mathematical exposition of the
formalisation's content. It does not require trust in the Lean proofs.
Last updated 2026-04-25 by Cowork agent.*
