# BLUEPRINT_BalabanRG.md

**Author**: Cowork agent (Claude), strategic blueprint 2026-04-25
**Subject**: Bałaban's renormalisation-group control over scales —
the historical Clay candidate
**Branch**: II of `OPENING_TREE.md`
**Companion**: `BLUEPRINT_F3Count.md`, `BLUEPRINT_F3Mayer.md`,
`BLUEPRINT_ContinuumLimit.md`, `BLUEPRINT_ReflectionPositivity.md`

---

## 0. Why Branch II is the long-horizon prep

Of all the branches in `OPENING_TREE.md`, **Branch II is the closest
known mathematical approach to the actual Clay-Millennium statement**
of Yang-Mills. Tadeusz Bałaban's series of papers (Comm. Math. Phys.
1986-1995, ~500 pages of analysis) constructed a rigorous
multi-scale RG framework for SU(2) lattice gauge theory and argued
it extends to SU(N≥3). Most experts agree the Bałaban approach
**modulo specific lemmas** completes the Clay statement; the
controversies are over those specific lemmas, not the framework.

This blueprint is **long-horizon prep**: not full formalisation
(that would be a multi-year project), but identification of:

1. **What the inductive RG step actually says** mathematically.
2. **What the project's existing `P3_BalabanRG/` and
   `ClayCore/BalabanRG/` infrastructure already covers**.
3. **Which axioms in the project can plausibly be retired by a
   Bałaban-style closure**.
4. **Recommended order of attack** if the project ever decides to
   pursue Branch II seriously.

This is **not an active execution plan** for the current session.
It is preparation, like analyzing a candidate opening before
deciding to play it.

---

## 1. The Bałaban framework in one paragraph

The lattice Wilson SU(N_c) gauge theory at lattice spacing `a` has a
gauge coupling `g(a)`. Asymptotic freedom (one-loop β-function with
`b₀ = 11N/(48π²) > 0`) says `g(a) → 0` as `a → 0`. Bałaban's
strategy: define a sequence of effective theories at scales
`a_0 > a_1 > ... > a_k > ...` related by **block-spin renormalisation**
(integrating out short-distance modes between scales). At each scale,
control the effective action via:

- **Small-field bound**: where the field is "close to a pure gauge",
  the effective action is approximately Gaussian.
- **Large-field suppression**: where the field is "far from a pure
  gauge", the Boltzmann weight is exponentially suppressed.

The **inductive RG step** says: if these two bounds hold at scale `a_k`,
they hold at scale `a_{k+1}` (with explicit constants). Iterating
gives uniform-in-`k` bounds that survive the continuum limit.

The Clay statement follows from:
1. The uniform-in-scale bound on the effective action.
2. Standard Osterwalder-Schrader reconstruction (Branch III + VII).

---

## 2. What the project already has

The project has substantial Bałaban scaffolding:

- **`YangMills/P3_BalabanRG/`** (5 files): `CorrelationNorms.lean`,
  `RGContraction.lean`, `MultiscaleDecay.lean`,
  `LatticeMassExtraction.lean`, `Phase3Assembly.lean`. Last touched
  2026-03-31 — stable but inactive. Defines the abstract framework.

- **`YangMills/ClayCore/BalabanRG/`** (~50 files): the active
  Bałaban implementation area. Heavily used (per `LAYER_AUDIT.md`,
  6 importers from outside ClayCore; many ClayCore-internal). Files
  cover P81 / P91 estimates (Bałaban's CMP 116 / CMP 122 papers).
  Active throughout April 2026.

- **`YangMills/L2_Balaban/`**, **`YangMills/L3_RGIteration/`**,
  **`YangMills/L4_LargeField/`** (all stubs, partly orphaned).

- **`YangMills/Experimental/LieSUN/`** and
  **`YangMills/Experimental/Semigroup/`**: 14 axioms (per
  `EXPERIMENTAL_AXIOMS_AUDIT.md`) supporting the Lie-derivative and
  semigroup machinery that Bałaban-RG needs.

So **the framework is partly built**. What's missing:
- The actual inductive RG step content (substantive analysis).
- The retirement of the 6 hard-retire Experimental axioms (Hille-Yosida,
  Beurling-Deny, Gronwall variance decay).
- Connection of the Bałaban scaffolding to the F3 / RP / continuum
  branches.

---

## 3. The inductive RG step — what to formalise

### 3.1 Statement (high level)

Per Bałaban CMP 122 (1989), Eqs. (1.98)-(1.100):

> **(One-step RG induction)**: Let `a_k` be a sequence of lattice
> spacings with `a_{k+1} = L · a_k` (some block-spin factor `L > 1`).
> Let `Z_k(g_k, A_k)` be the partition function at scale `a_k` with
> coupling `g_k` and effective action `A_k`. There exist explicit
> constants `c_1, c_2, ...` such that if `A_k` satisfies:
>
> - `‖R^sf_*(X)‖_∞ ≤ E_0 · g_k² · exp(-κ d(X))` (small-field bound)
> - `‖R^lf_*(X)‖_∞ ≤ exp(-p_0(g_k)) · exp(-κ d(X))` (large-field
>   suppression)
>
> then `A_{k+1}` satisfies the same bounds (with `g_{k+1}` adjusted
> per the running coupling) at scale `a_{k+1}`, with **the same
> constants**.

The proof is via:
- Block-spin integration: integrating out modes between `a_k` and
  `a_{k+1}` produces a new effective action.
- Cluster expansion of the resulting integral (similar to F3 but at
  a different scale).
- Bound on the small-field part: Gaussian approximation + 1-loop
  corrections.
- Bound on the large-field part: super-polynomial profile (per
  `YangMills/ClayCore/LargeFieldDominance.lean`).
- Combination via convexity / Hölder's inequality.

### 3.2 Project-internal statement

In the project's notation (from
`YangMills/P3_BalabanRG/CorrelationNorms.lean` etc.):

```lean
theorem balabanRG_inductive_step
    (k : ℕ) (g_k : ℝ) (hg_k : 0 < g_k) (hg_k_small : g_k < g_critical)
    (A_k : EffectiveAction k)
    (h_sf : SmallFieldBound A_k g_k κ E_0)
    (h_lf : LargeFieldBound A_k g_k κ p_0) :
    ∃ (A_{k+1} : EffectiveAction (k+1)) (g_{k+1} : ℝ),
      0 < g_{k+1} ∧
      g_{k+1} = g_k - b_0 · g_k³ + O(g_k⁵) ∧  -- one-loop running
      SmallFieldBound A_{k+1} g_{k+1} κ E_0 ∧
      LargeFieldBound A_{k+1} g_{k+1} κ p_0
```

### 3.3 Formalisation cost (rough estimate)

| Component | Estimated LOC | Status |
|---|---|---|
| Block-spin integration setup | ~300 | not started |
| Cluster expansion at scale (similar to F3 but parameterised by k) | ~500 | partly via F3 work |
| Small-field bound (Gaussian approx + 1-loop) | ~400 | not started |
| Large-field bound (super-polynomial) | ~200 | partly in `LargeFieldDominance.lean` |
| Combination via convexity | ~150 | not started |
| Iterative composition (apply over k = 0, 1, ..., N) | ~100 | not started |
| Continuum limit step (k → ∞ + RG fixed point) | ~200 | overlap with Branch VII |
| **Total** | **~1850 LOC** | mostly open |

Comparable to **2-3x the F3-Mayer scope**. Largest single Lean
formalisation in the project.

---

## 4. Retirement of Experimental axioms

Per `EXPERIMENTAL_AXIOMS_AUDIT.md`, the project has 14 axioms in
`YangMills/Experimental/`. Of these:

- **7 generator-data axioms**: easy retire (~250 LOC), unrelated to
  Bałaban RG.
- **1 smuggling axiom** (`lieDerivReg_all`): needs reformulation,
  not retirement.
- **6 hard-retire axioms**: `dirichlet_lipschitz_contraction`,
  `hille_yosida_core`, `poincare_to_variance_decay`,
  `variance_decay_from_bridge_and_poincare_semigroup_gap`,
  `gronwall_variance_decay`, `matExp_traceless_det_one`. **All six
  are Bałaban-RG-adjacent**.

Specifically, the 6 hard-retire axioms support:
- The semigroup theory needed for the Markov-chain interpretation of
  block-spin RG.
- The Beurling-Deny contraction needed for Dirichlet-form arguments
  in the small-field bound.
- The variance-decay framework that connects spectral-gap estimates
  to L²-decay of correlations.

**A successful Branch II closure would retire all 6 of these
axioms** as part of the natural development of the Bałaban
framework. This is a major epistemic gain — it would reduce the
project's axiom count from 14 to ~8 (the generator-data + the
matExp lemma).

---

## 5. Recommended order of attack

If the project ever pursues Branch II seriously:

### Phase A — Foundation (3-6 months)

1. **Mathlib-level work**: formalise C₀-semigroup theory, Krein-Rutman
   theorem, Beurling-Deny criteria for Dirichlet forms, Bochner-style
   integration on Lie groups. **All as Mathlib upstream PRs**.
2. **Retire the 6 hard-retire axioms** as the Mathlib infrastructure
   lands.

### Phase B — Bałaban setup (6-12 months)

3. **Formalise the block-spin RG** at the level of effective actions:
   `EffectiveAction k`, block-spin map, iteration.
4. **Small-field bound**: prove the Gaussian approximation with
   one-loop corrections at each scale.
5. **Large-field bound**: prove the super-polynomial suppression
   (extending `LargeFieldDominance.lean`).

### Phase C — Inductive step (6-12 months)

6. **Prove the one-step RG induction** combining small-field and
   large-field bounds. This is the analytic boss of Branch II.
7. **Iterate to all scales**: prove uniform-in-k bounds.

### Phase D — Continuum + Clay (3-6 months)

8. **Connect to Branch VII**: the uniform Bałaban bounds give the
   `m_lat(N) / a(N)` convergence needed by `HasContinuumMassGap_Genuine`.
9. **Connect to Branch III**: combined with reflection positivity,
   the Bałaban bounds verify the OS axioms.
10. **Final assembly**: produce `ClayYangMillsPhysicalStrong_Genuine`
    via the Bałaban path, complementary to (and stronger than) the
    F3 path.

### Total estimate

**~24-36 months of sustained Lean work** by a single agent, or
12-18 months with parallel agents (Codex daemon + multiple human
contributors). This is **the most ambitious branch** and the
closest to literal Clay closure.

---

## 6. Honest difficulty assessment

The Bałaban framework is **the hardest single mathematical problem
in current constructive QFT**. Critics have raised specific
concerns:

- **Large-field control**: Bałaban's CMP 122 large-field argument
  uses a super-polynomial profile that some experts find
  insufficiently rigorous at the boundary scales. (Documented in
  `YangMills/ClayCore/LargeFieldBound.lean` line 23-26.)
- **Inductive constants**: Bałaban's iteration controls constants
  step-by-step; some experts note that the constants compound in
  ways that may not give uniform bounds at all scales.
- **SU(N) generality**: Bałaban's published proofs cover SU(2)
  carefully; SU(3) and beyond are sketched. Full SU(N≥3) treatment
  is unclear from the literature.

**These are open mathematical questions**, not just formalisation
issues. Branch II's Lean formalisation could either:
- Confirm Bałaban's argument holds for all SU(N≥2) (the optimistic
  case).
- Surface the specific gaps that critics identify (the pessimistic
  case).

Either outcome is **a significant contribution to mathematical
physics** — formalising Bałaban's argument is itself novel work
beyond what any human team has accomplished.

---

## 7. Coordination with other branches

Branch II is **complementary to**, not competitive with, Branches
I (F3) and III (RP):

- Branch I (F3) gives lattice mass gap at small β. **Branch II
  generalises** this to arbitrary β via the multi-scale framework.
- Branch III (RP) gives lattice mass gap via spectral gap of
  transfer matrix. **Branch II provides** the uniform-in-scale
  control needed to take the continuum limit.
- Branch VII (continuum) defines the genuine continuum predicate.
  **Branch II provides** the witness via Bałaban's continuum-limit
  control.

The Clay closure is the **conjunction** of these branches. Branch
II is the longest-horizon piece.

---

## 8. References

- Bałaban, *Renormalization group approach to lattice gauge field
  theories*, CMP **109** (1986), 249-301.
- Bałaban, *Renormalization group methods in lattice gauge theory*,
  in *Constructive Quantum Field Theory II*, Proc. NATO ASI (1988).
- Bałaban, *Large field renormalization. I. The basic step of the
  RG*, CMP **116** (1987), 503-543.
- Bałaban, *Large field renormalization. II. Localization,
  exponentiation, and bounds for the R operation*, CMP **122**
  (1989), 355-392.
- Bałaban, *A low-temperature expansion for classical N-vector
  models*, CMP **167** (1995), 103-154.
- Magnen, Rivasseau, Sénéor, *Construction of YM_4 with an infrared
  cutoff*, CMP **155** (1993), 325-383.
- Federbush, *On the quantum Yang-Mills problem*, in *Constructive
  Quantum Field Theory II* (1988) — alternative approach with similar
  difficulty.

---

## 9. What Cowork can do for Branch II in this session

**Limited — this is genuinely the long-horizon branch.** What's
already produced:
- This blueprint identifying scope, mathematical content, retirement
  opportunities, and recommended order.

What Cowork could additionally produce in future sessions:
- **`BLUEPRINT_BalabanInductiveStep.md`**: detailed mathematical
  outline of the inductive step itself, with Lean signature sketches.
- **`YangMills/L2_Balaban/EffectiveAction.lean`**: scaffold for the
  effective-action structure with sorries.
- **Audit pass over `YangMills/ClayCore/BalabanRG/`**: identify
  what's there, what's stubs, what's substantive.

But the **substantive Lean work** — the actual proofs of the
small-field bound, large-field bound, and inductive step —
requires either:
- A dedicated multi-month Codex effort.
- Collaboration with a human expert in constructive QFT.

Branch II is **deferred for execution** but **prepared
strategically** by this blueprint. Cowork commits to writing the
inductive-step blueprint in a future session if Lluis approves.

---

## 10. Action items

For Lluis (decision pending):
- [ ] Approve Branch II as a long-horizon work area for the project.
      This is a decade-scale commitment but produces the canonical
      Clay closure.
- [ ] Decide whether Branch II should be pursued in parallel with
      Branches I, III, VII (more breadth, less depth) or after
      they close (sequential focus).

For Cowork agent (future sessions):
- [ ] Write `BLUEPRINT_BalabanInductiveStep.md` detailing the
      inductive step.
- [ ] Audit `YangMills/ClayCore/BalabanRG/` content vs claims.
- [ ] Identify the 3-5 most leveraged Mathlib upstream PRs that
      would unblock multiple Bałaban-adjacent retirements.

For Codex (long-term, if Branch II is approved):
- [ ] Phase A → D per §5 above.

---

## 11. Summary

Branch II (Bałaban RG) is the **historical and most rigorous** path
to Clay-Millennium-grade Yang-Mills. It is **massive in scope**
(~24-36 months of sustained Lean work), **strategically critical**
(retires 6 of the project's 14 Experimental axioms), and **the
canonical complement** to Branches I, III, VII.

Cowork has prepared this blueprint as long-horizon strategic prep.
The actual execution is **deferred** but the framework, scope, and
order of attack are now documented. When Lluis approves pursuing
Branch II seriously, the project has a starting roadmap.

Branches VII (continuum) and III (RP) remain Cowork's near-term
focus.

---

*Blueprint complete 2026-04-25 by Cowork agent. Branch II is
long-horizon prep; near-term Cowork attention stays on Branches
VII and III.*
