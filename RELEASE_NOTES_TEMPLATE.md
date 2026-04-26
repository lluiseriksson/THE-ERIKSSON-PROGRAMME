# RELEASE_NOTES_TEMPLATE.md

**Audience**: Codex daemon (or any agent) that bumps a version and
needs to append a release-note entry to `AXIOM_FRONTIER.md`.

**Purpose**: standardised template ensuring every release-note entry
contains the same core fields. Consistency makes the file scannable
and the audit verifiable.

---

## Where to use

When bumping the project's version (e.g. v1.85.0 → v1.86.0), prepend
a new entry to the top of `AXIOM_FRONTIER.md` using the template
below. The file is append-only at the top; older entries are never
modified.

---

## Template

Copy the section below verbatim and fill in the fields marked `<...>`.
Delete unused optional sections.

```markdown
# v<X>.<Y>.<Z> — <one-line title in present tense, no trailing period>

**Released: <YYYY-MM-DD>**

## What

<1-2 sentences describing the artifacts added or modified. Mention
the file path(s) explicitly. Avoid jargon-only descriptions —
include the mathematical or structural intent.>

<If new declarations: list them with `    name1`, `    name2` etc.,
indented 4 spaces. If a structure with multiple fields was added,
list the structure name only and describe the field set in prose.>

## Why

<1-2 sentences on what mathematical or structural goal this advances.
Reference the relevant blueprint, constraint contract priority,
finding, or roadmap item.>

<Indicate whether this release moves a percentage bar in the
README. If yes, state the bar(s) and the delta. If no, write
"No percentage bar moves." and explain what the release contributes
(packaging, scaffolding, infrastructure, etc.).>

## Oracle

Build:

    lake build YangMills.<RelevantModule>

Pinned traces:

    <theorem_or_def_name_1>
      [propext, Classical.choice, Quot.sound]

    <theorem_or_def_name_2>
      [propext, Classical.choice, Quot.sound]

    <... 2-5 representative declarations from this release ...>

No `sorry`. Non-Experimental Lean axiom count remains 0.

<If for any reason `lake build` was not run successfully on the
full library, document this — e.g. "Full-library check note: lake
build YangMills was started but exceeded the local 15-minute timeout;
the module-level build above is the pinned verification.">

---

```

---

## Field-by-field guidance

### Title

Present tense, no period. Examples that work:
- "exponential KP series prefactor for F3 counts" ✓
- "physical d=4 exponential F3 correlator endpoint" ✓
- "lattice-animal plaquette graph scaffold" ✓

Avoid:
- Past tense ("Added X") ✗
- Trailing period ✗
- Versioned references ("v1.85.0 stuff") ✗

### Released date

ISO format `YYYY-MM-DD`. Use the date the commit lands, not the
date of writing (if different).

### What

Always include:
- The Lean file path that was modified or created.
- The list of new declaration names (indented 4 spaces).

For pure-edit releases, describe the edit and reference the
declarations it affected.

For releases that touch multiple files, list each file's
contributions separately.

### Why

Always include:
- The strategic motivation (which blueprint / contract priority /
  finding does this advance).
- The percentage-bar status (moves what bar by how much, or
  doesn't move).

For substantive releases, describe what mathematical content was
added (not just "added theorem X" but "added the bound X ≤ Y · Z
for ...").

For canary releases (ergonomic accessors, mono_dim variants, etc.),
acknowledge that as such ("This is API ergonomics, not new
mathematical content").

### Oracle

Always include:
- The exact `lake build` command needed.
- 2-5 pinned `#print axioms` traces. Choose representative
  declarations: a structure constructor, a key theorem, an
  endpoint.
- The standard line: "No `sorry`. Non-Experimental Lean axiom count
  remains 0."

If the full-library `lake build YangMills` was not run (e.g. due to
timeout or explicit deferral), document that. The module-level
build is the canonical pinning.

---

## Examples (good)

### Substantive release (moves a bar)

```markdown
# v1.50.0 — L2.6 main target closed

**Released: 2026-04-22**

## What

Added `YangMills/ClayCore/SchurL26.lean` proving the character inner
product

    sunHaarProb_trace_normSq_integral_eq_one :
        ∫ U, |tr U|² ∂(sunHaarProb N) = 1

via the Schur orthogonality of matrix coefficients on SU(N).

## Why

Closes the L2.6 main target. This is the L1→L2 interface statement
that every downstream cluster-expansion bound consumes.

Bars move: L2.6 85% → 100%, L2 42% → 50%, OVERALL 40% → 48%.

## Oracle

Build:

    lake build YangMills.ClayCore.SchurL26

Pinned traces:

    sunHaarProb_trace_normSq_integral_eq_one
      [propext, Classical.choice, Quot.sound]

No `sorry`. Non-Experimental Lean axiom count remains 0.
```

### Canary release (no bar movement)

```markdown
# v1.74.0 — mono_count_dim application canaries for combined F3 packages

**Released: 2026-04-25**

## What

Added direct mono_count_dim application accessors for
`PhysicalShiftedF3MayerCountPackage` in
`YangMills/ClayCore/ClusterRpowBridge.lean`:

    PhysicalShiftedF3MayerCountPackage.mono_count_dim_apply
    PhysicalShiftedF3MayerCountPackage.mono_count_dim_dim
    PhysicalShiftedF3MayerCountPackage.mono_count_dim_C_conn

## Why

No percentage bar moves. This is API ergonomics extending the
existing `mono_dim_apply` pattern to combined Mayer+Count packages,
so downstream code can lift dim by `+ k` without re-deriving.

## Oracle

Build:

    lake build YangMills.ClayCore.ClusterRpowBridge

Pinned traces:

    PhysicalShiftedF3MayerCountPackage.mono_count_dim_apply
      [propext, Classical.choice, Quot.sound]

No `sorry`. Non-Experimental Lean axiom count remains 0.
```

### Infrastructure / scaffolding release (no bar, but substantive)

```markdown
# v1.85.0 — lattice-animal plaquette graph scaffold

**Released: 2026-04-25**

## What

Added `YangMills/ClayCore/LatticeAnimalCount.lean` (~99 LOC):

    siteLatticeDist_symm
    plaquetteGraph
    plaquetteGraph_adj_siteLatticeDist_le_one
    plaquetteGraph_adj_of_ne_of_siteLatticeDist_le_one
    plaquetteGraph_isChain_of_nodup_siteLatticeDist_isChain

This is the `SimpleGraph` form of the `PolymerConnected` adjacency
predicate, with the chain lemma bridging nodup site-distance lists
to graph chains.

## Why

No percentage bar moves. This is F3-Count Priority 1.2 scaffolding
(per `CODEX_CONSTRAINT_CONTRACT.md` §4 and `BLUEPRINT_F3Count.md`).
The remaining work is the BFS-tree count theorem and packaging.

## Oracle

Build:

    lake build YangMills.ClayCore.LatticeAnimalCount

Pinned traces:

    siteLatticeDist_symm
      [propext, Classical.choice, Quot.sound]

    plaquetteGraph_adj_siteLatticeDist_le_one
      [propext, Classical.choice, Quot.sound]

    plaquetteGraph_isChain_of_nodup_siteLatticeDist_isChain
      [propext, Classical.choice, Quot.sound]

No `sorry`. Non-Experimental Lean axiom count remains 0.
```

---

## Examples (avoid)

### Bad: missing oracle section

```markdown
# v1.86.0 — added some helpers

Added some helper lemmas for the Mayer expansion.
```

Why bad: no file path, no declaration names, no oracle traces, no
"why", no claim about axiom count.

### Bad: vague "why"

```markdown
## Why

Useful improvements.
```

Why bad: doesn't connect to any blueprint / priority / finding;
doesn't state bar movement.

### Bad: untracked declarations

```markdown
## What

Refactored the Mayer interpolation file.
```

Why bad: which file? Which declarations changed? Did the public API
move?

---

## Maintenance

This template should be revised when:

- A new field becomes useful (e.g., a "downstream impact" line if
  releases start affecting many consumers).
- The release-notes format itself is restructured (e.g.,
  consolidation with `README.md` "Last closed").

---

*Prepared 2026-04-25 by Cowork agent.*
