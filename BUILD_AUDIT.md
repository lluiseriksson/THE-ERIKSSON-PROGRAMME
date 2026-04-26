# BUILD_AUDIT.md

**Author**: Cowork agent (Claude), build-config audit 2026-04-25
**Subject**: `lakefile.lean`, `lean-toolchain`, `lake-manifest.json`,
`YangMills.lean` (root entry file)
**Question**: can an external reviewer run `lake build YangMills`
end-to-end and reproduce the project's claims?

---

## 0. Bottom line

The build configuration is **simple, current, and reproducible**.
Mathlib is pinned via `lake-manifest.json` to commit
`07642720480157414db592fa85b626dafb71355b`. The Lean toolchain
is `leanprover/lean4:v4.29.0-rc6`, matching what `README.md` states.

**One substantive finding**: the root file `YangMills.lean` (190
lines, 188 imports) **does NOT import**
`YangMills.ClayCore.LatticeAnimalCount`. So a full
`lake build YangMills` will not compile the v1.85.0+ Priority 1.2
work. Codex's per-release oracle traces are based on
**module-level builds** (`lake build YangMills.ClayCore.LatticeAnimalCount`)
explicitly, not the full library build. This is reasonable for
in-flight work but should be addressed when Priority 1.2 closes.

---

## 1. `lean-toolchain`

```
leanprover/lean4:v4.29.0-rc6
```

Matches the `README.md` badge. Single-line file. Standard.

## 2. `lakefile.lean` (10 lines)

```lean
import Lake
open Lake DSL

package «YangMills» where
  -- add package configuration options here

lean_lib «YangMills» where
  -- add library configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "master"
```

**Observations**:

- Minimal Lake configuration. No custom build options.
- Mathlib pulled from `master` (no version pin in lakefile).
- Last touched 2026-03-12 (project inception). Stable since.

**Risk**: tracking Mathlib master means upstream breaking changes
can break the project's build at any time. The `lake-manifest.json`
pin (§3) provides stability but only if `lake update` is **not**
run.

## 3. `lake-manifest.json`

Pins all dependencies to specific commits:

- **mathlib**: `07642720480157414db592fa85b626dafb71355b` (specific
  commit on master)
- **plausible**: `e84e3e16aea6b72cc5d311ca1bb25caad417e162`
- **LeanSearchClient**: `c5d5b8fe6e5158def25cd28eb94e4141ad97c843`
- **importGraph**: `f207d9fcf0cef00ba79962a33ef156061914d9c7`
- (and presumably more — file is 3202 bytes total)

**Observations**:

- The manifest provides the actual reproducibility — anyone running
  `lake build YangMills` after a fresh clone will pull these
  exact commits.
- The Mathlib pin (`07642720`) is from 2026-03-12 (the file's
  mtime). Either Mathlib hasn't changed or no one has run
  `lake update` since project inception.
- **Important caveat**: the strategic docs claim "Mathlib master"
  — but the actual reproducibility is against the pinned commit,
  not master. README badge `Mathlib-master` is technically
  misleading; should read `Mathlib-pinned` or specify the commit.

## 4. `YangMills.lean` (root entry, 190 lines, 188 imports)

This is the file `lake build YangMills` resolves. It's a
comprehensive `import` list covering:

- All of `YangMills/L0_Lattice/` (~6 files)
- All of `YangMills/L1_GibbsMeasure/` (3 files)
- Most of `YangMills/L2_Balaban`, `L3-L8`, `P2-P8` (~80+ files)
- Most of `YangMills/ClayCore/` (~150+ files)
- Specifically: `YangMills.ClayCore.ClusterRpowBridge`,
  `YangMills.ClayCore.ConnectingClusterCountExp`,
  `YangMills.ClayCore.ConnectedCorrDecay`, etc. — all the v1.79+
  exponential frontier infrastructure

### 4.1 What is NOT imported

Spot-check finds:

- **`YangMills.ClayCore.LatticeAnimalCount`** (created v1.85.0,
  developed through v1.91.0 — Priority 1.2 active work area).
  **Not in `YangMills.lean`.**

This means:

- `lake build YangMills` will not compile `LatticeAnimalCount.lean`.
- `lake build YangMills.ClayCore.LatticeAnimalCount` (the explicit
  module-level build, mentioned in v1.85+ release notes) is the
  only way to verify it compiles.
- The full-library build will succeed even if `LatticeAnimalCount`
  has issues — those would only surface at the module-level build.

### 4.2 Why this is OK (for now)

- Codex's per-release oracle traces in `AXIOM_FRONTIER.md`
  explicitly cite the module-level build target. The release
  notes are honest about scope.
- Adding the import to `YangMills.lean` while the file is
  in-flight could destabilise the full-library build if
  `LatticeAnimalCount` ends up depending on something not yet
  in scope.

### 4.3 What to do at Priority 1.2 closure

When the F3-Count witness lands and `LatticeAnimalCount.lean`
stabilises, the import should be added to `YangMills.lean`. This
is a one-line edit but enables full-library verification of the
F3 chain.

Suggested addition (alphabetical within ClayCore):

```lean
import YangMills.ClayCore.LatticeAnimalCount
```

Estimated edit: 30 seconds.

## 5. CI scope reminder

Per `.github/workflows/ci.yml` (audited in
`REPO_INFRASTRUCTURE_AUDIT.md` §4), CI runs:

- `lake build YangMills.P8_PhysicalGap.BalabanToLSI` (one specific
  module)
- `scripts/check_consistency.py` (sorry detection)

CI does **NOT** run `lake build YangMills` (the full library) due
to GitHub Actions free-tier time limits. So:

- The full-library build is verified locally by Lluis (or by
  Codex's daemon environment), not by CI.
- The F3 frontier work in `LatticeAnimalCount.lean` is verified
  at the module level by Codex's per-commit oracle checks.
- An external reviewer cloning the repo and running
  `lake build YangMills` would compile the bulk of the project
  but **miss** the most-recent F3 work.

This is documented in `ci.yml` itself with the comment "IMPORTANT
— SCOPE: This job builds ONE narrow target".

---

## 6. Reproducibility checklist for an external reviewer

```bash
# 1. Clone
git clone https://github.com/lluiseriksson/yang-mills-lean.git
cd yang-mills-lean

# 2. Install Lean (uses lean-toolchain version)
curl -L https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y
export PATH="$HOME/.elan/bin:$PATH"

# 3. Build (uses lake-manifest.json pin for reproducibility)
lake exe cache get      # download Mathlib build cache
lake build YangMills    # build the bulk of the project (~30 min on a 2024 laptop)

# 4. Verify oracle of any specific theorem
echo 'import YangMills.ClayCore.SchurL26
#print axioms YangMills.ClayCore.sunHaarProb_trace_normSq_integral_eq_one' | lake env lean --stdin

# Expected output:
# 'YangMills.ClayCore.sunHaarProb_trace_normSq_integral_eq_one' depends on axioms:
#   [propext, Classical.choice, Quot.sound]

# 5. Verify F3 frontier (in-flight work, module-level build)
lake build YangMills.ClayCore.LatticeAnimalCount
echo 'import YangMills.ClayCore.LatticeAnimalCount
#print axioms YangMills.siteNeighborBallBoundDim_ternary' | lake env lean --stdin
# (after v1.91.0 lands — verify the concrete bound)
```

## 7. Findings summary

1. **README badge `Mathlib-master` is technically misleading**;
   actual reproducibility is via the pinned commit
   `07642720`. **Severity: low** (cosmetic). Suggested fix:
   change badge to `Mathlib-pinned` or include commit prefix.
2. **`LatticeAnimalCount.lean` not in `YangMills.lean` root**.
   **Severity: low** (acceptable for in-flight work; should be
   resolved at Priority 1.2 closure). Suggested action: one-line
   import addition when v1.92+ closes the witness.
3. **CI scope limited to one module** (already documented in
   `ci.yml` and `REPO_INFRASTRUCTURE_AUDIT.md`). **Severity: low**
   for current phase; should expand at F3 closure.

---

## 8. v1.91.0 acknowledgment (sidebar)

v1.91.0 just landed: "concrete ternary site-neighbor bound" — the
**7th consecutive predict-confirm cycle**. Closes §3.2 of the
Priority 1.2 roadmap by proving:

- `siteDisplacement_sq_le_one_of_siteLatticeDist_le_one`
- `siteDisplacement_mem_unit_of_siteLatticeDist_le_one`
- `siteNeighborBallBoundDim_ternary : SiteNeighborBallBoundDim d (3 ^ d)`

Combined with v1.88 lifting theorem, this gives the **explicit
plaquette-graph local branching bound `(3^d) · d · d`** (= 1296
for d=4). §3.2 is now **fully closed**. Next step: §3.3 BFS-tree
count theorem (the analytic boss).

---

*Build audit complete 2026-04-25 by Cowork agent.*
