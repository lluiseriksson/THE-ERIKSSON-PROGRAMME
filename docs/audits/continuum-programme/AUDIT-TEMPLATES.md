# Executable audit templates: SU2, CONT-C0, CONT-C1

Historical registration base: `7c6aaab2f67fd5b9c4a23c45bbffebf476ef221a`
Core integration baseline: **8463 jobs at `7460e035`**  
Protocol: `BLIND-AUDIT-PROTOCOL.md`

Every instantiated manifest records its own producer SHA, observed public-main
SHA, and UTC observation time. The template base is historical context only.

The lane names are `SU2`, `CONT-C0`, and `CONT-C1`. The `CONT-` prefix avoids
collision with the repository's existing C1-C6 paper-lane charters.

## What the executable judge guarantees

`audit_lane_manifest.py` does not decide mathematics by keyword. It enforces
the audit contract around the mathematical decision:

1. the exact registered checks for the chosen lane are present, with no
   unregistered substitutions;
2. `PASS` has evidence, `FAIL` has a finite witness, and `BLOCKED` names the
   missing datum;
3. producer refs and SHAs are both full and optionally resolve to the same Git
   object;
4. file evidence stays inside the repository and an asserted SHA-256 matches;
5. no claim may be `PASS` while producer ref/SHA are absent;
6. a `CONT-C1` pass requires every constant to have an explicit dependency and
   validity-domain table;
7. a `CONT-C0` pass requires the actual regulator family, topology, tightness,
   uniqueness, and nontriviality entries;
8. an `SU2` pass requires explicit Haar/character conventions, reflection
   operations, and the full gluing/product-measure identity;
9. a module integrated into `YangMillsCore` fails the house gate unless its
   measured job count is strictly greater than **8463**.
10. a producer hypothesis retyped by a lane must have a compiled adapter that
    consumes the actual producer declaration at the load-bearing argument;
    an `rfl` restatement or prose-only correspondence is not an anti-drift
    certificate.

Structural `PASS` of a manifest means the record is complete and internally
eligible for its recorded verdicts. It does not turn its mathematical
`BLOCKED` entries into passes.

## Frozen invocation

```text
python docs/audits/continuum-programme/audit_lane_manifest.py \
  docs/audits/continuum-programme/templates/SU2.json \
  docs/audits/continuum-programme/templates/CONT-C0.json \
  docs/audits/continuum-programme/templates/CONT-C1.json \
  --verify-ref --json
```

Initial result: all three manifests are structurally `PASS`; their mathematical
counts are respectively `BLOCKED=11`, `BLOCKED=13`, and `BLOCKED=11`, because
no public producer ref/SHA or PR exists.

## SU2 lane

Template: `templates/SU2.json`.

The load-bearing test is `SU2-2G-GLUING`. If a reflected form is defined on
pairs of halves, the audit requires:

- a full-configuration assembly map and inverse;
- an exact account of shared/site or disjoint/bond boundary variables;
- equality of the product-Haar integral after reindexing;
- equality of the Wilson weight with the two half factors and every crossing
  plaquette;
- an exact multiplicity/counting proof.

The acceptance tolerance for this identity is **exact equality**. A `10^-12`
finite `Z_2` check is useful falsification evidence but is not proof and has no
transfer rule to `SU(2)`.

The remaining checks force one convention table:

- Haar total mass and left/right/inversion invariance;
- matrix-coefficient and character orthogonality, including dimension factors;
- trace and Wilson-action normalisations;
- link orientation, path-order reversal, group inverse/adjoint, and
  antilinearity;
- coefficient sign and convergence;
- arbitrary complex Gram-form positivity, not a real or diagonal slice.

If the SU2 lane introduces a local cut/action/kernel interface, its audit
oracle must also apply a producer theorem through that exact local interface.
Merely repeating the kernel's type does not show that the lattice Wilson
action or `GaugeConfig` gluing consumes it.

A result restricted to real observables on one slice is audited at that scope.
It fails an advertised full OS-positivity or reconstruction headline even if
the restricted theorem is true.

## CONT-C0 lane

Template: `templates/CONT-C0.json`.

The template separates the questions that are most often conflated:

```text
precompact/tight family
        |
        v
subsequence exists  --[separate uniqueness proof]--> full-family convergence
        |
        v
candidate limit --[separate scale/nontriviality tests]--> continuum theory claim
```

The following are registered `FAIL` witnesses when present:

- the candidate is an arbitrary chosen functional or a constant family;
- convergence to `L` is assumed in a hypothesis used to prove convergence to
  `L`;
- the topology does not carry the claimed fields/observables;
- only a subsequence is obtained but the headline says full limit;
- uniqueness is assumed or omitted;
- lattice units are retained with no physical scale;
- regulator-dependent counterterms are unnamed;
- no observable distinguishes the limit from zero, Gaussian/free, constant, or
  ultralocal alternatives as appropriate.

Compactness alone is not promoted to the Clay existence requirement; the
official Clay description expressly excludes that move without properties of
the limit.

Any locally named convergence, tightness, or nontriviality premise needs a
typed consumer of the actual regulated-state producer. A theorem that merely
accepts `HasWeakLimit`, `UniformlyTight`, or the desired positive variance as
an input is audited as transport/obligation, not as a construction of it.

## CONT-C1 lane

Template: `templates/CONT-C1.json`.

Every load-bearing constant gets one row with:

```text
name | definition | units | source locator | validity domain
depends on:
  a | lattice extent | physical volume | UV cutoff | IR regulator
  bare coupling | renormalised coupling | observable support | renormalisation scale
uniform in: [...]
```

Every dependency cell must be literal `yes` or `no` before a lane claim can be
`PASS`; `unknown` is `BLOCKED`. The audit treats a constant's validity domain
as part of the constant. Thus a displayed value independent of volume is not
volume-uniform if the admissible coupling/support/domain shrinks with volume.

For a transfer eigenvalue or lattice decay rate `r`, the physical energy
comparison must use the declared convention, for example
`E = -a^{-1} log r`. A positive number in lattice units is not a positive
continuum mass unless the rescaled lower bound remains positive uniformly
through the stated regulator limits.

## House checks reused, not duplicated

For every producer checkout, run:

```text
python scripts/check_module_prose.py <each-new-Lean-module>
python scripts/check_consistency.py
python scripts/source_db.py verify
lake build YangMillsCore
lake env lean oracle_check.lean
```

If the artefact is not integrated into the core, the job-count check is
`not_applicable`, not a pass. If it is integrated, the job count must be
strictly greater than 8463. The output and tool versions must be committed or
hashed in the audit report.

The template itself was exercised against an already published module:

```text
python scripts/check_module_prose.py YangMills/OS/SpatialReflection.lean
```

Result at the audit base:

```text
YangMills/OS/SpatialReflection.lean            OK

modules checked: 1  failures: 0
```

The consistency and canonical source-catalog checks also returned:

```text
Zero sorry in Lean source; zero axioms in the verified-core tree
OK: 9 catalog file(s), no structural errors
```

These green checks validate the reusable instruments, not a future producer
artefact.

## Clean-checkout procedure for a producer PR

1. Record `git ls-remote` output, PR URL, head ref, full head SHA, base SHA,
   UTC time, and the simultaneously observed public-main SHA.
2. Clone the public repository into a new empty temporary directory; checkout
   the producer SHA detached.
3. Hash every load-bearing input before executing it.
4. Copy the relevant template to a new immutable audit manifest; do not edit
   the template in place.
5. Run the lane-specific mathematical checks, then the house checks above.
6. Record one verdict per check. `FAIL` needs the smallest reproducible witness;
   `BLOCKED` needs the exact absent datum.
7. Validate the completed manifest with `--verify-ref`.
8. Immediately rerun `git ls-remote` for producer and public `main`. If the
   producer moved, rerun or stamp the report obsolete with the delta file list.
9. Publish a separate report naming the snapshot triple, producer SHA, and
   manifest hash. Do not merge the producer PR.

## Current public-ref witness

The current three lane verdicts are **BLOCKED** because the refs do not exist,
not because they point at the audit base. The authoritative command is:

```text
git ls-remote --heads origin \
  refs/heads/codex/su2-wilson-reflection-positivity \
  refs/heads/codex/continuum-c0 \
  refs/heads/codex/continuum-c1
```

At 2026-07-30 Europe/Stockholm it produced no output. The open-PR inventory
also contained none of those heads. A later artefact supersedes this fact only
with a new timestamped remote query and a new audit report.
