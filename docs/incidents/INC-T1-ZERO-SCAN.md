# INC-T1-ZERO-SCAN

**Status:** `T1_REPAIRED`; `V88_RERUN_AUDIT_IN_PROGRESS`
**Opened:** 2026-07-11  
**Committed state audited:** `b6748dd1dd80e983c3e7779d5d6a2dbf29830238`  
**Scope:** Surface Theorem computational control plane; no Part II Lean claim

## Decision

The committed statement “T1 VERIFIED; 78 lists, zero violations” is not accepted.
The repository currently contains both a zero-scan false green and live non-monotone
quadrature partitions. Numerical outputs that depend on those partitions remain in
maintenance until a clean rerun and supersession audit land.

This incident does **not** prove the Surface Theorem false. It falsifies the committed
instrumental claim and therefore withdraws the affected computation as terminal evidence.

## Takeover update (2026-07-11)

The scanner now resolves every target against its own directory, treats missing files and
fewer than 78 examined lists as fatal, and is exercised from both working directories by
the control-plane suite. Current result from both repository root and `scripts/`:

```text
node lists checked: 78 ; violations: 0
exit 0
```

T1 is therefore repaired. The incident stays open at the evidence level until the
independent v88 reruns, manifests, and T2–T7 audit are complete.

## Independent reproduction

From repository root:

```text
python scripts/test_monotone_nodes.py
node lists checked: 0 ; violations: 0
CONTRACT HOLDS: every partition strictly increasing.
exit 0
```

From `scripts/`:

```text
python test_monotone_nodes.py
node lists checked: 78 ; violations: 16
exit 1
```

The scanner resolves its target filenames against the process working directory, silently
skips every missing file, and accepts a zero scan. Invoking it from `scripts/` exposes the
second defect rather than curing the first.

## Live affected region families

The offending list is

```text
[r, 2, pi-r] = [1.2, 2.0, 1.9415926535...]
```

It occurs in region arrays consumed by nested `mp.quad` calls in:

- `scripts/cascade1_signed_minoration.py`;
- `scripts/cascade2_step0_eps.py`;
- `scripts/cascade3b_judges.py`;
- `scripts/cascade3_mirror_extraction.py`.

The 16 scanner hits arise because the same non-monotone partition appears in both axes and
several regions. They are code, not comments, deliberately decreasing delta samples, or
test-point tuples. No repair may merely sort the nodes: the replacement partition must be
the mathematically registered one used by the rerun.

## Executable quarantine

`tests/test_surface_monotone_contract.py` invokes the scanner from both repository root
and `scripts/`, requires at least 78 lists, requires zero violations, and requires identical
summaries. It is now a normal passing test; no expected-failure marker remains.

## Closure criteria

1. Resolve target paths from the scanner's own location, not the caller's directory.
2. Treat every missing target file as fatal.
3. Treat zero examined node lists as fatal and retain an explicit nonzero expectation.
4. Replace each live non-monotone partition from a pre-registered mathematical design;
   never auto-sort it.
5. Obtain identical nonzero-scan results from repository root and `scripts/`.
6. Reproduce T1 from a clean checkout on Linux and Windows.
7. Remove strict `xfail` and make T1 a normal passing control-plane test.
8. Rerun every dependent computation and commit manifests with hashes, environments,
   quarantine/supersession status, and reciprocal links.
9. Rejudge T2–T7 only from the newly manifested outputs.
