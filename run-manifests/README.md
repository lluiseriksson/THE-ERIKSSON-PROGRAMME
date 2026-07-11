# Reproducible run manifests

This directory is the opt-in provenance layer for committed computational runs.
It does not decide whether a mathematical statement is exact, certified, or proved.

One run is one JSON file named `<run_id>.json`. The validator is:

```powershell
python scripts/validate_run_manifests.py
```

The bootstrap ended with the independently rerun T1 contract. CI now uses
`--require-nonempty`: an empty manifest directory is fatal.

Bootstrap is not a bypass for new evidence. CI compares each change against its Git base:
every added or modified `scripts/*transcript*.txt` or `scripts/*output*.txt` must already
appear as an `outputs[].path` in a committed manifest. Historical artifacts are not forced
into retroactive manifests merely because this layer was introduced later.

## Required shape (schema version 1)

```json
{
  "schema_version": 1,
  "run_id": "cascade-example-20260711T180000Z",
  "claim_scope": "Design-only example; no certificate claim.",
  "status": "current",
  "started_utc": "2026-07-11T18:00:00Z",
  "finished_utc": "2026-07-11T18:10:00Z",
  "command": ["python", "scripts/example.py"],
  "working_directory": ".",
  "script": {"path": "scripts/example.py", "sha256": "<64 hex>"},
  "environment": {
    "python": "3.12.10",
    "libraries": {"mpmath": "1.3.0"}
  },
  "inputs": [],
  "outputs": [
    {"path": "scripts/example_transcript.txt", "sha256": "<64 hex>"}
  ],
  "supersedes": [],
  "superseded_by": null,
  "quarantine_reason": null
}
```

## State rules

- `current`: the run is the live evidence for its declared scope.
- `superseded`: `superseded_by` names the replacement, and that replacement lists this
  run under `supersedes`.
- `quarantined`: `quarantine_reason` is mandatory. Quarantined output is preserved.

Every referenced repository file must exist and match its recorded lowercase SHA-256.
Absolute paths and `..` escapes are rejected. Supersession references must be reciprocal,
refer to committed manifests, and contain no cycles. The finish time cannot precede the
start time, the working directory must exist, the recorded command must name the hashed
script, and each committed output path has exactly one manifest owner.
