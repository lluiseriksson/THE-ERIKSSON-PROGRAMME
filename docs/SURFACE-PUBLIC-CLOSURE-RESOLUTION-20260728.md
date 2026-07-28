# Surface public-closure resolution (2026-07-28)

## Question

An external re-verification of Surface branch commit `3596957b` reported
`3 failed, 697 passed`, with two unexpected failures attributed to source
anchors `0919aa10` and `1fed14e` allegedly lying outside the published Git
closure.

## Independent reproduction

A new full HTTPS clone was created from the public repository:

```text
git clone --no-local \
  https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME.git \
  C:\tmp\surface-public-clone-20260728-final2
git switch --detach origin/codex/surface-k2-kd-covariance-design
```

The detached checkout was exactly
`3596957bfe10c4aee28b8bc479ccbdde547f12c5`.  In that clone:

```text
git merge-base --is-ancestor 0919aa10 HEAD
# exit 0
git merge-base --is-ancestor 1fed14e HEAD
# exit 0
```

The two targeted tests then produced:

```text
python -m pytest -q \
  tests/test_project_state.py::test_repository_project_state_is_valid \
  tests/test_source_db.py::test_head_refs_prints_source_metadata_commit_anchors

2 passed in 1.76s
```

## Resolution

Both anchors are genuine ancestors of the published Surface branch.  Changing
them would corrupt accurate provenance, so no anchor was rewritten.  The
contrary result is consistent with an incomplete or stale Git object/ref view,
not with the public branch graph reproduced above.

This resolution is deliberately narrow.  It does not erase the external
desk's valid earlier findings about EOL-sensitive hashes and dependencies
missing from Git; those defects were repaired separately and remain recorded
in the audit history.
