# Directional-mask cold gate: live checkpoint

This is a launch record, not a compiler verdict or a seal.

- Source: 74fc4f4dcd115558de6cf882d17540fe57d9bd27.
- Published notebook checkpoint: 43814351678798dc05c5e660fe6cc14ef8ac8458.
- Runner revision: neumann-directional-masks-promoted-cold-v1.
- Colab account visually confirmed: lluiseriksson@gmail.com.
- Runtime configured CPU/high RAM, no GPU; UI reports 50.99 GB total RAM.
- The security dialog was explicitly confirmed once; cell execution count is 1.
- Actual cell output: HASH_GATE=PASS.
- Actual start: 2026-09-06T23:10:22.032781+00:00; launcher PID 4007.
- Runtime hostname e71af114d3fe. At the first remote log inspection, pinned
  Mathlib/cache stages had exit0 and directional_masks_focal had started.
- No repeat of the cell, no project build-output restoration, no exploratory CI.

Required next observation is the recorded stage or final status, not an
inference from elapsed time. Use the paths in
NEUMANN-DIRECTIONAL-MASKS-COLD-20260907.md to preserve and independently
verify original evidence before any selective retirement of PRE-VALIDATION.
The previous wrap/flat runtime was already deleted; do not reconnect it.

Prepared during the cold gate, NOT added to its queue:
tmp/NeumannRectangleFlatMaskedActionDraft.lean. One named theorem composes
the actual flat internal-bond Laplacian with incoming/outgoing rectangle
masks, retaining full-period sides direction by direction, both inverse
spacing factors, and the literal flat physical operator. No integer boundary
identification, carrier choice or regional inverse is asserted. It remains
PRE-VALIDATION and must first run as a separately parent-gated HOT diagnostic
after the current cold evidence has passed independent preservation.

This project-specific rewrite cites the three named project theorems. It is
not a pure Mathlib inference problem; extract a minimal repro only if its
first actual compiler error belongs to a project-free proof step.

Counters unchanged: 20/41, TermSource=0, window15 not attained.

## Separately prepared HOT contract, not launched

Draft source checkpoint f2196b046117a59b9d4d1717887bc127fa34690f.
Templates tmp/colab_neumann_rectangle_flat_masked_action_hot_template.py and
tmp/verify_neumann_rectangle_flat_masked_action_hot_template.py deliberately
keep parent archive/review/output hashes and executable-runner hash unset.
The unpinned producer is tested to reject execution before doing any work.
Do not fill these fields from a successful prefix or predicted output hash.

The bounded queue has eight stages: exact base HEAD, Mathlib pin, Lean/Lake
versions, clean-before, the two actual imported prerequisites, the one-name
physical draft, clean-after. Its parent is this same directional-mask cold
checkout. The prerequisite step may build the already sealed flat action
incrementally; it does not restore project outputs from another checkout.
One physical output, one requested axiom declaration, original statement and
proof bytes from the draft Git object. A pure Mathlib repro is not claimed.

The independent reader checks exact commands, stage order, source/ref hashes,
parent review, original logs, child exits, output/file sets and exact audit
coverage. Tests also inspect the actual producer's AST against those commands.
Synthetic fixtures: valid1, rejected11, first child failure preserved1,
additional exact-audit coverage rejections3. Measured local check:
exit0,0.2971324s,24121344 observed peak RSS, no pool/compiler/network build.
These fixtures test instrumentation only, not the new mathematical statement.
