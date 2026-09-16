# C6d source-separated ambient Green cold gate checkpoint

Operational checkpoint only.  It is not compiler evidence.

- active notebook source commit: `5b126c7df529db45fb9049a7be0720ccd12507a0`;
- source object under test: `0ea023c1a3589365dcc41a89514d1bff26c01080`;
- runner checkpoint: `0001de1979f05505256c9e37d1519315724ee859`;
- runner revision: `c6d-source-separated-ambient-green-v3`;
- current queue: positive focal/audit, zero focal/audit, `YangMillsCore` root;
- current hard counters remain `20/41`, `TermSource = 0`.

Live v3 prefix measured after reopening the same retained runtime, without
reexecuting the cell:

- positive focal: exit `0`, `8757` jobs, `2757.210` seconds;
- positive audit: exit `0`, 15 allowed axiom readouts, `59.532` seconds;
- zero-depth focal: exit `0`, `8552` jobs, `55.076` seconds;
- zero-depth audit: exit `0`, 10 allowed axiom readouts, `47.327` seconds;
- `YangMillsCore` root: started and remains the only live stage.

This prefix is not a seal.  The root result and the packaged verifier remain
mandatory.

The source object predates the private `NeZero` repairs in
`21ef2f163438b2e0ba788def8a70a1680aa6ba82` and
`04da977a3810e42aab00087baa39b7ef226b7bb2`.  Therefore a root failure in
the old canonical ambient-completion consumer must be classified using its
literal first error; it must not invalidate a separately passing Green focal,
but it also cannot seal the Green brick because the cold queue contract
includes the root.

Fail-closed fallback already generated statically from `04da977a...`:

- candidate runner: `tmp/c6d_source_green_04da_candidate.py`;
- SHA-256: `8AC66FA1879503CDD7DD25F6BFF6825219269F489A0F074D985198EEE3AF09B7`;
- queue contract: 5 stages, 25 axiom blocks, `YangMillsCore` root.

The candidate is not published and must be regenerated from the actual seal
SHA if the four Green PRE-VALIDATION marks are removed before the retry.

Parallel static work, which does not affect the frozen source object under
test, is durably published at
`8c551546796b8006752b76b51fbfd63476d9b008`.  That checkpoint adds only the
next independent PRE-VALIDATION pair
`BalabanCMP99SourceActiveRegionTerminalBlockDiameter` plus its audit and root
import.  Its two-file textual overlay guard passes.  It is not compiled and
must not be counted or sealed before its own Colab gate.

On PASS: preserve archive plus executed notebook, run the exact verifier,
remove PRE-VALIDATION only from the four paths in
`tmp/c6d-source-separated-ambient-green-seal-paths.txt`, record the evidence,
and keep the hard counters unchanged.

On FAIL: preserve the first error and repair only it.  Do not infer a seal
from a focal-only prefix and do not rerun the same source.
