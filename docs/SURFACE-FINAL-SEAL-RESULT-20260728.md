# Surface Theorem final seal (2026-07-28)

## Verdict

```text
G0 PASS
G1 REMOVED_FROM_TERMINAL_PAPER
G2 CERTIFIED
G3 CERTIFIED
G4 CERTIFIED
G5 CERTIFIED
G6 SEALED
Submission state READY_FOR_CLAIM_AUDIT
```

The executable final audit terminated with

```text
FINAL-SEAL PASS: terminal gates, manuscript, and PDF are present
```

It reconstructs the terminal prerequisites, the weak-main G2 terminal union,
and the closed-form anchor gate; it does not accept the board state or a
printed `PASS` as sufficient evidence.

## Reconstructed evidence

- v88 sanitation: five authoritative production/replay pairs.
- Low coupling: two `beta<=3` witnesses.
- Compact and edge covers: 3,651 bulk-beta boxes, 600,026 bulk-t boxes,
  170 left-edge beta boxes, and 410 right-edge beta boxes.
- Finite scaled left bridge: 912 beta intervals and 4,636 strict `t` rows,
  independently replayed.
- Moving right edge: the four-unit compact extension, 225 lower finite rows,
  375 upper finite rows, and the five-family half-line composition.
- High-beta weak lane: two adjacent 576-row covariance transcript pairs,
  exact relays, mirror/rest charges, all seams, and the promotion
  `G2_WEAK_TERMINAL_COVER_PROVED`.
- Closed-form normalization gate:
  `CLOSED_FORM_ANCHORS_PROVED`.
- Focused regression suite: 32 tests passed, including explicit LF/CRLF
  dependency-hash contracts and the general closure-board validator.

The old `audit_surface_g2_terminal_cover.py` sharp-positive composition is
superseded and is not imported by the final seal.  Its historical transcript
hashes correctly reject the normalization repair.  The canonical test now
targets `audit_surface_g2_weak_terminal_cover.py`.

The canonical weak transcripts record both their LF repository-blob and
Windows CRLF-checkout SHA-256 values in
`SURFACE-K2-WEAK-MAIN-COVARIANCE-RESULT-20260728.md`; Git EOL normalization
therefore cannot be mistaken for content drift.

## External refutation and portability repair

An external checkout refuted the first nominal seal at `97a9a7f2`.  Two
validators compared dependency hashes in an EOL-sensitive way, and the
moving-tail source recorded by the weak-main transcript was absent from the
Git tree.  Submission readiness was withdrawn while these defects were open.

Both validators now accept exactly the raw/LF/CRLF variants of unchanged
content and reject any other byte change.  The omitted module is versioned.
A clean detached LF worktree based on the repaired branch then passed the
focused tests, general closure validator, and complete final seal without
access to the shared worktree or untracked files.  See
`SURFACE-FINAL-SEAL-PORTABILITY-REPAIR-20260728.md`.

## Manuscript and build

The terminal manuscript contains the unconditional Surface Theorem and the
weak-main high-beta proof.  It has no `DO NOT SUBMIT` banner, unresolved
`[SLOT]`, undefined internal reference, or undefined citation.

The fresh two-pass pdfTeX build has 33 pages and records zero fatal errors,
undefined references, undefined citations, or overfull boxes.  Eight
representative pages, including the first pages, closure table, high-beta
proof, completion, and bibliography, were visually inspected without
clipping or overlap.

```text
TeX SHA-256
ebe578725f9ae049be059c1bc133b58a74b36819707c805b7afda799da609801

PDF SHA-256
e8cc61a1c370d941baff0ae9019dde4c0d528dbeb42f7c81b221667c1e67333e
```

The frozen worktree source checkpoint remained
`150f439ba30ac1ee915fc92e93ec0b4d708f4349`; publication is performed through
the isolated audit branch so that the shared dirty worktree is not moved.

## Margin-reporting discipline

The adaptive `GRID_COUNTS` and `WORST_LOWER` fields are execution diagnostics,
not analytic margins.  The preregistered floor-48 diagnostic refined all 157
grid-24 rows and improved every lower endpoint.  A separate non-gate grid-96
check improved the far critical row from approximately `-0.04989521` to
`-0.01502477`.  Neither diagnostic value is promoted as a uniform theorem
margin; the mathematical statement used by the relay is the certified strict
predicate `X_main>-1/20`.

The far fallback `X_main>-1/2` was preregistered and never activated.

## Independent-model scope

Claude Fable 5 High, using the explicitly selected `masterythief` profile,
independently audited the lane ownership and confirmed that
K4/S1'''/S2''' belong only to the superseded sharp-positive research route.
That conclusion was then checked directly against the imports and algebra of
the canonical weak audit.  A later bounded Fable manuscript audit timed out;
no result from that call was accepted or used in the first seal.

The separate external-audit branch subsequently completed a five-question
Fable 5 High adversarial mathematics audit: assembly identity, exact margin,
domain coverage, independent transcript sampling, and theorem statement all
passed.  Its transcript is preserved unchanged in
`scripts/audit_weak_main_math_transcript.txt`.  That mathematics pass did not
override the external executable failure; portability was restored only by
the code, packaging, and clean-archive rerun recorded above.
