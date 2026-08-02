# INC-SPATIAL-SYMWEIGHTED-GATE-005

Date: 2026-08-01

## Intended campaign

Run the symWeighted judge in normal and optimized Python in two fresh,
independent Colab clones at the same immutable repository SHA, with semantic
logs, shell/persisted exit codes, full JSON validation, and cross-clone hash
comparison.

The remote object was verified before cloning:

- repository SHA `2c009f607a6e0747f69effc0378b577b0f853ffb`;
- judge SHA-256
  `a95e66da0ee527b1776ceb3d13d83760d1fd88cc9227ebea668a2b98ca1946cf`;
- versioned harness SHA-256
  `668681a7f29e2a228b8036be31472a0203d56edfd7f9de9a8753dc0449bc5a65`.

No GPU was requested or opened.  No Lean or other campaign shared the runner.

## Completed units

`clone-a` checked out the exact SHA in its own temporary root.

- normal: wrapper PID 2166, child PID 2167, 275.045140011 s, shell exit 0,
  persisted exit 0;
- optimized: wrapper PID 3264, child PID 3265, 269.472493344 s, shell exit 0,
  persisted exit 0.

Both modes returned fresh one-line PASS JSON with all four counters equal to
5460.  Their hashes agree:

- log `a5bc995539a70b8e071cf71bd568d956248e978a1647621c96e4d415f2e322ba`;
- stderr (empty)
  `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`;
- exitcode
  `9a271f2a916b0b6ee6cecb2426f0b3206ef074578be55d9bc94f6f3fe3ab86aa`.

`clone-b` used a different temporary root, cloned afresh, and checked out the
same SHA.  Its normal mode passed: wrapper PID 4400, child PID 4401,
268.112386983 s, both exit codes 0, with the same three hashes and all four
counters equal to 5460.

## Interruption

Immediately after `clone-b` normal completed, the Colab cell ceased running.
The visible output contains no rejection message, traceback, FAIL line, or
`clone-b` optimized record.  The UI no longer displayed a connected Python
runtime.  No literal platform rejection was shown, so this incident assigns no
cause such as session excess or compute-unit exhaustion.

There is no final certificate artifact and the two-clone gate remains open.
The tab was closed rather than kept connected during preparation.

## Recovery contract

The recovery runner is preregistered to create a third, wholly fresh Colab
clone at the same SHA, run normal and optimized, validate the same fields, and
compare its output hashes to the complete `clone-a` witness above.  It does not
reuse either previous root or output.  Only a complete matching recovery run
can supply the second independent clone testimony.
