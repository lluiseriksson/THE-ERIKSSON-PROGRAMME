# One Commit, One Hypothesis

A productive commit should have one of these shapes:

## Type A — field discharge

```text
before: theorem ... (hfield : Field) ...
after:  theorem ... -- hfield supplied by named theorem/package field
```

## Type B — source promotion

```text
before: citation status = source_pending
after:  status = source_extracted with formula, assumptions, constants, dictionary,
        use_for, do_not_use_for, open_questions and Lean targets
```

## Type C — blocker sharpening

```text
before: "source theorem missing"
after:  exact missing lemma with source pages, symbols, quantifiers and the one Lean
        declaration it would feed
```

A patch that only adds downstream consumers is rejected unless it also performs
Type A, B or C.
