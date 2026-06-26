# Negative tests for creative formula candidates

Run these before promotion.

## Universal tests

1. Empty index: theorem must not discharge a source package only because the family is empty.
2. Singleton index: all constants should reduce to the expected one-term inequality.
3. Duplicate targets: two indices with same target must either be counted twice or require injectivity.
4. Zero denominator: every division by scale, gap, or coupling must have a positivity hypothesis.
5. Wrong metric direction: if source gives `d(Y) <= sum + n`, do not use it as `sum <= d(Y)`.
6. Source/Lean mismatch: every source family equality must be an iff or extensional equality.
7. Early norms: check whether triangle inequality destroys a cancellation the formula was supposed to preserve.
8. Constant hiding: reject `O(1)` if it absorbs a scale-dependent or volume-dependent factor.

## Verdict labels

- `killed`
- `needs_assumption`
- `toy_survives`
- `source_needed`
- `ready_for_lean_stub`
