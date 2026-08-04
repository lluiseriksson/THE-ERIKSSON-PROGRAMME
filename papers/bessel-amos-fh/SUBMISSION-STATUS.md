# Submission status — Bessel fractional-order note

Date: 2026-08-04 (Europe/Stockholm)

## Decision

**NO-GO for submission as a new analytic theorem or as a `+6` paper.**

**READY only for circulation as a priority-corrected synthesis and
machine-checked alternative proof.**

The earlier v7 title and novelty framing are withdrawn. Duplicate filenames
such as `bessel_fractional_order_v7(1).pdf` do not create a new version and
must not be submitted.

## Active artifact

- Version: v8
- Title: *An Explicit Optimal-Domain Synthesis for Modified-Bessel Ratios: a
  Recurrence-Only Riccati Proof and Lean Verification*
- PDF: `../../output/pdf/bessel_fractional_order_v8.pdf`
- Pages: 11
- SHA-256:
  `93a32ec29889412a96eb3ed9e16377601a2065dbc6a642ff772fb2feeab20208`
- Frozen body commit: `699dab6668d212489ff56c776aaa74f9b32632d9`
- Freeze commit: `4be716a8`

## Reason for the hold

Garofalo, Proposition 8.8, already records the exact unit-shift threshold
`nu >= -1/2` as classical, citing Yuan--Kalbfleisch (2000). The full
arbitrary-shift iff is a short corollary of Freitas--Laugesen Lemma 10, the
standard `I_-a` connection formula and `I_a,K_a` Wronskian, and the classical
large-argument expansion. The theorem remains correct and fully formalized;
the failed gate is analytic novelty, not correctness.

This status is an audit disposition, not an authorization to submit to a
journal or repository. Any terminal submission decision belongs to the owner
after independent external review.

