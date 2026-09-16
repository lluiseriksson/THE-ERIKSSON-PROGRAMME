# Step 8b.24 / C6c static design audit

Status: static audit only.  No Lean, Lake or axiom command was run.  No
tracked source was changed and no counter moves.

Verdict: **PASS WITH THREE REQUIRED DESIGN CORRECTIONS**, now applied to the
scratch design notes.

## Poincare absorption reachability correction

The P0--P5 source-facing chain has one scalar premise not discharged by the
current joint smallness registry:

```text
cmp99SourcePoincareErrorCoeff d Lblock depth spacing epsilon < 1.
```

It is propagated honestly from a single terminal premise to all retained
prefixes by coefficient monotonicity, but it is not thereby produced.  The
existing theorem `cmp99SourcePoincareErrorCoeff_zero` proves the premise at
`epsilon = 0`; this witnesses the flat endpoint and does not establish an
open positive-radius regime.  Until a positive-radius producer is named and
proved, the premise remains an upstream reachability obligation outside the
certified joint-window witness.  No promotion may describe it as already
closed or silently add it as a freely selectable sixteenth window.

The separation is literal in the types: the fourteen-window registry has no
top-level source `epsilon` field, but its nested CMP109 pivot record does have
`epsilon0`.  That radius cannot be chosen independently if both layers refer
to the same background.  The new scratch endpoint takes half the minimum of
the Poincare admissible radius and `pivot.epsilon0`, and proves the two pivot
conditions survive by their literal nonnegative linear formulas.  Thus the
common-radius scalar coupling is constructible rather than assumed; coupling
the resulting scalar package to the physical operators remains an assembler
obligation.

## 1. Live spacing premise in the derivative branch

The proposed mass-uniform derivative route correctly performs the exact
forward divided difference before taking norms.  Its prose then uses division
by the fine spacing, but the D1 input list did not explicitly contain
`hspacing : 0 < spacing`.  That omission could have reappeared as an
unexplained `NeZero`/nonzero premise during elaboration or, worse, as a dead
window substituted for the actual denominator fact.

The D1 contract now lists positive fine spacing explicitly and records that it
is consumed to prove the denominator nonzero.  No positive bare-mass premise
was added.

## 2. Covariance dependency was ordered backwards

The former C6c list described C6c.1 as assembling the complete CMP89
Lemma-2.4 package, including `C^(j)`, before C6c.2.  But the same measured
frontier correctly proves that the tracked inverse of
`Q_j G_j^2 Q_j^dagger` is not definitionally the CMP85 (2.30) covariance.
P2c inside C6c.2 is precisely the first proposed constructor of that literal
`C^(j)`.

Therefore a full Lemma-2.4 assembler cannot precede C6c.2 without either a
cycle or a false identification.  The nominal chain now has the honest order:

1. value plus left-derivative/Holder analytic endpoints;
2. literal CMP85 (2.30) covariance and recurrence (2.42);
3. CMP89 Eq.-(2.37) covariance decay/dictionary and common-majorant assembly;
4. CMP95/CMP96 transport.

The existing regional coarse-covariance decay remains reusable proof
substrate only.  It is not relabeled as the source covariance.

## Other checked gates

- P0 keeps dependent truncation internal and exposes no caller tower equality.
- P1 derives every prefix smallness statement from one terminal budget rather
  than accepting a family of windows.
- P2 keeps bare mass, flowing `a_j`, weighted coefficient and counting
  coefficient distinct.
- P2c's source-facing boundary constructs injectivity before the inverse; it
  does not accept the covariance or its inverse laws.
- P3 derives both (2.41) and (2.42) from inverse laws and the scalar recurrence;
  neither displayed recurrence is a premise.
- P4 uses the separate base identity and the exact source interval
  `1 <= j < k`; no `j=0` term is introduced.
- P5 keeps RG ratio `Lblock` and regional large-block parameter `K` distinct.

The P3 algebra also passed an independent exact-rational counter-check on a
non-diagonal three-dimensional precision with a proper nontrivial projector.
The fixture constructs `G`, `C` and `Gnext` as actual matrix inverses and
verifies both candidate inverse laws, (2.42), and the typed orientation of
(2.41).  It additionally checks that the Green sandwich and Schur inverse do
not commute, preventing a vacuous order test.  This remains semantic test
evidence, not Lean evidence.  Script:
`tmp/audit_p3_block_gaussian_rational.py`, SHA-256
`2CA6DF79AF53BCE7CAB0A86D8961ED379C05A5A759C3A673CAA3449ECAB28034`;
measured result:
`P3_BLOCK_GAUSSIAN_RATIONAL_OK
sha256=18CC58C5CBEE9F3D03C0CFB4745125A54C1B2785A655CA4E56DF20E531C18906`.

The duplicate acceptance-gate number in the Eq.-(2.34) note was also corrected
from a second `17` to `18`; this is editorial only.

## Remaining boundary

All P0--P5 files remain unelaborated scratch.  Passing this audit does not
establish that dependent transports, finite-dimensional inverse construction,
noncommutative Schur algebra or physical specialization typecheck.  The first
focal must remain stop-on-first-error, and no fallback may replace the literal
CMP85 covariance by the already tracked conditional middle.
