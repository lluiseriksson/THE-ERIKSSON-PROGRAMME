# Scaled-bulk candidate: preregistration for `[35,36]`

Registered 2026-07-16 before the provenance-bearing rerun.  This is a
partial candidate only; it cannot discharge the scaled-bulk slot or G2.

Frozen configuration:

* `CWIN=4`, beta Taylor order 12, `t` order 9, Arb precision 180;
* beta width `1/8`;
* units `[35,35.5]` and `[35.5,36]`, four adjacent beta boxes per unit;
* scaled Bessel derivative-tail factor
  `8*(1+2*(m+1)/beta_lo)`;
* exact semantic records are the printed `beta-box [lo,hi]: N t-boxes`
  lines, compared byte-for-byte between production and replay.

The candidate may load only the two displayed beta halves after production,
replay, dependency-hash, and adjacency validation.  It carries no claim for
`[36,1000/9)`, no sign-union completion, and no manuscript promotion.

The production and replay runs now pass from the same worktree head.  The
joint validator confirms eight adjacent beta boxes and 6,344 adaptive
`t`-boxes with exact semantic-record equality.  This is a reproducible partial
candidate, not a G2 certificate: the global sign contract and the remaining
beta interval are still open.
