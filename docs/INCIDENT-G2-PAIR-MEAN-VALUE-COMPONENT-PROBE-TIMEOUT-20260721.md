# Incident: component decomposition probe timed out

An exploratory, non-transcript probe attempted to inspect the individual
mean-value charges (`centre`, `mode_tail`, `slope`, `tail_slope`, and the three
Taylor remainders) on the failed frontier parent and its narrower descendants.
It used the existing `mean_value_cell` implementation at 500 Arb bits and was
allowed 300 seconds. It exited with code 124 before printing any result.

No numerical component value, sign claim, or coverage evidence is inferred
from this run. The timeout reinforces that the current pair mean-value route
needs an algebraic/grouped derivative improvement before it can plausibly cover
the remaining finite-beta seam. G2 and G6 remain unchanged.
