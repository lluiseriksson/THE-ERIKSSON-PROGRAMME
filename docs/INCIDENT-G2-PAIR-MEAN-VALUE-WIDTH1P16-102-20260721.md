# Incident: paired mean-value width 1/16 fails at beta 102

The preregistered cell

    beta   [102,1633/16] = [102,102.0625]
    lambda [3/2,19/10]
    modes 115, beta/lambda orders 50/50, Arb 500 bits

terminated with “mean-value upper endpoint is not negative”.  The runner
produced only the retained failed.txt traceback; no production or replay
certificate exists.

The adjacent width-1/32 cell [102,3265/32] passed, so this is an enclosure
width failure, not a certified sign change.  The width-1/16 route is retired
for this endpoint; no gate or manuscript state changes.
