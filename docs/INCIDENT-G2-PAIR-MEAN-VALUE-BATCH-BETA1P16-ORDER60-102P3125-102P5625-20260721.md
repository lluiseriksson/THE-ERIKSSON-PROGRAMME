# Incident: order-60 width-1/16 batch breaks at beta 102.4375

The preregistered four-cell batch produced two successful cells,
[1637/16,819/8] and [819/8,1639/16], extending the candidate cover to
beta=102.4375.  The next two cells, [1639/16,205/2] and
[205/2,1641/16], terminated with “mean-value upper endpoint is not
negative” before replay.  Their failed tracebacks are retained.

This is an enclosure-width/margin failure at the current order, not a
certified sign change.  The two passing cells remain candidate-only and the
two failing cells retire this unmodified width/order route beyond beta
102.4375.  No G2/G6 state changes.
