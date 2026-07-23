# Common-scale seam design timeout

The preregistered positive normalization by the beta-midpoint value
`s_0=J_1(beta_*)^4` was implemented in a byte-separate design driver.  It
scales every coefficient jet and absolute derivative accumulator by the same
positive constant, so the exact Wronskian sign is unchanged.

The first diagnostic on `[101.8125,101.84375]` under the unchanged
order-30/order-37, CWIN=`3/2`, 180-bit, `min_dt=1/100000` contract did not
emit a transcript within 180 seconds.  No sign, coverage, or gate promotion
is inferred.  The design is retained as a timed-out alternative to the
unscaled rescue; the finite-beta relay remains open.
