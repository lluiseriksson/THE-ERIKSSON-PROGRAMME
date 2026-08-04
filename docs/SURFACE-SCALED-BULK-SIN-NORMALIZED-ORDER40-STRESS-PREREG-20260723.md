# Sine-normalized order-40 stress preregistration

The order-30 sine-normalized one-box diagnostic still straddled zero.  This
separate stress keeps the same beta and t boxes and quotient recurrence but
raises the frozen Taylor contract to beta order 40, t-order 45, 220-bit Arb,
and `min_dt=1/200000`.  It tests whether the remaining width is a finite
Taylor remainder rather than a structural cancellation loss.

This is a single-box diagnostic only.  No output can promote the finite-beta
bridge or any surface gate.
