# Endpoint parity barrier for the Bessel Wronskian

This directory contains the source for the obstruction paper associated
with task (51). The paper proves `F_B > 0`, identifies the exact endpoint
cubic coefficient, proves its exponential cancellation rate, and gives a
structural no-go theorem for proofs using only the denominator kernel,
coefficient positivity/order, and the complete small-coupling jet.

The revised proof exposes the uniform Laplace tails, polynomial-moment
envelope bounds, an explicit perturbation radius, and a globally normalized
flat bump. These additions address the concentrated technical reservations
from the first specialist review.

It does **not** claim a proof or counterexample to the global Bessel
Wronskian conjecture.

## Reproduction

From the repository root:

```text
python scripts/wronskian_endpoint_kill_test.py --self-test-mutations
python -O scripts/wronskian_endpoint_kill_test.py --self-test-mutations
```

Compile the paper with two `pdflatex` passes from this directory. The
release PDF is copied to `output/pdf/wronskian_endpoint_barrier.pdf` after
render-and-inspect QA.

The numerical program is a high-precision diagnostic, not an interval
certificate. All acceptance conditions use explicit exceptions and remain
active under `python -O`.
