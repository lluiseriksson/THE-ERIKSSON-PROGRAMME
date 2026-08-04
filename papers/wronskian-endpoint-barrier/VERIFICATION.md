# Verification record

Date: 2026-08-04

Branch: `codex/wronskian-reduction-51`

## Mathematical status

- Exact: Neumann convolution identities and `F_B(t) > 0` on `(0, pi)`.
- Exact: endpoint telescoping and
  `W(pi-d) = -4 c3 Bpi d^3 + O(d^5)`.
- Ordinary asymptotic proof: cancellation exponent `8 - 4 sqrt(2)`.
- Ordinary perturbation proof: kernel/order/complete-anchor data do not
  identify the endpoint sign.
- Diagnostic only: high-precision finite calculations below.
- Not claimed: a proof or disproof of the global Bessel Wronskian conjecture.

## Local-light runs

Environment: Python 3.12.6, mpmath 1.3.0, one CPU process, 180 decimal
digits. Both commands completed below the 30-second per-process limit.

```text
python scripts/wronskian_endpoint_kill_test.py --self-test-mutations
exit 0; wall time 17.7 s

python -O scripts/wronskian_endpoint_kill_test.py --self-test-mutations
exit 0; wall time 15.2 s
```

The two runs produced the same acceptance data:

```text
KERNEL_GRAF_SANITY residual_max=3.7904762e-175
SMALL_BETA_ANCHOR beta=0.01 ratios=1.0000916707,1.00009167061,1.00009167049
ENDPOINT_INTEGRALS beta=1 c3_rel=7.2297596e-181 Bpi_rel=2.4099199e-181
ENDPOINT_INTEGRALS beta=8 c3_rel=2.1689279e-180 Bpi_rel=1.4459519e-180
ENDPOINT_CANCELLATION beta=8  ratio=3.86868117e-5
ENDPOINT_CANCELLATION beta=16 ratio=1.85217583e-12
ENDPOINT_CANCELLATION beta=32 ratio=5.90114568e-28
ENDPOINT_CANCELLATION beta=64 ratio=9.45545116e-60
fitted slopes: 2.10683103077, 2.23016100277, 2.2878524398
asymptotic slope: 8-4sqrt(2)=2.34314575051
ENDPOINT_IDENTITY beta=32 quotient=1.0000009109773
STRUCTURAL_PERTURBATION beta=32 c3_over_A1=1.270694641e-12
positive=True ratio_increasing=True
MUTATION_SELF_TEST PASS deliberate_false_predicate_rejected
VERDICT FB_KERNEL_PASS; GLOBAL_PARABOLIC_ROUTE_FAILS_ENDPOINT_KILL_TEST
```

All acceptance predicates are implemented with explicit exceptions, not
Python `assert`, and therefore remain active under `python -O`.

## Build and external-computation status

The PDF was built with local `pdflatex`; each pass took under two seconds.
The release PDF was rendered with Poppler and visually inspected page by
page. No Lean, Lake, interval oracle, Claude/Fable, Colab, GPU, or sustained
local computation was used.

The final frozen hashes are recorded in `FREEZE-MANIFEST.md`. This record is
an artifact handoff, not an external correctness certification.
