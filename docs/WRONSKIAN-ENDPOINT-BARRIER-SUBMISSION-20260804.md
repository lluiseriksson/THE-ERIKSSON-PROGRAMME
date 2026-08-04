# Wronskian endpoint barrier — ai.viXra submission record

Date recorded: **2026-08-04**

Operation: **NEW PAPER submitted to ai.viXra**

State: **submitted; public identifier and administrator outcome not yet recorded**

This is a companion obstruction paper to
[`ai.viXra:2607.0089`](https://ai.vixra.org/abs/2607.0089). It is **not** a
replacement for that paper and it does **not** prove or disprove the global
Bessel Wronskian conjecture.

## Submitted metadata

- Title: *Endpoint Parity Loss in a Bessel Wronskian: an exact obstruction to
  kernel-and-anchor proofs of global ratio monotonicity*
- Author: Lluis Eriksson
- Affiliation: Independent Researcher
- Category: Mathematical Physics
- MSC 2020: 33C10 (primary), 42A32 and 41A60 (secondary)
- Keywords: modified Bessel functions; Wronskians; sine-series ratio
  monotonicity; Neumann convolution; endpoint asymptotics; parity
  cancellation; structural non-identifiability

### Abstract

> For beta > 0 let I_m = I_m(beta) denote the modified Bessel function of the
> first kind and define
>
> a_m = I_m^2 ((m-1) I_(m-1)^2 + (m+1) I_(m+1)^2),
> b_m = m I_m^4,
>
> with sine series F_A(t) = sum_(m>=1) a_m sin(mt) and F_B(t) = sum_(m>=1)
> b_m sin(mt). The associated Wronskian is negative exactly when F_A/F_B is
> decreasing. We isolate what can and cannot be proved from two natural
> inputs: the Neumann convolution kernel I_0(2 beta sin(phi/2)) and the
> small-coupling anchor whose normalized limit is 4 sin^3(t).
>
> First, the convolution does prove F_B(t) > 0 for 0 < t < pi. Second, the
> endpoint is governed by two alternating quantities, c_3 and B_pi, through
> an exact cubic law. We prove B_pi > 0, derive integral representations, and
> establish that the cancellation lost by replacing the alternating
> quantities with positive-term majorants has exponential rate 8 - 4 sqrt(2).
> Finally, we prove a smooth one-parameter perturbation theorem: one may keep
> F_B and its kernel unchanged, preserve positivity and strict
> coefficient-ratio ordering, and preserve every jet at beta = 0, while
> choosing either sign of the endpoint cubic coefficient.
>
> Consequently those structural data, even taken together, do not imply
> global Wronskian negativity. This is a no-go theorem for a proof
> architecture, not a counterexample to the original Bessel conjecture. A
> short high-precision kill-test accompanies the paper; no computer-assisted
> inequality is used in the proofs.

### Comments

> 9 pages. New companion obstruction paper to ai.viXra:2607.0089, not a
> replacement. Diagnostic code and reproducibility record:
> https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME

## Exact submitted object

- Upload file: `wronskian_endpoint_barrier.pdf`
- Repository path: `output/pdf/wronskian_endpoint_barrier.pdf`
- Clean public replay commit:
  [`644671f66bed1558d57df6607b60d9c466404acd`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/commit/644671f66bed1558d57df6607b60d9c466404acd)
- Owner-reported manufacturing checkpoint:
  `8625b2d3a12290c11467f985e5f50fc60e764887`
- [PDF pinned at the clean replay commit](https://raw.githubusercontent.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/644671f66bed1558d57df6607b60d9c466404acd/output/pdf/wronskian_endpoint_barrier.pdf)
- PDF SHA-256:
  `c51cd46c1dc577e4d3bb6f2e36df748e715d2e6dc614c7290d8e9837d92986be`
- PDF Git blob OID: `2b876ff999babc50b24a19a74032e527fe5aa967`
- PDF size: 398,436 bytes
- Page count: 9
- TeX Git-blob/LF SHA-256:
  `cd702cb3c54a952bb5f8002b64be699e6822ab9d1e7e1c857e969dd1f73fd989`
- Submission-info Git-blob/LF SHA-256:
  `4bb71b1290f596d012fc03ae043112e8a748eb96286558535da6e68f834f9b48`

The original worktree report ended before upload. The owner's later statement
that the paper was sent supersedes that checkbox state. Do not submit it again
while the administrator outcome is pending.

## Verification and claim boundary

The exact PDF was hashed, parsed as nine pages, and rendered page by page from
the clean replay. No visible clipping, overlap, missing glyph, broken formula,
or unresolved placeholder was found.

The diagnostic command is:

```text
python scripts/wronskian_endpoint_kill_test.py --self-test-mutations
```

Its expected terminal line is:

```text
MUTATION_SELF_TEST PASS deliberate_false_predicate_rejected
```

That test is reproducibility evidence for the obstruction and its mutation
harness. It is not a computer-assisted proof of any paper inequality. The
paper contains ordinary analytic proofs, uses no Lean build or interval
oracle, and leaves the global Wronskian conjecture open.

The clean public replay deliberately excludes the unrelated RG bridge commits
that contaminated the original working history. The paper, script, records,
and their byte identities are preserved without those commits.
