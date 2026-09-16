# Owner-consumers v1: BLOCKED-INSTRUMENTATION, before checkout

This is not Lean evidence. The deliberate forbidden-axiom preflight fixture
raised `ValueError: FORBIDDEN_AXIOM`; the pinned old preflight expected
`RuntimeError`. The actual shell exit was 1. No checkout, toolchain install,
Lean, Lake or focal ran in this attempt.

- Source A unchanged: `ea524400bbf59777d461e8d04790516771258988`.
- Failed runner: `90f4d877d017e7a2b95aa9af740aee89f3cc5f3e`.
- Instrument-only v2 repair: `46825e3723bbab7c22966c0d55c1a91904834f35`.
- Runtime: `2a5234e831ca`, Colab CPU 50.99 GiB, 2026-09-04 ~21:38 UTC.
- Downloaded raw tmux transcript SHA256, matching the Colab hash:
  `A49F5AEE8797909441D2ED5A0606650BB993AA50B1AAE7F7C51EC2799F169CE6`.

`owner-consumers-verifier-self-test.log` is a separate, later synthetic
instrument test, not a rerun of the failed mathematical queue. Verifier
checkpoint `1c15c08902829f03fb1a0987f3d14c97bc08e33d`, script SHA256
`760EA7AB87A6B22628F22BDB985EA894FFE9BD5779E76DCC123CB9B47FBE75D3`.
The gate accepted two fixtures and rejected nine; both metadata verifiers
accepted their synthetic fixture and rejected six corruptions each. Duration
0.0820347710000533 seconds. Shell exit zero was observed separately in the
terminal, outside the tee'd log. Downloaded log SHA256:
`C466F8A8B2674A7DE64212FF30F607F7E82AE05192AC8BDD884635551982FBEB`.

The repaired cold queue is a different execution and remains pending at this
checkpoint. No PRE-VALIDATION notice is retired by this incident record.
Counters: 20/41, TermSource=0, window 15 not attained.
