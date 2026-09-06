# Physical Wilson reflection campaign

**Registered 6 September 2026, before implementation.**
Owner instruction: start the independent physical reflection workstream and
keep repository documentation and the dashboard current as work advances.
Base: `ff9498df9bb13050a3c663103e4a0830e793c56f`.

## Target and scope

Construct the physical bridge between Wilson lattice integrals, reflection
positivity and the transfer-operator hypotheses used by `OS/SharpBridge.lean`.
The first milestone is a literal four-link plaquette geometry, not a claim
of reflection positivity or a spectral gap. The subsequent integral must
retain the actual crossing variables. A gauge-pure common transporter that
cancels by definition does not satisfy this requirement.

This campaign is independent of hRpoly. Its implementation is confined to
new `YangMills/OS/` modules. Changes to documentation, news and dashboard
are authorized by the current owner instruction. No RG source, hRpoly
counter, canonical proof-state contract or existing accepted theorem is
changed. Integration into `YangMillsCore` is a later explicit verification
checkpoint. The earlier O charter's retracted constant-uniformity
obstruction is not revived.

## Registered milestone ladder

| ID | Required output | Current state |
|---|---|---|
| R1 | Four independent links; reflection involution; exact holonomy transformation; dictionary to `GaugeConfig.plaquetteHolonomy`; nontrivial dependence on each link | Planned; no compiler claim |
| R2 | Genuine Wilson weight and product-Haar reflection identity, with orientation, normalization and integrability visible | Open |
| R3 | Positive complex reflected Gram forms for a physically specified finite lattice and a nonzero physical test sector | Open |
| R4 | Physical quotient/completion, transfer operator, vacuum and correlation identity, ready for `SharpBridge` | Open |
| R5 | Appropriate total local-observable family and matched clustering inputs | Open |

For R1, label the positive boundary links `b,r,t,l` (bottom, right, top,
left). The oriented plaquette is `H=b*r*t^-1*l^-1`. Reflection in the
vertical bisector sends these links to `(b^-1,l,t^-1,r)`, hence
`H(reflect A)=b^-1*H(A)^-1*b`. The two crossing links are independent.
The later Wilson kernel dictionary must use `(b*r, l*t)`, since
`(b*r)*(l*t)^-1=H`; using the same transporter on both halves would
discard the physical coupling.

A single open square has no nonconstant gauge-invariant observable on
either half-tree. Therefore R1/R2 alone must not be promoted to a
nontrivial physical fluctuation sector. R3 must specify a geometry with
genuine half-lattice loops, or explicitly account for boundary gauge
conditions before selecting its nonzero test observable. This issue is
registered before any positivity result.

## Acceptance conditions

Each accepted R1 declaration must compile against the pinned toolchain and
Mathlib, and have an axiom transcript containing only the standard allowed
axioms (or a subset). Inspect the exact mathematical signature and retain
the source bytes/hash and complete command output. A compilation is not an
external mathematical audit, and a focal build is not a full core build.

R1 cannot close by just defining a factorized weight, receiving the desired
holonomy identity as a hypothesis, or constraining the crossing links to
coincide. R2 must name the actual integral. R3 must prove its positivity
and nonzero sector, rather than accept them as structure fields. R4/R5
retain any still-open physical construction explicitly.

All Lean/Lake/oracle and sustained computations run in this task's own
Colab Linux runtime under `CLAUDE.md`. Prepare the execution unit while
disconnected; record runtime opening, type, execution results and closure.
No use of another task's runtime. No Windows Lean execution is authorized.
Do not add a module to the verified core until the required root build,
oracle and review evidence is available at the exact integration source.

## Documentation contract

Update this status table and its evidence log at every material change.
Keep a campaign entry in `NEWS.md`, the documentation index and the
dashboard, with a link to this plan. Distinguish planned, drafted,
diagnostic-compiled, cold-verified, core-integrated and independently
audited states. A new date does not promote an earlier state. Failed
diagnostics are recorded and are not silently overwritten.

No rate of progress toward Clay is inferred. Historical Clay distance
remains `~0% (<0.1%)`: the 4D continuum construction and OS/Wightman
reconstruction remain open. This label is not a measured percentage.

## Evidence log

- 2026-09-06: campaign registered from the main source above. The preceding
  [static audit](POST-HRPOLY-CONTINUUM-AUDIT-20260906.md) identifies the
  existing thermodynamic and abstract operator results and their scope.
  Colab access checked without starting a computation runtime. R1 is the
  first implementation target; no new Lean result claimed.
