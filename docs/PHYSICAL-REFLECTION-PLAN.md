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
| R1 | Four independent links; reflection involution; exact holonomy transformation; dictionary to `GaugeConfig.plaquetteHolonomy`; nontrivial dependence on each link | Scoped cold PASS: revised source, 9/9 headline oracles, existing core at 8466 jobs and full 2815-command oracle. Not core-integrated or terminally reproduced |
| R2 | Genuine Wilson weight and product-Haar reflection identity, with orientation, normalization and integrability visible | Geometry compiled in diagnostic 3; measure failed and is being repaired. No R2 acceptance yet. See the [R2 plan](PHYSICAL-CYLINDER-R2-PLAN-20260906.md) |
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

The owner-requested [ARR paper reuse audit](PHYSICAL-REFLECTION-REUSE-AUDIT-20260906.md)
identifies existing Haar analysis, full original-edge gauge fixing and the
conditioned 2D heat-kernel disk amplitude in the satellite repository. Do not
recreate those results. R1 also reuses the mother's existing plaquette gauge
covariance instead of adding another proof. Its `ofPlaquette` dictionary is
local; global lattice reflection and extension of arbitrary four-tuples to a
configuration remain separate geometric requirements.

A single open square has no nonconstant gauge-invariant observable on
either half-tree. Therefore R1/R2 alone must not be promoted to a
nontrivial physical fluctuation sector. R3 must specify a geometry with
genuine half-lattice loops, or explicitly account for boundary gauge
conditions before selecting its nonzero test observable. This issue is
registered before any positivity result.

The [existing two-transporter obstruction](SU2-TWO-TRANSPORTER-NOGO-20260731.md)
and `OS/TwoTransporterHaarProjection.lean` already give the corresponding
Haar-mean projection for the D/E forms. Do not repeat that construction or
count it as a new result. R3 must exhibit a strictly positive reflected norm;
nonconstancy of a function alone is insufficient. A two-link spatial
cylinder is a candidate next geometry because both plaquettes share the
crossing links and the half-slices have closed spatial loops. Its measure,
reflection and nonzero-sector proofs remain to be supplied. The frozen
auxiliary SU(2) lane remains unmodified.

### Candidate R2 geometry, before implementation

Use two spatial links `u0,u1` on the lower circle, two `v0,v1` on the upper
circle, and independent crossing links `a0,a1`. The candidate boundary words
are `H0=u0*a1*v0^-1*a0^-1` and `H1=u1*a0*v1^-1*a1^-1`. Reflection exchanges
the circles and inverts both crossing links. The predicted local identities
are `H0(theta A)=a0^-1*H0(A)^-1*a0` and the analogous formula with `a1,H1`.
These are design formulas to instantiate from R1, not new compiled theorems.

The target measure has the actual density `w_beta(H0)*w_beta(H1)` against
six independent Haar factors. The test candidate is the spatial-loop trace
`tr(u0*u1)`, with centering and a strictly positive reflected norm still to
be proved. For fixed crossing links, the kernel can be written using the
vertex gauge transform of the upper slice:
`v0 -> a0*v0*a1^-1`, `v1 -> a1*v1*a0^-1`. Positivity after averaging that
gauge transform must be proved; it is not an automatic consequence of
pointwise positivity of the weight.

This cylinder has `(V,E,F)=(4,6,2)` and Euler characteristic zero. It is not
an inhabitant of the satellite's disk record, which imposes Euler
characteristic one. Reuse the Haar and covariance ingredients with explicit
type adapters; do not pretend that the disk-amplitude theorem already
applies to this geometry. This was registered before source implementation.
Two R2 modules are now drafted; five failed focal diagnostics are preserved
in the [R2 evidence log](evidence/physical-cylinder-r2-20260906/README.md).
Diagnostic 3 compiled the geometry, but the measure failed. The corrected
source remains unverified until its acceptance gates pass.

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
- 2026-09-06: R1 source draft prepared (UTF-8/LF SHA-256
  `1046B1EF184A1940A965AC9DFE0B3F65C30140083FC83EC6DBC8D5824084FCA4`).
  A task-owned CPU/high-RAM Colab diagnostic was initiated from registered
  source `23f488959005718ac634176d02f5626e8ce70151` plus those exact draft
  bytes. Build and ten headline oracle checks are pending. No core import
  was added.
- 2026-09-06: the preceding diagnostic completed successfully: focal build
  **8160 jobs**, ten requested oracle declarations, only subsets of
  `{propext, Classical.choice, Quot.sound}`. The exact source above was an
  overlay on `23f4889`, not committed code. No full core build ran in that
  diagnostic. The 139.159-second execution ran from
  `07:54:17.985510Z` to `07:56:37.145071Z` in this task's CPU/high-RAM runtime.
  The runtime was disconnected and deleted after preserving the archive in
  the notebook output; disconnection was observed before `08:07:10Z`.
  Connection/allocation start and the exact disconnect second were not
  captured, so exact billed connection duration is unavailable.
  [Notebook with original source, output and lossless archive export](https://colab.research.google.com/drive/1Hj6-16RKQ8Fk1gzEfJC6Qg5aqmVJKjaw).
  Archive byte SHA-256:
  `47aa60230ec74bf11b5e036ddb4fa0e19dc196164843d61ee6d6fdf18c50ff32`.
- 2026-09-06: compared the ARR manuscript with satellite source
  `a1fbea97cbe673d383dbb4bc5e2a2fb70dbf190a`. Removed R1's duplicate gauge
  action/covariance. The revised nine-declaration source has UTF-8/LF SHA-256
  `21A09C1447E2291C3D46679AAD76387794C4C95A3D4B13FF3A59CCDB47923921`.
  A fresh task-owned CPU/high-RAM Colab execution was prepared from
  `5066f3de44af98d73dc23e1062a0bcaf75b3a7e4` with exact source and oracle
  overlays; the full core, focal, source consistency and oracle checks are
  pending. This execution unit requests automatic runtime release after
  preserving its complete evidence in notebook output.
- 2026-09-06: revised R1 focal build passed at **8160 jobs**, all **nine**
  headline oracles passed, and source consistency passed. The unchanged
  `YangMillsCore` import closure rebuilt successfully at **8466 jobs** on
  the specified base. Building the full oracle import set plus standalone R1
  passed at **8467 jobs**; that is not a change to the core root. The
  `oracle_check.lean` overlay is UTF-8/LF SHA-256
  `D67DDFC964D29FF30AA670618F9FF93F2E19EE02701BD79263917D79A1EFE141`.
  The full 2815-command oracle replay remains in progress. The
  [public scoped transcript](evidence/physical-reflection-r1-20260906/revised-oracle.txt)
  records the nine actual outputs. This is one fresh revised-source run,
  not the two independent reproductions needed for terminal status.
  [Prior general-CI failures](PHYSICAL-REFLECTION-CI-BASELINE-20260906.md)
  are recorded independently of Lean and dashboard checks.
- 2026-09-06: registered the two-link spatial cylinder above as an R2/R3
  candidate after checking that the satellite disk theorem cannot instantiate
  its Euler-zero geometry. No positivity or nonzero-sector proof is claimed.
  Automatic approval review rejected deletion of the clean temporary
  satellite checkout with `blocked by policy`; that read-only comparison
  copy remains in the task's `work` directory. No further deletion attempted.
- 2026-09-06: the revised execution completed at `08:51:29.847037Z` with
  `SCOPED_PASS_NOT_CORE_INTEGRATED`. The full oracle exited **0** after
  **1561.023 s**: **2815** readouts, including **26** axiom-free declarations;
  all other dependencies are subsets of the allowed standard axioms.
  Complete full-oracle stdout SHA-256:
  `bf173c24b55930b876a4a77ae34347bfe2d3644b3a16798cec048a5b686f1a21`.
  The [public manifest](evidence/physical-reflection-r1-20260906/revised-manifest.json)
  transcribes every stage's command, real exit, timing and log hash from the
  notebook. The focal transcript hash matches that manifest. The complete
  archive is preserved losslessly as Base64 in the final notebook output;
  archive SHA-256:
  `0ffc58c188fdb8fad88a3f5c930d1bbb3920ee6857dbecab7cc820477941c330`.
  This CPU/high-RAM execution ran from `08:09:53.593994Z` to the finish above
  (**2496.253 s**, 41 min 36 s). Automatic runtime release followed archive
  preservation; the disconnected UI was observed before `08:52:28Z`.
  Execution timestamps are not exact allocation/billing timestamps; the
  latter were not captured. R1 source is published in PR #78 at
  `ea58f6127696a962953c636bb363a43a79b3a6c1` with the exact two
  production/global-oracle overlays recorded above and the generated focal
  driver preserved under docs. Later documentation changes do not alter
  those bytes.
  This completes one fresh revised-source check, not terminal two-clone
  reproduction, independent review, physical reflection positivity or core
  integration. R2–R5 remain open.
