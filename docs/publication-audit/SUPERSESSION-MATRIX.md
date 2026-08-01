# Supersession and replacement matrix — corpus frozen 2026-07-31

This matrix records claim-level relations.  A shared subject is not a
supersession.  `REPLACE-VERSION` keeps the same ai.viXra record and version
history; `SUPERSEDE-BY-NEW-PAPER` names a distinct, already-public record whose
claim actually repairs or extends the old one.  No upload or submission was
performed by this audit.

**Owner policy added 2026-08-01.**  Every `SUPERSEDE-BY-NEW-PAPER` relation is
also to be made visible in a replacement of the old record: the first PDF page
and the first abstract words must carry an uppercase `SUPERSEDED BY` notice,
followed by an exact retained/superseded claim map.  This does not change the
claim-level verdict or merge the two records; it makes the relation public.

## Replacement sequence

The owner order is causal rather than chronological:

1. `2602.0052v2 -> v3` — restore the displaced Interface Lemmas identity.
2. `2602.0036v2 -> v3` — retract the unproved Ricci/O'Neill chain.
3. `2602.0033v2 -> v3 (R30)` — replace the false exact-trace doubling step.
4. `2602.0085v1 -> v2` — retract the false Wilson-flow linearisation first.
5. `2602.0084v1 -> v2` — retract its imported and independent false lemmas.
6. `2602.0035v1 -> v2` — install the corrected Morse--Bott paper only after its
   upstream identity, curvature and trace dependencies have been corrected.
7. `2602.0038v2 -> v3` — retitle the simplified-measure propagator result.
8. `2602.0041v3 -> v4` — make the H-XSD/H-DOB conditionality public-facing.
9. `2601.0115v2 -> v3` — repair the clipped table after all P0/P1 actions.
10. `2512.0073v1 -> v2` — publish the Davies/TFIM correction and supersession
    map pointing to `2601.0023v2`.
11. `2601.0047v2 -> v3` — mark the ED benchmark as consolidated by
    `2601.0051v2`, without calling the retained finite data false.
12. `2607.0035v1 -> v2` — narrow the old 2D SU(2) record and point to the
    original-edge/tree--cotree closure in `2607.0039v1`.
13. `2607.0023v1 -> v2` — point the terminal sign claim to `2607.0089v1` while
    keeping its independent exact-to-Arb replay explicitly pending.

Do not start item *n+1* until the public page for item *n* shows the intended
new version, title/abstract/comments, direct PDF URL, page count and PDF SHA.
The owner reported items 1--9 sent on 2026-08-01 before the public pages
updated; those nine are now `ENVIADO/PENDIENTE`.  Do not resend them merely to
restore ordering.  Items 10--13 remain local until their independent audit and
release preflight pass.

## Action matrix

| Current public reference | Action | Replacement / successor | Exact reason (page and claim) | Claim dependants | Risk | Package state |
|---|---|---|---|---|---|---|
| `2602.0052v2`, SHA `1975125d…`, 10 pp | REPLACE-VERSION | local `2602.0052v3`, 16 pp, SHA `4ce8cb39…` | The record metadata says *Geodesic Convexity* while its v2 PDF is the corrected Morse--Bott block belonging to 2602.0035.  Archived `2602.0052v1`, 11 pp, SHA `2ef7856e…`, is the authentic *Interface Lemmas* paper; its global principal-log/Holley--Stroock closure also requires retraction. | 2602.0035 identity/provenance; 2602.0036; publication history | P0 | **LISTO-LOCAL**, independent audit PASS; owner order 1 |
| `2602.0036v2`, SHA `4f7aa102…`, 11 pp | REPLACE-VERSION | local `2602.0036v3`, 19 pp, SHA `7e86eb7b…` | Theorem 3.1 and Corollaries 3.2--3.3 rely on an O'Neill trace omitting mixed horizontal--vertical sectional terms; the printed Ricci proof and corollaries are therefore unestablished. | 2602.0033; 2602.0035 | P0 | **LISTO-LOCAL**, independent audit PASS; owner order 2 |
| `2602.0033v2`, SHA `91a7d95e…`, 8 pp | REPLACE-VERSION | local R30 `2602.0033v3`, 25 pp, SHA `878dba7c…` | pp. 4--6, Theorem 4.1 infers exact gap doubling from trace matching.  A positivity-improving 2x2 exact-trace counterexample has unequal gaps `1/3` and `1`.  R30 replaces this with a sufficient finite-scale lemma requiring `|Q_M-1|=o(X_M+Y_M)` and multiplicative relative tails. | 2602.0035; 2602.0051; 2602.0032 review; 2602.0040/0096 navigation | P0 | **LISTO-LOCAL**, independent math/package audits PASS; owner order 3 |
| `2602.0085v1`, SHA `930e7ea…`, 21 pp | REPLACE-VERSION | local `2602.0085v2`, 26 pp, SHA `deff7be4…` | Eq. (16)/Lemma 3.6 gives the wrong linearised kernel: at `U=1` the true Hessian annihilates a pure-gauge space of dimension at least `(|V|-1)(N^2-1)`.  Lemma 3.8, Proposition 3.9, Theorem 3.11 and Theorem 1.1 consequently fail. | 2602.0084; 2602.0096; 2602.0117 | P0 | **LISTO-LOCAL**, independent audit PASS; owner order 4 |
| `2602.0084v1`, SHA `633c08d3…`, 15 pp | REPLACE-VERSION | local `2602.0084v2`, 21 pp, SHA `4099349d…` | pp. 4--6, 9--10, 12 and 14 import 0085 and contain independent false heat-kernel, variance, periodic-support, nonlinear-map and Hille--Yosida steps; affected results include Lemmas 3.1, 3.3, 3.5, A.1 and Theorems 4.4, 5.1. | 2602.0092; 2602.0096; 2602.0117 | P0 | **LISTO-LOCAL**, uniform-Letter rebuild and independent audit PASS; owner order 5 |
| `2602.0035v1`, SHA `b7616a58…`, 11 pp | REPLACE-VERSION | local corrected `2602.0035v2`, 21 pp, SHA `05310780…` | v1 abstract/body present an unrestricted Morse--Bott mass-gap route.  The corrected material is presently misfiled under 2602.0052v2 and must be installed with explicit upstream caveats. | 2602.0040; 2602.0038/0036 citations; audit maps | P0 | **LISTO-LOCAL**, independent audit PASS; owner order 6 |
| `2602.0038v2`, SHA `306d2336…`, 10 pp | REPLACE-VERSION | local `2602.0038v3`, 11 pp, SHA `4bcadc2d…` | Title/abstract advertise a non-perturbative mass-gap proof; Definition 4 and the body establish only a zero-momentum propagator bound for a simplified quadratic Gribov--Zwanziger measure. | 2602.0036 entropic-mass import; programme summaries | P1 | **LISTO-LOCAL**, independent audit PASS; owner order 7 |
| `2602.0041v3`, SHA `f67dea05…`, 11 pp | REPLACE-VERSION | local `2602.0041v4`, 12 pp, SHA `d268921d…` | Theorem 1.1 is conditional on H-XSD, and its mass-gap part additionally on H-DOB; p. 9 retains continuum/OS work as open, while the public title is unconditional. | 2602.0051--0057; 2602.0089 | P1 | **LISTO-LOCAL**, independent audit PASS; owner order 8 |
| `2601.0115v2`, SHA `e845b2d9…`, 9 pp | REPLACE-VERSION | local `2601.0115v3`, 9 pp, SHA `7e32a880…` | Table 1 on public p. 6 is clipped: 152 text characters lie outside MediaBox.  The replacement preserves every character and brings the full table inside the page; the other eight pages are pixel-identical. | none identified beyond citations to this toy-model record | P2 | **LISTO-LOCAL**, independent audit PASS; owner order 9 |
| `2512.0073v1`, SHA `6fcfe527…`, 22 pp | SUPERSEDE-BY-NEW-PAPER + REPLACE-VERSION NOTICE | public successor `2601.0023v2`, SHA `871fcced…`, 6 pp; local notice `2512.0073v2`, 24 pp, SHA `11cc85a3…` | The successor corrects the general Davies Bohr decomposition, proof route, suppression constants and finite TFIM implementation while explicitly retaining every old `omega=0` statement and the witness conclusion with a repaired proof. | rate-envelope/maintenance interfaces | P0 | replacement candidate rebuilt after independent scope finding; reaudit pending |
| `2601.0047v2`, SHA `b2682f96…`, 5 pp | SUPERSEDE-BY-NEW-PAPER + REPLACE-VERSION NOTICE | public successor `2601.0051v2`, SHA `f10520e4…`, 4 pp; local notice `2601.0047v3`, 7 pp, SHA `a4779474…` | The successor retains the same exact-diagonalisation Petz-versus-Wilson benchmark and adds tensor-network ladders; it does not merely share a topic. | later Petz/Wilson benchmark summaries | P1 | replacement candidate built; independent audit pending |
| `2607.0035v1`, SHA `99413dfa…`, 9 pp | SUPERSEDE-BY-NEW-PAPER + REPLACE-VERSION NOTICE | public successor `2607.0039v1`, SHA `acb7b9b4…`, 10 pp; local notice `2607.0035v2`, 11 pp, SHA `86a3891f…` | Old pp. 7 and 9 stop at a post-gauge-fixed evaluator and disclaim the original-edge/face-holonomy bridge advertised by the title.  Successor pp. 5--8 supplies that bridge and tree--cotree closure. | exact 2D SU(2) area-law chain | P0 | replacement candidate built; independent audit pending |
| `2607.0023v1`, SHA `88d4cbd1…`, 13 pp | SUPERSEDE-BY-NEW-PAPER + REPLACE-VERSION NOTICE | public successor `2607.0089v1`, SHA `e8cc61a1…`, 33 pp; local notice `2607.0023v2`, 15 pp, SHA `7aa4ba1e…` | Old pp. 11--13 leave global ratio monotonicity conjectural; the successor claims the same terminal sign theorem and retains the bridge/certificate provenance. | surface-expansion/area-law chain | P1 | replacement candidate built; successor remains REVIEW-PENDING until exact-to-Arb replay |

## Actions deliberately not promoted

- R29 is an unsubmitted, rejected local object and is not a version, successor or
  citable repair.
- `2512.0081v2` remains `REVIEW-PENDING`: its current public PDF URL returns 404;
  the archived v1 hash cannot stand in for the unavailable current object.
- The remaining `REVIEW-PENDING` corpus is listed in `REVIEW-PENDING.md`; absence
  from this matrix does not turn an unresolved claim into `KEEP`.
