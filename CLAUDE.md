# THE ERIKSSON PROGRAMME — agent handoff (Surface Theorem closure)

Hash rule: every relay/commit message carries its hash context on the
first line. Read this file FIRST, then docs/SURFACE-CLOSURE-NOTES.md
(the acta, v1–v48 — the single source of truth; when anything
diverges, THE MOST RECENT HASH RULES).

## What this is

An audit-first mathematical research programme closing the SURFACE
THEOREM: for all beta > 0, (i) F_B > 0 on (0, pi) [proved twice] and
(ii) E' < 0 on (0, pi) [relay in progress]. The live manuscript is
papers/surface-complete/surface_theorem_complete.tex (+pdf, always
same commit). DO NOT SUBMIT while any [SLOT] lives.

## REGIME (non-negotiable, before any work)

1. TRICOTOMY everywhere: "exact" only with proof; "certified" only
   with a committed interval-arithmetic transcript; "verified" for
   numerics. No label upgrades without its witness.
2. Every number travels with (convention, t, beta). Convention:
   integrals over [-pi,pi]^2 unnormalized (conv:mass in the paper).
3. JUDGES BEFORE PAGES: no intermediate target is used unless its
   own pre-registration passed. Standing judges (notes v40–v48):
   - EXTERIOR: beta·X -> T(c) = (1/2 - 1/(8c^2))/c on nine
     pre-registered cells; R_1(c) must land in [residual, 3x] with
     residuals 0.101–0.292; stress cell (2.9, 15) judged in two
     pieces (saddle +0.023553; mirror -0.0707 vs derived M).
   - PARTIAL: beta·X_1 -> 2T(c) (frozen-ratio, single measure K);
     beta·X_2 -> -T(c) (ratio-variation, deficit-weighted).
   - L CROSS-TABLE: finite-difference L's must match the series
     table within +-25% cell by cell (v44).
   - FACTORY tolerances: x2 first-order moments, x3 masses, x10
     remainders (v37/v38 context).
   - RECEPTION of THE page: five marks IN ORDER, stop at first
     failure (v43).
4. SPLIT ROLES, mandatory: one session FABRICATES, a DIFFERENT
   session AUDITS against the judges before merging. Never both in
   one session.
5. Measured failure = commit with diagnosis. Never delete. (See
   derive_page_attempt1.py and notes v45–v46.)
6. Constants: only DERIVED constants go to ink; benches calibrate
   (ghost #23 rule).
7. Long runs: absolute script paths (ghosts #20/#21), frozen run
   clone, transcripts do not exist until committed, iteration caps
   (ghost #22), ball+boolean in every printed enclosure, provenance
   header (script sha256, library versions, stage parameters).

## WHERE EVERYTHING IS

- Repo: github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME (branch main).
- Acta: docs/SURFACE-CLOSURE-NOTES.md (v1–v48; ghosts #1–#25 with
  mechanisms and the rules they bought).
- Manuscript: papers/surface-complete/surface_theorem_complete.tex.
  Slots remaining: [6,15] coverage row, analytic relay [15,inf),
  sinc-cert, pi-window 4 constants, header theorem seal.
- Scripts (scripts/): exp_integrator_arb.py (DEFINITIVE integrator,
  sha256 834802f9... post ghost-#25; nesting assert; design table);
  exp_integrator_arb_RUN_1d888e99.py (pinned bytes of the harvest
  run); harvest_arb_transcript_1d888e99.txt (the certified local box
  transcript: point/stability/3x3 box all True, 22,986,387 cells);
  test_safe_sqrt.py (7 cases, arb-ball containment); margin_map_*
  (design-only, labeled); derive_page_attempt1.py (failed pass 1,
  archived); ERRATUM-display-supersets.md.
- Local machine (Lluis's Windows box): run clone
  C:\Users\lluis\AppData\Local\Temp\eriksson-push (FROZEN for git
  ops while runs live), push clone ...\eriksson-push2, python
  C:\Python312\python.exe (mpmath, sympy, python-flint 0.9.0).
  Oven outputs in C:\Users\lluis\AppData\Local\Temp\
  (margin_map_fine_out.txt, margin_map_probes_out.txt).
- Governance frozen at commit f2ea0d0: coverage witness = exhaustive
  Arb + independent sampled implementation audit (2%, seed =
  SHA256(f2ea0d0-ASCII | box-id), box-id = exact rational coords;
  ONE mismatch = full stop + autopsy).

## TASK QUEUE (strict order)

1. PASS 2 of THE PAGE (bilinear saddle extraction lemma): extract
   X_1 (pure-K bilinear r(z_s)[<D><ND> - <N><D^2>], five v5-templated
   moments) against judge 2T(c); then X_2 (deficit-weighted moments,
   bilateral root floor) against -T(c); sum against the exterior
   judge; Lagrange remainders citing the two-term companions (v40:
   |eps_1| <= 0.6/z^2, |eps_0| <= 0.4/z^2, R_2 <= 2.12 u^4). The
   X_2 = -X_1/2 shortcut is CANCELLED (asymptotic only, v48). On
   pass: ink to manuscript + tooth restored SAME COMMIT.
2. MECHANICAL CASCADE: minoration via mu_D = 2mu_1 - 4mu_P (exact,
   v35 — mu_1's integrand is positive, nothing to subtract);
   C-hat assembly against the 0.42 piece-A budget with the
   eight-cell law as lock; Region II (= the layer lemma, spec v32);
   splices; explicit beta_0 with the negotiation rule (analytic
   margin >= 2x consumed, machine absorbs [15, beta_0]).
3. OVEN: L matching (+-25% vs v44 table) -> pilot at dz ~ 0.25 with
   dz(beta) scaling -> full [3,15] campaign under frozen governance.
   If Lluis authorizes cloud: parallelize by beta ranges,
   concatenated transcripts with hashes.
4. EDGES: sinc-cert on (0, t*(beta)] x [3, beta_0] (exact sinc
   lemma is in the paper; minor criterion + tail m+n > pi/t +
   uniform overlap pending); pi-window 4 constants (c_3 as a cheap
   1D passenger in the harness).
5. MANUSCRIPT: replace each [SLOT] the day its piece closes; relay
   table without amber (thmB iv canonical + bulk iv resume from
   beta = 5.7305 are pending second witnesses); PDF+tex same commit.
6. SUBMISSION: arXiv math.CA (or JMAA direct), the complete paper,
   ghost ledger included. NOTHING is called final with a live slot.

## ON "ITERATE TO YANG–MILLS" (the honest instruction)

There exists NO proved reduction from the Surface Theorem (or
anything in these repos) to the Yang–Mills mass-gap problem. The
instruction is NOT "iterate toward YM" — that order produces
adjacent theorems with grandiose names, the exact trap this
programme learned to avoid. The correct sequence:
(a) finish and submit THIS paper;
(b) survive the referee — the first real external calibration,
    worth more than any plan;
(c) if the repos contain a chain claiming to connect to YM, the
    next work is auditing that chain LINK BY LINK under this same
    regime, starting from the weakest link, presuming it dies there
    (millennium programmes die at the bridge, not in the lemmas);
(d) only if a bridge link survives adversarial audit, build the
    next theorem THAT LINK demands — never the one ambition
    suggests.
Permanent honesty criterion: importance is not inherited by
thematic proximity; only a proved reduction transfers it. An agent
that respects (a)–(d) will advance whatever is mathematically
advanceable; one that jumps to (d) without (c) will manufacture
seventy more papers of fog.

## THE OWNER

Lluis decides what is submitted and when. That role is not
delegable. Bring him the complete manuscript when it exists.
