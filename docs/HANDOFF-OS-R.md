# HANDOFF — session of 2026-08-04 (account migration luis.ebikeride → lluiseriksson)

Anchor: branch `d3-closure` at `c76b79050`, PUSHED to
github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME.  Everything load-bearing
from this session is in the repo; this file is the recovery map.

## 1. What happened today (Addenda 603–608, docs/VERIFICATION-LEDGER.md)

1. **D-6 CLOSED** (`c7b870b05`, Add. 603): `dobrushin_ising_uniform_gap`
   green, core 8480 / oracle 3010 EXACT.  **Paper v8.1 delivered**
   (`1b8f7012c`, Add. 605): external verdict 5.98, FIRST place.  viXra
   REPLACEMENT ficha (v2 over the live v1 of 2026-08-03) delivered to the
   owner — THE OWNER CLICKS, nothing is in flight from our side.
2. **RI charter REGISTERED and PARKED** (`fbe95df28`, Add. 606,
   docs/RATE-INHERITANCE-CHARTER.md): Conjecture 1's commuting case
   COLLAPSES (strict cone + sink blindness + non-ergodicity; corrected
   √-floor; ξ*→0 not ∞).  Judges not run; nothing licensed there.
3. **17 satellite repos audited** (Add. 606 text): nothing ≥6; defects
   recorded (memory: satellite-repo-audit).
4. **28-paper idea sweep** (`c03c34979`, Add. 607): NO reachable ≥7;
   portfolio 6–6.5; two 7-shaped doors with kill-tests (memory:
   idea-sweep-28-papers).
5. **OS-R REGISTERED** (`c76b79050`, Add. 608): the owner's chosen
   campaign.  docs/OS-RECONSTRUCTION-CHARTER.md +
   scripts/judge_os_uniform.py (110/110 PASS locally, both modes,
   0.86 s).  **Fabrication is NOT licensed until the judges PASS on the
   Colab plane.**  Not one line of Lean exists yet.

## 2. THE STANDING ORDER (owner, 2026-08-04, verbatim intent)

"continúa y no pares hasta tener material 7+ + paper."

Honest execution of that order (recorded so the next session neither
ignores it nor fakes it):
- The sweep's consensus (five readers) is that NO ≥7 is reachable today.
  The order is executed by (a) shipping the OS-R paper (6.5 band — the
  highest-value reachable item), (b) running the registered KILL-TESTS
  on the two 7-shaped doors — the site-local Birkhoff cone (30-second
  numeric: Birkhoff ratio of √wK√w at L=2..8 outside the window; if
  →1 uniformly, dead) and noting the wronskian conjecture stays behind
  its proved parity barrier — and (c) if a kill-test SURVIVES, charter
  that door immediately: it is the only honest 7 on the board.
- Manufacturing a "7" by inflating a 6.5 abstract violates the
  programme's defining principle.  Do not do it.  A 6.5 with an honest
  abstract beats a hollow 7 (see CLAUDE.md Part II, first paragraph).

## 3. Recovery procedure (new account, any machine)

1. Clone / open the repo, branch `d3-closure`, verify HEAD ≥ `c76b79050`.
2. Read IN ORDER: this file → docs/OS-RECONSTRUCTION-CHARTER.md →
   docs/OS-R-FABRICATION-BLUEPRINT.md → ledger Addenda 603–608 →
   CLAUDE.md (both parts; the owner rule of 2026-08-01 governs
   execution planes: Colab Pro+ Linux builds, Windows edits).
3. Memory: if on the same Windows box and same working directory
   (`C:\Users\lluis\AppData\Local\Temp\eriksson-push2`), the auto-memory
   at `C:\Users\lluis\.claude\projects\C--Users-lluis-AppData-Local-Temp-eriksson-push2\memory\`
   should load (key = project path, not account).  If it does not, the
   repo files above carry the complete state; the memory files worth
   re-reading manually are os-r-campaign.md, idea-sweep-28-papers.md,
   rate-inheritance-campaign.md, satellite-repo-audit.md,
   dobrushin-d3-closed.md in that directory.
4. Note the multiaccount profiles note (~/.claude-profiles) in memory
   `claude-multiaccount-bridge` if switching accounts on the same box.

## 4. Next unit, exactly (OS-R-0 → OS-R-4)

1. **Plane judges (licenses fabrication):** fresh Colab CPU runtime;
   clone at `c76b79050` (pattern: rm -rf, git clone -b d3-closure,
   checkout SHA, elan-init, `lake exe cache get`); run
   `python scripts/judge_os_uniform.py` AND
   `python -O scripts/judge_os_uniform.py` — expect 110/110 both, exit 0
   (sentinel protocol; scripts/colab_dobrushin_d4_runner.py stage-1 has
   the judge in CERTIFIERS).  Also `lake build YangMillsCore` to confirm
   the 8480 baseline before fabrication.
2. **Fabricate** YangMills/OS/OSReconstructionUniform.lean per the
   BLUEPRINT (docs/OS-R-FABRICATION-BLUEPRINT.md) — expect D-6-style
   machinery-error ladders; the blueprint lists the known pin traps.
3. **Wire + predict:** add module to YangMillsCore.lean and oracle
   endpoints to oracle_check.lean; PREDICT both counts in the commit
   BEFORE measuring (base 8480 core / 3010 oracle at `c7b870b05`;
   +1 module job minimum, oracle +(number of new #print endpoints) —
   count them explicitly at wiring time).
4. **Fresh-clone verification** on the plane (extend the runner's
   LANE_MODULES with `YangMills.OS.OSReconstructionUniform`, stage-5
   hash list with the new file).
5. **Paper** papers/os-reconstruction/ ("The reconstructed theory has
   one mass") — collate the external-priority claim (no OS
   reconstruction found in Lean/Coq/Isabelle as of the sweep; verify
   before the abstract says "first").  Then external evaluation.

Colab operational notes that cost reruns to learn: queued cells are
CLIENT-side (a dead browser kills the queue); type into cells via
Monaco model injection + shadow-root run-button clicks, never raw
keyboard; disconnect the runtime when the unit ends; wrapped log lines
are read with their continuations (-A2).

## 5. Parked items (do not lose, do not start without owner)

- RI campaign (charter registered, judges unrun) — docs/RATE-INHERITANCE-CHARTER.md.
- Fractional Bessel step (6.0, sketch verified in-session, Add. 607) —
  needs literature collation (Segura 2021) + independent audit of the
  sketch (split roles: the generating reader must not audit it).
- D-7 by transplant (6.0) — natural phase 2 of OS-R.
- viXra v2 replacement — owner's click; do NOT resubmit while pending.
- Housekeeping: papers/spatial-reconstruction tex placeholders
  (JOBSAFTER etc.) must be frozen before that paper is cited;
  parity-barriers is on a different toolchain (4.30.0-rc2).
