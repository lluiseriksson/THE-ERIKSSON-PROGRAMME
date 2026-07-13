# C5 five-role audit — resolution table (J-C5-5)

Audit tree: paper v1.1, commit `61b1bb33` (tex `1FD2A8FD...`, pdf
`69DC6F40...`).  Desks per the C4 pattern: math referee, hostile
editor, checklist/formal-hygiene, formal+repro, external-tool; plus
the bibliography desk.  Discipline: one row per finding; findings
that would change mathematics or claims pass adversarial
verification (independent refuters, majority) before any ink moves;
editorial findings resolve by inspection.  Decisions: ACCEPT (fix),
REJECT (refuted, with reason), DEFER (post-tag, named).  No finding
is deleted.

STATUS: CLOSED (all six actas received and resolved; every ACCEPT
applied in paper v1.2 = the commit introducing this table).
Severity tally across the six desks: 2 CRITICAL (E1/E2 = M2 = X-F1,
triple-confirmed, both misquotes of the certified transcript in one
illustrative sentence), 5 MEDIUM, 17 LOW/observations; 1 REJECT
(E7, refuted by the math referee), 1 DEFER (X4, post-tag note).
ZERO findings against any theorem, any Lean statement, any
certificate, or any hash.  The "Commit" column value for every
ACCEPT row is this commit (v1.2).

| # | Rol | Hallazgo | Severidad | Refutadores | Decisión | Cambio | Commit |
|---|-----|----------|-----------|-------------|----------|--------|--------|
| B1 | Biblio | Segura23 entry incomplete (no vol/art/DOI) | MEDIUM | n/a (web-verified, Crossref) | ACCEPT | complete: JMAA 526 (2023), 127211, doi:10.1016/j.jmaa.2023.127211 | 99144dd8 (v1.2) |
| B2 | Biblio | Segura21 cited arXiv-only but PUBLISHED | MEDIUM | n/a (Crossref) | ACCEPT | upgrade: Results Math. 76 (2021), no. 4, Paper No. 221, doi:10.1007/s00025-021-01531-1 (keep arXiv id) | 99144dd8 (v1.2) |
| B3 | Biblio | Amos74 lacks DOI | LOW | n/a | ACCEPT | add doi:10.1090/S0025-5718-1974-0333287-7 | 99144dd8 (v1.2) |
| B4 | Biblio | RS16 lacks DOI | LOW | n/a | ACCEPT | add doi:10.1016/j.jmaa.2016.06.011 | 99144dd8 (v1.2) |
| B5 | Biblio | BP13 lacks DOI | LOW | n/a | ACCEPT | add doi:10.1090/S0002-9939-2012-11325-5 | 99144dd8 (v1.2) |
| E1 | Hostile editor | Companion illustrative row misquotes certified threshold: paper "x_dagger = 50250.44..." vs transcript `x_dag=[50250.3994989 +/- 5.04e-10]` | CRITICAL | CONFIRMED by direct transcript re-read (line 165) at this desk | ACCEPT | replace with 50250.3994... | 99144dd8 (v1.2) |
| E2 | Hostile editor | Same row, box width "~3e-16" vs transcript `width=[3.52501e-14]` (the e-16 figure belongs to the (100, 0.6) row) | CRITICAL | CONFIRMED by direct transcript re-read (line 162) | ACCEPT | replace with ~3.5e-14 | 99144dd8 (v1.2) |
| E3 | Hostile editor | Abstract "uniform lower bound EXACTLY on natural complementary ranges" asserts an iff; only one-directional `amosFamily_lower_of_one_le` exists as artifact; Conclusion "complete parameter classification" same asymmetry | MEDIUM | pending cross-check vs math referee acta | ACCEPT (soften wording; no new Lean at this stage) | abstract: "and a uniform lower bound for every c >= 1, with explicit counterexample witnesses"; conclusion: drop "complete" on the classification side | 99144dd8 (v1.2) |
| E4 | Hostile editor | Companion provenance "before the script existed and before any result was observed" contradicted by the DISCLOSED dev width probe (Technical Note item 4); Reproducibility section states it correctly | MEDIUM | CONFIRMED against charter Technical Note item 4 | ACCEPT | rephrase to "strictly before the certified run and before any certified result was observed" | 99144dd8 (v1.2) |
| E5 | Hostile editor | Abstract uses D'' with D undefined at first use | LOW | n/a | ACCEPT | add "where D = rho_nu - B_{nu,c}" | 99144dd8 (v1.2) |
| E6 | Hostile editor | Thm 3.3 items render 1.-5. but cited as "(v)" at line 419 | LOW | n/a | ACCEPT | roman labels (i)-(v) in the enumerate | 99144dd8 (v1.2) |
| E7 | Hostile editor | "9/4 - c^2 < 2 for c in (1/2,1] and its routine extension beyond" — the inequality is c^2 > 1/4, true for ALL c > 1/2; restriction reads as an error | LOW | REFUTED by math referee inventory item 8: the reduction and the extension wording are honest (9/4-c^2 decreases, negative past 3/2; Lean lemma covers all c > 1/2 with no cap) | REJECT (no change; phrasing accurately describes the proof structure) | none | n/a |
| E8 | Hostile editor | Thm 3.3 forward-depends on Thm 3.4 without a signpost | LOW | n/a | ACCEPT | one remark sentence before 3.3 | 99144dd8 (v1.2) |
| E9 | Hostile editor | Statuses paragraph typography: verified in \emph, others \textbf | LOW | n/a | ACCEPT | unify | 99144dd8 (v1.2) |
| E10 | Hostile editor | §4.2 asymptotics unlabeled under strict tricotomy | LOW | n/a | ACCEPT | tag "(paper-level; not used in the proofs)" | 99144dd8 (v1.2) |
| E11 | Hostile editor | Segura23 incomplete (= B1); dangling "which" in seed-contraction sentence | LOW | n/a | ACCEPT (merged with B1; rephrase sentence) | per B1 + rephrase | 99144dd8 (v1.2) |
| R1 | Formal+repro | Windows default `core.autocrlf=true` rewrites the script to CRLF at checkout; its runtime self-hash then contradicts the committed transcript header (false provenance alarm) | MEDIUM | n/a (mechanically demonstrated) | ACCEPT (editorial route: one repro-section sentence; no repo-wide .gitattributes to avoid touching other desks' lanes) | repro section: "on Windows clone with core.autocrlf=false (LF bytes reproduce the script self-hash) and core.longpaths=true" | 99144dd8 (v1.2) |
| R2 | Formal+repro | Clean clone aborts on default Windows git ("Filename too long", a Part II idea-db file) | MEDIUM | n/a (demonstrated) | ACCEPT (same sentence as R1 covers it; filename shortening deferred to the Part II desk, named) | merged into R1's sentence | 99144dd8 (v1.2) |
| R3 | Formal+repro | tectonic not on any stable PATH; only copy is in a session scratchpad | LOW | n/a | ACCEPT-OPERATIONAL (release script takes C5_TECTONIC env var; binary 0.15.0 located and verified) | scripts/c5_release_check.ps1 already parameterized | 99144dd8 (v1.2) |
| R4 | Formal+repro | RELEASE-MANIFEST.md did not exist (expected-open precondition) | LOW | n/a | RESOLVED THIS SESSION | preliminary manifest created with the recorded hashes incl. transcript e2a2f33a... | 99144dd8 (v1.2) |
| M1 | Math referee | Coth remark FALSE twice: x(coth x - 1) -> 0 (not 1/2), and the collapse is x_* ~ 2c/(2c-1) (= a/(2c-1) + 1/2), not a/(2c-1); the paper's own box value 501.0 contradicts its formula (500.5) by exactly 0.5 | MEDIUM | derivation shown (psi_{1/2} = 2 + 1/(x-1) + exp. small; crossing eq psi = 2(nu+c) gives x_* = 2c/(2c-1) = 501); 25-digit solve + transcript box agree | ACCEPT | rewrite the clause: "for which psi_{1/2}(x) = 2 + 1/(x-1) up to exponentially small error collapses the crossing equation psi_{1/2} = 2(nu+c) to x_* ~ 2c/(2c-1) = 501" (paper-level label stays) | 99144dd8 (v1.2) |
| M2 | Math referee | x_dagger misprint 50250.44 vs certified 50250.3995 | CRITICAL/MEDIUM | = E1; independently recomputed by this desk | ACCEPT (merged with E1) | per E1 | 99144dd8 (v1.2) |
| M3 | Math referee | q_nu printed as (x/2)^2/(nu+1); the Lean artifact besselRatioReal_lt_product has (x/2)^2/(nu+2) (paper variant true but weaker; artifact mismatch) | LOW | Lean source read (AmosCrossing.lean:122-125); charter Amendment 2 concurs (q_{nu+1} = x^2/(4(nu+2))) | ACCEPT | change (nu+1) -> (nu+2) inside q_nu | 99144dd8 (v1.2) |
| M4 | Math referee | Thm 3.3(iii) cites crossing_pos_right for derivative positivity; that lemma asserts a point with D > 0, not D' > 0 (which follows from crossing_hasDerivAt + crossing_threshold_strict) | LOW | Lean source read | ACCEPT | fix the citation to crossing_threshold_strict | 99144dd8 (v1.2) |
| M5 | Math referee | Abstract lower-half "exactly" not packaged as a single Lean iff | LOW | concurs with E3 | ACCEPT (merged with E3) | per E3 | 99144dd8 (v1.2) |
| M6 | Math referee | "strictly decreasing (amosFamily_anti)" — the Lean lemma proves the non-strict <= (all the chain needs) | LOW | Lean source read | ACCEPT | reword to non-strict ("decreasing (non-strict form in Lean; all the chain uses)") or "antitone" | 99144dd8 (v1.2) |
| X1 | External tool | "exact dyadic midpoints" not literally implementable (L0/U0 are balls for non-dyadic c and nu = pi); implementation uses ball midpoints — strictly CONSERVATIVE, but an undisclosed wording deviation from Amendment 8 | LOW | empirically verified conservative (arb comparisons return False when undecidable; PASS never spurious) | ACCEPT | one-line disclosure in the companion section ("outward-rounded ball midpoints; conservative") | 99144dd8 (v1.2) |
| X2 | External tool | mpmath VERIFIED pass implemented as box-end sign check + finite-difference D', not the registered "float bisection + containment"; properly segregated, influences no verdict | LOW | this desk RAN the registered version independently: 4/4 including the heavy row | ACCEPT | disclose the substitution in the companion section (the desk's registered-form pass is on the acta record) | 99144dd8 (v1.2) |
| X3 | External tool | Protocol-commit enumeration cites f6ec64ea + fdb0fe60 only; the implemented depth formula was registered in a THIRD pre-run commit ae60ff74 (timing verified benign: heavy row 0.6 s, full run fits the 57 s gap) | LOW | commit timestamps verified | ACCEPT | add ae60ff74 wherever protocol commits are enumerated (paper + manifest) | 99144dd8 (v1.2) |
| X4 | External tool | Script continues remaining rows after a FAIL; "full stop + autopsy" appears only at summary. Moot at 0 FAIL | LOW | n/a | DEFER (post-tag note; no rerun warranted) | none now; named in manifest audit addendum if desired | n/a |

Bibliography desk verdict: every volume/page/year/DOI already in the
file is CORRECT; diacritics (Ruiz-Antolin, Grun, Baricz) match
publisher spellings; Salazar26 (arXiv:2607.05538) verified to exist
with matching title/author; the Thiruvenkatachar--Nanjundiah
attribution confirmed standard (stated in BP13 itself); the
identifier-pending wording identical across ErikssonC2/C3/C4 per the
C4 precedent.  Only the five additive edits above.

## Actas (summaries; full texts in the session record)

### Bibliography desk (received first)
13 entries checked against Crossref/publisher/arXiv on 2026-07-13.
Findings B1-B5 above; nothing unverifiable; no field errors.

### Hostile editor
Findings E1-E11 above (2 CRITICAL, 2 MEDIUM, 7 LOW).  Explicitly
checked CLEAN: Amendment-7 verbatim sentence present twice in the
right places; Amendment-5 naming discipline satisfied (3F closed, so
"complete quantitative crossing classification" permitted, no
stronger phrasing); v1.1 independence micropatch correct in both
occurrences; novelty posture honest (five separate RS16
declarations); related-work collation faithful to Amendment 7;
Amendment-8 independence conditions match the charter; companion
status discipline correct; oracle/build/URL/footnote claims
accurate; all \ref/\cite resolve.  E1/E2 verified at the resolution
desk directly against transcript lines 162/165: CONFIRMED.

### Formal+repro desk
NO CRITICAL findings; R1-R4 above.  Reproduced cleanly at 61b1bb33:
toolchain + double Mathlib pin; all command targets present; all
four artifact hashes match (transcript e2a2f33a... recorded); script
provenance header and transcript header/structure complete (30 rows,
4 booleans each, PASS 30 / FAIL 0 / UNDECIDED 0, mpmath VERIFIED
30/30); Oracle.lean carries exactly 110 #print axioms lines; cited
commits are ancestors of 61b1bb33; clean-clone rehearsal green
(with R1/R2 caveats); 3-pair smoke test from the clone reproduces
the committed transcript DIGIT-IDENTICALLY (boxes, Nmax, step
counts); tectonic 0.15.0 compiles the tex to 10 pages; origin/main
contains 61b1bb33.  Heavy items (lake build, full 30-pair rerun)
excluded by design — they stand on committed transcripts.

### Math referee
NO CRITICAL; the theorem-level mathematics is SOUND.  Verified
inventory of 15 items: calibration, nullcline + trichotomy, family
derivative + slope identity (numeric to 1e-53 at actual crossings),
threshold algebra at all four occurrences, the COMPLETE contact
algebra (every displayed identity, numeric to 1e-50, Lean form and
cofactor K = -2c^2(2nu+1) verified verbatim at AmosTangency.lean:161),
window both ends incl. degenerate corners, lower-bound collapse,
witness reduction (E7 refuted: the (1/2,1] restriction is honest),
root comparison, Turan equivalence, asymptotics, NO CIRCULARITY in
the threshold->no-contact->strict->unconditional chain (dependency
direction read in the Lean sources), theorem statements = Lean
statements (3.1-3.5), scale law, companion internals (fixed rule
strictly contains the Lean window; heavy-row numbers reproduced).
Findings M1-M6 above.

### Checklist / formal hygiene
GREEN; 1 MEDIUM (CHK-1 = M3) + 3 LOW (CHK-2 = M4; CHK-3
crossing_hasDerivAt_everywhere description; CHK-4 "conversely"
larger than artifact — all fixed in v1.2).  Inventory: 31/31 cited
Lean identifiers exist, in the claimed files, statements matching
(AmosClosure byte-identical between f1c87fef and 61b1bb33); oracle
output = 110 lines all clean, byte-identical in names/order to
Oracle.lean, split 74 inherited + 36 C5-new (phase cumulative
comments consistent); build run 7 = 8175 jobs GREEN (runs 1-6
monotone 8172-8174); Amendment-8 commits confirmed pre-run ancestors
via merge-base; zero sorry / zero axiom / zero native_decide in
AmosClosure; all 15 \ref + 4 \eqref + 14 cites resolve in exact
bijection; theorem-artifact table 16/16 rows correct.

### External tool desk
NO CRITICAL; the certified core is SOUND and CONFORMANT.  Verdict
logic genuinely ball-sign-only (arb comparisons empirically return
False when undecidable — PASS can never be spurious); no float in
any certified path; grid = exactly the 30 registered pairs (pi as
arb ball, c as exact rational-ball quotients); recurrence/seed/
derivative formulas verified analytically; transcript parsed: 30
PASS, 120/120 certificate booleans, prec 128, 0 FAIL/UNDECIDED;
THREE ROWS RE-EXECUTED from the committed script reproduce the
transcript TO EVERY PRINTED DIGIT (incl. the heavy row, Nmax 146011,
0.6 s); independent mpmath implementation (dps 60, registered
float-bisection form) confirms 4/4 spot rows incl. (100, 0.501);
provenance sha + commit ordering verified (f6ec64ea 00:03:13 ->
fdb0fe60 00:07:32 -> ae60ff74 00:13:00 -> run 90818f33 00:13:57).
Findings X1-X4 above.
