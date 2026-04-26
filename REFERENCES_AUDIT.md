# REFERENCES_AUDIT.md

**Author**: Cowork agent (Claude), bibliographic audit pass 2026-04-25
**Subject**: verify the primary-source citations across all strategic
documents
**Method**: cross-check author names, journal volumes, publication
years against standard references in mathematical physics and
combinatorics

---

## 0. Method and scope

I audit citations in the following documents:

- `BLUEPRINT_F3Count.md`
- `BLUEPRINT_F3Mayer.md`
- `MATHLIB_GAPS.md`
- `MATHEMATICAL_REVIEWERS_COMPANION.md`
- `GENUINE_CONTINUUM_DESIGN.md`
- `PETER_WEYL_ROADMAP.md` (trimmed) and `PETER_WEYL_ROADMAP_HISTORY.md`
- `mathlib_pr_drafts/PR_DESCRIPTION*.md`

For each citation I verify:
- Author last names (correct spelling)
- Year of publication (consistent across docs)
- Journal abbreviation and volume (where given)
- Page range (where given) — light-touch; not all docs cite pages
- Conceptual accuracy (does the paper actually contain the claim
  attributed to it)

**This is a desk-audit using my training-data knowledge of the
mathematical physics literature**, not a fresh literature search.
Citations marked ✓ pass plausibility checks; ✗ are flagged for
human verification.

---

## 1. Citations and verification

### 1.1 Klarner — *Cell-growth problems*

**Cited in**: `BLUEPRINT_F3Count.md` §0, §2.2, `MATHLIB_GAPS.md` §2,
`MATHEMATICAL_REVIEWERS_COMPANION.md` §5.1, `mathlib_pr_drafts/AnimalCount.lean`
header, `mathlib_pr_drafts/PR_DESCRIPTION.md`,
`PETER_WEYL_ROADMAP.md` §5, `PETER_WEYL_ROADMAP_HISTORY.md` (preserved).

**Citation as written**:
> Klarner, *Cell-growth problems*, Canad. J. Math. **19** (1967),
> 851–863.

**Verification**:
- Author: David A. Klarner ✓
- Title: *Cell-growth problems* ✓ (this is the Klarner-Erdős
  framework paper for fixed polyominoes / lattice animals)
- Journal: Canadian Journal of Mathematics ✓
- Volume: 19 ✓
- Year: 1967 ✓
- Page range: 851–863 — **plausible** but I cannot verify the exact
  pages from training. The paper exists in volume 19 of Canad. J. Math.
  in 1967.

**Status**: ✓ verified except for exact page range (low risk).

### 1.2 Madras & Slade — *The Self-Avoiding Walk*

**Cited in**: `BLUEPRINT_F3Count.md` §0, §2.2,
`MATHEMATICAL_REVIEWERS_COMPANION.md` §5.1, §7,
`mathlib_pr_drafts/AnimalCount.lean` header, `PETER_WEYL_ROADMAP.md` §5.

**Citation as written**:
> N. Madras, G. Slade, *The Self-Avoiding Walk*, Birkhäuser (1993),
> Chapter 3.

**Verification**:
- Authors: Neal Madras and Gordon Slade ✓
- Title: *The Self-Avoiding Walk* ✓
- Publisher: Birkhäuser ✓ (Probability and its Applications series)
- Year: 1993 ✓
- Chapter 3: covers self-avoiding walk counting and connective
  constants ✓

The 2013 reprint by Modern Birkhäuser Classics is also legitimate;
some docs may cite that edition. Both are correct.

**Status**: ✓ verified.

### 1.3 Brydges & Kennedy — *Mayer expansions and the Hamilton-Jacobi equation*

**Cited in**: `BLUEPRINT_F3Mayer.md` §0, §3.1, §3.2,
`MATHEMATICAL_REVIEWERS_COMPANION.md` §4.4, §5.2, §7,
`PETER_WEYL_ROADMAP.md` §5.

**Citation as written**:
> Brydges & Kennedy, *Mayer expansions and the Hamilton-Jacobi
> equation*, J. Stat. Phys. **48** (1987), 19–49.

**Verification**:
- Authors: David C. Brydges and Tom Kennedy ✓
- Title: *Mayer expansions and the Hamilton-Jacobi equation* ✓
- Journal: Journal of Statistical Physics ✓
- Volume: 48 ✓
- Year: 1987 ✓
- Pages: **plausible** (vol 48 of JSP in 1987 has a paper at this
  range; cannot verify exact 19–49 from training)

**Status**: ✓ verified except for exact page range.

### 1.4 Battle & Federbush — random walks in cluster expansions

**Cited in**: `BLUEPRINT_F3Mayer.md` §3.1, `MATHEMATICAL_REVIEWERS_COMPANION.md` §5.2.

**Citation as written**:
> Battle–Federbush 1984 (random walks in cluster expansions)

**Verification**:
- Authors: Guy A. Battle and Paul Federbush ✓ (collaborated on
  cluster expansion / random-walk formulations in early 80s)
- Year: 1984 — there are multiple Battle-Federbush papers in this
  era; the 1984 paper *A note on cluster expansions, tree graph
  identities, extra 1/N! factors!!!* in *Letters in Mathematical
  Physics* is the most likely intended reference.
- **However**, the exact title and journal are not given in the
  blueprint. The reference is correct in spirit but should be
  pinned down before any external publication.

**Status**: ✓ verified (conceptually) but **needs more precise
citation** if used in academic-grade writeup. Suggest:
`G. Battle, P. Federbush, "A note on cluster expansions, tree graph
identities, extra 1/N! factors!!!", Lett. Math. Phys. 8 (1984),
1-3`. Verify before publication.

### 1.5 Kotecky & Preiss — *Cluster expansion for abstract polymer models*

**Cited in**: `BLUEPRINT_F3Mayer.md` §0, `MATHLIB_GAPS.md` §4,
`MATHEMATICAL_REVIEWERS_COMPANION.md` §7,
`mathlib_pr_drafts/PR_DESCRIPTION.md`,
`PETER_WEYL_ROADMAP.md` §5.

**Citation as written**:
> Kotecky–Preiss, *Cluster expansion for abstract polymer models*,
> Comm. Math. Phys. **103** (1986).

**Verification**:
- Authors: Roman Kotecký and David Preiss ✓
- Title: *Cluster expansion for abstract polymer models* ✓
- Journal: Communications in Mathematical Physics ✓ (CMP)
- Volume: 103 ✓
- Year: 1986 ✓
- **Pages**: not given in our docs. Standard reference: pp. 491-498.

**Status**: ✓ verified.

### 1.6 Osterwalder & Seiler — *Gauge field theories on a lattice*

**Cited in**: `BLUEPRINT_F3Mayer.md` §0,
`MATHEMATICAL_REVIEWERS_COMPANION.md` §4 intro, §7,
`PETER_WEYL_ROADMAP.md` §5.

**Citation as written**:
> Osterwalder–Seiler, *Gauge field theories on a lattice*,
> Ann. Physics **110** (1978).

**Verification**:
- Authors: Konrad Osterwalder and Erhard Seiler ✓
- Title: *Gauge field theories on a lattice* ✓
- Journal: Annals of Physics ✓
- Volume: 110 ✓
- Year: 1978 ✓
- Pages: standard reference is pp. 440-471.

**Status**: ✓ verified.

### 1.7 Seiler — monograph

**Cited in**: `BLUEPRINT_F3Mayer.md` §0,
`MATHEMATICAL_REVIEWERS_COMPANION.md` §5.2, §7.

**Citation as written**:
> Seiler, *Gauge Theories as a Problem of Constructive Quantum
> Field Theory*, ch. 4.

Sometimes given as:
> Seiler, *Gauge Theories as a Problem of Constructive Quantum
> Field Theory and Statistical Mechanics*, Lecture Notes in Physics
> **159** (1982).

**Verification**:
- Author: Erhard Seiler ✓
- Full title: *Gauge Theories as a Problem of Constructive Quantum
  Field Theory and Statistical Mechanics* ✓
- Series: Lecture Notes in Physics, Springer ✓
- Volume in series: 159 ✓
- Year: 1982 ✓

**Status**: ✓ verified. Suggest using the longer title in
academic-grade writeup; the truncated form is fine for blueprints.

### 1.8 Brydges — *A short course on cluster expansions*

**Cited in**: `BLUEPRINT_F3Mayer.md` §3.4 (implicitly),
`MATHEMATICAL_REVIEWERS_COMPANION.md` §4 intro, §7,
`PETER_WEYL_ROADMAP.md` §5.

**Citation as written**:
> Brydges, *A short course on cluster expansions*, Les Houches (1986).

**Verification**:
- Author: David C. Brydges ✓
- Title: *A short course on cluster expansions* ✓
- Venue: Les Houches Summer School lecture notes ✓
- Year: 1984 (lectures given), 1986 (publication in proceedings) —
  **mild inconsistency**. The published proceedings is in Osterwalder
  & Stora (eds), *Critical Phenomena, Random Systems, Gauge
  Theories*, North-Holland (1986). The lectures themselves are
  often cited as 1984.

**Status**: ✓ verified, with a note that "1986" refers to the
published proceedings; the lectures themselves were 1984. Either
form is academically acceptable.

### 1.9 Balaban — *Large field renormalization II*

**Cited in**: `MATHEMATICAL_REVIEWERS_COMPANION.md` §7,
`PETER_WEYL_ROADMAP.md` §5, `ROADMAP.md` §"External mathematics",
`UNCONDITIONALITY_ROADMAP.md` (history).

**Citation as written**:
> Balaban, *Large field renormalization. II. Localization,
> exponentiation, and bounds for the R operation*, Commun. Math.
> Phys. **122** (1989).

**Verification**:
- Author: Tadeusz Bałaban ✓ (Polish ł, often anglicised to "Balaban")
- Title: *Large field renormalization. II. Localization,
  exponentiation, and bounds for the R operation* ✓
- Journal: Communications in Mathematical Physics ✓
- Volume: 122 ✓
- Year: 1989 ✓

**Status**: ✓ verified.

### 1.10 Wilson — *Confinement of quarks*

**Cited in**: `MATHEMATICAL_REVIEWERS_COMPANION.md` §7.

**Citation as written**:
> Wilson, *Confinement of quarks*, Phys. Rev. D **10** (1974).

**Verification**:
- Author: Kenneth G. Wilson ✓
- Title: *Confinement of quarks* ✓
- Journal: Physical Review D ✓
- Volume: 10 ✓
- Year: 1974 ✓
- Pages: standard reference pp. 2445-2459.

**Status**: ✓ verified. This is the foundational paper of lattice
gauge theory.

### 1.11 Jaffe & Witten — *Quantum Yang-Mills Theory*

**Cited in**: `MATHEMATICAL_REVIEWERS_COMPANION.md` §6.3, §7.

**Citation as written**:
> Jaffe & Witten, *Quantum Yang–Mills Theory*, Clay Millennium
> Problem description (2000).

**Verification**:
- Authors: Arthur Jaffe and Edward Witten ✓
- Title: *Quantum Yang-Mills Theory* ✓
- Source: Clay Mathematics Institute Millennium Problem
  description, 2000 ✓
- Available at https://www.claymath.org/millennium/yang-mills/

**Status**: ✓ verified.

### 1.12 Holley & Stroock — *Logarithmic Sobolev inequalities and stochastic Ising models*

**Cited in**: `STATE_OF_THE_PROJECT_HISTORY.md` (legacy v1.46
content), various older docs.

**Citation as written**:
> Holley, R. & Stroock, D. "Logarithmic Sobolev inequalities and
> stochastic Ising models", Journal of Statistical Physics 46 (1987),
> 1159-1194.

**Verification**:
- Authors: Richard Holley and Daniel W. Stroock ✓
- Title: *Logarithmic Sobolev inequalities and stochastic Ising
  models* ✓
- Journal: Journal of Statistical Physics ✓
- Volume: 46 ✓
- Year: 1987 ✓
- Pages: 1159-1194 ✓

**Status**: ✓ verified.

### 1.13 Hölzl & Immler — Peter-Weyl in Isabelle

**Cited in**: `PETER_WEYL_ROADMAP.md` §5,
`PETER_WEYL_ROADMAP_HISTORY.md`.

**Citation as written**:
> Hölzl & Immler, *Peter–Weyl theorem in Isabelle/HOL* — reference
> for a comparable formalisation in a different proof assistant.

**Verification**:
- Authors: Johannes Hölzl, Fabian Immler ✓ (both worked on Isabelle
  formalisation of analysis/measure theory)
- Title: not pinned down in our citation. **The exact reference is
  unclear** — Hölzl and Immler have multiple Isabelle formalisation
  papers, and it is not certain that they have a Peter-Weyl
  formalisation specifically.

**Status**: ⚠ **needs verification before academic publication**.
The cited claim "Peter-Weyl in Isabelle/HOL" may be aspirational. If
no such paper exists, the reference should be removed or replaced
with a more accurate Isabelle / formalisation reference (e.g.
Bauer's work on representation theory in Isabelle, or whatever the
actual closest analogue is).

### 1.14 Stanley — *Enumerative Combinatorics*

**Cited in**: `MATHLIB_GAPS.md` §4 (Möbius lattice),
`mathlib_pr_drafts/PartitionLatticeMobius.lean`,
`mathlib_pr_drafts/PR_DESCRIPTION_Gap3.md`.

**Citation as written**:
> Stanley *Enumerative Combinatorics* vol. 1, Ch. 3.
> Stanley, *Enumerative Combinatorics* vol. 1, 2nd ed., Cambridge
> (2012), Proposition 3.10.4.

**Verification**:
- Author: Richard P. Stanley ✓
- Title: *Enumerative Combinatorics, Volume 1* ✓
- 2nd edition: Cambridge University Press, 2012 ✓
- Chapter 3 covers partitions, the partition lattice, and Möbius
  inversion ✓
- Proposition 3.10.4: I cannot verify the exact proposition number
  from training; the partition-lattice Möbius value is in §3.10
  (or §3.7 in the 1st edition).

**Status**: ✓ verified except for exact proposition number. Suggest
verifying against the actual book before academic publication.

### 1.15 Rota — *On the foundations of combinatorial theory I*

**Cited in**: `mathlib_pr_drafts/PartitionLatticeMobius.lean`,
`mathlib_pr_drafts/PR_DESCRIPTION_Gap3.md`.

**Citation as written**:
> Rota, *On the foundations of combinatorial theory I: Theory of
> Möbius functions*, Z. Wahrscheinlichkeitstheorie 2 (1964), 340–368.

**Verification**:
- Author: Gian-Carlo Rota ✓
- Title: *On the foundations of combinatorial theory I: Theory of
  Möbius functions* ✓
- Journal: *Zeitschrift für Wahrscheinlichkeitstheorie und
  verwandte Gebiete* (now Probability Theory and Related Fields) ✓
- Volume: 2 ✓
- Year: 1964 ✓
- Pages: 340-368 ✓

**Status**: ✓ verified.

---

## 2. Summary of issues

Out of 15 distinct primary-source citations, **13 are verified ✓**,
**2 require attention before academic publication**:

- **1.4 Battle-Federbush 1984**: title and journal not pinned.
  Recommend: `G. Battle, P. Federbush, "A note on cluster expansions,
  tree graph identities, extra 1/N! factors!!!", Lett. Math. Phys.
  8 (1984), 1-3`.
- **1.13 Hölzl-Immler Peter-Weyl**: existence of the cited paper is
  uncertain. Recommend: verify before any external publication; if
  no such paper exists, remove the citation or replace with
  whatever Isabelle/Coq formalisation actually exists for Peter-Weyl.

Both issues are in **non-blocking strategic documents** (blueprints
and Mathlib PR drafts). They do not affect the live Lean code or the
Lean proofs, only the human-readable bibliographic references.

---

## 3. Recommendations

### 3.1 Pre-publication checklist

Before any academic-grade publication based on this project:

- [ ] Pin down the Battle-Federbush 1984 reference (or replace with
      a more accurate one from the same authors).
- [ ] Verify the Hölzl-Immler Peter-Weyl claim. If no such paper
      exists, edit `PETER_WEYL_ROADMAP.md` and
      `PETER_WEYL_ROADMAP_HISTORY.md` to remove or replace.
- [ ] Verify Stanley Proposition number (3.10.4) against current
      edition.
- [ ] Verify exact page ranges where given.
- [ ] Add DOIs to all journal citations.

### 3.2 General hygiene

- All quoted theorems should ideally have at least one (author,
  year, [journal/volume]) verified-citation triple. The current
  state passes this for 13/15 references.
- For monographs, citing chapter or section is good practice; for
  papers, page range is good practice. Both are mostly present.
- The two flagged issues (1.4 and 1.13) should be tracked in
  `COWORK_FINDINGS.md` as observational findings if they are not
  resolved before the next major external communication about the
  project.

---

*Audit complete 2026-04-25 by Cowork agent.*
