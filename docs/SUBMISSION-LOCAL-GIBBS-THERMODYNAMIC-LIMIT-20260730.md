# Submission record — local Gibbs thermodynamic limit

Owner-reported submission date: **2026-07-30**.

Archive route: **arXiv**, primary category `cs.LO`, recommended cross-list
`math-ph`.  A public arXiv identifier has not yet been reported and is not
inferred here.

## Submitted artifact

- Title: *A Machine-Checked Thermodynamic Limit for Local Lattice Gauge Gibbs
  States*
- Author: Lluis Eriksson
- Extent: 7 pages, no figures
- Repository PDF:
  [`output/pdf/local_gibbs_thermodynamic_limit.pdf`](../output/pdf/local_gibbs_thermodynamic_limit.pdf)
- Public repository checkpoint: `d6282a83`
- Formal source checkpoint named in the PDF: `0be45284`
- PDF size: 104,063 bytes
- PDF SHA-256:
  `0a494cd745da4760428ad4e915075469c95eab7e638856b5e49925ec662a0919`
- Google Drive copy:
  <https://drive.google.com/file/d/1w_ydgw6EFPDsFr6oi5807dEk4F7IajUi/view?usp=drivesdk>

The owner-supplied local upload file, the blob retrieved from `d6282a83`, and
the repository PDF are byte-identical at the hash above.

## Abstract submitted

> We formalize in Lean 4 the thermodynamic limit of bounded local Gibbs
> expectations for a periodic lattice gauge model in a uniform
> Kotecky-Preiss regime. The proof treats the complete finite-volume sequence:
> an exact one-volume marked expansion cancels the extensive far gas
> algebraically, common-window terms are transported exactly, and the
> remaining boundary contribution is bounded by an existing volume-uniform
> pinned cluster tail. The resulting explicit Cauchy modulus tends to zero,
> so completeness constructs an infinite-volume positive normalized real
> local state. On the intrinsic integer-coordinate local-observable algebra,
> the state carries a genuine additive action of Z^d and is invariant under
> every integer translation, including inverses. For SU(2), Haar probability
> measure, and the physical Wilson plaquette energy Re tr(U), the hypotheses
> are discharged throughout the explicit punctured intervals
> 0 < |beta| <= 10^-5 in d=2 and 0 < |beta| <= 10^-6 in d=4. We construct a
> genuine centered free-boundary exhaustion and prove that its complete
> cofinal sequence converges to the same state as periodic boundary
> conditions. The normalized finite-volume two-plaquette
> truncated-correlation bound also passes to the state under explicit
> eventual realization and separation hypotheses. We do not claim arbitrary
> boundary conditions, a C*-algebraic state, a continuum limit,
> Osterwalder-Schrader reconstruction, or progress on the continuum
> Yang-Mills mass-gap problem.

## Submission metadata

- Comments:
  `7 pages, no figures. Lean 4 formalization. Verification artifact: https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/tree/d6282a83`
- Optional ACM classes: `F.4.1; D.2.4`
- `Report-no`, `Journal-ref`, and `DOI`: left blank.

## PDF audit

The submitted PDF is A4, PDF 1.4, unencrypted, has no JavaScript or active
form, and renders as seven complete pages.  Cambria, Cambria Bold, and Cambria
Italic are embedded subsets.  The ReportLab base-14 Helvetica and Courier
fonts are not embedded.  This is a portability warning, not evidence of a
different submitted binary; the submitted artifact is frozen by the hash
above.

## Claim boundary

The paper constructs a machine-checked thermodynamic limit in a uniform
strong-coupling KP regime, including a genuine integer-translation action,
one explicit centered free-boundary exhaustion, and passage of a stated
two-plaquette truncated-correlation bound.  It does not prove arbitrary
boundary-condition independence, construct a `C*`-algebraic state, take a
continuum limit, perform Osterwalder--Schrader reconstruction, or advance the
continuum Clay mass-gap claim.
