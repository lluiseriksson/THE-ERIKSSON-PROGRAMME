# Exact v5 notation audit and source correction candidate

Frozen AIRR version: ARR-2026-7EPM3V3DP796BBRR v5, PDF SHA256 69d802bfea8f8f23bfe6aba03cdc4835feac777e024c939040c7f099a11462c8. Frozen TeX SHA256 97dcbdb96e4dcc2f8eb3c892ea164c0dfdb4b887abd62f6e70a2a4bcf8fef621. Reviewer: the completed Gemini report published by AIRR PR368; its grade, wording, recommendation and every objection stay unchanged. This audit is by the preparing programme agent, not independent peer review.

## Disposition of the six reported potential errors

1. Missing c in Eq28: contradicted by exact source and rendered page30; previously documented operator response134. Do not insert a second c.
2. Inconsistent use of c in the page30 cube counterexample: same false premise. Eq28 already has c. No correction to the displayed bound is justified by this allegation.
3. Page25 s m^r: confirmed, should be s mu^r. Here s<=mu^(-r), so s mu^r<=1, independently of the adjoint dimension m used in earlier sections.
4. Page25 Section1: confirmed stale cross-reference. The actual necessary J-dimensional subspace argument is in Section16, immediately before the critical moment theorem. Add a stable section label and reference it.
5. Page28 8Dm, 2Dm s and denominator2Dm+c: confirmed stale weight notation. Correct all three to mu, as the surrounding hypotheses explicitly say a<=2mu or a=mu.
6. Proposition11.3 allegedly states R>1: contradicted by exact source and visually inspected page15; both already state R>=1. No change. The separate proof of a Fourier counting lemma later uses R>1 in a different context; it is not Proposition11.3.

An additional real stale m, omitted from the report's list, occurs in the divergence-zero line-test energy on page28: 2(D-1)mns must be 2(D-1)mu ns. Its following denominator already uses mu.

## Local analytic checks of the intended corrections

For a<=2mu, each directed edge contributes at most 2 a(x)(|u(x+e_i)|^2+|u(x)|^2). Summing all D directed occurrences and their endpoints gives E_a(u)<=8Dmu ||u||^2, also for n=2 with parallel occurrences counted. This is an elementary upper bound, not a new theorem or an extra coefficient assumption.

For a=mu and u=1 off S, at most 2D|S| directed edges cross S. Thus E_mu(u)<=2Dmu |S| and ||u||^2=n^D-|S|. Coercivity gives |S|>=cn^D/(2Dmu+c). For the actual j-line field, at most |S| lines are hit; transverse edges contribute at most 2(D-1)mu n|S| and the norm is at least n(n^(D-1)-|S|). This yields the already printed physical denominator2(D-1)mu+c. No physical/continuum hypothesis is removed.

## Artifact verification and limits

Pages15,25,28 were visually inspected from existing Colab render126, and their SHA256 values match 126-recovery-report.json bound to the exact PDF. Page15:9ca3c048ae91f0b37a2a8223f799f9c843fe5684748d16fee32ba38b0ca1a83f; page25:e69913b27efac4b629a27373d2155e0510206a1b85eca380997c9fd1a6b7537a; page28:20804482833ab33f95b0b5d70e1e70e5a3cb260c439d6a63689ea4330cccf625.

The candidate is a COPY with exactly seven substitutions: five weight-symbol corrections, one section reference and its label. Original v5 TeX/PDF unchanged. correction-audit.json gives exact replacements and input/output hashes. flat_critical_corrected.tex is not a published or reviewed new PDF. It deliberately retains historical manuscript disclosures, which must be reconciled for any complete subsequent revision. No new score transfers. No Lean, Lake, numerical execution, PDF build or runtime was performed in this unit. No new originality claim. PR29 remains20/41, TermSource0; the generic common-refinement route remains stopped at counter3.

NEXT: assemble a coherent new revision, including current model-review context and remaining editorial cleanup, then compile only in an own disconnected-prepared Colab Linux runtime, inspect all pages of the resulting exact PDF, retain first exact-artifact assessment and obtain/use its actual artifact permission if needed. Do not redeposit unchanged v5 or repeat Gemini review just to improve a grade. These source corrections alone do not authorize acceptance or count as a new paper.
