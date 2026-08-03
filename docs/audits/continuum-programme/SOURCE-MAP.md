# Primary-source map: SU(2), OS reconstruction, and continuum limits

Audit base: `7c6aaab2f67fd5b9c4a23c45bbffebf476ef221a`  
Packet: `continuum-os-source-packet.json`  
Validation:
`python docs/audits/continuum-programme/validate_source_packet.py`

This index is the readable view of the field-by-field JSON packet. Technical
credit is restricted to primary papers or the official Clay statement. Search
snippets and secondary summaries were used only to locate primary material.

## Result at a glance

| Topic | External standard | Repository comparison at the audit base | Verdict |
|---|---|---|---|
| Wilson SU(2) reflection positivity | Menotti--Pelissetto; Lüscher; Osterwalder--Seiler pending exact extraction | Published OS modules and Paper 13 are `Z_2`, not `SU(2)`. Paper 13 says its half-path-to-whole-path identification is numerically verified and not proved. No public SU(2) producer ref or PR exists. | **BLOCKED** for SU(2) artefact; Paper 13 limitation **CONFIRMED** |
| Continuum OS reconstruction | Corrected OS II theorem: `E0'` or `E0''` plus `E1-E4` | The repository state explicitly disclaims OS/Wightman reconstruction. Finite-lattice positivity and abstract transfer-operator bricks do not match the corrected continuum hypotheses. | **PASS** for current disclaimer; **BLOCKED** for any new reconstruction artefact |
| Thermodynamic versus continuum limit | Lüscher distinguishes `M,L -> infinity` from a critical/large-distance limit; Clay requires `a -> 0` and volume `-> infinity` | `tendsto_freeBoundaryThermodynamicExpectation` is a whole-sequence volume limit in a uniform local KP regime. No lattice-spacing family or `a -> 0` conclusion appears in the theorem. | **PASS** as thermodynamic-limit theorem; **FAIL** if advertised as continuum |
| Tightness, nontriviality, renormalisation | Clay official description: uniform estimates, regulator-dependent counterterms, non-Gaussianity for nonlinear examples, and no compactness-only solution | No public `CONT-C0`/`CONT-C1` artefact exists. The current state disclaims a continuum limit. | **BLOCKED** for producer artefacts |
| Clay requirement | Nontrivial QYM on `R^4` for every compact simple `G`, full axiomatic strength, and `Delta > 0` | Current state says no continuum limit, no OS/Wightman reconstruction, and no continuum mass gap. The available objects are finite-lattice, fixed-regulator, abelian, conditional, or thermodynamic-limit components. | **PASS** for non-overclaim; Clay claim **FAIL** against literal requirements |

## 1. Menotti and Pelissetto (1987)

- Primary record and DOI:
  <https://doi.org/10.1007/BF01221251>;
  open PDF:
  <https://scispace.com/pdf/general-proof-of-osterwalder-schrader-positivity-for-the-1dpcazlzxm.pdf>.
- Locator: printed pp. 369-373; especially Eq. (2.4), reflection definitions
  (2.5)-(2.6), the link-plane split (2.7), and site-plane analysis
  (2.11)-(2.25).
- Hypotheses: Wilson lattice action with gauge and Wilson-fermion fields;
  gauge-invariant `F` in the stated positive half-space; the fermionic
  statement uses hopping parameter `K < 1/6`. Reflection is antilinear and
  includes ordinary complex conjugation.
- Conclusion: the reflected expectation of `F` with itself is nonnegative.
  The paper extends the link-cutting-plane proof to site-containing planes and
  covers arbitrary Euclidean separations for the specified gauge-invariant
  observables.
- Exact applicability: authoritative comparison for the geometry of both
  reflection planes, gauge-invariant-observable scope, orientation/conjugation,
  and Wilson-action-specific splitting.
- Discrepancy: this source does not prove a future repository definition is the
  Wilson Gibbs pairing. The producer still owes its lattice-specific gluing,
  boundary classification, product-Haar reindexing, normalisation, and pure
  `SU(2)` specialization. It gives neither a continuum limit nor a mass gap.

## 2. Lüscher (1977)

- Primary PDF and DOI:
  <https://bib-pubdb1.desy.de/record/396349/files/7611148.pdf?version=1>;
  <https://doi.org/10.1007/BF01614090>.
- Locators:
  - printed p. 284 / viewer P3: infinite-volume lattice versus continuum
    critical/large-distance limit;
  - Proposition 1, printed pp. 287-288 / viewer P6: bounded,
    self-adjoint, gauge-invariant, strictly positive `T`, and
    `H = -a^{-1} log T`;
  - Eqs. (22)-(23), same pages: Haar quadratic form and irreducible-character
    expansion;
  - Proposition 2, printed p. 289 / viewer P7: identification of Euclidean
    expectations with operator Schwinger functions under stated boundary
    conditions.
- Hypotheses: finite four-dimensional Wilson lattice, `G = SU(N)`, invariant
  Haar measure with the paper's normalisation, specified gauge fixing and
  spatial/time boundary conditions; the fermionic construction takes
  `0 < K < 1/6`.
- Conclusion: a physical Hilbert space and strictly positive transfer matrix
  are constructed. For the one-link central kernel, positivity is equivalent
  to positivity of all character coefficients; positivity follows from
  nonnegative tensor-product multiplicities and occurrence of all irreducibles.
- Exact applicability: this is the decisive external check on character
  normalisation, representation multiplicities, Haar quadratic forms, lattice
  transfer positivity, and the physical conversion from a transfer eigenvalue
  to energy through `1/a`.
- Discrepancy: it does not establish vacuum uniqueness, boundary-condition
  independence, a continuum limit, or a gap uniform in volume and `a`. A
  producer must show where any representation-dimension factors enter under
  its own character convention.

## 3. Osterwalder and Schrader I (1973), with correction attached

- Primary PDF and DOI:
  <https://projecteuclid.org/journals/communications-in-mathematical-physics/volume-31/issue-2/Axioms-for-Euclidean-Greens-functions/cmp/1103858969.pdf>;
  <https://doi.org/10.1007/BF01645738>.
- Locator: printed pp. 87-90, axioms and original `E -> R` theorem.
- Hypotheses as originally stated: `E0` temperedness, `E1` Euclidean
  covariance, `E2` positivity, `E3` symmetry, and `E4` cluster.
- Original conclusion: reconstruction of Wightman distributions satisfying
  `R0-R5`.
- Exact applicability: the labels identify the separate obligations and show
  that reflection positivity is only `E2`.
- Discrepancy: OS II, printed p. 282, says OS I Lemma 8.8 is wrong and that
  sufficiency of the original `E0-E4` package is open. Therefore OS I cannot be
  cited alone as the operative sufficient theorem.
- Local acquisition evidence: primary PDF SHA-256
  `9E45658863823A5A769891141F8EB7B935F0DDFEC62F6554D9F802D8157DA878`.

## 4. Osterwalder and Schrader II (1975)

- Primary PDF and DOI:
  <https://projecteuclid.org/journals/communications-in-mathematical-physics/volume-42/issue-3/Axioms-for-Euclidean-Greens-functions-II-with-an-Appendix-by/cmp/1103899050.pdf>;
  <https://doi.org/10.1007/BF01608978>.
- Locators: printed p. 282 for the correction to OS I; printed p. 287,
  Eqs. (4.1)-(4.3) and Theorem `E' (or E'') -> R'`.
- Hypotheses: a sequence of Euclidean Green-function distributions satisfying
  the stronger `E0'` linear-growth condition, or the slightly stronger `E0''`,
  together with `E1-E4`.
- Conclusion: the sequence determines a unique Wightman QFT; its Wightman
  distributions satisfy all `R0-R5` and the additional `R0'` growth property.
- Exact applicability: this is the operative continuum reconstruction standard.
  A producer must match the distribution space, growth estimate, covariance,
  positivity, symmetry, and cluster property one by one.
- Discrepancy: none of finite-lattice reflection positivity, a null quotient,
  a finite transfer matrix, or an abstract implication from clustering to an
  operator bound supplies `E0'/E0''` and `E1-E4` for continuum Schwinger
  functions. The theorem itself does not prove a positive mass gap.
- Local acquisition evidence: primary PDF SHA-256
  `643A45D3037F788BA80ECFEF2F218778D7D511102F75FFC44468E20C16382C71`.

## 5. Osterwalder and Seiler (1978)

- DOI and publisher record:
  <https://doi.org/10.1016/0003-4916(78)90039-8>.
- Locator: Annals of Physics 110 (1978), pp. 440-471.
- Confirmed conclusion at abstract level only: the paper treats lattice
  approximations to Yang--Mills and fermion fields, verifies physical
  positivity for the approximation's Schwinger functions, and obtains a
  positive self-adjoint transfer matrix.
- Verdict: **BLOCKED** for exact technical use. This desk could not inspect the
  publisher full text, so it does not assign a theorem number, formula,
  normalisation, or precise hypothesis from memory.
- Exact applicability after unblocking: likely the closest direct primary
  comparator for the Wilson functional-integral route.
- Discrepancy: until the primary theorem is extracted, the citation is a
  locator, not evidence for a producer's splitting or coefficient claim.

## 6. Jaffe and Witten, official Clay description

- Official landing page and PDF:
  <https://www.claymath.org/millennium/yang-mills-the-maths-gap/>;
  <https://www.claymath.org/wp-content/uploads/2022/06/yangmills.pdf>.
- Exact problem locator: printed p. 5, Section 4.
- Requirement: for any compact simple gauge group `G`, construct a nontrivial
  quantum Yang--Mills theory on `R^4`, with axiomatic properties at least as
  strong as the cited Wightman/OS standards, and a mass gap `Delta > 0`.
  The preceding paragraph defines the gap as absence of Hamiltonian spectrum in
  `(0, Delta)`.
- Regulator/limit locators:
  - printed pp. 6-7: compact approximations versus `R^4`; convergence and
    uniform estimates;
  - printed pp. 7-8: Euclidean-invariant, reflection-positive, ergodic Borel
    measures; Gaussian gives a free field and non-Gaussianity is required for a
    nonlinear field in the example;
  - printed p. 8: cutoff `kappa`, finite volume `V`, divergent counterterms, and
    convergence after renormalisation;
  - printed p. 10: Wilson finite-dimensional lattice integrals require both
    lattice-spacing and infinite-volume limits; reflection positivity survives
    the Wilson approximation;
  - printed p. 11 and footnote 2: a volume-uniform mass gap needs new ideas, and
    compactness/weak existence alone is explicitly excluded unless properties
    of the limit, including axioms and a gap, are established.
- Exact applicability: external requirement matrix for `CONT-C0`, `CONT-C1`,
  and every Clay headline.
- Discrepancy: it is not a ready-made tightness theorem for a producer's chosen
  topology. The producer must define its regulator family, topology,
  observables, counterterms, full or subsequential convergence, uniqueness,
  nontriviality test, and uniform physical gap.

## Repository comparison at `7c6aaab2`

### Fixed-spacing thermodynamic theorem

`YangMills/L1_GibbsMeasure/FreeBoundaryThermodynamicLimit.lean:117` proves
`tendsto_freeBoundaryThermodynamicExpectation` for an explicit cofinal
free-boundary volume sequence under `UniformLocalKPRegime`. Its variables do
not include a lattice spacing tending to zero, a critical bare-coupling path,
renormalised observables, or continuum distributions. It is therefore exactly
a thermodynamic-limit result in its stated regime, not a continuum result.

### Paper 13 / Z₂ OS status

`papers/spatial-os/spatial_os.tex:43-60` says the positive form is defined as a
sum over pairs of halves and that the identification with the full-path Gibbs
sum is verified to `10^-12` by brute force but not proved. The numerical script
`scripts/judge_spatial_os.py` is committed; no matching committed transcript
was found by:

```text
git ls-tree -r --name-only 7c6aaab2 -- scripts |
  rg "judge_spatial_os|spatial_os.*transcript"
```

The output contains `scripts/judge_spatial_os.py` only. Thus the current paper
does not claim the full OS axiom, and its own limitation is confirmed. The
`SU2-2G` gate requires an `SU(2)` producer to prove the continuous-group
product-Haar gluing/factorisation rather than inherit this finite `Z_2`
numerical witness.

### Clay comparison

`CURRENT-STATE.md:2879-2885` says there is no continuum limit, no
OS/Wightman reconstruction, and no continuum Yang--Mills mass gap. Against the
official requirements, the missing pieces are:

1. a regulator-removed nontrivial theory on `R^4`;
2. corrected OS/Wightman axioms for the continuum Schwinger functions;
3. removal of `a` and volume with the required uniform controls;
4. renormalised gauge-invariant local fields/correlations with nontriviality;
5. a Hamiltonian gap `Delta > 0` in physical units after those limits.

Finite-lattice reflection positivity, fixed-`a` thermodynamic convergence, an
abstract operator implication, a `Z_2` example, or a lattice-unit eigenvalue
does not satisfy any omitted item by association. The current disclaimer
therefore passes the external comparison; any headline claiming the Clay
result from the present tree fails with this five-item witness.

## Source-desk limits

- No exact theorem claim is credited to Osterwalder--Seiler 1978 until its
  primary full text is inspected.
- The source packet does not judge a nonexistent producer artefact.
- The JSON is schema-compatible but remains in this audit directory because
  the desk is not authorised to edit `docs/source-db/catalogs/`.
- Fable and Opus supplied no accepted output; they are not sources.
