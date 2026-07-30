# CONTINUUM-C1 source packet

Only primary papers or authoritative lecture notes are used. A statement is
treated as reusable only after checking its hypotheses and printed location.

## 1. Chevyrev: two-dimensional Yang--Mills as a distribution

I. Chevyrev, *Yang--Mills measure on the two-dimensional torus as a random
distribution*, Communications in Mathematical Physics **372** (2019),
1027--1058.
[DOI 10.1007/s00220-019-03567-5](https://doi.org/10.1007/s00220-019-03567-5).

Checked:

- Theorem 1.1, printed pp. 1028--1029: for a compact, connected, simply
  connected group and `α∈(1/2,1)`, a distributional connection on the
  two-torus realizes the two-dimensional Yang--Mills holonomy law.
- Theorem 3.26, printed p. 1041: tight discrete norms yield subsequential
  convergence in a weaker distributional space.
- The discussion on printed p. 1030 warns that higher dimensions need
  renormalization and that unsmoothed Wilson loops may fail already in 3D.

Reusable: the obligation pattern “uniform scale-aware tail plus compact
embedding”. Not transferable: dimension 2 and heat-kernel action do not match
the repository's four-dimensional Wilson strong-coupling law.

## 2. Lüscher: dimensions and continuum tuning

M. Lüscher, *Advanced Lattice QCD*, Les Houches lectures (1997), DESY 98-017.
[Author-hosted PDF](https://luscher.web.cern.ch/lectures/LesHouches97.pdf).

Checked:

- printed pp. 1--2: the cutoff is proportional to `a⁻¹`, and the continuum
  limit is an `a→0` problem distinct from a thermodynamic limit;
- printed pp. 3--4, equation (2): the Wilson action sums
  `tr(1-U(p))`, with `U(x,μ)=exp(g₀aA_μ(x))`;
- printed p. 8: local gauge-invariant fields need appropriate
  renormalization factors.

Reusable: the engineering-dimension and cutoff audit. Not transferable: these
lectures do not prove nonperturbative four-dimensional tightness.

## 3. Balaban: localized small-field activities

T. Balaban, *Renormalization group approach to lattice gauge field theories:
II. Cluster expansions*, Communications in Mathematical Physics **116**
(1988), 1--22.
[DOI 10.1007/BF01239022](https://doi.org/10.1007/BF01239022).

Checked:

- Lemma 1, printed pp. 9--10, equation (1.36): localized analytic terms obey
  a small-field exponential localization bound;
- Lemma 2, printed p. 11: the localized expressions have the stated gauge
  invariance;
- Lemma 3, printed p. 20, equation (2.38): under all preceding restrictions,
  the resummed activity obeys exponential localization.

Reusable: constants, metrics, analytic domains, and small-field restrictions
must travel with the estimate. Not transferable: the substantial conditional
small-field construction is absent here; importing only the bound's shape
would launder hypotheses.

## 4. Osterwalder--Seiler: lattice theory and positivity

K. Osterwalder and E. Seiler, *Gauge field theories on a lattice*, Annals of
Physics **110** (1978), 440--471.
[DOI 10.1016/0003-4916(78)90039-8](https://doi.org/10.1016/0003-4916(78)90039-8).

Only the bibliographic record and abstract were accessible. No numbered
theorem from this paper is attributed or imported.

## 5. Driver: rigorous two-dimensional Wilson convergence

B. K. Driver, *YM2: continuum expectations, lattice convergence, and lassos*,
Communications in Mathematical Physics **123** (1989), 575--616.
[Author-hosted PDF](https://mathweb.ucsd.edu/~bdriver/DRIVER/Papers/Drivers_Papers/A3-YM2-Expectations.pdf);
[DOI 10.1007/BF01218586](https://doi.org/10.1007/BF01218586).

Checked:

- the introduction, printed p. 576, states convergence of gauge-fixed Wilson
  and Villain lattice approximations for gauge-invariant functions;
- Definition 8.4, printed p. 601, fixes the Wilson one-face density;
- Theorem 8.8, printed p. 602, assumes a faithful representation and
  `t(ε)/ε²` a positive integer with `t(ε)=t+O(ε)`, and proves uniform
  convergence of convolution powers to the heat kernel;
- Theorem 8.10, printed p. 603, proves convergence for bounded measurable
  observables on planar graph approximations; Corollary 8.11, printed p. 604,
  is the gauge-invariant form.

Reusable: rigorous precedent for planar two-dimensional Wilson convergence.
Not transferable: it neither gives the preregistered explicit
`3g⁴Aa²` error nor the repository-typed finite free-boundary `U(1)`
factorization required by E2/G1.

## 6. Cao--Chatterjee: a typed smoothed tightness criterion

S. Cao and S. Chatterjee, *A State Space for 3D Euclidean Yang--Mills
Theories*, Communications in Mathematical Physics **405** (2024), article 3.
[Open publisher-version PDF](https://d-nb.info/1326538667/34);
[DOI 10.1007/s00220-023-04870-y](https://doi.org/10.1007/s00220-023-04870-y).

Checked:

- printed p. 5 defines regularized Wilson loops after positive
  Yang--Mills-flow time;
- Theorem 1.6, printed p. 6: tightness of the smoothed Yang--Mills actions at
  every `t>0` yields a weakly convergent subsequence on the nonlinear
  distributional gauge-orbit state space;
- Theorem 1.12, printed pp. 9--10: uniform expected smoothed action follows
  under the paper's explicit GFF-like hypotheses;
- Remark 1.16, printed p. 10: the key probabilistic smoothing input breaks
  down in critical dimension four.

Reusable: a precise smoothing-to-tightness obligation. Not transferable: this
is a conditional three-dimensional criterion, and neither its GFF-like
hypotheses nor its heat-flow state space occurs in the repository.

## Consequence for C1

No checked source supplies a four-dimensional weak-coupling, scale-uniform
producer under the repository's hypotheses. Driver validates E2 as a natural
two-dimensional direction but does not discharge its explicit-rate gates.
The autonomous deliverable is therefore the quantified strong-coupling-window
no-go E1.
