# AQFT rapid-maintenance singularity paper — ai.viXra submission record

Date recorded: **2026-08-05**

Operation: **new AI-assisted paper submitted to ai.viXra.org**

Moderation/publication outcome and public identifier: **not recorded here**

## Submitted paper

Title: *Faithfulness, Not Algebra Type, Controls the Rapid-Maintenance
Singularity*

- Author: **Lluis Eriksson**
- Affiliation: **Independent Researcher**
- Category: **Mathematical Physics**
- Length: **31 pages, 1 figure**
- Frozen release commit: [`56e7ea46a38209b0a07f08a85260f55cdc863e4a`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/commit/56e7ea46a38209b0a07f08a85260f55cdc863e4a)
- [Exact submitted PDF](https://raw.githubusercontent.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/56e7ea46a38209b0a07f08a85260f55cdc863e4a/papers/aqft-rapid-maintenance/release-v8/Eriksson_Faithfulness_Rapid_Maintenance_AQFT_2026_v8.pdf)
- PDF size: **681,842 bytes**
- PDF SHA-256: `B0370F2ED9E30282F6DCC09F6E4AA32130340C5898F96DCA59F84B398EAF34C0`
- [Companion reproducibility ZIP](https://raw.githubusercontent.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/56e7ea46a38209b0a07f08a85260f55cdc863e4a/papers/aqft-rapid-maintenance/release-v8/AQFT_rapid_maintenance_v8_reproducibility.zip)
- ZIP size: **725,909 bytes**
- ZIP SHA-256: `53FCB0FB194923B0AC61CFA6907609FA8FC101804E4A539C2199512912C09BC6`

The PDF alone was submitted to ai.viXra. The archive is preserved separately
because the submission form does not accept supplementary files. It contains
the exact PDF, LaTeX source, numerical verification script, parameters, JSON
report, CSV data, generated figures, dependency list and a SHA-256 manifest.

## Exact submission metadata

The comments field was:

> 31 pages, 1 figure. Companion reproducibility archive containing complete
> LaTeX source, numerical verification code, data and SHA-256 manifest.

Keywords: algebraic quantum field theory; type III factors; quantum Markov
semigroups; Dirac reservoirs; relative Cauchy evolution; support leakage;
quantum thermodynamics.

The abstract submitted with the form was:

> We determine when rapid exact maintenance of a rank-deficient quantum target
> produces logarithmically divergent free-energy restoration power in
> algebraic quantum field theory. On every sigma-finite properly infinite
> factor we construct a bounded quantum Markov semigroup, a nonfaithful normal
> target and a faithful invariant reference state for which Araki relative
> entropy reduces exactly to a binary divergence. We derive the semigroup first
> from localized thermal fermionic probe collisions and then from one
> autonomous finite-bandwidth Dirac KMS reservoir with fixed smooth coupling.
> Exact memory equations yield an explicit finite-coupling Davies bound on
> finite van Hove windows. For a displayed compactly supported massless Dirac
> form factor, Araki--Wyss regularity, threshold behaviour and
> Fermi-golden-rule positivity give a completely bounded Davies approximation
> uniformly for all times with error of order `O(|lambda|)`; the sharper
> `O(lambda^2)` result is isolated under additional reduced-resonance
> hypotheses. We construct a background-covariant two-Dirac-field completion
> using Green operators, Moller maps and relative Cauchy scattering, proving
> naturality, causal factorization and exact spacelike triviality. A locality
> obstruction shows why a strictly local multiplier cannot coincide exactly
> with the solvable rank-one reservoir coupling, while a Feshbach reduction
> quantifies the correction. Finally, we prove that no fixed faithful vacuum or
> KMS restriction can exhibit the rank-boundary mechanism, but faithful
> families with a vanishing spectral floor recover its complete coefficient.
> The results separate algebra type, target faithfulness, microscopic
> realizability and regulator uniformity, and provide reproducible numerical
> audits of the finite-dimensional identities and explicit Dirac form factor.

## Reported verification and corrections

The release report records:

- three clean LaTeX passes, clean text extraction and visual inspection of all
  31 pages;
- an explicit all-time theorem for the displayed compact Dirac form factor,
  with a uniform `O(|lambda|)` approximation, Fermi-golden-rule positivity and
  Araki--Wyss regularity;
- a covariant completion using Green operators, Moller maps, relative Cauchy
  evolution, exact spacelike triviality and causal factorization;
- numerical checks shipped with their parameters, data and manifest;
- an adversarial Fable review that led to corrections of the second
  Araki--Wyss thermal weight, the charge-conjugation identification and several
  spectral conditions.

Those are release claims and packaged evidence. This submission record does
not constitute a new independent mathematical audit of them.

## Exact scope boundary

The all-time result in the submitted paper is the stated `O(|lambda|)` bound
for the displayed form factor. The sharper `O(lambda^2)` improvement remains
conditional on additional reduced-resonance hypotheses and is not promoted to
an unconditional conclusion here. The paper also separates the exactly
solvable rank-one reservoir coupling from strictly local multiplier couplings
and quantifies the latter through a Feshbach reduction.

This AQFT paper is independent of the canonical Yang--Mills proof-state DAG.
Its submission and artifact freeze do not update the recorded
`YangMillsCore` checkpoint and do not claim progress on the four-dimensional
Yang--Mills mass-gap problem.

The preceding 2026-08-05 Dobrushin C*-state submission remains recorded in
[`DOBRUSHIN-CSTAR-SUBMISSION-20260805.md`](DOBRUSHIN-CSTAR-SUBMISSION-20260805.md).
