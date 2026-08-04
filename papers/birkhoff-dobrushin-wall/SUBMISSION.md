# (46) Submission sheet: Local Tanh, Global Wall

Status: final scientific body with author fixed as **Lluis Eriksson**; **do not submit until the license is confirmed**.

## Recommended route

1. Deposit the technical note on arXiv.
2. Primary category: `math.PR` (Probability).
3. Suggested cross-list: `math.FA` (Functional Analysis). Use the cross-list only if the submission form permits it or the moderator accepts it.
4. After an independent mathematical audit, submit the 10-page note to *Electronic Communications in Probability* (ECP). ECP is the best-fit journal route because it publishes short probability papers; the initial journal PDF must be converted to the current ECP LaTeX template before journal submission.

This route is deliberately narrow. The paper does not claim a volume-uniform Birkhoff gap. Its publishable unit is the equality classification, the exact tensor wall, and the localization comparison.

## Author data

The manuscript and arXiv metadata identify the author as `Lluis Eriksson`.

- Authors: `Lluis Eriksson`
- Collaboration: none stated
- Affiliations: `[OPTIONAL, BUT MUST BE ACCURATE IF USED]`
- Corresponding email: `[REQUIRED BY THE SUBMISSION ACCOUNT/EDITORIAL SYSTEM]`
- ORCID: `[OPTIONAL]`
- Author consent: confirmed by the owner's explicit author instruction on August 4, 2026

Do not infer an affiliation from an email address or residence.

## arXiv metadata (copy/paste)

**Title**

```text
Local Tanh, Global Wall: Tensorization, Equality, and the Birkhoff--Dobrushin Divide
```

**Authors**

```text
Lluis Eriksson
```

**Abstract** (ASCII and under arXiv's 1920-character limit)

```text
For a strictly positive finite Markov kernel $P$, Birkhoff's projective contraction coefficient is $\tanh(\Delta_H(P)/4)$, whereas Dobrushin's coefficient is the exact contraction coefficient for oscillation. The sharp comparison $\delta(P)\leq\tanh(\Delta_H(P)/4)$ is known. We give a finite, explicit equality classification: apart from the rank-one case, equality holds exactly when a diameter-realizing pair of rows has a likelihood ratio taking two reciprocal values. On the closed probability simplex, the same classification holds inside a common face, while across distinct faces the infinite-distance bound is an equality exactly for disjoint supports. We then record the exact tensor law $\Delta_H(P\otimes Q)=\Delta_H(P)+\Delta_H(Q)$. Consequently the global Birkhoff coefficient of $P^{\otimes L}$ obeys hyperbolic addition and tends to one for every nonzero single-site diameter. The global Dobrushin coefficient also tends to one in every nontrivial product, while each coordinate oscillation contracts with the exact, volume-independent factor $\delta(P)$. For the binary Ising link all local quantities coincide at $\tanh |J|$, but the global projective coefficient is $\tanh(L|J|)$. Thus the same calculation both explains the ubiquitous local $\tanh$ and supplies a sharp wall against deducing a volume-uniform gap from the global tensor cone. We separate classical inputs, elementary tensor consequences, and the narrow equality and localization synthesis, and include a reproducible exact-arithmetic kill test. A companion Lean module checks the finite normalized results; the classical analytic Birkhoff--Hopf input remains external.
```

**Comments**

```text
10 pages, no figures. Technical note. Includes an exact-arithmetic kill test and a companion Lean 4 formalization; the classical analytic Birkhoff--Hopf theorem is used as an external input.
```

**MSC class**

```text
60J10 (Primary) 15B51, 47B65, 82B20 (Secondary)
```

**Keywords**

```text
Hilbert projective metric; Birkhoff contraction; Dobrushin coefficient; total variation; tensor products; Markov kernels; equality cases; Ising model
```

**Other fields**

- Journal reference: leave blank.
- DOI: leave blank.
- Report number: leave blank unless a real institution assigned one.
- License: `[REQUIRED AUTHOR DECISION]`. For maximum journal compatibility, check the target journal/funder policy before choosing. arXiv's license choice is irrevocable for that version.

## arXiv upload checklist

- Upload `candidate-46-arxiv-source.zip`; it contains one self-contained top-level TeX file and no generated PDF.
- Confirm the detected compiler and top-level file `birkhoff_dobrushin_wall.tex`.
- Compare arXiv's generated PDF page by page with the frozen final PDF.
- Paste the ASCII metadata above; do not paste Unicode punctuation from a PDF viewer.
- Confirm the author name, any genuine affiliation, category, and license.
- Preview once more before selecting the final submit action.
- Keep the resulting arXiv identifier and DOI for the repository record and any journal submission.

## ECP journal route (after independent audit)

Current destination: *Electronic Communications in Probability*.

- Scope/length fit: short research articles in probability; the manuscript is 10 pages.
- Initial submission portal: `https://www.e-publications.org/ims/submission/`
- Required preparation: convert the manuscript to the current ECP LaTeX template and submit the PDF through EJMS.
- License at publication: ECP states that published articles use CC BY 4.0.
- Fees: ECP states that author/publication fees are not required.

**Cover-letter draft**

```text
Dear Editor,

Please consider “Local Tanh, Global Wall: Tensorization, Equality, and the Birkhoff--Dobrushin Divide” for publication in Electronic Communications in Probability.

The paper is a 10-page technical note on contraction coefficients of finite Markov kernels. It clearly separates the classical Birkhoff--Hopf formula and the known sharp total-variation--Hilbert inequality from its contribution: a finite equality classification (including the closed-simplex singular branch), the exact additive tensor law and resulting obstruction to a volume-uniform global projective contraction, and the coordinate-local Dobrushin comparison. The note expressly does not claim a volume-uniform spectral gap from Birkhoff contraction.

An exact-arithmetic kill test and a companion Lean 4 formalization support the finite normalized statements; the classical analytic Birkhoff--Hopf input remains external.

[AUTHOR TO CONFIRM: The manuscript is original, is not under consideration elsewhere, and all authors consent to this submission.]

Sincerely,
[CORRESPONDING AUTHOR]
```

## Frozen paper identity

- Branch at packaging: `codex/candidate-46-birkhoff-dobrushin-wall`
- Scientific-body commit before author update: `7c2401e2a2c7`
- Final PDF: `output/pdf/birkhoff_dobrushin_wall.pdf`
- PDF bytes: `110645`
- PDF SHA-256: `2d9791a475e21a793f63cc2f00793968c28e3cc50cd1f5716dc3babc7a638d86`
- TeX: `papers/birkhoff-dobrushin-wall/birkhoff_dobrushin_wall.tex`
- TeX bytes (LF worktree): `31301`
- TeX SHA-256 (LF worktree): `399d0495141f67e3c335a937438c6e29232722eb24040425e59ba1949b5ea391`

The final external submit action is intentionally not performed here: it requires the submitter to certify rights and make an irrevocable license choice.
