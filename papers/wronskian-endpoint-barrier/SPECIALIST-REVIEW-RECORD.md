# Specialist review record

## Frozen mathematical object

- Paper-hardening commit: `4dc42092c03d454d366403fa9a4d1c77b3b4a099`
- Tree: `b120f46e21549e0942923db0fdc729a7d6355959`
- PDF SHA-256:
  `c51cd46c1dc577e4d3bb6f2e36df748e715d2e6dc614c7290d8e9837d92986be`

The reassessment below did not request a mathematical or editorial change to
that object. The paper body and PDF therefore remain unchanged.

## First assessment

- Score: **5.12 / 10** on the catalogue-comparison scale.
- Provisional place: seventh among programme papers, eighth when the Kerr
  stability paper is included as an external calibration.
- Main reservations: compressed uniform Laplace remainder/tail argument and
  compressed proof that the perturbation preserves every required inequality
  globally in `beta`.

Captured source:

- Bytes: 8,283
- SHA-256:
  `a5b23734168694bac46fa97a3886f958dad4b9b2866b1f8b0642c9b1ed6c57ef`
- Line endings: 143 LF, 143 CR

## Response to the first assessment

Commit `4dc42092` added:

- uniform differentiated fixed-order Bessel bounds;
- an explicit central Laplace window and two exterior deficit estimates;
- polynomial-moment product bounds for both absolute envelopes;
- a continuous positive preservation radius `rho(beta)`;
- a globally normalized flat bump with strictly concave exponent;
- separate small, compact, central, and large-`beta` arguments;
- an active diagnostic check of the explicit radius under normal Python and
  `python -O`.

## Reassessment

- Revised score: **5.20 / 10**.
- Reasonable interval: **5.12--5.28**.
- Place: **sixth among programme papers**.
- Place including Kerr as an external calibration: **seventh**.
- The reviewer explicitly found that the revised version converts the two
  vulnerable parts into quantified arguments verifiable line by line.

The reassessment confirms three autonomous contributions:

1. global positivity of `F_B`;
2. the exact endpoint cancellation exponent `8 - 4 sqrt(2)`;
3. global structural non-identifiability with a quantitative preservation
   radius.

It retains the decisive limitation: the paper neither proves nor disproves
global Bessel Wronskian negativity. It remains below the certificate-based
global-ratio paper for that reason. Lack of Lean or an interval certificate is
also retained as a comparative confidence limitation, not as a contradiction
in the ordinary proofs.

Captured reassessment source:

- Bytes: 8,151
- SHA-256:
  `f524bb6320aca4f7afa652d009ac8c4f631db984d722bed216efc4dd898a0848`
- Line endings: 160 LF, 160 CR

## Updated local ranking recorded by the review

The paper is sixth within the programme catalogue, behind the global-ratio
paper (5.25) and ahead of the continuous-order Bessel comparison paper
(5.18). With Kerr included as an external reference it is seventh overall.

This is a record of a supplied specialist judgement, not a self-issued proof
certificate. The catalogue score is distinct from the task-lane score of
6/10 recorded in `docs/WRONSKIAN-REDUCTION-51-RESULT.md`.
