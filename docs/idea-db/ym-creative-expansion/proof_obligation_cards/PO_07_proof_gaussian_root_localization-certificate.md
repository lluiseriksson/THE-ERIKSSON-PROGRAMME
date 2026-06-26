# PO 07 — `proof.gaussian.root.localization-certificate`

**Blocker:** gaussian pushforward/root localization/Hessian

**Source keys:** cmp116.gaussian-pushforward.2.5-2.6, cmp116.localized-activity.2.7-2.10, cmp95.covariance-green.bounds-source-target

**Lean payoff:** PhysicalLocalizedCovarianceRootCertificate, gaussian_pushforward

**v3 action:** Use finite SPD/root toys only as scaffolding; source dictionary remains separate.

## Acceptance rule

A commit passes this card only if it removes or narrows this exact blocker, or records the exact missing source theorem with enough quantifiers and constants for the next agent to attack directly. New downstream wrappers without source-field removal fail this card.
