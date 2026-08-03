# Blocker Matrix

Non-theorem-feedable entries and first actions. Use before opening PDFs.

| Priority | Citation | Status | Source | First blocker |
|---:|---|---|---|---|
| 1 | `cmp116.lemma1.window.1.11-1.29` | `visual_confirmed` | Balaban CMP116 | Pages 5-8 and Eqs. (1.11)-(1.29) are visually recovered; generic L1 and L2 are compiler-verified, while their physical specialization and the L7-L8 summation remain open. |
| 2 | `cmp116.lemma1.window.1.30-1.36` | `visual_confirmed` | Balaban CMP116 | Page 9 fixes the L9 scale inequality and the exact `1/4` and `1/16` scalar windows; the scale dictionary and formal Eq. (1.29)-to-(1.36) summation remain open. |
| 3 | `cmp116.lemma3.window.2.14-2.38` | `visual_confirmed` | Balaban CMP116 | Lemma 3's endpoint constants are confirmed from the rendered primary PDF; the exact D/P/Z0/Z0' dictionary and the remaining termwise hierarchy before (2.38) are still open. |
| 4 | `cammarota.cmp85.polymer-mayer-source-target` | `source_pending` | Cammarota CMP85 | Theorem statement, smallness, constants, metric and uniformity. |
| 5 | `cmp109.bond-convention.positive-oriented` | `source_pending` | Balaban CMP109 | Bridge from the general convention to CMP116 fixed-(Z0,Y0) P-bonds. |
| 6 | `cmp116.eq231.p-family-carrier-source-target` | `source_pending` | Balaban CMP116 | Membership iff and source carrier identification with the repository four-direction carrier. |
| 7 | `cmp95.covariance-green.bounds-source-target` | `visual_confirmed` | Balaban CMP95 | Source formulas are located; still need the G/G_k-to-repository covariance/root dictionary and CMP96/CMP99 transport. |
| 8 | `cmp96.one-step-covariance-law-source-target` | `located` | Balaban CMP96 | Label/page map located; exact theorem/equation body, hypotheses, normalization and scale dictionary remain open. |
| 9 | `cmp98.eq14-15-source-target` | `located` | Balaban CMP98 | Label/page map located; exact Q_k formula body, CMP116 alignment, determinant/Jacobian normalization and symbol dictionary remain open. |
| 10 | `cmp99.background-field-propagator-source-target` | `visual_confirmed` | Balaban CMP99 | Background-field propagator and decay/positivity theorems are located; still need the source-to-Lean covariance/Hessian dictionary. |
| 11 | `cmp102.variational-hessian-expansion-source-target` | `visual_confirmed` | Balaban CMP102 | Action expansion, rectangular H, literal Eq. (80), and positive second variation are located; Eq. (80) matches the Lean four-term core exactly, while the Wilson-Hessian coordinate/sign/normalization dictionary remains open. |
| 12 | `cmp122i.large-field-c-bound.1.70` | `visual_confirmed` | Balaban CMP122-I | Exact quantifiers and hypotheses of representation (1.63), including the U-bar analyticity space. |
| 13 | `cmp122ii.rprime-bound.1.98-1.100` | `visual_confirmed` | Balaban CMP122-II | Full Theorem 1 hypotheses and parameter restrictions for the exponentiated expansion. |

For `cmp116.lemma3.window.2.14-2.38`, direct inspection of the rendered primary
PDF confirms on page 20

`C3 = 2 (L+2)^4 O(1)^2 E0 C1 alpha4^-1 alpha6^-1 M^q exp(C2 kappa1)`

and the decay rate in (2.38) as `(1-8 delta) (L/2) kappa`.  Page 21 fixes
`(1-10 delta) (L/2) = 1`, hence
`delta = (1/10) (1-2/L)`.  The earlier OCR reading with
`alpha1^-1 alphaL^-1`, and the OCR parsing of `(L/2)` as a square root, are
rejected.  This visual recovery does not discharge the remaining source-to-Lean
dictionary for the preceding window.

For `cmp116.lemma1.window.1.11-1.29`, direct inspection of rendered pages 5-8
confirms that the split is `m > 2^4`, not `m > 24`, and recovers the fixed-point
constants in (1.13)-(1.16), the coupled-field estimates (1.19)-(1.22), the
Cauchy/localization estimate (1.24), and the final decay (1.29).  This removes
the OCR ambiguity but does not yet discharge the corresponding Lean Lemma-1
certificate.

For `cmp116.lemma1.window.1.30-1.36`, direct inspection of rendered page 9
fixes Eq. (1.31) as
`d_j(X) >= (L^j eta)^(-1) d_k(X0)`.  The source then assumes
`(1/4)*(kappa1-1) >= (1-delta)*kappa`, `0 < delta < 1`, and finally
`(1/16)*kappa1 >= (1-2*delta)*kappa`.  Earlier provisional coefficients
`1/2` and `7/8` are rejected.  The extraction is exact source evidence, not
a Lean discharge of the scale dictionary or of Eq. (1.36).
