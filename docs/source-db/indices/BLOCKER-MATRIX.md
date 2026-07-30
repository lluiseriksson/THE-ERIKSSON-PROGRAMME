# Blocker Matrix

Non-theorem-feedable entries and first actions. Use before opening PDFs.

| Priority | Citation | Status | Source | First blocker |
|---:|---|---|---|---|
| 1 | `cmp116.lemma3.window.2.14-2.38` | `visual_confirmed` | Balaban CMP116 | Lemma 3's endpoint constants are confirmed from the rendered primary PDF; the exact D/P/Z0/Z0' dictionary and the remaining termwise hierarchy before (2.38) are still open. |
| 2 | `cammarota.cmp85.polymer-mayer-source-target` | `source_pending` | Cammarota CMP85 | Theorem statement, smallness, constants, metric and uniformity. |
| 3 | `cmp109.bond-convention.positive-oriented` | `source_pending` | Balaban CMP109 | Bridge from the general convention to CMP116 fixed-(Z0,Y0) P-bonds. |
| 4 | `cmp116.eq231.p-family-carrier-source-target` | `source_pending` | Balaban CMP116 | Membership iff and source carrier identification with the repository four-direction carrier. |
| 5 | `cmp95.covariance-green.bounds-source-target` | `visual_confirmed` | Balaban CMP95 | Source formulas are located; still need the G/G_k-to-repository covariance/root dictionary and CMP96/CMP99 transport. |
| 6 | `cmp96.one-step-covariance-law-source-target` | `located` | Balaban CMP96 | Label/page map located; exact theorem/equation body, hypotheses, normalization and scale dictionary remain open. |
| 7 | `cmp98.eq14-15-source-target` | `located` | Balaban CMP98 | Label/page map located; exact Q_k formula body, CMP116 alignment, determinant/Jacobian normalization and symbol dictionary remain open. |
| 8 | `cmp99.background-field-propagator-source-target` | `visual_confirmed` | Balaban CMP99 | Background-field propagator and decay/positivity theorems are located; still need the source-to-Lean covariance/Hessian dictionary. |
| 9 | `cmp102.variational-hessian-expansion-source-target` | `visual_confirmed` | Balaban CMP102 | Action expansion and positive second variation are located; still need the Wilson-Hessian coordinate/sign/normalization dictionary. |
| 10 | `cmp122i.large-field-c-bound.1.70` | `visual_confirmed` | Balaban CMP122-I | Exact quantifiers and hypotheses of representation (1.63), including the U-bar analyticity space. |
| 11 | `cmp122ii.rprime-bound.1.98-1.100` | `visual_confirmed` | Balaban CMP122-II | Full Theorem 1 hypotheses and parameter restrictions for the exponentiated expansion. |

For `cmp116.lemma3.window.2.14-2.38`, direct inspection of the rendered primary
PDF confirms on page 20

`C3 = 2 (L+2)^4 O(1)^2 E0 C1 alpha4^-1 alpha6^-1 M^q exp(C2 kappa1)`

and the decay rate in (2.38) as `(1-8 delta) (L/2) kappa`.  Page 21 fixes
`(1-10 delta) (L/2) = 1`, hence
`delta = (1/10) (1-2/L)`.  The earlier OCR reading with
`alpha1^-1 alphaL^-1`, and the OCR parsing of `(L/2)` as a square root, are
rejected.  This visual recovery does not discharge the remaining source-to-Lean
dictionary for the preceding window.
