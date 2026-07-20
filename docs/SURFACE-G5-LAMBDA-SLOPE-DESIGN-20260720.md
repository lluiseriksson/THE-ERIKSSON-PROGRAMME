# G5 right-edge lambda-slope design (2026-07-20)

Status: **DESIGN ONLY**. This note does not alter G5, G2, or G6 and cannot
be cited as a terminal certificate.

The ratio seam `[2.320,2.325]` is too wide for direct interval evaluation:
the quadrature enclosure remains broad even after the high-grid diagnostic.
The chart code has a useful exact structural fact: `lambda` occurs only in
the rate `r*lambda*theta*phi/2`; the chart integrands themselves are
independent of `lambda`. If `F` is one of the five family integrals, integration
by parts in the outermost smearing variable gives

\[
        \lambda F'(\lambda)=F_{\rm flat}(\lambda)-F(\lambda).
\]

Here `F_flat` pins the outermost variable at its endpoint and retains the
polynomial weights: `r=±1` for `U0`, `theta=1` for `U1`, `phi=1` for `U2`,
`r=1` for `B0`, and `theta=1` for `B1`. The implementation is in
`scripts/surface_right_edge_lambda_slope_design.py`.

The module also differentiates the cancellation-free numerator

\[
 P_0=A_0B_0+\frac{\lambda^2}{4}(A_1B_0-A_0B_1),
\]

using the existing elementary series plus two explicitly derived derivative
series (`syy`, `jyy`). A future production lane may use the centered
mean-value enclosure

\[
 P_0([\lambda_0,\lambda_0+h])
 \subseteq P_0(\lambda_0)+h\,P_0'([\lambda_0,\lambda_0+h]),
\]

with adaptive lambda subdivision. The soundness obligations are: an
independent derivation of the five endpoint identities, a production/replay
transcript, an absolute-difference audit against any predecessor, and a
fresh coverage manifest. Until those exist this is a fabrication aid only.

The first smoke import and low-grid assembly pass; the resulting margins are
not sign certificates because the coarse chart quadrature still straddles
zero.
