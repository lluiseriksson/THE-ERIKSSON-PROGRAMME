# Joint limits of the bid increment and the tie priority

Companion calculation to Theorem 2 of source commit 1a5136086c0e4c6e4b9d25e59de19d9cbd0e3ca0. This material postdates the assessed PDF. All statements refer to unrestricted pure bids in the same two-agent game, with v2 on the grid.

Let D = T − v2 > 0 and let θh be the fractional part of T/h (a number in [0,1)). For an imperfect priority λh write s(h) = 1 − λh > 0. The largest possible efficient clearing price is P = T − h θh. Substitution in Theorem 2 gives the exact condition

    s(h) ≥ a h / [ D + (1 − θh)h ].

If s(h)/h tends to κ > a/D, there are efficient equilibria on every sufficiently fine grid. For finite κ their set of limit prices is the full interval [v2 + a/κ, T], by rounding the two endpoints of the admissible price interval inward. For κ = infinity the lower endpoint is v2. If s(h)/h tends to κ < a/D, eventually none exist. A first-order limit at equality does not determine existence, even along regularly spaced refinements of one market.

For the manuscript's example, take h = 4/n, T = 40/7, a = 1/4, D = 12/7, and s(h) = a h / (D + h/2). This fixes a single, smooth priority schedule; its ratio to h tends to the critical value 7/48. Cancelling the identical positive numerator in the exact test shows that efficient equilibria exist precisely when θh ≤ 1/2. Since T/h = 10n/7, the residues of 10n modulo 7 for n modulo 7 equal to 0 through 6 are respectively 0, 3, 6, 2, 5, 1, 4. Thus n modulo 7 in {0,1,3,5} admits efficiency, and {2,4,6} excludes it. The reverse-order, zero-price equilibrium remains available in every case. Along the efficient subsequences, prices converge to T. Nothing here predicts equilibrium selection.

This calculation identifies a specific rounding effect beyond the fixed-priority limit in the paper. The general failure of ordinary tie rules to reproduce grid limits was already reported in other auction models. See [Bidding in Common-Value Auctions With an Unknown Number of Competitors](https://doi.org/10.3982/ECTA17793).
