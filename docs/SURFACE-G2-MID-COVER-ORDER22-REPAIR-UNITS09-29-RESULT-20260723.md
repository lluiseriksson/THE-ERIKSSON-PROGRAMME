# Order-22 repair result — mid-cover units 09 and 29

The preregistered repair contract in
`SURFACE-G2-CWIN3P2-MID-COVER-ORDER22-REPAIR-UNITS09-29-PREREG-20260723.md`
was executed under the current tree with separate production and replay
processes.

| unit | beta interval | t rows | production SHA-256 |
|---|---|---:|---|
| 09 | `[101/2,203/4]` | 147 | `bc08bcc6490a83c0c21a83f1dc6c2b53dee845e2a26c72633320e02e97a59994` |
| 29 | `[111/2,223/4]` | 164 | `52ba38137ec7fe5c5d9220be3772226d0c193a7eca5c949fd6cf54460dcafa` |

For both units the production and replay bytes are identical.  The
independent structural check verified the order-22 contract, exact rational
beta domains, adjacent `t` rows from `3/5` to the moving endpoint, and a
strictly negative outward-rounded upper bound in every row.  The worst upper
bound was approximately `-5.57e-57` (unit 09) and `-3.62e-62` (unit 29).

This is quarantined finite-beta sign evidence.  It does not close the rest of
the 83-unit cover, does not prove the sign-to-`(H_tail)` relay, and carries no
K2/G2/G6 promotion.  A promotion-grade manifest must still bind the complete
cover, current hashes, independent replay, and the separate analytic relay.
