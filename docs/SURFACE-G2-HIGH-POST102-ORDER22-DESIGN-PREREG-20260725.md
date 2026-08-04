# Post-102 high-beta order-22 design probe

**Status:** preregistered diagnostic; no transcript, G2, H_tail, or G6 load.

The candidate union reaches `beta=1635/16` and the remaining high interval is
`[1635/16,1000/9]`. Before any output is read, this probe fixes a smaller
Taylor configuration (`CWIN=3/2`, beta order 22, `t` order 25, 180-bit Arb,
minimum `dt=1/100000`) on a single rational beta box. It is an algorithmic
conditioning test only; a successful result would require a new production /
replay contract and independent validator before it could enter any union.

The probe must report either a strict row cover or an explicit failure/timeout.
No adaptive width, precision, stopping rule, or post-hoc partition is allowed.
