# Retention at half noise depends on Hamming distances inside the cut

Analytic extension to the small-support note. Use its normalization on the uniform Boolean cube of dimension L. Here ρ=1/2, P=Pρ, h>0, g=Ph, π=hg≥b>0, Eπ=1 and Eπ³≤2. Let U=h/g. For any nonempty vertex set A define

    W(A) = max over x in A of Σ_{y in A} 3^(−27 d(x,y)/16).

Here d counts differing coordinates. With β=(3/4)2^(11/27)<1 and H depending only on b,

    ‖K_AA‖ ≤ min{1, H β^L W(A)^(16/27)}.                      (1)

The norm uses the stationary inner product. In the trace on C={h≥a}, 0<a≤b/4, the same estimate applies to A⊂C after replacing H by H/(1−a²/b). In particular every subexponential-cardinality set has exponentially small killed norm. Formula (1) also controls some exponentially large sets for which replacing W(A) by |A| gives a vacuous estimate. No marginal matching enters this theorem.

## Two ordinary hypercontractive steps

All function norms in this section use uniform probability. With Q=P_{√ρ}, we have ‖Qh‖₂²=E hPh=1. The stationary floor and Jensen give g⁻¹≤Pg/b, since g≥b P(1/g)≥b/(Pg). Use ordinary Boolean hypercontractivity in the form ‖P_t f‖_v≤‖f‖_u when t²≤(u−1)/(v−1), 1<u≤v. Since Pg=P_{ρ^(3/2)}Qh, we obtain ‖g⁻¹‖₉≤1/b. This step uses (ρ^(3/2))²=1/8.

If ‖g⁻¹‖_q≤B then h=π/g satisfies ‖h‖_u≤2^(1/3) B, with 1/u=1/3+1/q. Now Pg=P_{1/4}h. Hypercontractivity and the same floor inequality give ‖g⁻¹‖_{1+16(u−1)}≤2^(1/3)B/b. For q=9 we have u=9/4 and output 21. For q=21 we have u=21/8 and output 27. Thus ‖g⁻¹‖₂₇≤2^(2/3)b⁻³. Hölder for U=π/g² yields ‖U‖_{27/11}≤H=2^(5/3)b⁻⁶, since 1/3+2/27=11/27. This is the finite bootstrap of the published window manuscript specialized to the exponents needed here. It requires only forward hypercontractivity.

## Weighted row bound

The symmetric conjugate S of K has S(x,y)=√U(x)√U(y)(3/4)^L 3^(−d(x,y)). For v(x)=√U(x)>0 on A, the row ratio (S_AA v)(x)/v(x)=(3/4)^L Σ_{y in A} U(y)3^(−d(x,y)). The largest row ratio bounds the spectral radius by positive diagonal similarity and the row-sum norm. Symmetry and positivity of S_AA identify the spectral radius with the stationary killed norm. Counting-measure Hölder gives the row bound (1), because (Σ_y U(y)^(27/11))^(11/27)≤2^(11L/27)H and the conjugate exponent is 27/16. The conditional-stationary one-step retention is bounded by this norm. It follows that retention ≥δ implies W(A)≥(δ/H)^(27/16)β^(−27L/16).

For the trace, take B=Cᶜ, D=S_BC and θ=a²/b. On B one has U=h²/π≤θ and hence S_BB≤θ I. Positivity of the full block matrix gives D*D≤θ S_CC by Cauchy–Schwarz in its quadratic form. The conjugate of the successive-visit chain is T=S_CC+D*(I−S_BB)⁻¹D, by summing excursions. Therefore T≤S_CC/(1−θ). Compress this form inequality to A. Conditioning the stationary law on C multiplies its inner product by a constant, leaving operator norms unchanged.

## Exact checks and scope

* β²⁷=3²⁷/2⁴³<1, since 3¹⁷=129140163<134217728=2²⁷ and 3¹⁰=59049<65536=2¹⁶. The preceding diagonal proof at ρ=1/2 gave β_old³=2·27³/32³>1. Thus (1) answers the open parameter test in the preceding note.
* For L a multiple of 8, suppose |A|=2^(L/8) and distinct points are at distance at least L/8. Then W(A)≤1+(2·3^(−27/16))^(L/8)≤2. The cardinality-only right side before truncation grows, since (β·2^(2/27))²⁷=3²⁷/2⁴¹>1 (use 3⁹=19683>2¹⁴). Such sets exist: greedy packing removes fewer than or equal to Σ_{j≤L/8} binom(L,j)≤3^(L/8)(4/3)^L vertices per selection by the binomial theorem. This is <2^(7L/8), since 4⁸<2⁷·3⁷. Hence at least 2^(L/8) vertices can be selected. This is an example for the set geometry, with no restriction on the admissible potential.
* On a singleton W=1. On the full cube the norm-one cutoff must be retained. The original moment cap and floor persist. The weighted count can still be exponentially large on clustered sets. The full stationary-gap question remains open.

The hypercontractive input and inverse-floor iteration occur in the [published window paper](https://airr.science/papers/ARR-2026-4T35VQ6MZB8F99F4/versions/v2/). For the classical two-point product inequality see [Bonami, 1970](https://doi.org/10.5802/aif.357). The contribution here is the choice of two finite exponents and their combination with the actual distance-weighted return kernel. The literature comparison does not establish priority. Verification consists of a same-context analytic check of the steps and exact inequalities. No formal verification or independent review is claimed.
