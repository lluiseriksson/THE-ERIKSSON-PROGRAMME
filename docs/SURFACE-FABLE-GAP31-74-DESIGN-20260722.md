# Independent design memo: finite-beta gap and relay boundary

**Source:** bounded Fable High request, profile `default`, verified model
`claude-fable-5`, 2026-07-22.  This is recorded as design advice, not as a
proof or a certificate.

The response identifies a genuine logical obstruction: sign rows certifying
`W^J<0` cannot imply `(H_tail)`, because a positive smooth rescaling of all
`J_m` leaves the ratio and Wronskian sign unchanged while changing the
derivative majorants in `(H_tail)`.  Therefore any route that derives
`(H_tail)` from sign rows alone is invalid.

The valid replacement route is narrower.  On a compact domain, an exhaustive
strict `W^J<0` cover plus the exact scaling identity
`W=e^{8 beta}W^J` and the independently proved `F_B>0` theorem implies
`E'<0` pointwise.  The missing object is thus an admissible adjacent cover,
not a new implication lemma.  The noncompact complement still needs the
existing tail argument or a separate uniform remainder certificate.

The response suggested a three-cell pilot at `[31,497/16]`, `[52,833/16]`,
and `[1183/16,74]`, under the frozen CWIN=3/2, order-30/t-order-37,
180-bit contract.  That pilot is preregistered and its six production/replay
runs are archived.  All three cells pass their local sign-row judges, but
they remain candidate-only: they do not prove `(H_tail)`, close the full
`[31,74]` union, or promote G2/G6.
