"""Certificate for a prospective two-start design on the 127-unit frame."""
import json
from fractions import Fraction

N, n, offset, marked = 127, 32, 48, 62
frame = set(range(N))
def sample(s):
    return {(s + j*N)//n for j in range(n)}
unseen = [frame - (sample(s) | sample((s+offset) % N)) for s in range(N)]
assert {len(c) for c in unseen} == {63}
pair_max = max(len(a & b) for i,a in enumerate(unseen) for b in unseen[:i])
assert pair_max == 61
witness = sorted(unseen[0])[:marked]
assert sum(set(witness) <= c for c in unseen) == 1
print(json.dumps(dict(frame=N, sample=n, offset=offset, positive_count=marked,
    phase_pairs=N*(N-1)//2, max_common_unseen=pair_max, hidden_at_each_start=63,
    simultaneous_miss=str(Fraction(1,N)), extremal_placement=witness,
    class_of_optimality="uniform global phase and any fixed second offset",
    independent_starts=str(Fraction(34,127)**2)),indent=2))