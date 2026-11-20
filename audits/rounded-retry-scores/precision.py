"""Measure the ambiguity left by rounded, consecutive triples of public task counts."""
import hashlib
import io
import json
from collections import defaultdict
from itertools import product
from math import comb
from urllib.request import urlopen

from audit import DIGEST, URL


def label(total, failures, scale):
    return (2 * scale * (total - failures) + total) // (2 * total)


def labels(vector, n, scale):
    return tuple(label(3 * n, sum(vector[i:i + 3]), scale)
                 for i in range(len(vector) - 2))


def analyze(shown, n, scale):
    bins = defaultdict(list)
    for total in range(3 * n + 1):
        bins[label(3 * n, total, scale)].append(total)
    cost = [comb(value, 3) for value in range(n + 1)]
    # Each state fixes the last two counts. Carry the number of paths and
    # the extreme sums of C(f_i,3) among all prefixes ending at this pair.
    layers = []
    states = {(x, y): (1, cost[x] + cost[y], cost[x] + cost[y])
              for x, y in product(range(n + 1), repeat=2)}
    for mark in shown:
        layers.append(set(states))
        following = {}
        for (x, y), (ways, low, high) in states.items():
            for total in bins[mark]:
                z = total - x - y
                if 0 <= z <= n:
                    pair = (y, z)
                    new_low, new_high = low + cost[z], high + cost[z]
                    if pair in following:
                        count, lower, upper = following[pair]
                        following[pair] = (count + ways, min(lower, new_low), max(upper, new_high))
                    else:
                        following[pair] = (ways, new_low, new_high)
        states = following
    if not states:
        raise ValueError('No compatible vectors')
    viable = set(states)
    supports = [set() for _ in range(len(shown) + 2)]
    supports[-2].update(y for y, z in viable)
    supports[-1].update(z for y, z in viable)
    # Retain exactly states that have both a feasible prefix and a feasible suffix.
    choices = []
    for i in reversed(range(len(shown))):
        step = {}
        for x, y in layers[i]:
            possible = [t - x - y for t in bins[shown[i]] if (y, t - x - y) in viable]
            if possible:
                step[x, y] = (min(possible), max(possible))
                supports[i].add(x)
        viable = set(step)
        choices.append(step)
    witnesses = []
    for start, side in [(min(viable), 0), (max(viable), 1)]:
        vector = list(start)
        for step in reversed(choices):
            vector.append(step[tuple(vector[-2:])][side])
        assert labels(vector, n, scale) == tuple(shown)
        witnesses.append(vector)
    paths = sum(s[0] for s in states.values())
    assert (witnesses[0] == witnesses[1]) == (paths == 1)
    return dict(compatible_vectors=paths, identified_tasks=sum(len(v)==1 for v in supports),
                task_supports=[sorted(v) for v in supports], witnesses=witnesses,
                failing_triples_range=[min(s[1] for s in states.values()), max(s[2] for s in states.values())])


def exhaustive_test():
    checked = 0
    for scale in (5, 10, 100):
        by_label = defaultdict(list)
        for v in product(range(4), repeat=5):
            by_label[labels(v, 3, scale)].append(v)
        for shown, vectors in by_label.items():
            result = analyze(shown, 3, scale)
            assert result['compatible_vectors'] == len(vectors)
            assert result['task_supports'] == [sorted(set(col)) for col in zip(*vectors)]
            assert result['witnesses'] == [list(min(vectors)), list(max(vectors))]
            sums = [sum(comb(f, 3) for f in v) for v in vectors]
            assert result['failing_triples_range'] == [min(sums), max(sums)]
            checked += 1
    return checked


def study():
    import pyarrow.parquet as pq
    checked = exhaustive_test()
    with urlopen(URL, timeout=90) as response:
        raw = response.read()
    assert hashlib.sha256(raw).hexdigest() == DIGEST
    rows = sorted(pq.read_table(io.BytesIO(raw), columns=['problem', 'statuses', 'exit_codes']).to_pylist(),
                  key=lambda row: row['problem'])
    assert len(rows) == len({r['problem'] for r in rows}) == 161
    recorded = []
    for row in rows:
        status, codes = row['statuses'], row['exit_codes']
        assert len(status) == len(codes) == 50 and None not in status + codes
        recorded.append(sum(s != 'OK' or c != 0 for s, c in zip(status, codes)))
    result = {}
    observed = sum(comb(x, 3) for x in recorded)
    for scale in (1000, 100):
        shown = labels(recorded, 50, scale)
        case = analyze(shown, 50, scale)
        assert all(f in supp for f, supp in zip(recorded, case['task_supports']))
        lo, hi = case['failing_triples_range']
        assert lo <= observed <= hi
        case['rounded_labels'] = shown
        result[str(scale)] = case
    assert result['1000']['witnesses'][0] == result['1000']['witnesses'][1] == recorded
    return dict(data_url=URL, source_sha256=DIGEST, n=50, tasks=[r['problem'] for r in rows],
                configurations='1000 bins per unit = tenths of a percentage point, 100 = whole percentage points. Nearest, ties upward.',
                direct_check_label_classes=checked, direct_check_vectors_per_scale=1024,
                global_triple_denominator=161 * comb(50, 3), observed_failing_triples=observed,
                at_scale=result)


if __name__ == '__main__':
    print(json.dumps(study(), indent=2))
