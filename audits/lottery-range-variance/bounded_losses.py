"""Exact finite bounds for positive paired contrasts with capped adverse losses."""
from collections import Counter, defaultdict
from functools import lru_cache
from itertools import combinations_with_replacement, product
from math import comb, factorial, prod
from pathlib import Path
import hashlib
import json
from zipfile import ZipFile, ZIP_DEFLATED
import networkx as nx
from scipy.optimize import linear_sum_assignment
import numpy as np


def strata(span):
    groups = defaultdict(Counter)
    for i, j in combinations_with_replacement(range(span+1), 2):
        row = (0, i, j, span)
        count = 24 // prod(factorial(k) for k in Counter(row).values())
        groups[i+j][i*i+j*j] += count
    return list(groups.values())


@lru_cache(None)
def maximum(items, cap):
    if len(items) == 1:
        return 0
    network = nx.DiGraph()
    total = sum(count for _, count in items)
    for q, count in items:
        network.add_node(('a', q), demand=-count)
        network.add_node(('b', q), demand=count)
    for q, _ in items:
        for r, _ in items:
            if q-r <= cap:
                network.add_edge(('a', q), ('b', r), capacity=total, weight=-int(q < r))
    cost, flow = nx.network_simplex(network)
    residual = nx.DiGraph()
    for u, v, edge in network.edges(data=True):
        f = flow[u][v]
        assert 0 <= f <= edge['capacity']
        if f < edge['capacity']:
            residual.add_edge(u, v, weight=edge['weight'])
        if f:
            residual.add_edge(v, u, weight=-edge['weight'])
    for q, count in items:
        assert sum(flow[('a',q)].values()) == count
        assert sum(row.get(('b',q),0) for row in flow.values()) == count
    assert not nx.negative_edge_cycle(residual, weight='weight')
    return -cost


def literal(n, caps):
    groups = defaultdict(list)
    for row in product(range(n), repeat=4):
        groups[min(row),max(row),sum(row)].append(sum(x*x for x in row))
    result = Counter()
    for qs in groups.values():
        v = np.asarray(qs)
        diff = v[None,:] - v[:,None]
        for cap in caps:
            penalty = np.where(diff < -cap,len(v)+1,np.where(diff>0,-1,0))
            i,j = linear_sum_assignment(penalty)
            assert np.all(diff[i,j]>=-cap)
            result[cap] += int(np.sum(diff[i,j]>0))
    return result


def main():
    levels = [strata(d) for d in range(24)]
    table = {}
    for n in [2,3,4,5,6,7,8,12,16,24]:
        caps = sorted({0,1,2,4,6,n,2*n,4*n,n*n})
        wins = {d:sum((n-span)*maximum(tuple(sorted(g.items())),d)
                      for span in range(n) for g in levels[span]) for d in caps}
        assert wins[2] == 12*comb(n,3)-6*(n-2)
        assert wins[0] == wins[1] == 0
        assert wins[n*n] == n**4-(8*n**3-32*n**2+67*n-54)
        assert list(wins.values()) == sorted(wins.values())
        if n <= 7:
            assert literal(n,caps) == wins
        table[n] = wins
    assert table[16][2] == 6636
    archive = Path('/content/archive.zip')
    with ZipFile(archive,'w',ZIP_DEFLATED) as z:
        z.writestr('bounded.json',json.dumps(table,indent=2))
    print('archive_sha256', hashlib.sha256(archive.read_bytes()).hexdigest())


if __name__ == '__main__':
    main()
