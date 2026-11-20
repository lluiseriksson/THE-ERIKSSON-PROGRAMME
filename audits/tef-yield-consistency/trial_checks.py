from fractions import Fraction as F
import json
from pathlib import Path


def check(test, message):
    if not test:
        raise ValueError(message)


def calculate():
    record = json.loads(Path(__file__).with_name('yields.json').read_bytes())
    rows = {k: tuple(map(F, v)) for k, v in record['mg_per_plant'].items()}
    check(len(rows) == 20 and all(len(v) == 2 for v in rows.values()), 'table shape')
    a, b = 'TDT-4-15', 'RIL-44'
    dry_gain = rows[b][1] - rows[a][1]
    wet_loss = rows[a][0] - rows[b][0]
    t = wet_loss / (wet_loss + dry_gain)
    def score(k, p):
        return (1-p)*rows[k][0] + p*rows[k][1]
    for p, leader in [(0, a), (t, a), (1, b)]:
        check(all(score(leader, p) >= score(k, p) for k in rows), 'envelope')
    check(score(a,t) == score(b,t) and t == F(1900,2873), 'crossing')
    nearest = min(score(a,t)-score(k,t) for k in rows if k not in (a,b))
    means = [m for v in rows.values() for m in v]
    n = len(means)*2
    h = F(1,200)
    maximum = max(means)+h
    range_cap = n*maximum**2
    cap = 4*sum((m+h)**2 for m in means) - (2*sum(m-h for m in means))**2/n
    check(0 < cap < range_cap < 6442255-F(1,2), 'response-scale contradiction')
    # Exact extremal assignment for unrounded cell centers, one zero per pair.
    extremal = [y for m in means for y in (0,2*m)]
    centered = sum((y-sum(extremal)/n)**2 for y in extremal)
    check(centered == 4*sum(m*m for m in means)-(2*sum(means))**2/n, 'sharp fixed-means bound')
    wet_lsd,dry_lsd = F('102.47'),F('1.71')
    pair_lower_switch = (wet_loss+wet_lsd)/(wet_loss+wet_lsd+dry_gain-dry_lsd)
    field = json.loads(Path(__file__).with_name('field-yields.json').read_bytes())['g_per_plant']
    field = {k: tuple(map(F,v)) for k,v in field.items()}
    check(set(field) == set(rows), 'matched field panel')
    def field_score(k,p):
        return (1-p)*field[k][0] + p*field[k][1]
    cuts = [F(0), F(47,107), F(11,17), F(1)]
    leaders = ['TDT-4-15','Dtt-2','Boni']
    for left, right, g in zip(cuts,cuts[1:],leaders):
        for p in (left,right):
            check(all(field_score(g,p)>=field_score(k,p) for k in field), 'field segment')
        mid=(left+right)/2
        check(all(field_score(g,mid)>field_score(k,mid) for k in field if k!=g), 'unique interior')
    return dict(field_crossings=list(map(str,cuts[1:-1])),field_leaders=leaders,crossover=str(t), third_place_gap=str(nearest), maximum_TSS_from_range=str(range_cap),
                maximum_TSS_from_rounded_cells_upper=str(cap), fixed_mean_extremal_TSS=str(centered),
                S1_moisture_GY='6442255', S1_moisture_df=1, S5_conditional_lower_switch=str(pair_lower_switch),
                units='squared mg per plant for sums of squares; mg per plant for mean differences')


if __name__ == '__main__':
    print(json.dumps(calculate(),indent=2,sort_keys=True))

