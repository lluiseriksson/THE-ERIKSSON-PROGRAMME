"""Minimax consistency audit for the 24 official published A12 corridor prices."""
from fractions import Fraction as F
import json
from pathlib import Path
v=json.loads(Path('threshold.json').read_bytes())['rows']
totals=['5.47 7.53 11.12','22.82 31.63 46.98','24.62 34.27 50.99','24.76 34.45 51.23','25.00 34.78 51.71','26.14 36.53 53.99','27.58 38.09 56.23','28.78 39.91 58.74']
prices=[F(x) for line in totals for x in line.split()]
if len(prices)!=len(v) or [(r['co2'],r['axles']) for r in v]!=[(c,a) for c in [5,4,3,2,1,1,1,1] for a in [2,3,4]]:raise ValueError('Table order')
rates=[F(r['base'])+F(r['surcharge']) for r in v]
err,i,j=max(((pi*rj-pj*ri)/(ri+rj),i,j) for i,(pi,ri) in enumerate(zip(prices,rates)) for j,(pj,rj) in enumerate(zip(prices,rates)))
lim=max((p-err)/r for p,r in zip(prices,rates))
if lim!=min((p+err)/r for p,r in zip(prices,rates)) or max(abs(lim*r-p) for r,p in zip(rates,prices))!=err:raise ValueError('Minimax witness')
fixed=[abs(F(75)*r-p) for r,p in zip(rates,prices)]
print(json.dumps({'source':'https://www.go-maut.at/media/zglel2dk/go-maut-tarife-2026_streckenmaut_en.pdf','eur_ex_vat':list(map(str,prices)),'rows':len(v),'minimax_eur':str(err),'best_km':str(lim),'incompatible_at_cent_rounding':err>F(1,200),'witnesses':[dict(v[index],published=str(prices[index]),rate=str(rates[index])) for index in (i,j)],'max_abs_at_75':str(max(fixed)),'within_half_cent_at_75':sum(z<=F(1,200) for z in fixed)},indent=2))
