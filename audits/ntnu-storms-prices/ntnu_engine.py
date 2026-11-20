"""Reconstruct published NTNU design rows using the authors' unit-area convention."""
from decimal import Decimal as D
from pathlib import Path
from hashlib import sha256
from importlib.metadata import version
from urllib.request import urlopen
import json
import math
import re
import sys
from swmm.toolkit import solver, output, shared_enum

BASE = 'https://raw.githubusercontent.com/ElhadiMohsenAbdalla/SWMMLIDOPT/a824c03d1864b02d153c81679b61e2d9125d090a/Example/'
HASH = {'MultiOpt.json':'2423484a58456c597d7eea2241a650d3447e56461c1cb51e3ee77d72ea8f2321',
        'NTNU_case_withLID.inp':'0d48118a8b9ed836812a67729d14da6464c5151f5f57b58675ebf1f229897fa8'}
PORTFOLIO = (2,169,73,20,6)
ANCHORS = (*PORTFOLIO,1,200)

def need(ok, why):
    if not ok:
        raise ValueError(why)

def source(name):
    path=Path(name)
    if not path.exists():
        with urlopen(BASE+name,timeout=30) as f:
            path.write_bytes(f.read())
    raw=path.read_bytes()
    need(sha256(raw).hexdigest()==HASH[name],name)
    return raw.decode()

def rows_of(text,section):
    body=re.search(r'(?ms)^\['+section+r'\]\s*\n(.*?)(?=^\[|\Z)',text).group(1)
    return [s.split() for s in body.splitlines() if s.strip() and not s.lstrip().startswith(';')]

def evaluate(template,usage,area,fractions,storm):
    need(len(fractions)==len(usage)==13,'13 design fractions expected')
    replacement=[]
    for row,x in zip(usage,fractions):
        count=x*area[row[0]]*10000
        need(count>=0 and row[3:5]==['1','1'],'Unit area/width mismatch')
        # Decimal notation explicitly preserves the nonnegative integer part used by atoi.
        replacement.append(' '.join(row[:2]+[format(count,'f')]+row[3:]))
    return simulate(template,replacement,storm)

def evaluate_counts(template,rows,storm):
    return simulate(template,[' '.join(r) for r in rows],storm)

def simulate(template,replacement,storm):
    model=re.sub(r'(?ms)^\[LID_USAGE\].*?(?=^\[|\Z)','[LID_USAGE]\n'+'\n'.join(replacement)+'\n\n',template)
    model=model.replace('Rain1 VOLUME 0:01 1 TIMESERIES des2','Rain1 VOLUME 0:01 1 TIMESERIES '+storm)
    Path('trial.inp').write_text(model)
    solver.swmm_run('trial.inp','trial.rpt','trial.out')
    h=output.init()
    output.open(h,'trial.out')
    try:
        steps=output.get_times(h,shared_enum.Time.NUM_PERIODS)
        seconds=output.get_times(h,shared_enum.Time.REPORT_STEP)
        vals=output.get_system_series(h,shared_enum.SystemAttribute.OUTFALL_FLOWS,0,steps-1)
        need(steps==41 and seconds==60 and len(vals)==steps and all(math.isfinite(v) for v in vals),'Unexpected report interval or outflow')
        return max(vals)
    finally:
        output.close(h)
