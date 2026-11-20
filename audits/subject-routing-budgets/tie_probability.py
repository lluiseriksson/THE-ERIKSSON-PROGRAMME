"""Exact probability of satisfying all floors at the first feasible pooled optimum."""
import hashlib
import io
import itertools
import json
import math
from fractions import Fraction
from pathlib import Path
from urllib.request import urlopen
import zipfile

pin = "4c8b0787c71f557dc60746bf6b57df8ecad82c01"
url = ("https://raw.githubusercontent.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/"
       +pin+"/audits/subject-routing-budgets/subject-budgets.zip")
with urlopen(url,timeout=60) as response:
    data=response.read()
assert hashlib.sha256(data).hexdigest()=="e69329388fb6807b3ca3853ef370e4e6193ad71788dc4ebf0b3b4ac5af72310e"
with zipfile.ZipFile(io.BytesIO(data)) as archive:
    result=json.loads(archive.read("subject-budgets.json"))


def at_minimum(up,needs):
    k=sum(needs)
    return Fraction(math.prod(math.comb(u,d) for u,d in zip(up,needs)),math.comb(sum(up),k))


for up in itertools.product(range(3),repeat=3):
    rows=[g for g,count in enumerate(up) for _ in range(count)]
    for needs in itertools.product(*(range(u+1) for u in up)):
        choices=list(itertools.combinations(range(len(rows)),sum(needs)))
        safe=sum(all(sum(rows[i]==g for i in chosen)>=d for g,d in enumerate(needs)) for chosen in choices)
        assert Fraction(safe,len(choices))==at_minimum(up,needs)
groups=result["groups"]
names=list(groups)
up=[groups[g]["up"] for g in names]
needs=[groups[g]["lo"] for g in names]
k=sum(needs)
p=at_minimum(up,needs)
a,b=result["universal"][0]
assert k==1840 and a==2495 and sum(up)==2496
rows=[g for g in names for _ in range(groups[g]["up"])]
# At A-1 exactly two positive-gain rows are omitted. Both must belong
# to a subject that can spare only one, since every single omission is safe.
assert all(groups[g]["up"]-groups[g]["lo"]>=1 for g in names if groups[g]["up"])
fail=sum(math.comb(groups[g]["up"],2) for g in names if groups[g]["up"]-groups[g]["lo"]==1)
direct=sum(g==h and groups[g]["up"]-groups[g]["lo"]==1 for g,h in itertools.combinations(rows,2))
assert fail==direct and fail>0
def exact(p):
    return dict(numerator=str(p.numerator),denominator=str(p.denominator),decimal=float(p),
                log10=math.log10(p.numerator)-math.log10(p.denominator))
out=dict(pin=pin,assumption="uniform among pooled-optimal schedules at each exact budget",
         minimum_budget=k,probability_all_safe_at_minimum=exact(p),
         budget_before_guarantee=a-1,failing_omission_pairs=fail,total_pairs=math.comb(sum(up),2),
         probability_any_failure_before_guarantee=exact(Fraction(fail,math.comb(sum(up),2))),
         first_guaranteed=a,probability_any_failure_at_guarantee=0)
dest=Path("/content/archive.zip")
with zipfile.ZipFile(dest,"w",zipfile.ZIP_DEFLATED) as archive:
    archive.writestr("tie-probability.json",json.dumps(out,indent=2)+"\n")
print("archive_sha256",hashlib.sha256(dest.read_bytes()).hexdigest())
