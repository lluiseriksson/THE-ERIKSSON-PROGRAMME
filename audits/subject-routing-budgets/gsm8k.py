from collections import Counter
import csv,hashlib,io,json,zipfile
from itertools import product, combinations
from pathlib import Path
from urllib.request import urlopen
root='https://raw.githubusercontent.com/lm-sys/RouteLLM/0b64fdafe049e596a3f5657c219329f24af24198/routellm/evals/gsm8k/'
def fetch(name,digest):
    with urlopen(root+name,timeout=60) as response:data=response.read()
    assert hashlib.sha256(data).hexdigest()==digest
    return data.decode('utf-8-sig')
csv_text=fetch('gsm8k_responses.csv','1f38ed03db354a020f71e92022383dc3cf37bbf2694dea4daaeea7b6c43fe57b')
filters=fetch('contaminated_prompts.jsonl','1f5a7be02148ee0f7f306d233ba76a6573c826cee9499a34f8ef938a1a84c234')
excluded={json.loads(line)['eval_prompt'] for line in filters.splitlines() if line.strip()}
strong='gpt-4-1106-preview'; weak='mistralai/Mixtral-8x7B-Instruct-v0.1'
def bounds(weak_correct,up,down,n,k):
    cap=weak_correct+min(k,up)
    return cap-max(0,k-(n-down)),cap
for v in product((-1,0,1),repeat=5):
    for k in range(6):
        exact,cap=bounds(0,v.count(1),v.count(-1),5,k)
        assert exact==max(sum(z) for z in combinations(v,k))
        assert cap==max(sum(z) for j in range(k+1) for z in combinations(v,j))
rows=list(csv.DictReader(io.StringIO(csv_text)))
bank=[r for r in rows if r['prompt'] not in excluded]
def correct(s):
    return {'true':1,'false':0,'1':1,'0':0}[s.strip().lower()]
pairs=Counter((correct(r[weak]),correct(r[strong])) for r in bank)
weak_correct=pairs[1,0]+pairs[1,1]
strong_correct=pairs[0,1]+pairs[1,1]
gains=sorted([b-a for (a,b),count in pairs.items() for _ in range(count)],reverse=True)
n=len(gains);running=best=weak_correct;curve=[]
for k in range(n+1):
    if k:running+=gains[k-1]
    best=max(best,running)
    assert (running,best)==bounds(weak_correct,pairs[0,1],pairs[1,0],n,k)
    curve.append([k,running,best])
assert curve[-1][1]==strong_correct
out=dict(original_questions=len(rows),n=n,excluded_by_official_filter=len(rows)-n,unique_prompt_count=len({r['prompt'] for r in bank}),beneficial=pairs[0,1],harmful=pairs[1,0],both_correct=pairs[1,1],both_wrong=pairs[0,0],weak_correct=weak_correct,strong_correct=strong_correct,ceil_at_full=best,first_strict_discrepancy=next((k for k,x,y in curve if x<y),None),exact_and_at_most=curve,small_vectors=243,checked_integer_budgets=n+1,repository_pin='0b64fdafe049e596a3f5657c219329f24af24198')
with zipfile.ZipFile('/content/archive.zip','w',zipfile.ZIP_DEFLATED) as z:z.writestr('fixed-budget.json',json.dumps(out,indent=2)+'\n')
print('archive_sha256',hashlib.sha256(Path('/content/archive.zip').read_bytes()).hexdigest())
