"""Compute and verify exact two-model routing budgets from pinned paired labels."""
import ast
import csv
import hashlib
import io
import itertools
import json
import sys
import zipfile
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from urllib.request import urlopen

PIN = "0b64fdafe049e596a3f5657c219329f24af24198"
PROJECT = "lm-sys/RouteLLM"
BASE = "routellm/evals/mmlu/"
WEAK = "mistralai/Mixtral-8x7B-Instruct-v0.1"
STRONG = "gpt-4-1106-preview"


def get(url):
    with urlopen(url, timeout=60) as response:
        return response.read()


def subject(rows):
    w = sum(a for a, b in rows)
    gains = sorted((b-a for a, b in rows), reverse=True)
    n, u, h = len(rows), gains.count(1), gains.count(-1)
    t = max(w, w+u-h)
    lo, hi = t-w, min(n, n-h+w+u-t)
    allowed = [k for k, total in enumerate(itertools.accumulate(gains, initial=w)) if total >= t]
    assert allowed == list(range(lo, hi+1))
    return dict(n=n, weak=w, strong=w+u-h, up=u, down=h, floor=t, lo=lo, hi=hi)


def worst(g, k, n, up, down):
    return g["weak"] + max(0, min(k, up)-(up-g["up"])) - min(g["down"], max(0,k-(n-down)))


def small_check():
    labels = [(0,0),(0,1),(1,0),(1,1)]
    for seq in itertools.product(labels, repeat=4):
        groups = [subject(seq[:2]), subject(seq[2:])]
        gains = [b-a for a,b in seq]
        for k in range(5):
            scores = []
            for ix in itertools.combinations(range(4),k):
                score = [seq[i][int(i in ix)] for i in range(4)]
                scores.append((sum(score[:2]),sum(score[2:])))
            best = max(map(sum,scores))
            top = [v for v in scores if sum(v)==best]
            for j,g in enumerate(groups):
                assert min(v[j] for v in top)==worst(g,k,4,gains.count(1),gains.count(-1))
            feasible = sum(g["lo"] for g in groups)<=k<=sum(g["hi"] for g in groups)
            assert feasible==any(all(x>=g["floor"] for x,g in zip(v,groups)) for v in top)


def load_panel():
    tree = json.loads(get(f"https://api.github.com/repos/{PROJECT}/git/trees/{PIN}?recursive=1"))
    assert not tree["truncated"]
    blobs = {v["path"]:v["sha"] for v in tree["tree"]}
    manifest = {}

    def source(name):
        path = BASE+name
        data = get(f"https://raw.githubusercontent.com/{PROJECT}/{PIN}/{path}")
        digest = hashlib.sha1(b"blob "+str(len(data)).encode()+b"\0"+data).hexdigest()
        assert digest == blobs[path]
        manifest[path] = hashlib.sha256(data).hexdigest()
        return data.decode("utf-8-sig")

    domains = ast.literal_eval(ast.parse(source("domains.py")).body[0].value)
    assert len(domains)==len(set(domains))==57
    excluded = {json.loads(line)["eval_prompt"] for line in source("contaminated_prompts.jsonl").splitlines() if line}
    def load_domain(name):
        return list(csv.DictReader(io.StringIO(source(f"responses/mmlu_{name}.csv"))))

    rows_by_prompt = {}
    retained = []
    original = 0
    bit = {"true":1, "false":0, "1":1, "0":0}
    with ThreadPoolExecutor(max_workers=4) as pool:
        for name,rows in zip(domains,pool.map(load_domain,domains)):
            original += len(rows)
            for row in rows:
                prompt = row["prompt"]
                if prompt in excluded:
                    continue
                a,b = (bit[row[col].strip().lower()] for col in (WEAK,STRONG))
                rows_by_prompt.setdefault(prompt, []).append(len(retained))
                retained.append((name,a,b))
    return domains, original, retained, rows_by_prompt, manifest


def analyze(domains, items):
    pairs = {name:[] for name in domains}
    for name,a,b in items:
        pairs[name].append((a,b))
    groups = {name:subject(values) for name,values in pairs.items()}
    n = len(items)
    up,down,weak,lo,hi = (sum(g[key] for g in groups.values()) for key in ("up","down","weak","lo","hi"))
    universal = []
    witness = None
    for k in range(n+1):
        deficit,name = max((g["floor"]-worst(g,k,n,up,down),name) for name,g in groups.items())
        if deficit<=0:
            universal.append(k)
        if lo<=k<=hi and (witness is None or deficit>witness[0]):
            witness = deficit,name,k
    intervals = [[v[0],v[-1]] for _,it in itertools.groupby(enumerate(universal),lambda v:v[1]-v[0])
                 for v in [[value for _,value in it]]]
    ids = list(range(n))
    def gain(i):
        _,a,b = items[i]
        return b-a
    per_group = {name:[] for name in domains}
    for i in sorted(ids,key=gain,reverse=True):
        per_group[items[i][0]].append(i)
    def safe(k):
        required,extra = [],[]
        for name,ordered in per_group.items():
            g = groups[name]
            required.extend(ordered[:g["lo"]])
            extra.extend(ordered[g["lo"]:g["hi"]])
        return required + sorted(extra,key=gain,reverse=True)[:k-len(required)]
    def measure(chosen,k):
        selected = set(chosen)
        assert len(selected)==len(chosen)==k
        scores = dict.fromkeys(domains,0)
        for i,(name,a,b) in enumerate(items):
            scores[name] += b if i in selected else a
        assert sum(scores.values())==weak+min(k,up)-max(0,k-(n-down))
        return scores
    deficit,name,k = witness
    assert deficit>0
    schedules = {}
    for label,budget in [("safe_low",lo),("safe_high",hi),("safe_tie",k),("unsafe_tie",k)]:
        if label=="unsafe_tie":
            chosen = sorted(ids,key=lambda i:(-gain(i), gain(i)*int(items[i][0]==name),i))[:budget]
        else:
            chosen = safe(budget)
        scores = measure(chosen,budget)
        if label=="unsafe_tie":
            assert groups[name]["floor"]-scores[name]==deficit
        else:
            assert all(scores[g]>=s["floor"] for g,s in groups.items())
        schedules[label]=dict(budget=budget,correct=sum(scores.values()),subject_scores=scores,
                              selected_filtered_row_indices=sorted(chosen))
    assert all(lo<=k<=hi for k in universal)
    return dict(pin=PIN,weak_model=WEAK,strong_model=STRONG,n=n,
                up=up,down=down,weak_correct=weak,
                strong_correct=weak+up-down,existential=[lo,hi],universal=intervals,
                feasible_budgets_with_unsafe_optima=hi-lo+1-len(universal),
                largest_shortfall=dict(subject=name,budget=k,missed=deficit,floor=groups[name]["floor"]),
                exhaustive_four_item_cases=256,groups=groups,schedules=schedules)


def run():
    small_check()
    domains,original,items,prompts,manifest = load_panel()
    result = analyze(domains,items)
    result.update(raw=original, excluded=original-len(items), unique_retained_prompts=len(prompts),
                  source_sha256=manifest)
    return result


if __name__=="__main__":
    result = run()
    archive = Path(sys.argv[1] if len(sys.argv)==2 and sys.argv[1].endswith(".zip") else "/content/archive.zip")
    with zipfile.ZipFile(archive,"w",zipfile.ZIP_DEFLATED) as output:
        output.writestr("subject-budgets.json",json.dumps(result,sort_keys=True,indent=2)+"\n")
    print("archive_sha256",hashlib.sha256(archive.read_bytes()).hexdigest())
