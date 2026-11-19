"""Reconstruct three evaluation populations from the pinned public materials benchmark."""
import ast
import csv
import hashlib
import io
import json
import re
import sys
import urllib.request
import zipfile
from collections import Counter, defaultdict
from fractions import Fraction
from itertools import product
from pathlib import Path, PurePosixPath

import numpy as np

PIN = "631296b91a0b2de790de4f4b5cb563f223e2f66b"
ROOT = f"https://raw.githubusercontent.com/webbtheosim/data-efficient-regression/{PIN}/size/"
BLOBS = {
    100: "2ba639f5bfe2600805b7a2ddc12afb50bfa430f6",
    500: "0ed48b57e290efb5ecdeb721a909d3a8b073159c",
    1000: "04c9510ef438a21c6e90198274f597af3bd436d3",
    5000: "96816539b76725025c319ed27d3cd79ecbfe9061",
}
ARMS = ("cluster", "active")
MODES = {("sf","cluster","none","none"): "cluster", ("al","none","sv","topk"): "active"}
HALF = Fraction(1, 2)
H = Fraction(1, 200000)

def fetch(path, expected):
    with urllib.request.urlopen(ROOT + path, timeout=60) as response:
        raw = response.read()
    header = b"blob " + str(len(raw)).encode() + bytes([0])
    if hashlib.sha1(header + raw).hexdigest() != expected:
        raise ValueError(f"Git blob mismatch for {path}")
    return raw

def library_size(task):
    request = urllib.request.Request(ROOT + "databases/" + task + ".npy", headers={"Range":"bytes=0-127"})
    with urllib.request.urlopen(request,timeout=30) as response:
        raw = response.read(128)
    if raw[:8] != bytes([147])+b"NUMPY"+bytes([1,0]):
        raise ValueError(f"Unexpected NPY format for {task}")
    n = int.from_bytes(raw[8:10],"little")
    if n > 118:
        raise ValueError("Header exceeds the requested range")
    return ast.literal_eval(raw[10:10+n].decode().strip())["shape"][0]

def certificate(excluded_fraction, metrics):
    mae, rmse, relative = metrics
    q = 1-excluded_fraction
    m = (relative+H)**2
    a = max(0,mae-H)*max(0,relative-H)/(rmse+H)
    if m < q/4:
        return "pass"
    gap = a-q/2
    if gap > 0 and gap**2 > excluded_fraction*(m-q/4):
        if m > HALF**2:
            return "fail"
        if m < HALF**2:
            return "pass"
    return "unknown"

def costs(curve, population):
    candidates = []
    for point in curve:
        label = point[population]
        if label != "fail":
            candidates.append(point["cost"])
        if label == "pass":
            return candidates
    return candidates + [None]

def compare(cluster,active):
    if cluster is None or active is None:
        if cluster is None and active is None:
            return "neither"
        return "active_only" if cluster is None else "cluster_only"
    if cluster == active:
        return "equal"
    return "cluster_fewer" if cluster < active else "active_fewer"

def reconstruct():
    observations = defaultdict(set)
    results = fetch("results.csv","385bdf612e41170ca114514dbc51776a03d5d976")
    for row in csv.reader(io.StringIO(results.decode("utf-8-sig"))):
        arm = MODES.get(tuple(row[3:7]))
        if arm:
            key = row[0]+"-"+row[1], row[7], arm, int(row[2])
            observations[key].add(tuple(map(Fraction,row[9:12])))
    if not all(len(v)==1 for v in observations.values()):
        raise ValueError("Ambiguous published metric values")
    tasks_seeds = sorted({(t,s) for t,s,_,_ in observations})
    libraries = {t:library_size(t) for t in sorted({t for t,_ in tasks_seeds})}
    samples = {}
    duplicate_lists = 0
    for n,blob in BLOBS.items():
        raw = fetch(f"datasets/size_{n}.zip",blob)
        with zipfile.ZipFile(io.BytesIO(raw)) as archive:
            for member in archive.namelist():
                path = PurePosixPath(member)
                match = re.fullmatch(r"(.+)-(sf-cluster|al-sv-topk)-([0-9]+)\.npy",path.name)
                if not match or "__MACOSX" in path.parts:
                    continue
                task, method, seed = match.groups()
                arm = "cluster" if method=="sf-cluster" else "active"
                key = task,seed,arm,n
                if key not in observations:
                    continue
                arr = np.load(io.BytesIO(archive.read(member)),allow_pickle=False)
                if key in samples or arr.dtype.kind not in "iu" or arr.shape!=(n,):
                    raise ValueError(f"Invalid index list for {key}")
                ids = set(arr.tolist())
                if min(ids)<0 or max(ids)>=libraries[task]:
                    raise ValueError(f"Out-of-range index for {key}")
                duplicate_lists += int(len(ids)<n)
                samples[key]=ids
    if set(observations)!=set(samples):
        raise ValueError("Missing index lists")
    populations = ("whole","own","common")
    counts = {name:Counter() for name in populations}
    comparisons = {name:Counter() for name in populations}
    nonnested = 0
    pairs = []
    for task,seed in tasks_seeds:
        N = libraries[task]
        excluded = set().union(*(samples[task,seed,arm,n] for arm in ARMS for n in BLOBS))
        if len(excluded)>=N:
            raise ValueError("Empty fixed test set")
        curves = {}
        for arm in ARMS:
            seen,previous = set(),set()
            curve = []
            for n in BLOBS:
                selected = samples[task,seed,arm,n]
                nonnested += int(bool(previous-selected))
                previous = selected
                seen.update(selected)
                metrics, = observations[task,seed,arm,n]
                whole = "pass" if metrics[2]<HALF else "fail"
                if abs(metrics[2]-HALF)<=H:
                    raise ValueError("Whole-population rounding crossing")
                point = dict(budget=n,cost=len(seen),whole=whole,
                             own=certificate(Fraction(len(seen),N),metrics),
                             common=certificate(Fraction(len(excluded),N),metrics))
                for name in populations:
                    counts[name][point[name]]+=1
                curve.append(point)
            curves[arm]=curve
        record=dict(task=task,seed=seed,N=N,common_size=N-len(excluded),curves=curves)
        for name in populations:
            cc,ac = [costs(curves[arm],name) for arm in ARMS]
            outcomes=sorted({compare(x,y) for x,y in product(cc,ac)})
            comparisons[name][outcomes[0] if len(outcomes)==1 else "unresolved"]+=1
            record[name]=dict(cluster=cc,active=ac,outcomes=outcomes)
        pairs.append(record)
    return dict(source=PIN,rows=len(observations),pairs=len(pairs),duplicate_lists=duplicate_lists,
                nonnested=nonnested,cells=counts,comparisons=comparisons),pairs

def main():
    summary,pairs = reconstruct()
    assert summary["rows"]==1200 and summary["pairs"]==150
    assert summary["cells"]["own"]==dict(fail=369,unknown=467,**{"pass":364})
    assert summary["comparisons"]["own"]==dict(cluster_fewer=16,unresolved=134)
    assert (summary["duplicate_lists"],summary["nonnested"])==(105,900)
    target=Path(sys.argv[1])
    with zipfile.ZipFile(target,"x",zipfile.ZIP_DEFLATED) as archive:
        for name,value in [("summary",summary),("pairs",pairs)]:
            archive.writestr(name+".json",json.dumps(value,sort_keys=True))
    print("archive_sha256 "+hashlib.sha256(target.read_bytes()).hexdigest())

if __name__=="__main__":
    main()
