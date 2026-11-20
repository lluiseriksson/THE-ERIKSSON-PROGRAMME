"""Read public archival data only. Run on a dedicated Colab Linux CPU."""
from collections import Counter, defaultdict
from decimal import Decimal
from hashlib import sha256
from itertools import combinations
from pathlib import Path
import json
from urllib.request import urlopen
import zipfile

PIN = "04551715c7b74184ec5446fdd1c3221aae557862"
ROOT = f"https://raw.githubusercontent.com/dowlingwong/autoresearch_harness/{PIN}/"
TASKS = {"resnet_l40s": ("resnet", "val_auc", 1),
         "lr_synthetic": ("lr", "val_score", 1),
         "autoresearch_none": ("linux", "val_bpb", -1),
         "autoresearch_summary": ("linux", "val_bpb", -1)}

def require(ok, message):
    if not ok:
        raise ValueError(message)

def get(path):
    with urlopen(ROOT + path, timeout=45) as stream:
        return stream.read()

def curves(scores, sign):
    best = None
    attempts, scored, indices = [], [], []
    for i, value in enumerate(scores, 1):
        if value is not None:
            if best is None or sign * value > sign * best:
                best = value
            scored.append(best)
            indices.append(i)
        attempts.append(best)
    return attempts, scored, indices

def ordering(a, b, sign):
    return ((a > b) - (a < b)) * sign

manifest_raw = get("artifact_manifest.json")
groups = defaultdict(dict)
inputs = []
for item in json.loads(manifest_raw)["files"]:
    spec = TASKS.get(item.get("table7_row"))
    if spec is None or item["set"] != "primary":
        continue
    task, metric, sign = spec
    raw = get(item["path"])
    require(sha256(raw).hexdigest() == item["sha256"], item["path"])
    rows = [json.loads(line, parse_float=Decimal) for line in raw.splitlines() if line.strip()]
    require(len(rows) == item["records"] == item["expected_records"], item["campaign_id"])
    scores = []
    for index, row in enumerate(rows, 1):
        require(row["budget_index"] == index and row["campaign_id"] == item["campaign_id"], "sequence")
        valid = row["validity_status"] == "valid" and row["execution_status"] == "success"
        value = row["parsed_metrics"].get(metric) if valid else None
        require(not valid or value is not None, "missing primary metric")
        if value is not None:
            value = Decimal(str(value))
            require(value.is_finite(), "nonfinite score")
        scores.append(value)
    state = [rows[0][k] for k in ("node_state_hash", "training_seed", "current_best_before")]
    group = groups[task, item["seed"]]
    require(item["arm"] not in group, "duplicate arm")
    group[item["arm"]] = (curves(scores, sign), state, sign)
    inputs.append(dict(item, scored=sum(x is not None for x in scores), initial=state))

pairs, observations = [], []
for (task, seed), arms in sorted(groups.items()):
    for a, b in combinations(sorted(arms), 2):
        (ta, sa, ia), ra, sign = arms[a]
        (tb, sb, ib), rb, _ = arms[b]
        matched = bool(ra[0] and ra[1] is not None and ra == rb)
        counts = Counter()
        for k in range(1, min(len(sa), len(sb)) + 1):
            j = k-1
            if ta[j] is None or tb[j] is None:
                counts["undefined_attempt"] += 1
                continue
            da, ds = ordering(ta[j], tb[j], sign), ordering(sa[j], sb[j], sign)
            change = "strict_reversal" if da*ds == -1 else ("tie_transition" if da != ds else "same")
            counts[change] += 1
            observations.append(dict(task=task, seed=seed, matched=matched, arms=[a,b], k=k,
                attempt=[ta[j],tb[j]], scored=[sa[j],sb[j]], scored_at_attempt=[ia[j],ib[j]], classification=change))
        pairs.append(dict(task=task, seed=seed, arms=[a,b], matched=matched, valid_counts=[len(sa),len(sb)], counts=counts))
require(len(inputs) == 38 and len(pairs) == 34, "release population mismatch")
require(curves([None, Decimal(2), Decimal(1)], -1) == ([None,2,1],[2,1],[2,3]), "test failed")
data = dict(source=PIN, manifest_sha256=sha256(manifest_raw).hexdigest(), inputs=inputs, pairs=pairs, observations=observations)
dest = Path("/content/archive.zip")
with zipfile.ZipFile(dest, "w", zipfile.ZIP_DEFLATED) as z:
    z.writestr("clocks.json", json.dumps(data, default=str, indent=2)+"\n")
print("archive_sha256", sha256(dest.read_bytes()).hexdigest())
