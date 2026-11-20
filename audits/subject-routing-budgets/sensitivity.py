"""Compare three exact-string repetition policies against the official row-weighted panel."""
import hashlib
import json
from pathlib import Path
import sys
import zipfile

from mmlu import analyze, load_panel, small_check


def sensitivity():
    small_check()
    domains, original, items, prompts, manifest = load_panel()
    repeated = [v for v in prompts.values() if len(v)>1]
    policies = {
        "official": range(len(items)),
        "singleton": sorted(v[0] for v in prompts.values() if len(v)==1),
        "first": sorted(v[0] for v in prompts.values()),
        "last": sorted(v[-1] for v in prompts.values()),
    }
    reports = {}
    for key, indices in policies.items():
        rows = [items[i] for i in indices]
        report = analyze(domains,rows)
        reports[key] = report
    assert reports["official"]["existential"]==[1840,13951]
    assert reports["official"]["universal"]==[[2495,13300]]
    assert reports["official"]["largest_shortfall"]["missed"]==339
    return dict(raw_rows=original, official_exclusions=original-len(items), source_sha256=manifest,
                repeated_strings=len(repeated), repeated_rows=sum(map(len,repeated)),
                across_subjects=sum(len({items[i][0] for i in v})>1 for v in repeated),
                conflicting_pairs=sum(len({items[i][1:] for i in v})>1 for v in repeated), panels=reports)


if __name__=="__main__":
    archive = Path(sys.argv[1] if len(sys.argv)==2 and sys.argv[1].endswith(".zip") else "/content/archive.zip")
    with zipfile.ZipFile(archive,"w",zipfile.ZIP_DEFLATED) as target:
        target.writestr("sensitivity.json",json.dumps(sensitivity(),sort_keys=True,indent=2)+"\n")
    print("archive_sha256",hashlib.sha256(archive.read_bytes()).hexdigest())
