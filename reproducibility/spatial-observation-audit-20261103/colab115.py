"""Prepared own-runtime recipe115. UNEXECUTED at preparation; Colab Linux only."""
import base64
import hashlib
import json
import os
import pathlib
import platform
import subprocess
import sys
import traceback
import zipfile
from datetime import datetime, timezone

if not sys.platform.startswith("linux"):
    raise RuntimeError("Only execute in this chat's own Colab Linux runtime")
from google.colab import runtime

THREAD = "tep-own-spatial-observation-audit"
SOURCE = "ace78c3bb3f31d14244aa5acd61829c5d99ece34"
FIXTURE = "reproducibility/spatial-observation-audit-20261103/exact-audit.py"
FIXTURE_HASH = "e191abd7524ddb165bdab53e589255769da9a44a6d05ffe4777593551bdb209f"
NOTES = "reproducibility/mean-budget-order-20261101/"
FILES = [FIXTURE] + [NOTES + n for n in ["interblock-shorted-energy.md",
         "mean-penalty-slack-criterion.md", "sparse-point-observation-obstruction.md"]]
ROOT = pathlib.Path("/content/tep-own-115-spatial-observation")
if ROOT.exists():
    runtime.unassign()
    raise RuntimeError("Existing run115 must be recovered, not overwritten")
ROOT.mkdir(exist_ok=False)
OUT = ROOT / "evidence"
OUT.mkdir()
report = dict(run="115", thread=THREAD, source_sha=SOURCE,
              started_utc=datetime.now(timezone.utc).isoformat(), status="RUNNING",
              general_theorem_verified=False, new_lean_run=False,
              independent_review=False, terminal_reproduction=False, steps=[])


def need(ok, message):
    if not ok:
        raise ValueError(message)


def run(label, argv, cwd=None, timeout=180):
    p = subprocess.run(argv, cwd=cwd, capture_output=True, text=True, timeout=timeout)
    (OUT / (label + ".stdout.txt")).write_text(p.stdout)
    (OUT / (label + ".stderr.txt")).write_text(p.stderr)
    sentinel = OUT / (label + ".exit.txt")
    temp = OUT / (label + ".exit.tmp")
    temp.write_text(str(p.returncode) + "\n")
    value = temp.read_text()
    need(value == str(p.returncode) + "\n", "real decimal exit code")
    temp.replace(sentinel)
    report["steps"].append(dict(label=label, exit_code=p.returncode))
    need(p.returncode == 0, label + " failed; retain complete logs")
    return p.stdout


try:
    need(os.environ.get("COLAB_GPU", "0") in ["0", ""], "Use CPU, not a GPU allocation")
    payloads = []
    for name in ["fresh_a", "fresh_b"]:
        clone = ROOT / name
        run(name + "_init", ["git", "init", str(clone)])
        run(name + "_remote", ["git", "remote", "add", "origin",
                               "https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME.git"], clone)
        for key, value in [("core.autocrlf", "false"), ("core.sparseCheckout", "true"),
                           ("remote.origin.promisor", "true"),
                           ("remote.origin.partialclonefilter", "blob:none")]:
            run(name + "_config_" + key, ["git", "config", key, value], clone)
        (clone / ".git/info/sparse-checkout").write_text("\n".join("/" + f for f in FILES) + "\n")
        run(name + "_fetch", ["git", "fetch", "--depth=1", "--filter=blob:none",
                              "origin", SOURCE], clone)
        run(name + "_checkout", ["git", "checkout", "--detach", "FETCH_HEAD"], clone)
        sha = run(name + "_sha", ["git", "rev-parse", "HEAD"], clone).strip()
        need(sha == SOURCE, "exact immutable source SHA")
        need(hashlib.sha256((clone / FIXTURE).read_bytes()).hexdigest() == FIXTURE_HASH,
             "exact diagnostic bytes")
        for f in FILES:
            target = OUT / "source" / f
            target.parent.mkdir(parents=True, exist_ok=True)
            data = (clone / f).read_bytes()
            if target.exists():
                need(target.read_bytes() == data, "fresh-clone source bytes differ")
            else:
                target.write_bytes(data)
        for mode, flags in [("normal", []), ("optimized", ["-O"])]:
            stdout = run(name + "_" + mode,
                         [sys.executable] + flags + [str(clone / FIXTURE)], clone, 120)
            row = json.loads(stdout)
            need(row["status"] == "FINITE_DIAGNOSTICS_ACCEPTED", "diagnostic acceptance")
            need(row["accepted"] == 18 and row["real_mutations_rejected"] == 8,
                 "explicit finite acceptance/mutation counts")
            need(row["optimized"] == (mode == "optimized"), "real interpreter mode")
            need(row["general_theorem_verified"] is False and row["new_lean_run"] is False
                 and row["independent_review"] is False, "finite scope")
            row.pop("optimized")
            payloads.append(row)
    need(len(payloads) == 4 and all(x == payloads[0] for x in payloads),
         "both modes and two fresh clones must match complete output")
    report.update(status="EXACT_FINITE_DIAGNOSTICS_PASS", accepted_each=18,
                  real_mutations_rejected_each=8, fresh_clones=2,
                  normal_optimized_match=True, fresh_clone_payloads_match=True,
                  finite_payload_sha256=hashlib.sha256(json.dumps(payloads[0],
                      sort_keys=True, separators=(",", ":")).encode()).hexdigest(),
                  finite_fixtures=payloads[0]["fixtures"])
except BaseException as exc:
    report.update(status="FAIL", error=repr(exc))
    (OUT / "exception.txt").write_text(traceback.format_exc())
finally:
    report["finished_utc"] = datetime.now(timezone.utc).isoformat()
    report["colab_gpu_environment"] = os.environ.get("COLAB_GPU", "unset")
    report["runtime_note"] = "Own CPU allocation; record UI units before/after separately, do not infer zero cost"
    (OUT / "report.json").write_text(json.dumps(report, sort_keys=True, indent=2))
    (OUT / "python-platform.txt").write_text(sys.version + "\n" + platform.platform())
    (OUT / "recipe115.py").write_bytes(pathlib.Path(__file__).read_bytes())
    manifest = {str(p.relative_to(OUT)): hashlib.sha256(p.read_bytes()).hexdigest()
                for p in sorted(OUT.rglob("*")) if p.is_file()}
    (OUT / "manifest.json").write_text(json.dumps(manifest, sort_keys=True, indent=2))
    bundle = ROOT / "diagnostics115.zip"
    with zipfile.ZipFile(bundle, "w", zipfile.ZIP_DEFLATED) as z:
        for p in sorted(OUT.rglob("*")):
            if p.is_file():
                z.write(p, str(p.relative_to(OUT)))
    print("FINAL_REPORT=" + json.dumps(report, sort_keys=True), flush=True)
    print("BUNDLE_SHA256=" + hashlib.sha256(bundle.read_bytes()).hexdigest(), flush=True)
    print("EVIDENCE_BASE64_BEGIN=" + base64.b64encode(bundle.read_bytes()).decode()
          + "=EVIDENCE_BASE64_END", flush=True)
    print("Finite diagnostics only. Releasing this own runtime.", flush=True)
    runtime.unassign()
