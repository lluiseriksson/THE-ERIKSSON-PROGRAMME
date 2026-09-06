"""Validate the immutable R2 gate-6 archive; run only on the Colab plane.

This does not rewrite gate 6's FAIL verdict or rerun Lean. It checks saved
process exits, exact source/log bytes and every axiom report, including names
containing apostrophes. Usage: python check_gate6_logs.py ARCHIVE.tar.gz
Repeat with python -O. All acceptance and mutation checks are explicit.
"""

import copy
import hashlib
import io
import json
import re
import sys
import tarfile

ARCHIVE_SHA256 = "77c85e48ddf0402548fe7c9c4bb38ebbabbbe76636ecfaa7c4f2f8e32151d14d"
BASE = "ba48274f217220ae2aa47ddaddd8e377fb2231a8"
SOURCE_HASHES = {
    "PhysicalWilsonCylinder.lean": "cd4eef25817d3a5f2ef6f61fdd19d3e8e5c3eca3b5fc34202ddd7219933e4d79",
    "PhysicalWilsonCylinderMeasure.lean": "1a345a144a95d2a61076a86edd23abf3b097e51f5adc0e0edb8ea9aa224b6884",
    "oracle_check.lean": "2d7122db41bde8055f9a3290c98ae22e2db361b65b12f4bb5c4953ae5d2e09e3",
    "R2Audit.lean": "7f449daf562b7dff0daf6c62325f8550c99a326684412ea16efff35cd513ff8a",
}
STAGES = ["git-init", "remote", "fetch", "checkout", "elan", "toolchain",
          "mathlib-cache", "focal", "oracle", "core", "consistency", "dashboard",
          "global-imports", "global-oracle"]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
# A declaration name may itself contain apostrophes. Anchor at the report's
# line start and closing delimiter, not at the first apostrophe in the name.
REPORT = re.compile(
    r"^'([^\n]+)' (?:depends on axioms:\s*\[([^]]*)\]|does not depend on any axioms)$",
    re.M,
)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def check_reports(driver, output, count):
    names = re.findall(r"^#print axioms (\S+)", driver, re.M)
    rows = REPORT.findall(output)
    require(len(names) == count, "driver count")
    require(len(rows) == count, "report count")
    require([n for n, _ in rows] == names, "report names/order")
    for name, body in rows:
        require({x.strip() for x in body.split(",") if x.strip()} <= ALLOWED,
                "unexpected axiom: " + name)
    return rows


def check_artifacts(data):
    manifest = json.loads(data["manifest.json"])
    require(manifest["base"] == BASE, "base")
    require(manifest["verdict"] == "FAIL", "original verdict must remain FAIL")
    require(manifest["error"] == "RuntimeError('Global oracle names/count mismatch')",
            "original failure")
    require([s["name"] for s in manifest["stages"]] == STAGES, "stage names/order")
    for stage in manifest["stages"]:
        require(type(stage["exit"]) is int and stage["exit"] == 0,
                "nonzero or invalid exit: " + stage["name"])
        require(hashlib.sha256(data[stage["name"] + ".log"]).hexdigest()
                == stage["log_sha256"], "stage log hash: " + stage["name"])
    for name, expected in SOURCE_HASHES.items():
        require(hashlib.sha256(data[name]).hexdigest() == expected, "source hash: " + name)
    focal = check_reports(data["R2Audit.lean"].decode(), data["oracle.log"].decode(), 39)
    global_rows = check_reports(data["oracle_check.lean"].decode(),
                                data["global-oracle.log"].decode(), 2854)
    return focal, global_rows


def reject(label, operation):
    try:
        operation()
    except ValueError:
        return label
    raise RuntimeError("Mutation was accepted: " + label)


def mutation_checks(data):
    driver, output = data["oracle_check.lean"].decode(), data["global-oracle.log"].decode()
    matches = list(REPORT.finditer(output))
    first = matches[0]
    prime = next(m for m in matches if "'" in m.group(1))
    cases = {
        "missing report": output[:first.start()] + output[first.end():],
        "duplicate report": output + first.group(0) + "\n",
        "renamed report": output.replace(first.group(1), first.group(1) + "_wrong", 1),
        "removed prime": output[:prime.start()] + prime.group(0).replace(
            prime.group(1), prime.group(1).replace("'", ""), 1) + output[prime.end():],
        "nonstandard axiom": output.replace("[propext,", "[sorryAx,", 1),
        "malformed report": output.replace("depends on axioms:", "unreadable:", 1),
        "reordered reports": (matches[1].group(0) + "\n" + first.group(0)
                              + output[matches[1].end():]),
    }
    rejected = [reject(label, lambda text=text: check_reports(driver, text, 2854))
                for label, text in cases.items()]
    rejected.append(reject("driver name", lambda: check_reports(
        driver.replace(first.group(1), first.group(1) + "_wrong", 1), output, 2854)))
    for label, key, value in [("nonzero exit", "exit", 1), ("empty exit", "exit", ""),
                              ("log digest", "log_sha256", "0" * 64)]:
        mutated = copy.copy(data)
        manifest = json.loads(data["manifest.json"])
        manifest["stages"][-1][key] = value
        mutated["manifest.json"] = json.dumps(manifest).encode()
        rejected.append(reject(label, lambda d=mutated: check_artifacts(d)))
    mutated = copy.copy(data)
    mutated["PhysicalWilsonCylinderMeasure.lean"] += b"\n"
    rejected.append(reject("source bytes", lambda: check_artifacts(mutated)))
    mutated_log = copy.copy(data)
    mutated_log["global-oracle.log"] += b"\n"
    rejected.append(reject("log bytes", lambda: check_artifacts(mutated_log)))
    require(len(rejected) == 13, "mutation counter")
    return rejected


def main():
    with open(sys.argv[1], "rb") as stream:
        archive = stream.read()
    require(hashlib.sha256(archive).hexdigest() == ARCHIVE_SHA256, "archive hash")
    with tarfile.open(fileobj=io.BytesIO(archive), mode="r:gz") as tar:
        members = [m for m in tar.getmembers() if m.isfile()]
        keys = [m.name.rsplit("/", 1)[-1] for m in members]
        require(len(keys) == len(set(keys)), "duplicate archive member")
        data = {key: tar.extractfile(m).read() for key, m in zip(keys, members)}
    focal, rows = check_artifacts(data)
    rejected = mutation_checks(data)
    report = {
        "verdict": "SAVED_LOG_VALIDATION_PASS",
        "original_gate_verdict": "FAIL",
        "archive_sha256": ARCHIVE_SHA256,
        "global_stdout_sha256": hashlib.sha256(data["global-oracle.log"]).hexdigest(),
        "focal_reports": len(focal), "global_reports": len(rows),
        "global_axiom_free": sum(not body for _, body in rows),
        "primed_names": [name for name, _ in rows if "'" in name],
        "mutations_rejected": rejected,
        "build_summaries": {key: re.findall(r"Build completed successfully \(\d+ jobs\)\.",
                                            data[key + ".log"].decode())
                            for key in ["focal", "core", "global-imports"]},
    }
    print(json.dumps(report, sort_keys=True, indent=2))


if __name__ == "__main__":
    main()
