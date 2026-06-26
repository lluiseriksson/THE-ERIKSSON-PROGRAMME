#!/usr/bin/env python3
import argparse, json, sys
from pathlib import Path


def load(path):
    return json.loads(Path(path).read_text(encoding="utf-8"))


def score(contract, intake):
    removed = len(intake.get("removed_fields", []))
    promotions = len(intake.get("source_promotions", []))
    toys = len(intake.get("toy_theorems", []))
    consumers = len(intake.get("new_downstream_consumers", []))
    opaque = len(intake.get("new_opaque_props", []))
    s = 10*removed + 6*promotions + 4*toys - 8*consumers - 5*opaque
    hard_fail = []
    text = json.dumps(intake, ensure_ascii=False).lower()
    for forbidden in ["decide(p in pindex", "lower bound on |p| as carrier", "bibliography as theorem", "ocr-only constants"]:
        if forbidden in text:
            hard_fail.append(forbidden)
    if consumers and not (removed or promotions):
        hard_fail.append("new consumers without removed fields/source promotions")
    missing = []
    for e in contract.get("evidence_required", []):
        if e not in intake.get("evidence", []):
            missing.append(e)
    accept = (s >= 10 and (removed + promotions) >= 1 and not hard_fail)
    return s, accept, hard_fail, missing


def main():
    ap = argparse.ArgumentParser(description="Score a candidate patch against a mission contract")
    ap.add_argument("--contract", required=True)
    ap.add_argument("--intake", required=True)
    args = ap.parse_args()
    contract = load(args.contract)
    intake = load(args.intake)
    s, accept, hard_fail, missing = score(contract, intake)
    print(json.dumps({"score": s, "accept": accept, "hard_fail": hard_fail, "missing_evidence": missing}, indent=2, ensure_ascii=False))
    if not accept:
        sys.exit(2)

if __name__ == "__main__":
    main()
