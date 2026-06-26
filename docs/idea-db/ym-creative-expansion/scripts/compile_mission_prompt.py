#!/usr/bin/env python3
import argparse, json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

def main():
    ap = argparse.ArgumentParser(description="Compile a mission prompt from a v4 mission contract")
    ap.add_argument("contract", help="Path to mission_contracts/OC_*.json or contract id")
    args = ap.parse_args()
    p = Path(args.contract)
    if not p.exists():
        p = ROOT / "mission_contracts" / f"{args.contract}.json"
    c = json.loads(p.read_text(encoding="utf-8"))
    print(f"# Mission {c['id']}\n")
    print(f"Proof card: `{c['proof_card']}`\n")
    print(c["mission"] + "\n")
    print("Allowed source keys:")
    for k in c["allowed_source_keys"]:
        print(f"- `{k}`")
    print("\nTarget shape:\n")
    print("```text")
    print(c["target_shape"])
    print("```\n")
    print("Minimal success:")
    for x in c["minimal_success"]:
        print(f"- {x}")
    print("\nReject if:")
    for x in c["reject_if"]:
        print(f"- {x}")

if __name__ == "__main__":
    main()
