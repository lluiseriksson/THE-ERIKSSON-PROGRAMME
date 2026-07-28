"""Audit archived CWIN=3/2 rows for a direct Wronskian-sign theorem.

Unlike the G2 relay audit, this deliberately includes quarantined transcripts
as *candidate sign evidence*.  It never treats them as H_tail evidence and
never changes a manifest.  A passing result would still need an independent
proof that every transcript's dependency chain is authoritative before it
could be promoted to the paper.
"""

from __future__ import annotations

import hashlib
import json
import re
from fractions import Fraction
from pathlib import Path

from flint import arb, ctx

import audit_surface_g2_relay_admissibility as g2


ROOT = Path(__file__).resolve().parents[1]
BETA_LO, BETA_HI = Fraction(20), Fraction(1000, 9)
T_LEFT = Fraction(3, 5)


def _output_pairs(manifest: dict):
    return g2.output_groups(manifest)


def _transcript_ok(path: Path) -> tuple[bool, dict]:
    parsed = g2.parse_transcript(path)
    return not parsed["reasons"] and parsed.get("ok", False), parsed


def main() -> int:
    ctx.prec = 180
    units: list[dict] = []
    rejected: list[dict] = []
    seen = set()
    for manifest_path in sorted((ROOT / "run-manifests").glob("surface-scaled-bulk-*.json")):
        try:
            manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            continue
        run_id = str(manifest.get("run_id", ""))
        claim = str(manifest.get("claim_scope", ""))
        if "cwin3p2" not in run_id and "CWIN=3/2" not in claim:
            continue
        for group, production, replay in _output_pairs(manifest):
            pp, rp = ROOT / production["path"], ROOT / replay["path"]
            key = str(pp)
            if key in seen or not pp.is_file() or not rp.is_file():
                continue
            seen.add(key)
            reasons = []
            if pp.read_bytes() != rp.read_bytes():
                reasons.append("production_replay_byte_mismatch")
            for item in (production, replay):
                path = ROOT / item["path"]
                recorded = str(item.get("sha256", "")).lower()
                recorded_lf = str(item.get("sha256_lf", "")).lower()
                digest = hashlib.sha256(path.read_bytes()).hexdigest()
                digest_lf = hashlib.sha256(path.read_bytes().replace(b"\r\n", b"\n")).hexdigest()
                if recorded and digest != recorded and (not recorded_lf or digest_lf != recorded_lf):
                    reasons.append("recorded_output_hash_mismatch")
            good, parsed = _transcript_ok(pp)
            if not good:
                reasons.extend(parsed.get("reasons", []))
            if reasons:
                rejected.append({"manifest": manifest_path.name, "group": group,
                                 "beta": parsed.get("beta"),
                                 "reasons": sorted(set(reasons))})
                continue
            beta = tuple(Fraction(x) for x in parsed["beta"])
            units.append({"manifest": manifest_path.name, "group": group,
                          "beta": beta, "status": manifest.get("status", "")})

    units.sort(key=lambda item: (item["beta"], item["manifest"], item["group"]))

    def tiling(items):
        boxes = [item["beta"] for item in sorted(items, key=lambda x: (x["beta"], x["manifest"], x["group"]))]
        gaps, overlaps = [], []
        cursor = BETA_LO
        for lo, hi in boxes:
            if hi <= lo:
                continue
            if lo > cursor:
                gaps.append((cursor, lo))
            elif lo < cursor:
                overlaps.append((lo, min(cursor, hi)))
            cursor = max(cursor, hi)
        if cursor < BETA_HI:
            gaps.append((cursor, BETA_HI))
        complete = bool(boxes) and boxes[0][0] == BETA_LO and cursor == BETA_HI and not gaps and not overlaps
        return boxes, gaps, overlaps, cursor, complete

    boxes, gaps, overlaps, cursor, complete = tiling(units)
    current_boxes, current_gaps, current_overlaps, current_cursor, current_complete = tiling(
        [item for item in units if str(item["status"]).lower() == "current"]
    )
    print("DIRECT W-SIGN ARCHIVE AUDIT")
    print("VALID_TRANSCRIPTS", len(units))
    print("REJECTED_TRANSCRIPTS", len(rejected))
    reason_counts = {}
    for item in rejected:
        for reason in item["reasons"]:
            reason_counts[reason] = reason_counts.get(reason, 0) + 1
    print("REJECTION_REASONS", reason_counts)
    print("BETA_COMPONENT", (boxes[0][0], cursor) if boxes else None)
    print("GAPS", [(str(lo), str(hi)) for lo, hi in gaps])
    print("OVERLAPS", [(str(lo), str(hi)) for lo, hi in overlaps[:20]])
    print("EXACT_BETA_TILING", complete)
    print("CURRENT_STATUS_TILING", current_complete)
    print("CURRENT_STATUS_COMPONENT", (current_boxes[0][0], current_cursor) if current_boxes else None)
    print("CURRENT_STATUS_GAPS", [(str(lo), str(hi)) for lo, hi in current_gaps])
    print("CURRENT_STATUS_OVERLAPS", [(str(lo), str(hi)) for lo, hi in current_overlaps[:20]])
    print("CONCLUSION: candidate W^J sign only; no H_tail/G2/G6/K2/K4 promotion")
    return 0 if not complete else 1


if __name__ == "__main__":
    raise SystemExit(main())
