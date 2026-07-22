"""Read-only pre-registered audit for the finite-beta scaled relay.

This script never edits manifests and never promotes G2/G6.  It separates
archive admissibility (hashes, CWIN, signs, adjacency and seams) from the
still-unproved analytic implication to (H_tail).
"""

from __future__ import annotations

import hashlib
import json
import math
import re
from fractions import Fraction
from pathlib import Path

from flint import arb, ctx


ROOT = Path(__file__).resolve().parents[1]
MANIFEST_GLOB = "surface-scaled-bulk-*.json"
BETA_LO = Fraction(20)
BETA_HI = Fraction(1000, 9)
T_LEFT = Fraction(3, 5)
RELAY_STATUS = "RELAY_LEMMA_UNPROVED"


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def sha256_lf(path: Path) -> str:
    return hashlib.sha256(path.read_bytes().replace(b"\\r\\n", b"\\n")).hexdigest()


def fraction(value: str) -> Fraction:
    return Fraction(value)


def parse_cwin(config_line: str) -> Fraction | None:
    match = re.search(r"\bCWIN\s+([^\s]+)", config_line)
    return fraction(match.group(1)) if match else None


def parse_transcript(path: Path) -> dict:
    lines = path.read_text(encoding="utf-8").splitlines()
    result = {"path": str(path.relative_to(ROOT)), "ok": False, "reasons": []}
    config = next((line for line in lines if line.startswith("config ")), None)
    beta_line = next((line for line in lines if line.startswith("beta_domain ")), None)
    t_domain_line = next((line for line in lines if line.startswith("t_domain ")), None)
    if config is None or beta_line is None or t_domain_line is None:
        result["reasons"].append("missing_scaled_domain_headers")
        return result
    result["cwin"] = str(parse_cwin(config)) if parse_cwin(config) is not None else None
    if parse_cwin(config) != Fraction(3, 2):
        result["reasons"].append("cwin_not_3_over_2")
    _, beta_lo_text, beta_hi_text = beta_line.split()[:3]
    beta_lo, beta_hi = fraction(beta_lo_text), fraction(beta_hi_text)
    result["beta"] = [str(beta_lo), str(beta_hi)]
    if beta_lo < BETA_LO or beta_hi > BETA_HI or beta_lo >= beta_hi:
        result["reasons"].append("beta_box_outside_target")
    _, t_lo_text, t_hi_text = t_domain_line.split()[:3]
    t_lo, t_hi = fraction(t_lo_text), fraction(t_hi_text)
    rows = []
    for line in lines:
        if not line.startswith("trow ") or " upper " not in line:
            continue
        head, upper_text = line.split(" upper ", 1)
        _, index_text, lo_text, hi_text = head.split()
        rows.append((int(index_text), fraction(lo_text), fraction(hi_text), arb(upper_text)))
    result["rows"] = len(rows)
    cursor = t_lo
    for expected, (index, lo, hi, upper) in enumerate(rows):
        if index != expected:
            result["reasons"].append("row_index_gap")
        if lo != cursor or hi <= lo:
            result["reasons"].append("row_adjacency_failure")
        if not upper.is_finite() or not (upper < 0):
            result["reasons"].append("nonnegative_or_nonfinite_upper")
        cursor = hi
    if not rows:
        result["reasons"].append("no_t_rows")
    elif cursor != t_hi:
        result["reasons"].append("row_partition_does_not_end_at_domain")

    # The right seam increases with beta, so beta_lo gives the conservative
    # endpoint that must be covered by every box.
    beta_arb = arb(beta_lo.numerator) / arb(beta_lo.denominator)
    target_hi = arb.pi() - arb(3) / (arb(2) * beta_arb)
    start_ok = t_lo <= T_LEFT
    cursor_arb = arb(cursor.numerator) / arb(cursor.denominator)
    end_ok = bool(cursor_arb >= target_hi) if rows else False
    result["required_t"] = [str(T_LEFT), target_hi.str(18)]
    result["t_domain"] = [str(t_lo), str(t_hi)]
    if not start_ok:
        result["reasons"].append("left_bulk_seam_gap")
    if not end_ok:
        result["reasons"].append("right_g5_seam_gap")
    result["ok"] = not result["reasons"]
    return result


def output_groups(manifest: dict) -> list[tuple[str, dict, dict]]:
    """Normalize the three historical manifest schemas into output pairs."""
    groups = []
    if isinstance(manifest.get("outputs"), list):
        groups.append(("outputs", manifest["outputs"]))
    if isinstance(manifest.get("units"), list):
        for index, unit in enumerate(manifest["units"]):
            if isinstance(unit, dict):
                groups.append((f"unit-{index}", [unit.get("production"), unit.get("replay")]))
    if isinstance(manifest.get("unit"), dict):
        unit = manifest["unit"]
        groups.append((str(unit.get("name", "unit")), [unit.get("production"), unit.get("replay")]))
    result = []
    for name, outputs in groups:
        if not isinstance(outputs, list):
            continue
        production = next((x for x in outputs if isinstance(x, dict)
                           and not str(x.get("path", "")).endswith("_rerun.txt")), None)
        replay = next((x for x in outputs if isinstance(x, dict)
                       and str(x.get("path", "")).endswith("_rerun.txt")), None)
        if production and replay:
            result.append((name, production, replay))
    return result


def verify_outputs(production: dict, replay: dict) -> list[str]:
    reasons = []
    pp, rp = ROOT / production["path"], ROOT / replay["path"]
    if not pp.is_file() or not rp.is_file():
        return ["production_or_replay_file_missing"]
    if pp.read_bytes() != rp.read_bytes():
        reasons.append("production_replay_byte_mismatch")
    for item in (production, replay):
        path = ROOT / item["path"]
        recorded = item.get("sha256")
        recorded_lf = item.get("sha256_lf")
        if (recorded and sha256(path).lower() != str(recorded).lower()
                and (not recorded_lf or sha256_lf(path).lower() != str(recorded_lf).lower())):
            reasons.append("recorded_output_hash_mismatch")
    return reasons


def main() -> int:
    ctx.prec = 180
    units = []
    skipped = []
    for path in sorted((ROOT / "run-manifests").glob(MANIFEST_GLOB)):
        try:
            manifest = json.loads(path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            skipped.append({"manifest": path.name, "reason": "unreadable_json"})
            continue
        claim = str(manifest.get("claim_scope", ""))
        run_id = str(manifest.get("run_id", ""))
        if "CWIN=3/2" not in claim and "cwin3p2" not in run_id:
            continue
        # Explicitly quarantined/design-only manifests are inventory records,
        # never admissible relay units.  They must not enter the acceptance
        # set merely because their transcripts happen to parse and replay.
        if str(manifest.get("status", "")).lower() in {"design_only", "quarantined"}:
            skipped.append({"manifest": path.name, "reason": "explicit_nonterminal_status"})
            continue
        if "not admissible" in claim.lower() or "post-hoc" in claim.lower():
            skipped.append({"manifest": path.name, "reason": "explicit_nonterminal_claim"})
            continue
        groups = output_groups(manifest)
        if not groups:
            units.append({"manifest": path.name, "status": manifest.get("status"),
                          "ok": False, "reasons": ["production_or_replay_missing"]})
            continue
        for group_name, production, replay in groups:
            reasons = verify_outputs(production, replay)
            production_path = ROOT / production["path"]
            parsed = (parse_transcript(production_path)
                      if production_path.is_file()
                      else {"ok": False, "reasons": ["no_production_transcript"]})
            reasons.extend(parsed.get("reasons", []))
            units.append({"manifest": path.name, "unit": group_name,
                          "status": manifest.get("status"),
                          "ok": not reasons and parsed.get("ok", False),
                          "reasons": sorted(set(reasons)), "transcript": parsed})
    accepted = [u for u in units if u["ok"]]
    accepted_boxes = sorted((u["transcript"]["beta"] for u in accepted), key=lambda x: Fraction(x[0]))
    adjacency = all(Fraction(a[1]) == Fraction(b[0]) for a, b in zip(accepted_boxes, accepted_boxes[1:]))
    beta_gaps = []
    if accepted_boxes and Fraction(accepted_boxes[0][0]) > BETA_LO:
        beta_gaps.append([str(BETA_LO), accepted_boxes[0][0]])
    for left, right in zip(accepted_boxes, accepted_boxes[1:]):
        if Fraction(left[1]) < Fraction(right[0]):
            beta_gaps.append([left[1], right[0]])
    if accepted_boxes and Fraction(accepted_boxes[-1][1]) < BETA_HI:
        beta_gaps.append([accepted_boxes[-1][1], str(BETA_HI)])
    covered = bool(accepted_boxes and Fraction(accepted_boxes[0][0]) == BETA_LO
                   and Fraction(accepted_boxes[-1][1]) == BETA_HI and adjacency)
    summary = {
        "contract": "SURFACE-G2-FINITE-BETA-RELAY-CONTRACT-20260721",
        "relay_status": RELAY_STATUS,
        "target_beta": [str(BETA_LO), str(BETA_HI)],
        "target_t_left": str(T_LEFT),
        "units_seen": len(units),
        "units_admissible": len(accepted),
        "beta_union_adjacency": adjacency,
        "beta_union_complete": covered,
        "beta_union_gaps": beta_gaps,
        "accepted_beta_boxes": accepted_boxes,
        "deficiencies": [u for u in units if not u["ok"]],
        "skipped_manifests": skipped,
        "promotion": "NONE",
    }
    print(json.dumps(summary, indent=2, sort_keys=True))
    print("G2 RELAY AUDIT ONLY; NO G2/G6 PROMOTION")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
