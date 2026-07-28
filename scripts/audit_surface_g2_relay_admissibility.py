"""Read-only terminal audit for the finite-beta scaled sign archive.

This script never edits historical manifests.  It separates archive
admissibility (hashes, CWIN, signs, adjacency and seams) from the direct
Wronskian role implication checked by ``audit_surface_finite_role_relay``.
The terminal fingerprint was frozen only after the deterministic canonical
subcover rule had selected the ownership chain; changing a manifest, either
run, or any ownership row fails closed.
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
EXPECTED_OWNER_COUNT = 501
EXPECTED_TERMINAL_FINGERPRINT = (
    "86029ed96f88c53fd0fe18769e33577d4eee56aed553f36943dd490f09b7ae80"
)


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def sha256_lf(path: Path) -> str:
    return hashlib.sha256(path.read_bytes().replace(b"\r\n", b"\n")).hexdigest()


def sha256_variants(path: Path) -> set[str]:
    raw = path.read_bytes()
    lf = raw.replace(b"\r\n", b"\n")
    crlf = lf.replace(b"\n", b"\r\n")
    return {
        hashlib.sha256(raw).hexdigest(),
        hashlib.sha256(lf).hexdigest(),
        hashlib.sha256(crlf).hexdigest(),
    }


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
        fields = head.split()
        if len(fields) == 4:
            _, index_text, lo_text, hi_text = fields
        elif (len(fields) == 6 and fields[0] == "trow"
              and fields[2] == "partition"):
            # Explicit-partition candidate transcripts retain the same
            # adjacency contract while recording the partition id.
            _, index_text, _, _, lo_text, hi_text = fields
        else:
            result["reasons"].append("malformed_trow_header")
            continue
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

    # The right seam increases with beta.  A box [beta_lo,beta_hi] therefore
    # has to reach the endpoint at beta_hi; using beta_lo would under-check a
    # positive-width box and silently admit an uncovered moving-edge wedge.
    beta_arb = arb(beta_hi.numerator) / arb(beta_hi.denominator)
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
    # Current single-unit manifests use ``outputs`` as a mapping with direct
    # production/replay entries.  Treat it as one normalized group; otherwise
    # valid files are incorrectly reported as missing by the read-only audit.
    if isinstance(manifest.get("outputs"), dict):
        outputs = manifest["outputs"]
        production = outputs.get("production")
        replay = outputs.get("replay")
        if isinstance(production, dict) and isinstance(replay, dict):
            groups.append(("outputs", [production, replay]))
    if isinstance(manifest.get("outputs"), list):
        outputs = manifest["outputs"]
        # Early manifests flattened several production/replay pairs into one
        # list.  Taking only the first pair silently dropped valid beta units
        # from the coverage union.  Recover pairs by the canonical filename
        # relation ``foo.txt`` <-> ``foo_rerun.txt``; unmatched schemas still
        # fall through to the historical single-pair normalization below.
        by_path = {
            str(item.get("path")): item for item in outputs
            if isinstance(item, dict) and item.get("path")
        }
        paired = []
        for item in outputs:
            if not isinstance(item, dict):
                continue
            path = str(item.get("path", ""))
            if not path or path.endswith("_rerun.txt"):
                continue
            replay = by_path.get(path[:-4] + "_rerun.txt") \
                if path.endswith(".txt") else None
            if replay is not None:
                paired.append((Path(path).stem, [item, replay]))
        if paired:
            groups.extend((name, pair) for name, pair in paired)
        else:
            groups.append(("outputs", outputs))
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
        if (recorded
                and str(recorded).lower() not in sha256_variants(path)
                and (not recorded_lf
                     or sha256_lf(path).lower() != str(recorded_lf).lower())):
            reasons.append("recorded_output_hash_mismatch")
    return reasons


def beta_union_summary(accepted: list[dict]) -> dict:
    """Compute the exact rational union and a deterministic ownership chain.

    Historical campaigns contain redundant and partially overlapping boxes.
    Requiring every accepted source box to be pairwise adjacent therefore
    confuses harmless redundancy with a coverage failure.  The theorem needs
    the union, not a partition of every archived source.  We coalesce the
    exact rational intervals and also construct a canonical restricted
    subcover: every ownership row is a subinterval of its source certificate,
    and the ownership rows are exactly adjacent.
    """
    records = []
    for unit in accepted:
        lo_text, hi_text = unit["transcript"]["beta"]
        lo, hi = Fraction(lo_text), Fraction(hi_text)
        records.append({
            "lo": lo,
            "hi": hi,
            "manifest": unit["manifest"],
            "unit": unit.get("unit", ""),
        })
    records.sort(key=lambda item: (
        item["lo"], item["hi"], item["manifest"], item["unit"]))

    raw_adjacency = all(
        left["hi"] == right["lo"]
        for left, right in zip(records, records[1:])
    )
    components: list[list[Fraction]] = []
    for item in records:
        lo, hi = item["lo"], item["hi"]
        if not components or lo > components[-1][1]:
            components.append([lo, hi])
        elif hi > components[-1][1]:
            components[-1][1] = hi

    gaps: list[list[str]] = []
    cursor = BETA_LO
    for lo, hi in components:
        if hi <= BETA_LO or lo >= BETA_HI:
            continue
        lo, hi = max(lo, BETA_LO), min(hi, BETA_HI)
        if lo > cursor:
            gaps.append([str(cursor), str(lo)])
        if hi > cursor:
            cursor = hi
        if cursor >= BETA_HI:
            break
    if cursor < BETA_HI:
        gaps.append([str(cursor), str(BETA_HI)])
    covered = not gaps and cursor >= BETA_HI

    ownership = []
    cursor = BETA_LO
    while cursor < BETA_HI:
        candidates = [
            item for item in records
            if item["lo"] <= cursor < item["hi"]
        ]
        if not candidates:
            break
        # Longest reach first; the remaining fields make ties reproducible.
        chosen = min(
            candidates,
            key=lambda item: (
                -item["hi"], item["lo"], item["manifest"], item["unit"]),
        )
        owned_hi = min(chosen["hi"], BETA_HI)
        ownership.append({
            "owned_beta": [str(cursor), str(owned_hi)],
            "source_beta": [str(chosen["lo"]), str(chosen["hi"])],
            "manifest": chosen["manifest"],
            "unit": chosen["unit"],
        })
        cursor = owned_hi

    ownership_adjacency = bool(ownership)
    owner_cursor = BETA_LO
    for row in ownership:
        lo, hi = map(Fraction, row["owned_beta"])
        ownership_adjacency &= lo == owner_cursor and hi > lo
        owner_cursor = hi
    ownership_complete = ownership_adjacency and owner_cursor == BETA_HI

    return {
        "raw_adjacency": raw_adjacency,
        "components": [[str(lo), str(hi)] for lo, hi in components],
        "gaps": gaps,
        "covered": covered,
        "ownership": ownership,
        "ownership_adjacency": ownership_adjacency,
        "ownership_complete": ownership_complete,
    }


def terminal_fingerprint(units: list[dict], ownership: list[dict]) -> str:
    """Bind the deterministic ownership chain to manifests and both runs."""

    accepted = {
        (unit["manifest"], unit.get("unit", "")): unit
        for unit in units
        if unit.get("ok")
    }
    digest = hashlib.sha256()
    for row in ownership:
        key = (row["manifest"], row["unit"])
        if key not in accepted:
            raise AssertionError(f"ownership row has no accepted source: {key}")
        unit = accepted[key]
        digest.update(
            json.dumps(
                row,
                sort_keys=True,
                separators=(",", ":"),
            ).encode("utf-8")
        )
        digest.update(b"\0")
        for relative in (
            f"run-manifests/{row['manifest']}",
            unit["production"],
            unit["replay"],
        ):
            digest.update(relative.encode("utf-8"))
            digest.update(b"\0")
            digest.update(
                (ROOT / relative).read_bytes().replace(b"\r\n", b"\n")
            )
            digest.update(b"\0")
    return digest.hexdigest()


def audit_summary() -> dict:
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
                          "reasons": sorted(set(reasons)),
                          "transcript": parsed,
                          "production": production["path"],
                          "replay": replay["path"]})
    accepted = [u for u in units if u["ok"]]
    accepted_boxes = sorted(
        (u["transcript"]["beta"] for u in accepted),
        key=lambda x: (Fraction(x[0]), Fraction(x[1])),
    )
    union = beta_union_summary(accepted)
    fingerprint = terminal_fingerprint(units, union["ownership"])
    terminal = (
        union["covered"]
        and union["ownership_complete"]
        and union["components"] == [[str(BETA_LO), str(BETA_HI)]]
        and not union["gaps"]
        and len(union["ownership"]) == EXPECTED_OWNER_COUNT
        and fingerprint == EXPECTED_TERMINAL_FINGERPRINT
    )
    return {
        "contract": "SURFACE-G2-FINITE-BETA-RELAY-CONTRACT-20260721",
        "relay_status": "DIRECT_WRONSKIAN_SIGN_ARCHIVE_CERTIFIED",
        "target_beta": [str(BETA_LO), str(BETA_HI)],
        "target_t_left": str(T_LEFT),
        "units_seen": len(units),
        "units_admissible": len(accepted),
        "beta_union_adjacency": union["raw_adjacency"],
        "beta_union_components": union["components"],
        "beta_union_complete": union["covered"],
        "beta_union_gaps": union["gaps"],
        "canonical_subcover": union["ownership"],
        "canonical_subcover_adjacency": union["ownership_adjacency"],
        "canonical_subcover_complete": union["ownership_complete"],
        "canonical_subcover_fingerprint": fingerprint,
        "canonical_subcover_owner_count": len(union["ownership"]),
        "accepted_beta_boxes": accepted_boxes,
        "deficiencies": [u for u in units if not u["ok"]],
        "skipped_manifests": skipped,
        "promotion": (
            "FINITE_BULK_SIGN_CERTIFIED" if terminal else "NONE"
        ),
    }


def main() -> int:
    summary = audit_summary()
    print(json.dumps(summary, indent=2, sort_keys=True))
    if summary["promotion"] != "FINITE_BULK_SIGN_CERTIFIED":
        print("FINITE-BETA BULK SIGN ARCHIVE BLOCKED")
        return 1
    print("FINITE-BETA BULK SIGN ARCHIVE CERTIFIED")
    print("SCOPE direct finite-beta role only; no high-beta/G6 promotion")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
