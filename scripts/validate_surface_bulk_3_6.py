"""Validate the canonical historical [3,6] plain Arb bulk transcript."""

from __future__ import annotations

from decimal import Decimal
import hashlib
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
TRANSCRIPT = ROOT / "scripts" / "certify_bulk_arb_transcript.txt"
SCRIPT = ROOT / "scripts" / "certify_bulk_arb.py"
COMMIT = "31663045ec3482f81b3577cbf491d706c7668de1"
SCRIPT_SHA256 = "3422ea0b603ebcf0af721586e51b7c268d3959545b81e4cc86dbd2cfb611c60a"
SCRIPT_SHA256_LF = "370ae701548344aa173603774b8c9fb260eb085bc352032418f28c089ac6efa8"
FINAL = ("CERTIFIED (plain, Arb): W < 0 on [0.6, pi-1.5/beta] x [3, 6]; "
         "592068 t-boxes total")
BOX = re.compile(r"^beta-box \[([0-9.]+), ([0-9.]+)\]: ([0-9]+) t-boxes$")


def validate(path: Path = TRANSCRIPT) -> dict[str, object]:
    raw = path.read_bytes()
    lines = raw.decode("utf-8").splitlines()
    if not lines or lines[-1] != FINAL:
        raise AssertionError("missing exact terminal verdict")
    text = "\n".join(lines)
    if text.count("narrowing beta step") != 1:
        raise AssertionError("expected exactly one recorded beta-step refinement")
    if "narrowing beta step to 0.000500 at beta=5.5280" not in text:
        raise AssertionError("unexpected adaptive refinement location")
    script_raw = SCRIPT.read_bytes()
    if hashlib.sha256(script_raw).hexdigest() != SCRIPT_SHA256:
        raise AssertionError("worktree script hash mismatch")
    blob = subprocess.check_output(
        ["git", "-c", f"safe.directory={ROOT.as_posix()}", "show",
         f"{COMMIT}:scripts/certify_bulk_arb.py"], cwd=ROOT)
    if hashlib.sha256(blob).hexdigest() != SCRIPT_SHA256_LF:
        raise AssertionError("executed script does not match recorded commit blob")
    if hashlib.sha256(script_raw.replace(b"\r\n", b"\n")).hexdigest() != SCRIPT_SHA256_LF:
        raise AssertionError("worktree script LF normalization mismatch")
    rows = []
    for line in lines:
        m = BOX.match(line)
        if m:
            rows.append((Decimal(m.group(1)), Decimal(m.group(2)), int(m.group(3))))
    if len(rows) != 3472:
        raise AssertionError(f"expected 3472 beta boxes, got {len(rows)}")
    cursor = Decimal("3.0000")
    for lo, hi, count in rows:
        width = hi - lo
        if lo != cursor or width not in (Decimal("0.0010"), Decimal("0.0005")) or count <= 0:
            raise AssertionError(f"coverage gap/overlap at {lo}")
        cursor = hi
    widths = [hi - lo for lo, hi, _ in rows]
    if widths.count(Decimal("0.0010")) != 2528 or widths.count(Decimal("0.0005")) != 944:
        raise AssertionError("adaptive width counts mismatch")
    if cursor != Decimal("6.0000") or sum(r[2] for r in rows) != 592068:
        raise AssertionError("coverage endpoint or t-box total mismatch")
    return {"beta_boxes": len(rows), "t_boxes": 592068,
            "transcript_sha256": hashlib.sha256(raw).hexdigest()}


if __name__ == "__main__":
    result = validate()
    print("surface bulk [3,6] transcript OK: "
          f"{result['beta_boxes']} beta boxes, {result['t_boxes']} t boxes, "
          f"sha256={result['transcript_sha256']}")
