"""Validate the historical plain-Arb bulk certificate on beta in [3,6]."""

from __future__ import annotations

from decimal import Decimal
import hashlib
from pathlib import Path
import re
import subprocess


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "certify_bulk_arb.py"
TRANSCRIPT = ROOT / "scripts" / "certify_bulk_arb_transcript.txt"
SOURCE_COMMIT = "31663045ec3482f81b3577cbf491d706c7668de1"
SCRIPT_SHA256 = (
    "3422ea0b603ebcf0af721586e51b7c268d3959545b81e4cc86dbd2cfb611c60a"
)
SCRIPT_LF_SHA256 = (
    "370ae701548344aa173603774b8c9fb260eb085bc352032418f28c089ac6efa8"
)
TRANSCRIPT_SHA256 = (
    "5b7d1ef34a2dfd01a56acfa89255672702c23f238288740f726f42b9b65d76d7"
)
TRANSCRIPT_LF_SHA256 = (
    "71e8256876cd6b86c3b239727f4162d075c981fc73132ed3e22962b295d951e5"
)
ROW = re.compile(
    r"^beta-box \[([0-9.]+), ([0-9.]+)\]: ([0-9]+) t-boxes$"
)
TERMINAL = (
    "CERTIFIED (plain, Arb): W < 0 on "
    "[0.6, pi-1.5/beta] x [3, 6]; 592068 t-boxes total"
)


def _blob(relative: str) -> bytes:
    return subprocess.check_output(
        [
            "git",
            "-c",
            f"safe.directory={ROOT.as_posix()}",
            "show",
            f"{SOURCE_COMMIT}:{relative}",
        ],
        cwd=ROOT,
    )


def validate() -> dict[str, object]:
    script_bytes = SCRIPT.read_bytes()
    transcript_bytes = TRANSCRIPT.read_bytes()
    assert hashlib.sha256(script_bytes).hexdigest() == SCRIPT_SHA256
    assert hashlib.sha256(transcript_bytes).hexdigest() == TRANSCRIPT_SHA256
    assert hashlib.sha256(script_bytes.replace(b"\r\n", b"\n")).hexdigest() == (
        SCRIPT_LF_SHA256
    )
    assert hashlib.sha256(
        transcript_bytes.replace(b"\r\n", b"\n")
    ).hexdigest() == TRANSCRIPT_LF_SHA256
    assert hashlib.sha256(_blob("scripts/certify_bulk_arb.py")).hexdigest() == (
        SCRIPT_LF_SHA256
    )
    assert hashlib.sha256(
        _blob("scripts/certify_bulk_arb_transcript.txt")
    ).hexdigest() == TRANSCRIPT_LF_SHA256

    lines = transcript_bytes.decode("utf-8").splitlines()
    assert lines and lines[-1] == TERMINAL
    rows = []
    for line in lines:
        match = ROW.match(line)
        if match:
            rows.append(
                (
                    Decimal(match.group(1)),
                    Decimal(match.group(2)),
                    int(match.group(3)),
                )
            )
    assert len(rows) == 3472
    cursor = Decimal("3")
    for lo, hi, count in rows:
        assert lo == cursor and hi > lo and count > 0
        cursor = hi
    assert cursor == Decimal("6")
    assert sum(count for _, _, count in rows) == 592_068
    return {
        "beta_boxes": len(rows),
        "t_boxes": 592_068,
        "transcript_sha256": TRANSCRIPT_SHA256,
    }


def main() -> int:
    result = validate()
    print(
        "PLAIN BULK [3,6] TRANSCRIPT PASS:",
        result["beta_boxes"],
        "beta boxes;",
        result["t_boxes"],
        "strict t boxes",
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
