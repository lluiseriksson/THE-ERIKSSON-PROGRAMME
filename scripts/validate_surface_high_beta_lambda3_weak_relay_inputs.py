"""Validate the tighter lambda-three consequences for the weak-main relay.

This parser is deliberately independent of python-flint.  It validates the
immutable production/replay bytes, recorded dependency hashes, and outward
decimal endpoints before comparing them with the new rational thresholds.
"""

from __future__ import annotations

from decimal import Decimal, getcontext
import hashlib
from pathlib import Path
import platform
import re
import subprocess

from surface_eol_hashes import sha256_variants


ROOT = Path(__file__).resolve().parents[1]
PRODUCTION = (
    ROOT/"scripts"/
    "surface_high_beta_lambda3_joint_production_20260728.txt"
)
REPLAY = (
    ROOT/"scripts"/
    "surface_high_beta_lambda3_joint_replay_20260728.txt"
)
EXPECTED_SHA256 = (
    "a2e9f9b7db49ddc3b6186552ef33c0b7bb6d15cc2a64929137e3f3032bc8f4c9"
)
RHO_THRESHOLD = Decimal(7)/Decimal(200)
ADVERSE_THRESHOLD = Decimal(43)/Decimal(50)
INTERVAL = re.compile(
    r"^\[([+-]?[0-9]+(?:\.[0-9]+)?(?:e[+-]?[0-9]+)?) "
    r"\+/- ([0-9]+(?:\.[0-9]+)?(?:e[+-]?[0-9]+)?)\]$",
    re.IGNORECASE,
)


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def dependency_hash_matches(path: Path, expected: str) -> bool:
    """Accept only byte-identical content modulo LF/CRLF representation."""

    return expected.lower() in sha256_variants(path)


def transcript_hash_matches(path: Path, expected: str) -> bool:
    """Bind an immutable transcript modulo Git's LF/CRLF representation."""

    return expected.lower() in sha256_variants(path)


def upper_endpoint(text: str) -> Decimal:
    match = INTERVAL.fullmatch(text)
    if match is None:
        raise AssertionError(f"unrecognized Arb interval: {text!r}")
    return Decimal(match.group(1))+Decimal(match.group(2))


def validate() -> dict[str, object]:
    getcontext().prec = 100
    production = PRODUCTION.read_bytes()
    replay = REPLAY.read_bytes()
    if production != replay:
        raise AssertionError("lambda-three production/replay byte mismatch")
    digest = hashlib.sha256(production).hexdigest()
    if not transcript_hash_matches(PRODUCTION, EXPECTED_SHA256):
        raise AssertionError(f"unexpected lambda-three digest: {digest}")
    lines = production.decode("utf-8").splitlines()
    recorded = {
        pieces[1]: pieces[2]
        for line in lines
        if line.startswith("DEPENDENCY ")
        for pieces in (line.split(),)
    }
    if not recorded:
        raise AssertionError("missing dependency ledger")
    for relative, expected in recorded.items():
        path = ROOT/relative
        if not dependency_hash_matches(path, expected):
            actual = sha256(path)
            raise AssertionError(
                f"dependency drift {relative}: {actual} != {expected}"
            )
    rho_line = next(line for line in lines if line.startswith("rho "))
    adverse_line = next(
        line for line in lines
        if line.startswith("joint_adverse_upper ")
    )
    rho_text = rho_line[len("rho "):].split(" worst ", 1)[0]
    adverse_text = (
        adverse_line[len("joint_adverse_upper "):]
        .split(" worst ", 1)[0]
    )
    rho_upper = upper_endpoint(rho_text)
    adverse_upper = upper_endpoint(adverse_text)
    if not rho_upper < RHO_THRESHOLD:
        raise AssertionError((rho_upper, RHO_THRESHOLD))
    if not adverse_upper < ADVERSE_THRESHOLD:
        raise AssertionError((adverse_upper, ADVERSE_THRESHOLD))
    return {
        "transcript_sha256": EXPECTED_SHA256,
        "checkout_sha256": digest,
        "dependency_count": len(recorded),
        "rho_upper": rho_upper,
        "adverse_upper": adverse_upper,
    }


def main() -> int:
    result = validate()
    print("LAMBDA3 WEAK-RELAY INPUT VALIDATION PASS")
    print(
        "git_head",
        subprocess.check_output(
            ["git", "-c", "safe.directory=*", "rev-parse", "HEAD"],
            cwd=ROOT,
            text=True,
        ).strip(),
    )
    print("python", platform.python_version())
    print("script_sha256", sha256(Path(__file__).resolve()).upper())
    print("transcript_sha256", result["transcript_sha256"])
    print("dependency_count", result["dependency_count"])
    print("rho_upper", result["rho_upper"], "< 7/200")
    print("adverse_upper", result["adverse_upper"], "< 43/50")
    print(
        "SCOPE immutable lambda-three inputs only; "
        "X_main >= -1/20 remains open"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
