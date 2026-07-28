"""Audit the adjacent K4 t-box candidate chain [3,3.07].

This is a topology/provenance audit only.  It deliberately cannot promote
K4, S1'''/S2''', or G6: the regular endpoint, global t union, overlap, and
weighted union obligations remain separate.
"""

from fractions import Fraction
import hashlib
import json
from pathlib import Path

from flint import arb, ctx
from run_record_archive import frozen_record_path


ROOT = Path(__file__).resolve().parents[1]
PREFIX = "surface-remainder-k4-tbox-delta0040-t"
UNITS = ("300-301", "301-302", "302-303", "303-304", "304-305", "305-306", "306-307", "307-308")
NAMES = (
    "muF_main", "nuD_main", "nuF_main", "MD_mirror",
    "MF_mirror", "MD2r_mirror", "MDFr_mirror",
)


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest().upper()


def parse_fraction(value: str) -> Fraction:
    return Fraction(value)


def main() -> int:
    ctx.prec = 140
    records = []
    for unit in UNITS:
        manifest = frozen_record_path(f"{PREFIX}{unit}-20260723.json")
        data = json.loads(manifest.read_text(encoding="utf-8"))
        assert data["status"] == "K4_T_BOX_CERTIFIED_CANDIDATE"
        assert data["promotion"] == "NONE"
        assert data["cells"] == 2304
        assert "no K4/S1'''/S2'''/G6 promotion" in data["scope"]
        dlo, dhi = map(parse_fraction, data["domain"]["delta"])
        tlo, thi = map(parse_fraction, data["domain"]["t"])
        assert (dlo, dhi) == (Fraction(1, 25), Fraction(81, 2000))
        transcript = ROOT / data["transcript"]
        replay = ROOT / data["replay"]
        assert transcript.read_bytes() == replay.read_bytes()
        actual = digest(transcript)
        assert actual == data["transcript_sha256"] == data["replay_sha256"]
        fractions = {name: arb(data["fractions"][name]) for name in NAMES}
        assert all(value.upper() < 1 for value in fractions.values())
        records.append((tlo, thi, data))
    records.sort()
    for (_, previous_hi, _), (current_lo, _, _) in zip(records, records[1:]):
        assert previous_hi == current_lo, (previous_hi, current_lo)
    assert records[0][0] == Fraction(3)
    assert records[-1][1] == Fraction(77, 25)
    print("K4 T-BOX CHAIN AUDIT PASS")
    print("UNITS", len(records), "CELLS", len(records) * 2304)
    print("T_DOMAIN", records[0][0], records[-1][1])
    print("PRODUCTION/REPLAY BYTE EQUALITY PASS")
    print("CANDIDATE ONLY; NO K4/S1'''/S2'''/G6 PROMOTION")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
