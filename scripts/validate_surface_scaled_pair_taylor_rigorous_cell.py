"""Validate the frozen local pair-Taylor candidate transcripts."""

from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
PROD = ROOT / "outputs/surface-scaled-pair-taylor-rigorous-cell-20260721.production.txt"
REPLAY = ROOT / "outputs/surface-scaled-pair-taylor-rigorous-cell-20260721.replay.txt"
STRESS_PROD = ROOT / "outputs/surface-scaled-pair-taylor-rigorous-stress-20260721.production.txt"
STRESS_REPLAY = ROOT / "outputs/surface-scaled-pair-taylor-rigorous-stress-20260721.replay.txt"


def main():
    a = PROD.read_bytes()
    b = REPLAY.read_bytes()
    assert a == b, "production/replay transcript mismatch"
    text = a.decode("utf-8")
    assert "NEGATIVE True" in text
    assert "NO G2/G6 PROMOTION" in text
    assert "ENCLOSURE [-1.3684535880997e-79 +/- 4.37e-93]" in text
    stress = STRESS_PROD.read_bytes()
    assert stress == STRESS_REPLAY.read_bytes(), "stress replay mismatch"
    stress_text = stress.decode("utf-8")
    assert "NEGATIVE True" in stress_text
    assert "ENCLOSURE [-1.13912636450264370488479847567e-63 +/- 6.91e-93]" in stress_text
    print("RIGOROUS PAIR-TAYLOR LOCAL TRANSCRIPT VALID")
    print("BYTE_IDENTICAL", len(a), "bytes")
    print("STRESS_BYTE_IDENTICAL", len(stress), "bytes")
    print("CANDIDATE_ONLY")


if __name__ == "__main__":
    main()
