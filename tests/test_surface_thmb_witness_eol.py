from pathlib import Path

from scripts.audit_surface_thmb_witnesses import read_text, sha256_lf


def test_thmb_source_hash_and_transcript_are_eol_stable(tmp_path: Path) -> None:
    lf = tmp_path / "lf.txt"
    crlf = tmp_path / "crlf.txt"
    lf.write_bytes(b"source_sha256 value\npass 1 CERTIFIED Crit < 0\n")
    crlf.write_bytes(b"source_sha256 value\r\npass 1 CERTIFIED Crit < 0\r\n")
    assert read_text(lf) == read_text(crlf)
    assert sha256_lf(lf) == sha256_lf(crlf)
