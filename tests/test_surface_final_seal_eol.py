from pathlib import Path

from scripts.audit_surface_final_seal import canonical_text_sha256


def test_canonical_text_hash_is_eol_stable(tmp_path: Path) -> None:
    lf = tmp_path / "lf.tex"
    crlf = tmp_path / "crlf.tex"
    lf.write_bytes(b"alpha\nbeta\n")
    crlf.write_bytes(b"alpha\r\nbeta\r\n")
    assert canonical_text_sha256(lf) == canonical_text_sha256(crlf)
