"""Reject the optional H_cube refinement from the terminal surface paper."""

from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
PAPER = ROOT/"papers"/"surface-complete"/"surface_theorem_complete.tex"


def audit():
    text = PAPER.read_text(encoding="utf-8")
    forbidden = ("H_{\\rm cube}", "M_{\\rm sharp}",
                 "sharpened mirror bound, conditional")
    assert all(token not in text for token in forbidden)
    # The unconditional bound that carries the actual theorem load remains.
    assert "$M$ is unconditional, as is" in text
    assert "Corollary~\\ref{cor:regIIInum}" in text
    assert "H_{\\rm tail}" in text
    # H_tail survives only as a labelled historical conditional result.  The
    # terminal theorem must not cite that lemma in any direction.
    assert (
        r"\begin{lemma}[conditional historical saddle extraction; not used in"
        in text
    )
    assert r"\ref{lem:extraction}" not in text
    assert r"\eqref{lem:extraction}" not in text
    assert r"\autoref{lem:extraction}" not in text
    return True


if __name__ == "__main__":
    audit()
    print("OPTIONAL H_CUBE REMOVAL AUDIT PASS; UNCONDITIONAL M RETAINED")
