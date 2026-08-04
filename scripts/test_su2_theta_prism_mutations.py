#!/usr/bin/env python3
"""Mutation self-test for theta-prism rational and syntactic guards."""

from pathlib import Path
import subprocess
import sys
import tempfile


ROOT = Path(__file__).resolve().parents[1]
CERTIFIER = ROOT / "scripts" / "certify_su2_theta_prism_rationals.py"
VALIDATOR = ROOT / "scripts" / "validate_su2_theta_prism_contract.py"


def require_failure(command: list[str], label: str) -> None:
    completed = subprocess.run(command, cwd=ROOT, capture_output=True, text=True)
    if completed.returncode == 0:
        raise RuntimeError(f"mutation unexpectedly passed: {label}")


def main() -> int:
    modes = ([sys.executable], [sys.executable, "-O"])
    for python in modes:
        mode = "-O" if "-O" in python else "normal"
        require_failure(
            [*python, str(CERTIFIER), "--singlet", "1/3"],
            f"singlet 1/2 -> 1/3 ({mode})",
        )
        require_failure(
            [*python, str(CERTIFIER), "--domain", "all beta"],
            f"domain -> all beta ({mode})",
        )

        with tempfile.TemporaryDirectory(prefix="theta-prism-mutation-") as temp:
            probe = Path(temp) / "Cheat.lean"
            for index, snippet in enumerate(
                (
                    "structure Bad where\n  cheat : witnessNormSq = 3/4\n",
                    "structure Bad where\n  renamed_field:\n    CompleteUOrthogonality\n",
                    "structure Bad where\n  another : YangMills.SU2ThetaPrism.CompleteRelativeOrthogonality\n",
                )
            ):
                probe.write_text(snippet, encoding="utf-8", newline="\n")
                require_failure(
                    [*python, str(VALIDATOR), "--probe-text", str(probe)],
                    f"headline field probe {index + 1} ({mode})",
                )

    print("PASS: 10 theta-prism mutations rejected in normal Python and -O")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
