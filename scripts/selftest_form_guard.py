"""Adversarial self-test of the submission-form guard, in BOTH python modes.

Written after the guard's first test silently tested nothing: the injection used
`.replace(target, ..., 1)` and never checked that the replacement had happened,
so the "adversarial" run fed the guard a clean file and reported PASS.  A test
that does not verify it changed the input is not a test.

    python scripts/selftest_form_guard.py

Exit 0 only if the guard REFUSES the poisoned input in normal mode AND under
`-O`, and accepts the clean input in both.  Exit 2 if the injection itself
fails, which is the failure mode that hid here.
"""
import io
import os
import shutil
import subprocess
import sys

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
TEX = os.path.join(REPO, "papers", "spatial-reflection", "spatial_reflection.tex")
SRC = os.path.join(REPO, "scripts", "form_from_tex.py")
PHRASE = "weight that destroys uniformity leaves positivity"
ANCHOR = "\\begin{abstract}"


def run(flags):
    r = subprocess.run([sys.executable] + flags + [SRC],
                       capture_output=True, text=True, cwd=REPO)
    return r.returncode


def main() -> int:
    checks = 0
    bad = []

    clean = io.open(TEX, encoding="utf-8", newline="").read()
    if ANCHOR not in clean:
        print("INJECTION IMPOSSIBLE: %r not found in %s" % (ANCHOR, TEX))
        return 2

    bak = TEX + ".selftest.bak"
    shutil.copyfile(TEX, bak)
    try:
        # ---- the clean file must be accepted, in both modes
        for flags, name in (([], "normal"), (["-O"], "-O")):
            checks += 1
            code = run(flags)
            print("clean    %-7s exit=%d" % (name, code))
            if code != 0:
                bad.append("clean input rejected in " + name)

        # ---- poison, and VERIFY the poison landed before believing the result
        poisoned = clean.replace(
            ANCHOR, ANCHOR + "\nThe same " + PHRASE + " exactly where it was.\n", 1)
        if poisoned == clean:
            print("INJECTION DID NOTHING -- the test would have tested nothing")
            return 2
        io.open(TEX, "w", encoding="utf-8", newline="").write(poisoned)
        readback = io.open(TEX, encoding="utf-8", newline="").read()
        if PHRASE not in readback:
            print("INJECTION DID NOT REACH DISK")
            return 2
        print("injection verified on disk")

        for flags, name in (([], "normal"), (["-O"], "-O")):
            checks += 1
            code = run(flags)
            print("poisoned %-7s exit=%d" % (name, code))
            if code == 0:
                bad.append("guard did NOT fire in " + name)
    finally:
        shutil.copyfile(bak, TEX)
        os.remove(bak)
        run([])                       # regenerate the form from the clean tex

    if checks != 4:
        print("check counter disagrees:", checks)
        return 2
    if bad:
        for b in bad:
            print("FAILED:", b)
        return 1
    print("checks run: %d, all passed -- guard fires in both modes" % checks)
    return 0


if __name__ == "__main__":
    sys.exit(main())
