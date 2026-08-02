"""Certify the chronology of the pre-registration that the clean anchor cannot.

WHY THIS IS NEEDED, and it is a wound this campaign gave itself.  The paper's
source anchor is a CURATED REPLAY built from the campaign base, so that it would
carry this paper's changes and nothing from a concurrent lane sharing the same
clone.  The replay works: the tree is clean.  But it cost the property that made
the pre-registration checkable by inspection --- the judge commits are no longer
ANCESTORS of the anchor, so a reader looking only at the clean branch sees the
judges and the Lean appear together in one commit.

The claim "these judges were committed before the Lean existed" is historically
true and the original commits carry the dates.  What this script adds is the
missing half: that the judge files IN THE CLEAN ANCHOR are byte-identical to the
blobs that were pre-registered.  Chronology is then certified by the original
commits PLUS blob identity, not by ancestry --- and that is exactly how the
paper states it, rather than letting the replay imply an ancestry it lacks.

    python scripts/verify_prereg_blobs.py [<anchor-rev>]

Exit 1 on any mismatch, in normal and `-O` modes alike.  No acceptance decision
depends on `assert`.
"""
import os
import subprocess
import sys

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

# (pre-registration commit, path, what it licenses)
PREREG = [
    ("2392c080", "scripts/judge_site_bridge.py",
     "the site bridge: S1 the assembly bijection, S2 the weight identity"),
    ("47d48fc2", "scripts/judge_os_reconstruction.py",
     "the reconstruction: R1 rank, R2 self-adjointness, R3 the defining "
     "equation, R4 the spectrum"),
]


def blob(rev, path):
    r = subprocess.run(["git", "rev-parse", "%s:%s" % (rev, path)], cwd=REPO,
                       capture_output=True, text=True)
    return r.stdout.strip() if r.returncode == 0 else None


def is_ancestor(a, b):
    r = subprocess.run(["git", "merge-base", "--is-ancestor", a, b], cwd=REPO,
                       capture_output=True)
    return r.returncode == 0


def main():
    anchor = sys.argv[1] if len(sys.argv) > 1 else "HEAD"
    checks = []
    print("anchor: %s" % blob(anchor, "") or anchor)
    for commit, path, licenses in PREREG:
        a = blob(commit, path)
        b = blob(anchor, path)
        checks.append(("pre-registration commit %s exists" % commit,
                       a is not None))
        checks.append(("file present in the anchor: %s" % path,
                       b is not None))
        checks.append(("blob identical to the pre-registered one: %s" % path,
                       a is not None and a == b))
        print("  %-38s prereg=%s" % (os.path.basename(path), a))
        print("  %-38s anchor=%s  %s" % ("", b,
                                         "IDENTICAL" if a == b else "DIFFER"))
        print("  licenses: %s" % licenses)
        # Reported, deliberately NOT required: the whole point is that the
        # clean anchor is a replay and does not descend from these commits.
        print("  ancestor of the anchor: %s (expected NO for a replay)"
              % ("YES" if is_ancestor(commit, anchor) else "NO"))

    ran = 0
    bad = []
    for name, ok in checks:
        ran += 1
        if not ok:
            bad.append(name)
    if ran != len(checks):
        print("check counter disagrees: %d of %d" % (ran, len(checks)))
        return 2
    print()
    print("checks run: %d" % ran)
    if bad:
        for name in bad:
            print("FAILED:", name)
        return 1
    print("chronology certified by ORIGINAL COMMITS PLUS BLOB IDENTITY, "
          "not by ancestry of the clean anchor")
    return 0


if __name__ == "__main__":
    sys.exit(main())
