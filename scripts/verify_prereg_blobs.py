"""Certify the chronology of the pre-registration that the clean anchor cannot.

WHY THIS IS NEEDED, and it is a wound this campaign gave itself.  The paper's
source anchor is a CURATED REPLAY built from the campaign base, so that it would
carry this paper's changes and nothing from a concurrent lane sharing the same
clone.  The replay works: the tree is clean.  But it cost the property that made
the pre-registration checkable by inspection --- the judge commits are no longer
ANCESTORS of the anchor, so a reader looking only at the clean branch sees the
judges and the Lean appear together in one commit.

WHAT AN EARLIER VERSION OF THIS FILE DID NOT DO, all four found by an external
reading and all four now checks rather than prose:

  * it omitted `6e67629a`, the commit that registered the v2 job prediction,
    although the manuscript names it alongside the two judges;
  * it PRINTED the absent ancestry instead of requiring it, so a later
    reconstruction that restored ancestry would still have exited zero while
    the paper went on claiming a replay;
  * it proved blob identity and stopped, which shows the replay's judge IS the
    pre-registered judge but says nothing about the judge preceding the Lean it
    licenses.  That is now checked on the ORIGINAL history: each gate commit is
    an ancestor of the v1.0 published anchor, and the target it licenses did not
    yet exist at the gate commit;
  * its banner called `blob(anchor, "")`, which asks for `rev:` with an empty
    path and, by operator precedence, could not be rescued by the trailing
    `or`.  There is a separate `revision()` helper now.

The certified chain is therefore:

    original commit is earlier  +  its target was still absent there
                                +  the blob in the replay is identical

Exit 1 on any failure, in normal and `-O` modes alike.  No acceptance decision
depends on `assert`.

    python scripts/verify_prereg_blobs.py [<anchor-rev>]
"""
import os
import subprocess
import sys

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

# The anchor the ORIGINAL campaign published; the gates must precede it.
V1_ANCHOR = "c90dc745"

# (commit, path, target-that-must-still-be-absent, what it licenses)
GATES = [
    ("2392c080", "scripts/judge_site_bridge.py",
     ("YangMills/OS/SpatialOS.lean", "sum_pathsAt_eq"),
     "the site bridge: S1 the assembly bijection, S2 the weight identity"),
    ("47d48fc2", "scripts/judge_os_reconstruction.py",
     ("YangMills/OS/SpatialReconstruction.lean", None),
     "the reconstruction: R1 rank, R2 self-adjointness, R3 the defining "
     "equation, R4 the spectrum"),
]

# The prediction registered in a commit MESSAGE rather than in a file.
PREDICTION_COMMIT = "6e67629a"
PREDICTION_TOKENS = ["8469", "delta exactly 0"]

NON_ANCESTORS = ["2392c080", "47d48fc2", "6e67629a"]


def revision(rev):
    """The full SHA of a revision, or None."""
    r = subprocess.run(["git", "rev-parse", rev], cwd=REPO,
                       capture_output=True, text=True)
    return r.stdout.strip() if r.returncode == 0 else None


def blob(rev, path):
    r = subprocess.run(["git", "rev-parse", "%s:%s" % (rev, path)], cwd=REPO,
                       capture_output=True, text=True)
    return r.stdout.strip() if r.returncode == 0 else None


def file_exists(rev, path):
    r = subprocess.run(["git", "cat-file", "-e", "%s:%s" % (rev, path)],
                       cwd=REPO, capture_output=True)
    return r.returncode == 0


def file_text(rev, path):
    r = subprocess.run(["git", "show", "%s:%s" % (rev, path)], cwd=REPO,
                       capture_output=True)
    return r.stdout.decode("utf-8", "replace") if r.returncode == 0 else None


def message(rev):
    r = subprocess.run(["git", "log", "-1", "--format=%B", rev], cwd=REPO,
                       capture_output=True, text=True)
    return r.stdout if r.returncode == 0 else ""


def is_ancestor(a, b):
    r = subprocess.run(["git", "merge-base", "--is-ancestor", a, b], cwd=REPO,
                       capture_output=True)
    return r.returncode == 0


def main():
    anchor = sys.argv[1] if len(sys.argv) > 1 else "HEAD"
    full = revision(anchor)
    print("anchor    : %s" % (full or "UNRESOLVED"))
    print("v1 anchor : %s" % (revision(V1_ANCHOR) or "UNRESOLVED"))
    checks = [("anchor revision resolves", full is not None)]

    for commit, path, (target_path, target_name), licenses in GATES:
        a = blob(commit, path)
        b = blob(anchor, path)
        print()
        print("  gate %s -- %s" % (commit, os.path.basename(path)))
        print("    licenses            : %s" % licenses)
        print("    blob at the gate    : %s" % a)
        print("    blob at the anchor  : %s   %s"
              % (b, "IDENTICAL" if (a and a == b) else "DIFFER"))
        checks.append(("gate commit resolves: %s" % commit,
                       revision(commit) is not None))
        checks.append(("blob identical to the pre-registered one: %s" % path,
                       a is not None and a == b))

        # chronology, on the ORIGINAL history
        anc = is_ancestor(commit, V1_ANCHOR)
        print("    precedes the v1.0 anchor on the original history: %s"
              % ("YES" if anc else "NO"))
        checks.append(("gate %s precedes the v1.0 published anchor" % commit,
                       anc))

        if target_name is None:
            absent = not file_exists(commit, target_path)
            print("    target module absent at the gate commit          : %s"
                  % ("YES" if absent else "NO"))
            checks.append(("target module %s absent at %s"
                           % (target_path, commit), absent))
        else:
            text = file_text(commit, target_path) or ""
            absent = target_name not in text
            print("    target `%s` absent at the gate commit: %s"
                  % (target_name, "YES" if absent else "NO"))
            checks.append(("target %s absent at %s" % (target_name, commit),
                           absent))

    # the prediction registered in a commit message
    msg = message(PREDICTION_COMMIT)
    print()
    print("  prediction commit %s" % PREDICTION_COMMIT)
    for tok in PREDICTION_TOKENS:
        present = tok in msg
        print("    registers %-18r : %s" % (tok, "YES" if present else "NO"))
        checks.append(("commit %s registers %r" % (PREDICTION_COMMIT, tok),
                       present))

    # the replay property itself, REQUIRED and not merely printed
    print()
    for commit in NON_ANCESTORS:
        anc = is_ancestor(commit, anchor)
        print("  %s ancestor of the replay anchor: %s (must be NO)"
              % (commit, "YES" if anc else "NO"))
        checks.append(("%s is deliberately NOT an ancestor of the replay anchor"
                       % commit, not anc))

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
    print("chronology certified: each gate is EARLIER on the original history,")
    print("its target was still ABSENT there, and its blob in the replay is")
    print("IDENTICAL -- ancestry of the clean anchor is required to be absent.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
