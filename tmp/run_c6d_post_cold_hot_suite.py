#!/usr/bin/env python3
"""Run the retained-runtime C6d diagnostics once, in dependency order.

Every child runner is fetched from an exact Git object and checked by SHA-256.
Any transport mismatch or child exception stops the suite immediately. This
is hot diagnostic evidence only and cannot retire PRE-VALIDATION.
"""

from __future__ import annotations

import hashlib
from pathlib import Path
import urllib.request


RUNNERS = [
    (
        "uniform_certificate_from_value",
        "83346b6cc4bb18c7ba2802a2aa23ed1a6562df81",
        "tmp/run_c6d_uniform_certificate_from_value_hot.py",
        "52716291c88367cfe6604ad9e454418dee3664648375aff36fa61fbb1eb565b8",
    ),
    (
        "neumann_precision",
        "fc1461517467cb8a13dabc95931c9d35803467d4",
        "tmp/run_c6d_cmp89_neumann_precision_hot.py",
        "7e03743155837fcbfc9bd1ce98f432fbeb192e8225e240294c38046864c1a19e",
    ),
    (
        "reflection_branch",
        "3a40b6819a32aa940eaf6e1e316aac765d596b55",
        "tmp/run_c6d_cmp89_reflection_branch_hot.py",
        "ee476352a1773520f6bc911173223479b63543435b39c3ce1e153a87391c2c8e",
    ),
    (
        "neumann_dirichlet_boundary_nogo",
        "cb59fbafef375daaea125aac29a1afba6f7196b8",
        "tmp/run_c6d_cmp89_neumann_dirichlet_nogo_hot.py",
        "163949334d4153df9761c33af6b9f1b67d3f542e4eb5b5ffb148e036361782d6",
    ),
    (
        "reflection_orbit",
        "b5d73d094c3cf69f1effd3e1a65fe10f60818808",
        "tmp/run_c6d_cmp89_reflection_orbit_hot.py",
        "e664e0032f2376f02397f16bec9ecf340f59ba1c8e52aca2012d54798e0a9d29",
    ),
    (
        "reflection_scale",
        "8323dc229d7b2c8169b85a0b134844fb1e3d0025",
        "tmp/run_c6d_cmp89_reflection_scale_hot.py",
        "8a05126a7a32f8813eaf83323611483afb7af522aec6ee28a5e1ec961bcdb5c7",
    ),
    (
        "reflection_representation",
        "8323dc229d7b2c8169b85a0b134844fb1e3d0025",
        "tmp/run_c6d_cmp89_reflection_representation_hot.py",
        "f4f5e577a13ffd3dfe6ae2a024429455509a9151c89e6671fe50f7e82e73af49",
    ),
    (
        "reflection_residue",
        "3ece7761e8c52afd0265f9374fa2feecfa00cdee",
        "tmp/run_c6d_cmp89_reflection_residue_hot.py",
        "99f22c996c8a0ae7707ca8de3e696ae1fbc21456ccb398a38322caa4d9e8bdab",
    ),
]

HOT_ROOT = Path("/content/hrpoly-c6d-green-owner-prefix")
LEGACY_CHILD_ROOT = HOT_ROOT / "repo"


def ensure_child_root() -> None:
    """Expose the cold checkout at the path pinned by the child runners."""
    if not HOT_ROOT.is_dir():
        raise RuntimeError(f"HOT_REPO_MISSING={HOT_ROOT}")
    if not LEGACY_CHILD_ROOT.exists():
        LEGACY_CHILD_ROOT.symlink_to(HOT_ROOT, target_is_directory=True)
    if LEGACY_CHILD_ROOT.resolve() != HOT_ROOT.resolve():
        raise RuntimeError(
            f"HOT_REPO_ALIAS_MISMATCH={LEGACY_CHILD_ROOT.resolve()}"
        )


def main() -> None:
    ensure_child_root()
    for index, (name, commit, path, expected) in enumerate(RUNNERS, start=1):
        url = (
            "https://raw.githubusercontent.com/lluiseriksson/"
            f"THE-ERIKSSON-PROGRAMME/{commit}/{path}"
        )
        print(
            f"HOT_SUITE_STAGE={index:02d}_{name} TRANSPORT={url}",
            flush=True,
        )
        with urllib.request.urlopen(url) as response:
            payload = response.read()
        actual = hashlib.sha256(payload).hexdigest()
        print(
            f"HOT_SUITE_STAGE={index:02d}_{name} SHA256={actual}",
            flush=True,
        )
        if actual != expected:
            raise RuntimeError(f"HOT_SUITE_RUNNER_HASH_MISMATCH={name}")
        namespace = {"__name__": "__main__", "__file__": url}
        exec(compile(payload, url, "exec"), namespace)
        print(f"HOT_SUITE_STAGE={index:02d}_{name} PASS", flush=True)
    print("HOT_C6D_POST_COLD_DIAGNOSTIC_SUITE_PASS", flush=True)


if __name__ == "__main__":
    main()
