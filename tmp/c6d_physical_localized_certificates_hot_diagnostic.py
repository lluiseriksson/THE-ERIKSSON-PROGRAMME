#!/usr/bin/env python3
"""HOT_DIAGNOSTIC_ONLY for the physical-localized C6d certificate drafts.

Run only after the cold Green-owner gate has emitted and preserved PASS.  The
script reuses that retained Colab checkout/build, fetches one exact public Git
commit, verifies every draft blob ID, promotes the six drafts in the disposable
checkout, and builds the three focal/audit pairs stop-on-first-error.

Its output can guide the next edit.  It cannot seal source, retire
PRE-VALIDATION, move 20/41, or establish window 15.
"""

from __future__ import annotations

import subprocess
import sys
import time
from pathlib import Path


SOURCE_SHA = "4d0340fb794ca0194711d0084ca5aa86a83aa2ce"

PROMOTIONS = (
    (
        "tmp/BalabanCMP99SourcePhysicalLocalizedRegionRoot.draft.lean",
        "af92e60f290c6375ea6426c6ca17a3494a2c0780",
        "YangMills/RG/BalabanCMP99SourcePhysicalLocalizedRegionRoot.lean",
    ),
    (
        "tmp/BalabanCMP99SourcePhysicalLocalizedRegionRootAudit.draft.lean",
        "aa96ee08e11a305ddea7821c6a6188ac3772fd3b",
        "YangMills/RG/BalabanCMP99SourcePhysicalLocalizedRegionRootAudit.lean",
    ),
    (
        "tmp/BalabanCMP99Eq360C6dSourceSeparatedPhysicalLocalizedPerDepthCertificate.draft.lean",
        "aa3c42fbc0e9cd21b64572fab0eddd82d3125a33",
        "YangMills/RG/BalabanCMP99Eq360C6dSourceSeparatedPhysicalLocalizedPerDepthCertificate.lean",
    ),
    (
        "tmp/BalabanCMP99Eq360C6dSourceSeparatedPhysicalLocalizedPerDepthCertificateAudit.draft.lean",
        "e8a0fb89e352eaf69116e47ffa91238015d40f5d",
        "YangMills/RG/BalabanCMP99Eq360C6dSourceSeparatedPhysicalLocalizedPerDepthCertificateAudit.lean",
    ),
    (
        "tmp/BalabanCMP99Eq360C6dSourceSeparatedPhysicalLocalizedZeroDepthCertificate.draft.lean",
        "1afaa52e838eb9204b56d7820f79db5cbc95d028",
        "YangMills/RG/BalabanCMP99Eq360C6dSourceSeparatedPhysicalLocalizedZeroDepthCertificate.lean",
    ),
    (
        "tmp/BalabanCMP99Eq360C6dSourceSeparatedPhysicalLocalizedZeroDepthCertificateAudit.draft.lean",
        "5ab7b8f2a3e874f32b3d8dcae130449f60d90ebe",
        "YangMills/RG/BalabanCMP99Eq360C6dSourceSeparatedPhysicalLocalizedZeroDepthCertificateAudit.lean",
    ),
)

TARGETS = (
    "YangMills.RG.BalabanCMP99SourcePhysicalLocalizedRegionRoot",
    "YangMills.RG.BalabanCMP99SourcePhysicalLocalizedRegionRootAudit",
    "YangMills.RG.BalabanCMP99Eq360C6dSourceSeparatedPhysicalLocalizedPerDepthCertificate",
    "YangMills.RG.BalabanCMP99Eq360C6dSourceSeparatedPhysicalLocalizedPerDepthCertificateAudit",
    "YangMills.RG.BalabanCMP99Eq360C6dSourceSeparatedPhysicalLocalizedZeroDepthCertificate",
    "YangMills.RG.BalabanCMP99Eq360C6dSourceSeparatedPhysicalLocalizedZeroDepthCertificateAudit",
)


def run(args: list[str], *, capture: bool = False) -> subprocess.CompletedProcess[bytes]:
    print(f"CMD={args!r}", flush=True)
    return subprocess.run(args, check=False, stdout=subprocess.PIPE if capture else None)


def main() -> int:
    root = Path.cwd()
    if not (root / "lakefile.toml").is_file():
        print("FINAL_STATUS=FAIL REASON=NOT_REPO_ROOT", flush=True)
        return 2

    fetched = run(["git", "fetch", "--no-tags", "origin", SOURCE_SHA])
    if fetched.returncode != 0:
        print(f"FINAL_STATUS=FAIL STAGE=fetch EXIT={fetched.returncode}", flush=True)
        return fetched.returncode

    checked_out = run(["git", "checkout", "--detach", SOURCE_SHA])
    if checked_out.returncode != 0:
        print(
            f"FINAL_STATUS=FAIL STAGE=checkout EXIT={checked_out.returncode}",
            flush=True,
        )
        return checked_out.returncode
    head = run(["git", "rev-parse", "HEAD"], capture=True)
    if head.returncode != 0 or head.stdout.decode().strip() != SOURCE_SHA:
        print("FINAL_STATUS=FAIL STAGE=head_gate", flush=True)
        return 4

    for source, expected_blob, destination in PROMOTIONS:
        actual = run(["git", "rev-parse", f"{SOURCE_SHA}:{source}"], capture=True)
        if actual.returncode != 0:
            print(f"FINAL_STATUS=FAIL STAGE=blob_lookup PATH={source}", flush=True)
            return actual.returncode
        actual_blob = actual.stdout.decode().strip()
        if actual_blob != expected_blob:
            print(
                "FINAL_STATUS=FAIL STAGE=blob_gate "
                f"PATH={source} EXPECTED={expected_blob} ACTUAL={actual_blob}",
                flush=True,
            )
            return 3
        content = run(["git", "show", f"{SOURCE_SHA}:{source}"], capture=True)
        if content.returncode != 0:
            print(f"FINAL_STATUS=FAIL STAGE=git_show PATH={source}", flush=True)
            return content.returncode
        out = root / destination
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_bytes(content.stdout)
        print(f"PROMOTED={source} DEST={destination} BLOB={actual_blob}", flush=True)

    for index, target in enumerate(TARGETS, start=1):
        stage = f"{index:02d}_{target.rsplit('.', 1)[-1]}"
        start = time.perf_counter()
        result = run(["lake", "build", target])
        seconds = time.perf_counter() - start
        print(f"STAGE={stage} EXIT={result.returncode} SECONDS={seconds:.3f}", flush=True)
        if result.returncode != 0:
            print(f"FINAL_STATUS=FAIL STAGE={stage}", flush=True)
            return result.returncode

    print("FINAL_STATUS=PASS MODE=HOT_DIAGNOSTIC_ONLY", flush=True)
    return 0


if __name__ == "__main__":
    sys.exit(main())
