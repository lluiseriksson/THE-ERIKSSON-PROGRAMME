#!/usr/bin/env python3
"""Fail-closed promotion of the remaining C6d fixed-depth action prefix.

The finite brick contains the generic and literal C6d pairs for the left
derivative, covariant Laplacian and right-adjoint derivative.  It performs
text transport only, never runs Lean and never removes PRE-VALIDATION.  The
exact block-localized Green value and physical background must already be
sealed in the selected source commit.
"""

from __future__ import annotations

import importlib.util
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / "tmp" / "promote_c6d_green_owner_prefix.py"
SOURCES = (
    "tmp/BalabanCMP99Eq342LeftDerivativeFromValueBound.draft.lean",
    "tmp/BalabanCMP99Eq342LeftDerivativeFromValueBoundAudit.draft.lean",
    "tmp/BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenLeftDerivative.draft.lean",
    "tmp/BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenLeftDerivativeAudit.draft.lean",
    "tmp/BalabanCMP99Eq342LaplacianFromLeftDerivativeBound.draft.lean",
    "tmp/BalabanCMP99Eq342LaplacianFromLeftDerivativeBoundAudit.draft.lean",
    "tmp/BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenLaplacian.draft.lean",
    "tmp/BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenLaplacianAudit.draft.lean",
    "tmp/BalabanCMP99Eq342RightAdjointFromValueBound.draft.lean",
    "tmp/BalabanCMP99Eq342RightAdjointFromValueBoundAudit.draft.lean",
    "tmp/BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenRightAdjoint.draft.lean",
    "tmp/BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenRightAdjointAudit.draft.lean",
)
PREREQUISITES = (
    "YangMills/RG/BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenBlockLocalizedOwnerDecay.lean",
    "YangMills/RG/BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenBlockLocalizedOwnerDecayAudit.lean",
    "YangMills/RG/BalabanCMP99Eq360C6dSourceSeparatedPhysicalBackground.lean",
    "YangMills/RG/BalabanCMP99Eq360C6dSourceSeparatedPhysicalBackgroundAudit.lean",
)
AUDIT_IMPORTS = (
    "import YangMills.RG.BalabanCMP99Eq342LeftDerivativeFromValueBoundAudit",
    "import YangMills.RG.BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenLeftDerivativeAudit",
    "import YangMills.RG.BalabanCMP99Eq342LaplacianFromLeftDerivativeBoundAudit",
    "import YangMills.RG.BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenLaplacianAudit",
    "import YangMills.RG.BalabanCMP99Eq342RightAdjointFromValueBoundAudit",
    "import YangMills.RG.BalabanCMP99Eq360C6dSourceSeparatedAmbientGreenRightAdjointAudit",
)


def main() -> int:
    spec = importlib.util.spec_from_file_location("c6d_four_action_prefix_base", BASE)
    if spec is None or spec.loader is None:
        raise RuntimeError("C6D_FOUR_ACTION_PREFIX_PROMOTER_BASE_IMPORT_FAILED")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    module.SOURCES = SOURCES
    module.PREREQUISITES = PREREQUISITES
    module.AUDIT_IMPORTS = AUDIT_IMPORTS
    module.PROMOTION_SENTINEL = "C6D_FOUR_ACTION_PREFIX"
    return module.main()


if __name__ == "__main__":
    raise SystemExit(main())
