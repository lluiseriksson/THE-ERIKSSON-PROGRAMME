/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceFlatGeneratedTerminalComplexFieldData
import YangMills.RG.BalabanCMP99SourceFlatAmbientLaplacian
import YangMills.RG.BalabanCMP99SourceFlatPhysicalTransport

/-!
# Flat generated-background dictionary

The source-recursion background and the ambient-Laplacian background are
independently named physical gauge configurations.  This module proves their
literal equality at the unit field instead of identifying them silently by
notation.

No stencil transport, spacing normalization, precision action, inverse or
Green operator is asserted here.
-/

namespace YangMills.RG

open YangMills

noncomputable section

/-- The source flat gauge configuration is exactly the ambient flat gauge
background.  Both sides are literal unit fields; neither is caller data. -/
theorem cmp99SourceFlatGaugeConfig_eq_cmp99FlatGaugeBackground
    (d N Nc : ℕ) [NeZero d] [NeZero N] [NeZero Nc] :
    cmp99SourceFlatGaugeConfig d N Nc =
      cmp99FlatGaugeBackground d N Nc := by
  rfl

end

end YangMills.RG
