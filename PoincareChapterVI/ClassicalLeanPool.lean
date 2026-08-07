/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import LeanPool.PoincareThreeBody.LocalEnergyLeaf

/-!
# The merged Lean Pool foundation

The classical planar restricted-three-body development was merged as
[Vilin97/lean-pool#329](https://github.com/Vilin97/lean-pool/pull/329).  This module pins the
merge commit and exposes its final theorem as the upstream foundation for the separate,
source-faithful investigation of Poincaré's Chapter VI.

The two developments should not be conflated: Lean Pool proves the classical nonintegrability
statement through the collision-band route presented in Yagasaki's modern proof.  The files in
this repository investigate Poincaré's original complex-singularity and projective-geometry
route and explicitly track its additional obligations.
-/

namespace PoincareChapterVI

/-- The already-merged classical nonintegrability theorem, re-exported without duplicating its
formalization in this repository. -/
theorem classicalPlanarRestrictedThreeBodyNonintegrability :
    ¬∃ δ : ℝ, 0 < δ ∧
      ∃ F : ℝ → LeanPool.PoincareThreeBody.PhaseSpace → ℝ,
        LeanPool.PoincareThreeBody.IsJointlyAnalytic δ F ∧
          LeanPool.PoincareThreeBody.IsFirstIntegralFamily δ F ∧
            LeanPool.PoincareThreeBody.IsIndependentSomewhere δ F :=
  LeanPool.PoincareThreeBody.nonintegrability_of_collisionBand

end PoincareChapterVI
