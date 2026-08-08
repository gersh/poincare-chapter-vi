/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.ChapterVIThreeArcAsymptotic
import PoincareChapterVI.ChapterVIDOuterArcRegularity

/-!
# Compiled outer arcs and the principal three-arc continuation

The local middle curve is now a literal source-coordinate path, and the compiled polar
certificate proves that the two complementary outer integrals have a finite collision limit.
This file joins those two completed analytic statements.

The remaining datum is deliberately geometric: synchronize the positive local critical value
`k` with the certified global radial parameter and prove that the continued full source contour
decomposes into the certified outer contribution plus the constructed local middle contribution.
Once that placement is supplied, regularity and the nonzero logarithmic coefficient are automatic.
-/

noncomputable section

open Filter Topology

namespace PoincareChapterVI

/-- The exact remaining placement data after the compiled outer certificate and the literal
local middle path have been proved.  `globalParameter` synchronizes the local critical value with
the outer certificate's radial parameter; `decomposition` is the source-sheet contour identity. -/
structure ChapterVIDCompiledPrincipalThreeArcPlacement
    (run : ChapterVIDOuterArcPolarCompiledGrid.CompiledRunVerdict)
    (massProduct : ℂ) (b d : ℤ)
    (model : ChapterVIDPrincipalLocalSourceModel massProduct b d) where
  fullContribution : ℝ → ℂ
  globalParameter : ℝ → unitInterval
  globalParameter_tendsto :
    Tendsto globalParameter (𝓝[>] (0 : ℝ)) (𝓝 (1 : unitInterval))
  decomposition : ∀ᶠ k in 𝓝[>] (0 : ℝ),
    fullContribution k =
      ChapterVIDOuterArcRegularity.principalRegularContribution
        run massProduct b d (globalParameter k) +
      chapterVIDPrincipalLocalPhiContribution massProduct b d model.L k

namespace ChapterVIDCompiledPrincipalThreeArcPlacement

/-- The certified regular contribution, pulled back from the global radial parameter to the
positive local critical-value parameter. -/
def regularContribution
    {run : ChapterVIDOuterArcPolarCompiledGrid.CompiledRunVerdict}
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalLocalSourceModel massProduct b d}
    (placement : ChapterVIDCompiledPrincipalThreeArcPlacement
      run massProduct b d model) : ℝ → ℂ :=
  fun k ↦ ChapterVIDOuterArcRegularity.principalRegularContribution
    run massProduct b d (placement.globalParameter k)

/-- The compiled outer contribution has a finite limit after synchronization with the local
critical-value parameter. -/
theorem tendsto_regularContribution
    {run : ChapterVIDOuterArcPolarCompiledGrid.CompiledRunVerdict}
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalLocalSourceModel massProduct b d}
    (placement : ChapterVIDCompiledPrincipalThreeArcPlacement
      run massProduct b d model) :
    Tendsto placement.regularContribution (𝓝[>] (0 : ℝ))
      (𝓝 (ChapterVIDOuterArcRegularity.principalRegularContribution
        run massProduct b d 1)) :=
  Filter.Tendsto.comp
    (ChapterVIDOuterArcRegularity.tendsto_principalRegularContribution_collision
      run massProduct b d)
    placement.globalParameter_tendsto

/-- Convert the geometric placement data into the generic three-arc asymptotic package.  In
particular, the formerly abstract `regular_sublog` field is discharged by the compiled finite
outer limit. -/
def toThreeArcContinuation
    {run : ChapterVIDOuterArcPolarCompiledGrid.CompiledRunVerdict}
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalLocalSourceModel massProduct b d}
    (placement : ChapterVIDCompiledPrincipalThreeArcPlacement
      run massProduct b d model) :
    ChapterVIDPrincipalThreeArcContinuation massProduct b d model :=
  ChapterVIDPrincipalThreeArcContinuation.of_tendsto_regular
    placement.fullContribution placement.regularContribution
    placement.decomposition placement.tendsto_regularContribution

/-- The fully placed compiled continuation inherits Poincaré's exact logarithmic coefficient. -/
theorem tendsto_full_inv_neg_log_smul
    {run : ChapterVIDOuterArcPolarCompiledGrid.CompiledRunVerdict}
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalLocalSourceModel massProduct b d}
    (placement : ChapterVIDCompiledPrincipalThreeArcPlacement
      run massProduct b d model) :
    Tendsto
      (fun k : ℝ ↦ (-Real.log k)⁻¹ • placement.fullContribution k)
      (𝓝[>] 0)
      (𝓝 ((2 * Real.pi * Complex.I : ℂ)⁻¹ *
        chapterVIDPrincipalMorseAmplitude massProduct b d (0, 0))) :=
  placement.toThreeArcContinuation.tendsto_full_inv_neg_log_smul

/-- For nonzero physical masses, the coefficient produced by the compiled three-arc
continuation cannot vanish. -/
theorem full_logCoefficient_ne_zero
    {run : ChapterVIDOuterArcPolarCompiledGrid.CompiledRunVerdict}
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalLocalSourceModel massProduct b d}
    (placement : ChapterVIDCompiledPrincipalThreeArcPlacement
      run massProduct b d model) (hmass : massProduct ≠ 0) :
    (2 * Real.pi * Complex.I : ℂ)⁻¹ *
      chapterVIDPrincipalMorseAmplitude massProduct b d (0, 0) ≠ 0 :=
  placement.toThreeArcContinuation.full_logCoefficient_ne_zero hmass

end ChapterVIDCompiledPrincipalThreeArcPlacement

end PoincareChapterVI
