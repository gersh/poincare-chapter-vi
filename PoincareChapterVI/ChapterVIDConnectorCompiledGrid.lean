/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.ChapterVIDConnectorPlacement
import PoincareChapterVI.ChapterVILeanCompCertNonzeroGrid

/-!
# LeanCompCert interval-grid boundary for the D connectors

This file is the executable-certificate route for the two connector rectangles. For each side,
one grid encloses the literal transformed radicand. Every cell selects whichever signed
coordinate separates its output rectangle from zero. The verified compiled program checks those
finite endpoint comparisons. The affine root coordinate is proved nonzero analytically.

The data deliberately retain two kernel-side obligations: the cells cover the unit square and
their output rectangles enclose the actual analytic functions. In particular, noncomputable
local Morse inverses are never silently evaluated by compiled code; their certified interval
enclosures must be justified in Lean.
-/

noncomputable section

open scoped unitInterval

namespace PoincareChapterVI

namespace ChapterVIDConnectorCompiledGrid

open ChapterVILeanCompCertNonzeroGrid

/-- The interval campaign needed for one connector side. -/
structure Data
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide)
    (precision radicandCells : ℕ) where
  radicand : ChapterVILeanCompCertNonzeroGrid.Data (I × I)
    precision radicandCells (model.rectangleRadicand side)

/-- The only external observation for one connector: its verified compiled radicand batch
returned zero failures. -/
structure RunVerdict
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide}
    {precision radicandCells : ℕ}
    (radicandName : String)
    (data : Data model side precision radicandCells) : Prop where
  radicand : ChapterVILeanCompCertNonzeroGrid.RunVerdict radicandName data.radicand

/-- Reconstruct the semantic connector certificate from the two successful compiled grids. -/
theorem RunVerdict.toConnectorCertificate
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide}
    {precision radicandCells : ℕ}
    {radicandName : String}
    {data : Data model side precision radicandCells}
    (run : RunVerdict radicandName data) :
    ChapterVIDConnectorCompiledCertificate model side where
  radicand := {
    continuous := model.continuous_rectangleRadicand_of_coordinate_ne_zero side
      (model.rectanglePoint_ne_zero side)
    ne_zero := ChapterVILeanCompCertNonzeroGrid.ne_zero run.radicand }

/-- End-to-end compiled-grid route. Successful radicand batches for both connectors produce the
canonical five-term formal sum with Poincare's exact logarithmic leading coefficient. Seam
compatibility is a separate geometric obligation. -/
theorem exists_fivePieceContribution_tendsto_of_compiledGrids
    (outerRun : ChapterVIDOuterArcPolarCompiledGrid.CompiledRunVerdict)
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    {initialPrecision initialRadicandCells : ℕ}
    {finalPrecision finalRadicandCells : ℕ}
    {initialRadicandName finalRadicandName : String}
    {initialData : Data model .initial initialPrecision initialRadicandCells}
    {finalData : Data model .final finalPrecision finalRadicandCells}
    (initialRun : RunVerdict initialRadicandName initialData)
    (finalRun : RunVerdict finalRadicandName finalData) :
    ∃ pair : ChapterVIDPrincipalConnectorModel.CertifiedConnectorPair outerRun model,
      Filter.Tendsto
        (fun k : ℝ ↦ (-Real.log k)⁻¹ • pair.fivePieceContribution k)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds ((2 * Real.pi * Complex.I : ℂ)⁻¹ *
          chapterVIDPrincipalMorseAmplitude massProduct b d (0, 0))) :=
  ChapterVIDPrincipalConnectorModel.exists_fivePieceContribution_tendsto_of_compiledCertificates
    outerRun model initialRun.toConnectorCertificate finalRun.toConnectorCertificate

end ChapterVIDConnectorCompiledGrid

end PoincareChapterVI
