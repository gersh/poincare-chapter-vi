/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.ChapterVIDConnectorPlacement
import PoincareChapterVI.ChapterVILeanCompCertNonzeroGrid
import PoincareChapterVI.ChapterVILeanCompCertCartesianRadicandTrace

/-!
# LeanCompCert Cartesian grids for the D connectors

Each connector cell supplies dyadic rectangles for the selected parameter root and affine root
coordinate. `ChapterVILeanCompCertCartesianRadicandTrace` turns them into the literal transformed
radicand using only checked signed fixed-point operations. The same compiled batch checks a
signed component separating the resulting radicand rectangle from zero.

The kernel-side obligations are now narrow and auditable: the cells cover the unit square and
their two input rectangles contain the actual analytic values. Static integer budgets derive all
norm enclosures, and checked products derive both exponential error bounds. In particular, there
is no longer a field that simply asserts that a proposed output rectangle contains the whole
radicand. Enclosing the noncomputable inverse-Morse endpoint is isolated in `coordinate_contains`.
-/

noncomputable section

open scoped unitInterval

namespace PoincareChapterVI

namespace ChapterVIDConnectorCompiledGrid

open ChapterVILeanCompCertBatch
open LeanCompCert.Ports.SignedProductClaims

abbrev Rectangle (precision : ℕ) := ChapterVISignedDyadicComplexRectangle precision
abbrev CartesianTrace {precision : ℕ}
    (zeta coordinate : Rectangle precision) :=
  ChapterVILeanCompCertCartesianRadicandTrace.Trace zeta coordinate

/-- One connector cell, with semantic enclosures only for the two inputs and exact rational
constants. All subsequent bounds and arithmetic are checked by Lean or LeanCompCert. -/
structure Cell
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) (precision : ℕ) where
  region : Set (I × I)
  zeta : Rectangle precision
  coordinate : Rectangle precision
  trace : CartesianTrace zeta coordinate
  separation : ChapterVIComplexZeroSeparation
  zeta_contains : ∀ point ∈ region,
    zeta.Contains (model.connectorParameterRoot point.1)
  coordinate_contains : ∀ point ∈ region,
    coordinate.Contains (model.rectanglePoint side point)
  exponentialCoefficient_contains :
    trace.exponentialCoefficient.Contains (100 / 30003 : ℝ)
  inverse10001_contains : trace.inverse10001.Contains (1 / 10001 : ℝ)

def Cell.operations
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide} {precision : ℕ}
    (cell : Cell model side precision) : List (DyadicOperation precision) :=
  cell.trace.operations ++
    [ChapterVILeanCompCertNonzeroGrid.separationOperation
      cell.trace.output cell.separation]

/-- A finite Cartesian grid for one connector. -/
structure Data
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) (precision cells : ℕ) where
  cell : Fin cells → Cell model side precision
  covers : ∀ point : I × I, ∃ index, point ∈ (cell index).region
  admissible : Admissible (batchClaims
    ((List.finRange cells).flatMap fun index ↦ (cell index).operations))

def Data.operations
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide} {precision cells : ℕ}
    (data : Data model side precision cells) : List (DyadicOperation precision) :=
  (List.finRange cells).flatMap fun index ↦ (data.cell index).operations

/-- The sole external observation for one connector: its combined arithmetic-and-separation
batch returned zero failures. -/
structure RunVerdict
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide}
    {precision cells : ℕ}
    (name : String) (data : Data model side precision cells) : Prop where
  returnsZero : (batchComputation name data.operations).Returns ((0 : Nat) : Int)

theorem cell_operation_mem
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide} {precision cells : ℕ}
    (data : Data model side precision cells) (index : Fin cells)
    (operation : DyadicOperation precision)
    (hoperation : operation ∈ (data.cell index).operations) :
    operation ∈ data.operations := by
  rw [Data.operations, List.mem_flatMap]
  exact ⟨index, by simp, hoperation⟩

theorem trace_operation_mem
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide} {precision cells : ℕ}
    (data : Data model side precision cells) (index : Fin cells)
    (operation : DyadicOperation precision)
    (hoperation : operation ∈ (data.cell index).trace.operations) :
    operation ∈ data.operations :=
  cell_operation_mem data index operation
    (List.mem_append_left _ hoperation)

theorem separation_operation_mem
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide} {precision cells : ℕ}
    (data : Data model side precision cells) (index : Fin cells) :
    ChapterVILeanCompCertNonzeroGrid.separationOperation
        (data.cell index).trace.output (data.cell index).separation ∈
      data.operations := by
  apply cell_operation_mem data index
  simp [Cell.operations]

/-- The combined compiled run reconstructs exact nonvanishing of the literal connector
radicand throughout the continuum rectangle. -/
theorem radicand_ne_zero
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide} {precision cells : ℕ}
    {name : String} {data : Data model side precision cells}
    (run : RunVerdict name data) (point : I × I) :
    model.rectangleRadicand side point ≠ 0 := by
  obtain ⟨index, hregion⟩ := data.covers point
  let cell := data.cell index
  have hall : ∀ operation ∈ cell.trace.operations, operation.Sound := by
    intro operation hoperation
    exact allSound_of_returns_zero name data.operations data.admissible run.returnsZero
      operation (trace_operation_mem data index operation hoperation)
  have hcontains : cell.trace.output.Contains (model.rectangleRadicand side point) := by
    change cell.trace.output.Contains
      (chapterVIDRootCoordinateRadicand
        (model.connectorParameterRoot point.1) (model.rectanglePoint side point))
    exact cell.trace.output_contains_rootCoordinateRadicand_of_allSound hall
      (cell.zeta_contains point hregion) (cell.coordinate_contains point hregion)
      cell.exponentialCoefficient_contains cell.inverse10001_contains
      (model.connectorParameterRoot_ne_zero point.1)
      (model.rectanglePoint_ne_zero side point)
  have hseparation := allSound_of_returns_zero name data.operations data.admissible
    run.returnsZero
    (ChapterVILeanCompCertNonzeroGrid.separationOperation
      cell.trace.output cell.separation)
    (separation_operation_mem data index)
  exact cell.separation.ne_zero_of_lower_pos hcontains hseparation

/-- Reconstruct the semantic connector certificate from one successful Cartesian grid. -/
theorem RunVerdict.toConnectorCertificate
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide}
    {precision cells : ℕ}
    {name : String} {data : Data model side precision cells}
    (run : RunVerdict name data) :
    ChapterVIDConnectorCompiledCertificate model side where
  radicand := {
    continuous := model.continuous_rectangleRadicand_of_coordinate_ne_zero side
      (model.rectanglePoint_ne_zero side)
    ne_zero := radicand_ne_zero run }

/-- End-to-end compiled-grid route. Successful Cartesian radicand batches for both connectors
produce the canonical five-term formal sum with Poincare's exact logarithmic leading coefficient.
Seam compatibility is a separate geometric obligation. -/
theorem exists_fivePieceContribution_tendsto_of_compiledGrids
    (outerRun : ChapterVIDOuterArcPolarCompiledGrid.CompiledRunVerdict)
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    {initialPrecision initialCells finalPrecision finalCells : ℕ}
    {initialName finalName : String}
    {initialData : Data model .initial initialPrecision initialCells}
    {finalData : Data model .final finalPrecision finalCells}
    (initialRun : RunVerdict initialName initialData)
    (finalRun : RunVerdict finalName finalData) :
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
