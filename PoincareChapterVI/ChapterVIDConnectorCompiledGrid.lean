/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.ChapterVIDConnectorPlacement
import PoincareChapterVI.ChapterVIDConnectorInputBounds
import PoincareChapterVI.ChapterVIDConnectorEndpointCollar
import PoincareChapterVI.ChapterVILeanCompCertNonzeroGrid
import PoincareChapterVI.ChapterVILeanCompCertCartesianRadicandTrace

/-!
# LeanCompCert Cartesian grids for the D connectors

Each connector cell supplies dyadic rectangles for the selected parameter root and affine root
coordinate. `ChapterVILeanCompCertCartesianRadicandTrace` turns them into the literal transformed
radicand using only checked signed fixed-point operations. The same compiled batch checks a
signed component separating the resulting radicand rectangle from zero.

The kernel-side obligations are now narrow and auditable. After shrinking the local connector,
its root parameter stays in the final compiled radial cell, so the generated artifact only has to
subdivide the affine interpolation parameter. Static integer budgets derive all norm enclosures,
and checked products derive both exponential error bounds. The two collision factors are enclosed
and separated from zero independently, avoiding interval dependency from multiplying them first.
In particular, there is no field that simply asserts that a proposed output rectangle contains the
whole radicand. Enclosing the noncomputable inverse-Morse endpoint remains isolated in the endpoint
containment obligations.
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
  plusSeparation : ChapterVIComplexZeroSeparation
  minusSeparation : ChapterVIComplexZeroSeparation
  coordinateOperations : List (DyadicOperation precision)
  zeta_contains : ∀ point ∈ region,
    zeta.Contains (model.connectorParameterRoot point.1)
  coordinate_contains_of_allSound :
    (∀ operation ∈ coordinateOperations, operation.Sound) →
      ∀ point ∈ region, coordinate.Contains (model.rectanglePoint side point)
  exponentialCoefficient_contains :
    trace.exponentialCoefficient.Contains (100 / 30003 : ℝ)
  inverse10001_contains : trace.inverse10001.Contains (1 / 10001 : ℝ)

/-- Certificate-facing connector cell built from endpoint rectangles and a checked affine
interpolation. This removes the whole-coordinate enclosure as a semantic premise: only the two
endpoints and the real interpolation parameter must be enclosed. -/
structure AffineCell
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) (precision : ℕ) where
  region : Set (I × I)
  zeta : Rectangle precision
  source : Rectangle precision
  target : Rectangle precision
  parameter : ChapterVISignedDyadicInterval precision
  coordinateTrace : ChapterVISignedDyadicComplexRectangle.LineMapTrace
    source target parameter
  trace : CartesianTrace zeta coordinateTrace.output
  plusSeparation : ChapterVIComplexZeroSeparation
  minusSeparation : ChapterVIComplexZeroSeparation
  zeta_contains : ∀ point ∈ region,
    zeta.Contains (model.connectorParameterRoot point.1)
  source_contains : ∀ point ∈ region,
    source.Contains (model.rootModel.connectorSource side (model.criticalValue point.1))
  target_contains : ∀ point ∈ region,
    target.Contains (model.rootModel.connectorTarget side (model.criticalValue point.1))
  parameter_contains : ∀ point ∈ region, parameter.Contains (point.2 : ℝ)
  exponentialCoefficient_contains :
    trace.exponentialCoefficient.Contains (100 / 30003 : ℝ)
  inverse10001_contains : trace.inverse10001.Contains (1 / 10001 : ℝ)

def AffineCell.toCell
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide} {precision : ℕ}
    (cell : AffineCell model side precision) : Cell model side precision where
  region := cell.region
  zeta := cell.zeta
  coordinate := cell.coordinateTrace.output
  trace := cell.trace
  plusSeparation := cell.plusSeparation
  minusSeparation := cell.minusSeparation
  coordinateOperations := cell.coordinateTrace.operations
  zeta_contains := cell.zeta_contains
  coordinate_contains_of_allSound := by
    intro hall point hpoint
    have hline := cell.coordinateTrace.output_contains_lineMap_of_allSound hall
      (cell.source_contains point hpoint) (cell.target_contains point hpoint)
      (cell.parameter_contains point hpoint)
    simpa [ChapterVIDPrincipalConnectorModel.rectanglePoint,
      ChapterVIDPrincipalGlobalRootModel.connectorPoint] using hline
  exponentialCoefficient_contains := cell.exponentialCoefficient_contains
  inverse10001_contains := cell.inverse10001_contains

def coarseSourceRectangle (side : ChapterVIDOuterArcSide) (outer : Rectangle 20) :
    Rectangle 20 :=
  match side with
  | .initial => outer
  | .final => ChapterVIDConnectorInputBounds.localEndpointRectangle

def coarseTargetRectangle (side : ChapterVIDOuterArcSide) (outer : Rectangle 20) :
    Rectangle 20 :=
  match side with
  | .initial => ChapterVIDConnectorInputBounds.localEndpointRectangle
  | .final => outer

/-- A concrete affine-cell interface in which the inverse-Morse endpoint box is discharged once
and for all by `localEndpointRectangle_contains`. Certificate generation supplies only the outer
endpoint box, interpolation interval, and parameter-root box. -/
structure CoarseEndpointCell
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) where
  region : Set (I × I)
  zeta : Rectangle 20
  outer : Rectangle 20
  parameter : ChapterVISignedDyadicInterval 20
  coordinateTrace : ChapterVISignedDyadicComplexRectangle.LineMapTrace
    (coarseSourceRectangle side outer) (coarseTargetRectangle side outer) parameter
  trace : CartesianTrace zeta coordinateTrace.output
  plusSeparation : ChapterVIComplexZeroSeparation
  minusSeparation : ChapterVIComplexZeroSeparation
  zeta_contains : ∀ point ∈ region,
    zeta.Contains (model.connectorParameterRoot point.1)
  outer_contains : ∀ point ∈ region,
    outer.Contains
      (model.rootModel.outerConnectorEndpoint side (model.criticalValue point.1))
  parameter_contains : ∀ point ∈ region, parameter.Contains (point.2 : ℝ)
  exponentialCoefficient_contains :
    trace.exponentialCoefficient.Contains (100 / 30003 : ℝ)
  inverse10001_contains : trace.inverse10001.Contains (1 / 10001 : ℝ)

def CoarseEndpointCell.toAffineCell
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide}
    (cell : CoarseEndpointCell model side) : AffineCell model side 20 := by
  cases side with
  | initial =>
      exact {
        region := cell.region
        zeta := cell.zeta
        source := cell.outer
        target := ChapterVIDConnectorInputBounds.localEndpointRectangle
        parameter := cell.parameter
        coordinateTrace := cell.coordinateTrace
        trace := cell.trace
        plusSeparation := cell.plusSeparation
        minusSeparation := cell.minusSeparation
        zeta_contains := cell.zeta_contains
        source_contains := by
          intro point hpoint
          simpa [ChapterVIDPrincipalGlobalRootModel.connectorSource] using
            cell.outer_contains point hpoint
        target_contains := by
          intro point _
          simpa [ChapterVIDPrincipalGlobalRootModel.connectorTarget] using
            ChapterVIDConnectorInputBounds.localEndpointRectangle_contains
              model.rootModel .initial (model.criticalValue point.1)
              (model.criticalValue_mem_rootModel point.1)
        parameter_contains := cell.parameter_contains
        exponentialCoefficient_contains := cell.exponentialCoefficient_contains
        inverse10001_contains := cell.inverse10001_contains }
  | final =>
      exact {
        region := cell.region
        zeta := cell.zeta
        source := ChapterVIDConnectorInputBounds.localEndpointRectangle
        target := cell.outer
        parameter := cell.parameter
        coordinateTrace := cell.coordinateTrace
        trace := cell.trace
        plusSeparation := cell.plusSeparation
        minusSeparation := cell.minusSeparation
        zeta_contains := cell.zeta_contains
        source_contains := by
          intro point _
          simpa [ChapterVIDPrincipalGlobalRootModel.connectorSource] using
            ChapterVIDConnectorInputBounds.localEndpointRectangle_contains
              model.rootModel .final (model.criticalValue point.1)
              (model.criticalValue_mem_rootModel point.1)
        target_contains := by
          intro point hpoint
          simpa [ChapterVIDPrincipalGlobalRootModel.connectorTarget] using
            cell.outer_contains point hpoint
        parameter_contains := cell.parameter_contains
        exponentialCoefficient_contains := cell.exponentialCoefficient_contains
        inverse10001_contains := cell.inverse10001_contains }

def CoarseEndpointCell.toCell
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide}
    (cell : CoarseEndpointCell model side) : Cell model side 20 :=
  cell.toAffineCell.toCell

/-- The connector model has already been shrunk into the last certified radial cell. Thus a
generated cell needs only its connector-parameter interval and arithmetic traces; the parameter
root and outer endpoint boxes are fixed and their semantic containment is automatic. -/
structure TerminalCoarseEndpointCell
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) where
  region : Set (I × I)
  parameter : ChapterVISignedDyadicInterval 20
  coordinateTrace : ChapterVISignedDyadicComplexRectangle.LineMapTrace
    (coarseSourceRectangle side
      (ChapterVIDConnectorInputBounds.terminalOuterRectangle side))
    (coarseTargetRectangle side
      (ChapterVIDConnectorInputBounds.terminalOuterRectangle side)) parameter
  trace : CartesianTrace
    ChapterVIDConnectorInputBounds.terminalZetaRectangle coordinateTrace.output
  plusSeparation : ChapterVIComplexZeroSeparation
  minusSeparation : ChapterVIComplexZeroSeparation
  parameter_contains : ∀ point ∈ region, parameter.Contains (point.2 : ℝ)
  exponentialCoefficient_contains :
    trace.exponentialCoefficient.Contains (100 / 30003 : ℝ)
  inverse10001_contains : trace.inverse10001.Contains (1 / 10001 : ℝ)

def TerminalCoarseEndpointCell.toCoarseEndpointCell
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide}
    (cell : TerminalCoarseEndpointCell model side) : CoarseEndpointCell model side where
  region := cell.region
  zeta := ChapterVIDConnectorInputBounds.terminalZetaRectangle
  outer := ChapterVIDConnectorInputBounds.terminalOuterRectangle side
  parameter := cell.parameter
  coordinateTrace := cell.coordinateTrace
  trace := cell.trace
  plusSeparation := cell.plusSeparation
  minusSeparation := cell.minusSeparation
  zeta_contains := by
    intro point _
    simpa [ChapterVIDPrincipalConnectorModel.connectorParameterRoot] using
      ChapterVIDConnectorInputBounds.terminalZetaRectangle_contains model point.1
  outer_contains := by
    intro point _
    exact ChapterVIDConnectorInputBounds.terminalOuterRectangle_contains model side point.1
  parameter_contains := cell.parameter_contains
  exponentialCoefficient_contains := cell.exponentialCoefficient_contains
  inverse10001_contains := cell.inverse10001_contains

def TerminalCoarseEndpointCell.toCell
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide}
    (cell : TerminalCoarseEndpointCell model side) : Cell model side 20 :=
  cell.toCoarseEndpointCell.toCell

def Cell.operations
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide} {precision : ℕ}
  (cell : Cell model side precision) : List (DyadicOperation precision) :=
  cell.coordinateOperations ++ cell.trace.operations ++
    [ChapterVILeanCompCertNonzeroGrid.separationOperation
      cell.trace.factorPlus cell.plusSeparation,
    ChapterVILeanCompCertNonzeroGrid.separationOperation
      cell.trace.factorMinus cell.minusSeparation]

/-- Reconstruct the two literal collision-factor enclosures separately.  This is the sharp
interface used by branch transport; multiplying the rectangles first loses the conjugate-like
dependency between the factors. -/
theorem Cell.factors_contain_of_allSound
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide} {precision : ℕ}
    (cell : Cell model side precision)
    (hcoordinate : ∀ operation ∈ cell.coordinateOperations, operation.Sound)
    (hall : ∀ operation ∈ cell.trace.operations, operation.Sound)
    (point : I × I) (hregion : point ∈ cell.region) :
    cell.trace.factorPlus.Contains (model.rectangleFactorPlus side point) ∧
      cell.trace.factorMinus.Contains (model.rectangleFactorMinus side point) := by
  let ζ := model.connectorParameterRoot point.1
  let u := model.rectanglePoint side point
  have hζ : cell.zeta.Contains ζ := cell.zeta_contains point hregion
  have hu : cell.coordinate.Contains u :=
    cell.coordinate_contains_of_allSound hcoordinate point hregion
  have hζne : ζ ≠ 0 := model.connectorParameterRoot_ne_zero point.1
  have hune : u ≠ 0 := model.rectanglePoint_ne_zero side point
  have hanomalies := cell.trace.anomalies_contain_of_allSound hall hζ hu
    cell.exponentialCoefficient_contains hζne hune
  have hfactors := cell.trace.factors_contain_sparse_of_allSound hall hu
    cell.inverse10001_contains hanomalies.1 hanomalies.2
  constructor
  · rw [show model.rectangleFactorPlus side point =
        chapterVIDRootCoordinateCollisionFactorPlus ζ u by rfl,
      chapterVIDRootCoordinateCollisionFactorPlus_eq_polarCertificateFormula hζne hune]
    exact hfactors.1
  · rw [show model.rectangleFactorMinus side point =
        chapterVIDRootCoordinateCollisionFactorMinus ζ u by rfl,
      chapterVIDRootCoordinateCollisionFactorMinus_eq_polarCertificateFormula hζne hune]
    exact hfactors.2

/-- Kernel-side semantic reconstruction for one checked connector cell.  The surrounding grid
only has to supply soundness of the operations and membership of the point in this cell. -/
theorem Cell.radicand_ne_zero_of_allSound
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide} {precision : ℕ}
    (cell : Cell model side precision)
    (hcoordinate : ∀ operation ∈ cell.coordinateOperations, operation.Sound)
    (hall : ∀ operation ∈ cell.trace.operations, operation.Sound)
    (hplusSound : (ChapterVILeanCompCertNonzeroGrid.separationOperation
      cell.trace.factorPlus cell.plusSeparation).Sound)
    (hminusSound : (ChapterVILeanCompCertNonzeroGrid.separationOperation
      cell.trace.factorMinus cell.minusSeparation).Sound)
    (point : I × I) (hregion : point ∈ cell.region) :
    model.rectangleRadicand side point ≠ 0 := by
  let ζ := model.connectorParameterRoot point.1
  let u := model.rectanglePoint side point
  have hζ : cell.zeta.Contains ζ := cell.zeta_contains point hregion
  have hu : cell.coordinate.Contains u :=
    cell.coordinate_contains_of_allSound hcoordinate point hregion
  have hζne : ζ ≠ 0 := model.connectorParameterRoot_ne_zero point.1
  have hune : u ≠ 0 := model.rectanglePoint_ne_zero side point
  have hanomalies := cell.trace.anomalies_contain_of_allSound hall hζ hu
    cell.exponentialCoefficient_contains hζne hune
  have hfactors := cell.trace.factors_contain_sparse_of_allSound hall hu
    cell.inverse10001_contains hanomalies.1 hanomalies.2
  have hplusNe := cell.plusSeparation.ne_zero_of_lower_pos hfactors.1 hplusSound
  have hminusNe := cell.minusSeparation.ne_zero_of_lower_pos hfactors.2 hminusSound
  change chapterVIDRootCoordinateRadicand ζ u ≠ 0
  rw [chapterVIDRootCoordinateRadicand_eq_polarCertificateFormula hζne hune]
  exact mul_ne_zero hplusNe hminusNe

/-- A finite Cartesian grid for one connector. -/
structure Data
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) (precision cells : ℕ) where
  cell : Fin cells → Cell model side precision
  covers : ∀ point : I × I, ∃ index, point ∈ (cell index).region
  admissible : Admissible (batchClaims
    ((List.finRange cells).flatMap fun index ↦ (cell index).operations))

/-- A complete connector grid whose only analytic input boxes are the parameter root and the
explicit outer endpoint. The noncomputable local endpoint and affine interpolation have already
been discharged by `CoarseEndpointCell.toCell`. -/
structure CoarseData
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) (cells : ℕ) where
  cell : Fin cells → CoarseEndpointCell model side
  covers : ∀ point : I × I, ∃ index, point ∈ (cell index).region
  admissible : Admissible (batchClaims
    ((List.finRange cells).flatMap fun index ↦ (cell index).toCell.operations))

def CoarseData.toData
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide} {cells : ℕ}
    (data : CoarseData model side cells) : Data model side 20 cells := by
  cases side <;>
    exact {
      cell := fun index ↦ (data.cell index).toCell
      covers := data.covers
      admissible := data.admissible }

/-- One-dimensional terminal-cell grid: the sole varying mesh coordinate is the affine
connector parameter. -/
structure TerminalCoarseData
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) (cells : ℕ) where
  cell : Fin cells → TerminalCoarseEndpointCell model side
  covers : ∀ point : I × I, ∃ index, point ∈ (cell index).region
  admissible : Admissible (batchClaims
    ((List.finRange cells).flatMap fun index ↦ (cell index).toCell.operations))

def TerminalCoarseData.toData
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide} {cells : ℕ}
    (data : TerminalCoarseData model side cells) : Data model side 20 cells := by
  cases side <;>
    exact {
      cell := fun index ↦ (data.cell index).toCell
      covers := data.covers
      admissible := data.admissible }

def Data.operations
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide} {precision cells : ℕ}
  (data : Data model side precision cells) : List (DyadicOperation precision) :=
  (List.finRange cells).flatMap fun index ↦ (data.cell index).operations

/-- A compiled grid for the bulk of one connector.  Cells only cover the complement of the
analytic endpoint collar, so the impossible collision-containing endpoint boxes never enter the
compiled run. -/
structure BulkData
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide)
    (collar : ChapterVIDPrincipalConnectorModel.ConnectorEndpointCollar model side)
    (precision cells : ℕ) where
  cell : Fin cells → Cell model side precision
  covers : ∀ point : I × I,
    collar.width ≤ model.connectorLocalBoundaryDistance side point →
      ∃ index, point ∈ (cell index).region
  admissible : Admissible (batchClaims
    ((List.finRange cells).flatMap fun index ↦ (cell index).operations))

def BulkData.operations
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide}
    {collar : ChapterVIDPrincipalConnectorModel.ConnectorEndpointCollar model side}
    {precision cells : ℕ}
    (data : BulkData model side collar precision cells) :
    List (DyadicOperation precision) :=
  (List.finRange cells).flatMap fun index ↦ (data.cell index).operations

/-- One-dimensional certificate-generator interface for the bulk outside an analytic endpoint
collar.  Parameter-root and outer-endpoint enclosures remain the proved terminal-cell boxes. -/
structure TerminalCoarseBulkData
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide)
    (collar : ChapterVIDPrincipalConnectorModel.ConnectorEndpointCollar model side)
    (cells : ℕ) where
  cell : Fin cells → TerminalCoarseEndpointCell model side
  covers : ∀ point : I × I,
    collar.width ≤ model.connectorLocalBoundaryDistance side point →
      ∃ index, point ∈ (cell index).region
  admissible : Admissible (batchClaims
    ((List.finRange cells).flatMap fun index ↦ (cell index).toCell.operations))

/-- Power-of-two specialization consumed by a certificate generator after an endpoint-collar
exponent has been selected. -/
abbrev DyadicTerminalCoarseBulkData
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide)
    (collar : ChapterVIDPrincipalConnectorModel.DyadicConnectorEndpointCollar model side)
    (cells : ℕ) :=
  TerminalCoarseBulkData model side collar.toEndpointCollar cells

def TerminalCoarseBulkData.toBulkData
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide}
    {collar : ChapterVIDPrincipalConnectorModel.ConnectorEndpointCollar model side}
    {cells : ℕ}
    (data : TerminalCoarseBulkData model side collar cells) :
    BulkData model side collar 20 cells := by
  cases side <;>
    exact {
      cell := fun index ↦ (data.cell index).toCell
      covers := data.covers
      admissible := data.admissible }

/-- The sole external observation for one connector: its combined arithmetic and two-factor
separation batch returned zero failures. -/
structure RunVerdict
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide}
    {precision cells : ℕ}
    (name : String) (data : Data model side precision cells) : Prop where
  returnsZero : (batchComputation name data.operations).Returns ((0 : Nat) : Int)

/-- The sole external observation for a hybrid connector: the arithmetic batch for its compiled
bulk returned zero failures.  Endpoint nonvanishing is supplied by `collar`. -/
structure BulkRunVerdict
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide}
    {collar : ChapterVIDPrincipalConnectorModel.ConnectorEndpointCollar model side}
    {precision cells : ℕ}
    (name : String) (data : BulkData model side collar precision cells) : Prop where
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
    (by simp [Cell.operations, hoperation])

theorem coordinate_operation_mem
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide} {precision cells : ℕ}
    (data : Data model side precision cells) (index : Fin cells)
    (operation : DyadicOperation precision)
    (hoperation : operation ∈ (data.cell index).coordinateOperations) :
    operation ∈ data.operations :=
  cell_operation_mem data index operation
    (by simp [Cell.operations, hoperation])

theorem plus_separation_operation_mem
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide} {precision cells : ℕ}
    (data : Data model side precision cells) (index : Fin cells) :
    ChapterVILeanCompCertNonzeroGrid.separationOperation
        (data.cell index).trace.factorPlus (data.cell index).plusSeparation ∈
      data.operations := by
  apply cell_operation_mem data index
  simp [Cell.operations]

theorem minus_separation_operation_mem
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide} {precision cells : ℕ}
    (data : Data model side precision cells) (index : Fin cells) :
    ChapterVILeanCompCertNonzeroGrid.separationOperation
        (data.cell index).trace.factorMinus (data.cell index).minusSeparation ∈
      data.operations := by
  apply cell_operation_mem data index
  simp [Cell.operations]

theorem bulk_cell_operation_mem
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide}
    {collar : ChapterVIDPrincipalConnectorModel.ConnectorEndpointCollar model side}
    {precision cells : ℕ}
    (data : BulkData model side collar precision cells) (index : Fin cells)
    (operation : DyadicOperation precision)
    (hoperation : operation ∈ (data.cell index).operations) :
    operation ∈ data.operations := by
  rw [BulkData.operations, List.mem_flatMap]
  exact ⟨index, by simp, hoperation⟩

theorem bulk_trace_operation_mem
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide}
    {collar : ChapterVIDPrincipalConnectorModel.ConnectorEndpointCollar model side}
    {precision cells : ℕ}
    (data : BulkData model side collar precision cells) (index : Fin cells)
    (operation : DyadicOperation precision)
    (hoperation : operation ∈ (data.cell index).trace.operations) :
    operation ∈ data.operations :=
  bulk_cell_operation_mem data index operation
    (by simp [Cell.operations, hoperation])

theorem bulk_coordinate_operation_mem
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide}
    {collar : ChapterVIDPrincipalConnectorModel.ConnectorEndpointCollar model side}
    {precision cells : ℕ}
    (data : BulkData model side collar precision cells) (index : Fin cells)
    (operation : DyadicOperation precision)
    (hoperation : operation ∈ (data.cell index).coordinateOperations) :
    operation ∈ data.operations :=
  bulk_cell_operation_mem data index operation
    (by simp [Cell.operations, hoperation])

theorem bulk_plus_separation_operation_mem
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide}
    {collar : ChapterVIDPrincipalConnectorModel.ConnectorEndpointCollar model side}
    {precision cells : ℕ}
    (data : BulkData model side collar precision cells) (index : Fin cells) :
    ChapterVILeanCompCertNonzeroGrid.separationOperation
        (data.cell index).trace.factorPlus (data.cell index).plusSeparation ∈
      data.operations := by
  apply bulk_cell_operation_mem data index
  simp [Cell.operations]

theorem bulk_minus_separation_operation_mem
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide}
    {collar : ChapterVIDPrincipalConnectorModel.ConnectorEndpointCollar model side}
    {precision cells : ℕ}
    (data : BulkData model side collar precision cells) (index : Fin cells) :
    ChapterVILeanCompCertNonzeroGrid.separationOperation
        (data.cell index).trace.factorMinus (data.cell index).minusSeparation ∈
      data.operations := by
  apply bulk_cell_operation_mem data index
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
  have hcoordinate : ∀ operation ∈ cell.coordinateOperations,
      operation.Sound := by
    intro operation hoperation
    exact allSound_of_returns_zero name data.operations data.admissible run.returnsZero
      operation (coordinate_operation_mem data index operation hoperation)
  have hall : ∀ operation ∈ cell.trace.operations, operation.Sound := by
    intro operation hoperation
    exact allSound_of_returns_zero name data.operations data.admissible run.returnsZero
      operation (trace_operation_mem data index operation hoperation)
  have hplusSound := allSound_of_returns_zero name data.operations data.admissible
    run.returnsZero
    (ChapterVILeanCompCertNonzeroGrid.separationOperation
      cell.trace.factorPlus cell.plusSeparation)
    (plus_separation_operation_mem data index)
  have hminusSound := allSound_of_returns_zero name data.operations data.admissible
    run.returnsZero
    (ChapterVILeanCompCertNonzeroGrid.separationOperation
      cell.trace.factorMinus cell.minusSeparation)
    (minus_separation_operation_mem data index)
  exact cell.radicand_ne_zero_of_allSound hcoordinate hall hplusSound hminusSound
    point hregion

/-- Exact nonvanishing reconstructed by splitting the connector into the analytic Morse collar
and its LeanCompCert-checked Cartesian bulk. -/
theorem bulkRun_radicand_ne_zero
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide}
    {collar : ChapterVIDPrincipalConnectorModel.ConnectorEndpointCollar model side}
    {precision cells : ℕ}
    {name : String} {data : BulkData model side collar precision cells}
    (run : BulkRunVerdict name data) (point : I × I) :
    model.rectangleRadicand side point ≠ 0 := by
  by_cases hcollar :
      model.connectorLocalBoundaryDistance side point < collar.width
  · exact collar.radicand_ne_zero point hcollar
  · obtain ⟨index, hregion⟩ := data.covers point (le_of_not_gt hcollar)
    let cell := data.cell index
    have hcoordinate : ∀ operation ∈ cell.coordinateOperations,
        operation.Sound := by
      intro operation hoperation
      exact allSound_of_returns_zero name data.operations data.admissible run.returnsZero
        operation (bulk_coordinate_operation_mem data index operation hoperation)
    have hall : ∀ operation ∈ cell.trace.operations, operation.Sound := by
      intro operation hoperation
      exact allSound_of_returns_zero name data.operations data.admissible run.returnsZero
        operation (bulk_trace_operation_mem data index operation hoperation)
    have hplusSound := allSound_of_returns_zero name data.operations data.admissible
      run.returnsZero
      (ChapterVILeanCompCertNonzeroGrid.separationOperation
        cell.trace.factorPlus cell.plusSeparation)
      (bulk_plus_separation_operation_mem data index)
    have hminusSound := allSound_of_returns_zero name data.operations data.admissible
      run.returnsZero
      (ChapterVILeanCompCertNonzeroGrid.separationOperation
        cell.trace.factorMinus cell.minusSeparation)
      (bulk_minus_separation_operation_mem data index)
    exact cell.radicand_ne_zero_of_allSound hcoordinate hall hplusSound hminusSound
      point hregion

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

/-- Reconstruct the same downstream connector certificate from an analytic endpoint collar and
a successful compiled run on its complement. -/
theorem BulkRunVerdict.toConnectorCertificate
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide}
    {collar : ChapterVIDPrincipalConnectorModel.ConnectorEndpointCollar model side}
    {precision cells : ℕ}
    {name : String} {data : BulkData model side collar precision cells}
    (run : BulkRunVerdict name data) :
    ChapterVIDConnectorCompiledCertificate model side where
  radicand := {
    continuous := model.continuous_rectangleRadicand_of_coordinate_ne_zero side
      (model.rectanglePoint_ne_zero side)
    ne_zero := bulkRun_radicand_ne_zero run }

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

/-- End-to-end hybrid route: exact Morse collars remove the endpoint singularity from the
finite artifact, while LeanCompCert checks the remaining one-dimensional connector bulks. -/
theorem exists_fivePieceContribution_tendsto_of_compiledBulks
    (outerRun : ChapterVIDOuterArcPolarCompiledGrid.CompiledRunVerdict)
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    {initialCollar :
      ChapterVIDPrincipalConnectorModel.ConnectorEndpointCollar model .initial}
    {finalCollar :
      ChapterVIDPrincipalConnectorModel.ConnectorEndpointCollar model .final}
    {initialPrecision initialCells finalPrecision finalCells : ℕ}
    {initialName finalName : String}
    {initialData :
      BulkData model .initial initialCollar initialPrecision initialCells}
    {finalData : BulkData model .final finalCollar finalPrecision finalCells}
    (initialRun : BulkRunVerdict initialName initialData)
    (finalRun : BulkRunVerdict finalName finalData) :
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
