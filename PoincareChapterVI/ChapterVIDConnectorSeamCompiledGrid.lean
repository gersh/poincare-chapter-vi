/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.ChapterVIDConnectorCompiledGrid

/-!
# Compiled branch-cut certificates for the D connector seams

Nonvanishing of a connector radicand produces a square-root sheet, but does not determine the
sign with which an outer-normalized sheet reaches the local Morse boundary.  Connectedness
reduces that question to the single path with critical-value parameter `s = 0`.

This file gives a LeanCompCert-facing certificate for that path.  Each interval cell proves one
of three strict signed bounds on the computed radicand rectangle: positive real part, positive
imaginary part, or negative imaginary part.  Their union is the domain on which Mathlib's
principal complex square root is continuous.  Consequently a successful compiled batch proves
that continuation of the outer principal root reaches the positive local Morse root.

The compiled computation checks only signed fixed-point arithmetic and strict integer bounds.
The cell cover, interval-containment bridge, continuity argument, and square-root uniqueness are
ordinary Lean theorems.
-/

noncomputable section

open Set Topology
open scoped unitInterval

namespace PoincareChapterVI

namespace ChapterVIDConnectorSeamCompiledGrid

open ChapterVILeanCompCertBatch
open LeanCompCert.Ports.SignedProductClaims
open ChapterVIDConnectorCompiledGrid

/-- The three rectangle positions that avoid the branch cut of the principal square root. -/
inductive SlitPlaneSeparation
  | realPositive
  | imagPositive
  | imagNegative
  deriving DecidableEq, Repr

namespace SlitPlaneSeparation

def toZeroSeparation : SlitPlaneSeparation → ChapterVIComplexZeroSeparation
  | .realPositive => .realPositive
  | .imagPositive => .imagPositive
  | .imagNegative => .imagNegative

def interval {precision : ℕ}
    (separation : SlitPlaneSeparation)
    (rectangle : ChapterVISignedDyadicComplexRectangle precision) :
    ChapterVISignedDyadicInterval precision :=
  separation.toZeroSeparation.interval rectangle

def value (separation : SlitPlaneSeparation) (z : ℂ) : ℝ :=
  separation.toZeroSeparation.value z

theorem value_pos_of_lower_pos
    {precision : ℕ}
    (separation : SlitPlaneSeparation)
    {rectangle : ChapterVISignedDyadicComplexRectangle precision}
    {z : ℂ} (hz : rectangle.Contains z)
    (hlower : 0 < (separation.interval rectangle).lower) :
    0 < separation.value z := by
  have hcontains := separation.toZeroSeparation.interval_contains_value hz
  have hlowerReal : 0 <
      ((separation.interval rectangle).lower : ℝ) /
        ChapterVISignedDyadicInterval.scale precision :=
    div_pos (by exact_mod_cast hlower)
      (ChapterVISignedDyadicInterval.scale_pos precision)
  exact hlowerReal.trans_le hcontains.1

/-- A passing signed bound is precisely the pointwise hypothesis needed by
`Complex.continuousAt_sqrt`. -/
theorem sqrt_condition_of_lower_pos
    {precision : ℕ}
    (separation : SlitPlaneSeparation)
    {rectangle : ChapterVISignedDyadicComplexRectangle precision}
    {z : ℂ} (hz : rectangle.Contains z)
    (hlower : 0 < (separation.interval rectangle).lower) :
    0 ≤ z.re ∨ z.im ≠ 0 := by
  have hvalue := separation.value_pos_of_lower_pos hz hlower
  cases separation with
  | realPositive =>
      exact Or.inl hvalue.le
  | imagPositive =>
      exact Or.inr (by
        intro hzero
        simp [value, toZeroSeparation, ChapterVIComplexZeroSeparation.value, hzero] at hvalue)
  | imagNegative =>
      exact Or.inr (by
        intro hzero
        simp [value, toZeroSeparation, ChapterVIComplexZeroSeparation.value, hzero] at hvalue)

theorem ne_zero_of_lower_pos
    {precision : ℕ}
    (separation : SlitPlaneSeparation)
    {rectangle : ChapterVISignedDyadicComplexRectangle precision}
    {z : ℂ} (hz : rectangle.Contains z)
    (hlower : 0 < (separation.interval rectangle).lower) :
    z ≠ 0 := by
  have hvalue := separation.value_pos_of_lower_pos hz hlower
  intro hzero
  subst z
  cases separation <;>
    simp [value, toZeroSeparation, ChapterVIComplexZeroSeparation.value] at hvalue

end SlitPlaneSeparation

/-- The one signed comparison attached to a seam-path cell. -/
def separationOperation {precision : ℕ}
    (rectangle : ChapterVISignedDyadicComplexRectangle precision)
    (separation : SlitPlaneSeparation) : DyadicOperation precision :=
  .positiveLower (separation.interval rectangle)

/-- Arithmetic for a connector cell followed by its branch-cut separation check. -/
def seamOperations
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide} {precision : ℕ}
    (cell : ChapterVIDConnectorCompiledGrid.Cell model side precision)
    (separation : SlitPlaneSeparation) :
    List (DyadicOperation precision) :=
  cell.coordinateOperations ++ cell.trace.operations ++
    [separationOperation cell.trace.output separation]

/-- The connector path at the single critical-value parameter needed to determine the seam
sign.  Its orientation is left unchanged; the outer endpoint is `0` on the initial connector and
`1` on the final connector. -/
def connectorPathPoint
    {massProduct : ℂ} {b d : ℤ}
    (_model : ChapterVIDPrincipalConnectorModel massProduct b d) (t : I) : I × I :=
  (0, t)

def outerParameter : ChapterVIDOuterArcSide → I
  | .initial => 0
  | .final => 1

def localParameter : ChapterVIDOuterArcSide → I
  | .initial => 1
  | .final => 0

@[simp] theorem connectorPathPoint_outer
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) :
    connectorPathPoint model (outerParameter side) = model.connectorBoundaryPoint side 0 := by
  cases side <;> rfl

@[simp] theorem connectorPathPoint_local
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) :
    connectorPathPoint model (localParameter side) =
      model.connectorLocalBoundaryPoint side 0 := by
  cases side <;> rfl

/-- A finite one-dimensional cover of the `s = 0` connector path. -/
structure SeamData
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) (precision cells : ℕ) where
  cell : Fin cells → ChapterVIDConnectorCompiledGrid.Cell model side precision
  separation : Fin cells → SlitPlaneSeparation
  covers : ∀ t : I, ∃ index, connectorPathPoint model t ∈ (cell index).region
  admissible : Admissible (batchClaims
    ((List.finRange cells).flatMap fun index ↦
      seamOperations (cell index) (separation index)))

def SeamData.operations
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide} {precision cells : ℕ}
    (data : SeamData model side precision cells) : List (DyadicOperation precision) :=
  (List.finRange cells).flatMap fun index ↦
    seamOperations (data.cell index) (data.separation index)

/-- The sole external observation: the CompCert-compiled batch returned zero failed claims. -/
structure SeamRunVerdict
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide} {precision cells : ℕ}
    (name : String) (data : SeamData model side precision cells) : Prop where
  returnsZero : (batchComputation name data.operations).Returns ((0 : Nat) : Int)

theorem cell_operation_mem
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide} {precision cells : ℕ}
    (data : SeamData model side precision cells) (index : Fin cells)
    (operation : DyadicOperation precision)
    (hoperation : operation ∈
      seamOperations (data.cell index) (data.separation index)) :
    operation ∈ data.operations := by
  rw [SeamData.operations, List.mem_flatMap]
  exact ⟨index, by simp, hoperation⟩

theorem coordinate_operation_mem
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide} {precision cells : ℕ}
    (data : SeamData model side precision cells) (index : Fin cells)
    (operation : DyadicOperation precision)
    (hoperation : operation ∈ (data.cell index).coordinateOperations) :
    operation ∈ data.operations :=
  cell_operation_mem data index operation
    (by simp [seamOperations, hoperation])

theorem trace_operation_mem
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide} {precision cells : ℕ}
    (data : SeamData model side precision cells) (index : Fin cells)
    (operation : DyadicOperation precision)
    (hoperation : operation ∈ (data.cell index).trace.operations) :
    operation ∈ data.operations :=
  cell_operation_mem data index operation
    (by simp [seamOperations, hoperation])

theorem separation_operation_mem
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide} {precision cells : ℕ}
    (data : SeamData model side precision cells) (index : Fin cells) :
    separationOperation (data.cell index).trace.output (data.separation index) ∈
      data.operations := by
  apply cell_operation_mem data index
  simp [seamOperations]

theorem output_contains_radicand_of_allSound
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide} {precision : ℕ}
    (cell : ChapterVIDConnectorCompiledGrid.Cell model side precision)
    (hcoordinate : ∀ operation ∈ cell.coordinateOperations, operation.Sound)
    (htrace : ∀ operation ∈ cell.trace.operations, operation.Sound)
    (point : I × I) (hregion : point ∈ cell.region) :
    cell.trace.output.Contains (model.rectangleRadicand side point) := by
  have hcoordinateContains :=
    cell.coordinate_contains_of_allSound hcoordinate point hregion
  exact cell.trace.output_contains_rootCoordinateRadicand_of_allSound htrace
    (cell.zeta_contains point hregion) hcoordinateContains
    cell.exponentialCoefficient_contains cell.inverse10001_contains
    (model.connectorParameterRoot_ne_zero point.1)
    (model.rectanglePoint_ne_zero side point)

/-- A successful path batch puts every radicand value in the continuity domain of the principal
square root. -/
theorem sqrt_condition
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide} {precision cells : ℕ}
    {name : String} {data : SeamData model side precision cells}
    (run : SeamRunVerdict name data) (t : I) :
    0 ≤ (model.rectangleRadicand side (connectorPathPoint model t)).re ∨
      (model.rectangleRadicand side (connectorPathPoint model t)).im ≠ 0 := by
  obtain ⟨index, hregion⟩ := data.covers t
  let cell := data.cell index
  have hcoordinate : ∀ operation ∈ cell.coordinateOperations, operation.Sound := by
    intro operation hoperation
    exact allSound_of_returns_zero name data.operations data.admissible run.returnsZero
      operation (coordinate_operation_mem data index operation hoperation)
  have htrace : ∀ operation ∈ cell.trace.operations, operation.Sound := by
    intro operation hoperation
    exact allSound_of_returns_zero name data.operations data.admissible run.returnsZero
      operation (trace_operation_mem data index operation hoperation)
  have hseparation := allSound_of_returns_zero name data.operations data.admissible
    run.returnsZero
    (separationOperation cell.trace.output (data.separation index))
    (separation_operation_mem data index)
  exact (data.separation index).sqrt_condition_of_lower_pos
    (output_contains_radicand_of_allSound cell hcoordinate htrace _ hregion)
    hseparation

theorem radicand_ne_zero
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide} {precision cells : ℕ}
    {name : String} {data : SeamData model side precision cells}
    (run : SeamRunVerdict name data) (t : I) :
    model.rectangleRadicand side (connectorPathPoint model t) ≠ 0 := by
  obtain ⟨index, hregion⟩ := data.covers t
  let cell := data.cell index
  have hcoordinate : ∀ operation ∈ cell.coordinateOperations, operation.Sound := by
    intro operation hoperation
    exact allSound_of_returns_zero name data.operations data.admissible run.returnsZero
      operation (coordinate_operation_mem data index operation hoperation)
  have htrace : ∀ operation ∈ cell.trace.operations, operation.Sound := by
    intro operation hoperation
    exact allSound_of_returns_zero name data.operations data.admissible run.returnsZero
      operation (trace_operation_mem data index operation hoperation)
  have hseparation := allSound_of_returns_zero name data.operations data.admissible
    run.returnsZero
    (separationOperation cell.trace.output (data.separation index))
    (separation_operation_mem data index)
  exact (data.separation index).ne_zero_of_lower_pos
    (output_contains_radicand_of_allSound cell hcoordinate htrace _ hregion)
    hseparation

/-- The principal square root is a continuous sheet along the certified seam path. -/
def principalPathSheet
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide} {precision cells : ℕ}
    {name : String} {data : SeamData model side precision cells}
    (run : SeamRunVerdict name data) :
    ChapterVIContinuousSquareRootSheet
      (fun t : I ↦ model.rectangleRadicand side (connectorPathPoint model t)) where
  root t := Complex.sqrt (model.rectangleRadicand side (connectorPathPoint model t))
  continuous_root := by
    rw [continuous_iff_continuousAt]
    intro t
    exact (Complex.continuousAt_sqrt (sqrt_condition run t)).comp_of_eq
      ((model.continuous_rectangleRadicand_of_coordinate_ne_zero side
        (model.rectanglePoint_ne_zero side)).continuousAt.comp_of_eq
          (continuous_const.prodMk continuous_id).continuousAt rfl) rfl
  root_sq t := by
    unfold Complex.sqrt
    exact Complex.cpow_nat_inv_pow _ (by norm_num : (2 : ℕ) ≠ 0)

/-- A branch-cut batch fixes the previously ambiguous local sign of any connector sheet already
normalized to the compiled outer principal sheet. -/
theorem connectorSheet_eq_localBoundaryRoot_zero
    (outerRun : ChapterVIDOuterArcPolarCompiledGrid.CompiledRunVerdict)
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide} {precision cells : ℕ}
    {name : String} {data : SeamData model side precision cells}
    (run : SeamRunVerdict name data)
    (sheet : ChapterVIContinuousSquareRootSheet (model.rectangleRadicand side))
    (houter : ∀ s : I,
      sheet.root (model.connectorBoundaryPoint side s) =
        model.connectorOuterBoundaryRoot outerRun side s) :
    sheet.root (model.connectorLocalBoundaryPoint side 0) =
      model.connectorLocalBoundaryRoot 0 := by
  let restricted : ChapterVIContinuousSquareRootSheet
      (fun t : I ↦ model.rectangleRadicand side (connectorPathPoint model t)) := {
    root := fun t ↦ sheet.root (connectorPathPoint model t)
    continuous_root := sheet.continuous_root.comp
      (continuous_const.prodMk continuous_id)
    root_sq := fun t ↦ sheet.root_sq _ }
  have hbase : restricted.root (outerParameter side) =
      (principalPathSheet run).root (outerParameter side) := by
    rw [show restricted.root (outerParameter side) =
        sheet.root (model.connectorBoundaryPoint side 0) by
      simp [restricted]]
    rw [houter 0]
    change Complex.sqrt
        (chapterVIDOuterArcRadicand side (model.connectorOuterBoundaryPoint side 0)) =
      Complex.sqrt
        (model.rectangleRadicand side (connectorPathPoint model (outerParameter side)))
    rw [← model.rectangleRadicand_connectorBoundaryPoint side 0]
    simp
  have hall := restricted.root_eq_of_eq_at (principalPathSheet run)
    (radicand_ne_zero run) (outerParameter side) hbase
  have hlocal := congrFun hall (localParameter side)
  rw [show restricted.root (localParameter side) =
      sheet.root (model.connectorLocalBoundaryPoint side 0) by
    simp [restricted]] at hlocal
  rw [show (principalPathSheet run).root (localParameter side) =
      Complex.sqrt (model.connectorLocalBoundaryRadicand 0) by
    simp [principalPathSheet, model.rectangleRadicand_connectorLocalBoundaryPoint]] at hlocal
  exact hlocal

/-- Two successful seam batches upgrade a certificate-selected connector pair to the fully
compatible five-piece contour package. -/
def toSeamCompatiblePair
    (outerRun : ChapterVIDOuterArcPolarCompiledGrid.CompiledRunVerdict)
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    (pair : ChapterVIDPrincipalConnectorModel.CertifiedConnectorPair outerRun model)
    {initialPrecision initialCells finalPrecision finalCells : ℕ}
    {initialName finalName : String}
    {initialData : SeamData model .initial initialPrecision initialCells}
    {finalData : SeamData model .final finalPrecision finalCells}
    (initialRun : SeamRunVerdict initialName initialData)
    (finalRun : SeamRunVerdict finalName finalData) :
    ChapterVIDPrincipalConnectorModel.SeamCompatibleCertifiedConnectorPair outerRun model where
  pair := pair
  initial_local_at_zero :=
    connectorSheet_eq_localBoundaryRoot_zero outerRun initialRun pair.initialSheet
      pair.initial_outer
  final_local_at_zero :=
    connectorSheet_eq_localBoundaryRoot_zero outerRun finalRun pair.finalSheet
      pair.final_outer

/-- End-to-end seam-selection theorem.  The existing continuum nonvanishing certificates create
the outer-normalized connector sheets; the two compiled branch-cut batches then prove that both
sheets reach the positive local Morse branch. -/
theorem exists_seamCompatiblePair_of_compiledCertificates
    (outerRun : ChapterVIDOuterArcPolarCompiledGrid.CompiledRunVerdict)
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (initialCertificate : ChapterVIDConnectorCompiledCertificate model .initial)
    (finalCertificate : ChapterVIDConnectorCompiledCertificate model .final)
    {initialPrecision initialCells finalPrecision finalCells : ℕ}
    {initialName finalName : String}
    {initialData : SeamData model .initial initialPrecision initialCells}
    {finalData : SeamData model .final finalPrecision finalCells}
    (initialRun : SeamRunVerdict initialName initialData)
    (finalRun : SeamRunVerdict finalName finalData) :
    Nonempty
      (ChapterVIDPrincipalConnectorModel.SeamCompatibleCertifiedConnectorPair outerRun model) := by
  obtain ⟨pair⟩ :=
    ChapterVIDPrincipalConnectorModel.exists_certifiedConnectorPair outerRun model
      initialCertificate finalCertificate
  exact ⟨toSeamCompatiblePair outerRun pair initialRun finalRun⟩

/-- The same compiled inputs produce a genuinely seam-compatible five-piece formal contribution
with Poincare's explicit logarithmic leading coefficient. -/
theorem exists_seamCompatibleContribution_tendsto_of_compiledCertificates
    (outerRun : ChapterVIDOuterArcPolarCompiledGrid.CompiledRunVerdict)
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (initialCertificate : ChapterVIDConnectorCompiledCertificate model .initial)
    (finalCertificate : ChapterVIDConnectorCompiledCertificate model .final)
    {initialPrecision initialCells finalPrecision finalCells : ℕ}
    {initialName finalName : String}
    {initialData : SeamData model .initial initialPrecision initialCells}
    {finalData : SeamData model .final finalPrecision finalCells}
    (initialRun : SeamRunVerdict initialName initialData)
    (finalRun : SeamRunVerdict finalName finalData) :
    ∃ compatible :
        ChapterVIDPrincipalConnectorModel.SeamCompatibleCertifiedConnectorPair outerRun model,
      Filter.Tendsto
        (fun k : ℝ ↦ (-Real.log k)⁻¹ • compatible.fivePieceContribution k)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds ((2 * Real.pi * Complex.I : ℂ)⁻¹ *
          chapterVIDPrincipalMorseAmplitude massProduct b d (0, 0))) := by
  obtain ⟨compatible⟩ := exists_seamCompatiblePair_of_compiledCertificates outerRun model
    initialCertificate finalCertificate initialRun finalRun
  exact ⟨compatible, compatible.tendsto_fivePiece_inv_neg_log_smul⟩

end ChapterVIDConnectorSeamCompiledGrid

end PoincareChapterVI
