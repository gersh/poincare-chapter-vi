/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.ChapterVIDConnectorFactorBulkCompiled
import PoincareChapterVI.ChapterVIDHomogeneousAdmissibility

/-!
# Uniform two-dimensional use of the D-connector bulk table

The reference connector table was originally exposed only on the seam `s = 0`.  Its actual
input rectangles are uniform in the critical-value parameter: the terminal parameter-root box,
outer-endpoint box, and inverse-Morse endpoint box already contain every `s : I`.  This file
changes only the semantic coverage predicate of each row.  The checked operations and all
LeanCompCert proofs are definitionally the same.

Consequently the existing 1024-row table certifies the complete two-dimensional connector bulk,
outside the fixed `261/1024` neighborhood of the local endpoint.  The remaining collar is the
scale-sensitive analytic part handled by the homogeneous derivative argument.
-/

noncomputable section

open Set Topology
open scoped unitInterval

namespace PoincareChapterVI.ChapterVIDConnectorFullBulk

open ChapterVILeanCompCertBatch
open ChapterVIDConnectorCompiledGrid
open ChapterVIDConnectorSeamCompiledGrid
open ChapterVIDConnectorFactorBulkReference

/-- The same mesh row as the seam campaign, with no restriction on the first square
coordinate. -/
def fullMeshRegion (index : Fin meshCells) : Set (I × I) :=
  {point | point.2 ∈ chapterVIUnitGridCell 1023
    ⟨index.val, by
      have hi := index.isLt
      change index.val < 1024 at hi
      omega⟩}

theorem parameterInterval_contains_of_mem_fullMeshRegion
    (index : Fin meshCells) (point : I × I)
    (hpoint : point ∈ fullMeshRegion index) :
    (parameterInterval index).Contains (point.2 : ℝ) := by
  apply parameterInterval_contains_of_mem_meshRegion index (0, point.2)
  exact ⟨rfl, hpoint⟩

/-- Repackage a reference row with full parameter coverage.  All arithmetic traces are reused
verbatim. -/
def fullTerminalCell
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) (index : Fin meshCells) :
    TerminalCoarseEndpointCell model side where
  region := fullMeshRegion index
  parameter := parameterInterval index
  coordinateTrace := coordinateTrace side index
  trace := radicandTrace side index
  plusSeparation :=
    (slitSeparation (radicandTrace side index).factorPlus).toZeroSeparation
  minusSeparation :=
    (slitSeparation (radicandTrace side index).factorMinus).toZeroSeparation
  parameter_contains := parameterInterval_contains_of_mem_fullMeshRegion index
  exponentialCoefficient_contains :=
    ChapterVIDOuterArcPolarCompiledGrid.exponentialCoefficient_contains
  inverse10001_contains := ChapterVIDOuterArcPolarCompiledGrid.inverse10001_contains

def fullCell
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) (index : Fin meshCells) :
    ChapterVIDConnectorCompiledGrid.Cell model side 20 :=
  (fullTerminalCell model side (retainedMeshIndex side index)).toCell

theorem fullCell_region
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) (index : Fin meshCells) :
    (fullCell model side index).region =
      fullMeshRegion (retainedMeshIndex side index) := by
  cases side <;> rfl

def fullCellOperations
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) (index : Fin meshCells) :=
  (fullCell model side index).coordinateOperations ++
    (fullCell model side index).trace.operations ++
    [separationOperation (fullCell model side index).trace.factorPlus
      (plusSeparation side index),
     separationOperation (fullCell model side index).trace.factorMinus
      (minusSeparation side index)]

theorem fullCellOperations_eq_reference
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) (index : Fin meshCells) :
    fullCellOperations model side index = referenceCellOperations side index := by
  cases side <;> rfl

theorem point_mem_fullBulkMeshIndex
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) (point : I × I)
    (hbulk : (collarCells : ℝ) / meshCells ≤
      model.connectorLocalBoundaryDistance side point) :
    point ∈ (fullCell model side (bulkMeshIndex side point.2)).region := by
  rw [fullCell_region, retainedMeshIndex_bulkMeshIndex]
  have hdist : (collarCells : ℝ) / meshCells ≤
      dist point.2 (localParameter side) := by
    cases side <;>
      simpa [ChapterVIDPrincipalConnectorModel.connectorLocalBoundaryDistance,
        dist_localParameter_eq] using hbulk
  have hpath := connectorPathPoint_mem_bulkMeshIndex model side point.2
    hdist
  exact hpath.2

/-- The old sharded verdict proves both factor separations at every point of the full bulk
rectangle. -/
theorem fullCell_facts
    (run : ReferenceCompiledRunVerdict)
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) (index : Fin meshCells)
    (point : I × I) (hregion : point ∈ (fullCell model side index).region) :
    (0 < (plusSeparation side index).value
      (model.rectangleFactorPlus side point)) ∧
    (0 < (minusSeparation side index).value
      (model.rectangleFactorMinus side point)) := by
  let selected := fullCell model side index
  have hsound (operation : DyadicOperation 20)
      (hoperation : operation ∈ fullCellOperations model side index) :
      operation.Sound := by
    apply run.operationSound side operation
    rw [referenceOperations, List.mem_flatMap]
    refine ⟨index, by simp, ?_⟩
    rw [← fullCellOperations_eq_reference model side index]
    exact hoperation
  have hcoordinate : ∀ operation ∈ selected.coordinateOperations,
      operation.Sound := by
    intro operation hoperation
    apply hsound operation
    simp [fullCellOperations, selected, hoperation]
  have htrace : ∀ operation ∈ selected.trace.operations,
      operation.Sound := by
    intro operation hoperation
    apply hsound operation
    simp [fullCellOperations, selected, hoperation]
  have hplusSound := hsound
    (separationOperation selected.trace.factorPlus (plusSeparation side index))
    (by simp [fullCellOperations, selected])
  have hminusSound := hsound
    (separationOperation selected.trace.factorMinus (minusSeparation side index))
    (by simp [fullCellOperations, selected])
  have hcontains := selected.factors_contain_of_allSound hcoordinate htrace point hregion
  exact ⟨(plusSeparation side index).value_pos_of_lower_pos hcontains.1 hplusSound,
    (minusSeparation side index).value_pos_of_lower_pos hcontains.2 hminusSound⟩

/-- Exact nonvanishing of Poincare's literal radicand on the complete two-dimensional bulk. -/
theorem radicand_ne_zero_on_fullBulk
    (run : ReferenceCompiledRunVerdict)
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) (point : I × I)
    (hbulk : (collarCells : ℝ) / meshCells ≤
      model.connectorLocalBoundaryDistance side point) :
    model.rectangleRadicand side point ≠ 0 := by
  let index := bulkMeshIndex side point.2
  have hregion : point ∈ (fullCell model side index).region :=
    point_mem_fullBulkMeshIndex model side point hbulk
  have hfacts := fullCell_facts run model side index point hregion
  have hplus : model.rectangleFactorPlus side point ≠ 0 :=
    (plusSeparation side index).ne_zero_of_value_pos hfacts.1
  have hminus : model.rectangleFactorMinus side point ≠ 0 :=
    (minusSeparation side index).ne_zero_of_value_pos hfacts.2
  rw [model.rectangleRadicand_eq_factor_mul side point]
  exact mul_ne_zero hplus hminus

set_option maxHeartbeats 800000 in
/-- The reference bulk and homogeneous tables prove nonvanishing on every positive-critical-value
fiber of the complete connector rectangle.  The excluded face `s = 1` is the collision limit and
is covered by the local Morse sheet, rather than by a global rectangular branch choice. -/
theorem radicand_ne_zero_on_puncturedRectangle
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDAnchoredConnectorModel massProduct b d)
    (hL : model.rootModel.L ≤ 1 / (2 : ℝ) ^ 20)
    (uniform : ChapterVIDUniformAnchorData model (1 / (2 : ℝ) ^ 10))
    (side : ChapterVIDOuterArcSide) (point : I × I)
    (hparameter : point.1 ≠ 1) :
    model.rectangleRadicand side point ≠ 0 := by
  by_cases hbulk : (collarCells : ℝ) / meshCells ≤
      model.connectorLocalBoundaryDistance side point
  · exact radicand_ne_zero_on_fullBulk
      ChapterVIDConnectorFactorBulkReference.referenceRunVerdict
        model.toChapterVIDPrincipalConnectorModel side point hbulk
  · let k := model.criticalValue point.1
    have hkpos : 0 < k := by
      unfold k ChapterVIDPrincipalConnectorModel.criticalValue
      apply mul_pos model.κ_pos
      apply sub_pos.mpr
      apply lt_of_le_of_ne point.1.property.2
      intro heq
      apply hparameter
      exact Subtype.ext heq
    have hkmem := model.criticalValue_mem point.1
    let restricted := model.restrictParameter uniform hkpos hkmem.2
    have hLrestricted : restricted.rootModel.L ≤ 1 / (2 : ℝ) ^ 20 := by
      change model.rootModel.L ≤ 1 / (2 : ℝ) ^ 20
      exact hL
    have hDirection : ∀ selectedSide : ChapterVIDOuterArcSide,
        ‖chapterVIDNormalizedLocalEndpointDelta selectedSide restricted.κ
              restricted.rootModel.L - deriv chapterVIDGlobalContourFromMorse 0‖ <
          1 / (2 : ℝ) ^ 10 := by
      intro selectedSide
      have hfacts := uniform.facts k ⟨hkpos.le, hkmem.2⟩
      cases selectedSide with
      | initial =>
          change ‖chapterVIDNormalizedLocalEndpointDelta .initial k model.rootModel.L -
            deriv chapterVIDGlobalContourFromMorse 0‖ < 1 / (2 : ℝ) ^ 10
          exact hfacts.2.1.1.trans_le (min_le_left _ _)
      | final =>
          change ‖chapterVIDNormalizedLocalEndpointDelta .final k model.rootModel.L -
            deriv chapterVIDGlobalContourFromMorse 0‖ < 1 / (2 : ℝ) ^ 10
          exact hfacts.2.1.2.trans_le (min_le_left _ _)
    have hcertificates :=
      ChapterVIDHomogeneousCompiledTable.orientedRealDerivativeCertificates_of_runs
        ChapterVIDHomogeneousCompiledTable.referenceAdmissibility
        ChapterVIDHomogeneousCompiledTable.referenceRunVerdict restricted hLrestricted hDirection
    have horiented : ChapterVIDConnectorFactorCrossing.OrientedRealDerivativeCertificate
        restricted.toChapterVIDPrincipalConnectorModel side := by
      cases side with
      | initial => exact hcertificates.1
      | final => exact hcertificates.2
    have htCollar : (point.2 : ℝ) ∈
        ChapterVIDConnectorFactorMonotonicity.collarInterval side := by
      have hdist : model.connectorLocalBoundaryDistance side point <
          (collarCells : ℝ) / meshCells := lt_of_not_ge hbulk
      cases side with
      | initial =>
          change (point.2 : ℝ) ∈ Set.Icc (763 / 1024 : ℝ) 1
          constructor
          · simp only [ChapterVIDPrincipalConnectorModel.connectorLocalBoundaryDistance,
              collarCells, meshCells] at hdist
            linarith
          · exact point.2.property.2
      | final =>
          change (point.2 : ℝ) ∈ Set.Icc 0 (261 / 1024 : ℝ)
          constructor
          · exact point.2.property.1
          · simpa [ChapterVIDPrincipalConnectorModel.connectorLocalBoundaryDistance,
              collarCells, meshCells] using hdist.le
    have hpoint :
        model.rectanglePoint side point =
          restricted.rectanglePoint side
            (connectorPathPoint restricted.toChapterVIDPrincipalConnectorModel point.2) := by
      simp only [connectorPathPoint]
      simp [ChapterVIDPrincipalConnectorModel.rectanglePoint,
        ChapterVIDPrincipalGlobalRootModel.connectorPoint, restricted,
        ChapterVIDAnchoredConnectorModel.restrictParameter,
        ChapterVIDPrincipalConnectorModel.restrictParameter, k,
        ChapterVIDPrincipalConnectorModel.criticalValue]
    have hroot : model.connectorParameterRoot point.1 =
        restricted.connectorParameterRoot 0 := by
      simp [ChapterVIDPrincipalConnectorModel.connectorParameterRoot, restricted,
        ChapterVIDAnchoredConnectorModel.restrictParameter,
        ChapterVIDPrincipalConnectorModel.restrictParameter, k,
        ChapterVIDPrincipalConnectorModel.criticalValue]
    have hplusRestricted :=
      ChapterVIDConnectorFactorCrossing.plus_re_pos_on_collar_of_oriented restricted
        ChapterVIDConnectorFactorDerivativeReference.referenceRunVerdict
        ChapterVIDConnectorFactorSecondDerivativeReference.referenceRunVerdict
        side horiented point.2 htCollar
    have hminusRestricted :=
      ChapterVIDConnectorFactorMonotonicity.companion_re_pos_on_collar
        restricted.toChapterVIDPrincipalConnectorModel
        ChapterVIDConnectorFactorDerivativeReference.referenceRunVerdict
        ChapterVIDConnectorFactorSecondDerivativeReference.referenceRunVerdict
        side point.2 htCollar
    have hplus : model.rectangleFactorPlus side point ≠ 0 := by
      intro hzero
      have hre := congrArg Complex.re hzero
      rw [show model.rectangleFactorPlus side point =
          restricted.rectangleFactorPlus side
            (connectorPathPoint restricted.toChapterVIDPrincipalConnectorModel point.2) by
        unfold ChapterVIDPrincipalConnectorModel.rectangleFactorPlus
        rw [hpoint, hroot]
        rfl] at hre
      simp at hre
      linarith
    have hminus : model.rectangleFactorMinus side point ≠ 0 := by
      intro hzero
      have hre := congrArg Complex.re hzero
      rw [show model.rectangleFactorMinus side point =
          restricted.rectangleFactorMinus side
            (connectorPathPoint restricted.toChapterVIDPrincipalConnectorModel point.2) by
        unfold ChapterVIDPrincipalConnectorModel.rectangleFactorMinus
        rw [hpoint, hroot]
        rfl] at hre
      simp at hre
      linarith
    rw [model.rectangleRadicand_eq_factor_mul side point]
    exact mul_ne_zero hplus hminus

/-- Unconditional selection of a connector model whose two complete positive-parameter
rectangles are certified nonvanishing. -/
theorem exists_model_with_puncturedRectangle_nonvanishing
    (massProduct : ℂ) (b d : ℤ) :
    ∃ model : ChapterVIDAnchoredConnectorModel massProduct b d,
      ∀ (side : ChapterVIDOuterArcSide) (point : I × I), point.1 ≠ 1 →
        model.rectangleRadicand side point ≠ 0 := by
  obtain ⟨model, hL, _, _, uniform⟩ :=
    exists_chapterVIDAnchoredConnectorModel_bounded_direction massProduct b d
      (1 / (2 : ℝ) ^ 20) 1 (1 / (2 : ℝ) ^ 10)
      (by positivity) (by positivity) (by positivity)
  exact ⟨model, fun side point hpoint ↦
    radicand_ne_zero_on_puncturedRectangle model hL uniform side point hpoint⟩

/-- The positive-critical-value parameter interval.  The endpoint `1` in the normalized
parameter is the collision fiber, so the historical continuation lives naturally on this
half-open interval. -/
abbrev PositiveConnectorParameter := Set.Ico (0 : ℝ) 1

/-- Inclusion of the positive-critical-value parameter into the closed unit interval used by
the connector formulas. -/
def positiveParameterToUnit (s : PositiveConnectorParameter) : I :=
  ⟨s, s.property.1, s.property.2.le⟩

theorem continuous_positiveParameterToUnit : Continuous positiveParameterToUnit := by
  exact Continuous.subtype_mk continuous_subtype_val _

/-- The complete connector rectangle with the collision face removed, expressed in the literal
coordinates consumed by `rectangleRadicand`. -/
def positiveRectanglePoint (point : PositiveConnectorParameter × I) : I × I :=
  (positiveParameterToUnit point.1, point.2)

theorem continuous_positiveRectanglePoint : Continuous positiveRectanglePoint := by
  exact (continuous_positiveParameterToUnit.comp continuous_fst).prodMk continuous_snd

/-- Poincaré's literal connector radicand on the geometrically correct punctured rectangle. -/
def positiveRectangleRadicand
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) : PositiveConnectorParameter × I → ℂ :=
  fun point ↦ model.rectangleRadicand side (positiveRectanglePoint point)

theorem continuous_positiveRectangleRadicand
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) :
    Continuous (positiveRectangleRadicand model side) :=
  (model.continuous_rectangleRadicand_of_coordinate_ne_zero side
    (model.rectanglePoint_ne_zero side)).comp continuous_positiveRectanglePoint

theorem positiveRectangleRadicand_ne_zero
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDAnchoredConnectorModel massProduct b d)
    (hL : model.rootModel.L ≤ 1 / (2 : ℝ) ^ 20)
    (uniform : ChapterVIDUniformAnchorData model (1 / (2 : ℝ) ^ 10))
    (side : ChapterVIDOuterArcSide) (point : PositiveConnectorParameter × I) :
    positiveRectangleRadicand model.toChapterVIDPrincipalConnectorModel side point ≠ 0 := by
  apply radicand_ne_zero_on_puncturedRectangle model hL uniform side
  intro heq
  have hvalue := congrArg Subtype.val heq
  simp [positiveRectanglePoint, positiveParameterToUnit] at hvalue
  exact point.1.property.2.ne hvalue

/-- The finite bulk table plus the homogeneous endpoint argument therefore constructs an actual
continuous square-root sheet on each complete positive-parameter connector rectangle.  There is
no branch asserted on the collision face; that face is supplied by the local Morse chart. -/
theorem exists_positiveRectangleSquareRootSheet
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDAnchoredConnectorModel massProduct b d)
    (hL : model.rootModel.L ≤ 1 / (2 : ℝ) ^ 20)
    (uniform : ChapterVIDUniformAnchorData model (1 / (2 : ℝ) ^ 10))
    (side : ChapterVIDOuterArcSide)
    (base : PositiveConnectorParameter × I) (baseRoot : ℂ)
    (hbaseRoot : baseRoot ^ 2 = positiveRectangleRadicand
      model.toChapterVIDPrincipalConnectorModel side base) :
    ∃ sheet : ChapterVIContinuousSquareRootSheet
        (positiveRectangleRadicand model.toChapterVIDPrincipalConnectorModel side),
      sheet.root base = baseRoot := by
  let : ContractibleSpace PositiveConnectorParameter :=
    (convex_Ico (0 : ℝ) 1).contractibleSpace ⟨0, by norm_num⟩
  let : LocallyPathConnectedSpace PositiveConnectorParameter :=
    (convex_Ico (0 : ℝ) 1).locallyPathConnectedSpace
  let : ContractibleSpace I :=
    (convex_Icc (0 : ℝ) 1).contractibleSpace (by simp)
  let : LocallyPathConnectedSpace I :=
    (convex_Icc (0 : ℝ) 1).locallyPathConnectedSpace
  let : LocallyPathConnectedSpace (PositiveConnectorParameter × I) := by
    refine LocallyPathConnectedSpace.of_bases
      (p := fun (point : PositiveConnectorParameter × I)
          (sets : Set PositiveConnectorParameter × Set I) ↦
        (sets.1 ∈ nhds point.1 ∧ IsPathConnected sets.1) ∧
          (sets.2 ∈ nhds point.2 ∧ IsPathConnected sets.2))
      (s := fun _ sets ↦ sets.1 ×ˢ sets.2) ?_ ?_
    · intro point
      rw [nhds_prod_eq]
      exact (path_connected_basis point.1).prod (path_connected_basis point.2)
    · intro _ sets hsets
      exact hsets.1.2.prod hsets.2.2
  exact exists_chapterVIContinuousSquareRootSheet _
    (continuous_positiveRectangleRadicand model.toChapterVIDPrincipalConnectorModel side)
    (positiveRectangleRadicand_ne_zero model hL uniform side)
    base baseRoot hbaseRoot

end PoincareChapterVI.ChapterVIDConnectorFullBulk
