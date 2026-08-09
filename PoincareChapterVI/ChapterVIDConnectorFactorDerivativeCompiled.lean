/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.ChapterVIDConnectorFactorDerivativeAdmissibility
import PoincareChapterVI.ChapterVILeanCompCertAttestation

/-!
# Sharded compiled certificate for connector-factor monotonicity

The 492 derivative-certified cells are split into 41 independent artifacts of 12 cells each.
Lean verifies that every artifact lies in LeanCompCert's bounded integer fragment.  A successful
compiled run, optionally supplied by hash-bound receipts, then reconstructs the interval meaning
of every operation and proves strict positivity of the path derivative's imaginary part.

This module intentionally says nothing about the 30 endpoint-adjacent cells omitted from the
reference campaign.  Their treatment is a separate analytic obligation.
-/

noncomputable section

open scoped unitInterval

namespace PoincareChapterVI.ChapterVIDConnectorFactorDerivativeReference

open ChapterVILeanCompCertBatch
open ChapterVILeanCompCertAttestation
open ChapterVILeanCompCertCartesianFactorDerivativeTrace
open ChapterVIDConnectorFactorBulkReference
open ChapterVIDConnectorSeamCompiledGrid
open LeanCompCert.Ports.SignedProductClaims

/-- The external execution observations for all 41 bounded derivative artifacts. -/
structure ReferenceCompiledRunVerdict : Prop where
  returnsZero : ∀ side shard,
    (batchComputation (shardArtifactName side shard)
      (shardOperations side shard)).Returns ((0 : Nat) : Int)

/-- Hash-bound receipts for the exact Lean-derived artifacts produce the compiled verdict.
`RunAdmission` remains explicit: it is the empirical statement that the identified binary ran. -/
theorem ReferenceCompiledRunVerdict.ofReceipts
    (crypto : LeanCompCert.Attest.ReceiptCrypto)
    (receipt : (side : ChapterVIDOuterArcSide) → Fin (shardCount side) →
      LeanCompCert.Attest.RunReceipt)
    (kind : (side : ChapterVIDOuterArcSide) → Fin (shardCount side) →
      LeanCompCert.Attest.AttestationKind)
    (params nonce : (side : ChapterVIDOuterArcSide) → Fin (shardCount side) → String)
    (bound : ∀ side shard,
      LeanCompCert.Attest.receiptBindsProved crypto
        (batchArtifact (shardArtifactName side shard) (shardOperations side shard))
        (kind side shard) (params side shard) (nonce side shard) ((0 : Nat) : Int)
        (receipt side shard) = true)
    (admitted : ∀ side shard,
      LeanCompCert.Attest.RunAdmission crypto
        (batchArtifact (shardArtifactName side shard) (shardOperations side shard))
        (receipt side shard)) : ReferenceCompiledRunVerdict where
  returnsZero side shard :=
    returns_zero_of_receipt (shardArtifactName side shard) (shardOperations side shard)
      crypto (receipt side shard) (kind side shard) (params side shard) (nonce side shard)
      (bound side shard) (admitted side shard)

/-- Every operation in the assembled derivative table is sound after the 41 shard runs pass. -/
theorem ReferenceCompiledRunVerdict.operationSound
    (run : ReferenceCompiledRunVerdict)
    (side : ChapterVIDOuterArcSide) (operation : DyadicOperation 20)
    (hoperation : operation ∈ operations side) : operation.Sound := by
  obtain ⟨shard, hshard⟩ := operation_mem_shard side operation hoperation
  exact allSound_of_returns_zero (shardArtifactName side shard)
    (shardOperations side shard) (shard_admissible side shard)
    (run.returnsZero side shard) operation hshard

theorem ReferenceCompiledRunVerdict.cellOperationSound
    (run : ReferenceCompiledRunVerdict)
    (side : ChapterVIDOuterArcSide) (index : Fin (cells side))
    (operation : DyadicOperation 20)
    (hoperation : operation ∈ cellOperations side index) : operation.Sound := by
  apply run.operationSound side operation
  rw [operations, List.mem_flatMap]
  exact ⟨index, by simp, hoperation⟩

theorem ReferenceCompiledRunVerdict.traceOperationSound
    (run : ReferenceCompiledRunVerdict)
    (side : ChapterVIDOuterArcSide) (index : Fin (cells side))
    (operation : DyadicOperation 20)
    (hoperation : operation ∈ (trace side index).operations) : operation.Sound := by
  apply run.cellOperationSound side index operation
  simp only [cellOperations, List.mem_append]
  exact Or.inl (Or.inr hoperation)

theorem ReferenceCompiledRunVerdict.coordinateOperationSound
    (run : ReferenceCompiledRunVerdict)
    (side : ChapterVIDOuterArcSide) (index : Fin (cells side))
    (operation : DyadicOperation 20)
    (hoperation : operation ∈
      (coordinateTrace side (meshIndex side index)).operations) : operation.Sound := by
  apply run.cellOperationSound side index operation
  simp only [cellOperations, List.mem_append]
  exact Or.inl (Or.inl hoperation)

/-- Semantic reconstruction of a derivative rectangle from one compiled row. -/
theorem ReferenceCompiledRunVerdict.derivativeProduct_contains
    (run : ReferenceCompiledRunVerdict)
    (side : ChapterVIDOuterArcSide) (index : Fin (cells side))
    {ζ u direction : ℂ}
    (hu : (coordinateTrace side (meshIndex side index)).output.Contains u)
    (hy : (radicandTrace side (meshIndex side index)).y.Contains
      (chapterVIDRootSecondAnomaly ζ u))
    (hdirection : (delta side).Contains direction) :
    (trace side index).output.Contains
      (chapterVIDRootCoordinateCollisionFactorPlusDerivative ζ u * direction) := by
  exact (trace side index).output_contains_of_allSound
    (run.traceOperationSound side index) hu hy
    ChapterVIDOuterArcPolarCompiledGrid.inverse10001_contains
    derivativeCoefficient_contains hdirection

/-- The compiled derivative row proves positive imaginary path derivative. -/
theorem ReferenceCompiledRunVerdict.derivativeProduct_im_pos
    (run : ReferenceCompiledRunVerdict)
    (side : ChapterVIDOuterArcSide) (index : Fin (cells side))
    {ζ u direction : ℂ}
    (hu : (coordinateTrace side (meshIndex side index)).output.Contains u)
    (hy : (radicandTrace side (meshIndex side index)).y.Contains
      (chapterVIDRootSecondAnomaly ζ u))
    (hdirection : (delta side).Contains direction) :
    0 < (chapterVIDRootCoordinateCollisionFactorPlusDerivative ζ u * direction).im := by
  have hcontains := run.derivativeProduct_contains side index hu hy hdirection
  have hsound := run.cellOperationSound side index
    (separationOperation (trace side index).output .imagPositive)
    (by simp [cellOperations])
  exact SlitPlaneSeparation.imagPositive.value_pos_of_lower_pos hcontains
    (by simpa [separationOperation, DyadicOperation.Sound] using hsound)

/-- The same compiled row keeps the nonvanishing companion factor in the positive half-plane. -/
theorem ReferenceCompiledRunVerdict.companion_re_pos
    (run : ReferenceCompiledRunVerdict)
    (side : ChapterVIDOuterArcSide) (index : Fin (cells side))
    {z : ℂ}
    (hz : (radicandTrace side (meshIndex side index)).factorMinus.Contains z) : 0 < z.re := by
  have hsound := run.cellOperationSound side index
    (separationOperation
      (radicandTrace side (meshIndex side index)).factorMinus .realPositive)
    (by simp [cellOperations])
  exact SlitPlaneSeparation.realPositive.value_pos_of_lower_pos hz
    (by simpa [separationOperation, DyadicOperation.Sound] using hsound)

/-- Every operation in the Cartesian radicand trace underlying a derivative row is sound. -/
theorem ReferenceCompiledRunVerdict.radicandOperationSound
    (run : ReferenceCompiledRunVerdict)
    (side : ChapterVIDOuterArcSide) (index : Fin (cells side))
    (operation : DyadicOperation 20)
    (hoperation : operation ∈
      (radicandTrace side (meshIndex side index)).operations) : operation.Sound := by
  apply run.traceOperationSound side index operation
  simp [trace, ChapterVILeanCompCertCartesianFactorDerivativeTrace.Trace.operations,
    hoperation]

/-- Every derivative row puts the actual companion collision factor in the positive real
half-plane. -/
theorem ReferenceCompiledRunVerdict.modelCompanion_re_pos
    {massProduct : ℂ} {b d : ℤ}
    (run : ReferenceCompiledRunVerdict)
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) (index : Fin (cells side))
    (point : I × I)
    (hregion : point ∈ meshRegion (meshIndex side index)) :
    0 < (model.rectangleFactorMinus side point).re := by
  let cell := (terminalCell model side (meshIndex side index)).toCoarseEndpointCell.toCell
  have hcellRegion : cell.region = meshRegion (meshIndex side index) := by
    cases side <;> rfl
  have hcoordinate : ∀ operation ∈ cell.coordinateOperations, operation.Sound := by
    intro operation hoperation
    apply run.coordinateOperationSound side index operation
    cases side <;> exact hoperation
  have htrace : ∀ operation ∈ cell.trace.operations, operation.Sound := by
    intro operation hoperation
    apply run.radicandOperationSound side index operation
    cases side <;> exact hoperation
  have hfactors := cell.factors_contain_of_allSound hcoordinate htrace point
    (by rw [hcellRegion]; exact hregion)
  apply run.companion_re_pos side index
  cases side <;> exact hfactors.2

/-- A compiled derivative row applies to the literal affine connector in the model.  In
particular, the coordinate, anomaly, and connector direction enclosures are reconstructed from
the row's checked line-map and Cartesian-radicand operations rather than accepted as premises. -/
theorem ReferenceCompiledRunVerdict.modelDerivative_im_pos
    {massProduct : ℂ} {b d : ℤ}
    (run : ReferenceCompiledRunVerdict)
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) (index : Fin (cells side))
    (point : I × I)
    (hregion : point ∈ meshRegion (meshIndex side index)) :
    0 < (chapterVIDRootCoordinateCollisionFactorPlusDerivative
        (model.connectorParameterRoot point.1) (model.rectanglePoint side point) *
      (model.rootModel.connectorTarget side (model.criticalValue point.1) -
        model.rootModel.connectorSource side (model.criticalValue point.1))).im := by
  let terminal := terminalCell model side (meshIndex side index)
  let affine := terminal.toCoarseEndpointCell.toAffineCell
  have haffineRegion : affine.region = meshRegion (meshIndex side index) := by
    cases side <;> rfl
  have haffineCoordinateOperations : affine.coordinateTrace.operations =
      (coordinateTrace side (meshIndex side index)).operations := by
    cases side <;> rfl
  have haffineCoordinateOutput : affine.coordinateTrace.output =
      (coordinateTrace side (meshIndex side index)).output := by
    cases side <;> rfl
  have haffineSource : affine.source = sourceRectangle side := by
    cases side <;> rfl
  have haffineTarget : affine.target = targetRectangle side := by
    cases side <;> rfl
  have hcoordinate : ∀ operation ∈ affine.coordinateTrace.operations, operation.Sound := by
    intro operation hoperation
    rw [haffineCoordinateOperations] at hoperation
    exact run.coordinateOperationSound side index operation hoperation
  have hu : (coordinateTrace side (meshIndex side index)).output.Contains
      (model.rectanglePoint side point) := by
    have hline := affine.coordinateTrace.output_contains_lineMap_of_allSound hcoordinate
      (affine.source_contains point (by rw [haffineRegion]; exact hregion))
      (affine.target_contains point (by rw [haffineRegion]; exact hregion))
      (affine.parameter_contains point (by rw [haffineRegion]; exact hregion))
    rw [haffineCoordinateOutput] at hline
    simpa [ChapterVIDPrincipalConnectorModel.rectanglePoint,
      ChapterVIDPrincipalGlobalRootModel.connectorPoint] using hline
  have hζ : ChapterVIDConnectorInputBounds.terminalZetaRectangle.Contains
      (model.connectorParameterRoot point.1) := by
    simpa [ChapterVIDPrincipalConnectorModel.connectorParameterRoot] using
      ChapterVIDConnectorInputBounds.terminalZetaRectangle_contains model point.1
  have hy : (radicandTrace side (meshIndex side index)).y.Contains
      (chapterVIDRootSecondAnomaly
        (model.connectorParameterRoot point.1) (model.rectanglePoint side point)) := by
    exact ((radicandTrace side (meshIndex side index)).anomalies_contain_of_allSound
      (run.radicandOperationSound side index) hζ hu
      ChapterVIDOuterArcPolarCompiledGrid.exponentialCoefficient_contains
      (model.connectorParameterRoot_ne_zero point.1)
      (model.rectanglePoint_ne_zero side point)).1
  have hdirection : (delta side).Contains
      (model.rootModel.connectorTarget side (model.criticalValue point.1) -
        model.rootModel.connectorSource side (model.criticalValue point.1)) := by
    have hsub := ChapterVISignedDyadicComplexRectangle.sub_contains
      (affine.target_contains point (by rw [haffineRegion]; exact hregion))
      (affine.source_contains point (by rw [haffineRegion]; exact hregion))
    rw [haffineTarget, haffineSource] at hsub
    exact hsub
  exact run.derivativeProduct_im_pos side index hu hy hdirection

/-- The compiled inequality is the derivative inequality for the actual real connector
parameter.  This packages the analytic differentiation theorem together with the checked row,
so downstream monotonicity arguments do not need to identify the interval expression by hand. -/
theorem ReferenceCompiledRunVerdict.modelLineImag_hasDerivAt_and_pos
    {massProduct : ℂ} {b d : ℤ}
    (run : ReferenceCompiledRunVerdict)
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) (index : Fin (cells side))
    (s t : I) (hregion : (s, t) ∈ meshRegion (meshIndex side index)) :
    let derivative :=
      (chapterVIDRootCoordinateCollisionFactorPlusDerivative
          (model.connectorParameterRoot s) (model.rectanglePoint side (s, t)) *
        (model.rootModel.connectorTarget side (model.criticalValue s) -
          model.rootModel.connectorSource side (model.criticalValue s))).im
    HasDerivAt
        (chapterVIDRootCoordinateCollisionFactorPlusLineImag
          (model.connectorParameterRoot s)
          (model.rootModel.connectorSource side (model.criticalValue s))
          (model.rootModel.connectorTarget side (model.criticalValue s)))
        derivative (t : ℝ) ∧
      0 < derivative := by
  dsimp only
  constructor
  · apply hasDerivAt_chapterVIDRootCoordinateCollisionFactorPlusLineImag
      (model.connectorParameterRoot_ne_zero s)
    simpa [ChapterVIDPrincipalConnectorModel.rectanglePoint,
      ChapterVIDPrincipalGlobalRootModel.connectorPoint] using
      model.rectanglePoint_ne_zero side (s, t)
  · exact run.modelDerivative_im_pos model side index (s, t) hregion

end PoincareChapterVI.ChapterVIDConnectorFactorDerivativeReference
