/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.ChapterVIDConnectorFactorSecondDerivativeAdmissibility
import PoincareChapterVI.ChapterVILeanCompCertAttestation

/-!
# Sharded compiled certificate for terminal connector curvature

Ten three-cell artifacts cover the 30 cells omitted by the first-derivative campaign.  A zero
compiled verdict reconstructs the literal value of `f''(u) * Δ²`, proves negative imaginary
curvature on the initial side and positive imaginary curvature on the final side, keeps the
companion factor in the positive real half-plane, and identifies the curvature value as the
derivative of the actual affine path derivative.
-/

noncomputable section

open scoped unitInterval

namespace PoincareChapterVI.ChapterVIDConnectorFactorSecondDerivativeReference

open ChapterVILeanCompCertBatch
open ChapterVILeanCompCertAttestation
open ChapterVILeanCompCertCartesianFactorSecondDerivativeTrace
open ChapterVIDConnectorFactorBulkReference
open ChapterVIDConnectorSeamCompiledGrid
open LeanCompCert.Ports.SignedProductClaims

/-- External execution observations for the ten bounded curvature artifacts. -/
structure ReferenceCompiledRunVerdict : Prop where
  returnsZero : ∀ side shard,
    (batchComputation (shardArtifactName side shard)
      (shardOperations side shard)).Returns ((0 : Nat) : Int)

/-- Unconditional verified-program verdict for all second-derivative shards. -/
theorem referenceRunVerdict : ReferenceCompiledRunVerdict where
  returnsZero side shard :=
    ChapterVILeanCompCertIntervalBridge.returns_zero_of_allHold
      (shardArtifactName side shard) (batchClaims (shardOperations side shard))
      (shard_admissible side shard) (shard_allHold side shard)

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
  simp [cellOperations, hoperation]

theorem ReferenceCompiledRunVerdict.coordinateOperationSound
    (run : ReferenceCompiledRunVerdict)
    (side : ChapterVIDOuterArcSide) (index : Fin (cells side))
    (operation : DyadicOperation 20)
    (hoperation : operation ∈
      (coordinateTrace side (meshIndex side index)).operations) : operation.Sound := by
  apply run.cellOperationSound side index operation
  simp [cellOperations, hoperation]

theorem ReferenceCompiledRunVerdict.radicandOperationSound
    (run : ReferenceCompiledRunVerdict)
    (side : ChapterVIDOuterArcSide) (index : Fin (cells side))
    (operation : DyadicOperation 20)
    (hoperation : operation ∈
      (radicandTrace side (meshIndex side index)).operations) : operation.Sound := by
  apply run.traceOperationSound side index operation
  simp [trace,
    ChapterVILeanCompCertCartesianFactorSecondDerivativeTrace.Trace.operations,
    hoperation]

/-- Semantic reconstruction of one compiled curvature rectangle. -/
theorem ReferenceCompiledRunVerdict.curvature_contains
    (run : ReferenceCompiledRunVerdict)
    (side : ChapterVIDOuterArcSide) (index : Fin (cells side))
    {ζ u direction : ℂ}
    (hu : (coordinateTrace side (meshIndex side index)).output.Contains u)
    (hy : (radicandTrace side (meshIndex side index)).y.Contains
      (chapterVIDRootSecondAnomaly ζ u))
    (hdirection : (delta side).Contains direction) :
    (trace side index).output.Contains
      (chapterVIDRootCoordinateCollisionFactorPlusSecondDerivative ζ u * direction ^ 2) := by
  exact (trace side index).output_contains_of_allSound
    (run.traceOperationSound side index) hu hy
    ChapterVIDOuterArcPolarCompiledGrid.inverse10001_contains
    logCoefficient_contains secondCoefficient_contains hdirection

/-- The compiled row gives the side-oriented strict sign of affine curvature. -/
theorem ReferenceCompiledRunVerdict.curvature_separated
    (run : ReferenceCompiledRunVerdict)
    (side : ChapterVIDOuterArcSide) (index : Fin (cells side))
    {ζ u direction : ℂ}
    (hu : (coordinateTrace side (meshIndex side index)).output.Contains u)
    (hy : (radicandTrace side (meshIndex side index)).y.Contains
      (chapterVIDRootSecondAnomaly ζ u))
    (hdirection : (delta side).Contains direction) :
    0 < (separation side).value
      (chapterVIDRootCoordinateCollisionFactorPlusSecondDerivative ζ u * direction ^ 2) := by
  have hcontains := run.curvature_contains side index hu hy hdirection
  have hsound := run.cellOperationSound side index
    (separationOperation (trace side index).output (separation side))
    (by simp [cellOperations])
  exact (separation side).value_pos_of_lower_pos hcontains
    (by simpa [separationOperation, DyadicOperation.Sound] using hsound)

/-- The same terminal row keeps the companion collision factor in the positive real half-plane. -/
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

/-- A compiled curvature row applies to the literal affine connector in the selected model. -/
theorem ReferenceCompiledRunVerdict.modelCurvature_separated
    {massProduct : ℂ} {b d : ℤ}
    (run : ReferenceCompiledRunVerdict)
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) (index : Fin (cells side))
    (point : I × I)
    (hregion : point ∈ ChapterVIDConnectorFactorBulkReference.meshRegion
      (meshIndex side index)) :
    0 < (separation side).value
      (chapterVIDRootCoordinateCollisionFactorPlusSecondDerivative
        (model.connectorParameterRoot point.1) (model.rectanglePoint side point) *
        (model.rootModel.connectorTarget side (model.criticalValue point.1) -
          model.rootModel.connectorSource side (model.criticalValue point.1)) ^ 2) := by
  let terminal := ChapterVIDConnectorFactorBulkReference.terminalCell
    model side (meshIndex side index)
  let affine := terminal.toCoarseEndpointCell.toAffineCell
  have haffineRegion : affine.region =
      ChapterVIDConnectorFactorBulkReference.meshRegion (meshIndex side index) := by
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
  exact run.curvature_separated side index hu hy hdirection

/-- A compiled terminal row puts the actual companion collision factor in the positive real
half-plane.  The proof reconstructs both the affine coordinate and the reciprocal anomaly from
the checked row before applying the row's separation claim. -/
theorem ReferenceCompiledRunVerdict.modelCompanion_re_pos
    {massProduct : ℂ} {b d : ℤ}
    (run : ReferenceCompiledRunVerdict)
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) (index : Fin (cells side))
    (point : I × I)
    (hregion : point ∈ ChapterVIDConnectorFactorBulkReference.meshRegion
      (meshIndex side index)) :
    0 < (model.rectangleFactorMinus side point).re := by
  let terminal := ChapterVIDConnectorFactorBulkReference.terminalCell
    model side (meshIndex side index)
  let affine := terminal.toCoarseEndpointCell.toAffineCell
  have haffineRegion : affine.region =
      ChapterVIDConnectorFactorBulkReference.meshRegion (meshIndex side index) := by
    cases side <;> rfl
  have haffineCoordinateOperations : affine.coordinateTrace.operations =
      (coordinateTrace side (meshIndex side index)).operations := by
    cases side <;> rfl
  have haffineCoordinateOutput : affine.coordinateTrace.output =
      (coordinateTrace side (meshIndex side index)).output := by
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
  have hanomalies :=
    (radicandTrace side (meshIndex side index)).anomalies_contain_of_allSound
      (run.radicandOperationSound side index) hζ hu
      ChapterVIDOuterArcPolarCompiledGrid.exponentialCoefficient_contains
      (model.connectorParameterRoot_ne_zero point.1)
      (model.rectanglePoint_ne_zero side point)
  have hfactors :=
    (radicandTrace side (meshIndex side index)).factors_contain_sparse_of_allSound
      (run.radicandOperationSound side index) hu
      ChapterVIDOuterArcPolarCompiledGrid.inverse10001_contains
      hanomalies.1 hanomalies.2
  apply run.companion_re_pos side index
  rw [show model.rectangleFactorMinus side point =
        chapterVIDRootCoordinateCollisionFactorMinus
          (model.connectorParameterRoot point.1) (model.rectanglePoint side point) by rfl,
      chapterVIDRootCoordinateCollisionFactorMinus_eq_polarCertificateFormula
        (model.connectorParameterRoot_ne_zero point.1)
        (model.rectanglePoint_ne_zero side point)]
  exact hfactors.2

/-- The compiled value is the derivative of the actual path derivative, with the expected
opposite curvature orientations on the two connector sides. -/
theorem ReferenceCompiledRunVerdict.modelLineDerivativeImag_hasDerivAt_and_oriented
    {massProduct : ℂ} {b d : ℤ}
    (run : ReferenceCompiledRunVerdict)
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) (index : Fin (cells side))
    (s t : I)
    (hregion : (s, t) ∈ ChapterVIDConnectorFactorBulkReference.meshRegion
      (meshIndex side index)) :
    let curvature :=
      (chapterVIDRootCoordinateCollisionFactorPlusSecondDerivative
        (model.connectorParameterRoot s) (model.rectanglePoint side (s, t)) *
        (model.rootModel.connectorTarget side (model.criticalValue s) -
          model.rootModel.connectorSource side (model.criticalValue s)) ^ 2).im
    HasDerivAt
      (chapterVIDRootCoordinateCollisionFactorPlusLineDerivativeImag
        (model.connectorParameterRoot s)
        (model.rootModel.connectorSource side (model.criticalValue s))
        (model.rootModel.connectorTarget side (model.criticalValue s)))
      curvature (t : ℝ) ∧
      match side with
      | .initial => curvature < 0
      | .final => 0 < curvature := by
  dsimp only
  constructor
  · apply hasDerivAt_chapterVIDRootCoordinateCollisionFactorPlusLineDerivativeImag
    simpa [ChapterVIDPrincipalConnectorModel.rectanglePoint,
      ChapterVIDPrincipalGlobalRootModel.connectorPoint] using
      model.rectanglePoint_ne_zero side (s, t)
  · have hsign := run.modelCurvature_separated model side index (s, t) hregion
    cases side with
    | initial =>
        change 0 < -(
          chapterVIDRootCoordinateCollisionFactorPlusSecondDerivative
            (model.connectorParameterRoot s) (model.rectanglePoint .initial (s, t)) *
            (model.rootModel.connectorTarget .initial (model.criticalValue s) -
              model.rootModel.connectorSource .initial (model.criticalValue s)) ^ 2).im at hsign
        linarith
    | final =>
        simpa only [separation, SlitPlaneSeparation.value,
          SlitPlaneSeparation.toZeroSeparation,
          ChapterVIComplexZeroSeparation.value] using hsign

end PoincareChapterVI.ChapterVIDConnectorFactorSecondDerivativeReference
