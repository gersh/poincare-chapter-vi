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
  exact List.mem_append_left _ hoperation

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

end PoincareChapterVI.ChapterVIDConnectorFactorDerivativeReference
