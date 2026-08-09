/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.ChapterVIDConnectorFactorBulkAdmissibility

/-!
# Sharded compiled certificate for the reference connector-factor mesh

The 1024-cell reference mesh is split into 32 artifacts of 32 cells on each connector side.
Lean checks only the unsigned-64-bit admissibility of each bounded shard.  The arithmetic verdict
comes from the exact LeanCompCert artifact, optionally through a hash-bound run receipt.  The
individual shard facts are then assembled into the semantic verdict expected by the connector
continuation theorem; no monolithic kernel evaluation or monolithic C artifact is used.
-/

noncomputable section

open scoped unitInterval

namespace PoincareChapterVI.ChapterVIDConnectorFactorBulkReference

open ChapterVILeanCompCertBatch
open ChapterVILeanCompCertAttestation
open ChapterVIDConnectorSeamCompiledGrid
open LeanCompCert.Ports.SignedProductClaims

/-- Every encoded interval operation contributes at most nine integer claims. -/
theorem operation_claims_length_le_nine (operation : DyadicOperation 20) :
    operation.claims.length ≤ 9 := by
  cases operation <;>
    simp [DyadicOperation.claims, ChapterVILeanCompCertIntervalBridge.mulClaims,
      ChapterVILeanCompCertIntervalBridge.positiveReciprocalClaims]

theorem batchClaims_length_le_nine_mul (operations : List (DyadicOperation 20)) :
    (batchClaims operations).length ≤ 9 * operations.length := by
  induction operations with
  | nil => simp [batchClaims]
  | cons operation rest ih =>
      rw [batchClaims, List.flatMap_cons, List.length_append]
      change operation.claims.length + (batchClaims rest).length ≤
        9 * (operation :: rest).length
      have hop := operation_claims_length_le_nine operation
      simp only [List.length_cons]
      omega

theorem referenceCellOperations_length (side : ChapterVIDOuterArcSide)
    (index : Fin meshCells) : (referenceCellOperations side index).length = 62 := by
  cases side <;> rfl

theorem referenceOperations_length (side : ChapterVIDOuterArcSide) :
    (referenceOperations side).length = 1024 * 62 := by
  rw [referenceOperations, List.length_flatMap]
  have hfun : (fun index : Fin meshCells ↦
      (referenceCellOperations side index).length) = Function.const _ 62 := by
    funext index
    exact referenceCellOperations_length side index
  rw [hfun, List.map_const, List.sum_replicate, List.length_finRange]
  norm_num [meshCells]

theorem referenceAnchor_admissible (side : ChapterVIDOuterArcSide) :
    Admissible (batchClaims (referenceAnchorOperations side)) := by
  cases side <;>
    refine ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

def referenceAnchorData
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) : FactorLocalAnchorData model side 20 where
  cell := anchorCell model side
  local_mem := anchorCell_local_mem model side
  admissible := by
    rw [anchorCell_operations model side]
    exact referenceAnchor_admissible side

theorem referenceAnchorData_operations
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) :
    (referenceAnchorData model side).operations = referenceAnchorOperations side := by
  exact anchorCell_operations model side

def anchorArtifactName (side : ChapterVIDOuterArcSide) : String :=
  s!"chapter_vi_connector_factor_{ChapterVIDOuterArcPolarCompiledGrid.sideName side}_anchor"

/-- The two exact local-endpoint anchor runs. -/
structure ReferenceAnchorCompiledRunVerdict : Prop where
  returnsZero : ∀ side,
    (batchComputation (anchorArtifactName side) (referenceAnchorOperations side)).Returns
      ((0 : Nat) : Int)

theorem ReferenceAnchorCompiledRunVerdict.ofReceipts
    (crypto : LeanCompCert.Attest.ReceiptCrypto)
    (receipt : ChapterVIDOuterArcSide → LeanCompCert.Attest.RunReceipt)
    (kind : ChapterVIDOuterArcSide → LeanCompCert.Attest.AttestationKind)
    (params nonce : ChapterVIDOuterArcSide → String)
    (bound : ∀ side,
      LeanCompCert.Attest.receiptBindsProved crypto
        (batchArtifact (anchorArtifactName side) (referenceAnchorOperations side))
        (kind side) (params side) (nonce side) ((0 : Nat) : Int) (receipt side) = true)
    (admitted : ∀ side,
      LeanCompCert.Attest.RunAdmission crypto
        (batchArtifact (anchorArtifactName side) (referenceAnchorOperations side))
        (receipt side)) : ReferenceAnchorCompiledRunVerdict where
  returnsZero side :=
    returns_zero_of_receipt (anchorArtifactName side) (referenceAnchorOperations side)
      crypto (receipt side) (kind side) (params side) (nonce side)
      (bound side) (admitted side)

theorem ReferenceAnchorCompiledRunVerdict.toFactorLocalAnchorRunVerdict
    (run : ReferenceAnchorCompiledRunVerdict)
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) :
    FactorLocalAnchorRunVerdict (anchorArtifactName side) (referenceAnchorData model side) := by
  constructor
  rw [referenceAnchorData_operations model side]
  exact run.returnsZero side

theorem ReferenceAnchorCompiledRunVerdict.exists_factorEndpointCollar
    (run : ReferenceAnchorCompiledRunVerdict)
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) : Nonempty (FactorEndpointCollar model side) :=
  exists_factorEndpointCollar_of_anchorRun
    (run.toFactorLocalAnchorRunVerdict model side)

/-- Shard admissibility implies admissibility of the assembled semantic batch.  The first two
fields are transported from the shard containing the claim; only the total claim-count bound is
evaluated globally. -/
theorem reference_admissible (side : ChapterVIDOuterArcSide) :
    Admissible (batchClaims (referenceOperations side)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro claim hclaim
    obtain ⟨shard, hshard⟩ := referenceClaim_mem_shard side claim hclaim
    exact (shard_admissible side shard).factors_lt claim hshard
  · intro claim hclaim
    obtain ⟨shard, hshard⟩ := referenceClaim_mem_shard side claim hclaim
    exact (shard_admissible side shard).products_lt claim hshard
  · have hlength := batchClaims_length_le_nine_mul (referenceOperations side)
    rw [referenceOperations_length side] at hlength
    exact hlength.trans_lt (by norm_num [LeanCompCert.Verified.Reflect.M])

/-- The concrete mathematical mesh, with machine-word safety discharged by the generated shard
proofs.  `hcutoff` remains visible because it is the quantitative analytic collar estimate, not
part of the finite computation. -/
def referenceData
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide)
    (collar : FactorEndpointCollar model side)
    (hcutoff : (collarCells : ℝ) / meshCells ≤ collar.width) :
    FactorBulkData model side collar 20 meshCells :=
  data model side collar hcutoff (reference_admissible side)

theorem referenceData_operations
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide)
    (collar : FactorEndpointCollar model side)
    (hcutoff : (collarCells : ℝ) / meshCells ≤ collar.width) :
    (referenceData model side collar hcutoff).operations = referenceOperations side := by
  change operations model side = referenceOperations side
  exact operations_eq_reference model side

/-- The external observations for the 64 bounded artifacts. -/
structure ReferenceCompiledRunVerdict : Prop where
  returnsZero : ∀ side shard,
    (batchComputation (shardArtifactName side shard)
      (referenceShardOperations side shard)).Returns ((0 : Nat) : Int)

/-- A family of receipts for the exact Lean-derived shard artifacts yields the complete compiled
run verdict.  `RunAdmission` is intentionally explicit and records the empirical execution
premise for each artifact. -/
theorem ReferenceCompiledRunVerdict.ofReceipts
    (crypto : LeanCompCert.Attest.ReceiptCrypto)
    (receipt : (side : ChapterVIDOuterArcSide) → Fin shardCount →
      LeanCompCert.Attest.RunReceipt)
    (kind : (side : ChapterVIDOuterArcSide) → Fin shardCount →
      LeanCompCert.Attest.AttestationKind)
    (params nonce : (side : ChapterVIDOuterArcSide) → Fin shardCount → String)
    (bound : ∀ side shard,
      LeanCompCert.Attest.receiptBindsProved crypto
        (batchArtifact (shardArtifactName side shard)
          (referenceShardOperations side shard))
        (kind side shard) (params side shard) (nonce side shard) ((0 : Nat) : Int)
        (receipt side shard) = true)
    (admitted : ∀ side shard,
      LeanCompCert.Attest.RunAdmission crypto
        (batchArtifact (shardArtifactName side shard)
          (referenceShardOperations side shard))
        (receipt side shard)) :
    ReferenceCompiledRunVerdict where
  returnsZero side shard :=
    returns_zero_of_receipt (shardArtifactName side shard)
      (referenceShardOperations side shard) crypto (receipt side shard)
      (kind side shard) (params side shard) (nonce side shard)
      (bound side shard) (admitted side shard)

theorem ReferenceCompiledRunVerdict.operationSound
    (run : ReferenceCompiledRunVerdict)
    (side : ChapterVIDOuterArcSide) (operation : DyadicOperation 20)
    (hoperation : operation ∈ referenceOperations side) : operation.Sound := by
  rw [referenceOperations, List.mem_flatMap] at hoperation
  obtain ⟨index, _, hcell⟩ := hoperation
  obtain ⟨shard, hshard⟩ := referenceCellOperations_mem_shard side index operation hcell
  exact allSound_of_returns_zero (shardArtifactName side shard)
    (referenceShardOperations side shard) (shard_admissible side shard)
    (run.returnsZero side shard) operation hshard

theorem ReferenceCompiledRunVerdict.cellOperationSound
    (run : ReferenceCompiledRunVerdict)
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) (index : Fin meshCells)
    (operation : DyadicOperation 20)
    (hoperation : operation ∈ cellOperations model side index) : operation.Sound := by
  apply run.operationSound side operation
  rw [referenceOperations, List.mem_flatMap]
  refine ⟨index, by simp, ?_⟩
  rw [← cellOperations_eq_reference]
  exact hoperation

/-- Semantic collision-factor reconstruction for any row of the sharded direct campaign. -/
theorem ReferenceCompiledRunVerdict.cell_facts
    (run : ReferenceCompiledRunVerdict)
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) (index : Fin meshCells)
    (point : I × I) (hregion : point ∈ (cell model side index).region) :
    (0 < (plusSeparation side index).value (model.rectangleFactorPlus side point)) ∧
      0 < (minusSeparation side index).value (model.rectangleFactorMinus side point) := by
  let selected := cell model side index
  have hcoordinate : ∀ operation ∈ selected.coordinateOperations, operation.Sound := by
    intro operation hoperation
    apply run.cellOperationSound model side index operation
    simp [cellOperations, selected, hoperation]
  have htrace : ∀ operation ∈ selected.trace.operations, operation.Sound := by
    intro operation hoperation
    apply run.cellOperationSound model side index operation
    simp [cellOperations, selected, hoperation]
  have hplusSound := run.cellOperationSound model side index
    (separationOperation selected.trace.factorPlus (plusSeparation side index))
    (by simp [cellOperations, selected])
  have hminusSound := run.cellOperationSound model side index
    (separationOperation selected.trace.factorMinus (minusSeparation side index))
    (by simp [cellOperations, selected])
  have hcontains := selected.factors_contain_of_allSound hcoordinate htrace point hregion
  exact ⟨(plusSeparation side index).value_pos_of_lower_pos hcontains.1 hplusSound,
    (minusSeparation side index).value_pos_of_lower_pos hcontains.2 hminusSound⟩

def assembledArtifactName (side : ChapterVIDOuterArcSide) : String :=
  s!"chapter_vi_connector_factor_{ChapterVIDOuterArcPolarCompiledGrid.sideName side}_assembled"

/-- Assemble the shard results into the existing factor-bulk interface.  The assembled
computation is proved to return zero from the individual semantic certificates; it is not emitted
or run as a second, giant artifact. -/
theorem ReferenceCompiledRunVerdict.toFactorBulkRunVerdict
    (run : ReferenceCompiledRunVerdict)
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide)
    (collar : FactorEndpointCollar model side)
    (hcutoff : (collarCells : ℝ) / meshCells ≤ collar.width) :
    FactorBulkRunVerdict (assembledArtifactName side)
      (referenceData model side collar hcutoff) := by
  apply FactorBulkRunVerdict.ofAllSound
  intro operation hoperation
  rw [referenceData_operations model side collar hcutoff] at hoperation
  exact run.operationSound side operation hoperation

end PoincareChapterVI.ChapterVIDConnectorFactorBulkReference
