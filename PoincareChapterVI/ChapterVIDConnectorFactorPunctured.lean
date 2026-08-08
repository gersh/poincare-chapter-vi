/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.ChapterVIDConnectorSeamCompiledGrid

/-!
# Compiled connector-factor campaigns with no quantitative collar premise

The endpoint factor margin is proportional to the (existentially chosen) Morse length `L`.
Consequently no fixed dyadic width can be inferred from continuity alone.  The scalable
certificate interface should instead cover the punctured seam: every point except the exact
local endpoint is checked by compiled factor cells, while the endpoint itself is handled by the
existing exact Morse identity and compiled companion-factor anchor.

This file records that interface and reduces it to the already-proved hybrid continuation
theorem.  A continuity collar is still selected internally, but its width is never exposed to,
or assumed by, the compiled campaign.  Thus a future scale-aware terminal campaign can be joined
to the passing fixed bulk campaign without asserting an unjustified numerical lower bound on the
collar.
-/

noncomputable section

open Set Topology
open scoped unitInterval

namespace PoincareChapterVI
namespace ChapterVIDConnectorFactorPunctured

open ChapterVILeanCompCertBatch
open ChapterVILeanCompCertAttestation
open LeanCompCert.Ports.SignedProductClaims
open ChapterVIDConnectorCompiledGrid
open ChapterVIDConnectorSeamCompiledGrid

/-- Factor-wise compiled cells covering every seam point except the exact local endpoint.

Unlike `FactorBulkData`, this structure contains no collar and hence no numerical comparison
between a dyadic cutoff and an existential continuity radius. -/
structure Data
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) (precision cells : ℕ) where
  cell : Fin cells → ChapterVIDConnectorCompiledGrid.Cell model side precision
  plusSeparation : Fin cells → SlitPlaneSeparation
  minusSeparation : Fin cells → SlitPlaneSeparation
  covers : ∀ t : I, t ≠ localParameter side →
    ∃ index, connectorPathPoint model t ∈ (cell index).region
  outerIndex : Fin cells
  outer_mem : connectorPathPoint model (outerParameter side) ∈ (cell outerIndex).region
  outer_plus : plusSeparation outerIndex = outerPlusSeparation side
  outer_minus : minusSeparation outerIndex = outerMinusSeparation side
  admissible : Admissible (batchClaims
    ((List.finRange cells).flatMap fun index ↦
      (cell index).coordinateOperations ++ (cell index).trace.operations ++
        [separationOperation (cell index).trace.factorPlus (plusSeparation index),
          separationOperation (cell index).trace.factorMinus (minusSeparation index)]))

def Data.cellOperations
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide} {precision cells : ℕ}
    (data : Data model side precision cells) (index : Fin cells) :
    List (DyadicOperation precision) :=
  (data.cell index).coordinateOperations ++ (data.cell index).trace.operations ++
    [separationOperation (data.cell index).trace.factorPlus (data.plusSeparation index),
      separationOperation (data.cell index).trace.factorMinus (data.minusSeparation index)]

def Data.operations
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide} {precision cells : ℕ}
    (data : Data model side precision cells) : List (DyadicOperation precision) :=
  (List.finRange cells).flatMap data.cellOperations

/-- A zero verdict for the exact punctured-seam batch. -/
structure RunVerdict
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide} {precision cells : ℕ}
    (name : String) (data : Data model side precision cells) : Prop where
  returnsZero : (batchComputation name data.operations).Returns ((0 : Nat) : Int)

theorem RunVerdict.ofAllSound
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide} {precision cells : ℕ}
    (name : String) (data : Data model side precision cells)
    (hall : ∀ operation ∈ data.operations, operation.Sound) :
    RunVerdict name data :=
  ⟨returns_zero_of_allSound name data.operations data.admissible hall⟩

/-- Forgetting punctured coverage gives valid bulk data for *any* positive endpoint collar.
The crucial implication is purely metric: a point outside a positive-width collar cannot be the
endpoint. -/
def Data.toFactorBulkData
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide} {precision cells : ℕ}
    (data : Data model side precision cells)
    (collar : FactorEndpointCollar model side) :
    FactorBulkData model side collar precision cells where
  cell := data.cell
  plusSeparation := data.plusSeparation
  minusSeparation := data.minusSeparation
  covers := by
    intro t hdist
    apply data.covers t
    intro heq
    subst t
    simp only [dist_self] at hdist
    exact (not_le_of_gt collar.width_pos) hdist
  outerIndex := data.outerIndex
  outer_mem := data.outer_mem
  outer_plus := data.outer_plus
  outer_minus := data.outer_minus
  admissible := data.admissible

theorem RunVerdict.toFactorBulkRunVerdict
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide} {precision cells : ℕ}
    {name : String} {data : Data model side precision cells}
    (run : RunVerdict name data)
    (collar : FactorEndpointCollar model side) :
    FactorBulkRunVerdict name (data.toFactorBulkData collar) := by
  have hcell : (data.toFactorBulkData collar).cellOperations = data.cellOperations := by
    funext index
    rfl
  have hoperations : (data.toFactorBulkData collar).operations = data.operations := by
    unfold FactorBulkData.operations Data.operations
    rw [hcell]
  constructor
  rw [hoperations]
  exact run.returnsZero

/-- Receipt constructor for an attested CompCert execution of the punctured campaign. -/
theorem RunVerdict.ofReceipt
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide} {precision cells : ℕ}
    (name : String) (data : Data model side precision cells)
    (crypto : LeanCompCert.Attest.ReceiptCrypto)
    (receipt : LeanCompCert.Attest.RunReceipt)
    (kind : LeanCompCert.Attest.AttestationKind) (params nonce : String)
    (bound : LeanCompCert.Attest.receiptBindsProved crypto
      (batchArtifact name data.operations) kind params nonce ((0 : Nat) : Int) receipt = true)
    (admitted : LeanCompCert.Attest.RunAdmission crypto
      (batchArtifact name data.operations) receipt) :
    RunVerdict name data :=
  ⟨returns_zero_of_receipt name data.operations crypto receipt kind params nonce bound admitted⟩

/-- End-to-end connector theorem with no quantitative collar hypothesis.  Endpoint anchors
produce some positive continuity collars; punctured campaigns automatically cover the complement
of whichever collars Lean selects. -/
theorem exists_seamCompatibleContribution_tendsto_of_puncturedCertificates
    (outerRun : ChapterVIDOuterArcPolarCompiledGrid.CompiledRunVerdict)
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (initialCertificate : ChapterVIDConnectorCompiledCertificate model .initial)
    (finalCertificate : ChapterVIDConnectorCompiledCertificate model .final)
    {initialAnchorPrecision finalAnchorPrecision : ℕ}
    {initialAnchorName finalAnchorName : String}
    {initialAnchorData : FactorLocalAnchorData model .initial initialAnchorPrecision}
    {finalAnchorData : FactorLocalAnchorData model .final finalAnchorPrecision}
    (initialAnchorRun : FactorLocalAnchorRunVerdict initialAnchorName initialAnchorData)
    (finalAnchorRun : FactorLocalAnchorRunVerdict finalAnchorName finalAnchorData)
    {initialPrecision initialCells finalPrecision finalCells : ℕ}
    {initialName finalName : String}
    {initialData : Data model .initial initialPrecision initialCells}
    {finalData : Data model .final finalPrecision finalCells}
    (initialRun : RunVerdict initialName initialData)
    (finalRun : RunVerdict finalName finalData) :
    ∃ compatible :
        ChapterVIDPrincipalConnectorModel.SeamCompatibleCertifiedConnectorPair outerRun model,
      Filter.Tendsto
        (fun k : ℝ ↦ (-Real.log k)⁻¹ • compatible.fivePieceContribution k)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds ((2 * Real.pi * Complex.I : ℂ)⁻¹ *
          chapterVIDPrincipalMorseAmplitude massProduct b d (0, 0))) := by
  obtain ⟨initialCollar⟩ :=
    exists_factorEndpointCollar_of_anchorRun initialAnchorRun
  obtain ⟨finalCollar⟩ :=
    exists_factorEndpointCollar_of_anchorRun finalAnchorRun
  exact exists_seamCompatibleContribution_tendsto_of_factorBulkCertificates
    outerRun model initialCertificate finalCertificate
    (initialRun.toFactorBulkRunVerdict initialCollar)
    (finalRun.toFactorBulkRunVerdict finalCollar)

end ChapterVIDConnectorFactorPunctured
end PoincareChapterVI
