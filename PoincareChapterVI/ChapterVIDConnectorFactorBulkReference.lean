/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.ChapterVIDConnectorSeamCompiledGrid
import PoincareChapterVI.ChapterVIUnitSquareGrid

/-!
# Concrete reference mesh for the factor-wise connector batches

This module turns the passing `1024 / 261` reference campaign into pure Lean data.  Trace
construction is total: every analytic precondition and rounded-arithmetic condition is an
operation in the compiled batch.  The only deliberately explicit mathematical hypothesis is
that the factor collar has width at least `261 / 1024`.
-/

noncomputable section

open Set
open scoped unitInterval

namespace PoincareChapterVI.ChapterVIDConnectorFactorBulkReference

open ChapterVILeanCompCertProposals
open ChapterVILeanCompCertBatch
open ChapterVIDConnectorCompiledGrid
open ChapterVIDConnectorSeamCompiledGrid
open LeanCompCert.Ports.SignedProductClaims

abbrev Interval := ChapterVISignedDyadicInterval 20
abbrev Rectangle := ChapterVISignedDyadicComplexRectangle 20

def meshCells : ℕ := 1024
def collarCells : ℕ := 261
def initialLastMeshIndex : ℕ := 762
def finalFirstMeshIndex : ℕ := 261

def parameterInterval (index : Fin meshCells) : Interval :=
  ⟨(index.val * 1024 : ℕ), ((index.val + 1) * 1024 : ℕ)⟩

def meshRegion (index : Fin meshCells) : Set (I × I) :=
  {point | point.1 = 0 ∧ point.2 ∈ chapterVIUnitGridCell 1023
    ⟨index.val, by
      have hi := index.isLt
      change index.val < 1024 at hi
      omega⟩}

theorem parameterInterval_contains_of_mem_meshRegion
    (index : Fin meshCells) (point : I × I) (hpoint : point ∈ meshRegion index) :
    (parameterInterval index).Contains (point.2 : ℝ) := by
  rcases hpoint with ⟨_, hlower, hupper⟩
  have hsucc : index.val + 1 ≤ 1024 := by
    have := index.isLt
    simp only [meshCells] at this
    omega
  rw [min_eq_left hsucc] at hupper
  change ((index.val * 1024 : ℕ) : ℝ) / (2 : ℝ) ^ 20 ≤ (point.2 : ℝ) ∧
    (point.2 : ℝ) ≤ (((index.val + 1) * 1024 : ℕ) : ℝ) / (2 : ℝ) ^ 20
  constructor
  · convert hlower using 1 <;> norm_num <;> ring
  · convert hupper using 1 <;> norm_num <;> ring

def rawMeshIndex (t : I) : Fin meshCells :=
  ⟨min (chapterVIUnitGridIndex 1023 t).val 1023, by
    simp only [meshCells]
    omega⟩

theorem rawMeshIndex_mem (t : I) :
    t ∈ chapterVIUnitGridCell 1023
      ⟨(rawMeshIndex t).val, by
        have hi := (rawMeshIndex t).isLt
        change (rawMeshIndex t).val < 1024 at hi
        omega⟩ := by
  have hcell := chapterVIUnitGridIndex_mem_cell 1023 t
  let k := (chapterVIUnitGridIndex 1023 t).val
  by_cases hk : k ≤ 1023
  · have hmin : min k 1023 = k := min_eq_left hk
    simpa [rawMeshIndex, k, hmin] using hcell
  · have hkEq : k = 1024 := by
      have hkLt := (chapterVIUnitGridIndex 1023 t).isLt
      omega
    have ht : (t : ℝ) = 1 := by
      rcases hcell with ⟨hlower, _⟩
      change (k : ℝ) / 1024 ≤ (t : ℝ) at hlower
      rw [hkEq] at hlower
      norm_num at hlower
      exact le_antisymm t.property.2 hlower
    have htSubtype : t = 1 := Subtype.ext ht
    subst t
    simp [chapterVIUnitGridCell, rawMeshIndex, k, hkEq]
    norm_num

def bulkMeshIndex (side : ChapterVIDOuterArcSide) (t : I) : Fin meshCells :=
  match side with
  | .initial => ⟨min (rawMeshIndex t).val initialLastMeshIndex, by
      simp only [meshCells, initialLastMeshIndex]
      omega⟩
  | .final => ⟨max (rawMeshIndex t).val finalFirstMeshIndex, by
      have hraw := (rawMeshIndex t).isLt
      simp only [meshCells, finalFirstMeshIndex] at hraw ⊢
      omega⟩

theorem dist_localParameter_eq (side : ChapterVIDOuterArcSide) (t : I) :
    dist t (localParameter side) =
      match side with
      | .initial => 1 - (t : ℝ)
      | .final => (t : ℝ) := by
  cases side with
  | initial =>
      rw [Subtype.dist_eq, Real.dist_eq]
      change |(t : ℝ) - 1| = 1 - (t : ℝ)
      rw [abs_of_nonpos]
      · ring
      · linarith [t.property.2]
  | final =>
      rw [Subtype.dist_eq, Real.dist_eq]
      change |(t : ℝ) - 0| = (t : ℝ)
      rw [abs_of_nonneg]
      · ring
      · simpa only [sub_zero] using t.property.1

theorem connectorPathPoint_mem_bulkMeshIndex
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) (t : I)
    (hbulk : (collarCells : ℝ) / meshCells ≤ dist t (localParameter side)) :
    connectorPathPoint model t ∈ meshRegion (bulkMeshIndex side t) := by
  constructor
  · rfl
  · have hraw := rawMeshIndex_mem t
    cases side with
    | initial =>
        simp only [dist_localParameter_eq, collarCells, meshCells] at hbulk
        rcases hraw with ⟨hrawLower, hrawUpper⟩
        simp only [bulkMeshIndex]
        by_cases hindex : (rawMeshIndex t).val ≤ initialLastMeshIndex
        · simpa [min_eq_left hindex] using ⟨hrawLower, hrawUpper⟩
        · have hmin : min (rawMeshIndex t).val initialLastMeshIndex =
              initialLastMeshIndex := min_eq_right (le_of_not_ge hindex)
          simp only [chapterVIUnitGridCell]
          change
            ((min (rawMeshIndex t).val initialLastMeshIndex : ℕ) : ℝ) / 1024 ≤
                (t : ℝ) ∧
              (t : ℝ) ≤
                ((min (min (rawMeshIndex t).val initialLastMeshIndex + 1) 1024 : ℕ) : ℝ) /
                  1024
          rw [hmin]
          norm_num [initialLastMeshIndex]
          constructor
          · change ((rawMeshIndex t).val : ℝ) / 1024 ≤ (t : ℝ) at hrawLower
            have : 763 ≤ (rawMeshIndex t).val := by
              simp only [initialLastMeshIndex] at hindex
              omega
            have hreal : (763 : ℝ) ≤ (rawMeshIndex t).val := by exact_mod_cast this
            nlinarith
          · norm_num at hbulk ⊢
            nlinarith
    | final =>
        simp only [dist_localParameter_eq, collarCells, meshCells] at hbulk
        rcases hraw with ⟨hrawLower, hrawUpper⟩
        simp only [bulkMeshIndex]
        by_cases hindex : finalFirstMeshIndex ≤ (rawMeshIndex t).val
        · simpa [max_eq_left hindex] using ⟨hrawLower, hrawUpper⟩
        · have hlt : (rawMeshIndex t).val < finalFirstMeshIndex := by omega
          have hsuccRaw : (rawMeshIndex t).val + 1 ≤ 1024 := by
            have hi := (rawMeshIndex t).isLt
            change (rawMeshIndex t).val < 1024 at hi
            omega
          rw [min_eq_left hsuccRaw] at hrawUpper
          change (t : ℝ) ≤ ((rawMeshIndex t).val + 1 : ℕ) / 1024 at hrawUpper
          simp only [finalFirstMeshIndex] at hlt
          have : (rawMeshIndex t).val + 1 ≤ 261 := by omega
          have hreal : (((rawMeshIndex t).val + 1 : ℕ) : ℝ) ≤ 261 := by
            exact_mod_cast this
          simp only [chapterVIUnitGridCell]
          change
            ((max (rawMeshIndex t).val finalFirstMeshIndex : ℕ) : ℝ) / 1024 ≤
                (t : ℝ) ∧
              (t : ℝ) ≤
                ((min (max (rawMeshIndex t).val finalFirstMeshIndex + 1) 1024 : ℕ) : ℝ) /
                  1024
          rw [max_eq_right (le_of_not_ge hindex)]
          norm_num [finalFirstMeshIndex] at hbulk hrawUpper ⊢
          constructor
          · exact hbulk
          · have hdiv :
                (((rawMeshIndex t).val + 1 : ℕ) : ℝ) / 1024 ≤ (261 : ℝ) / 1024 :=
              div_le_div_of_nonneg_right hreal (by norm_num)
            have hdiv' :
                (((rawMeshIndex t).val : ℝ) + 1) / 1024 ≤ (261 : ℝ) / 1024 := by
              simpa only [Nat.cast_add, Nat.cast_one] using hdiv
            have ht261 := hrawUpper.trans hdiv'
            norm_num at ht261 ⊢
            linarith

def retainedMeshIndex (side : ChapterVIDOuterArcSide)
    (index : Fin meshCells) : Fin meshCells :=
  match side with
  | .initial => ⟨min index.val initialLastMeshIndex, by
      simp only [meshCells, initialLastMeshIndex]
      omega⟩
  | .final => ⟨max index.val finalFirstMeshIndex, by
      have hi := index.isLt
      simp only [meshCells, finalFirstMeshIndex] at hi ⊢
      omega⟩

theorem retainedMeshIndex_bulkMeshIndex
    (side : ChapterVIDOuterArcSide) (t : I) :
    retainedMeshIndex side (bulkMeshIndex side t) = bulkMeshIndex side t := by
  apply Fin.ext
  cases side with
  | initial =>
      simp [retainedMeshIndex, bulkMeshIndex, initialLastMeshIndex,
        finalFirstMeshIndex, min_assoc]
  | final =>
      simp [retainedMeshIndex, bulkMeshIndex, initialLastMeshIndex,
        finalFirstMeshIndex, max_assoc]

def sourceRectangle (side : ChapterVIDOuterArcSide) : Rectangle :=
  coarseSourceRectangle side
    (ChapterVIDConnectorInputBounds.terminalOuterRectangle side)

def targetRectangle (side : ChapterVIDOuterArcSide) : Rectangle :=
  coarseTargetRectangle side
    (ChapterVIDConnectorInputBounds.terminalOuterRectangle side)

def coordinateTrace (side : ChapterVIDOuterArcSide) (index : Fin meshCells) :=
  lineMapTrace (sourceRectangle side) (targetRectangle side) (parameterInterval index)

def radicandTrace (side : ChapterVIDOuterArcSide) (index : Fin meshCells) :=
  cartesianRadicandTrace ChapterVIDConnectorInputBounds.terminalZetaRectangle
    (coordinateTrace side index).output
    ChapterVIDOuterArcPolarCompiledGrid.exponentialCoefficient
    ChapterVIDOuterArcPolarCompiledGrid.inverse10001

/-- Total proposal for a principal-slit chart. A fallback is still emitted as a failed positive
real claim, so choosing the wrong chart cannot create a false theorem. -/
def slitSeparation (rectangle : Rectangle) : SlitPlaneSeparation :=
  if 0 < rectangle.imag.lower then .imagPositive
  else if rectangle.imag.upper < 0 then .imagNegative
  else if 0 < rectangle.real.lower then .realPositive
  else .realPositive

def terminalCell
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) (index : Fin meshCells) :
    TerminalCoarseEndpointCell model side where
  region := meshRegion index
  parameter := parameterInterval index
  coordinateTrace := coordinateTrace side index
  trace := radicandTrace side index
  plusSeparation :=
    (slitSeparation (radicandTrace side index).factorPlus).toZeroSeparation
  minusSeparation :=
    (slitSeparation (radicandTrace side index).factorMinus).toZeroSeparation
  parameter_contains := parameterInterval_contains_of_mem_meshRegion index
  exponentialCoefficient_contains := by
    exact ChapterVIDOuterArcPolarCompiledGrid.exponentialCoefficient_contains
  inverse10001_contains := by
    exact ChapterVIDOuterArcPolarCompiledGrid.inverse10001_contains

def cell
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) (index : Fin meshCells) :
    ChapterVIDConnectorCompiledGrid.Cell model side 20 :=
  (terminalCell model side (retainedMeshIndex side index)).toCell

theorem cell_region
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) (index : Fin meshCells) :
    (cell model side index).region = meshRegion (retainedMeshIndex side index) := by
  cases side <;> rfl

def plusSeparation (side : ChapterVIDOuterArcSide) (index : Fin meshCells) :
    SlitPlaneSeparation :=
  slitSeparation (radicandTrace side (retainedMeshIndex side index)).factorPlus

def minusSeparation (side : ChapterVIDOuterArcSide) (index : Fin meshCells) :
    SlitPlaneSeparation :=
  slitSeparation (radicandTrace side (retainedMeshIndex side index)).factorMinus

def outerIndex : ChapterVIDOuterArcSide → Fin meshCells
  | .initial => ⟨0, by norm_num [meshCells]⟩
  | .final => ⟨1023, by norm_num [meshCells]⟩

theorem connectorPathPoint_outer_mem
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) :
    connectorPathPoint model (outerParameter side) ∈
      (cell model side (outerIndex side)).region := by
  rw [cell_region]
  cases side <;>
    norm_num [retainedMeshIndex, outerIndex, meshRegion, chapterVIUnitGridCell,
      outerParameter, connectorPathPoint, initialLastMeshIndex, finalFirstMeshIndex]

theorem outer_plus_label (side : ChapterVIDOuterArcSide) :
    plusSeparation side (outerIndex side) = outerPlusSeparation side := by
  cases side <;> decide +kernel

theorem outer_minus_label (side : ChapterVIDOuterArcSide) :
    minusSeparation side (outerIndex side) = outerMinusSeparation side := by
  cases side <;> decide +kernel

def cellOperations
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) (index : Fin meshCells) :=
  (cell model side index).coordinateOperations ++
    (cell model side index).trace.operations ++
    [separationOperation (cell model side index).trace.factorPlus (plusSeparation side index),
      separationOperation (cell model side index).trace.factorMinus (minusSeparation side index)]

def referenceCellOperations (side : ChapterVIDOuterArcSide) (index : Fin meshCells) :=
  (coordinateTrace side (retainedMeshIndex side index)).operations ++
    (radicandTrace side (retainedMeshIndex side index)).operations ++
    [separationOperation
        (radicandTrace side (retainedMeshIndex side index)).factorPlus
        (plusSeparation side index),
      separationOperation
        (radicandTrace side (retainedMeshIndex side index)).factorMinus
        (minusSeparation side index)]

theorem cellOperations_eq_reference
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) (index : Fin meshCells) :
    cellOperations model side index = referenceCellOperations side index := by
  cases side <;> rfl

def operations
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) :=
  (List.finRange meshCells).flatMap (cellOperations model side)

def referenceOperations (side : ChapterVIDOuterArcSide) :=
  (List.finRange meshCells).flatMap (referenceCellOperations side)

/-- The reference campaign is emitted as 32 independent artifacts per connector side. -/
def shardCount : ℕ := 32

/-- Each compiled artifact contains 32 adjacent mesh cells. -/
def cellsPerShard : ℕ := 32

def shardCellIndex (shard : Fin shardCount) (offset : Fin cellsPerShard) : Fin meshCells :=
  ⟨shard.val * cellsPerShard + offset.val, by
    have hshard := shard.isLt
    have hoffset := offset.isLt
    simp only [shardCount] at hshard
    simp only [cellsPerShard] at hoffset
    simp only [meshCells, cellsPerShard]
    omega⟩

def referenceShardOperations (side : ChapterVIDOuterArcSide) (shard : Fin shardCount) :=
  (List.finRange cellsPerShard).flatMap fun offset ↦
    referenceCellOperations side (shardCellIndex shard offset)

def shardArtifactName (side : ChapterVIDOuterArcSide) (shard : Fin shardCount) : String :=
  s!"chapter_vi_connector_factor_{ChapterVIDOuterArcPolarCompiledGrid.sideName side}_{shard.val}"

theorem referenceCellOperations_mem_shard
    (side : ChapterVIDOuterArcSide) (index : Fin meshCells)
    (operation : DyadicOperation 20)
    (hoperation : operation ∈ referenceCellOperations side index) :
    ∃ shard : Fin shardCount, operation ∈ referenceShardOperations side shard := by
  let shard : Fin shardCount := ⟨index.val / cellsPerShard, by
    have hindex := index.isLt
    simp only [meshCells, cellsPerShard, shardCount] at hindex ⊢
    omega⟩
  let offset : Fin cellsPerShard := ⟨index.val % cellsPerShard, by
    simp only [cellsPerShard]
    omega⟩
  have hindexEq : shardCellIndex shard offset = index := by
    apply Fin.ext
    simp only [shardCellIndex, shard, offset]
    simp only [cellsPerShard]
    omega
  refine ⟨shard, ?_⟩
  rw [referenceShardOperations, List.mem_flatMap]
  exact ⟨offset, by simp, by simpa only [hindexEq] using hoperation⟩

theorem referenceClaim_mem_shard
    (side : ChapterVIDOuterArcSide) (claim : Claim)
    (hclaim : claim ∈ ChapterVILeanCompCertBatch.batchClaims (referenceOperations side)) :
    ∃ shard : Fin shardCount,
      claim ∈ ChapterVILeanCompCertBatch.batchClaims (referenceShardOperations side shard) := by
  rw [ChapterVILeanCompCertBatch.batchClaims, List.mem_flatMap] at hclaim
  obtain ⟨operation, hoperation, hclaim⟩ := hclaim
  rw [referenceOperations, List.mem_flatMap] at hoperation
  obtain ⟨index, _, hoperation⟩ := hoperation
  obtain ⟨shard, hshard⟩ := referenceCellOperations_mem_shard side index operation hoperation
  refine ⟨shard, ?_⟩
  rw [ChapterVILeanCompCertBatch.batchClaims, List.mem_flatMap]
  exact ⟨operation, hshard, hclaim⟩

theorem operations_eq_reference
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) :
    operations model side = referenceOperations side := by
  unfold operations referenceOperations
  induction List.finRange meshCells with
  | nil => rfl
  | cons index rest ih =>
      simp only [List.flatMap_cons]
      rw [cellOperations_eq_reference model side index, ih]

/-- Exact connector parameter at the local Morse endpoint. -/
def anchorParameter : ChapterVIDOuterArcSide → Interval
  | .initial => ChapterVISignedDyadicInterval.pointInt 20 1
  | .final => ChapterVISignedDyadicInterval.pointInt 20 0

def anchorRegion
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) : Set (I × I) :=
  {point | point = connectorPathPoint model (localParameter side)}

def anchorCoordinateTrace (side : ChapterVIDOuterArcSide) :=
  lineMapTrace (sourceRectangle side) (targetRectangle side) (anchorParameter side)

def anchorRadicandTrace (side : ChapterVIDOuterArcSide) :=
  cartesianRadicandTrace ChapterVIDConnectorInputBounds.terminalZetaRectangle
    (anchorCoordinateTrace side).output
    ChapterVIDOuterArcPolarCompiledGrid.exponentialCoefficient
    ChapterVIDOuterArcPolarCompiledGrid.inverse10001

def anchorTerminalCell
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) : TerminalCoarseEndpointCell model side where
  region := anchorRegion model side
  parameter := anchorParameter side
  coordinateTrace := anchorCoordinateTrace side
  trace := anchorRadicandTrace side
  plusSeparation := .realPositive
  minusSeparation := .realPositive
  parameter_contains := by
    intro point hpoint
    subst point
    cases side <;>
      norm_num [anchorParameter, connectorPathPoint, localParameter,
        ChapterVISignedDyadicInterval.pointInt, ChapterVISignedDyadicInterval.Contains,
        ChapterVISignedDyadicInterval.toRealInterval, ChapterVIRealInterval.Contains,
        ChapterVISignedDyadicInterval.scale]
  exponentialCoefficient_contains :=
    ChapterVIDOuterArcPolarCompiledGrid.exponentialCoefficient_contains
  inverse10001_contains := ChapterVIDOuterArcPolarCompiledGrid.inverse10001_contains

def anchorCell
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) : ChapterVIDConnectorCompiledGrid.Cell model side 20 :=
  (anchorTerminalCell model side).toCell

theorem anchorCell_local_mem
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) :
    connectorPathPoint model (localParameter side) ∈ (anchorCell model side).region := by
  cases side <;>
    simp [anchorCell, TerminalCoarseEndpointCell.toCell,
      TerminalCoarseEndpointCell.toCoarseEndpointCell, CoarseEndpointCell.toCell,
      CoarseEndpointCell.toAffineCell, AffineCell.toCell, anchorTerminalCell, anchorRegion]

def referenceAnchorOperations (side : ChapterVIDOuterArcSide) :=
  (anchorCoordinateTrace side).operations ++ (anchorRadicandTrace side).operations ++
    [separationOperation (anchorRadicandTrace side).factorMinus .realPositive]

theorem anchorCell_operations
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) :
    (anchorCell model side).coordinateOperations ++ (anchorCell model side).trace.operations ++
        [separationOperation (anchorCell model side).trace.factorMinus .realPositive] =
      referenceAnchorOperations side := by
  cases side <;> rfl

/-- The exact `FactorBulkData` used by the passing reference campaign.  The two hypotheses are
kept separate: `hcutoff` is the remaining analytic estimate, while `hadmissible` is the generated
machine-word bound checked independently in kernel-sized shards. -/
def data
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide)
    (collar : FactorEndpointCollar model side)
    (hcutoff : (collarCells : ℝ) / meshCells ≤ collar.width)
    (hadmissible : LeanCompCert.Ports.SignedProductClaims.Admissible
      (ChapterVILeanCompCertBatch.batchClaims (referenceOperations side))) :
    FactorBulkData model side collar 20 meshCells where
  cell := cell model side
  plusSeparation := plusSeparation side
  minusSeparation := minusSeparation side
  covers := by
    intro t ht
    let index := bulkMeshIndex side t
    refine ⟨index, ?_⟩
    rw [cell_region]
    rw [retainedMeshIndex_bulkMeshIndex]
    exact connectorPathPoint_mem_bulkMeshIndex model side t (hcutoff.trans ht)
  outerIndex := outerIndex side
  outer_mem := connectorPathPoint_outer_mem model side
  outer_plus := outer_plus_label side
  outer_minus := outer_minus_label side
  admissible := by
    change LeanCompCert.Ports.SignedProductClaims.Admissible
      (ChapterVILeanCompCertBatch.batchClaims (operations model side))
    rw [operations_eq_reference model side]
    exact hadmissible

end PoincareChapterVI.ChapterVIDConnectorFactorBulkReference
