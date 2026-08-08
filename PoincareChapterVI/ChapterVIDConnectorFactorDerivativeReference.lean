/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.ChapterVIDConnectorFactorBulkReference
import PoincareChapterVI.ChapterVILeanCompCertCartesianFactorDerivativeTrace

/-!
# Reference derivative campaign for the connector terminal cells

The passing direct factor campaign stops at cell `762` on the initial connector and starts at
cell `261` on the final connector.  On the next 240 initial-side cells and 252 final-side cells
toward the local endpoints, the
imaginary part of the derivative of the vanishing factor has a strictly positive compiled lower
bound.  This is the monotonicity certificate needed to transport the endpoint branch choice.

The 21 initial-side and 9 final-side cells nearest the endpoints are deliberately excluded.  Those
30 cells retain the scale-sensitive `L -> 0` issue and must not be hidden by an interval box
containing the double zero.
-/

namespace PoincareChapterVI.ChapterVIDConnectorFactorDerivativeReference

open ChapterVILeanCompCertBatch
open ChapterVILeanCompCertProposals
open ChapterVILeanCompCertCartesianFactorDerivativeTrace
open ChapterVIDConnectorCompiledGrid
open ChapterVIDConnectorFactorBulkReference
open ChapterVIDConnectorSeamCompiledGrid
open LeanCompCert.Ports.SignedProductClaims

abbrev Interval := ChapterVISignedDyadicInterval 20
abbrev Rectangle := ChapterVISignedDyadicComplexRectangle 20

def cells : ChapterVIDOuterArcSide → ℕ
  | .initial => 240
  | .final => 252

/-- `200 / 10001`, rounded outward at 20 binary fractional bits. -/
def derivativeCoefficient : Interval := ⟨20969, 20970⟩

theorem derivativeCoefficient_contains :
    derivativeCoefficient.Contains (200 / 10001 : ℝ) := by
  constructor <;>
    norm_num [derivativeCoefficient, ChapterVISignedDyadicInterval.Contains,
      ChapterVISignedDyadicInterval.toRealInterval, ChapterVIRealInterval.Contains,
      ChapterVISignedDyadicInterval.scale]

/-- Global mesh index of a derivative-certified terminal cell. -/
def meshIndex (side : ChapterVIDOuterArcSide) (index : Fin (cells side)) : Fin meshCells :=
  match side with
  | .initial => ⟨index.val + 763, by
      have hi := index.isLt
      simp only [cells, meshCells] at hi ⊢
      omega⟩
  | .final => ⟨index.val + 9, by
      have hi := index.isLt
      simp only [cells, meshCells] at hi ⊢
      omega⟩

def delta (side : ChapterVIDOuterArcSide) : Rectangle :=
  (targetRectangle side).sub (sourceRectangle side)

def trace (side : ChapterVIDOuterArcSide) (index : Fin (cells side)) :=
  derivativeTrace (radicandTrace side (meshIndex side index))
    derivativeCoefficient (delta side)

/-- Each row checks the derivative's positive imaginary part and reuses the direct positive-real
check for the companion factor. -/
def cellOperations (side : ChapterVIDOuterArcSide) (index : Fin (cells side)) :
    List (DyadicOperation 20) :=
  (trace side index).operations ++
    [separationOperation (trace side index).output .imagPositive,
      separationOperation
        (radicandTrace side (meshIndex side index)).factorMinus .realPositive]

def operations (side : ChapterVIDOuterArcSide) : List (DyadicOperation 20) :=
  (List.finRange (cells side)).flatMap (cellOperations side)

def shardCount : ChapterVIDOuterArcSide → ℕ
  | .initial => 20
  | .final => 21
def cellsPerShard : ℕ := 12

def shardCellIndex (side : ChapterVIDOuterArcSide)
    (shard : Fin (shardCount side)) (offset : Fin cellsPerShard) : Fin (cells side) :=
  ⟨shard.val * cellsPerShard + offset.val, by
    cases side <;>
      simp only [shardCount, cells] at shard ⊢ <;>
      have hs := shard.isLt <;>
      have ho := offset.isLt <;>
      simp only [cellsPerShard] at hs ho ⊢ <;>
      omega⟩

def shardOperations (side : ChapterVIDOuterArcSide) (shard : Fin (shardCount side)) :
    List (DyadicOperation 20) :=
  (List.finRange cellsPerShard).flatMap fun offset ↦
    cellOperations side (shardCellIndex side shard offset)

def shardArtifactName (side : ChapterVIDOuterArcSide) (shard : Fin (shardCount side)) : String :=
  s!"chapter_vi_connector_factor_derivative_{
    ChapterVIDOuterArcPolarCompiledGrid.sideName side}_{shard.val}"

theorem cellOperations_mem_shard
    (side : ChapterVIDOuterArcSide) (index : Fin (cells side))
    (operation : DyadicOperation 20)
    (hoperation : operation ∈ cellOperations side index) :
    ∃ shard : Fin (shardCount side), operation ∈ shardOperations side shard := by
  let shard : Fin (shardCount side) := ⟨index.val / cellsPerShard, by
    have hindex := index.isLt
    cases side <;>
      simp only [cells, shardCount, cellsPerShard] at hindex ⊢ <;>
      omega⟩
  let offset : Fin cellsPerShard := ⟨index.val % cellsPerShard, by
    simp only [cellsPerShard]
    omega⟩
  have hindexEq : shardCellIndex side shard offset = index := by
    apply Fin.ext
    simp only [shardCellIndex, shard, offset, cellsPerShard]
    omega
  refine ⟨shard, ?_⟩
  rw [shardOperations, List.mem_flatMap]
  exact ⟨offset, by simp, by simpa only [hindexEq] using hoperation⟩

theorem operation_mem_shard
    (side : ChapterVIDOuterArcSide) (operation : DyadicOperation 20)
    (hoperation : operation ∈ operations side) :
    ∃ shard : Fin (shardCount side), operation ∈ shardOperations side shard := by
  rw [operations, List.mem_flatMap] at hoperation
  obtain ⟨index, _, hcell⟩ := hoperation
  exact cellOperations_mem_shard side index operation hcell

theorem claim_mem_shard
    (side : ChapterVIDOuterArcSide) (claim : Claim)
    (hclaim : claim ∈ batchClaims (operations side)) :
    ∃ shard : Fin (shardCount side), claim ∈ batchClaims (shardOperations side shard) := by
  rw [batchClaims, List.mem_flatMap] at hclaim
  obtain ⟨operation, hoperation, hclaim⟩ := hclaim
  obtain ⟨shard, hshard⟩ := operation_mem_shard side operation hoperation
  refine ⟨shard, ?_⟩
  rw [batchClaims, List.mem_flatMap]
  exact ⟨operation, hshard, hclaim⟩

end PoincareChapterVI.ChapterVIDConnectorFactorDerivativeReference
