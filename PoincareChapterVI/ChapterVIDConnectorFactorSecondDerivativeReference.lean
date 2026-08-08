/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.ChapterVIDConnectorFactorDerivativeReference
import PoincareChapterVI.ChapterVILeanCompCertCartesianFactorSecondDerivativeTrace

/-!
# Reference second-order campaign for the final connector cells

The first-order campaign stops 21 cells before the initial local endpoint and starts 9 cells
after the final local endpoint.  On exactly those 30 cells this campaign certifies the affine
curvature `f''(u) * Δ²`: its imaginary part is negative on the initial connector and positive on
the final connector.  Unlike an absolute first-derivative enclosure, this quantity retains the
quadratic connector scale at the double zero.
-/

namespace PoincareChapterVI.ChapterVIDConnectorFactorSecondDerivativeReference

open ChapterVILeanCompCertBatch
open ChapterVILeanCompCertProposals
open ChapterVILeanCompCertCartesianFactorSecondDerivativeTrace
open ChapterVIDConnectorCompiledGrid
open ChapterVIDConnectorFactorBulkReference
open ChapterVIDConnectorSeamCompiledGrid
open LeanCompCert.Ports.SignedProductClaims

abbrev Interval := ChapterVISignedDyadicInterval 20
abbrev Rectangle := ChapterVISignedDyadicComplexRectangle 20

def cells : ChapterVIDOuterArcSide → ℕ
  | .initial => 21
  | .final => 9

/-- `100 / 10001`, rounded outward at 20 binary fractional bits. -/
def logCoefficient : Interval := ⟨10484, 10485⟩

/-- `200 / 10001`, rounded outward at 20 binary fractional bits. -/
def secondCoefficient : Interval := ⟨20969, 20970⟩

theorem logCoefficient_contains :
    logCoefficient.Contains (100 / 10001 : ℝ) := by
  constructor <;>
    norm_num [logCoefficient, ChapterVISignedDyadicInterval.Contains,
      ChapterVISignedDyadicInterval.toRealInterval, ChapterVIRealInterval.Contains,
      ChapterVISignedDyadicInterval.scale]

theorem secondCoefficient_contains :
    secondCoefficient.Contains (200 / 10001 : ℝ) := by
  constructor <;>
    norm_num [secondCoefficient, ChapterVISignedDyadicInterval.Contains,
      ChapterVISignedDyadicInterval.toRealInterval, ChapterVIRealInterval.Contains,
      ChapterVISignedDyadicInterval.scale]

/-- Global mesh index of a second-order terminal cell. -/
def meshIndex (side : ChapterVIDOuterArcSide) (index : Fin (cells side)) : Fin meshCells :=
  match side with
  | .initial => ⟨index.val + 1003, by
      have hi := index.isLt
      simp only [cells, meshCells] at hi ⊢
      omega⟩
  | .final => ⟨index.val, by
      have hi := index.isLt
      simp only [cells, meshCells] at hi ⊢
      omega⟩

def delta (side : ChapterVIDOuterArcSide) : Rectangle :=
  (targetRectangle side).sub (sourceRectangle side)

def trace (side : ChapterVIDOuterArcSide) (index : Fin (cells side)) :=
  secondDerivativeTrace (radicandTrace side (meshIndex side index))
    logCoefficient secondCoefficient (delta side)

def separation : ChapterVIDOuterArcSide → SlitPlaneSeparation
  | .initial => .imagNegative
  | .final => .imagPositive

/-- Each row checks the side-appropriate strict imaginary curvature sign. -/
def cellOperations (side : ChapterVIDOuterArcSide) (index : Fin (cells side)) :
    List (DyadicOperation 20) :=
  (coordinateTrace side (meshIndex side index)).operations ++
    (trace side index).operations ++
    [separationOperation (trace side index).output (separation side)]

def operations (side : ChapterVIDOuterArcSide) : List (DyadicOperation 20) :=
  (List.finRange (cells side)).flatMap (cellOperations side)

def cellsPerShard : ℕ := 3

def shardCount : ChapterVIDOuterArcSide → ℕ
  | .initial => 7
  | .final => 3

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
  s!"chapter_vi_connector_factor_second_derivative_{
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

end PoincareChapterVI.ChapterVIDConnectorFactorSecondDerivativeReference
