/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.ChapterVIDOuterArcUnitTrace
import PoincareChapterVI.ChapterVIUnitSquareGrid

/-!
# A compiled whole-cell outer-quarter certificate

This regression certificate evaluates the rational unit-quarter map on the full first mesh cell
`0 ≤ t ≤ 1/16`, rather than at one point.  It exercises the exact operation-list shape used by the
eventual generated campaign: multiplication, positive reciprocal, one batch verdict, and semantic
containment for every parameter in the cell.
-/

namespace PoincareChapterVI

open ChapterVILeanCompCertBatch
open LeanCompCert.Ports.SignedProductClaims
open scoped unitInterval

namespace ChapterVIDOuterArcUnitCompiledCell

def input : ChapterVISignedDyadicInterval 16 := ⟨0, 4096⟩

def trace : ChapterVIDOuterArcUnitTrace.Trace input where
  tSq := ⟨0, 256⟩
  denominatorInv := ⟨65280, 65536⟩
  twoT := ⟨0, 8192⟩
  realOut := ⟨65025, 65536⟩
  imagOut := ⟨0, 8192⟩

def operations : List (DyadicOperation 16) := trace.operations

theorem operations_admissible : Admissible (batchClaims operations) := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem operations_returns_zero :
    (batchComputation "chapter-vi-d-outer-unit-first-cell" operations).Returns
      ((0 : Nat) : Int) := by
  decide +kernel

theorem input_contains_of_mem_first_cell
    {parameter : I}
    (hparameter : parameter ∈ chapterVIUnitGridCell 15 (0 : Fin 17)) :
    input.Contains (parameter : ℝ) := by
  have hbounds : (0 : ℝ) ≤ (parameter : ℝ) ∧ (parameter : ℝ) ≤ 1 / 16 := by
    simpa [chapterVIUnitGridCell] using hparameter
  constructor
  · norm_num [input, ChapterVISignedDyadicInterval.Contains,
      ChapterVISignedDyadicInterval.toRealInterval,
      ChapterVISignedDyadicInterval.scale]
    exact hbounds.1
  · norm_num [input, ChapterVISignedDyadicInterval.Contains,
      ChapterVISignedDyadicInterval.toRealInterval,
      ChapterVISignedDyadicInterval.scale]
    exact hbounds.2

/-- The compiled row encloses the exact initial or final outer-quarter point over the whole cell. -/
theorem outerOutput_contains
    (side : ChapterVIDOuterArcSide) {parameter : I}
    (hparameter : parameter ∈ chapterVIUnitGridCell 15 (0 : Fin 17)) :
    (ChapterVIDOuterArcUnitTrace.outerOutput side trace).Contains
      (chapterVIDRationalOuterArcUnit side parameter) := by
  apply ChapterVIDOuterArcUnitTrace.outerOutput_contains_of_allSound
  · intro operation hoperation
    exact allSound_of_returns_zero
      "chapter-vi-d-outer-unit-first-cell" operations operations_admissible
      operations_returns_zero operation (by simpa [operations] using hoperation)
  · exact input_contains_of_mem_first_cell hparameter

end ChapterVIDOuterArcUnitCompiledCell

end PoincareChapterVI
