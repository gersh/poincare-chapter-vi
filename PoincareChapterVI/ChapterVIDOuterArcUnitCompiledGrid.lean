/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.ChapterVIDOuterArcUnitTrace
import PoincareChapterVI.ChapterVIUnitSquareGrid

/-!
# Compiled rational-unit traces for every outer-arc mesh cell

This is the first complete generated dimension of the D outer-arc campaign.  Seventeen rows cover
`0 ≤ t ≤ 1` at mesh width `1/16` (the last row is the endpoint singleton).  All 85 rounded
operations are flattened into one LeanCompCert computation, and its zero verdict proves the exact
rational initial and final quarter parametrizations are enclosed on every cell.
-/

namespace PoincareChapterVI

open ChapterVILeanCompCertBatch
open LeanCompCert.Ports.SignedProductClaims
open scoped unitInterval

namespace ChapterVIDOuterArcUnitCompiledGrid

abbrev Interval := ChapterVISignedDyadicInterval 16

def input (i : Fin 17) : Interval :=
  ⟨(i.val * 4096 : ℕ), (min (i.val + 1) 16 * 4096 : ℕ)⟩

def tSq : Fin 17 → Interval := ![
  ⟨0, 256⟩, ⟨256, 1024⟩, ⟨1024, 2304⟩, ⟨2304, 4096⟩,
  ⟨4096, 6400⟩, ⟨6400, 9216⟩, ⟨9216, 12544⟩, ⟨12544, 16384⟩,
  ⟨16384, 20736⟩, ⟨20736, 25600⟩, ⟨25600, 30976⟩, ⟨30976, 36864⟩,
  ⟨36864, 43264⟩, ⟨43264, 50176⟩, ⟨50176, 57600⟩, ⟨57600, 65536⟩,
  ⟨65536, 65536⟩]

def denominatorInv : Fin 17 → Interval := ![
  ⟨65280, 65536⟩, ⟨64527, 65281⟩, ⟨63310, 64528⟩, ⟨61680, 63311⟩,
  ⟨59705, 61681⟩, ⟨57456, 59706⟩, ⟨55007, 57457⟩, ⟨52428, 55008⟩,
  ⟨49784, 52429⟩, ⟨47127, 49785⟩, ⟨44501, 47128⟩, ⟨41943, 44502⟩,
  ⟨39475, 41944⟩, ⟨37117, 39476⟩, ⟨34879, 37118⟩, ⟨32768, 34880⟩,
  ⟨32768, 32768⟩]

def twoT : Fin 17 → Interval := ![
  ⟨0, 8192⟩, ⟨8192, 16384⟩, ⟨16384, 24576⟩, ⟨24576, 32768⟩,
  ⟨32768, 40960⟩, ⟨40960, 49152⟩, ⟨49152, 57344⟩, ⟨57344, 65536⟩,
  ⟨65536, 73728⟩, ⟨73728, 81920⟩, ⟨81920, 90112⟩, ⟨90112, 98304⟩,
  ⟨98304, 106496⟩, ⟨106496, 114688⟩, ⟨114688, 122880⟩,
  ⟨122880, 131072⟩, ⟨131072, 131072⟩]

def realOut : Fin 17 → Interval := ![
  ⟨65025, 65536⟩, ⟨63518, 65026⟩, ⟨61084, 63520⟩, ⟨57825, 61086⟩,
  ⟨53874, 57826⟩, ⟨49376, 53876⟩, ⟨44478, 49378⟩, ⟨39321, 44480⟩,
  ⟨34032, 39322⟩, ⟨28718, 34033⟩, ⟨23467, 28719⟩, ⟨18350, 23468⟩,
  ⟨13415, 18351⟩, ⟨8699, 13416⟩, ⟨4223, 8700⟩, ⟨0, 4224⟩, ⟨0, 0⟩]

def imagOut : Fin 17 → Interval := ![
  ⟨0, 8192⟩, ⟨8065, 16321⟩, ⟨15827, 24198⟩, ⟨23130, 31656⟩,
  ⟨29852, 38551⟩, ⟨35910, 44780⟩, ⟨41255, 50275⟩, ⟨45874, 55008⟩,
  ⟨49784, 58983⟩, ⟨53017, 62232⟩, ⟨55626, 64801⟩, ⟨57671, 66753⟩,
  ⟨59212, 68159⟩, ⟨60315, 69083⟩, ⟨61038, 69597⟩, ⟨61440, 69760⟩,
  ⟨65536, 65536⟩]

def trace (i : Fin 17) : ChapterVIDOuterArcUnitTrace.Trace (input i) where
  tSq := tSq i
  denominatorInv := denominatorInv i
  twoT := twoT i
  realOut := realOut i
  imagOut := imagOut i

def operations : List (DyadicOperation 16) :=
  (List.ofFn fun i : Fin 17 => (trace i).operations).flatten

theorem trace_operations_mem (i : Fin 17) (operation : DyadicOperation 16)
    (hoperation : operation ∈ (trace i).operations) : operation ∈ operations := by
  rw [operations, List.mem_flatten]
  exact ⟨(trace i).operations, List.mem_ofFn.mpr ⟨i, rfl⟩, hoperation⟩

theorem operations_admissible : Admissible (batchClaims operations) := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem operations_returns_zero :
    (batchComputation "chapter-vi-d-outer-unit-grid-16" operations).Returns
      ((0 : Nat) : Int) := by
  decide +kernel

theorem input_contains_of_mem_cell (i : Fin 17) {parameter : I}
    (hparameter : parameter ∈ chapterVIUnitGridCell 15 i) :
    (input i).Contains (parameter : ℝ) := by
  have hbounds := hparameter
  simp only [chapterVIUnitGridCell, Set.mem_ofPred_eq] at hbounds
  constructor
  · change (((i.val * 4096 : ℕ) : ℤ) : ℝ) / (2 : ℝ) ^ 16 ≤ (parameter : ℝ)
    convert hbounds.1 using 1 <;> norm_num <;> ring
  · change (parameter : ℝ) ≤
      (((min (i.val + 1) 16 * 4096 : ℕ) : ℤ) : ℝ) / (2 : ℝ) ^ 16
    convert hbounds.2 using 1 <;> norm_num <;> ring

theorem outerOutput_contains_cell (side : ChapterVIDOuterArcSide)
    (i : Fin 17) {parameter : I}
    (hparameter : parameter ∈ chapterVIUnitGridCell 15 i) :
    (ChapterVIDOuterArcUnitTrace.outerOutput side (trace i)).Contains
      (chapterVIDRationalOuterArcUnit side parameter) := by
  apply ChapterVIDOuterArcUnitTrace.outerOutput_contains_of_allSound
  · intro operation hoperation
    exact allSound_of_returns_zero "chapter-vi-d-outer-unit-grid-16"
      operations operations_admissible operations_returns_zero operation
      (trace_operations_mem i operation hoperation)
  · exact input_contains_of_mem_cell i hparameter

/-- Every parameter belongs to a row whose compiled rectangle encloses the exact unit point. -/
theorem exists_outerOutput_contains (side : ChapterVIDOuterArcSide) (parameter : I) :
    ∃ i : Fin 17,
      (ChapterVIDOuterArcUnitTrace.outerOutput side (trace i)).Contains
        (chapterVIDRationalOuterArcUnit side parameter) := by
  let i := chapterVIUnitGridIndex 15 parameter
  exact ⟨i, outerOutput_contains_cell side i
    (chapterVIUnitGridIndex_mem_cell 15 parameter)⟩

end ChapterVIDOuterArcUnitCompiledGrid

end PoincareChapterVI
