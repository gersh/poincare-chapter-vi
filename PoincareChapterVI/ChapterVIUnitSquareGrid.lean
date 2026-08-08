/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Topology.MetricSpace.Pseudo.Constructions
import Mathlib.Topology.UnitInterval
import PoincareChapterVI.ChapterVISquareRootSheet

/-!
# A finite rational mesh covering the Chapter VI parameter square

The compiled outer-arc campaign samples a uniform `(n+2) × (n+2)` grid in `I × I`, with
denominator `n+1`.  This file proves once, independently of the radicand computation, that every
point of the square lies within product distance `1/(n+1)` of a sample.  Thus the eventual
certificate table cannot silently assume that its rows cover the continuum.
-/

noncomputable section

open Set
open scoped unitInterval

namespace PoincareChapterVI

/-- The `i`th rational mesh point, including both endpoints zero and one. -/
def chapterVIUnitGridPoint (n : ℕ) (i : Fin (n + 2)) : I :=
  ⟨(i : ℝ) / (n + 1 : ℕ), by
    constructor
    · positivity
    · have hi : i.val ≤ n + 1 := by omega
      exact (div_le_one (by positivity)).2 (by exact_mod_cast hi)⟩

@[simp] theorem chapterVIUnitGridPoint_val (n : ℕ) (i : Fin (n + 2)) :
    (chapterVIUnitGridPoint n i : ℝ) = (i : ℝ) / (n + 1 : ℕ) :=
  rfl

/-- The lower mesh index associated with a point of the unit interval. -/
def chapterVIUnitGridIndex (n : ℕ) (x : I) : Fin (n + 2) :=
  ⟨⌊((n + 1 : ℕ) : ℝ) * (x : ℝ)⌋₊, by
    have hmul : (((n + 1 : ℕ) : ℝ) * (x : ℝ)) ≤ (n + 1 : ℕ) := by
      have hx := x.property.2
      nlinarith
    exact Nat.lt_succ_of_le (Nat.floor_le_of_le hmul)⟩

/-- Flooring to the lower grid point moves a unit-interval coordinate by at most one mesh step. -/
theorem dist_chapterVIUnitGridPoint_index_le (n : ℕ) (x : I) :
    dist x (chapterVIUnitGridPoint n (chapterVIUnitGridIndex n x)) ≤
      (1 : ℝ) / (n + 1 : ℕ) := by
  let N : ℕ := n + 1
  have hN : (0 : ℝ) < N := by positivity
  have hxnonneg : 0 ≤ (N : ℝ) * (x : ℝ) :=
    mul_nonneg (Nat.cast_nonneg N) x.property.1
  have hlower :
      (⌊(N : ℝ) * (x : ℝ)⌋₊ : ℝ) ≤ (N : ℝ) * (x : ℝ) :=
    Nat.floor_le hxnonneg
  have hupper :
      (N : ℝ) * (x : ℝ) < (⌊(N : ℝ) * (x : ℝ)⌋₊ : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have hgrid_le :
      (⌊(N : ℝ) * (x : ℝ)⌋₊ : ℝ) / N ≤ (x : ℝ) := by
    rw [div_le_iff₀ hN]
    simpa [mul_comm] using hlower
  have hdiff :
      (x : ℝ) - (⌊(N : ℝ) * (x : ℝ)⌋₊ : ℝ) / N ≤ 1 / N := by
    have hxupper :
        (x : ℝ) ≤ (⌊(N : ℝ) * (x : ℝ)⌋₊ : ℝ) / N + 1 / N := by
      rw [← add_div, le_div_iff₀ hN]
      linarith
    linarith
  rw [Subtype.dist_eq, Real.dist_eq, chapterVIUnitGridPoint_val]
  change |(x : ℝ) - (⌊((n + 1 : ℕ) : ℝ) * (x : ℝ)⌋₊ : ℝ) /
      (n + 1 : ℕ)| ≤ _
  rw [abs_of_nonneg]
  · simpa [N] using hdiff
  · simpa [N] using sub_nonneg.mpr hgrid_le

/-- The finite uniform mesh on the unit square. -/
noncomputable def chapterVIUnitSquareGrid (n : ℕ) : Finset (I × I) :=
  by
    classical
    exact Finset.univ.image fun ij : Fin (n + 2) × Fin (n + 2) ↦
      (chapterVIUnitGridPoint n ij.1, chapterVIUnitGridPoint n ij.2)

theorem chapterVIUnitSquareGrid_mem (n : ℕ)
    (i j : Fin (n + 2)) :
    (chapterVIUnitGridPoint n i, chapterVIUnitGridPoint n j) ∈
      chapterVIUnitSquareGrid n := by
  classical
  exact Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, rfl⟩

/-- Every parameter pair is within one mesh step of a compiled sample row. -/
theorem chapterVIUnitSquareGrid_covers (n : ℕ) (x : I × I) :
    ∃ center ∈ chapterVIUnitSquareGrid n,
      dist x center ≤ (1 : ℝ) / (n + 1 : ℕ) := by
  let i := chapterVIUnitGridIndex n x.1
  let j := chapterVIUnitGridIndex n x.2
  let center : I × I :=
    (chapterVIUnitGridPoint n i, chapterVIUnitGridPoint n j)
  refine ⟨center, chapterVIUnitSquareGrid_mem n i j, ?_⟩
  rw [Prod.dist_eq]
  exact max_le
    (dist_chapterVIUnitGridPoint_index_le n x.1)
    (dist_chapterVIUnitGridPoint_index_le n x.2)

/-! ## Interval cells for direct compiled enclosures -/

/-- The closed cell beginning at a lower-grid index. The last index gives the degenerate cell
`{1}`, which makes flooring work uniformly at the right endpoint. -/
def chapterVIUnitGridCell (n : ℕ) (i : Fin (n + 2)) : Set I :=
  {x | (i.val : ℝ) / (n + 1 : ℕ) ≤ (x : ℝ) ∧
    (x : ℝ) ≤ (min (i.val + 1) (n + 1) : ℕ) / (n + 1 : ℕ)}

theorem chapterVIUnitGridIndex_mem_cell (n : ℕ) (x : I) :
    x ∈ chapterVIUnitGridCell n (chapterVIUnitGridIndex n x) := by
  let N : ℕ := n + 1
  let k : ℕ := ⌊(N : ℝ) * (x : ℝ)⌋₊
  have hN : (0 : ℝ) < N := by positivity
  have hxnonneg : 0 ≤ (N : ℝ) * (x : ℝ) :=
    mul_nonneg (Nat.cast_nonneg N) x.property.1
  have hkLower : (k : ℝ) ≤ (N : ℝ) * (x : ℝ) := by
    exact Nat.floor_le hxnonneg
  have hkUpper : (N : ℝ) * (x : ℝ) < (k : ℝ) + 1 := by
    exact Nat.lt_floor_add_one _
  have hkN : k ≤ N := by
    apply Nat.floor_le_of_le
    have hx := x.property.2
    nlinarith
  change ((chapterVIUnitGridIndex n x).val : ℝ) / (n + 1 : ℕ) ≤ (x : ℝ) ∧
    (x : ℝ) ≤
      (min ((chapterVIUnitGridIndex n x).val + 1) (n + 1) : ℕ) /
        (n + 1 : ℕ)
  change (k : ℝ) / N ≤ (x : ℝ) ∧
    (x : ℝ) ≤ (min (k + 1) N : ℕ) / N
  constructor
  · rw [div_le_iff₀ hN]
    simpa [mul_comm] using hkLower
  · by_cases htop : k = N
    · have hmin : min (k + 1) N = N := by omega
      rw [hmin]
      simpa [ne_of_gt hN] using x.property.2
    · have hksucc : k + 1 ≤ N := by omega
      rw [min_eq_left hksucc, le_div_iff₀ hN]
      simpa [mul_comm, Nat.cast_add, Nat.cast_one] using hkUpper.le

/-- A rectangular cell of the rational unit-square mesh. -/
def chapterVIUnitSquareCell (n : ℕ)
    (cell : Fin (n + 2) × Fin (n + 2)) : Set (I × I) :=
  chapterVIUnitGridCell n cell.1 ×ˢ chapterVIUnitGridCell n cell.2

theorem chapterVIUnitSquareCells_cover (n : ℕ) (x : I × I) :
    ∃ cell : Fin (n + 2) × Fin (n + 2),
      x ∈ chapterVIUnitSquareCell n cell :=
  ⟨(chapterVIUnitGridIndex n x.1, chapterVIUnitGridIndex n x.2),
    chapterVIUnitGridIndex_mem_cell n x.1,
    chapterVIUnitGridIndex_mem_cell n x.2⟩

/-- A direct interval enclosure for every rational mesh cell is already a global
positive-real-part certificate; no separate Lipschitz estimate is needed. -/
def ChapterVIFinitePositiveRealPartIndexedCover.ofUnitSquareCells
    {radicand : I × I → ℂ} (n : ℕ) (margin : ℝ)
    (hmargin : 0 < margin)
    (hcells : ∀ cell : Fin (n + 2) × Fin (n + 2),
      ∀ x ∈ chapterVIUnitSquareCell n cell, margin ≤ (radicand x).re) :
    ChapterVIFinitePositiveRealPartIndexedCover
      (chapterVIUnitSquareCell n) radicand where
  margin := margin
  margin_pos := hmargin
  covers := chapterVIUnitSquareCells_cover n
  cellRealPart := hcells

/-- Package a checked uniform sample table and a Lipschitz estimate into the exact positive-real
cover consumed by the outer-arc square-root construction. -/
def ChapterVIFinitePositiveRealPartCover.ofUnitSquareGrid
    {radicand : I × I → ℂ} (n : ℕ) (lipschitzConstant : NNReal)
    (sampleMargin : ℝ)
    (hlipschitz : LipschitzWith lipschitzConstant radicand)
    (hsamples : ∀ center ∈ chapterVIUnitSquareGrid n,
      sampleMargin ≤ (radicand center).re)
    (hmargin : 0 < sampleMargin)
    (herror : (lipschitzConstant : ℝ) * ((1 : ℝ) / (n + 1 : ℕ)) < sampleMargin) :
    ChapterVIFinitePositiveRealPartCover radicand where
  samples := chapterVIUnitSquareGrid n
  coverRadius := (1 : ℝ) / (n + 1 : ℕ)
  lipschitzConstant := lipschitzConstant
  sampleMargin := sampleMargin
  coverRadius_nonneg := by positivity
  sampleMargin_pos := hmargin
  covers := chapterVIUnitSquareGrid_covers n
  lipschitz := hlipschitz
  sampleRealPart := hsamples
  error_lt_margin := herror

end PoincareChapterVI
