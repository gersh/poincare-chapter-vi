/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import Mathlib

/-!
# Finite nonuniform interval grids

A short order-theoretic lemma used by the clustered Chapter VI certificate mesh.  It keeps the
covering proof independent of how the rational nodes were chosen.
-/

namespace PoincareChapterVI

/-- Consecutive nodes of any monotone finite list cover the interval between its endpoints. -/
theorem exists_mem_adjacent_node_interval
    (node : ℕ → ℝ) (n : ℕ) (hn : 0 < n) (hmono : Monotone node)
    {x : ℝ} (hstart : node 0 ≤ x) (hend : x ≤ node n) :
    ∃ i : ℕ, i < n ∧ node i ≤ x ∧ x ≤ node (i + 1) := by
  let P : ℕ → Prop := fun k ↦ k ≤ n ∧ x ≤ node k
  have hexists : ∃ k, P k := ⟨n, le_rfl, hend⟩
  let k := Nat.find hexists
  have hk : P k := Nat.find_spec hexists
  by_cases hkzero : k = 0
  · subst k
    exact ⟨0, hn, hstart, hk.2.trans (hmono (by omega))⟩
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hkzero
    let i := k - 1
    have hik : i + 1 = k := by
      dsimp [i]
      omega
    have hiltn : i < n := by
      have hkn : k ≤ n := hk.1
      omega
    have hlower : node i ≤ x := by
      by_contra hnot
      have hxnode : x ≤ node i := le_of_not_ge hnot
      have hiP : P i := ⟨by omega, hxnode⟩
      have := Nat.find_min' hexists hiP
      omega
    exact ⟨i, hiltn, hlower, by simpa [hik] using hk.2⟩

/-- The clustered rational nodes used in the radial direction. -/
def chapterVICubicClusterNode (cells i : ℕ) : ℚ :=
  1 - (((cells : ℚ) - min i cells) / cells) ^ 3

/-- The clustered rational nodes used in the angular direction. -/
def chapterVIQuadraticClusterNode (cells i : ℕ) : ℚ :=
  1 - (((cells : ℚ) - min i cells) / cells) ^ 2

theorem monotone_chapterVICubicClusterNode {cells : ℕ} (hcells : 0 < cells) :
    Monotone (chapterVICubicClusterNode cells) := by
  intro i j hij
  have hmin : min i cells ≤ min j cells := min_le_min hij le_rfl
  have hden : (0 : ℚ) < cells := by exact_mod_cast hcells
  have hdiff : (cells : ℚ) - min j cells ≤ (cells : ℚ) - min i cells := by
    gcongr
  have hnonnegJ : (0 : ℚ) ≤ (cells : ℚ) - min j cells := by
    rw [sub_nonneg]
    exact_mod_cast min_le_right j cells
  have hquot : ((cells : ℚ) - min j cells) / cells ≤
      ((cells : ℚ) - min i cells) / cells :=
    div_le_div_of_nonneg_right hdiff hden.le
  unfold chapterVICubicClusterNode
  have hpow := pow_le_pow_left₀ (div_nonneg hnonnegJ hden.le) hquot 3
  linarith

theorem monotone_chapterVIQuadraticClusterNode {cells : ℕ} (hcells : 0 < cells) :
    Monotone (chapterVIQuadraticClusterNode cells) := by
  intro i j hij
  have hmin : min i cells ≤ min j cells := min_le_min hij le_rfl
  have hden : (0 : ℚ) < cells := by exact_mod_cast hcells
  have hdiff : (cells : ℚ) - min j cells ≤ (cells : ℚ) - min i cells := by
    gcongr
  have hnonnegJ : (0 : ℚ) ≤ (cells : ℚ) - min j cells := by
    rw [sub_nonneg]
    exact_mod_cast min_le_right j cells
  have hquot : ((cells : ℚ) - min j cells) / cells ≤
      ((cells : ℚ) - min i cells) / cells :=
    div_le_div_of_nonneg_right hdiff hden.le
  unfold chapterVIQuadraticClusterNode
  have hpow := pow_le_pow_left₀ (div_nonneg hnonnegJ hden.le) hquot 2
  linarith

@[simp]
theorem chapterVICubicClusterNode_zero {cells : ℕ} (hcells : 0 < cells) :
    chapterVICubicClusterNode cells 0 = 0 := by
  simp [chapterVICubicClusterNode, hcells.ne']

@[simp]
theorem chapterVICubicClusterNode_last {cells : ℕ} (hcells : 0 < cells) :
    chapterVICubicClusterNode cells cells = 1 := by
  simp [chapterVICubicClusterNode, hcells.ne']

@[simp]
theorem chapterVIQuadraticClusterNode_zero {cells : ℕ} (hcells : 0 < cells) :
    chapterVIQuadraticClusterNode cells 0 = 0 := by
  simp [chapterVIQuadraticClusterNode, hcells.ne']

@[simp]
theorem chapterVIQuadraticClusterNode_last {cells : ℕ} (hcells : 0 < cells) :
    chapterVIQuadraticClusterNode cells cells = 1 := by
  simp [chapterVIQuadraticClusterNode, hcells.ne']

theorem exists_mem_cubicClusterCell (cells : ℕ) (hcells : 0 < cells) (x : Set.Icc (0 : ℝ) 1) :
    ∃ i : ℕ, i < cells ∧
      (chapterVICubicClusterNode cells i : ℝ) ≤ x ∧
        x ≤ (chapterVICubicClusterNode cells (i + 1) : ℝ) := by
  apply exists_mem_adjacent_node_interval
    (fun i ↦ (chapterVICubicClusterNode cells i : ℝ)) cells hcells
  · intro i j hij
    change ((chapterVICubicClusterNode cells i : ℚ) : ℝ) ≤
      ((chapterVICubicClusterNode cells j : ℚ) : ℝ)
    exact_mod_cast monotone_chapterVICubicClusterNode hcells hij
  · norm_num [chapterVICubicClusterNode, hcells.ne']
    exact x.property.1
  · norm_num [chapterVICubicClusterNode, hcells.ne']
    exact x.property.2

theorem exists_mem_quadraticClusterCell (cells : ℕ) (hcells : 0 < cells)
    (x : Set.Icc (0 : ℝ) 1) :
    ∃ i : ℕ, i < cells ∧
      (chapterVIQuadraticClusterNode cells i : ℝ) ≤ x ∧
        x ≤ (chapterVIQuadraticClusterNode cells (i + 1) : ℝ) := by
  apply exists_mem_adjacent_node_interval
    (fun i ↦ (chapterVIQuadraticClusterNode cells i : ℝ)) cells hcells
  · intro i j hij
    change ((chapterVIQuadraticClusterNode cells i : ℚ) : ℝ) ≤
      ((chapterVIQuadraticClusterNode cells j : ℚ) : ℝ)
    exact_mod_cast monotone_chapterVIQuadraticClusterNode hcells hij
  · norm_num [chapterVIQuadraticClusterNode, hcells.ne']
    exact x.property.1
  · norm_num [chapterVIQuadraticClusterNode, hcells.ne']
    exact x.property.2

end PoincareChapterVI
