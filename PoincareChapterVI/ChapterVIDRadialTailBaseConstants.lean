/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.ChapterVIDCriticalParameterInterval
import PoincareChapterVI.ChapterVIDRealCriticalParameter
import PoincareChapterVI.ChapterVILeanCompCertProposals

/-!
# Sharp algebraic constants for the radial-tail certificate

The 40-bit affine table needs a substantially sharper endpoint modulus than the older 20-bit
polar grid.  These bounds are derived from the proved `10^-12` bracket for Poincare's algebraic
root and rational Taylor bounds for the one real exponential.
-/

noncomputable section

namespace PoincareChapterVI

open Real Set

theorem chapterVIDPositiveBranchOrdinate_ultrafine_bounds :
    (25291298948 / 1000000000000 : ℝ) ≤
        chapterVIDPositiveBranchOrdinate (-chapterVIDRoot) ∧
      chapterVIDPositiveBranchOrdinate (-chapterVIDRoot) ≤
        (25291298950 / 1000000000000 : ℝ) := by
  have ha := chapterVIDRoot_ultrafine_mem
  have ha' : -chapterVIDRoot ∈ Set.Icc
      (26865395704 / 1000000000000 : ℝ)
      (26865395705 / 1000000000000 : ℝ) := by
    constructor <;> linarith [ha.1, ha.2]
  have ha0 : 0 < -chapterVIDRoot := by linarith [chapterVIDRoot_lt_zero]
  have hden : 0 < 2 * (1 + (1 / 100 : ℝ) ^ 2) * (-chapterVIDRoot) := by positivity
  unfold chapterVIDPositiveBranchOrdinate
  constructor
  · rw [le_div_iff₀ hden]
    have hsquareLower : 0 ≤
        (-chapterVIDRoot - 26865395704 / 1000000000000) *
          (-chapterVIDRoot + 26865395704 / 1000000000000) :=
      mul_nonneg (by linarith [ha'.1]) (by linarith [ha'.1])
    nlinarith [ha'.1, ha'.2, hsquareLower]
  · rw [div_le_iff₀ hden]
    have hsquareUpper : 0 ≤
        (26865395705 / 1000000000000 + chapterVIDRoot) *
          (26865395705 / 1000000000000 - chapterVIDRoot) :=
      mul_nonneg (by linarith [ha'.2]) (by linarith [ha'.1])
    nlinarith [ha'.1, ha'.2, hsquareUpper]

theorem chapterVIDPositiveBranchRationalFactor_ultrafine_bounds :
    (602171453349 / 1000000000000000 : ℝ) ≤
        chapterVIDPositiveBranchOrdinate (-chapterVIDRoot) ^ 3 / (-chapterVIDRoot) ∧
      chapterVIDPositiveBranchOrdinate (-chapterVIDRoot) ^ 3 / (-chapterVIDRoot) ≤
        (60217145352 / 100000000000000 : ℝ) := by
  have ha := chapterVIDRoot_ultrafine_mem
  have haLower : (26865395704 / 1000000000000 : ℝ) ≤ -chapterVIDRoot := by linarith [ha.2]
  have haUpper : -chapterVIDRoot ≤ (26865395705 / 1000000000000 : ℝ) := by linarith [ha.1]
  have ha0 : 0 < -chapterVIDRoot := by linarith [chapterVIDRoot_lt_zero]
  obtain ⟨hyLower, hyUpper⟩ := chapterVIDPositiveBranchOrdinate_ultrafine_bounds
  have hy0 : 0 ≤ chapterVIDPositiveBranchOrdinate (-chapterVIDRoot) := by positivity
  constructor
  · rw [le_div_iff₀ ha0]
    have hcube : (25291298948 / 1000000000000 : ℝ) ^ 3 ≤
        chapterVIDPositiveBranchOrdinate (-chapterVIDRoot) ^ 3 :=
      pow_le_pow_left₀ (by norm_num) hyLower 3
    calc
      (602171453349 / 1000000000000000 : ℝ) * -chapterVIDRoot ≤
          (602171453349 / 1000000000000000 : ℝ) *
            (26865395705 / 1000000000000 : ℝ) :=
        mul_le_mul_of_nonneg_left haUpper (by norm_num)
      _ ≤ (25291298948 / 1000000000000 : ℝ) ^ 3 := by norm_num
      _ ≤ chapterVIDPositiveBranchOrdinate (-chapterVIDRoot) ^ 3 := hcube
  · rw [div_le_iff₀ ha0]
    have hcube : chapterVIDPositiveBranchOrdinate (-chapterVIDRoot) ^ 3 ≤
        (25291298950 / 1000000000000 : ℝ) ^ 3 :=
      pow_le_pow_left₀ hy0 hyUpper 3
    calc
      chapterVIDPositiveBranchOrdinate (-chapterVIDRoot) ^ 3 ≤
          (25291298950 / 1000000000000 : ℝ) ^ 3 := hcube
      _ ≤ (60217145352 / 100000000000000 : ℝ) *
          (26865395704 / 1000000000000 : ℝ) := by norm_num
      _ ≤ (60217145352 / 100000000000000 : ℝ) * -chapterVIDRoot :=
        mul_le_mul_of_nonneg_left haLower (by norm_num)

theorem chapterVIDPositiveBranchExponent_ultrafine_bounds :
    (37192019937 / 100000000000 : ℝ) ≤
        chapterVIDPositiveBranchExponent (-chapterVIDRoot) ∧
      chapterVIDPositiveBranchExponent (-chapterVIDRoot) ≤
        (37192019939 / 100000000000 : ℝ) := by
  have ha := chapterVIDRoot_ultrafine_mem
  have haLower : (26865395704 / 1000000000000 : ℝ) ≤ -chapterVIDRoot := by linarith [ha.2]
  have haUpper : -chapterVIDRoot ≤ (26865395705 / 1000000000000 : ℝ) := by linarith [ha.1]
  have ha0 : 0 < -chapterVIDRoot := by linarith [chapterVIDRoot_lt_zero]
  have hk : (0 : ℝ) < 100 / 10001 := by norm_num
  unfold chapterVIDPositiveBranchExponent
  constructor
  · rw [show (-chapterVIDRoot)⁻¹ = 1 / (-chapterVIDRoot) by simp]
    rw [show (100 / 10001 : ℝ) * (1 / -chapterVIDRoot - -chapterVIDRoot) =
      (1 / -chapterVIDRoot - -chapterVIDRoot) * (100 / 10001) by ring]
    rw [← div_le_iff₀ hk, le_sub_iff_add_le, le_div_iff₀ ha0]
    nlinarith [haUpper, sq_nonneg chapterVIDRoot]
  · rw [show (-chapterVIDRoot)⁻¹ = 1 / (-chapterVIDRoot) by simp]
    rw [show (100 / 10001 : ℝ) * (1 / -chapterVIDRoot - -chapterVIDRoot) =
      (1 / -chapterVIDRoot - -chapterVIDRoot) * (100 / 10001) by ring]
    rw [← le_div_iff₀ hk, sub_le_iff_le_add, div_le_iff₀ ha0]
    nlinarith [haLower, sq_nonneg chapterVIDRoot]

theorem chapterVIDPositiveBranchExp_ultrafine_bounds :
    (14505172244 / 10000000000 : ℝ) ≤
        Real.exp (chapterVIDPositiveBranchExponent (-chapterVIDRoot)) ∧
      Real.exp (chapterVIDPositiveBranchExponent (-chapterVIDRoot)) ≤
        (14505172246 / 10000000000 : ℝ) := by
  obtain ⟨hElo, hEhi⟩ := chapterVIDPositiveBranchExponent_ultrafine_bounds
  constructor
  · calc
      (14505172244 / 10000000000 : ℝ) ≤
          ∑ m ∈ Finset.range 14,
            (37192019937 / 100000000000 : ℝ) ^ m / m.factorial := by
        norm_num [Finset.sum_range_succ, Nat.factorial]
      _ ≤ Real.exp (37192019937 / 100000000000 : ℝ) :=
        Real.sum_le_exp_of_nonneg (by norm_num) 14
      _ ≤ Real.exp (chapterVIDPositiveBranchExponent (-chapterVIDRoot)) :=
        Real.exp_le_exp.mpr hElo
  · calc
      Real.exp (chapterVIDPositiveBranchExponent (-chapterVIDRoot)) ≤
          Real.exp (37192019939 / 100000000000 : ℝ) := Real.exp_le_exp.mpr hEhi
      _ ≤ (∑ m ∈ Finset.range 14,
            (37192019939 / 100000000000 : ℝ) ^ m / m.factorial) +
          (37192019939 / 100000000000 : ℝ) ^ 14 * ((14 : ℕ) + 1) /
            (Nat.factorial 14 * 14) :=
        Real.exp_bound' (x := (37192019939 / 100000000000 : ℝ)) (n := 14)
          (by norm_num) (by norm_num) (by norm_num)
      _ ≤ (14505172246 / 10000000000 : ℝ) := by
        norm_num [Finset.sum_range_succ, Nat.factorial]

/-- Three-ulp 40-bit enclosure of the exact endpoint modulus. -/
theorem chapterVIDCriticalParameterModulus_dyadic40_bounds :
    (960379498 / (2 : ℝ) ^ 40) ≤ chapterVIDCriticalParameterModulus ∧
      chapterVIDCriticalParameterModulus ≤ (960379499 / (2 : ℝ) ^ 40) := by
  obtain ⟨hfactorLower, hfactorUpper⟩ :=
    chapterVIDPositiveBranchRationalFactor_ultrafine_bounds
  obtain ⟨hexpLower, hexpUpper⟩ := chapterVIDPositiveBranchExp_ultrafine_bounds
  rw [chapterVIDCriticalParameterModulus,
    show chapterVIDRoot = -(-chapterVIDRoot) by ring,
    chapterVIDCurveThreeSmoothParameter_neg]
  have hfactorNonneg : 0 ≤
      chapterVIDPositiveBranchOrdinate (-chapterVIDRoot) ^ 3 / -chapterVIDRoot := by
    linarith [hfactorLower]
  have hexpNonneg : 0 ≤ Real.exp (chapterVIDPositiveBranchExponent (-chapterVIDRoot)) :=
    Real.exp_nonneg _
  constructor
  · calc
      (960379498 / (2 : ℝ) ^ 40) ≤
          (602171453349 / 1000000000000000 : ℝ) *
            (14505172244 / 10000000000 : ℝ) := by norm_num
      _ ≤ chapterVIDPositiveBranchOrdinate (-chapterVIDRoot) ^ 3 / -chapterVIDRoot *
          Real.exp (chapterVIDPositiveBranchExponent (-chapterVIDRoot)) :=
        mul_le_mul hfactorLower hexpLower (by norm_num) hfactorNonneg
  · calc
      chapterVIDPositiveBranchOrdinate (-chapterVIDRoot) ^ 3 / -chapterVIDRoot *
          Real.exp (chapterVIDPositiveBranchExponent (-chapterVIDRoot)) ≤
          (60217145352 / 100000000000000 : ℝ) *
            (14505172246 / 10000000000 : ℝ) :=
        mul_le_mul hfactorUpper hexpUpper hexpNonneg (by norm_num)
      _ ≤ (960379499 / (2 : ℝ) ^ 40) := by norm_num

namespace ChapterVIDRadialTailBaseConstants

abbrev Interval := ChapterVISignedDyadicInterval 40
abbrev Rectangle := ChapterVISignedDyadicComplexRectangle 40

def zeroInterval : Interval := ChapterVISignedDyadicInterval.pointInt 40 0

def realRectangle (interval : Interval) : Rectangle := ⟨interval, zeroInterval⟩

def qD : Interval := ⟨960379498, 960379499⟩

def collisionRadius : Interval := ⟨329304430503, 329304430508⟩

def collision : Rectangle := realRectangle collisionRadius.neg

def yBase : Rectangle := realRectangle ⟨-27808077278, -27808077274⟩

theorem qD_contains : qD.Contains chapterVIDCriticalParameterModulus := by
  simpa [qD, ChapterVISignedDyadicInterval.Contains,
    ChapterVISignedDyadicInterval.toRealInterval, ChapterVISignedDyadicInterval.scale,
    ChapterVIRealInterval.Contains] using chapterVIDCriticalParameterModulus_dyadic40_bounds

theorem collisionRadius_contains : collisionRadius.Contains ‖chapterVIDCollisionLift‖ := by
  have hcube := chapterVIDCollisionRadius_cube
  have hroot := chapterVIDRoot_ultrafine_mem
  constructor
  · change (329304430503 : ℝ) / (2 : ℝ) ^ 40 ≤ ‖chapterVIDCollisionLift‖
    apply le_of_pow_le_pow_left₀ (n := 3) (by norm_num) (norm_nonneg _)
    rw [hcube]
    norm_num
    linarith [hroot.1, hroot.2]
  · change ‖chapterVIDCollisionLift‖ ≤ (329304430508 : ℝ) / (2 : ℝ) ^ 40
    apply le_of_pow_le_pow_left₀ (n := 3) (by norm_num)
      (by norm_num : 0 ≤ (329304430508 : ℝ) / (2 : ℝ) ^ 40)
    rw [hcube]
    calc
      -chapterVIDRoot ≤ (26865395705 / 1000000000000 : ℝ) := by linarith [hroot.1]
      _ ≤ ((329304430508 : ℝ) / (2 : ℝ) ^ 40) ^ 3 := by norm_num

theorem collision_contains : collision.Contains chapterVIDCollisionLift := by
  have hradius := collisionRadius_contains
  rw [chapterVIDCollisionLift_eq_neg_norm]
  constructor
  · simpa [collision, realRectangle, ChapterVISignedDyadicComplexRectangle.Contains,
      ChapterVISignedDyadicInterval.neg_contains, Complex.neg_re,
      ChapterVISignedDyadicInterval.Contains, ChapterVISignedDyadicInterval.toRealInterval,
      ChapterVISignedDyadicInterval.scale, ChapterVIRealInterval.Contains] using
        ChapterVISignedDyadicInterval.neg_contains hradius
  · simpa [collision, realRectangle, zeroInterval] using
      ChapterVISignedDyadicInterval.pointInt_contains 40 0

theorem chapterVIDYReal_eq_neg_positiveOrdinate :
    chapterVIDYReal = -chapterVIDPositiveBranchOrdinate (-chapterVIDRoot) := by
  unfold chapterVIDYReal chapterVIDPositiveBranchOrdinate
  field_simp [chapterVIDRoot_lt_zero.ne]
  ring

theorem yBase_contains : yBase.Contains chapterVIDY := by
  rw [chapterVIDY_eq_ofReal, chapterVIDYReal_eq_neg_positiveOrdinate]
  obtain ⟨hlower, hupper⟩ := chapterVIDPositiveBranchOrdinate_ultrafine_bounds
  simp only [yBase, realRectangle, zeroInterval,
    ChapterVISignedDyadicComplexRectangle.Contains,
    ChapterVISignedDyadicInterval.Contains,
    ChapterVISignedDyadicInterval.toRealInterval,
    ChapterVISignedDyadicInterval.scale, ChapterVIRealInterval.Contains,
    Complex.ofReal_re, Complex.ofReal_im]
  constructor
  · constructor
    · norm_num at ⊢
      linarith
    · norm_num at ⊢
      linarith
  · norm_num [ChapterVISignedDyadicInterval.pointInt]

end ChapterVIDRadialTailBaseConstants

end PoincareChapterVI
