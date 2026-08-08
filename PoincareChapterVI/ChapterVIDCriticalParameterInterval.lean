/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.ChapterVIDCertificateContour

/-!
# A rational enclosure of the source parameter at D

The compiled sign certificate isolates Poincare's root as
`-0.027 <= x_D <= -0.026`.  This file propagates that small rational interval through the
definition of the positive source modulus.  The only transcendental factor is `exp E`, where
`0 <= E < 1`; the standard inequalities `1 + E <= exp E <= 1 / (1-E)` are already sufficient.

The deliberately modest final enclosure is intended as input to the compiled radial grid, not as
a high-precision numerical evaluation of D.
-/

noncomputable section

open Complex Real
open scoped unitInterval

namespace PoincareChapterVI

/-- The positive version `a=-x` of the rational collision branch ordinate. -/
def chapterVIDPositiveBranchOrdinate (a : ℝ) : ℝ :=
  (a + 1 / 100) ^ 2 / (2 * (1 + (1 / 100 : ℝ) ^ 2) * a)

/-- The positive exponent in the source modulus after writing the negative root as `x=-a`. -/
def chapterVIDPositiveBranchExponent (a : ℝ) : ℝ :=
  (100 / 10001 : ℝ) * (a⁻¹ - a)

theorem chapterVIDCurveThreeSmoothParameter_neg (a : ℝ) :
    chapterVIDCurveThreeSmoothParameter (-a) =
      chapterVIDPositiveBranchOrdinate a ^ 3 / a *
        Real.exp (chapterVIDPositiveBranchExponent a) := by
  unfold chapterVIDCurveThreeSmoothParameter chapterVIDCurveThreeY
    chapterVIDPositiveBranchOrdinate chapterVIDPositiveBranchExponent
  congr 1
  · congr 1
    · ring
    · simp
  · apply congrArg Real.exp
    rw [inv_neg]
    ring

theorem chapterVIDPositiveBranchOrdinate_bounds
    {a : ℝ} (ha : a ∈ Set.Icc (26 / 1000 : ℝ) (27 / 1000 : ℝ)) :
    (249 / 10000 : ℝ) ≤ chapterVIDPositiveBranchOrdinate a ∧
      chapterVIDPositiveBranchOrdinate a ≤ (254 / 10000 : ℝ) := by
  have ha0 : 0 < a := by linarith [ha.1]
  have hden : 0 < 2 * (1 + (1 / 100 : ℝ) ^ 2) * a := by positivity
  unfold chapterVIDPositiveBranchOrdinate
  constructor
  · rw [le_div_iff₀ hden]
    have hsquareLower : 0 ≤ (a - 26 / 1000) * (a + 26 / 1000) :=
      mul_nonneg (by linarith [ha.1]) (by linarith [ha.1])
    nlinarith [ha.1, ha.2, hsquareLower]
  · rw [div_le_iff₀ hden]
    have hsquareUpper : 0 ≤ (27 / 1000 - a) * (27 / 1000 + a) :=
      mul_nonneg (by linarith [ha.2]) (by linarith [ha.1])
    nlinarith [ha.1, ha.2, hsquareUpper]

theorem chapterVIDPositiveBranchRationalFactor_bounds
    {a : ℝ} (ha : a ∈ Set.Icc (26 / 1000 : ℝ) (27 / 1000 : ℝ)) :
    (57 / 100000 : ℝ) ≤ chapterVIDPositiveBranchOrdinate a ^ 3 / a ∧
      chapterVIDPositiveBranchOrdinate a ^ 3 / a ≤ (64 / 100000 : ℝ) := by
  have ha0 : 0 < a := by linarith [ha.1]
  obtain ⟨hbLower, hbUpper⟩ := chapterVIDPositiveBranchOrdinate_bounds ha
  have hb0 : 0 ≤ chapterVIDPositiveBranchOrdinate a := by positivity
  constructor
  · rw [le_div_iff₀ ha0]
    have hcube : (249 / 10000 : ℝ) ^ 3 ≤
        chapterVIDPositiveBranchOrdinate a ^ 3 :=
      pow_le_pow_left₀ (by norm_num) hbLower 3
    nlinarith [ha.2]
  · rw [div_le_iff₀ ha0]
    have hcube : chapterVIDPositiveBranchOrdinate a ^ 3 ≤
        (254 / 10000 : ℝ) ^ 3 :=
      pow_le_pow_left₀ hb0 hbUpper 3
    nlinarith [ha.1]

theorem chapterVIDPositiveBranchExponent_bounds
    {a : ℝ} (ha : a ∈ Set.Icc (26 / 1000 : ℝ) (27 / 1000 : ℝ)) :
    (37 / 100 : ℝ) ≤ chapterVIDPositiveBranchExponent a ∧
      chapterVIDPositiveBranchExponent a ≤ (39 / 100 : ℝ) := by
  have ha0 : 0 < a := by linarith [ha.1]
  have hk : (0 : ℝ) < 100 / 10001 := by norm_num
  unfold chapterVIDPositiveBranchExponent
  constructor
  · rw [show a⁻¹ = 1 / a by simp]
    rw [show (100 / 10001 : ℝ) * (1 / a - a) = (1 / a - a) * (100 / 10001) by ring]
    rw [← div_le_iff₀ hk, le_sub_iff_add_le, le_div_iff₀ ha0]
    nlinarith [ha.2, sq_nonneg a]
  · rw [show a⁻¹ = 1 / a by simp]
    rw [show (100 / 10001 : ℝ) * (1 / a - a) = (1 / a - a) * (100 / 10001) by ring]
    rw [← le_div_iff₀ hk, sub_le_iff_le_add, div_le_iff₀ ha0]
    nlinarith [ha.1, sq_nonneg a]

/-- A fully rational enclosure of the one exponential needed at the D endpoint. -/
theorem chapterVIDPositiveBranchExp_bounds
    {a : ℝ} (ha : a ∈ Set.Icc (26 / 1000 : ℝ) (27 / 1000 : ℝ)) :
    (137 / 100 : ℝ) ≤ Real.exp (chapterVIDPositiveBranchExponent a) ∧
      Real.exp (chapterVIDPositiveBranchExponent a) ≤ (164 / 100 : ℝ) := by
  obtain ⟨hElo, hEhi⟩ := chapterVIDPositiveBranchExponent_bounds ha
  have hE0 : 0 ≤ chapterVIDPositiveBranchExponent a := by linarith
  have hE1 : chapterVIDPositiveBranchExponent a < 1 := by linarith
  constructor
  · exact (by linarith [Real.add_one_le_exp (chapterVIDPositiveBranchExponent a)])
  · calc
      Real.exp (chapterVIDPositiveBranchExponent a) ≤
          1 / (1 - chapterVIDPositiveBranchExponent a) :=
        Real.exp_bound_div_one_sub_of_interval hE0 hE1
      _ ≤ 164 / 100 := by
        rw [div_le_iff₀ (by linarith : 0 < 1 - chapterVIDPositiveBranchExponent a)]
        nlinarith

/-- Coarse but rigorous dyadic-friendly bounds for the endpoint source modulus `q_D`. -/
theorem chapterVIDCriticalParameterModulus_bounds :
    (3 / 4000 : ℝ) ≤ chapterVIDCriticalParameterModulus ∧
      chapterVIDCriticalParameterModulus ≤ (11 / 10000 : ℝ) := by
  have ha : -chapterVIDRoot ∈ Set.Icc (26 / 1000 : ℝ) (27 / 1000 : ℝ) := by
    constructor <;> linarith [chapterVIDRoot_mem.1, chapterVIDRoot_mem.2]
  obtain ⟨hfactorLower, hfactorUpper⟩ :=
    chapterVIDPositiveBranchRationalFactor_bounds ha
  obtain ⟨hexpLower, hexpUpper⟩ := chapterVIDPositiveBranchExp_bounds ha
  rw [chapterVIDCriticalParameterModulus,
    show chapterVIDRoot = -(-chapterVIDRoot) by ring,
    chapterVIDCurveThreeSmoothParameter_neg]
  have hfactorNonneg : 0 ≤
      chapterVIDPositiveBranchOrdinate (-chapterVIDRoot) ^ 3 / -chapterVIDRoot :=
    (show (0 : ℝ) ≤ 57 / 100000 by norm_num).trans hfactorLower
  have hexpNonneg : 0 ≤ Real.exp (chapterVIDPositiveBranchExponent (-chapterVIDRoot)) :=
    Real.exp_nonneg _
  constructor
  · calc
      (3 / 4000 : ℝ) ≤ (57 / 100000) * (137 / 100) := by norm_num
      _ ≤ chapterVIDPositiveBranchOrdinate (-chapterVIDRoot) ^ 3 / -chapterVIDRoot *
          Real.exp (chapterVIDPositiveBranchExponent (-chapterVIDRoot)) :=
        mul_le_mul hfactorLower hexpLower (by norm_num) hfactorNonneg
  · calc
      chapterVIDPositiveBranchOrdinate (-chapterVIDRoot) ^ 3 / -chapterVIDRoot *
          Real.exp (chapterVIDPositiveBranchExponent (-chapterVIDRoot)) ≤
          (64 / 100000) * (164 / 100) :=
        mul_le_mul hfactorUpper hexpUpper hexpNonneg (by norm_num)
      _ ≤ (11 / 10000 : ℝ) := by norm_num

/-- Every affine source parameter used by the certificate contour stays in the same positive
endpoint enclosure and below one. -/
theorem chapterVIDCertificateParameter_bounds (s : I) :
    (3 / 4000 : ℝ) ≤ chapterVIDCertificateParameter s ∧
      chapterVIDCertificateParameter s ≤ 1 := by
  obtain ⟨hqLower, hqUpper⟩ := chapterVIDCriticalParameterModulus_bounds
  unfold chapterVIDCertificateParameter
  simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, smul_eq_mul]
  rw [show (s : ℝ) * (chapterVIDCriticalParameterModulus - 1) + 1 =
      (1 - (s : ℝ)) + (s : ℝ) * chapterVIDCriticalParameterModulus by ring]
  constructor
  · have hleft : 0 ≤ (1 - (s : ℝ)) * (1 - 3 / 4000) :=
      mul_nonneg (by linarith [s.property.2]) (by norm_num)
    have hright : 0 ≤ (s : ℝ) *
        (chapterVIDCriticalParameterModulus - 3 / 4000) :=
      mul_nonneg s.property.1 (sub_nonneg.mpr hqLower)
    nlinarith
  · have hproduct : 0 ≤ (s : ℝ) * (1 - chapterVIDCriticalParameterModulus) :=
      mul_nonneg s.property.1 (by linarith)
    nlinarith

theorem chapterVIDCommonParameterRootPath_eq_parameter_rpow (s : I) :
    chapterVIDCommonParameterRootPath s =
      ((chapterVIDCertificateParameter s ^ ((3 : ℝ)⁻¹) : ℝ) : ℂ) := by
  change chapterVIPositiveRealCubicLift
      (AffineMap.lineMap 1 chapterVIDCriticalParameterModulus (s : ℝ)) = _
  have hparameter : 0 ≤
      AffineMap.lineMap 1 chapterVIDCriticalParameterModulus (s : ℝ) := by
    simpa [chapterVIDCertificateParameter] using
      (chapterVIDCertificateParameter_pos s).le
  unfold chapterVIPositiveRealCubicLift chapterVIPositiveRealCubicValue
    chapterVIDCertificateParameter
  rw [max_eq_left hparameter]

/-- The positive collision radius is exactly the cubic root of `-x_D`. -/
theorem chapterVIDCollisionRadius_cube :
    ‖chapterVIDCollisionLift‖ ^ 3 = -chapterVIDRoot := by
  have hpow := congrArg norm chapterVIDCollisionLift_pow
  rw [norm_pow, chapterVIDX, norm_real, Real.norm_eq_abs,
    abs_of_neg chapterVIDRoot_lt_zero] at hpow
  simpa using hpow

theorem chapterVIDCollisionRadius_eq_rpow :
    ‖chapterVIDCollisionLift‖ = (-chapterVIDRoot) ^ ((3 : ℝ)⁻¹) := by
  have hrootNonneg : 0 ≤ -chapterVIDRoot := by linarith [chapterVIDRoot_lt_zero]
  have hrpowNonneg : 0 ≤ (-chapterVIDRoot) ^ ((3 : ℝ)⁻¹) :=
    Real.rpow_nonneg hrootNonneg _
  have hrpowCube : ((-chapterVIDRoot) ^ ((3 : ℝ)⁻¹)) ^ (3 : ℕ) =
      -chapterVIDRoot := Real.rpow_inv_natCast_pow hrootNonneg (by norm_num)
  apply le_antisymm
  · apply le_of_pow_le_pow_left₀ (n := 3) (by norm_num) hrpowNonneg
    rw [chapterVIDCollisionRadius_cube, hrpowCube]
  · apply le_of_pow_le_pow_left₀ (n := 3) (by norm_num) (norm_nonneg _)
    rw [chapterVIDCollisionRadius_cube, hrpowCube]

end PoincareChapterVI
