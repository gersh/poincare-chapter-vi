/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.ChapterVIDAdmissibility
import PoincareChapterVI.ChapterVISourceCoordinates

/-!
# Poincaré's `x^(1/3)` source coordinate at D

In §97 Poincaré replaces the original contour variable `t` by `u = x^(1/c)`, because the
square of the perturbing integrand is single-valued in `(z^(1/c), u)`.  For the concrete choice
`a=-1`, `c=3`, and `sin φ = 200/10001`, the exact map back to the original §94 coordinate is

`t = u exp((100/30003) ((u^3)⁻¹-u^3))`.

Writing `ζ=z^(1/3)`, the circular second anomaly is `y=ζt`.  This file verifies those
identities and connects the synchronized real D branches to the literal source radicand in the
changed coordinate.  It is the missing coordinate bridge between Poincaré's §97 figure and the
original contour integral.
-/

noncomputable section

open Complex Real
open scoped Topology unitInterval

namespace PoincareChapterVI

/-- The exact §97 change from `u=x^(1/3)` back to the original §94 contour variable `t`. -/
def chapterVIDRootToOriginalContour (u : ℂ) : ℂ :=
  u * exp ((100 / 30003 : ℂ) * ((u ^ 3)⁻¹ - u ^ 3))

theorem continuousOn_chapterVIDRootToOriginalContour :
    ContinuousOn chapterVIDRootToOriginalContour ({0} : Set ℂ)ᶜ := by
  unfold chapterVIDRootToOriginalContour
  fun_prop (disch := simp_all)

/-- Cubing the changed coordinate recovers the exponential form of Kepler's equation. -/
theorem chapterVIDRootToOriginalContour_pow (u : ℂ) :
    chapterVIDRootToOriginalContour u ^ 3 =
      chapterVIKeplerExponential chapterVIDEccentricity (u ^ 3) := by
  unfold chapterVIDRootToOriginalContour chapterVIKeplerExponential chapterVIDEccentricity
  rw [mul_pow, ← Complex.exp_nat_mul]
  congr 1
  ring_nf

theorem chapterVIDRootToOriginalContour_ne_zero {u : ℂ} (hu : u ≠ 0) :
    chapterVIDRootToOriginalContour u ≠ 0 := by
  unfold chapterVIDRootToOriginalContour
  exact mul_ne_zero hu (exp_ne_zero _)

/-- For `a=-1`, the circular second anomaly is `y=ζt`, where `ζ^3=z`. -/
def chapterVIDRootSecondAnomaly (ζ u : ℂ) : ℂ :=
  ζ * chapterVIDRootToOriginalContour u

/-- The transformed coordinates have exactly the source parameter `z=ζ^3`. -/
theorem chapterVIDRootCoordinates_singularityParameter
    {ζ u : ℂ} (hu : u ≠ 0) :
    chapterVISingularityParameter (-1) 3 (-100 / 10001) 0
        (u ^ 3) (chapterVIDRootSecondAnomaly ζ u) = ζ ^ 3 := by
  rw [show (-100 / 10001 : ℂ) = ((-1 : ℤ) : ℂ) * chapterVIDEccentricity / 2 by
      norm_num [chapterVIDEccentricity],
    show (0 : ℂ) = ((3 : ℤ) : ℂ) * 0 / 2 by norm_num,
    chapterVI_singularityParameter_eq_keplerExponential_zpow]
  rw [← chapterVIDRootToOriginalContour_pow]
  simp only [chapterVIKeplerExponential, zero_div, zero_mul, Complex.exp_zero,
    chapterVIDRootSecondAnomaly, zpow_neg_one, zpow_ofNat]
  have ht := chapterVIDRootToOriginalContour_ne_zero hu
  field_simp [ht]

/-- Poincaré's first collision factor in the changed `(ζ,u)` coordinate. -/
def chapterVIDRootCoordinateCollisionFactorPlus (ζ u : ℂ) : ℂ :=
  chapterVIPlanarCollisionFactorPlus chapterVIDEccentricity chapterVIDComplement
    0 1 2 (u ^ 3) (chapterVIDRootSecondAnomaly ζ u)

/-- The literal planar source radicand in Poincaré's changed `(ζ,u)` coordinate. -/
def chapterVIDRootCoordinateRadicand (ζ u : ℂ) : ℂ :=
  chapterVIPlanarSourceRadicand chapterVIDEccentricity chapterVIDComplement
    0 1 2 2 (u ^ 3) (chapterVIDRootSecondAnomaly ζ u)

theorem chapterVIDRootCoordinateRadicand_eq_factors (ζ u : ℂ) :
    chapterVIDRootCoordinateRadicand ζ u =
      chapterVIDRootCoordinateCollisionFactorPlus ζ u *
        chapterVIPlanarCollisionFactorMinus chapterVIDEccentricity chapterVIDComplement
          0 1 2 (u ^ 3) (chapterVIDRootSecondAnomaly ζ u) := by
  rfl

/-- The positive real cubic root, used for Poincaré's radial `ζ=z^(1/3)` segment. -/
noncomputable def chapterVIPositiveRealCubicValue (x : ℝ) : ℝ :=
  max x 0 ^ ((3 : ℝ)⁻¹)

noncomputable def chapterVIPositiveRealCubicLift (x : ℝ) : ℂ :=
  chapterVIPositiveRealCubicValue x

theorem continuous_chapterVIPositiveRealCubicLift :
    Continuous chapterVIPositiveRealCubicLift := by
  unfold chapterVIPositiveRealCubicLift chapterVIPositiveRealCubicValue
  fun_prop (disch := norm_num)

@[simp]
theorem chapterVIPositiveRealCubicLift_pow
    {x : ℝ} (hx : 0 ≤ x) :
    chapterVIPositiveRealCubicLift x ^ 3 = (x : ℂ) := by
  have hrpow : (x ^ ((3 : ℝ)⁻¹)) ^ (3 : ℕ) = x :=
    Real.rpow_inv_natCast_pow hx (by norm_num)
  unfold chapterVIPositiveRealCubicLift chapterVIPositiveRealCubicValue
  rw [max_eq_left hx]
  exact_mod_cast hrpow

theorem chapterVIPositiveRealCubicValue_pow
    {x : ℝ} (hx : 0 ≤ x) :
    chapterVIPositiveRealCubicValue x ^ 3 = x := by
  unfold chapterVIPositiveRealCubicValue
  rw [max_eq_left hx]
  exact Real.rpow_inv_natCast_pow hx (by norm_num)

/-- The real value underlying the selected negative-real cubic lift. -/
noncomputable def chapterVINegativeRealCubicValue (x : ℝ) : ℝ :=
  -(max (-x) 0 ^ ((3 : ℝ)⁻¹))

@[simp]
theorem chapterVINegativeRealCubicValue_pow
    {x : ℝ} (hx : x ≤ 0) :
    chapterVINegativeRealCubicValue x ^ 3 = x := by
  have hnonneg : 0 ≤ -x := neg_nonneg.mpr hx
  have hrpow := Real.rpow_inv_natCast_pow hnonneg (by norm_num : (3 : ℕ) ≠ 0)
  unfold chapterVINegativeRealCubicValue
  rw [max_eq_left hnonneg]
  calc
    (-((-x) ^ ((3 : ℝ)⁻¹))) ^ (3 : ℕ) =
        -(((-x) ^ ((3 : ℝ)⁻¹)) ^ (3 : ℕ)) := by ring
    _ = -(-x) := by
      exact congrArg Neg.neg hrpow
    _ = x := by ring

@[simp]
theorem chapterVINegativeRealCubicLift_eq_value (x : ℝ) :
    chapterVINegativeRealCubicLift x = chapterVINegativeRealCubicValue x := by
  unfold chapterVINegativeRealCubicLift chapterVINegativeRealCubicValue
  push_cast
  rfl

/-- The real restriction of the map from `u=x^(1/3)` back to `t`. -/
def chapterVIDRootToOriginalContourReal (u : ℝ) : ℝ :=
  u * Real.exp ((100 / 30003 : ℝ) * ((u ^ 3)⁻¹ - u ^ 3))

theorem chapterVIDRootToOriginalContour_ofReal (u : ℝ) :
    chapterVIDRootToOriginalContour (u : ℂ) =
      (chapterVIDRootToOriginalContourReal u : ℂ) := by
  unfold chapterVIDRootToOriginalContour chapterVIDRootToOriginalContourReal
  push_cast
  rfl

theorem chapterVIDRootToOriginalContourReal_pow (u : ℝ) :
    chapterVIDRootToOriginalContourReal u ^ 3 =
      u ^ 3 * Real.exp ((100 / 10001 : ℝ) * ((u ^ 3)⁻¹ - u ^ 3)) := by
  unfold chapterVIDRootToOriginalContourReal
  rw [mul_pow, ← Real.exp_nat_mul]
  congr 1
  ring_nf

/-- The real second anomaly reconstructed from `ζ=z^(1/3)` and `u=x^(1/3)`. -/
def chapterVIDRootSecondAnomalyReal (ζ u : ℝ) : ℝ :=
  ζ * chapterVIDRootToOriginalContourReal u

theorem chapterVIDRootSecondAnomaly_ofReal (ζ u : ℝ) :
    chapterVIDRootSecondAnomaly (ζ : ℂ) (u : ℂ) =
      (chapterVIDRootSecondAnomalyReal ζ u : ℂ) := by
  rw [chapterVIDRootSecondAnomaly, chapterVIDRootToOriginalContour_ofReal]
  simp [chapterVIDRootSecondAnomalyReal]

/-- The actual radial source parameter `ζ=z^(1/3)` shared by the two D branches. -/
noncomputable def chapterVIDCommonParameterRootPath : Path
    (chapterVIPositiveRealCubicLift 1)
    (chapterVIPositiveRealCubicLift chapterVIDCriticalParameterModulus) :=
  (Path.segment (1 : ℝ) chapterVIDCriticalParameterModulus).map
    continuous_chapterVIPositiveRealCubicLift

theorem chapterVIDCriticalParameterModulus_pos :
    0 < chapterVIDCriticalParameterModulus := by
  exact chapterVIDCurveThreeSmoothParameter_pos chapterVIDRoot_lt_zero

theorem chapterVIDCurveThreeY_at_root :
    (chapterVIDCurveThreeY chapterVIDRoot : ℂ) = chapterVIDY := by
  unfold chapterVIDCurveThreeY chapterVIDY chapterVIDX
  push_cast
  norm_num

@[simp]
theorem chapterVIDCommonParameterRootPath_pow (s : I) :
    chapterVIDCommonParameterRootPath s ^ 3 =
      (chapterVIDCurveThreeSmoothParameter (chapterVIDInsideXPath s) : ℂ) := by
  change chapterVIPositiveRealCubicLift
      (AffineMap.lineMap 1 chapterVIDCriticalParameterModulus (s : ℝ)) ^ 3 = _
  rw [chapterVIPositiveRealCubicLift_pow]
  · exact_mod_cast (chapterVIDInsideXPath_parameter s).symm
  · have hs0 := s.property.1
    have hs1 := s.property.2
    simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, smul_eq_mul]
    nlinarith [chapterVIDCriticalParameterModulus_pos]

theorem chapterVIDCommonParameterRootPath_eq_value (s : I) :
    chapterVIDCommonParameterRootPath s =
      (chapterVIPositiveRealCubicValue
        (chapterVIDCurveThreeSmoothParameter (chapterVIDInsideXPath s)) : ℂ) := by
  change chapterVIPositiveRealCubicLift
      (AffineMap.lineMap 1 chapterVIDCriticalParameterModulus (s : ℝ)) = _
  rw [chapterVIDInsideXPath_parameter]
  rfl

/-- At fixed nonzero `x`, the concrete source parameter is injective in the cube `y^3`. -/
theorem chapterVID_singularityParameter_y_cube_injective
    {x y₁ y₂ : ℂ} (hx : x ≠ 0)
    (hparameter :
      chapterVISingularityParameter (-1) 3 (-100 / 10001) 0 x y₁ =
        chapterVISingularityParameter (-1) 3 (-100 / 10001) 0 x y₂) :
    y₁ ^ 3 = y₂ ^ 3 := by
  unfold chapterVISingularityParameter at hparameter
  simp only [zpow_neg_one, zpow_ofNat, zero_mul, add_zero] at hparameter
  have hfactor : x⁻¹ * exp ((-100 / 10001 : ℂ) * (x⁻¹ - x)) ≠ 0 :=
    mul_ne_zero (inv_ne_zero hx) (exp_ne_zero _)
  apply mul_left_cancel₀ hfactor
  calc
    (x⁻¹ * exp ((-100 / 10001 : ℂ) * (x⁻¹ - x))) * y₁ ^ 3 =
        x⁻¹ * y₁ ^ 3 * exp ((-100 / 10001 : ℂ) * (x⁻¹ - x)) := by ring
    _ = x⁻¹ * y₂ ^ 3 * exp ((-100 / 10001 : ℂ) * (x⁻¹ - x)) := hparameter
    _ = (x⁻¹ * exp ((-100 / 10001 : ℂ) * (x⁻¹ - x))) * y₂ ^ 3 := by ring

noncomputable def chapterVIDInsidePoleValue (s : I) : ℝ :=
  chapterVINegativeRealCubicValue (chapterVIDInsideXPath s)

noncomputable def chapterVIDOutsidePoleValue (s : I) : ℝ :=
  chapterVINegativeRealCubicValue (chapterVIDOutsideXPath s)

noncomputable def chapterVIDCommonParameterRootValue (s : I) : ℝ :=
  chapterVIPositiveRealCubicValue
    (chapterVIDCurveThreeSmoothParameter (chapterVIDInsideXPath s))

theorem chapterVIDInsidePolePath_eq_value (s : I) :
    chapterVIDInsidePolePath s = (chapterVIDInsidePoleValue s : ℂ) := by
  change chapterVINegativeRealCubicLift (chapterVIDInsideXPath s) = _
  rw [chapterVINegativeRealCubicLift_eq_value]
  rfl

theorem chapterVIDOutsidePolePath_eq_value (s : I) :
    chapterVIDOutsidePolePath s = (chapterVIDOutsidePoleValue s : ℂ) := by
  change chapterVINegativeRealCubicLift (chapterVIDOutsideXPath s) = _
  rw [chapterVINegativeRealCubicLift_eq_value]
  rfl

theorem chapterVIDCommonParameterRootPath_eq_realValue (s : I) :
    chapterVIDCommonParameterRootPath s =
      (chapterVIDCommonParameterRootValue s : ℂ) := by
  exact chapterVIDCommonParameterRootPath_eq_value s

noncomputable def chapterVIDInsideTransformedSecondAnomaly (s : I) : ℝ :=
  chapterVIDRootSecondAnomalyReal
    (chapterVIDCommonParameterRootValue s) (chapterVIDInsidePoleValue s)

noncomputable def chapterVIDOutsideTransformedSecondAnomaly (s : I) : ℝ :=
  chapterVIDRootSecondAnomalyReal
    (chapterVIDCommonParameterRootValue s) (chapterVIDOutsidePoleValue s)

theorem chapterVIDInsideRootSecondAnomaly_eq_realValue (s : I) :
    chapterVIDRootSecondAnomaly (chapterVIDCommonParameterRootPath s)
        (chapterVIDInsidePolePath s) =
      (chapterVIDInsideTransformedSecondAnomaly s : ℂ) := by
  rw [chapterVIDCommonParameterRootPath_eq_realValue,
    chapterVIDInsidePolePath_eq_value, chapterVIDRootSecondAnomaly_ofReal]
  rfl

theorem chapterVIDOutsideRootSecondAnomaly_eq_realValue (s : I) :
    chapterVIDRootSecondAnomaly (chapterVIDCommonParameterRootPath s)
        (chapterVIDOutsidePolePath s) =
      (chapterVIDOutsideTransformedSecondAnomaly s : ℂ) := by
  rw [chapterVIDCommonParameterRootPath_eq_realValue,
    chapterVIDOutsidePolePath_eq_value, chapterVIDRootSecondAnomaly_ofReal]
  rfl

/-- The transformed second anomaly on the inside path is exactly Poincaré's curve-(3) value,
not merely a value differing by a cube root of unity. -/
theorem chapterVIDInsideTransformedSecondAnomaly_eq_curveThree (s : I) :
    chapterVIDInsideTransformedSecondAnomaly s =
      chapterVIDCurveThreeY (chapterVIDInsideXPath s) := by
  have hu : chapterVIDInsidePolePath s ≠ 0 := by
    intro hzero
    have hpow := congrArg (fun z : ℂ ↦ z ^ 3) hzero
    rw [chapterVIDInsidePolePath_pow, zero_pow (by norm_num)] at hpow
    exact (ofReal_ne_zero.mpr (ne_of_lt (chapterVIDInsideXPath_neg s))) hpow
  have htrans := chapterVIDRootCoordinates_singularityParameter
    (ζ := chapterVIDCommonParameterRootPath s)
    (u := chapterVIDInsidePolePath s) hu
  rw [chapterVIDInsidePolePath_pow, chapterVIDCommonParameterRootPath_pow] at htrans
  have hbranch := chapterVID_singularityParameter_curveThree_eq_smooth
    (chapterVIDInsideXPath_neg s)
  have hcubes :
      chapterVIDRootSecondAnomaly (chapterVIDCommonParameterRootPath s)
          (chapterVIDInsidePolePath s) ^ 3 =
        (chapterVIDCurveThreeY (chapterVIDInsideXPath s) : ℂ) ^ 3 := by
    apply chapterVID_singularityParameter_y_cube_injective
      (x := (chapterVIDInsideXPath s : ℂ))
      (by exact_mod_cast (ne_of_lt (chapterVIDInsideXPath_neg s)))
    exact htrans.trans hbranch.symm
  rw [chapterVIDInsideRootSecondAnomaly_eq_realValue] at hcubes
  have hreal : chapterVIDInsideTransformedSecondAnomaly s ^ 3 =
      chapterVIDCurveThreeY (chapterVIDInsideXPath s) ^ 3 := by
    exact_mod_cast hcubes
  exact (show Function.Injective (fun x : ℝ ↦ x ^ 3) from
    (Odd.strictMono_pow (by decide : Odd 3)).injective) hreal

/-- The same exact source-coordinate identification on the exterior path. -/
theorem chapterVIDOutsideTransformedSecondAnomaly_eq_curveThree (s : I) :
    chapterVIDOutsideTransformedSecondAnomaly s =
      chapterVIDCurveThreeY (chapterVIDOutsideXPath s) := by
  have hu : chapterVIDOutsidePolePath s ≠ 0 := by
    intro hzero
    have hpow := congrArg (fun z : ℂ ↦ z ^ 3) hzero
    rw [chapterVIDOutsidePolePath_pow, zero_pow (by norm_num)] at hpow
    exact (ofReal_ne_zero.mpr (ne_of_lt (chapterVIDOutsideXPath_neg s))) hpow
  have htrans := chapterVIDRootCoordinates_singularityParameter
    (ζ := chapterVIDCommonParameterRootPath s)
    (u := chapterVIDOutsidePolePath s) hu
  rw [chapterVIDOutsidePolePath_pow, chapterVIDCommonParameterRootPath_pow] at htrans
  rw [chapterVIDPolePaths_parameter_synchronized] at htrans
  have hbranch := chapterVID_singularityParameter_curveThree_eq_smooth
    (chapterVIDOutsideXPath_neg s)
  have hcubes :
      chapterVIDRootSecondAnomaly (chapterVIDCommonParameterRootPath s)
          (chapterVIDOutsidePolePath s) ^ 3 =
        (chapterVIDCurveThreeY (chapterVIDOutsideXPath s) : ℂ) ^ 3 := by
    apply chapterVID_singularityParameter_y_cube_injective
      (x := (chapterVIDOutsideXPath s : ℂ))
      (by exact_mod_cast (ne_of_lt (chapterVIDOutsideXPath_neg s)))
    exact htrans.trans hbranch.symm
  rw [chapterVIDOutsideRootSecondAnomaly_eq_realValue] at hcubes
  have hreal : chapterVIDOutsideTransformedSecondAnomaly s ^ 3 =
      chapterVIDCurveThreeY (chapterVIDOutsideXPath s) ^ 3 := by
    exact_mod_cast hcubes
  exact (show Function.Injective (fun x : ℝ ↦ x ^ 3) from
    (Odd.strictMono_pow (by decide : Odd 3)).injective) hreal

theorem chapterVIDInsideRootSecondAnomaly_eq_curveThree (s : I) :
    chapterVIDRootSecondAnomaly (chapterVIDCommonParameterRootPath s)
        (chapterVIDInsidePolePath s) =
      (chapterVIDCurveThreeY (chapterVIDInsideXPath s) : ℂ) := by
  rw [chapterVIDInsideRootSecondAnomaly_eq_realValue,
    chapterVIDInsideTransformedSecondAnomaly_eq_curveThree]

theorem chapterVIDOutsideRootSecondAnomaly_eq_curveThree (s : I) :
    chapterVIDRootSecondAnomaly (chapterVIDCommonParameterRootPath s)
        (chapterVIDOutsidePolePath s) =
      (chapterVIDCurveThreeY (chapterVIDOutsideXPath s) : ℂ) := by
  rw [chapterVIDOutsideRootSecondAnomaly_eq_realValue,
    chapterVIDOutsideTransformedSecondAnomaly_eq_curveThree]

/-- The inside pole path is pointwise a zero of the literal source factor after Poincaré's
§97 change of variables. -/
theorem chapterVIDInsideRootCoordinateCollision (s : I) :
    chapterVIDRootCoordinateCollisionFactorPlus
      (chapterVIDCommonParameterRootPath s) (chapterVIDInsidePolePath s) = 0 := by
  unfold chapterVIDRootCoordinateCollisionFactorPlus
  rw [chapterVIDInsidePolePath_pow,
    chapterVIDInsideRootSecondAnomaly_eq_curveThree]
  exact chapterVID_curveThree_collisionFactorPlus (chapterVIDInsideXPath_neg s)

/-- The exterior pole path is the second pointwise zero of the transformed source factor. -/
theorem chapterVIDOutsideRootCoordinateCollision (s : I) :
    chapterVIDRootCoordinateCollisionFactorPlus
      (chapterVIDCommonParameterRootPath s) (chapterVIDOutsidePolePath s) = 0 := by
  unfold chapterVIDRootCoordinateCollisionFactorPlus
  rw [chapterVIDOutsidePolePath_pow,
    chapterVIDOutsideRootSecondAnomaly_eq_curveThree]
  exact chapterVID_curveThree_collisionFactorPlus (chapterVIDOutsideXPath_neg s)

theorem chapterVIDInsideRootCoordinateRadicand_zero (s : I) :
    chapterVIDRootCoordinateRadicand
      (chapterVIDCommonParameterRootPath s) (chapterVIDInsidePolePath s) = 0 := by
  rw [chapterVIDRootCoordinateRadicand_eq_factors,
    chapterVIDInsideRootCoordinateCollision, zero_mul]

theorem chapterVIDOutsideRootCoordinateRadicand_zero (s : I) :
    chapterVIDRootCoordinateRadicand
      (chapterVIDCommonParameterRootPath s) (chapterVIDOutsidePolePath s) = 0 := by
  rw [chapterVIDRootCoordinateRadicand_eq_factors,
    chapterVIDOutsideRootCoordinateCollision, zero_mul]

/-- The two transformed branches carry exactly the external source parameter `z=ζ^3`. -/
theorem chapterVIDInsideRootCoordinate_sourceParameter (s : I) :
    chapterVISingularityParameter (-1) 3 (-100 / 10001) 0
        (chapterVIDInsidePolePath s ^ 3)
        (chapterVIDRootSecondAnomaly (chapterVIDCommonParameterRootPath s)
          (chapterVIDInsidePolePath s)) =
      chapterVIDCommonParameterRootPath s ^ 3 := by
  apply chapterVIDRootCoordinates_singularityParameter
  intro hzero
  have hpow := congrArg (fun z : ℂ ↦ z ^ 3) hzero
  rw [chapterVIDInsidePolePath_pow, zero_pow (by norm_num)] at hpow
  exact (ofReal_ne_zero.mpr (ne_of_lt (chapterVIDInsideXPath_neg s))) hpow

theorem chapterVIDOutsideRootCoordinate_sourceParameter (s : I) :
    chapterVISingularityParameter (-1) 3 (-100 / 10001) 0
        (chapterVIDOutsidePolePath s ^ 3)
        (chapterVIDRootSecondAnomaly (chapterVIDCommonParameterRootPath s)
          (chapterVIDOutsidePolePath s)) =
      chapterVIDCommonParameterRootPath s ^ 3 := by
  apply chapterVIDRootCoordinates_singularityParameter
  intro hzero
  have hpow := congrArg (fun z : ℂ ↦ z ^ 3) hzero
  rw [chapterVIDOutsidePolePath_pow, zero_pow (by norm_num)] at hpow
  exact (ofReal_ne_zero.mpr (ne_of_lt (chapterVIDOutsideXPath_neg s))) hpow

/-- Complete source-coordinate data for Poincaré's D pinch in the `x^(1/3)` plane. -/
structure ChapterVIDRootCoordinatePinch where
  parameterRoot : Path
    (chapterVIPositiveRealCubicLift 1)
    (chapterVIPositiveRealCubicLift chapterVIDCriticalParameterModulus)
  insidePole : Path chapterVIDInsideEndpointLift chapterVIDCollisionLift
  outsidePole : Path chapterVIDOutsideEndpointLift chapterVIDCollisionLift
  insideRadicand_zero : ∀ s : I,
    chapterVIDRootCoordinateRadicand (parameterRoot s) (insidePole s) = 0
  outsideRadicand_zero : ∀ s : I,
    chapterVIDRootCoordinateRadicand (parameterRoot s) (outsidePole s) = 0
  insideSourceParameter : ∀ s : I,
    chapterVISingularityParameter (-1) 3 (-100 / 10001) 0
        (insidePole s ^ 3)
        (chapterVIDRootSecondAnomaly (parameterRoot s) (insidePole s)) =
      parameterRoot s ^ 3
  outsideSourceParameter : ∀ s : I,
    chapterVISingularityParameter (-1) 3 (-100 / 10001) 0
        (outsidePole s ^ 3)
        (chapterVIDRootSecondAnomaly (parameterRoot s) (outsidePole s)) =
      parameterRoot s ^ 3

noncomputable def chapterVIDRootCoordinatePinch : ChapterVIDRootCoordinatePinch where
  parameterRoot := chapterVIDCommonParameterRootPath
  insidePole := chapterVIDInsidePolePath
  outsidePole := chapterVIDOutsidePolePath
  insideRadicand_zero := chapterVIDInsideRootCoordinateRadicand_zero
  outsideRadicand_zero := chapterVIDOutsideRootCoordinateRadicand_zero
  insideSourceParameter := chapterVIDInsideRootCoordinate_sourceParameter
  outsideSourceParameter := chapterVIDOutsideRootCoordinate_sourceParameter

/-- Source-coordinate form of the genuine-pinch conclusion: no smooth closed contour beginning
at the unit circle in Poincaré's `x^(1/3)` plane can avoid both literal-radicand zero paths until
they coalesce at D. -/
theorem chapterVIDRootCoordinatePinch_no_avoiding_contour
    {b : ℂ} {final : Path b b}
    (contour : ContinuousMap.Homotopy
      (chapterVIUnitCirclePath : C(I, ℂ)) (final : C(I, ℂ)))
    (hcontourClosed : ∀ s : I, contour (s, 0) = contour (s, 1)) :
    ¬ (Nonempty (ChapterVIMovingPoleAvoidance contour
          chapterVIDRootCoordinatePinch.insidePole) ∧
      Nonempty (ChapterVIMovingPoleAvoidance contour
          chapterVIDRootCoordinatePinch.outsidePole)) := by
  exact chapterVID_not_both_canonicalMovingPoleAvoidances contour hcontourClosed

/-- Fully source-facing admissibility statement.  A closed smooth contour family beginning at
the unit circle cannot keep Poincaré's literal transformed radicand nonzero throughout the radial
continuation from `|ζ|=1` to D.  The only regularity data left explicit are the two translated
`C²` conditions required by the Stokes/winding theorem. -/
theorem chapterVIDRootCoordinateRadicand_forces_contour_singularity
    {b : ℂ} {final : Path b b}
    (contour : ContinuousMap.Homotopy
      (chapterVIUnitCirclePath : C(I, ℂ)) (final : C(I, ℂ)))
    (hcontourClosed : ∀ s : I, contour (s, 0) = contour (s, 1))
    (hregular : ∀ s t : I,
      chapterVIDRootCoordinateRadicand (chapterVIDCommonParameterRootPath s)
        (contour (s, t)) ≠ 0)
    (hinsideC2 : ContDiffOn ℝ 2
      (fun st : ℝ × ℝ ↦ Set.IccExtend zero_le_one
        ((chapterVITranslateContourHomotopy contour
          chapterVIDInsidePolePath).extend st.1) st.2)
      (Set.Icc 0 1))
    (houtsideC2 : ContDiffOn ℝ 2
      (fun st : ℝ × ℝ ↦ Set.IccExtend zero_le_one
        ((chapterVITranslateContourHomotopy contour
          chapterVIDOutsidePolePath).extend st.1) st.2)
      (Set.Icc 0 1)) : False := by
  have hinsideAvoid : ∀ s t : I, contour (s, t) ≠ chapterVIDInsidePolePath s := by
    intro s t heq
    apply hregular s t
    rw [heq]
    exact chapterVIDInsideRootCoordinateRadicand_zero s
  have houtsideAvoid : ∀ s t : I, contour (s, t) ≠ chapterVIDOutsidePolePath s := by
    intro s t heq
    apply hregular s t
    rw [heq]
    exact chapterVIDOutsideRootCoordinateRadicand_zero s
  apply chapterVIDRootCoordinatePinch_no_avoiding_contour contour hcontourClosed
  exact ⟨⟨chapterVIMovingPoleAvoidanceOfPointwise contour chapterVIDInsidePolePath
      hinsideAvoid hinsideC2⟩,
    ⟨chapterVIMovingPoleAvoidanceOfPointwise contour chapterVIDOutsidePolePath
      houtsideAvoid houtsideC2⟩⟩

end PoincareChapterVI
