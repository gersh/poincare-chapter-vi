/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.ChapterVIDRootCoordinates

/-!
# A canonical radial contour pinched by Poincare's two D branches

The two explicit §97 pole paths are negative real points.  Until the final collision, the inside
pole has smaller modulus than the outside pole.  This file uses that order to construct an actual
closed contour family: at every time its radius is a fixed convex combination of the two pole
radii, chosen so that the initial radius is exactly one.  Consequently the family starts at
Poincare's literal coefficient circle, avoids both selected poles for every time before D, and
passes through their common collision point at the final half-turn.

This is the global topological placement of the pinching contour in the `x^(1/3)` coordinate.  It
does not by itself assert a square-root sheet for the full integrand or `C²` regularity of the
inverse-monotone global parameterization; those are kept separate from the proved geometry.
-/

noncomputable section

open Complex Real
open scoped Topology unitInterval

namespace PoincareChapterVI

/-- Modulus of the pole that starts inside the unit coefficient circle. -/
def chapterVIDInsidePoleRadius (s : I) : ℝ :=
  ‖chapterVIDInsidePolePath s‖

/-- Modulus of the pole that starts outside the unit coefficient circle. -/
def chapterVIDOutsidePoleRadius (s : I) : ℝ :=
  ‖chapterVIDOutsidePolePath s‖

theorem chapterVIDInsidePoleRadius_pow (s : I) :
    chapterVIDInsidePoleRadius s ^ 3 = -chapterVIDInsideXPath s := by
  rw [chapterVIDInsidePoleRadius, ← norm_pow, chapterVIDInsidePolePath_pow, norm_real,
    Real.norm_eq_abs, abs_of_neg (chapterVIDInsideXPath_neg s)]

theorem chapterVIDOutsidePoleRadius_pow (s : I) :
    chapterVIDOutsidePoleRadius s ^ 3 = -chapterVIDOutsideXPath s := by
  rw [chapterVIDOutsidePoleRadius, ← norm_pow, chapterVIDOutsidePolePath_pow, norm_real,
    Real.norm_eq_abs, abs_of_neg (chapterVIDOutsideXPath_neg s)]

/-- The inside pole never crosses outside the exterior pole before they meet. -/
theorem chapterVIDInsidePoleRadius_le_outside (s : I) :
    chapterVIDInsidePoleRadius s ≤ chapterVIDOutsidePoleRadius s := by
  apply (pow_le_pow_iff_left₀
    (show 0 ≤ chapterVIDInsidePoleRadius s by exact norm_nonneg _)
    (show 0 ≤ chapterVIDOutsidePoleRadius s by exact norm_nonneg _)
    (by norm_num : (3 : ℕ) ≠ 0)).mp
  have hinside := (chapterVIDInsideXPath_mem s).1
  have houtside := (chapterVIDOutsideXPath_mem s).2
  calc
    chapterVIDInsidePoleRadius s ^ 3 = -chapterVIDInsideXPath s :=
      chapterVIDInsidePoleRadius_pow s
    _ ≤ -chapterVIDOutsideXPath s := by linarith
    _ = chapterVIDOutsidePoleRadius s ^ 3 :=
      (chapterVIDOutsidePoleRadius_pow s).symm

/-- Before the final time, the inside algebraic branch lies strictly to the right of D. -/
theorem chapterVIDRoot_lt_insideXPath_of_lt_one
    {s : I} (hs : (s : ℝ) < 1) :
    chapterVIDRoot < chapterVIDInsideXPath s := by
  have hle := (chapterVIDInsideXPath_mem s).1
  apply lt_of_le_of_ne hle
  intro heq
  have hparameter := chapterVIDInsideXPath_parameter s
  rw [← heq] at hparameter
  have hcritical := chapterVIDCriticalParameterModulus_lt_one
  unfold chapterVIDCriticalParameterModulus at hcritical hparameter
  simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, smul_eq_mul]
    at hparameter
  nlinarith

/-- Before the final time, the outside algebraic branch lies strictly to the left of D. -/
theorem chapterVIDOutsideXPath_lt_root_of_lt_one
    {s : I} (hs : (s : ℝ) < 1) :
    chapterVIDOutsideXPath s < chapterVIDRoot := by
  have hle := (chapterVIDOutsideXPath_mem s).2
  apply lt_of_le_of_ne hle
  intro heq
  have hparameter := chapterVIDOutsideXPath_negativeParameter s
  unfold chapterVIDOutsideNegativeParameter at hparameter
  rw [heq] at hparameter
  have hcritical := chapterVIDCriticalParameterModulus_lt_one
  unfold chapterVIDCriticalParameterModulus at hcritical hparameter
  simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, smul_eq_mul]
    at hparameter
  nlinarith

/-- The two pole radii are strictly separated at every pre-collision time. -/
theorem chapterVIDInsidePoleRadius_lt_outside_of_lt_one
    {s : I} (hs : (s : ℝ) < 1) :
    chapterVIDInsidePoleRadius s < chapterVIDOutsidePoleRadius s := by
  rw [← pow_lt_pow_iff_left₀
    (show 0 ≤ chapterVIDInsidePoleRadius s by exact norm_nonneg _)
    (show 0 ≤ chapterVIDOutsidePoleRadius s by exact norm_nonneg _)
    (by norm_num : (3 : ℕ) ≠ 0)]
  rw [chapterVIDInsidePoleRadius_pow, chapterVIDOutsidePoleRadius_pow]
  linarith [chapterVIDRoot_lt_insideXPath_of_lt_one hs,
    chapterVIDOutsideXPath_lt_root_of_lt_one hs]

theorem continuous_chapterVIDInsidePoleRadius :
    Continuous chapterVIDInsidePoleRadius :=
  chapterVIDInsidePolePath.continuous.norm

theorem continuous_chapterVIDOutsidePoleRadius :
    Continuous chapterVIDOutsidePoleRadius :=
  chapterVIDOutsidePolePath.continuous.norm

theorem chapterVIDInsidePoleRadius_zero_lt_one :
    chapterVIDInsidePoleRadius 0 < 1 := by
  simpa [chapterVIDInsidePoleRadius] using chapterVIDInsideEndpointLift_norm_lt_one

theorem one_lt_chapterVIDOutsidePoleRadius_zero :
    1 < chapterVIDOutsidePoleRadius 0 := by
  simpa [chapterVIDOutsidePoleRadius] using one_lt_chapterVIDOutsideEndpointLift_norm

/-- The unique constant convex weight that makes the initial intermediate radius equal to one. -/
def chapterVIDRadialContourWeight : ℝ :=
  (1 - chapterVIDInsidePoleRadius 0) /
    (chapterVIDOutsidePoleRadius 0 - chapterVIDInsidePoleRadius 0)

theorem chapterVIDRadialContourWeight_pos : 0 < chapterVIDRadialContourWeight := by
  unfold chapterVIDRadialContourWeight
  apply div_pos <;>
    linarith [chapterVIDInsidePoleRadius_zero_lt_one,
      one_lt_chapterVIDOutsidePoleRadius_zero]

theorem chapterVIDRadialContourWeight_lt_one : chapterVIDRadialContourWeight < 1 := by
  unfold chapterVIDRadialContourWeight
  rw [div_lt_one (by
    linarith [chapterVIDInsidePoleRadius_zero_lt_one,
      one_lt_chapterVIDOutsidePoleRadius_zero])]
  linarith [one_lt_chapterVIDOutsidePoleRadius_zero]

/-- Radius of the canonical contour lying between the two moving poles. -/
def chapterVIDRadialContourRadius (s : I) : ℝ :=
  chapterVIDInsidePoleRadius s + chapterVIDRadialContourWeight *
    (chapterVIDOutsidePoleRadius s - chapterVIDInsidePoleRadius s)

theorem continuous_chapterVIDRadialContourRadius :
    Continuous chapterVIDRadialContourRadius := by
  unfold chapterVIDRadialContourRadius
  exact continuous_chapterVIDInsidePoleRadius.add
    (continuous_const.mul
      (continuous_chapterVIDOutsidePoleRadius.sub
        continuous_chapterVIDInsidePoleRadius))

@[simp]
theorem chapterVIDRadialContourRadius_zero : chapterVIDRadialContourRadius 0 = 1 := by
  unfold chapterVIDRadialContourRadius chapterVIDRadialContourWeight
  field_simp [sub_ne_zero.mpr
    (ne_of_gt (chapterVIDInsidePoleRadius_lt_outside_of_lt_one
      (s := (0 : I)) (by norm_num)))]
  ring

theorem chapterVIDRadialContourRadius_between
    {s : I} (hs : (s : ℝ) < 1) :
    chapterVIDInsidePoleRadius s < chapterVIDRadialContourRadius s ∧
      chapterVIDRadialContourRadius s < chapterVIDOutsidePoleRadius s := by
  have hseparated := chapterVIDInsidePoleRadius_lt_outside_of_lt_one hs
  constructor
  · unfold chapterVIDRadialContourRadius
    nlinarith [chapterVIDRadialContourWeight_pos]
  · unfold chapterVIDRadialContourRadius
    nlinarith [chapterVIDRadialContourWeight_lt_one,
      chapterVIDRadialContourWeight_pos]

@[simp]
theorem chapterVIDPoleRadii_one_eq :
    chapterVIDInsidePoleRadius 1 = chapterVIDOutsidePoleRadius 1 := by
  simp [chapterVIDInsidePoleRadius, chapterVIDOutsidePoleRadius]

@[simp]
theorem chapterVIDRadialContourRadius_one :
    chapterVIDRadialContourRadius 1 = chapterVIDInsidePoleRadius 1 := by
  simp [chapterVIDRadialContourRadius]

/-- Positively oriented circle of arbitrary real radius, with the same angular parameter as the
literal unit coefficient contour. -/
def chapterVIDRadialCirclePath (radius : ℝ) :
    Path (radius : ℂ) (radius : ℂ) :=
  (chapterVIUnitCirclePath.map
    (f := fun z : ℂ ↦ (radius : ℂ) * z)
    (continuous_const.mul continuous_id)).cast (by simp) (by simp)

@[simp]
theorem chapterVIDRadialCirclePath_apply (radius : ℝ) (t : I) :
    chapterVIDRadialCirclePath radius t =
      (radius : ℂ) * chapterVIUnitCirclePath t := by
  simp [chapterVIDRadialCirclePath]

/-- The canonical global contour homotopy from the literal unit circle to the circle pinched at
D. -/
def chapterVIDRadialContourHomotopy : ContinuousMap.Homotopy
    (chapterVIUnitCirclePath : C(I, ℂ))
    (chapterVIDRadialCirclePath (chapterVIDInsidePoleRadius 1) : C(I, ℂ)) where
  toFun st :=
    (chapterVIDRadialContourRadius st.1 : ℂ) * chapterVIUnitCirclePath st.2
  continuous_toFun := by
    exact (Complex.ofRealCLM.continuous.comp
      (continuous_chapterVIDRadialContourRadius.comp continuous_fst)).mul
      (chapterVIUnitCirclePath.continuous.comp continuous_snd)
  map_zero_left t := by simp
  map_one_left t := by
    simp [chapterVIDRadialCirclePath_apply]

@[simp]
theorem chapterVIDRadialContourHomotopy_apply (s t : I) :
    chapterVIDRadialContourHomotopy (s, t) =
      (chapterVIDRadialContourRadius s : ℂ) * chapterVIUnitCirclePath t :=
  rfl

theorem chapterVIUnitCirclePath_norm (t : I) :
    ‖chapterVIUnitCirclePath t‖ = 1 := by
  change ‖circleMap 0 1 (AffineMap.lineMap 0 (2 * Real.pi) (t : ℝ))‖ = 1
  simp

theorem chapterVIDInsidePoleRadius_pos (s : I) :
    0 < chapterVIDInsidePoleRadius s := by
  have hpow := chapterVIDInsidePoleRadius_pow s
  have hx := chapterVIDInsideXPath_neg s
  by_contra h
  have hzero : chapterVIDInsidePoleRadius s = 0 :=
    le_antisymm (not_lt.mp h)
      (show 0 ≤ chapterVIDInsidePoleRadius s by exact norm_nonneg _)
  rw [hzero] at hpow
  norm_num at hpow
  linarith

theorem chapterVIDRadialContourRadius_pos (s : I) :
    0 < chapterVIDRadialContourRadius s := by
  by_cases hs : (s : ℝ) < 1
  · exact (chapterVIDInsidePoleRadius_pos s).trans
      (chapterVIDRadialContourRadius_between hs).1
  · have hs_one : s = 1 := by
      apply Subtype.ext
      simp only [Set.Icc.coe_one]
      exact le_antisymm s.property.2 (not_lt.mp hs)
    rw [hs_one, chapterVIDRadialContourRadius_one]
    exact chapterVIDInsidePoleRadius_pos 1

/-- Every point of the contour at time `s` has the chosen intermediate radius. -/
theorem chapterVIDRadialContourHomotopy_norm (s t : I) :
    ‖chapterVIDRadialContourHomotopy (s, t)‖ =
      chapterVIDRadialContourRadius s := by
  rw [chapterVIDRadialContourHomotopy_apply, norm_mul,
    chapterVIUnitCirclePath_norm, mul_one, norm_real, Real.norm_eq_abs,
    abs_of_pos (chapterVIDRadialContourRadius_pos s)]

/-- At every pre-collision time, the canonical contour avoids the inside pole. -/
theorem chapterVIDRadialContour_ne_insidePole
    {s : I} (hs : (s : ℝ) < 1) (t : I) :
    chapterVIDRadialContourHomotopy (s, t) ≠ chapterVIDInsidePolePath s := by
  intro heq
  have hnorm := congrArg norm heq
  rw [chapterVIDRadialContourHomotopy_norm] at hnorm
  exact (chapterVIDRadialContourRadius_between hs).1.ne hnorm.symm

/-- At every pre-collision time, the canonical contour avoids the outside pole. -/
theorem chapterVIDRadialContour_ne_outsidePole
    {s : I} (hs : (s : ℝ) < 1) (t : I) :
    chapterVIDRadialContourHomotopy (s, t) ≠ chapterVIDOutsidePolePath s := by
  intro heq
  have hnorm := congrArg norm heq
  rw [chapterVIDRadialContourHomotopy_norm] at hnorm
  exact (chapterVIDRadialContourRadius_between hs).2.ne hnorm

/-- The half-turn parameter at which a radial circle reaches the negative real axis. -/
def chapterVIDHalfTurn : I :=
  ⟨1 / 2, by norm_num⟩

@[simp]
theorem chapterVIUnitCirclePath_halfTurn :
    chapterVIUnitCirclePath chapterVIDHalfTurn = -1 := by
  change circleMap 0 1 (AffineMap.lineMap 0 (2 * Real.pi) (1 / 2 : ℝ)) = -1
  rw [show AffineMap.lineMap 0 (2 * Real.pi) (1 / 2 : ℝ) = Real.pi by
    simp [AffineMap.lineMap_apply]]
  simp [circleMap]

theorem chapterVIDCollisionLift_eq_neg_norm :
    chapterVIDCollisionLift = -(‖chapterVIDCollisionLift‖ : ℂ) := by
  rw [chapterVIDCollisionLift, chapterVINegativeRealCubicLift_eq_value]
  have hnegative : chapterVINegativeRealCubicValue chapterVIDRoot < 0 := by
    unfold chapterVINegativeRealCubicValue
    have hpositive : 0 < max (-chapterVIDRoot) 0 := by
      rw [max_eq_left (by linarith [chapterVIDRoot_lt_zero])]
      linarith [chapterVIDRoot_lt_zero]
    exact neg_neg_of_pos (Real.rpow_pos_of_pos hpositive _)
  rw [norm_real, Real.norm_eq_abs, abs_of_neg hnegative]
  push_cast
  ring

/-- The endpoint contour passes through the common pole exactly at its negative-real half-turn. -/
theorem chapterVIDRadialContour_collision :
    chapterVIDRadialContourHomotopy (1, chapterVIDHalfTurn) =
      chapterVIDCollisionLift := by
  rw [chapterVIDRadialContourHomotopy_apply, chapterVIDRadialContourRadius_one,
    chapterVIDInsidePoleRadius, chapterVIDInsidePolePath.target,
    chapterVIUnitCirclePath_halfTurn]
  calc
    (‖chapterVIDCollisionLift‖ : ℂ) * -1 =
        -(‖chapterVIDCollisionLift‖ : ℂ) := by ring
    _ = chapterVIDCollisionLift := chapterVIDCollisionLift_eq_neg_norm.symm

/-- Source-facing package for the explicit global contour placement. -/
structure ChapterVIDCanonicalRadialPinch where
  contour : ContinuousMap.Homotopy
    (chapterVIUnitCirclePath : C(I, ℂ))
    (chapterVIDRadialCirclePath (chapterVIDInsidePoleRadius 1) : C(I, ℂ))
  avoidsInside : ∀ {s : I}, (s : ℝ) < 1 → ∀ t : I,
    contour (s, t) ≠ chapterVIDInsidePolePath s
  avoidsOutside : ∀ {s : I}, (s : ℝ) < 1 → ∀ t : I,
    contour (s, t) ≠ chapterVIDOutsidePolePath s
  reachesCollision : contour (1, chapterVIDHalfTurn) = chapterVIDCollisionLift

/-- The canonical radial contour realizes the global topological pinch forced by the §97
inside/outside calculation. -/
def chapterVIDCanonicalRadialPinch : ChapterVIDCanonicalRadialPinch where
  contour := chapterVIDRadialContourHomotopy
  avoidsInside := chapterVIDRadialContour_ne_insidePole
  avoidsOutside := chapterVIDRadialContour_ne_outsidePole
  reachesCollision := chapterVIDRadialContour_collision

end PoincareChapterVI
