/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.ChapterVIDConnectorFactorTerminal
import PoincareChapterVI.ChapterVIDGlobalMorseBridge

/-!
# First-order orientation of the inverse-Morse endpoint

The endpoint anchor needed by the terminal compiled campaign depends on the orientation of the
local inverse-Morse coordinate.  This file starts that exact calculation by proving that
Poincare's explicit global change `u -> t` has a strictly positive real derivative at D, and
records the reciprocal derivative of both local inverse maps.
-/

noncomputable section

namespace PoincareChapterVI

/-- The derivative of the literal `u -> t` map in the logarithmic-derivative form used by the
compiled factor traces. -/
theorem hasDerivAt_chapterVIDRootToOriginalContour_logDerivative
    {u : ℂ} (hu : u ≠ 0) :
    HasDerivAt chapterVIDRootToOriginalContour
      (chapterVIDRootToOriginalContour u *
        chapterVIDRootSecondAnomalyLogDerivative u) u := by
  have h := hasDerivAt_chapterVIDRootSecondAnomaly (ζ := (1 : ℂ)) hu
  convert h using 1
  · funext w
    simp [chapterVIDRootSecondAnomaly]
  · simp [chapterVIDRootSecondAnomaly]

/-- Exact real expression for the derivative of Poincare's root-coordinate change at D. -/
theorem deriv_chapterVIDRootToOriginalContour_collision_eq_ofReal :
    deriv chapterVIDRootToOriginalContour chapterVIDCollisionLift =
      ((Real.exp ((100 / 30003 : ℝ) * (chapterVIDRoot⁻¹ - chapterVIDRoot)) *
        (1 - (100 / 10001 : ℝ) *
          (chapterVIDRoot⁻¹ + chapterVIDRoot)) : ℝ) : ℂ) := by
  rw [(hasDerivAt_chapterVIDRootToOriginalContour_logDerivative
    chapterVIDCollisionLift_ne_zero).deriv]
  have hfactor :
      chapterVIDRootToOriginalContour chapterVIDCollisionLift *
          chapterVIDRootSecondAnomalyLogDerivative chapterVIDCollisionLift =
        Complex.exp (chapterVIDRootExponentialArgument chapterVIDCollisionLift) *
          (1 - (100 / 10001 : ℂ) *
            ((chapterVIDCollisionLift ^ 3)⁻¹ + chapterVIDCollisionLift ^ 3)) := by
    unfold chapterVIDRootToOriginalContour chapterVIDRootSecondAnomalyLogDerivative
    field_simp [chapterVIDCollisionLift_ne_zero]
  rw [hfactor, chapterVIDCollisionLift_pow]
  have harg : chapterVIDRootExponentialArgument chapterVIDCollisionLift =
      ((100 / 30003 : ℝ) * (chapterVIDRoot⁻¹ - chapterVIDRoot) : ℝ) := by
    unfold chapterVIDRootExponentialArgument
    rw [chapterVIDCollisionLift_pow]
    unfold chapterVIDX
    push_cast
    rfl
  rw [harg, ← Complex.ofReal_exp]
  apply Complex.ext
  · simp only [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.div_re,
      Complex.inv_re, Complex.add_re, Complex.ofReal_re]
    norm_num [chapterVIDX, Complex.normSq_apply]
  · simp [chapterVIDX, Complex.mul_im, Complex.inv_im]

theorem deriv_chapterVIDRootToOriginalContour_collision_re_pos :
    0 < (deriv chapterVIDRootToOriginalContour chapterVIDCollisionLift).re := by
  rw [deriv_chapterVIDRootToOriginalContour_collision_eq_ofReal,
    Complex.ofReal_re]
  apply mul_pos (Real.exp_pos _)
  have hinvneg : chapterVIDRoot⁻¹ < 0 := by
    simpa only [one_div] using one_div_neg.mpr chapterVIDRoot_lt_zero
  have hxneg : chapterVIDRoot⁻¹ + chapterVIDRoot < 0 :=
    add_neg hinvneg chapterVIDRoot_lt_zero
  nlinarith

theorem deriv_chapterVIDRootToOriginalContour_collision_im :
    (deriv chapterVIDRootToOriginalContour chapterVIDCollisionLift).im = 0 := by
  rw [deriv_chapterVIDRootToOriginalContour_collision_eq_ofReal,
    Complex.ofReal_im]

/-- The local inverse used by the moving root construction has reciprocal strict derivative. -/
theorem hasStrictDerivAt_chapterVIDOriginalContourToRoot :
    HasStrictDerivAt chapterVIDOriginalContourToRoot
      (deriv chapterVIDRootToOriginalContour chapterVIDCollisionLift)⁻¹
      chapterVIDTBase := by
  have h := hasStrictDerivAt_chapterVIDRootToOriginalContour_collision.to_localInverse
    deriv_chapterVIDRootToOriginalContour_collision_ne_zero
  have hbase : chapterVIDRootToOriginalContour chapterVIDCollisionLift =
      chapterVIDTBase := rfl
  rw [hbase] at h
  simpa only [chapterVIDOriginalContourToRoot] using h

theorem deriv_chapterVIDOriginalContourToRoot :
    deriv chapterVIDOriginalContourToRoot chapterVIDTBase =
      (deriv chapterVIDRootToOriginalContour chapterVIDCollisionLift)⁻¹ :=
  hasStrictDerivAt_chapterVIDOriginalContourToRoot.hasDerivAt.deriv

theorem deriv_chapterVIDOriginalContourToRoot_re_pos :
    0 < (deriv chapterVIDOriginalContourToRoot chapterVIDTBase).re := by
  rw [deriv_chapterVIDOriginalContourToRoot, Complex.inv_re]
  exact div_pos deriv_chapterVIDRootToOriginalContour_collision_re_pos
    (Complex.normSq_pos.mpr deriv_chapterVIDRootToOriginalContour_collision_ne_zero)

theorem deriv_chapterVIDOriginalContourToRoot_im :
    (deriv chapterVIDOriginalContourToRoot chapterVIDTBase).im = 0 := by
  rw [deriv_chapterVIDOriginalContourToRoot, Complex.inv_im,
    deriv_chapterVIDRootToOriginalContour_collision_im]
  simp

/-- The deck-normalized map is pointwise the literal map, hence has the same oriented
derivative. -/
theorem deriv_chapterVIDDeckedRootToLocalContour_collision :
    deriv chapterVIDDeckedRootToLocalContour chapterVIDCollisionLift =
      deriv chapterVIDRootToOriginalContour chapterVIDCollisionLift := by
  congr 1
  funext u
  exact chapterVIDDeckedRootToLocalContour_eq u

theorem deriv_chapterVIDDeckedRootToLocalContour_collision_re_pos :
    0 < (deriv chapterVIDDeckedRootToLocalContour chapterVIDCollisionLift).re := by
  rw [deriv_chapterVIDDeckedRootToLocalContour_collision]
  exact deriv_chapterVIDRootToOriginalContour_collision_re_pos

end PoincareChapterVI
