/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.ChapterVICriticalParameter

/-!
# Transversality of Poincaré's concrete double point D

This file discharges the premise isolated in `ChapterVICriticalParameter.lean`.  Along the
external `z` direction, the first anomaly remains fixed and the second anomaly passes through
the selected cubic-root and Kepler inverse branches.  Both inverse derivatives are nonzero.
The vanishing collision factor therefore has derivative `-2 y'(z_D) ≠ 0`; multiplication by the
already-proved nonzero companion factor gives `k'(z_D) ≠ 0` for the full critical value.

No numerical approximation or compiled certificate is needed for this step: the finite
nonvanishing inputs were already established for D, and the rest is exact analytic calculus.
-/

noncomputable section

open Filter Topology

namespace PoincareChapterVI

/-- At fixed `t_D`, Poincaré's second-mean input at `z_D` is the cube of its base value. -/
theorem chapterVIDParameterInput_base :
    chapterVIDZBase / (chapterVIDTBase ^ (3 : ℤ)) ^ (-1 : ℤ) =
      chapterVIKeplerExponential 0 chapterVIDY ^ (3 : ℤ) := by
  unfold chapterVIDZBase chapterVIContourBase chapterVIMeanToContourMap
  rw [chapterVIDTBase_pow]
  simp [chapterVIKeplerExponential]
  field_simp [chapterVIDX_ne_zero, Complex.exp_ne_zero]

/-- The selected cubic-root branch for the second mean anomaly when `z` varies and `t=t_D`. -/
def chapterVIDParameterSecondMean (z : ℂ) : ℂ :=
  let base := chapterVIKeplerExponential 0 chapterVIDY
  let hbase : base ≠ 0 := chapterVIKeplerExponential_ne_zero 0 chapterVIDY_ne_zero
  chapterVIPowerLocalInverse 3 base hbase (by norm_num)
    (z / (chapterVIDTBase ^ (3 : ℤ)) ^ (-1 : ℤ))

/-- The second eccentric-anomaly exponential along the same external-parameter slice. -/
def chapterVIDParameterY (z : ℂ) : ℂ :=
  chapterVIKeplerLocalInverse 0 chapterVIDY chapterVIDY_ne_zero
    chapterVID_secondKeplerCritical (chapterVIDParameterSecondMean z)

@[simp]
theorem chapterVIDParameterSecondMean_base :
    chapterVIDParameterSecondMean chapterVIDZBase =
      chapterVIKeplerExponential 0 chapterVIDY := by
  unfold chapterVIDParameterSecondMean
  rw [chapterVIDParameterInput_base]
  exact chapterVIPowerLocalInverse_apply_base 3
    (chapterVIKeplerExponential 0 chapterVIDY)
    (chapterVIKeplerExponential_ne_zero 0 chapterVIDY_ne_zero) (by norm_num)

@[simp]
theorem chapterVIDParameterY_base :
    chapterVIDParameterY chapterVIDZBase = chapterVIDY := by
  unfold chapterVIDParameterY
  rw [chapterVIDParameterSecondMean_base]
  exact chapterVIKeplerLocalInverse_apply_base 0 chapterVIDY chapterVIDY_ne_zero
    chapterVID_secondKeplerCritical

theorem hasDerivAt_chapterVIDParameterSecondMean :
    HasDerivAt chapterVIDParameterSecondMean
      ((((3 : ℤ) : ℂ) *
          (chapterVIKeplerExponential 0 chapterVIDY) ^ ((3 : ℤ) - 1))⁻¹ *
        (1 / (chapterVIDTBase ^ (3 : ℤ)) ^ (-1 : ℤ))) chapterVIDZBase := by
  have hinput : HasDerivAt
      (fun z : ℂ ↦ z / (chapterVIDTBase ^ (3 : ℤ)) ^ (-1 : ℤ))
      (1 / (chapterVIDTBase ^ (3 : ℤ)) ^ (-1 : ℤ)) chapterVIDZBase :=
    (hasDerivAt_id chapterVIDZBase).div_const
      ((chapterVIDTBase ^ (3 : ℤ)) ^ (-1 : ℤ))
  have houter : HasDerivAt
      (chapterVIPowerLocalInverse 3
        (chapterVIKeplerExponential 0 chapterVIDY)
        (chapterVIKeplerExponential_ne_zero 0 chapterVIDY_ne_zero) (by norm_num))
      ((((3 : ℤ) : ℂ) *
          (chapterVIKeplerExponential 0 chapterVIDY) ^ ((3 : ℤ) - 1))⁻¹)
      (chapterVIDZBase / (chapterVIDTBase ^ (3 : ℤ)) ^ (-1 : ℤ)) := by
    simpa only [chapterVIDParameterInput_base] using
      hasDerivAt_chapterVIPowerLocalInverse 3
        (chapterVIKeplerExponential 0 chapterVIDY)
        (chapterVIKeplerExponential_ne_zero 0 chapterVIDY_ne_zero) (by norm_num)
  have hcomp := houter.comp chapterVIDZBase hinput
  unfold chapterVIDParameterSecondMean
  exact hcomp

theorem deriv_chapterVIDParameterSecondMean_ne_zero :
    deriv chapterVIDParameterSecondMean chapterVIDZBase ≠ 0 := by
  rw [hasDerivAt_chapterVIDParameterSecondMean.deriv]
  apply mul_ne_zero
  · exact inv_ne_zero (mul_ne_zero (by norm_num)
      (zpow_ne_zero _ (chapterVIKeplerExponential_ne_zero 0 chapterVIDY_ne_zero)))
  · exact div_ne_zero one_ne_zero
      (zpow_ne_zero _ (zpow_ne_zero _ chapterVIDTBase_ne_zero))

theorem hasDerivAt_chapterVIDParameterY :
    HasDerivAt chapterVIDParameterY
      ((chapterVIKeplerExponentialDerivative 0 chapterVIDY)⁻¹ *
        deriv chapterVIDParameterSecondMean chapterVIDZBase) chapterVIDZBase := by
  have houter : HasDerivAt
      (chapterVIKeplerLocalInverse 0 chapterVIDY chapterVIDY_ne_zero
        chapterVID_secondKeplerCritical)
      (chapterVIKeplerExponentialDerivative 0 chapterVIDY)⁻¹
      (chapterVIDParameterSecondMean chapterVIDZBase) := by
    simpa only [chapterVIDParameterSecondMean_base] using
      hasDerivAt_chapterVIKeplerLocalInverse 0 chapterVIDY chapterVIDY_ne_zero
        chapterVID_secondKeplerCritical
  have hcomp := houter.comp chapterVIDZBase
    hasDerivAt_chapterVIDParameterSecondMean
  unfold chapterVIDParameterY
  rw [hasDerivAt_chapterVIDParameterSecondMean.deriv]
  exact hcomp

theorem deriv_chapterVIDParameterY_ne_zero :
    deriv chapterVIDParameterY chapterVIDZBase ≠ 0 := by
  rw [hasDerivAt_chapterVIDParameterY.deriv]
  exact mul_ne_zero (inv_ne_zero chapterVID_secondKeplerCritical)
    deriv_chapterVIDParameterSecondMean_ne_zero

/-- The collision factor that vanishes at D, restricted to the `z`-parameter slice. -/
def chapterVIDParameterCollisionPlus (z : ℂ) : ℂ :=
  chapterVIPoincareCollisionFactorPlus (-1) 3
    chapterVIDEccentricity chapterVIDComplement 0 1 2
    (chapterVIDX, chapterVIDY) chapterVIDX_ne_zero chapterVIDY_ne_zero
    chapterVID_firstKeplerCritical chapterVID_secondKeplerCritical (by norm_num)
    (z, chapterVIDTBase)

theorem chapterVIDParameterCollisionPlus_eq (z : ℂ) :
    chapterVIDParameterCollisionPlus z =
      chapterVIPlanarCollisionFactorPlus chapterVIDEccentricity chapterVIDComplement
        0 1 2 chapterVIDX (chapterVIDParameterY z) := by
  unfold chapterVIDParameterCollisionPlus chapterVIPoincareCollisionFactorPlus
    chapterVIPoincareAnomalyPair chapterVIDParameterY chapterVIDParameterSecondMean
  simp only
  rw [chapterVIDTBase_pow]
  rw [chapterVIKeplerLocalInverse_apply_base]

theorem hasDerivAt_chapterVIDParameterCollisionPlus :
    HasDerivAt chapterVIDParameterCollisionPlus
      (-2 * deriv chapterVIDParameterY chapterVIDZBase) chapterVIDZBase := by
  have hy : HasDerivAt chapterVIDParameterY
      (deriv chapterVIDParameterY chapterVIDZBase) chapterVIDZBase :=
    hasDerivAt_chapterVIDParameterY.congr_deriv
      hasDerivAt_chapterVIDParameterY.deriv.symm
  have hyne : ∀ᶠ z in 𝓝 chapterVIDZBase, chapterVIDParameterY z ≠ 0 :=
    hy.continuousAt.eventually_ne (by
      rw [chapterVIDParameterY_base]
      exact chapterVIDY_ne_zero)
  let constant :=
    chapterVIPlanarKeplerLaurentPlus chapterVIDEccentricity chapterVIDComplement chapterVIDX
  let simple : ℂ → ℂ := (fun _ ↦ constant) - fun z ↦ 2 * chapterVIDParameterY z
  have heq : chapterVIDParameterCollisionPlus =ᶠ[𝓝 chapterVIDZBase] simple := by
    filter_upwards [hyne] with z hz
    rw [chapterVIDParameterCollisionPlus_eq]
    have hsecond : chapterVIPlanarKeplerLaurentPlus 0 1 (chapterVIDParameterY z) =
        chapterVIDParameterY z := by
      unfold chapterVIPlanarKeplerLaurentPlus chapterVIPlanarDistanceFactorPlus
      field_simp [hz]
      ring
    unfold chapterVIPlanarCollisionFactorPlus
    change chapterVIPlanarKeplerLaurentPlus chapterVIDEccentricity chapterVIDComplement
        chapterVIDX - 2 * chapterVIPlanarKeplerLaurentPlus 0 1 (chapterVIDParameterY z) =
      simple z
    rw [hsecond]
    rfl
  have hsimple : HasDerivAt simple
      (-2 * deriv chapterVIDParameterY chapterVIDZBase) chapterVIDZBase := by
    have hderiv := (hasDerivAt_const chapterVIDZBase constant).sub (hy.const_mul 2)
    exact hderiv.congr_deriv (by ring)
  exact hsimple.congr_of_eventuallyEq heq

theorem deriv_chapterVIDParameterCollisionPlus_ne_zero :
    deriv chapterVIDParameterCollisionPlus chapterVIDZBase ≠ 0 := by
  rw [hasDerivAt_chapterVIDParameterCollisionPlus.deriv]
  exact mul_ne_zero (by norm_num) deriv_chapterVIDParameterY_ne_zero

/-- The companion collision factor on the same external-parameter slice. -/
def chapterVIDParameterCollisionMinus (z : ℂ) : ℂ :=
  chapterVIPoincareCollisionFactorMinus (-1) 3
    chapterVIDEccentricity chapterVIDComplement 0 1 2
    (chapterVIDX, chapterVIDY) chapterVIDX_ne_zero chapterVIDY_ne_zero
    chapterVID_firstKeplerCritical chapterVID_secondKeplerCritical (by norm_num)
    (z, chapterVIDTBase)

@[simp]
theorem chapterVIDParameterCollisionPlus_base :
    chapterVIDParameterCollisionPlus chapterVIDZBase = 0 := by
  unfold chapterVIDParameterCollisionPlus chapterVIDZBase
  rw [chapterVIPoincareCollisionFactorPlus_apply_base
    (-1) 3 chapterVIDEccentricity chapterVIDComplement 0 1 2
    (chapterVIDX, chapterVIDY) chapterVIDX_ne_zero chapterVIDY_ne_zero
    chapterVID_firstKeplerCritical chapterVID_secondKeplerCritical (by norm_num)
    chapterVIDTBase chapterVIDTBase_pow]
  exact chapterVID_collisionFactorPlus

theorem chapterVIDParameterCollisionMinus_base_ne_zero :
    chapterVIDParameterCollisionMinus chapterVIDZBase ≠ 0 := by
  unfold chapterVIDParameterCollisionMinus chapterVIDZBase
  rw [chapterVIPoincareCollisionFactorMinus_apply_base
    (-1) 3 chapterVIDEccentricity chapterVIDComplement 0 1 2
    (chapterVIDX, chapterVIDY) chapterVIDX_ne_zero chapterVIDY_ne_zero
    chapterVID_firstKeplerCritical chapterVID_secondKeplerCritical (by norm_num)
    chapterVIDTBase chapterVIDTBase_pow]
  exact chapterVID_collisionFactorMinus_ne_zero

theorem analyticAt_chapterVIDParameterCollisionMinus :
    AnalyticAt ℂ chapterVIDParameterCollisionMinus chapterVIDZBase := by
  have hjoint := analyticAt_chapterVIPoincareCollisionFactorMinus
    (-1) 3 chapterVIDEccentricity chapterVIDComplement 0 1 2
    (chapterVIDX, chapterVIDY) chapterVIDX_ne_zero chapterVIDY_ne_zero
    chapterVID_firstKeplerCritical chapterVID_secondKeplerCritical (by norm_num)
    chapterVIDTBase chapterVIDTBase_ne_zero chapterVIDTBase_pow
  have hline : AnalyticAt ℂ (fun z : ℂ ↦ (z, chapterVIDTBase)) chapterVIDZBase :=
    analyticAt_id.prod analyticAt_const
  unfold chapterVIDParameterCollisionMinus
  simpa only [Function.comp_def] using hjoint.comp_of_eq hline rfl

theorem chapterVIDRadicand_parameterSlice_eq :
    (fun z : ℂ ↦ chapterVIDRadicand (z, chapterVIDTBase)) =
      chapterVIDParameterCollisionPlus * chapterVIDParameterCollisionMinus := by
  rfl

theorem deriv_chapterVIDRadicand_parameterSlice_ne_zero :
    deriv (fun z : ℂ ↦ chapterVIDRadicand (z, chapterVIDTBase))
      chapterVIDZBase ≠ 0 := by
  have hminus :=
    analyticAt_chapterVIDParameterCollisionMinus.hasStrictDerivAt.hasDerivAt
  have hproduct := hasDerivAt_chapterVIDParameterCollisionPlus.mul hminus
  have hderiv :
      deriv (chapterVIDParameterCollisionPlus * chapterVIDParameterCollisionMinus)
          chapterVIDZBase =
        (-2 * deriv chapterVIDParameterY chapterVIDZBase) *
          chapterVIDParameterCollisionMinus chapterVIDZBase := by
    rw [hproduct.deriv]
    rw [chapterVIDParameterCollisionPlus_base]
    ring
  rw [chapterVIDRadicand_parameterSlice_eq, hderiv]
  apply mul_ne_zero
  · rw [← hasDerivAt_chapterVIDParameterCollisionPlus.deriv]
    exact deriv_chapterVIDParameterCollisionPlus_ne_zero
  · exact chapterVIDParameterCollisionMinus_base_ne_zero

theorem chapterVIDParameterDerivative_eq_sliceDeriv :
    chapterVIDParameterDerivative =
      deriv (fun z : ℂ ↦ chapterVIDRadicand (z, chapterVIDTBase)) chapterVIDZBase := by
  have hline : HasDerivAt (fun z : ℂ ↦ (z, chapterVIDTBase)) (1, 0)
      chapterVIDZBase := (hasDerivAt_id chapterVIDZBase).prodMk
        (hasDerivAt_const chapterVIDZBase chapterVIDTBase)
  have hcomp := analyticAt_chapterVIDRadicand.hasStrictFDerivAt.hasFDerivAt
    |>.comp_hasDerivAt chapterVIDZBase hline
  unfold chapterVIDParameterDerivative
  simpa only [Function.comp_def] using hcomp.deriv.symm

/-- The moving critical value is a genuine local coordinate at Poincaré's concrete point D. -/
theorem deriv_chapterVIDCriticalValue_ne_zero :
    deriv chapterVIDCriticalValue chapterVIDZBase ≠ 0 := by
  rw [deriv_chapterVIDCriticalValue_eq_parameterDerivative,
    chapterVIDParameterDerivative_eq_sliceDeriv]
  exact deriv_chapterVIDRadicand_parameterSlice_ne_zero

/-! ## Unconditional critical-value coordinates at D -/

/-- The actual analytic inverse `k ↦ z(k)` at D, now with transversality discharged. -/
def chapterVIDCriticalParameterInverseAtD : ℂ → ℂ :=
  chapterVIDCriticalParameterInverse deriv_chapterVIDCriticalValue_ne_zero

@[simp]
theorem chapterVIDCriticalParameterInverseAtD_zero :
    chapterVIDCriticalParameterInverseAtD 0 = chapterVIDZBase :=
  chapterVIDCriticalParameterInverse_zero deriv_chapterVIDCriticalValue_ne_zero

theorem analyticAt_chapterVIDCriticalParameterInverseAtD :
    AnalyticAt ℂ chapterVIDCriticalParameterInverseAtD 0 :=
  analyticAt_chapterVIDCriticalParameterInverse
    deriv_chapterVIDCriticalValue_ne_zero

/-- The literal source point in the now-unconditional `(k,v)` chart. -/
def chapterVIDCriticalMorseSourcePointAtD (point : ℂ × ℂ) : ℂ × ℂ :=
  chapterVIDCriticalMorseSourcePoint deriv_chapterVIDCriticalValue_ne_zero point

@[simp]
theorem chapterVIDCriticalMorseSourcePointAtD_base :
    chapterVIDCriticalMorseSourcePointAtD (0, 0) =
      (chapterVIDZBase, chapterVIDTBase) :=
  chapterVIDCriticalMorseSourcePoint_base deriv_chapterVIDCriticalValue_ne_zero

/-- Poincaré's literal source radicand is unconditionally `k+v²` near D. -/
theorem eventually_chapterVIDRadicand_criticalMorseSourcePointAtD_eq :
    ∀ᶠ point in 𝓝 ((0 : ℂ), (0 : ℂ)),
      chapterVIDRadicand (chapterVIDCriticalMorseSourcePointAtD point) =
        point.1 + point.2 ^ 2 :=
  eventually_chapterVIDRadicand_criticalMorseSourcePoint_eq
    deriv_chapterVIDCriticalValue_ne_zero

/-- The complete numerator/Jacobian amplitude in the unconditional `(k,v)` chart. -/
def chapterVIDCriticalMorseAmplitudeAtD
    (sourceAmplitude : ℂ × ℂ → ℂ) (point : ℂ × ℂ) : ℂ :=
  chapterVIDCriticalMorseAmplitude deriv_chapterVIDCriticalValue_ne_zero
    sourceAmplitude point

theorem analyticAt_chapterVIDCriticalMorseAmplitudeAtD
    {sourceAmplitude : ℂ × ℂ → ℂ}
    (hsource : AnalyticAt ℂ sourceAmplitude
      (chapterVIDZBase, chapterVIDTBase)) :
    AnalyticAt ℂ (chapterVIDCriticalMorseAmplitudeAtD sourceAmplitude) (0, 0) :=
  analyticAt_chapterVIDCriticalMorseAmplitude
    deriv_chapterVIDCriticalValue_ne_zero hsource

end PoincareChapterVI
