/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import Mathlib.Analysis.Calculus.Deriv.Inv
import PoincareChapterVI.ChapterVIDCandidate

/-!
# The differential identity at Poincaré's point D

On the collision branch (3), after the tangent-half-angle substitution, the first collision
factor is

`H(x,y) = (x-τ)² / ((1+τ²)x) - βy`.

Along a fixed-`z` fiber with `a=-1`, `c=3`, the anomaly coordinates satisfy

`ẋ = 3(1+τ²)x² / (t(x-τ)(1-τx))`,  `ẏ = y/t`.

The key exact identity is

`Ḣ = P₇(x)/(t(1+τ²)x(1-τx)) + H/t`.

Thus equation (7) and equation (3) give `Ḣ=0`. Differentiating once more shows that a
simple equation-(7) root gives `Ḧ≠0`, once the actual inverse-coordinate fiber is proved to
satisfy these differential equations on a neighborhood.
-/

noncomputable section

namespace PoincareChapterVI

/-- The half-angle form of the first collision factor, specialized to a circular second orbit. -/
def chapterVIHalfAngleCollisionPlus (τ β x y : ℂ) : ℂ :=
  (x - τ) ^ 2 / ((1 + τ ^ 2) * x) - β * y

/-- The first collision factor agrees with its half-angle form. -/
theorem chapterVIPlanarCollisionFactorPlus_eq_halfAngle
    (τ eccentricity complement β x y : ℂ)
    (hsine : (1 + τ ^ 2) * eccentricity = 2 * τ)
    (hcosine : (1 + τ ^ 2) * complement = 1 - τ ^ 2)
    (hx : x ≠ 0) (hy : y ≠ 0) (hB : 1 + τ ^ 2 ≠ 0) :
    chapterVIPlanarCollisionFactorPlus eccentricity complement 0 1 β x y =
      chapterVIHalfAngleCollisionPlus τ β x y := by
  have hfirst := chapterVI_planarDistanceFactorPlus_halfAngle
    τ eccentricity complement x hsine hcosine
  have hLfirst : chapterVIPlanarKeplerLaurentPlus eccentricity complement x =
      (x - τ) ^ 2 / ((1 + τ ^ 2) * x) := by
    unfold chapterVIPlanarKeplerLaurentPlus
    field_simp [hx, hB]
    simpa only [mul_comm] using hfirst
  have hLsecond : chapterVIPlanarKeplerLaurentPlus 0 1 y = y := by
    unfold chapterVIPlanarKeplerLaurentPlus chapterVIPlanarDistanceFactorPlus
    field_simp [hy]
    ring
  unfold chapterVIPlanarCollisionFactorPlus chapterVIHalfAngleCollisionPlus
  rw [hLfirst, hLsecond]

/-- Exact differential-ideal identity behind Poincaré's equation (7). -/
theorem hasDerivAt_chapterVIHalfAngleCollisionPlus_of_fiber
    (τ β : ℂ) {x y : ℂ → ℂ} {t : ℂ}
    (ht : t ≠ 0) (hx0 : x t ≠ 0) (hxtau : x t - τ ≠ 0)
    (hxcritical : 1 - τ * x t ≠ 0)
    (hB : 1 + τ ^ 2 ≠ 0)
    (hx : HasDerivAt x
      (3 * (1 + τ ^ 2) * (x t) ^ 2 /
        (t * (x t - τ) * (1 - τ * x t))) t)
    (hy : HasDerivAt y (y t / t) t) :
    HasDerivAt (fun w ↦ chapterVIHalfAngleCollisionPlus τ β (x w) (y w))
      (chapterVISecondKindPolynomialSeven (-1) 3 τ (x t) /
          (t * (1 + τ ^ 2) * x t * (1 - τ * x t)) +
        chapterVIHalfAngleCollisionPlus τ β (x t) (y t) / t) t := by
  have hden : HasDerivAt (fun w ↦ (1 + τ ^ 2) * x w)
      ((1 + τ ^ 2) *
        (3 * (1 + τ ^ 2) * (x t) ^ 2 /
          (t * (x t - τ) * (1 - τ * x t)))) t :=
    hx.const_mul (1 + τ ^ 2)
  have hnum := (hx.sub_const τ).pow 2
  have hquot := hnum.div hden (mul_ne_zero hB hx0)
  have hcollision := hquot.sub (hy.const_mul β)
  have hxcritical' : 1 - x t * τ ≠ 0 := by simpa only [mul_comm] using hxcritical
  convert hcollision using 1
  · rfl
  · rfl
  · funext w
    simp only [Pi.sub_apply]
    rfl
  · unfold chapterVISecondKindPolynomialSeven chapterVIHalfAngleCollisionPlus
    simp only [Pi.pow_apply]
    field_simp [ht, hx0, hxtau, hxcritical, hxcritical', hB]
    ring

/-- At a simultaneous root of equations (3) and (7), the first fiber derivative vanishes. -/
theorem deriv_chapterVIHalfAngleCollisionPlus_eq_zero_of_fiber
    (τ β : ℂ) {x y : ℂ → ℂ} {t : ℂ}
    (ht : t ≠ 0) (hx0 : x t ≠ 0) (hxtau : x t - τ ≠ 0)
    (hxcritical : 1 - τ * x t ≠ 0) (hB : 1 + τ ^ 2 ≠ 0)
    (hx : HasDerivAt x
      (3 * (1 + τ ^ 2) * (x t) ^ 2 /
        (t * (x t - τ) * (1 - τ * x t))) t)
    (hy : HasDerivAt y (y t / t) t)
    (hcollision : chapterVIHalfAngleCollisionPlus τ β (x t) (y t) = 0)
    (hseven : chapterVISecondKindPolynomialSeven (-1) 3 τ (x t) = 0) :
    deriv (fun w ↦ chapterVIHalfAngleCollisionPlus τ β (x w) (y w)) t = 0 := by
  rw [(hasDerivAt_chapterVIHalfAngleCollisionPlus_of_fiber τ β ht hx0 hxtau
    hxcritical hB hx hy).deriv, hcollision, hseven]
  simp

/-! ## The actual inverse-coordinate fiber at the certified D point -/

/-- Poincaré's local `(z,t) ↦ (x,y)` inverse, restricted to the fixed `z` through D. -/
def chapterVIDFiberAnomalies (t : ℂ) : ℂ × ℂ :=
  chapterVIPoincareAnomalyPair (-1) 3 chapterVIDEccentricity 0
    (chapterVIDX, chapterVIDY) chapterVIDX_ne_zero chapterVIDY_ne_zero
    chapterVID_firstKeplerCritical chapterVID_secondKeplerCritical (by norm_num)
    ((chapterVIContourBase (-1) 3 chapterVIDEccentricity 0
      (chapterVIDX, chapterVIDY)).1, t)

def chapterVIDFiberX (t : ℂ) : ℂ := (chapterVIDFiberAnomalies t).1

def chapterVIDFiberY (t : ℂ) : ℂ := (chapterVIDFiberAnomalies t).2

@[simp] theorem chapterVIDFiberAnomalies_apply_base
    {t : ℂ} (htPower : t ^ (3 : ℤ) =
      chapterVIKeplerExponential chapterVIDEccentricity chapterVIDX) :
    chapterVIDFiberAnomalies t = (chapterVIDX, chapterVIDY) := by
  exact chapterVIPoincareAnomalyPair_apply_base (-1) 3 chapterVIDEccentricity 0
    (chapterVIDX, chapterVIDY) chapterVIDX_ne_zero chapterVIDY_ne_zero
    chapterVID_firstKeplerCritical chapterVID_secondKeplerCritical (by norm_num) t htPower

@[simp] theorem chapterVIDFiberX_apply_base
    {t : ℂ} (htPower : t ^ (3 : ℤ) =
      chapterVIKeplerExponential chapterVIDEccentricity chapterVIDX) :
    chapterVIDFiberX t = chapterVIDX := by
  rw [chapterVIDFiberX, chapterVIDFiberAnomalies_apply_base htPower]

@[simp] theorem chapterVIDFiberY_apply_base
    {t : ℂ} (htPower : t ^ (3 : ℤ) =
      chapterVIKeplerExponential chapterVIDEccentricity chapterVIDX) :
    chapterVIDFiberY t = chapterVIDY := by
  rw [chapterVIDFiberY, chapterVIDFiberAnomalies_apply_base htPower]

/-- The first actual anomaly coordinate satisfies Poincaré's fixed-fiber ODE at D. -/
theorem hasDerivAt_chapterVIDFiberX
    {t : ℂ} (ht : t ≠ 0)
    (htPower : t ^ (3 : ℤ) =
      chapterVIKeplerExponential chapterVIDEccentricity chapterVIDX) :
    HasDerivAt chapterVIDFiberX
      (3 * (1 + (1 / 100 : ℂ) ^ 2) * chapterVIDX ^ 2 /
        (t * (chapterVIDX - 1 / 100) *
          (1 - (1 / 100 : ℂ) * chapterVIDX))) t := by
  have hpow : HasDerivAt (fun w : ℂ ↦ w ^ 3) (3 * t ^ 2) t := by
    simpa only [Nat.cast_ofNat, Nat.reduceSub] using hasDerivAt_pow 3 t
  have hinverse := hasDerivAt_chapterVIKeplerLocalInverse
    chapterVIDEccentricity chapterVIDX chapterVIDX_ne_zero chapterVID_firstKeplerCritical
  have htPowerNat : t ^ 3 =
      chapterVIKeplerExponential chapterVIDEccentricity chapterVIDX := by
    simpa only [zpow_ofNat] using htPower
  have hinverse' : HasDerivAt
      (chapterVIKeplerLocalInverse chapterVIDEccentricity chapterVIDX
        chapterVIDX_ne_zero chapterVID_firstKeplerCritical)
      (chapterVIKeplerExponentialDerivative chapterVIDEccentricity chapterVIDX)⁻¹
      (t ^ 3) := by
    simpa only [htPowerNat] using hinverse
  have hcomp := hinverse'.comp t hpow
  have hcoeff :
      (chapterVIKeplerExponentialDerivative chapterVIDEccentricity chapterVIDX)⁻¹ *
          (3 * t ^ 2) =
        3 * (1 + (1 / 100 : ℂ) ^ 2) * chapterVIDX ^ 2 /
          (t * (chapterVIDX - 1 / 100) *
            (1 - (1 / 100 : ℂ) * chapterVIDX)) := by
    unfold chapterVIKeplerExponentialDerivative
    have hexp : Complex.exp
        (chapterVIDEccentricity / 2 * (chapterVIDX⁻¹ - chapterVIDX)) ≠ 0 :=
      Complex.exp_ne_zero _
    field_simp [ht, chapterVIDX_ne_zero, chapterVIDX_sub_tau_ne_zero,
      chapterVID_one_sub_tau_mul_x_ne_zero, hexp]
    rw [htPowerNat]
    unfold chapterVIKeplerExponential
    norm_num [chapterVIDEccentricity]
    have hexparg :
        200 / 10001 * (1 - chapterVIDX ^ 2) / (2 * chapterVIDX) =
          100 / 10001 * (chapterVIDX⁻¹ - chapterVIDX) := by
      field_simp [chapterVIDX_ne_zero]
      ring
    rw [hexparg]
    have hA : 1 - chapterVIDEccentricity / 2 *
        (chapterVIDX + chapterVIDX⁻¹) ≠ 0 :=
      (chapterVIKeplerExponentialDerivative_ne_zero_iff chapterVIDEccentricity
        chapterVIDX_ne_zero).mp chapterVID_firstKeplerCritical
    have hd : -100 + chapterVIDX * 10001 - chapterVIDX ^ 2 * 100 ≠ 0 := by
      intro hd0
      apply hA
      field_simp [chapterVIDX_ne_zero]
      norm_num [chapterVIDEccentricity]
      linear_combination (2 / 10001) * hd0
    field_simp [chapterVIDX_ne_zero, chapterVIDX_sub_tau_ne_zero,
      chapterVID_one_sub_tau_mul_x_ne_zero, hexp, hA, hd]
    rw [show 2 * chapterVIDX * 10001 - 200 * (chapterVIDX ^ 2 + 1) =
      2 * (-100 + chapterVIDX * 10001 - chapterVIDX ^ 2 * 100) by ring]
    rw [show (chapterVIDX * 100 - 1) * (100 - chapterVIDX) =
      -100 + chapterVIDX * 10001 - chapterVIDX ^ 2 * 100 by ring]
    field_simp [hd]
  rw [hcoeff] at hcomp
  change HasDerivAt
    (fun w : ℂ ↦ chapterVIKeplerLocalInverse chapterVIDEccentricity chapterVIDX
      chapterVIDX_ne_zero chapterVID_firstKeplerCritical (w ^ 3)) _ t
  convert hcomp using 1 <;> rfl

/-- The second actual anomaly coordinate satisfies `ẏ=y/t` on the same fixed fiber. -/
theorem hasDerivAt_chapterVIDFiberY
    {t : ℂ} (ht : t ≠ 0)
    (htPower : t ^ (3 : ℤ) =
      chapterVIKeplerExponential chapterVIDEccentricity chapterVIDX) :
    HasDerivAt chapterVIDFiberY (chapterVIDY / t) t := by
  let firstMeanBase := chapterVIKeplerExponential chapterVIDEccentricity chapterVIDX
  let secondMeanBase := chapterVIKeplerExponential 0 chapterVIDY
  let zBase := (chapterVIContourBase (-1) 3 chapterVIDEccentricity 0
    (chapterVIDX, chapterVIDY)).1
  have hfirstMeanBase : firstMeanBase ≠ 0 :=
    chapterVIKeplerExponential_ne_zero _ chapterVIDX_ne_zero
  have hsecondMeanBase : secondMeanBase ≠ 0 :=
    chapterVIKeplerExponential_ne_zero _ chapterVIDY_ne_zero
  have hsecondMeanBase_eq : secondMeanBase = chapterVIDY := by
    simp [secondMeanBase, chapterVIKeplerExponential]
  have hpow : HasDerivAt (fun w : ℂ ↦ w ^ 3) (3 * t ^ 2) t := by
    simpa only [Nat.cast_ofNat, Nat.reduceSub] using hasDerivAt_pow 3 t
  have hratioValue : zBase / (t ^ 3)⁻¹ = secondMeanBase ^ (3 : ℤ) := by
    dsimp only [zBase, chapterVIContourBase, chapterVIMeanToContourMap]
    change (firstMeanBase ^ (-1 : ℤ) * secondMeanBase ^ (3 : ℤ)) /
      (t ^ 3)⁻¹ = secondMeanBase ^ (3 : ℤ)
    rw [show t ^ 3 = firstMeanBase by simpa only [firstMeanBase, zpow_ofNat] using htPower]
    field_simp [hfirstMeanBase]
  have hratio : HasDerivAt (fun w : ℂ ↦ zBase / (w ^ 3)⁻¹)
      (3 * secondMeanBase ^ (3 : ℤ) / t) t := by
    have hsimple := hpow.const_mul zBase
    have hsame : (fun w : ℂ ↦ zBase / (w ^ 3)⁻¹) =ᶠ[nhds t]
        (fun w : ℂ ↦ zBase * w ^ 3) := by
      filter_upwards with w
      simp [div_eq_mul_inv]
    have hratioSame := hsimple.congr_of_eventuallyEq hsame
    apply hratioSame.congr_deriv
    rw [← hratioValue]
    field_simp [ht]
  have hpowerInverse := hasDerivAt_chapterVIPowerLocalInverse
    (3 : ℤ) secondMeanBase hsecondMeanBase (by norm_num)
  have hpowerInverse' : HasDerivAt
      (chapterVIPowerLocalInverse (3 : ℤ) secondMeanBase hsecondMeanBase (by norm_num))
      ((((3 : ℤ) : ℂ) * secondMeanBase ^ ((3 : ℤ) - 1))⁻¹)
      (zBase / (t ^ 3)⁻¹) := by
    rw [hratioValue]
    exact hpowerInverse
  have hsecondMeanRaw := hpowerInverse'.comp t hratio
  have hsecondMean : HasDerivAt
      (fun w : ℂ ↦ chapterVIPowerLocalInverse (3 : ℤ) secondMeanBase
        hsecondMeanBase (by norm_num) (zBase / (w ^ 3)⁻¹))
      (secondMeanBase / t) t := by
    have hsecondMeanSame : HasDerivAt
        (fun w : ℂ ↦ chapterVIPowerLocalInverse (3 : ℤ) secondMeanBase
          hsecondMeanBase (by norm_num) (zBase / (w ^ 3)⁻¹))
        (((((3 : ℤ) : ℂ) * secondMeanBase ^ ((3 : ℤ) - 1))⁻¹) *
          (3 * secondMeanBase ^ (3 : ℤ) / t)) t := by
      simpa only [Function.comp_def] using hsecondMeanRaw
    apply hsecondMeanSame.congr_deriv
    simp only [Int.cast_ofNat, zpow_ofNat]
    field_simp [ht, hsecondMeanBase]
    ring_nf
    rfl
  have hkeplerInverse := hasDerivAt_chapterVIKeplerLocalInverse
    0 chapterVIDY chapterVIDY_ne_zero chapterVID_secondKeplerCritical
  have hsecondMeanValue :
      chapterVIPowerLocalInverse (3 : ℤ) secondMeanBase hsecondMeanBase (by norm_num)
        (zBase / (t ^ 3)⁻¹) = chapterVIDY := by
    rw [hratioValue, chapterVIPowerLocalInverse_apply_base]
    exact hsecondMeanBase_eq
  have hkeplerInverse' : HasDerivAt
      (chapterVIKeplerLocalInverse 0 chapterVIDY chapterVIDY_ne_zero
        chapterVID_secondKeplerCritical)
      (chapterVIKeplerExponentialDerivative 0 chapterVIDY)⁻¹
      (chapterVIPowerLocalInverse (3 : ℤ) secondMeanBase hsecondMeanBase (by norm_num)
        (zBase / (t ^ 3)⁻¹)) := by
    have hkeplerInverseAtY : HasDerivAt
        (chapterVIKeplerLocalInverse 0 chapterVIDY chapterVIDY_ne_zero
          chapterVID_secondKeplerCritical)
        (chapterVIKeplerExponentialDerivative 0 chapterVIDY)⁻¹ chapterVIDY := by
      simpa [chapterVIKeplerExponential] using hkeplerInverse
    simpa only [hsecondMeanValue] using hkeplerInverseAtY
  have hfinal := hkeplerInverse'.comp t hsecondMean
  have hderivativeOne :
      (chapterVIKeplerExponentialDerivative 0 chapterVIDY)⁻¹ = 1 := by
    unfold chapterVIKeplerExponentialDerivative
    norm_num
  rw [hderivativeOne, one_mul] at hfinal
  unfold chapterVIDFiberY chapterVIDFiberAnomalies chapterVIPoincareAnomalyPair
  simp only [secondMeanBase, zBase, Function.comp_def,
    chapterVIKeplerExponential, zero_div, zero_mul, Complex.exp_zero,
    mul_one, zpow_neg_one] at hfinal ⊢
  convert hfinal using 1 <;> rfl

/-! ## The certified first-order tangency at D -/

/-- The real equation-(7) certificate, transported to the complex anomaly coordinate. -/
theorem chapterVIDX_secondKindSeven :
    chapterVISecondKindPolynomialSeven (-1) 3 (1 / 100 : ℂ) chapterVIDX = 0 := by
  unfold chapterVIDX
  exact_mod_cast chapterVIDRoot_secondKindSeven

/-- Equation (3) says exactly that the half-angle collision factor vanishes at D. -/
theorem chapterVID_halfAngleCollisionPlus :
    chapterVIHalfAngleCollisionPlus (1 / 100 : ℂ) 2 chapterVIDX chapterVIDY = 0 := by
  have hfactor := chapterVIPlanarCollisionFactorPlus_eq_halfAngle
    (1 / 100 : ℂ) chapterVIDEccentricity chapterVIDComplement 2
    chapterVIDX chapterVIDY chapterVID_halfAngle_sine chapterVID_halfAngle_cosine
    chapterVIDX_ne_zero chapterVIDY_ne_zero (by norm_num)
  rw [chapterVID_collisionFactorPlus] at hfactor
  exact hfactor.symm

/-- Along the actual fixed-`z` fiber, Poincaré's collision factor has zero first derivative
at the certified point D. -/
theorem deriv_chapterVIDHalfAngleCollisionPlus_eq_zero
    {t : ℂ} (ht : t ≠ 0)
    (htPower : t ^ (3 : ℤ) =
      chapterVIKeplerExponential chapterVIDEccentricity chapterVIDX) :
    deriv (fun w ↦ chapterVIHalfAngleCollisionPlus (1 / 100 : ℂ) 2
      (chapterVIDFiberX w) (chapterVIDFiberY w)) t = 0 := by
  apply deriv_chapterVIHalfAngleCollisionPlus_eq_zero_of_fiber
    (1 / 100 : ℂ) 2 ht
  · simpa only [chapterVIDFiberX_apply_base htPower] using chapterVIDX_ne_zero
  · simpa only [chapterVIDFiberX_apply_base htPower] using chapterVIDX_sub_tau_ne_zero
  · simpa only [chapterVIDFiberX_apply_base htPower] using
      chapterVID_one_sub_tau_mul_x_ne_zero
  · norm_num
  · simpa only [chapterVIDFiberX_apply_base htPower] using
      hasDerivAt_chapterVIDFiberX ht htPower
  · simpa only [chapterVIDFiberY_apply_base htPower] using
      hasDerivAt_chapterVIDFiberY ht htPower
  · simpa only [chapterVIDFiberX_apply_base htPower,
      chapterVIDFiberY_apply_base htPower] using chapterVID_halfAngleCollisionPlus
  · simpa only [chapterVIDFiberX_apply_base htPower] using chapterVIDX_secondKindSeven

/-- The same first-order tangency, stated for the literal source collision factor rather than
its half-angle normal form. -/
theorem deriv_chapterVIDPlanarCollisionFactorPlus_eq_zero
    {t : ℂ} (ht : t ≠ 0)
    (htPower : t ^ (3 : ℤ) =
      chapterVIKeplerExponential chapterVIDEccentricity chapterVIDX) :
    deriv (fun w ↦ chapterVIPlanarCollisionFactorPlus
      chapterVIDEccentricity chapterVIDComplement 0 1 2
      (chapterVIDFiberX w) (chapterVIDFiberY w)) t = 0 := by
  have hx := hasDerivAt_chapterVIDFiberX ht htPower
  have hy := hasDerivAt_chapterVIDFiberY ht htPower
  have hx_ne : chapterVIDFiberX t ≠ 0 := by
    simpa only [chapterVIDFiberX_apply_base htPower] using chapterVIDX_ne_zero
  have hy_ne : chapterVIDFiberY t ≠ 0 := by
    simpa only [chapterVIDFiberY_apply_base htPower] using chapterVIDY_ne_zero
  have hx_eventually := hx.continuousAt.eventually_ne hx_ne
  have hy_eventually := hy.continuousAt.eventually_ne hy_ne
  have heq : (fun w ↦ chapterVIPlanarCollisionFactorPlus
      chapterVIDEccentricity chapterVIDComplement 0 1 2
      (chapterVIDFiberX w) (chapterVIDFiberY w)) =ᶠ[nhds t]
      (fun w ↦ chapterVIHalfAngleCollisionPlus (1 / 100 : ℂ) 2
        (chapterVIDFiberX w) (chapterVIDFiberY w)) := by
    filter_upwards [hx_eventually, hy_eventually] with w hxw hyw
    exact chapterVIPlanarCollisionFactorPlus_eq_halfAngle
      (1 / 100 : ℂ) chapterVIDEccentricity chapterVIDComplement 2
      (chapterVIDFiberX w) (chapterVIDFiberY w)
      chapterVID_halfAngle_sine chapterVID_halfAngle_cosine hxw hyw (by norm_num)
  rw [heq.deriv_eq]
  exact deriv_chapterVIDHalfAngleCollisionPlus_eq_zero ht htPower

/-- The first derivative certificate in Poincaré's literal `(z,t)` coordinates. -/
theorem deriv_chapterVIDPoincareCollisionFactorPlus_eq_zero
    {t : ℂ} (ht : t ≠ 0)
    (htPower : t ^ (3 : ℤ) =
      chapterVIKeplerExponential chapterVIDEccentricity chapterVIDX) :
    deriv (fun w ↦ chapterVIPoincareCollisionFactorPlus
      (-1) 3 chapterVIDEccentricity chapterVIDComplement 0 1 2
      (chapterVIDX, chapterVIDY) chapterVIDX_ne_zero chapterVIDY_ne_zero
      chapterVID_firstKeplerCritical chapterVID_secondKeplerCritical (by norm_num)
      ((chapterVIContourBase (-1) 3 chapterVIDEccentricity 0
        (chapterVIDX, chapterVIDY)).1, w)) t = 0 := by
  change deriv (fun w ↦ chapterVIPlanarCollisionFactorPlus
    chapterVIDEccentricity chapterVIDComplement 0 1 2
    (chapterVIDFiberX w) (chapterVIDFiberY w)) t = 0
  exact deriv_chapterVIDPlanarCollisionFactorPlus_eq_zero ht htPower

end PoincareChapterVI
