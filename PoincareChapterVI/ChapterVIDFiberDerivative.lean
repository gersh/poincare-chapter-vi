/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Complex.Polynomial.Basic
import PoincareChapterVI.ChapterVIDCandidate
import PoincareChapterVI.ChapterVIDoubleZero

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

/-- A selected lift `t_D` satisfying Poincaré's relation `t_D³ = exp(i l_D)`. -/
theorem exists_chapterVIDTBase : ∃ t : ℂ,
    t ^ 3 = chapterVIKeplerExponential chapterVIDEccentricity chapterVIDX :=
  IsAlgClosed.exists_pow_nat_eq
    (chapterVIKeplerExponential chapterVIDEccentricity chapterVIDX) (by norm_num)

noncomputable def chapterVIDTBase : ℂ :=
  Classical.choose exists_chapterVIDTBase

@[simp] theorem chapterVIDTBase_pow : chapterVIDTBase ^ (3 : ℤ) =
    chapterVIKeplerExponential chapterVIDEccentricity chapterVIDX := by
  unfold chapterVIDTBase
  simpa only [zpow_ofNat] using Classical.choose_spec
    exists_chapterVIDTBase

theorem chapterVIDTBase_ne_zero : chapterVIDTBase ≠ 0 := by
  intro hzero
  have hmean := chapterVIKeplerExponential_ne_zero
    chapterVIDEccentricity chapterVIDX_ne_zero
  apply hmean
  rw [← chapterVIDTBase_pow, hzero]
  norm_num

/-- The second mean-anomaly input along the fixed-`z` fiber, simplified using `a=-1`, `c=3`. -/
def chapterVIDSecondMeanInput (t : ℂ) : ℂ :=
  (chapterVIContourBase (-1) 3 chapterVIDEccentricity 0
    (chapterVIDX, chapterVIDY)).1 * t ^ 3

/-- The selected cubic-root branch producing the second mean anomaly along the fiber. -/
def chapterVIDSecondMean (t : ℂ) : ℂ :=
  let base := chapterVIKeplerExponential 0 chapterVIDY
  let hbase : base ≠ 0 := chapterVIKeplerExponential_ne_zero 0 chapterVIDY_ne_zero
  chapterVIPowerLocalInverse 3 base hbase (by norm_num) (chapterVIDSecondMeanInput t)

theorem chapterVIDFiberY_eq_keplerInverse_secondMean (t : ℂ) :
    chapterVIDFiberY t =
      chapterVIKeplerLocalInverse 0 chapterVIDY chapterVIDY_ne_zero
        chapterVID_secondKeplerCritical (chapterVIDSecondMean t) := by
  unfold chapterVIDFiberY chapterVIDFiberAnomalies chapterVIPoincareAnomalyPair
    chapterVIDSecondMean chapterVIDSecondMeanInput
  simp only [zpow_ofNat, zpow_neg_one, div_eq_mul_inv, inv_inv]

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

/-- The complete fixed-`z` inverse-coordinate fiber is analytic at the selected lift of D. -/
theorem analyticAt_chapterVIDFiberAnomalies
    {t : ℂ} (ht : t ≠ 0)
    (htPower : t ^ (3 : ℤ) =
      chapterVIKeplerExponential chapterVIDEccentricity chapterVIDX) :
    AnalyticAt ℂ chapterVIDFiberAnomalies t := by
  have hpair := analyticAt_chapterVIPoincareAnomalyPair
    (-1) 3 chapterVIDEccentricity 0 (chapterVIDX, chapterVIDY)
    chapterVIDX_ne_zero chapterVIDY_ne_zero chapterVID_firstKeplerCritical
    chapterVID_secondKeplerCritical (by norm_num) t ht htPower
  have hline : AnalyticAt ℂ (fun w : ℂ ↦
      ((chapterVIContourBase (-1) 3 chapterVIDEccentricity 0
        (chapterVIDX, chapterVIDY)).1, w)) t :=
    analyticAt_const.prod analyticAt_id
  have hcomp := hpair.comp hline
  change AnalyticAt ℂ (fun w ↦ chapterVIPoincareAnomalyPair
    (-1) 3 chapterVIDEccentricity 0 (chapterVIDX, chapterVIDY)
    chapterVIDX_ne_zero chapterVIDY_ne_zero chapterVID_firstKeplerCritical
    chapterVID_secondKeplerCritical (by norm_num)
    ((chapterVIContourBase (-1) 3 chapterVIDEccentricity 0
      (chapterVIDX, chapterVIDY)).1, w)) t
  convert hcomp using 1
  all_goals rfl

theorem analyticAt_chapterVIDFiberX
    {t : ℂ} (ht : t ≠ 0)
    (htPower : t ^ (3 : ℤ) =
      chapterVIKeplerExponential chapterVIDEccentricity chapterVIDX) :
    AnalyticAt ℂ chapterVIDFiberX t := by
  change AnalyticAt ℂ (fun w ↦ (chapterVIDFiberAnomalies w).1) t
  simpa only [Function.comp_def] using
    analyticAt_fst.comp (analyticAt_chapterVIDFiberAnomalies ht htPower)

theorem analyticAt_chapterVIDFiberY
    {t : ℂ} (ht : t ≠ 0)
    (htPower : t ^ (3 : ℤ) =
      chapterVIKeplerExponential chapterVIDEccentricity chapterVIDX) :
    AnalyticAt ℂ chapterVIDFiberY t := by
  change AnalyticAt ℂ (fun w ↦ (chapterVIDFiberAnomalies w).2) t
  simpa only [Function.comp_def] using
    analyticAt_snd.comp (analyticAt_chapterVIDFiberAnomalies ht htPower)

/-- The selected first Kepler inverse really is a right inverse throughout a neighborhood of
the lifted point D, not merely at its center. -/
theorem eventually_chapterVIKeplerExponential_chapterVIDFiberX
    {t : ℂ} (htPower : t ^ (3 : ℤ) =
      chapterVIKeplerExponential chapterVIDEccentricity chapterVIDX) :
    (fun w ↦ chapterVIKeplerExponential chapterVIDEccentricity
      (chapterVIDFiberX w)) =ᶠ[nhds t] fun w ↦ w ^ 3 := by
  have htPowerNat : t ^ 3 =
      chapterVIKeplerExponential chapterVIDEccentricity chapterVIDX := by
    simpa only [zpow_ofNat] using htPower
  have htend : Filter.Tendsto (fun w : ℂ ↦ w ^ 3) (nhds t)
      (nhds (chapterVIKeplerExponential chapterVIDEccentricity chapterVIDX)) := by
    rw [← htPowerNat]
    exact (by fun_prop : ContinuousAt (fun w : ℂ ↦ w ^ 3) t)
  have hright := (eventually_chapterVIKeplerExponential_localInverse
    chapterVIDEccentricity chapterVIDX chapterVIDX_ne_zero
    chapterVID_firstKeplerCritical).comp_tendsto htend
  change (fun w ↦ chapterVIKeplerExponential chapterVIDEccentricity
    (chapterVIKeplerLocalInverse chapterVIDEccentricity chapterVIDX
      chapterVIDX_ne_zero chapterVID_firstKeplerCritical (w ^ 3))) =ᶠ[nhds t]
      fun w ↦ w ^ 3
  change ((fun mean ↦ chapterVIKeplerExponential chapterVIDEccentricity
    (chapterVIKeplerLocalInverse chapterVIDEccentricity chapterVIDX
      chapterVIDX_ne_zero chapterVID_firstKeplerCritical mean)) ∘
      fun w : ℂ ↦ w ^ 3) =ᶠ[nhds t] (fun mean : ℂ ↦ mean) ∘ fun w : ℂ ↦ w ^ 3
  exact hright

@[simp] theorem chapterVIDSecondMeanInput_apply_base
    {t : ℂ} (htPower : t ^ (3 : ℤ) =
      chapterVIKeplerExponential chapterVIDEccentricity chapterVIDX) :
    chapterVIDSecondMeanInput t =
      chapterVIKeplerExponential 0 chapterVIDY ^ (3 : ℤ) := by
  have hfirst := chapterVIKeplerExponential_ne_zero
    chapterVIDEccentricity chapterVIDX_ne_zero
  unfold chapterVIDSecondMeanInput chapterVIContourBase chapterVIMeanToContourMap
  dsimp only
  rw [show t ^ 3 = chapterVIKeplerExponential chapterVIDEccentricity chapterVIDX by
    simpa only [zpow_ofNat] using htPower]
  simp only [zpow_neg_one, zpow_ofNat]
  field_simp [hfirst]

/-- The second selected cubic-root branch is a genuine right inverse near D. -/
theorem eventually_chapterVIDSecondMean_cubed
    {t : ℂ} (htPower : t ^ (3 : ℤ) =
      chapterVIKeplerExponential chapterVIDEccentricity chapterVIDX) :
    (fun w ↦ chapterVIDSecondMean w ^ (3 : ℤ)) =ᶠ[nhds t]
      chapterVIDSecondMeanInput := by
  have hbase : chapterVIKeplerExponential 0 chapterVIDY ≠ 0 :=
    chapterVIKeplerExponential_ne_zero 0 chapterVIDY_ne_zero
  have hinput : AnalyticAt ℂ chapterVIDSecondMeanInput t := by
    unfold chapterVIDSecondMeanInput
    fun_prop
  have htend : Filter.Tendsto chapterVIDSecondMeanInput (nhds t)
      (nhds ((chapterVIKeplerExponential 0 chapterVIDY) ^ (3 : ℤ))) := by
    rw [← chapterVIDSecondMeanInput_apply_base htPower]
    exact hinput.continuousAt
  have hright := (eventually_zpow_chapterVIPowerLocalInverse
    (3 : ℤ) (chapterVIKeplerExponential 0 chapterVIDY) hbase (by norm_num)).comp_tendsto htend
  change ((fun mean : ℂ ↦ chapterVIPowerLocalInverse 3
    (chapterVIKeplerExponential 0 chapterVIDY) hbase (by norm_num) mean ^ (3 : ℤ)) ∘
      chapterVIDSecondMeanInput) =ᶠ[nhds t]
    (fun mean : ℂ ↦ mean) ∘ chapterVIDSecondMeanInput
  convert hright using 1

/-- The circular second Kepler inverse is locally the identity on the selected mean branch. -/
theorem eventually_chapterVIDFiberY_eq_secondMean
    {t : ℂ} (htPower : t ^ (3 : ℤ) =
      chapterVIKeplerExponential chapterVIDEccentricity chapterVIDX) :
    chapterVIDFiberY =ᶠ[nhds t] chapterVIDSecondMean := by
  have hbase : chapterVIKeplerExponential 0 chapterVIDY ≠ 0 :=
    chapterVIKeplerExponential_ne_zero 0 chapterVIDY_ne_zero
  have hinput : AnalyticAt ℂ chapterVIDSecondMeanInput t := by
    unfold chapterVIDSecondMeanInput
    fun_prop
  have hpower : AnalyticAt ℂ chapterVIDSecondMean t := by
    unfold chapterVIDSecondMean
    apply (analyticAt_chapterVIPowerLocalInverse 3
      (chapterVIKeplerExponential 0 chapterVIDY) hbase (by norm_num)).comp_of_eq hinput
    exact chapterVIDSecondMeanInput_apply_base htPower
  have hpower_base : chapterVIDSecondMean t = chapterVIDY := by
    unfold chapterVIDSecondMean
    have hbase_eq : chapterVIKeplerExponential 0 chapterVIDY = chapterVIDY := by
      simp [chapterVIKeplerExponential]
    rw [chapterVIDSecondMeanInput_apply_base htPower,
      chapterVIPowerLocalInverse_apply_base]
    exact hbase_eq
  have htend : Filter.Tendsto chapterVIDSecondMean (nhds t)
      (nhds (chapterVIKeplerExponential 0 chapterVIDY)) := by
    rw [show chapterVIKeplerExponential 0 chapterVIDY = chapterVIDY by
      simp [chapterVIKeplerExponential], ← hpower_base]
    exact hpower.continuousAt
  have hright := (eventually_chapterVIKeplerExponential_localInverse
    0 chapterVIDY chapterVIDY_ne_zero chapterVID_secondKeplerCritical).comp_tendsto htend
  have hright' :
      (fun w ↦ chapterVIKeplerLocalInverse 0 chapterVIDY chapterVIDY_ne_zero
        chapterVID_secondKeplerCritical (chapterVIDSecondMean w)) =ᶠ[nhds t]
        chapterVIDSecondMean := by
    simpa only [Function.comp_def, chapterVIKeplerExponential, zero_div, zero_mul,
      Complex.exp_zero, mul_one] using hright
  filter_upwards [hright'] with w hw
  rw [chapterVIDFiberY_eq_keplerInverse_secondMean, hw]

/-- Cubing the actual second anomaly coordinate recovers its fixed-`z` input near D. -/
theorem eventually_chapterVIDFiberY_cubed
    {t : ℂ} (htPower : t ^ (3 : ℤ) =
      chapterVIKeplerExponential chapterVIDEccentricity chapterVIDX) :
    (fun w ↦ chapterVIDFiberY w ^ (3 : ℤ)) =ᶠ[nhds t]
      chapterVIDSecondMeanInput := by
  exact (eventually_chapterVIDFiberY_eq_secondMean htPower).fun_comp
    (fun y : ℂ ↦ y ^ (3 : ℤ)) |>.trans
      (eventually_chapterVIDSecondMean_cubed htPower)

/-- The first anomaly ODE holds throughout a neighborhood of D.  This is the analytic
neighborhood statement needed to differentiate the differential-ideal identity a second time. -/
theorem eventually_hasDerivAt_chapterVIDFiberX
    {t : ℂ} (ht : t ≠ 0)
    (htPower : t ^ (3 : ℤ) =
      chapterVIKeplerExponential chapterVIDEccentricity chapterVIDX) :
    ∀ᶠ w in nhds t, HasDerivAt chapterVIDFiberX
      (3 * (1 + (1 / 100 : ℂ) ^ 2) * chapterVIDFiberX w ^ 2 /
        (w * (chapterVIDFiberX w - 1 / 100) *
          (1 - (1 / 100 : ℂ) * chapterVIDFiberX w))) w := by
  have hanalytic := analyticAt_chapterVIDFiberX ht htPower
  have hanalytic_eventually := hanalytic.eventually_analyticAt
  have hright := eventually_chapterVIKeplerExponential_chapterVIDFiberX htPower
  have hderiv_right := hright.deriv
  have hw_eventually : ∀ᶠ w in nhds t, w ≠ 0 :=
    continuousAt_id.eventually_ne ht
  have hx_eventually : ∀ᶠ w in nhds t, chapterVIDFiberX w ≠ 0 :=
    hanalytic.continuousAt.eventually_ne (by
      simpa only [chapterVIDFiberX_apply_base htPower] using chapterVIDX_ne_zero)
  have hxtau_analytic : AnalyticAt ℂ
      (fun w ↦ chapterVIDFiberX w - (1 / 100 : ℂ)) t :=
    hanalytic.sub analyticAt_const
  have hxtau_eventually : ∀ᶠ w in nhds t,
      chapterVIDFiberX w - (1 / 100 : ℂ) ≠ 0 :=
    hxtau_analytic.continuousAt.eventually_ne (by
      simpa only [chapterVIDFiberX_apply_base htPower] using chapterVIDX_sub_tau_ne_zero)
  have hxcritical_analytic : AnalyticAt ℂ
      (fun w ↦ 1 - (1 / 100 : ℂ) * chapterVIDFiberX w) t :=
    analyticAt_const.sub (analyticAt_const.mul hanalytic)
  have hxcritical_eventually : ∀ᶠ w in nhds t,
      1 - (1 / 100 : ℂ) * chapterVIDFiberX w ≠ 0 :=
    hxcritical_analytic.continuousAt.eventually_ne (by
      simpa only [chapterVIDFiberX_apply_base htPower] using
        chapterVID_one_sub_tau_mul_x_ne_zero)
  filter_upwards [hanalytic_eventually, hright, hderiv_right, hw_eventually,
    hx_eventually, hxtau_eventually, hxcritical_eventually] with
    w haw hvalue hderivValue hw hxw hxtauw hxcriticalw
  have hcriticalw :
      chapterVIKeplerExponentialDerivative chapterVIDEccentricity
        (chapterVIDFiberX w) ≠ 0 := by
    rw [chapterVIKeplerExponentialDerivative_ne_zero_iff
      chapterVIDEccentricity hxw]
    intro hzero
    have hfactor :
        (chapterVIDFiberX w - 1 / 100) *
          (1 - (1 / 100 : ℂ) * chapterVIDFiberX w) = 0 := by
      field_simp [hxw] at hzero
      norm_num [chapterVIDEccentricity] at hzero
      field_simp
      ring_nf at hzero ⊢
      linear_combination (10001 / 2) * hzero
    exact (mul_ne_zero hxtauw hxcriticalw) hfactor
  have hxraw := haw.differentiableAt.hasDerivAt
  have hkepler := hasDerivAt_chapterVIKeplerExponential
    chapterVIDEccentricity hxw
  have hcomp := hkepler.comp w hxraw
  have hpow : HasDerivAt (fun u : ℂ ↦ u ^ 3) (3 * w ^ 2) w := by
    simpa only [Nat.cast_ofNat, Nat.reduceSub] using hasDerivAt_pow 3 w
  have hderivEquation :
      chapterVIKeplerExponentialDerivative chapterVIDEccentricity
          (chapterVIDFiberX w) * deriv chapterVIDFiberX w = 3 * w ^ 2 := by
    rw [← hcomp.deriv, ← hpow.deriv]
    exact hderivValue
  apply hxraw.congr_deriv
  have hexp_eq : Complex.exp (chapterVIDEccentricity / 2 *
      ((chapterVIDFiberX w)⁻¹ - chapterVIDFiberX w)) =
      w ^ 3 / chapterVIDFiberX w := by
    apply (eq_div_iff hxw).2
    unfold chapterVIKeplerExponential at hvalue
    simpa only [mul_comm] using hvalue
  have hcritical_eq : 1 - chapterVIDEccentricity / 2 *
      (chapterVIDFiberX w + (chapterVIDFiberX w)⁻¹) =
      (chapterVIDFiberX w - 1 / 100) *
        (1 - (1 / 100 : ℂ) * chapterVIDFiberX w) /
          ((1 + (1 / 100 : ℂ) ^ 2) * chapterVIDFiberX w) := by
    field_simp [hxw]
    norm_num [chapterVIDEccentricity]
    ring
  unfold chapterVIKeplerExponentialDerivative at hderivEquation
  rw [hexp_eq, hcritical_eq] at hderivEquation
  have hdenominator : w * (chapterVIDFiberX w - 1 / 100) *
      (1 - (1 / 100 : ℂ) * chapterVIDFiberX w) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hw hxtauw) hxcriticalw
  apply (eq_div_iff hdenominator).2
  field_simp [hw, hxw, hxtauw, hxcriticalw] at hderivEquation ⊢
  linear_combination hderivEquation

/-- The circular second-anomaly ODE `ẏ=y/t` likewise holds throughout a neighborhood of D. -/
theorem eventually_hasDerivAt_chapterVIDFiberY
    {t : ℂ} (ht : t ≠ 0)
    (htPower : t ^ (3 : ℤ) =
      chapterVIKeplerExponential chapterVIDEccentricity chapterVIDX) :
    ∀ᶠ w in nhds t, HasDerivAt chapterVIDFiberY (chapterVIDFiberY w / w) w := by
  have hanalytic := analyticAt_chapterVIDFiberY ht htPower
  have hanalytic_eventually := hanalytic.eventually_analyticAt
  have hcubed := eventually_chapterVIDFiberY_cubed htPower
  have hderiv_cubed := hcubed.deriv
  have hw_eventually : ∀ᶠ w in nhds t, w ≠ 0 :=
    continuousAt_id.eventually_ne ht
  have hy_eventually : ∀ᶠ w in nhds t, chapterVIDFiberY w ≠ 0 :=
    hanalytic.continuousAt.eventually_ne (by
      simpa only [chapterVIDFiberY_apply_base htPower] using chapterVIDY_ne_zero)
  filter_upwards [hanalytic_eventually, hcubed, hderiv_cubed, hw_eventually,
    hy_eventually] with w haw hvalue hderivValue hw hyw
  have hyraw := haw.differentiableAt.hasDerivAt
  have hleft := hyraw.pow 3
  have hpow : HasDerivAt (fun u : ℂ ↦ u ^ 3) (3 * w ^ 2) w := by
    simpa only [Nat.cast_ofNat, Nat.reduceSub] using hasDerivAt_pow 3 w
  have hright : HasDerivAt chapterVIDSecondMeanInput
      ((chapterVIContourBase (-1) 3 chapterVIDEccentricity 0
        (chapterVIDX, chapterVIDY)).1 * (3 * w ^ 2)) w := by
    unfold chapterVIDSecondMeanInput
    convert hpow.const_mul
      (chapterVIContourBase (-1) 3 chapterVIDEccentricity 0
        (chapterVIDX, chapterVIDY)).1 using 1
  have hderivEquation :
      3 * chapterVIDFiberY w ^ 2 * deriv chapterVIDFiberY w =
        (chapterVIContourBase (-1) 3 chapterVIDEccentricity 0
          (chapterVIDX, chapterVIDY)).1 * (3 * w ^ 2) := by
    have hleftDeriv : deriv (fun u ↦ chapterVIDFiberY u ^ 3) w =
        (3 : ℂ) * chapterVIDFiberY w ^ 2 * deriv chapterVIDFiberY w := by
      convert hleft.deriv using 1 <;> rfl
    rw [← hleftDeriv, ← hright.deriv]
    exact hderivValue
  have hvalue' : chapterVIDFiberY w ^ 3 =
      (chapterVIContourBase (-1) 3 chapterVIDEccentricity 0
        (chapterVIDX, chapterVIDY)).1 * w ^ 3 := by
    simpa only [zpow_ofNat, chapterVIDSecondMeanInput] using hvalue
  apply hyraw.congr_deriv
  have hz_eq : (chapterVIContourBase (-1) 3 chapterVIDEccentricity 0
      (chapterVIDX, chapterVIDY)).1 = chapterVIDFiberY w ^ 3 / w ^ 3 := by
    apply (eq_div_iff (pow_ne_zero 3 hw)).2
    exact hvalue'.symm
  rw [hz_eq] at hderivEquation
  field_simp [hw, hyw] at hderivEquation ⊢
  linear_combination hderivEquation

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

theorem chapterVIDFiberX_derivative_ne_zero
    {t : ℂ} (ht : t ≠ 0)
    (_htPower : t ^ (3 : ℤ) =
      chapterVIKeplerExponential chapterVIDEccentricity chapterVIDX) :
    3 * (1 + (1 / 100 : ℂ) ^ 2) * chapterVIDX ^ 2 /
      (t * (chapterVIDX - 1 / 100) *
        (1 - (1 / 100 : ℂ) * chapterVIDX)) ≠ 0 :=
  div_ne_zero
    (mul_ne_zero (mul_ne_zero (by norm_num) (by norm_num))
      (pow_ne_zero 2 chapterVIDX_ne_zero))
    (mul_ne_zero (mul_ne_zero ht chapterVIDX_sub_tau_ne_zero)
      chapterVID_one_sub_tau_mul_x_ne_zero)

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

/-- The complex derivative of equation (7) at D, normalized against the cleared integer
polynomial used by the compiled root-isolation certificate. -/
theorem hasDerivAt_chapterVIDSecondKindSeven :
    HasDerivAt (chapterVISecondKindPolynomialSeven (-1) 3 (1 / 100 : ℂ))
      ((7500 * chapterVIDX ^ 2 + 1000050 * chapterVIDX + 12501) / 250000)
      chapterVIDX := by
  have hx := hasDerivAt_id chapterVIDX
  have hfirst := ((((hasDerivAt_const chapterVIDX (3 : ℂ)).mul
    (hx.add_const (1 / 100))).mul_const (1 + (1 / 100 : ℂ) ^ 2)).mul hx)
  have hcritical := (hasDerivAt_const chapterVIDX (1 : ℂ)).sub
    (hx.const_mul (1 / 100))
  have hsecond := (((hasDerivAt_const chapterVIDX (-1 : ℂ)).mul
    ((hx.sub_const (1 / 100)).pow 2)).mul hcritical)
  unfold chapterVISecondKindPolynomialSeven
  convert hfirst.add hsecond using 1
  · rfl
  · rfl
  · funext x
    simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, id_eq]
  · norm_num
    ring

/-- The equation-(7) root is simple over `ℂ`; this is the finite nonzero multiplier that will
remain in the second derivative after the differential identity is differentiated. -/
theorem deriv_chapterVIDSecondKindSeven_ne_zero :
    deriv (chapterVISecondKindPolynomialSeven (-1) 3 (1 / 100 : ℂ)) chapterVIDX ≠ 0 := by
  rw [hasDerivAt_chapterVIDSecondKindSeven.deriv]
  have hreal :
      7500 * chapterVIDRoot ^ 2 + 1000050 * chapterVIDRoot + 12501 ≠ 0 := by
    rw [← (hasDerivAt_chapterVIDPolynomial chapterVIDRoot).deriv]
    exact chapterVIDRoot_deriv_ne_zero
  have hcomplex :
      7500 * chapterVIDX ^ 2 + 1000050 * chapterVIDX + 12501 ≠ 0 := by
    unfold chapterVIDX
    exact_mod_cast hreal
  exact div_ne_zero hcomplex (by norm_num)

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

/-- Along the actual fixed-`z` fiber, Poincaré's collision factor has derivative zero at the
certified point D. -/
theorem hasDerivAt_chapterVIDHalfAngleCollisionPlus_zero
    {t : ℂ} (ht : t ≠ 0)
    (htPower : t ^ (3 : ℤ) =
      chapterVIKeplerExponential chapterVIDEccentricity chapterVIDX) :
    HasDerivAt (fun w ↦ chapterVIHalfAngleCollisionPlus (1 / 100 : ℂ) 2
      (chapterVIDFiberX w) (chapterVIDFiberY w)) 0 t := by
  have hraw := hasDerivAt_chapterVIHalfAngleCollisionPlus_of_fiber
    (x := chapterVIDFiberX) (y := chapterVIDFiberY) (1 / 100 : ℂ) 2 ht
    (by simpa only [chapterVIDFiberX_apply_base htPower] using chapterVIDX_ne_zero)
    (by simpa only [chapterVIDFiberX_apply_base htPower] using chapterVIDX_sub_tau_ne_zero)
    (by simpa only [chapterVIDFiberX_apply_base htPower] using
      chapterVID_one_sub_tau_mul_x_ne_zero)
    (by norm_num)
    (by simpa only [chapterVIDFiberX_apply_base htPower] using
      hasDerivAt_chapterVIDFiberX ht htPower)
    (by simpa only [chapterVIDFiberY_apply_base htPower] using
      hasDerivAt_chapterVIDFiberY ht htPower)
  apply hraw.congr_deriv
  rw [chapterVIDFiberX_apply_base htPower, chapterVIDFiberY_apply_base htPower,
    chapterVIDX_secondKindSeven, chapterVID_halfAngleCollisionPlus]
  simp

/-- The corresponding first derivative vanishes. -/
theorem deriv_chapterVIDHalfAngleCollisionPlus_eq_zero
    {t : ℂ} (ht : t ≠ 0)
    (htPower : t ^ (3 : ℤ) =
      chapterVIKeplerExponential chapterVIDEccentricity chapterVIDX) :
    deriv (fun w ↦ chapterVIHalfAngleCollisionPlus (1 / 100 : ℂ) 2
      (chapterVIDFiberX w) (chapterVIDFiberY w)) t = 0 :=
  (hasDerivAt_chapterVIDHalfAngleCollisionPlus_zero ht htPower).deriv

/-- Poincaré's exact differential-ideal formula for `H'` holds throughout a neighborhood of D. -/
theorem eventually_hasDerivAt_chapterVIDHalfAngleCollisionPlus
    {t : ℂ} (ht : t ≠ 0)
    (htPower : t ^ (3 : ℤ) =
      chapterVIKeplerExponential chapterVIDEccentricity chapterVIDX) :
    ∀ᶠ w in nhds t, HasDerivAt
      (fun u ↦ chapterVIHalfAngleCollisionPlus (1 / 100 : ℂ) 2
        (chapterVIDFiberX u) (chapterVIDFiberY u))
      (chapterVISecondKindPolynomialSeven (-1) 3 (1 / 100 : ℂ)
          (chapterVIDFiberX w) /
          (w * (1 + (1 / 100 : ℂ) ^ 2) * chapterVIDFiberX w *
            (1 - (1 / 100 : ℂ) * chapterVIDFiberX w)) +
        chapterVIHalfAngleCollisionPlus (1 / 100 : ℂ) 2
          (chapterVIDFiberX w) (chapterVIDFiberY w) / w) w := by
  have hxanalytic := analyticAt_chapterVIDFiberX ht htPower
  have hw_eventually : ∀ᶠ w in nhds t, w ≠ 0 :=
    continuousAt_id.eventually_ne ht
  have hx_eventually : ∀ᶠ w in nhds t, chapterVIDFiberX w ≠ 0 :=
    hxanalytic.continuousAt.eventually_ne (by
      simpa only [chapterVIDFiberX_apply_base htPower] using chapterVIDX_ne_zero)
  have hxtau_eventually : ∀ᶠ w in nhds t,
      chapterVIDFiberX w - (1 / 100 : ℂ) ≠ 0 :=
    (hxanalytic.sub analyticAt_const).continuousAt.eventually_ne (by
      simpa only [Pi.sub_apply, chapterVIDFiberX_apply_base htPower] using
        chapterVIDX_sub_tau_ne_zero)
  have hxcritical_eventually : ∀ᶠ w in nhds t,
      1 - (1 / 100 : ℂ) * chapterVIDFiberX w ≠ 0 :=
    (analyticAt_const.sub (analyticAt_const.mul hxanalytic)).continuousAt.eventually_ne (by
      simpa only [Pi.sub_apply, Pi.mul_apply, chapterVIDFiberX_apply_base htPower] using
        chapterVID_one_sub_tau_mul_x_ne_zero)
  have hxode := eventually_hasDerivAt_chapterVIDFiberX ht htPower
  have hyode := eventually_hasDerivAt_chapterVIDFiberY ht htPower
  filter_upwards [hw_eventually, hx_eventually, hxtau_eventually,
    hxcritical_eventually, hxode, hyode] with w hw hxw hxtauw hxcriticalw hx hy
  exact hasDerivAt_chapterVIHalfAngleCollisionPlus_of_fiber
    (1 / 100 : ℂ) 2 hw hxw hxtauw hxcriticalw (by norm_num) hx hy

theorem eventually_deriv_chapterVIDHalfAngleCollisionPlus_eq
    {t : ℂ} (ht : t ≠ 0)
    (htPower : t ^ (3 : ℤ) =
      chapterVIKeplerExponential chapterVIDEccentricity chapterVIDX) :
    (fun w ↦ deriv (fun u ↦ chapterVIHalfAngleCollisionPlus (1 / 100 : ℂ) 2
      (chapterVIDFiberX u) (chapterVIDFiberY u)) w) =ᶠ[nhds t]
      (fun w ↦ chapterVISecondKindPolynomialSeven (-1) 3 (1 / 100 : ℂ)
          (chapterVIDFiberX w) /
          (w * (1 + (1 / 100 : ℂ) ^ 2) * chapterVIDFiberX w *
            (1 - (1 / 100 : ℂ) * chapterVIDFiberX w)) +
        chapterVIHalfAngleCollisionPlus (1 / 100 : ℂ) 2
          (chapterVIDFiberX w) (chapterVIDFiberY w) / w) := by
  filter_upwards [eventually_hasDerivAt_chapterVIDHalfAngleCollisionPlus ht htPower] with w hw
  exact hw.deriv

/-- The derivative of the right-hand side of Poincaré's differential identity at D.  All terms
except the simple equation-(7) multiplier vanish. -/
theorem hasDerivAt_chapterVIDHalfAngleDerivativeRHS
    {t : ℂ} (ht : t ≠ 0)
    (htPower : t ^ (3 : ℤ) =
      chapterVIKeplerExponential chapterVIDEccentricity chapterVIDX) :
    HasDerivAt
      (fun w ↦ chapterVISecondKindPolynomialSeven (-1) 3 (1 / 100 : ℂ)
          (chapterVIDFiberX w) /
          (w * (1 + (1 / 100 : ℂ) ^ 2) * chapterVIDFiberX w *
            (1 - (1 / 100 : ℂ) * chapterVIDFiberX w)) +
        chapterVIHalfAngleCollisionPlus (1 / 100 : ℂ) 2
          (chapterVIDFiberX w) (chapterVIDFiberY w) / w)
      (deriv (chapterVISecondKindPolynomialSeven (-1) 3 (1 / 100 : ℂ)) chapterVIDX *
          (3 * (1 + (1 / 100 : ℂ) ^ 2) * chapterVIDX ^ 2 /
            (t * (chapterVIDX - 1 / 100) *
              (1 - (1 / 100 : ℂ) * chapterVIDX))) /
        (t * (1 + (1 / 100 : ℂ) ^ 2) * chapterVIDX *
          (1 - (1 / 100 : ℂ) * chapterVIDX))) t := by
  let xdot : ℂ := 3 * (1 + (1 / 100 : ℂ) ^ 2) * chapterVIDX ^ 2 /
    (t * (chapterVIDX - 1 / 100) * (1 - (1 / 100 : ℂ) * chapterVIDX))
  have hx : HasDerivAt chapterVIDFiberX xdot t := by
    simpa only [xdot] using hasDerivAt_chapterVIDFiberX ht htPower
  have hpolyBase := hasDerivAt_chapterVIDSecondKindSeven
  have hpoly : HasDerivAt
      (chapterVISecondKindPolynomialSeven (-1) 3 (1 / 100 : ℂ))
      (deriv (chapterVISecondKindPolynomialSeven (-1) 3 (1 / 100 : ℂ)) chapterVIDX)
      chapterVIDX :=
    hpolyBase.congr_deriv hpolyBase.deriv.symm
  have hpoly' : HasDerivAt
      (chapterVISecondKindPolynomialSeven (-1) 3 (1 / 100 : ℂ))
      (deriv (chapterVISecondKindPolynomialSeven (-1) 3 (1 / 100 : ℂ)) chapterVIDX)
      (chapterVIDFiberX t) := by
    simpa only [chapterVIDFiberX_apply_base htPower] using hpoly
  have hpolyComp := hpoly'.comp t hx
  let den : ℂ → ℂ := fun w ↦
    w * (1 + (1 / 100 : ℂ) ^ 2) * chapterVIDFiberX w *
      (1 - (1 / 100 : ℂ) * chapterVIDFiberX w)
  have hdendiff : DifferentiableAt ℂ den t := by
    dsimp only [den]
    exact (((hasDerivAt_id t).mul_const (1 + (1 / 100 : ℂ) ^ 2)).mul hx).mul
      ((hasDerivAt_const t (1 : ℂ)).sub (hx.const_mul (1 / 100 : ℂ))) |>.differentiableAt
  have hden : HasDerivAt den (deriv den t) t := hdendiff.hasDerivAt
  have hden_ne : t * (1 + (1 / 100 : ℂ) ^ 2) * chapterVIDX *
      (1 - (1 / 100 : ℂ) * chapterVIDX) ≠ 0 :=
    mul_ne_zero
      (mul_ne_zero (mul_ne_zero ht (by norm_num)) chapterVIDX_ne_zero)
      chapterVID_one_sub_tau_mul_x_ne_zero
  have hden_ne' : den t ≠ 0 := by
    simpa only [den,
      chapterVIDFiberX_apply_base htPower] using hden_ne
  have hquot := hpolyComp.div hden hden_ne'
  have hquotSimple : HasDerivAt
      (fun w ↦ chapterVISecondKindPolynomialSeven (-1) 3 (1 / 100 : ℂ)
        (chapterVIDFiberX w) /
          (w * (1 + (1 / 100 : ℂ) ^ 2) * chapterVIDFiberX w *
            (1 - (1 / 100 : ℂ) * chapterVIDFiberX w)))
      (deriv (chapterVISecondKindPolynomialSeven (-1) 3 (1 / 100 : ℂ)) chapterVIDX *
        xdot / (t * (1 + (1 / 100 : ℂ) ^ 2) * chapterVIDX *
          (1 - (1 / 100 : ℂ) * chapterVIDX))) t := by
    apply hquot.congr_deriv
    simp only [Function.comp_apply, den,
      chapterVIDFiberX_apply_base htPower, chapterVIDX_secondKindSeven,
      zero_mul, sub_zero]
    field_simp [hden_ne]
  have hcollision := hasDerivAt_chapterVIDHalfAngleCollisionPlus_zero ht htPower
  have hid := hasDerivAt_id t
  have hcollisionQuot := hcollision.div hid ht
  have hcollisionQuotSimple : HasDerivAt
      (fun w ↦ chapterVIHalfAngleCollisionPlus (1 / 100 : ℂ) 2
        (chapterVIDFiberX w) (chapterVIDFiberY w) / w) 0 t := by
    apply hcollisionQuot.congr_deriv
    simp only [id_eq, chapterVIDFiberX_apply_base htPower,
      chapterVIDFiberY_apply_base htPower, chapterVID_halfAngleCollisionPlus]
    field_simp [ht]
    ring
  have hsum := hquotSimple.add hcollisionQuotSimple
  dsimp only [xdot] at hsum
  change HasDerivAt
    ((fun w ↦ chapterVISecondKindPolynomialSeven (-1) 3 (1 / 100 : ℂ)
      (chapterVIDFiberX w) /
        (w * (1 + (1 / 100 : ℂ) ^ 2) * chapterVIDFiberX w *
          (1 - (1 / 100 : ℂ) * chapterVIDFiberX w))) +
      fun w ↦ chapterVIHalfAngleCollisionPlus (1 / 100 : ℂ) 2
        (chapterVIDFiberX w) (chapterVIDFiberY w) / w) _ t
  convert hsum using 1
  all_goals first | rfl | simp

/-- The collision factor has a genuine double, not higher-order, zero along the selected fiber. -/
theorem deriv_deriv_chapterVIDHalfAngleCollisionPlus_ne_zero
    {t : ℂ} (ht : t ≠ 0)
    (htPower : t ^ (3 : ℤ) =
      chapterVIKeplerExponential chapterVIDEccentricity chapterVIDX) :
    deriv (fun w ↦ deriv (fun u ↦ chapterVIHalfAngleCollisionPlus (1 / 100 : ℂ) 2
      (chapterVIDFiberX u) (chapterVIDFiberY u)) w) t ≠ 0 := by
  have heq := (eventually_deriv_chapterVIDHalfAngleCollisionPlus_eq ht htPower).deriv_eq
  rw [heq, (hasDerivAt_chapterVIDHalfAngleDerivativeRHS ht htPower).deriv]
  apply div_ne_zero
  · exact mul_ne_zero deriv_chapterVIDSecondKindSeven_ne_zero
      (chapterVIDFiberX_derivative_ne_zero ht htPower)
  · exact mul_ne_zero
      (mul_ne_zero (mul_ne_zero ht (by norm_num)) chapterVIDX_ne_zero)
      chapterVID_one_sub_tau_mul_x_ne_zero

/-- The same first-order tangency, stated for the literal source collision factor rather than
its half-angle normal form. -/
theorem eventually_chapterVIDPlanarCollisionFactorPlus_eq_halfAngle
    {t : ℂ} (ht : t ≠ 0)
    (htPower : t ^ (3 : ℤ) =
      chapterVIKeplerExponential chapterVIDEccentricity chapterVIDX) :
    (fun w ↦ chapterVIPlanarCollisionFactorPlus
      chapterVIDEccentricity chapterVIDComplement 0 1 2
      (chapterVIDFiberX w) (chapterVIDFiberY w)) =ᶠ[nhds t]
      (fun w ↦ chapterVIHalfAngleCollisionPlus (1 / 100 : ℂ) 2
        (chapterVIDFiberX w) (chapterVIDFiberY w)) := by
  have hx := hasDerivAt_chapterVIDFiberX ht htPower
  have hy := hasDerivAt_chapterVIDFiberY ht htPower
  have hx_ne : chapterVIDFiberX t ≠ 0 := by
    simpa only [chapterVIDFiberX_apply_base htPower] using chapterVIDX_ne_zero
  have hy_ne : chapterVIDFiberY t ≠ 0 := by
    simpa only [chapterVIDFiberY_apply_base htPower] using chapterVIDY_ne_zero
  have hx_eventually := hx.continuousAt.eventually_ne hx_ne
  have hy_eventually := hy.continuousAt.eventually_ne hy_ne
  filter_upwards [hx_eventually, hy_eventually] with w hxw hyw
  exact chapterVIPlanarCollisionFactorPlus_eq_halfAngle
    (1 / 100 : ℂ) chapterVIDEccentricity chapterVIDComplement 2
    (chapterVIDFiberX w) (chapterVIDFiberY w)
    chapterVID_halfAngle_sine chapterVID_halfAngle_cosine hxw hyw (by norm_num)

theorem deriv_chapterVIDPlanarCollisionFactorPlus_eq_zero
    {t : ℂ} (ht : t ≠ 0)
    (htPower : t ^ (3 : ℤ) =
      chapterVIKeplerExponential chapterVIDEccentricity chapterVIDX) :
    deriv (fun w ↦ chapterVIPlanarCollisionFactorPlus
      chapterVIDEccentricity chapterVIDComplement 0 1 2
      (chapterVIDFiberX w) (chapterVIDFiberY w)) t = 0 := by
  have heq := eventually_chapterVIDPlanarCollisionFactorPlus_eq_halfAngle ht htPower
  rw [heq.deriv_eq]
  exact deriv_chapterVIDHalfAngleCollisionPlus_eq_zero ht htPower

theorem deriv_deriv_chapterVIDPlanarCollisionFactorPlus_ne_zero
    {t : ℂ} (ht : t ≠ 0)
    (htPower : t ^ (3 : ℤ) =
      chapterVIKeplerExponential chapterVIDEccentricity chapterVIDX) :
    deriv (fun w ↦ deriv (fun u ↦ chapterVIPlanarCollisionFactorPlus
      chapterVIDEccentricity chapterVIDComplement 0 1 2
      (chapterVIDFiberX u) (chapterVIDFiberY u)) w) t ≠ 0 := by
  have heq := eventually_chapterVIDPlanarCollisionFactorPlus_eq_halfAngle ht htPower
  rw [(heq.deriv).deriv_eq]
  exact deriv_deriv_chapterVIDHalfAngleCollisionPlus_ne_zero ht htPower

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

/-- The nonzero second derivative in Poincaré's literal `(z,t)` coordinates. -/
theorem deriv_deriv_chapterVIDPoincareCollisionFactorPlus_ne_zero
    {t : ℂ} (ht : t ≠ 0)
    (htPower : t ^ (3 : ℤ) =
      chapterVIKeplerExponential chapterVIDEccentricity chapterVIDX) :
    deriv (fun w ↦ deriv (fun u ↦ chapterVIPoincareCollisionFactorPlus
      (-1) 3 chapterVIDEccentricity chapterVIDComplement 0 1 2
      (chapterVIDX, chapterVIDY) chapterVIDX_ne_zero chapterVIDY_ne_zero
      chapterVID_firstKeplerCritical chapterVID_secondKeplerCritical (by norm_num)
      ((chapterVIContourBase (-1) 3 chapterVIDEccentricity 0
        (chapterVIDX, chapterVIDY)).1, u)) w) t ≠ 0 := by
  change deriv (fun w ↦ deriv (fun u ↦ chapterVIPlanarCollisionFactorPlus
    chapterVIDEccentricity chapterVIDComplement 0 1 2
    (chapterVIDFiberX u) (chapterVIDFiberY u)) w) t ≠ 0
  exact deriv_deriv_chapterVIDPlanarCollisionFactorPlus_ne_zero ht htPower

/-- The complete convergent Poincaré radicand has analytic order exactly two on the certified
fixed-`z` fiber through D. -/
theorem analyticOrderAt_chapterVIDPoincareRadicand_eq_two :
    analyticOrderAt
      (fun w ↦ chapterVIPoincareRadicand (-1) 3
        chapterVIDEccentricity chapterVIDComplement 0 1 2 2
        (chapterVIDX, chapterVIDY) chapterVIDX_ne_zero chapterVIDY_ne_zero
        chapterVID_firstKeplerCritical chapterVID_secondKeplerCritical (by norm_num)
        ((chapterVIContourBase (-1) 3 chapterVIDEccentricity 0
          (chapterVIDX, chapterVIDY)).1, w)) chapterVIDTBase = 2 := by
  apply analyticOrderAt_chapterVIPoincareRadicand_sourceFiber_eq_two
    (-1) 3 chapterVIDEccentricity chapterVIDComplement 0 1 2 2
    (chapterVIDX, chapterVIDY) chapterVIDX_ne_zero chapterVIDY_ne_zero
    chapterVID_firstKeplerCritical chapterVID_secondKeplerCritical (by norm_num)
    chapterVIDTBase chapterVIDTBase_ne_zero chapterVIDTBase_pow
  · rw [chapterVIPoincareCollisionFactorPlus_apply_base
      (-1) 3 chapterVIDEccentricity chapterVIDComplement 0 1 2
      (chapterVIDX, chapterVIDY) chapterVIDX_ne_zero chapterVIDY_ne_zero
      chapterVID_firstKeplerCritical chapterVID_secondKeplerCritical (by norm_num)
      chapterVIDTBase chapterVIDTBase_pow]
    exact chapterVID_collisionFactorPlus
  · exact deriv_chapterVIDPoincareCollisionFactorPlus_eq_zero
      chapterVIDTBase_ne_zero chapterVIDTBase_pow
  · exact deriv_deriv_chapterVIDPoincareCollisionFactorPlus_ne_zero
      chapterVIDTBase_ne_zero chapterVIDTBase_pow
  · rw [chapterVIPoincareCollisionFactorMinus_apply_base
      (-1) 3 chapterVIDEccentricity chapterVIDComplement 0 1 2
      (chapterVIDX, chapterVIDY) chapterVIDX_ne_zero chapterVIDY_ne_zero
      chapterVID_firstKeplerCritical chapterVID_secondKeplerCritical (by norm_num)
      chapterVIDTBase chapterVIDTBase_pow]
    exact chapterVID_collisionFactorMinus_ne_zero

end PoincareChapterVI
