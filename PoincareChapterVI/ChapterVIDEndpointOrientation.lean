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

open Filter
open scoped ComplexConjugate

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

/-- Poincare's explicit real-coefficient root-coordinate change commutes with complex
conjugation. -/
theorem chapterVIDRootToOriginalContour_conj (u : ℂ) :
    chapterVIDRootToOriginalContour (conj u) =
      conj (chapterVIDRootToOriginalContour u) := by
  unfold chapterVIDRootToOriginalContour chapterVIDRootExponentialArgument
  rw [map_mul, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_sub, map_inv₀, map_pow, map_div₀, map_ofNat]

/-- The canonical local inverse therefore maps nearby real source coordinates to exactly real
root coordinates. -/
theorem eventually_chapterVIDOriginalContourToRoot_ofReal_im_eq_zero :
    ∀ᶠ t : ℝ in nhds chapterVIDTBase.re,
      (chapterVIDOriginalContourToRoot (t : ℂ)).im = 0 := by
  have hfa : (chapterVIDRootToOriginalContour chapterVIDCollisionLift).im = 0 := by
    change chapterVIDTBase.im = 0
    exact Complex.conj_eq_iff_im.mp conj_chapterVIDTBase
  have h := eventually_localInverse_ofReal_im_eq_zero
    hasStrictDerivAt_chapterVIDRootToOriginalContour_collision
    deriv_chapterVIDRootToOriginalContour_collision_ne_zero
    conj_chapterVIDCollisionLift hfa
    (Filter.Eventually.of_forall chapterVIDRootToOriginalContour_conj)
  have hbase : chapterVIDRootToOriginalContour chapterVIDCollisionLift =
      chapterVIDTBase := rfl
  rw [hbase] at h
  simpa only [chapterVIDOriginalContourToRoot] using h

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

/-! ## Certified phase of the prepared unit -/

theorem chapterVIDRootCoordinateCollisionFactorPlus_base :
    chapterVIDRootCoordinateCollisionFactorPlus chapterVIDZRootBase
      chapterVIDCollisionLift = 0 := by
  unfold chapterVIDRootCoordinateCollisionFactorPlus
  rw [chapterVIDCollisionLift_pow, chapterVIDRootSecondAnomaly_base]
  exact chapterVID_collisionFactorPlus

theorem chapterVIDRootCoordinateCollisionFactorMinus_base_eq_parameter :
    chapterVIDRootCoordinateCollisionFactorMinus chapterVIDZRootBase
      chapterVIDCollisionLift =
        chapterVIDParameterCollisionMinus chapterVIDZBase := by
  unfold chapterVIDRootCoordinateCollisionFactorMinus
  rw [chapterVIDCollisionLift_pow, chapterVIDRootSecondAnomaly_base]
  unfold chapterVIDParameterCollisionMinus chapterVIDZBase
  rw [chapterVIPoincareCollisionFactorMinus_apply_base
    (-1) 3 chapterVIDEccentricity chapterVIDComplement 0 1 2
    (chapterVIDX, chapterVIDY) chapterVIDX_ne_zero chapterVIDY_ne_zero
    chapterVID_firstKeplerCritical chapterVID_secondKeplerCritical (by norm_num)
    chapterVIDTBase chapterVIDTBase_pow]

set_option backward.isDefEq.respectTransparency.types false in
theorem chapterVIDRootCoordinateRadicandSecondDerivative_base :
    deriv (deriv (chapterVIDRootCoordinateRadicand chapterVIDZRootBase))
        chapterVIDCollisionLift =
      chapterVIDRootCoordinateCollisionFactorPlusSecondDerivative
          chapterVIDZRootBase chapterVIDCollisionLift *
        chapterVIDRootCoordinateCollisionFactorMinus chapterVIDZRootBase
          chapterVIDCollisionLift := by
  let plus : ℂ → ℂ := fun u ↦
    chapterVIPlanarCollisionFactorPlus chapterVIDEccentricity chapterVIDComplement
      0 1 2 (u ^ 3) (chapterVIDRootSecondAnomaly chapterVIDZRootBase u)
  let minus : ℂ → ℂ := fun u ↦
    chapterVIPlanarCollisionFactorMinus chapterVIDEccentricity chapterVIDComplement
      0 1 2 (u ^ 3) (chapterVIDRootSecondAnomaly chapterVIDZRootBase u)
  let plus' := chapterVIDRootCoordinateCollisionFactorPlusDerivative chapterVIDZRootBase
  have hplusEq : plus =
      chapterVIDRootCoordinateCollisionFactorPlus chapterVIDZRootBase := rfl
  have hminusEq : minus =
      chapterVIDRootCoordinateCollisionFactorMinus chapterVIDZRootBase := rfl
  have hanomaly : AnalyticAt ℂ
      (chapterVIDRootSecondAnomaly chapterVIDZRootBase) chapterVIDCollisionLift := by
    unfold chapterVIDRootSecondAnomaly
    exact analyticAt_const.mul
      (analyticAt_chapterVIDRootToOriginalContour chapterVIDCollisionLift_ne_zero)
  have hpair : AnalyticAt ℂ (fun u : ℂ ↦
      (u ^ 3, chapterVIDRootSecondAnomaly chapterVIDZRootBase u))
      chapterVIDCollisionLift :=
    (analyticAt_id.pow 3).prod hanomaly
  have hfirstNe : chapterVIDCollisionLift ^ 3 ≠ 0 :=
    pow_ne_zero 3 chapterVIDCollisionLift_ne_zero
  have hsecondNe : chapterVIDRootSecondAnomaly chapterVIDZRootBase
      chapterVIDCollisionLift ≠ 0 := by
    rw [chapterVIDRootSecondAnomaly_base]
    exact chapterVIDY_ne_zero
  have hplus : AnalyticAt ℂ plus chapterVIDCollisionLift := by
    have hsource := analyticAt_chapterVIPlanarCollisionFactorPlus
      chapterVIDEccentricity chapterVIDComplement 0 1 2
      (point := (chapterVIDCollisionLift ^ 3,
        chapterVIDRootSecondAnomaly chapterVIDZRootBase chapterVIDCollisionLift))
      hfirstNe hsecondNe
    simpa only [plus, chapterVIDRootCoordinateCollisionFactorPlus,
      Function.comp_def] using hsource.comp_of_eq hpair rfl
  have hminus : AnalyticAt ℂ minus chapterVIDCollisionLift := by
    have hsource := analyticAt_chapterVIPlanarCollisionFactorMinus
      chapterVIDEccentricity chapterVIDComplement 0 1 2
      (point := (chapterVIDCollisionLift ^ 3,
        chapterVIDRootSecondAnomaly chapterVIDZRootBase chapterVIDCollisionLift))
      hfirstNe hsecondNe
    simpa only [minus, chapterVIDRootCoordinateCollisionFactorMinus,
      Function.comp_def] using hsource.comp_of_eq hpair rfl
  have hderiv : deriv (plus * minus) =ᶠ[nhds chapterVIDCollisionLift]
      plus' * minus + plus * deriv minus := by
    filter_upwards [hplus.eventually_analyticAt, hminus.eventually_analyticAt,
      eventually_ne_nhds chapterVIDCollisionLift_ne_zero] with u hpu hmu hu
    rw [deriv_mul hpu.differentiableAt hmu.differentiableAt]
    have hpderiv : deriv plus u = plus' u := by
      rw [hplusEq]
      exact (hasDerivAt_chapterVIDRootCoordinateCollisionFactorPlus
        chapterVIDZRootBase_ne_zero hu).deriv
    rw [hpderiv]
    rfl
  have hproduct : chapterVIDRootCoordinateRadicand chapterVIDZRootBase =
      plus * minus := by
    funext u
    exact chapterVIDRootCoordinateRadicand_eq_factors chapterVIDZRootBase u
  rw [hproduct]
  rw [hderiv.deriv_eq]
  rw [deriv_add
    ((hasDerivAt_chapterVIDRootCoordinateCollisionFactorPlusDerivative
      chapterVIDCollisionLift_ne_zero).differentiableAt.mul hminus.differentiableAt)
    (hplus.differentiableAt.mul hminus.deriv.differentiableAt)]
  rw [deriv_mul
    (hasDerivAt_chapterVIDRootCoordinateCollisionFactorPlusDerivative
      chapterVIDCollisionLift_ne_zero).differentiableAt hminus.differentiableAt,
    deriv_mul hplus.differentiableAt hminus.deriv.differentiableAt]
  rw [(hasDerivAt_chapterVIDRootCoordinateCollisionFactorPlusDerivative
      chapterVIDCollisionLift_ne_zero).deriv]
  rw [hplusEq, hminusEq]
  rw [(hasDerivAt_chapterVIDRootCoordinateCollisionFactorPlus
      chapterVIDZRootBase_ne_zero chapterVIDCollisionLift_ne_zero).deriv]
  rw [chapterVIDRootCoordinateCollisionFactorPlusDerivative_base,
    chapterVIDRootCoordinateCollisionFactorPlus_base]
  ring

theorem chapterVIDRootCoordinateCollisionFactorPlusSecondDerivative_base_im :
    (chapterVIDRootCoordinateCollisionFactorPlusSecondDerivative
      chapterVIDZRootBase chapterVIDCollisionLift).im = 0 := by
  rw [chapterVIDRootCoordinateCollisionFactorPlusSecondDerivative_base_formula]
  have hscalar :
      (-18 * (33327498249925 * (chapterVIDRoot : ℂ) ^ 2 +
          833324982499 * (chapterVIDRoot : ℂ) - 1666499975) /
          (2500500025 * (chapterVIDRoot : ℂ) ^ 4)) =
        ((-18 * (33327498249925 * chapterVIDRoot ^ 2 +
          833324982499 * chapterVIDRoot - 1666499975) /
          (2500500025 * chapterVIDRoot ^ 4) : ℝ) : ℂ) := by
    push_cast
    rfl
  have hscalarIm :
      (-18 * (33327498249925 * (chapterVIDRoot : ℂ) ^ 2 +
          833324982499 * (chapterVIDRoot : ℂ) - 1666499975) /
          (2500500025 * (chapterVIDRoot : ℂ) ^ 4)).im = 0 := by
    rw [hscalar]
    exact Complex.ofReal_im _
  rw [Complex.mul_im]
  have hcollisionIm : chapterVIDCollisionLift.im = 0 := by
    rw [chapterVIDCollisionLift_eq_neg_norm]
    simp
  rw [hcollisionIm, hscalarIm]
  ring

theorem chapterVIDRootCoordinateRadicandSecondDerivative_base_re_neg :
    (deriv (deriv (chapterVIDRootCoordinateRadicand chapterVIDZRootBase))
      chapterVIDCollisionLift).re < 0 := by
  rw [chapterVIDRootCoordinateRadicandSecondDerivative_base, Complex.mul_re,
    chapterVIDRootCoordinateCollisionFactorPlusSecondDerivative_base_im, zero_mul, sub_zero,
    chapterVIDRootCoordinateCollisionFactorMinus_base_eq_parameter]
  exact mul_neg_of_neg_of_pos
    chapterVIDRootCoordinateCollisionFactorPlusSecondDerivative_base_re_neg
    chapterVIDParameterCollisionMinus_base_re_pos

theorem chapterVIDRootCoordinateRadicandSecondDerivative_base_im_zero :
    (deriv (deriv (chapterVIDRootCoordinateRadicand chapterVIDZRootBase))
      chapterVIDCollisionLift).im = 0 := by
  have hminusIm :
      (chapterVIDRootCoordinateCollisionFactorMinus chapterVIDZRootBase
        chapterVIDCollisionLift).im = 0 := by
    rw [chapterVIDRootCoordinateCollisionFactorMinus_base_eq_parameter]
    have h := congrArg Complex.im chapterVIDParameterCollisionMinus_base_eq_ofReal
    simpa only [Complex.ofReal_im] using h
  rw [chapterVIDRootCoordinateRadicandSecondDerivative_base, Complex.mul_im,
    chapterVIDRootCoordinateCollisionFactorPlusSecondDerivative_base_im, hminusIm]
  ring

set_option backward.isDefEq.respectTransparency.types false in
theorem chapterVI_secondDeriv_comp_of_first_zero
    {f g : ℂ → ℂ} {x : ℂ}
    (hf : AnalyticAt ℂ f (g x)) (hg : AnalyticAt ℂ g x)
    (hfirst : deriv f (g x) = 0) :
    deriv (deriv (f ∘ g)) x =
      deriv (deriv f) (g x) * (deriv g x) ^ 2 := by
  have hchain : deriv (f ∘ g) =ᶠ[nhds x]
      (deriv f ∘ g) * deriv g := by
    filter_upwards [hg.eventually_analyticAt,
      hg.continuousAt.tendsto.eventually hf.eventually_analyticAt] with y hgy hfy
    rw [(hfy.differentiableAt.hasDerivAt.comp y
      hgy.differentiableAt.hasDerivAt).deriv]
    rfl
  rw [hchain.deriv_eq]
  have hleft : HasDerivAt (deriv f ∘ g)
      (deriv (deriv f) (g x) * deriv g x) x :=
    hf.deriv.differentiableAt.hasDerivAt.comp x
      hg.differentiableAt.hasDerivAt
  rw [deriv_mul hleft.differentiableAt hg.deriv.differentiableAt,
    hleft.deriv]
  change deriv (deriv f) (g x) * deriv g x * deriv g x +
      deriv f (g x) * deriv (deriv g) x = _
  rw [hfirst]
  ring

theorem eventually_chapterVIDRootCoordinateRadicand_eq_centered_comp :
    chapterVIDRootCoordinateRadicand chapterVIDZRootBase =ᶠ[
        nhds chapterVIDCollisionLift]
      (fun u : ℂ ↦ chapterVIDCenteredRadicand
        (chapterVIDZBase,
          chapterVIDRootToOriginalContour u - chapterVIDTBase)) := by
  have htend : Tendsto (fun u : ℂ ↦ (chapterVIDZRootBase, u))
      (nhds chapterVIDCollisionLift)
      (nhds (chapterVIDZRootBase, chapterVIDCollisionLift)) :=
    continuousAt_const.prodMk continuousAt_id
  have hpulled := htend.eventually eventually_chapterVIDRadicand_rootCoordinates
  have hzpow : chapterVIDZRootBase ^ 3 = chapterVIDZBase := by
    simpa only [zpow_ofNat] using chapterVIDZRootBase_pow
  filter_upwards [hpulled] with u hu
  rw [← hu]
  unfold chapterVIDCenteredRadicand
  rw [chapterVIDCriticalCenter_base, chapterVIDCriticalValue_base, sub_zero, hzpow]
  congr 2
  ring

theorem chapterVI_secondDeriv_sq_mul (U : ℂ → ℂ) (hU : AnalyticAt ℂ U 0) :
    deriv (deriv (fun u : ℂ ↦ u ^ 2 * U u)) 0 = 2 * U 0 := by
  let q : ℂ → ℂ := fun u ↦ u ^ 2 * U u
  have hderiv : deriv q =ᶠ[nhds 0]
      fun u ↦ 2 * u * U u + u ^ 2 * deriv U u := by
    filter_upwards [hU.eventually_analyticAt] with u hu
    change deriv ((fun z : ℂ ↦ z ^ 2) * U) u = _
    rw [deriv_mul (hasDerivAt_pow 2 u).differentiableAt hu.differentiableAt,
      (hasDerivAt_pow 2 u).deriv]
    simp
  have hfirst : deriv (fun u : ℂ ↦ 2 * u * U u) 0 = 2 * U 0 := by
    have hlinear : deriv (fun u : ℂ ↦ 2 * u) 0 = 2 :=
      (hasDerivAt_const_mul (x := (0 : ℂ)) (2 : ℂ)).deriv
    change deriv ((fun u : ℂ ↦ 2 * u) * U) 0 = _
    rw [deriv_mul (by fun_prop) hU.differentiableAt, hlinear]
    simp
  have hsecond : deriv (fun u : ℂ ↦ u ^ 2 * deriv U u) 0 = 0 := by
    change deriv ((fun u : ℂ ↦ u ^ 2) * deriv U) 0 = _
    rw [deriv_mul (hasDerivAt_pow 2 (0 : ℂ)).differentiableAt
      hU.deriv.differentiableAt, (hasDerivAt_pow 2 (0 : ℂ)).deriv]
    norm_num
  change deriv (deriv q) 0 = _
  rw [hderiv.deriv_eq]
  change deriv ((fun u : ℂ ↦ 2 * u * U u) +
    (fun u : ℂ ↦ u ^ 2 * deriv U u)) 0 = _
  rw [deriv_add (by fun_prop) (by fun_prop), hfirst, hsecond, add_zero]

theorem eventually_chapterVIDRootCoordinateRadicand_eq_fiberUnit_comp :
    chapterVIDRootCoordinateRadicand chapterVIDZRootBase =ᶠ[
        nhds chapterVIDCollisionLift]
      (fun u : ℂ ↦
        (chapterVIDRootToOriginalContour u - chapterVIDTBase) ^ 2 *
          chapterVIDCenteredFiberUnit
            (chapterVIDRootToOriginalContour u - chapterVIDTBase)) := by
  let shift : ℂ → ℂ := fun u ↦
    chapterVIDRootToOriginalContour u - chapterVIDTBase
  have hshift : AnalyticAt ℂ shift chapterVIDCollisionLift := by
    exact (analyticAt_chapterVIDRootToOriginalContour
      chapterVIDCollisionLift_ne_zero).sub analyticAt_const
  have hshiftBase : shift chapterVIDCollisionLift = 0 := by
    apply sub_eq_zero.mpr
    rfl
  have hcentered : chapterVIDRootCoordinateRadicand chapterVIDZRootBase =ᶠ[
      nhds chapterVIDCollisionLift]
      (fun u : ℂ ↦ chapterVIDCenteredRadicand (chapterVIDZBase, shift u)) := by
    simpa only [shift, Function.comp_def] using
      eventually_chapterVIDRootCoordinateRadicand_eq_centered_comp
  have htend : Tendsto shift (nhds chapterVIDCollisionLift) (nhds 0) := by
    have htend' := hshift.continuousAt
    change Tendsto shift (nhds chapterVIDCollisionLift)
      (nhds (shift chapterVIDCollisionLift)) at htend'
    rwa [hshiftBase] at htend'
  have hfactor := htend.eventually
    (show (fun s : ℂ ↦ chapterVIDCenteredRadicand (chapterVIDZBase, s)) =ᶠ[
        nhds 0] (fun s ↦ s ^ 2 * chapterVIDCenteredFiberUnit s) from
      eventually_chapterVIDCenteredRadicand_eq_sq_mul_fiberUnit)
  filter_upwards [hcentered, hfactor] with u hu hfactorU
  exact hu.trans hfactorU

theorem chapterVIDRootCoordinateRadicandSecondDerivative_eq_fiberUnit :
    deriv (deriv (chapterVIDRootCoordinateRadicand chapterVIDZRootBase))
        chapterVIDCollisionLift =
      (2 * chapterVIDCenteredFiberUnit 0) *
        (deriv chapterVIDRootToOriginalContour chapterVIDCollisionLift) ^ 2 := by
  let U := chapterVIDCenteredFiberUnit
  let q : ℂ → ℂ := fun s ↦ s ^ 2 * U s
  let shift : ℂ → ℂ := fun u ↦
    chapterVIDRootToOriginalContour u - chapterVIDTBase
  have hU : AnalyticAt ℂ U 0 := by
    simpa only [U] using analyticAt_chapterVIDCenteredFiberUnit
  have hq : AnalyticAt ℂ q 0 := by
    exact (analyticAt_id.pow 2).mul hU
  have hshift : AnalyticAt ℂ shift chapterVIDCollisionLift := by
    exact (analyticAt_chapterVIDRootToOriginalContour
      chapterVIDCollisionLift_ne_zero).sub analyticAt_const
  have hshiftBase : shift chapterVIDCollisionLift = 0 := by
    apply sub_eq_zero.mpr
    rfl
  have hqFirst : deriv q 0 = 0 := by
    change deriv ((fun s : ℂ ↦ s ^ 2) * U) 0 = 0
    rw [deriv_mul (hasDerivAt_pow 2 (0 : ℂ)).differentiableAt
      hU.differentiableAt, (hasDerivAt_pow 2 (0 : ℂ)).deriv]
    norm_num
  have heq : chapterVIDRootCoordinateRadicand chapterVIDZRootBase =ᶠ[
      nhds chapterVIDCollisionLift] q ∘ shift := by
    simpa only [q, U, shift, Function.comp_def] using
      eventually_chapterVIDRootCoordinateRadicand_eq_fiberUnit_comp
  calc
    deriv (deriv (chapterVIDRootCoordinateRadicand chapterVIDZRootBase))
        chapterVIDCollisionLift =
        deriv (deriv (q ∘ shift)) chapterVIDCollisionLift :=
      (heq.deriv).deriv_eq
    _ = deriv (deriv q) (shift chapterVIDCollisionLift) *
        (deriv shift chapterVIDCollisionLift) ^ 2 :=
      chapterVI_secondDeriv_comp_of_first_zero
        (by simpa only [hshiftBase] using hq) hshift
        (by simpa only [hshiftBase] using hqFirst)
    _ = _ := by
      rw [hshiftBase]
      have hqSecond : deriv (deriv q) 0 = 2 * U 0 := by
        simpa only [q] using chapterVI_secondDeriv_sq_mul U hU
      have hderivShift : deriv shift chapterVIDCollisionLift =
          deriv chapterVIDRootToOriginalContour chapterVIDCollisionLift := by
        unfold shift
        rw [deriv_sub_const]
      rw [hqSecond, hderivShift]

theorem chapterVIDCenteredFiberUnit_base_re_neg :
    (chapterVIDCenteredFiberUnit 0).re < 0 := by
  let d := deriv chapterVIDRootToOriginalContour chapterVIDCollisionLift
  have hdre : 0 < d.re := by
    exact deriv_chapterVIDRootToOriginalContour_collision_re_pos
  have hdim : d.im = 0 := by
    exact deriv_chapterVIDRootToOriginalContour_collision_im
  have hdreal : d = (d.re : ℂ) := by
    apply Complex.ext
    · simp
    · simpa only [Complex.ofReal_im] using hdim
  have heq := chapterVIDRootCoordinateRadicandSecondDerivative_eq_fiberUnit
  change deriv (deriv (chapterVIDRootCoordinateRadicand chapterVIDZRootBase))
      chapterVIDCollisionLift = (2 * chapterVIDCenteredFiberUnit 0) * d ^ 2 at heq
  rw [hdreal] at heq
  have hpow : ((d.re : ℂ) ^ 2) = ((d.re ^ 2 : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hpow] at heq
  have hre := congrArg Complex.re heq
  have hrhs : ((2 * chapterVIDCenteredFiberUnit 0) *
      ((d.re ^ 2 : ℝ) : ℂ)).re =
      2 * (chapterVIDCenteredFiberUnit 0).re * d.re ^ 2 := by
    rw [Complex.mul_re]
    have hrecast : (((d.re ^ 2 : ℝ) : ℂ)).re = d.re ^ 2 :=
      Complex.ofReal_re _
    have himcast : (((d.re ^ 2 : ℝ) : ℂ)).im = 0 :=
      Complex.ofReal_im _
    rw [hrecast, himcast]
    norm_num [Complex.mul_re]
  rw [hrhs] at hre
  have hroot := chapterVIDRootCoordinateRadicandSecondDerivative_base_re_neg
  nlinarith [sq_pos_of_pos hdre]

theorem chapterVIDCenteredFiberUnit_base_im :
    (chapterVIDCenteredFiberUnit 0).im = 0 := by
  let d := deriv chapterVIDRootToOriginalContour chapterVIDCollisionLift
  have hdre : 0 < d.re := by
    exact deriv_chapterVIDRootToOriginalContour_collision_re_pos
  have hdim : d.im = 0 := by
    exact deriv_chapterVIDRootToOriginalContour_collision_im
  have hdreal : d = (d.re : ℂ) := by
    apply Complex.ext
    · simp
    · simpa only [Complex.ofReal_im] using hdim
  have heq := chapterVIDRootCoordinateRadicandSecondDerivative_eq_fiberUnit
  change deriv (deriv (chapterVIDRootCoordinateRadicand chapterVIDZRootBase))
      chapterVIDCollisionLift = (2 * chapterVIDCenteredFiberUnit 0) * d ^ 2 at heq
  rw [hdreal] at heq
  have hpow : ((d.re : ℂ) ^ 2) = ((d.re ^ 2 : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hpow] at heq
  have him := congrArg Complex.im heq
  have hrhs : ((2 * chapterVIDCenteredFiberUnit 0) *
      ((d.re ^ 2 : ℝ) : ℂ)).im =
      2 * (chapterVIDCenteredFiberUnit 0).im * d.re ^ 2 := by
    rw [Complex.mul_im]
    have hrecast : (((d.re ^ 2 : ℝ) : ℂ)).re = d.re ^ 2 :=
      Complex.ofReal_re _
    have himcast : (((d.re ^ 2 : ℝ) : ℂ)).im = 0 :=
      Complex.ofReal_im _
    rw [hrecast, himcast]
    norm_num [Complex.mul_im]
  rw [hrhs] at him
  have hroot := chapterVIDRootCoordinateRadicandSecondDerivative_base_im_zero
  rw [hroot] at him
  have hsquare : d.re ^ 2 ≠ 0 := (sq_pos_of_pos hdre).ne'
  have htwoSquare : (2 : ℝ) * d.re ^ 2 ≠ 0 :=
    mul_ne_zero (by norm_num) hsquare
  apply (mul_eq_zero.mp ?_).resolve_right htwoSquare
  nlinarith [him]

theorem chapterVIDPreparedUnit_base_eq_fiberUnit :
    chapterVIDCenteredConvergentPreparedGerm.unit (chapterVIDZBase, 0) =
      chapterVIDCenteredFiberUnit 0 :=
  eventually_chapterVIDCenteredPreparedUnit_eq_fiberUnit.self_of_nhds

theorem chapterVIDPreparedUnit_base_re_neg :
    (chapterVIDCenteredConvergentPreparedGerm.unit
      (chapterVIDZBase, 0)).re < 0 := by
  rw [chapterVIDPreparedUnit_base_eq_fiberUnit]
  exact chapterVIDCenteredFiberUnit_base_re_neg

theorem chapterVIDPreparedUnit_base_im :
    (chapterVIDCenteredConvergentPreparedGerm.unit
      (chapterVIDZBase, 0)).im = 0 := by
  rw [chapterVIDPreparedUnit_base_eq_fiberUnit]
  exact chapterVIDCenteredFiberUnit_base_im

/-! ## Phase selected by the prepared-unit square root -/

theorem chapterVIDMorseRootBase_eq_I_mul_sqrt_neg_unit
    (hneg : (chapterVIDCenteredConvergentPreparedGerm.unit
      (chapterVIDZBase, 0)).re < 0)
    (him : (chapterVIDCenteredConvergentPreparedGerm.unit
      (chapterVIDZBase, 0)).im = 0) :
    chapterVIDMorseRootBase = Complex.I * Complex.sqrt
      (-chapterVIDCenteredConvergentPreparedGerm.unit (chapterVIDZBase, 0)) := by
  have hnot : chapterVIDCenteredConvergentPreparedGerm.unit
      (chapterVIDZBase, 0) ∉ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    intro h
    rcases h with hre | him'
    · exact (not_lt_of_ge hneg.le) hre
    · exact him' him
  unfold chapterVIDMorseRootBase ChapterVIConvergentPreparedGerm.unitRootGerm
  simp [ChapterVIHolomorphicSquareRootGerm.of_analyticAt, hnot]

theorem chapterVIDMorseRootBase_im_pos_of_unit_neg
    (hneg : (chapterVIDCenteredConvergentPreparedGerm.unit
      (chapterVIDZBase, 0)).re < 0)
    (him : (chapterVIDCenteredConvergentPreparedGerm.unit
      (chapterVIDZBase, 0)).im = 0) :
    0 < chapterVIDMorseRootBase.im := by
  rw [chapterVIDMorseRootBase_eq_I_mul_sqrt_neg_unit hneg him,
    Complex.mul_im]
  simp only [Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add]
  let unit := chapterVIDCenteredConvergentPreparedGerm.unit (chapterVIDZBase, 0)
  have hminus : -unit = ((-unit.re : ℝ) : ℂ) := by
    apply Complex.ext
    · simp
    · simp [him, unit]
  rw [hminus, Complex.re_sqrt_ofReal]
  exact Real.sqrt_pos.2 (by dsimp [unit]; linarith)

theorem chapterVIDMorseRootBase_re_zero_of_unit_neg
    (hneg : (chapterVIDCenteredConvergentPreparedGerm.unit
      (chapterVIDZBase, 0)).re < 0)
    (him : (chapterVIDCenteredConvergentPreparedGerm.unit
      (chapterVIDZBase, 0)).im = 0) :
    chapterVIDMorseRootBase.re = 0 := by
  rw [chapterVIDMorseRootBase_eq_I_mul_sqrt_neg_unit hneg him,
    Complex.mul_re]
  simp only [Complex.I_re, Complex.I_im, zero_mul, zero_sub]
  let unit := chapterVIDCenteredConvergentPreparedGerm.unit (chapterVIDZBase, 0)
  have hmem : -unit ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    left
    simpa [unit] using neg_pos.mpr hneg
  have hsquare : Complex.sqrt (-unit) ^ 2 = -unit :=
    Complex.sq_sqrt_of_mem_slitPlane hmem
  have hsqrtRe : 0 < (Complex.sqrt (-unit)).re := by
    have hroot := chapterVIDMorseRootBase_im_pos_of_unit_neg hneg him
    rw [chapterVIDMorseRootBase_eq_I_mul_sqrt_neg_unit hneg him,
      Complex.mul_im] at hroot
    simpa using hroot
  have hsquareIm := congrArg Complex.im hsquare
  simp only [pow_two, Complex.mul_im, Complex.neg_im] at hsquareIm
  rw [show unit.im = 0 by exact him] at hsquareIm
  have hsqrtIm : (Complex.sqrt (-unit)).im = 0 := by
    nlinarith
  rw [hsqrtIm]
  simp

theorem deriv_chapterVIDGlobalMorseFiberCoordinate_re_zero_of_unit_neg
    (hneg : (chapterVIDCenteredConvergentPreparedGerm.unit
      (chapterVIDZBase, 0)).re < 0)
    (him : (chapterVIDCenteredConvergentPreparedGerm.unit
      (chapterVIDZBase, 0)).im = 0) :
    (deriv chapterVIDGlobalMorseFiberCoordinate chapterVIDCollisionLift).re = 0 := by
  rw [deriv_chapterVIDGlobalMorseFiberCoordinate,
    deriv_chapterVIDDeckedRootToLocalContour_collision, Complex.mul_re,
    deriv_chapterVIDRootToOriginalContour_collision_im,
    chapterVIDMorseRootBase_re_zero_of_unit_neg hneg him]
  ring

theorem deriv_chapterVIDGlobalMorseFiberCoordinate_im_pos_of_unit_neg
    (hneg : (chapterVIDCenteredConvergentPreparedGerm.unit
      (chapterVIDZBase, 0)).re < 0)
    (him : (chapterVIDCenteredConvergentPreparedGerm.unit
      (chapterVIDZBase, 0)).im = 0) :
    0 < (deriv chapterVIDGlobalMorseFiberCoordinate chapterVIDCollisionLift).im := by
  rw [deriv_chapterVIDGlobalMorseFiberCoordinate,
    deriv_chapterVIDDeckedRootToLocalContour_collision, Complex.mul_im,
    deriv_chapterVIDRootToOriginalContour_collision_im]
  simp only [zero_mul, add_zero]
  exact mul_pos deriv_chapterVIDRootToOriginalContour_collision_re_pos
    (chapterVIDMorseRootBase_im_pos_of_unit_neg hneg him)

/-- Conditional on the prepared unit's exact negative-real phase, increasing the Morse
coordinate moves the global contour downward from D. -/
theorem deriv_chapterVIDGlobalContourFromMorse_re_zero_of_unit_neg
    (hneg : (chapterVIDCenteredConvergentPreparedGerm.unit
      (chapterVIDZBase, 0)).re < 0)
    (him : (chapterVIDCenteredConvergentPreparedGerm.unit
      (chapterVIDZBase, 0)).im = 0) :
    (deriv chapterVIDGlobalContourFromMorse 0).re = 0 := by
  rw [deriv_chapterVIDGlobalContourFromMorse, Complex.inv_re,
    deriv_chapterVIDGlobalMorseFiberCoordinate_re_zero_of_unit_neg hneg him]
  simp

theorem deriv_chapterVIDGlobalContourFromMorse_im_neg_of_unit_neg
    (hneg : (chapterVIDCenteredConvergentPreparedGerm.unit
      (chapterVIDZBase, 0)).re < 0)
    (him : (chapterVIDCenteredConvergentPreparedGerm.unit
      (chapterVIDZBase, 0)).im = 0) :
    (deriv chapterVIDGlobalContourFromMorse 0).im < 0 := by
  rw [deriv_chapterVIDGlobalContourFromMorse, Complex.inv_im]
  have hforward :=
    deriv_chapterVIDGlobalMorseFiberCoordinate_im_pos_of_unit_neg hneg him
  have hnorm : 0 < Complex.normSq
      (deriv chapterVIDGlobalMorseFiberCoordinate chapterVIDCollisionLift) :=
    Complex.normSq_pos.mpr deriv_chapterVIDGlobalMorseFiberCoordinate_ne_zero
  exact div_neg_of_neg_of_pos (neg_neg_of_pos hforward) hnorm

/-! The certificate-backed unit phase discharges the hypotheses above, so the endpoint
orientation is now unconditional. -/

theorem chapterVIDMorseRootBase_im_pos :
    0 < chapterVIDMorseRootBase.im :=
  chapterVIDMorseRootBase_im_pos_of_unit_neg
    chapterVIDPreparedUnit_base_re_neg chapterVIDPreparedUnit_base_im

theorem chapterVIDMorseRootBase_re_zero :
    chapterVIDMorseRootBase.re = 0 :=
  chapterVIDMorseRootBase_re_zero_of_unit_neg
    chapterVIDPreparedUnit_base_re_neg chapterVIDPreparedUnit_base_im

theorem deriv_chapterVIDGlobalMorseFiberCoordinate_re_zero :
    (deriv chapterVIDGlobalMorseFiberCoordinate chapterVIDCollisionLift).re = 0 :=
  deriv_chapterVIDGlobalMorseFiberCoordinate_re_zero_of_unit_neg
    chapterVIDPreparedUnit_base_re_neg chapterVIDPreparedUnit_base_im

theorem deriv_chapterVIDGlobalMorseFiberCoordinate_im_pos :
    0 < (deriv chapterVIDGlobalMorseFiberCoordinate chapterVIDCollisionLift).im :=
  deriv_chapterVIDGlobalMorseFiberCoordinate_im_pos_of_unit_neg
    chapterVIDPreparedUnit_base_re_neg chapterVIDPreparedUnit_base_im

theorem deriv_chapterVIDGlobalContourFromMorse_re_zero :
    (deriv chapterVIDGlobalContourFromMorse 0).re = 0 :=
  deriv_chapterVIDGlobalContourFromMorse_re_zero_of_unit_neg
    chapterVIDPreparedUnit_base_re_neg chapterVIDPreparedUnit_base_im

theorem deriv_chapterVIDGlobalContourFromMorse_im_neg :
    (deriv chapterVIDGlobalContourFromMorse 0).im < 0 :=
  deriv_chapterVIDGlobalContourFromMorse_im_neg_of_unit_neg
    chapterVIDPreparedUnit_base_re_neg chapterVIDPreparedUnit_base_im

/-! ## Uniform propagation on a shrunken compact Morse rectangle -/

/-- The inverse parametric Morse map fixes the zero section near D. -/
theorem eventually_chapterVIDMorseFiberInverse_axis_eq_zero :
    ∀ᶠ z : ℂ in nhds chapterVIDZBase,
      chapterVIDMorseFiberInverse (z, 0) = 0 := by
  have htend : Tendsto (fun z : ℂ ↦ (z, (0 : ℂ)))
      (nhds chapterVIDZBase) (nhds (chapterVIDZBase, 0)) :=
    continuousAt_id.prodMk continuousAt_const
  filter_upwards [htend.eventually eventually_chapterVIDMorseInverse_left] with z hz
  have hsnd := congrArg Prod.snd hz
  simpa [chapterVIDMorseMap, chapterVIDMorseFiberInverse] using hsnd

/-- Consequently the zero Morse coordinate reconstructs the moving critical center itself. -/
theorem eventually_chapterVIDMorseSourcePoint_axis_eq_center :
    ∀ᶠ z : ℂ in nhds chapterVIDZBase,
      (chapterVIDMorseSourcePoint (z, 0)).2 = chapterVIDCriticalCenter z := by
  filter_upwards [eventually_chapterVIDMorseFiberInverse_axis_eq_zero] with z hz
  simp [chapterVIDMorseSourcePoint, hz]

theorem eventually_chapterVIDCriticalMorseRootPoint_zero_eq_globalContour :
    (fun v : ℂ ↦ chapterVIDCriticalMorseRootPoint (0, v)) =ᶠ[nhds 0]
      chapterVIDGlobalContourFromMorse := by
  have htend : Tendsto chapterVIDGlobalContourFromMorse
      (nhds 0) (nhds chapterVIDCollisionLift) := by
    rw [← chapterVIDGlobalContourFromMorse_zero]
    exact analyticAt_chapterVIDGlobalContourFromMorse.continuousAt
  have hleft := htend.eventually
    eventually_chapterVIDOriginalContourToRoot_rootToOriginalContour
  filter_upwards [eventually_chapterVIDGlobalSourceContourFromMorse_eq_morseSourcePoint,
    hleft] with v hsource hleftv
  have hsnd := congrArg Prod.snd hsource
  unfold chapterVIDCriticalMorseRootPoint chapterVIDCriticalMorseSourcePointAtD
    chapterVIDCriticalMorseSourcePoint chapterVIDCriticalMorseParameterMap
  simp only [chapterVIDCriticalParameterInverse_zero]
  change chapterVIDOriginalContourToRoot
      (chapterVIDMorseSourcePoint (chapterVIDZBase, v)).2 = _
  rw [← hsnd]
  simp only [chapterVIDGlobalSourceContourFromMorse_eq]
  exact hleftv

theorem chapterVIDCriticalMorseRootFiberDerivative_base :
    chapterVIFiberDerivative chapterVIDCriticalMorseRootPoint (0, 0) =
      deriv chapterVIDGlobalContourFromMorse 0 := by
  rw [chapterVIFiberDerivative_eq_deriv
    analyticAt_chapterVIDCriticalMorseRootPoint]
  exact eventually_chapterVIDCriticalMorseRootPoint_zero_eq_globalContour.deriv_eq

theorem chapterVIDCriticalMorseRootFiberDerivative_base_im_neg :
    (chapterVIFiberDerivative chapterVIDCriticalMorseRootPoint (0, 0)).im < 0 := by
  rw [chapterVIDCriticalMorseRootFiberDerivative_base]
  exact deriv_chapterVIDGlobalContourFromMorse_im_neg

theorem eventually_chapterVIDCriticalMorseRootFiberDerivative_im_neg :
    ∀ᶠ point : ℂ × ℂ in nhds (0, 0),
      (chapterVIFiberDerivative chapterVIDCriticalMorseRootPoint point).im < 0 := by
  have hanalytic := analyticAt_chapterVIFiberDerivative
    analyticAt_chapterVIDCriticalMorseRootPoint
  have hcont : ContinuousAt
      (fun point : ℂ × ℂ ↦
        (chapterVIFiberDerivative chapterVIDCriticalMorseRootPoint point).im)
      (0, 0) :=
    Complex.continuous_im.continuousAt.comp_of_eq hanalytic.continuousAt rfl
  exact hcont.eventually (Iio_mem_nhds
    chapterVIDCriticalMorseRootFiberDerivative_base_im_neg)

/-- Along the real critical-value axis, the zero Morse coordinate maps to the real root axis
near D. This identifies the zero section that separates the upper and lower local branches. -/
theorem eventually_chapterVIDCriticalMorseRootPoint_center_im_zero :
    ∀ᶠ k : ℝ in nhds 0,
      (chapterVIDCriticalMorseRootPoint ((k : ℂ), 0)).im = 0 := by
  let z : ℝ → ℂ := fun k ↦ chapterVIDCriticalParameterInverseAtD (k : ℂ)
  let center : ℝ → ℂ := fun k ↦ chapterVIDCriticalCenter (z k)
  have hzTend : Tendsto z (nhds 0) (nhds chapterVIDZBase) := by
    change Tendsto (chapterVIDCriticalParameterInverseAtD ∘
      fun k : ℝ ↦ (k : ℂ)) _ _
    have hreal : Tendsto (fun k : ℝ ↦ (k : ℂ)) (nhds 0) (nhds (0 : ℂ)) :=
      Complex.continuous_ofReal.continuousAt
    have hinv :=
      analyticAt_chapterVIDCriticalParameterInverseAtD.continuousAt.tendsto.comp hreal
    simpa only [chapterVIDCriticalParameterInverseAtD_zero] using hinv
  have hcenterTend : Tendsto center (nhds 0) (nhds chapterVIDTBase) := by
    change Tendsto (chapterVIDCriticalCenter ∘ z) _ _
    have h := analyticAt_chapterVIDCriticalCenter.continuousAt.tendsto.comp hzTend
    simpa only [chapterVIDCriticalCenter_base] using h
  have hcenterReTend : Tendsto (fun k ↦ (center k).re)
      (nhds 0) (nhds chapterVIDTBase.re) :=
    Complex.continuous_re.continuousAt.tendsto.comp hcenterTend
  have hrootReal := hcenterReTend.eventually
    eventually_chapterVIDOriginalContourToRoot_ofReal_im_eq_zero
  have hzReal := eventually_chapterVIDCriticalParameterInverseAtD_im_eq_zero
  have hcenterConj := hzTend.eventually eventually_chapterVIDCriticalCenter_conj
  have haxis := hzTend.eventually eventually_chapterVIDMorseSourcePoint_axis_eq_center
  filter_upwards [hzReal, hcenterConj, haxis, hrootReal] with
      k hzk hconj haxisK hroot
  have hzConj : conj (z k) = z k := by
    apply Complex.ext
    · simp
    · simp [z, hzk]
  have hcenterIm : (center k).im = 0 := by
    have hsymm : conj (center k) = center k := by
      rw [← hconj, hzConj]
    exact Complex.conj_eq_iff_im.mp hsymm
  have hcenterEq : ((center k).re : ℂ) = center k := by
    apply Complex.ext
    · simp
    · simpa only [Complex.ofReal_im] using hcenterIm.symm
  unfold chapterVIDCriticalMorseRootPoint chapterVIDCriticalMorseSourcePointAtD
    chapterVIDCriticalMorseSourcePoint chapterVIDCriticalMorseParameterMap
  change (chapterVIDOriginalContourToRoot
    (chapterVIDMorseSourcePoint (z k, 0)).2).im = 0
  rw [haxisK]
  change (chapterVIDOriginalContourToRoot (center k)).im = 0
  rw [← hcenterEq]
  exact hroot

/-- A compact global root model on which increasing the real Morse coordinate moves the actual
root coordinate strictly downward throughout the selected rectangle. -/
structure ChapterVIDOrientedGlobalRootModel
    (massProduct : ℂ) (b d : ℤ)
    extends ChapterVIDPrincipalGlobalRootModel massProduct b d where
  rootFiberDerivative_im_neg : ∀ k ∈ Set.Icc 0 δ, ∀ v ∈ Set.uIcc (-L) L,
    (chapterVIFiberDerivative chapterVIDCriticalMorseRootPoint
      ((k : ℂ), (v : ℂ))).im < 0
  rootCenter_im_zero : ∀ k ∈ Set.Icc 0 δ,
    (chapterVIDCriticalMorseRootPoint ((k : ℂ), 0)).im = 0

/-- The strict base-point phase can be imposed uniformly by shrinking the compact model. -/
theorem exists_chapterVIDOrientedGlobalRootModel
    (massProduct : ℂ) (b d : ℤ) :
    Nonempty (ChapterVIDOrientedGlobalRootModel massProduct b d) := by
  obtain ⟨model⟩ := exists_chapterVIDPrincipalGlobalRootModel massProduct b d
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp
    eventually_chapterVIDCriticalMorseRootFiberDerivative_im_neg
  obtain ⟨η, hη, hrealBall⟩ := Metric.mem_nhds_iff.mp
    eventually_chapterVIDCriticalMorseRootPoint_center_im_zero
  let r := min (min model.δ model.L) (min (ε / 2) (η / 2))
  have hr : 0 < r := by
    dsimp [r]
    exact lt_min (lt_min model.δ_pos model.L_pos)
      (lt_min (by positivity) (by positivity))
  have hrδ : r ≤ model.δ := by
    exact (min_le_left (min model.δ model.L) (min (ε / 2) (η / 2))).trans
      (min_le_left model.δ model.L)
  have hrL : r ≤ model.L := by
    exact (min_le_left (min model.δ model.L) (min (ε / 2) (η / 2))).trans
      (min_le_right model.δ model.L)
  have hrε : r ≤ ε / 2 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hrη : r ≤ η / 2 :=
    (min_le_right _ _).trans (min_le_right _ _)
  let restricted := model.restrict r r hr hr hrδ hrL
  refine ⟨{
    toChapterVIDPrincipalGlobalRootModel := restricted
    rootFiberDerivative_im_neg := ?_
    rootCenter_im_zero := ?_ }⟩
  intro k hk v hv
  change k ∈ Set.Icc 0 r at hk
  change v ∈ Set.uIcc (-r) r at hv
  apply hball
  rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
  simp only [Complex.dist_eq, sub_zero, Complex.norm_real, Real.norm_eq_abs]
  rw [Set.uIcc_of_le (by linarith [hr])] at hv
  constructor
  · rw [abs_of_nonneg hk.1]
    linarith [hk.2, hrε]
  · rw [abs_lt]
    constructor <;> linarith [hv.1, hv.2, hrε]
  intro k hk
  change k ∈ Set.Icc 0 r at hk
  apply hrealBall
  rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg hk.1]
  linarith [hk.2, hrη]

/-- A connector model retaining the strict inverse-Morse orientation on its complete root
rectangle. -/
structure ChapterVIDOrientedConnectorModel
    (massProduct : ℂ) (b d : ℤ)
    extends ChapterVIDPrincipalConnectorModel massProduct b d where
  rootFiberDerivative_im_neg :
    ∀ k ∈ Set.Icc 0 rootModel.δ, ∀ v ∈ Set.uIcc (-rootModel.L) rootModel.L,
      (chapterVIFiberDerivative chapterVIDCriticalMorseRootPoint
        ((k : ℂ), (v : ℂ))).im < 0
  rootCenter_im_zero : ∀ k ∈ Set.Icc 0 rootModel.δ,
    (chapterVIDCriticalMorseRootPoint ((k : ℂ), 0)).im = 0

/-- The branch-agreement interval can be chosen after the oriented root rectangle, so both the
compiled global sheet and the strict local phase hold in one connector model. -/
theorem exists_chapterVIDOrientedConnectorModel
    (massProduct : ℂ) (b d : ℤ) :
    Nonempty (ChapterVIDOrientedConnectorModel massProduct b d) := by
  obtain ⟨orientedRoot⟩ :=
    exists_chapterVIDOrientedGlobalRootModel massProduct b d
  obtain ⟨connector, hroot⟩ :=
    exists_chapterVIDPrincipalConnectorModel_of_rootModel
      orientedRoot.toChapterVIDPrincipalGlobalRootModel
  refine ⟨{
    toChapterVIDPrincipalConnectorModel := connector
    rootFiberDerivative_im_neg := ?_
    rootCenter_im_zero := ?_ }⟩
  intro k hk v hv
  rw [hroot] at hk hv
  exact orientedRoot.rootFiberDerivative_im_neg k hk v hv
  intro k hk
  rw [hroot] at hk
  exact orientedRoot.rootCenter_im_zero k hk

/-- Imaginary part of the actual inverse-Morse root coordinate on a real fiber. -/
def ChapterVIDOrientedConnectorModel.rootFiberImag
    {massProduct : ℂ} {b d : ℤ}
    (_model : ChapterVIDOrientedConnectorModel massProduct b d)
    (k v : ℝ) : ℝ :=
  (chapterVIDCriticalMorseRootPoint ((k : ℂ), (v : ℂ))).im

/-- The named two-variable fiber derivative is the real derivative of the root coordinate's
imaginary part. -/
theorem ChapterVIDOrientedConnectorModel.hasDerivAt_rootFiberImag
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDOrientedConnectorModel massProduct b d)
    {k v : ℝ}
    (hk : k ∈ Set.Icc 0 model.rootModel.δ)
    (hv : v ∈ Set.uIcc (-model.rootModel.L) model.rootModel.L) :
    HasDerivAt (model.rootFiberImag k)
      (chapterVIFiberDerivative chapterVIDCriticalMorseRootPoint
        ((k : ℂ), (v : ℂ))).im v := by
  have hpoint := model.rootModel.root_analyticAt k hk v hv
  have hfiber : AnalyticAt ℂ
      (fun w : ℂ ↦ chapterVIDCriticalMorseRootPoint ((k : ℂ), w)) (v : ℂ) :=
    hpoint.comp (analyticAt_const.prod analyticAt_id)
  have hcomplex : HasDerivAt
      (fun w : ℂ ↦ chapterVIDCriticalMorseRootPoint ((k : ℂ), w))
      (chapterVIFiberDerivative chapterVIDCriticalMorseRootPoint
        ((k : ℂ), (v : ℂ))) (v : ℂ) := by
    rw [chapterVIFiberDerivative_eq_deriv hpoint]
    exact hfiber.differentiableAt.hasDerivAt
  have hreal := (hcomplex.const_mul (-Complex.I)).real_of_complex
  convert hreal using 1
  · funext x
    simp [ChapterVIDOrientedConnectorModel.rootFiberImag, Complex.mul_re]
  · simp [Complex.mul_re]

/-- Uniform phase propagation: on every selected real parameter fiber, increasing the Morse
coordinate strictly lowers the imaginary part of the actual global root coordinate. -/
theorem ChapterVIDOrientedConnectorModel.strictAntiOn_rootFiberImag
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDOrientedConnectorModel massProduct b d)
    {k : ℝ} (hk : k ∈ Set.Icc 0 model.κ) :
    StrictAntiOn (model.rootFiberImag k)
      (Set.Icc (-model.rootModel.L) model.rootModel.L) := by
  have hkRoot : k ∈ Set.Icc 0 model.rootModel.δ :=
    ⟨hk.1, hk.2.trans model.κ_le_delta⟩
  have hinterval : -model.rootModel.L ≤ model.rootModel.L := by
    linarith [model.rootModel.L_pos]
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
  · intro v hv
    have hvU : v ∈ Set.uIcc (-model.rootModel.L) model.rootModel.L := by
      rw [Set.uIcc_of_le hinterval]
      exact hv
    exact (model.hasDerivAt_rootFiberImag hkRoot hvU).continuousAt.continuousWithinAt
  · intro v hv
    have hv' : v ∈ Set.Icc (-model.rootModel.L) model.rootModel.L :=
      interior_subset hv
    have hvU : v ∈ Set.uIcc (-model.rootModel.L) model.rootModel.L := by
      rw [Set.uIcc_of_le hinterval]
      exact hv'
    rw [(model.hasDerivAt_rootFiberImag hkRoot hvU).deriv]
    exact model.rootFiberDerivative_im_neg k hkRoot v hvU

/-- The two local connector endpoints inherit the strict vertical ordering selected at D. -/
theorem ChapterVIDOrientedConnectorModel.initial_endpoint_im_gt_final
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDOrientedConnectorModel massProduct b d)
    {k : ℝ} (hk : k ∈ Set.Icc 0 model.κ) :
    (model.rootModel.localConnectorEndpoint .final k).im <
      (model.rootModel.localConnectorEndpoint .initial k).im := by
  have hL : -model.rootModel.L < model.rootModel.L := by
    linarith [model.rootModel.L_pos]
  have hanti := model.strictAntiOn_rootFiberImag hk
  have h := hanti
    (Set.left_mem_Icc.mpr hL.le) (Set.right_mem_Icc.mpr hL.le) hL
  simpa [ChapterVIDOrientedConnectorModel.rootFiberImag,
    ChapterVIDPrincipalGlobalRootModel.localConnectorEndpoint] using h

/-- The initial local endpoint lies strictly above the real root axis. -/
theorem ChapterVIDOrientedConnectorModel.initial_endpoint_im_pos
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDOrientedConnectorModel massProduct b d)
    {k : ℝ} (hk : k ∈ Set.Icc 0 model.κ) :
    0 < (model.rootModel.localConnectorEndpoint .initial k).im := by
  have hkRoot : k ∈ Set.Icc 0 model.rootModel.δ :=
    ⟨hk.1, hk.2.trans model.κ_le_delta⟩
  have hminus : -model.rootModel.L < 0 := by
    linarith [model.rootModel.L_pos]
  have hL : -model.rootModel.L ≤ model.rootModel.L := hminus.le.trans
    model.rootModel.L_pos.le
  have hanti := model.strictAntiOn_rootFiberImag hk
  have h := hanti (Set.left_mem_Icc.mpr hL)
    (Set.mem_Icc.mpr ⟨hminus.le, model.rootModel.L_pos.le⟩) hminus
  change (chapterVIDCriticalMorseRootPoint ((k : ℂ), 0)).im <
    (chapterVIDCriticalMorseRootPoint
      ((k : ℂ), ((-model.rootModel.L : ℝ) : ℂ))).im at h
  rw [model.rootCenter_im_zero k hkRoot] at h
  simpa [ChapterVIDOrientedConnectorModel.rootFiberImag,
    ChapterVIDPrincipalGlobalRootModel.localConnectorEndpoint] using h

/-- The final local endpoint lies strictly below the real root axis. -/
theorem ChapterVIDOrientedConnectorModel.final_endpoint_im_neg
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDOrientedConnectorModel massProduct b d)
    {k : ℝ} (hk : k ∈ Set.Icc 0 model.κ) :
    (model.rootModel.localConnectorEndpoint .final k).im < 0 := by
  have hkRoot : k ∈ Set.Icc 0 model.rootModel.δ :=
    ⟨hk.1, hk.2.trans model.κ_le_delta⟩
  have hplus : 0 < model.rootModel.L := model.rootModel.L_pos
  have hL : -model.rootModel.L ≤ model.rootModel.L := by linarith
  have hanti := model.strictAntiOn_rootFiberImag hk
  have h := hanti (Set.mem_Icc.mpr ⟨by linarith, hplus.le⟩)
    (Set.right_mem_Icc.mpr hL) hplus
  change (chapterVIDCriticalMorseRootPoint
      ((k : ℂ), ((model.rootModel.L : ℝ) : ℂ))).im <
    (chapterVIDCriticalMorseRootPoint ((k : ℂ), 0)).im at h
  rw [model.rootCenter_im_zero k hkRoot] at h
  simpa [ChapterVIDOrientedConnectorModel.rootFiberImag,
    ChapterVIDPrincipalGlobalRootModel.localConnectorEndpoint] using h

end PoincareChapterVI
