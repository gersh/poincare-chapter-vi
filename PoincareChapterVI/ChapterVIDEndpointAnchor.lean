/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.ChapterVIDEndpointOrientation

/-!
# Endpoint anchors for the compiled terminal connector campaign

The inverse-Morse phase determines the first nonzero variation of both components of the literal
collision-factor path derivative at D. Its imaginary component is positive on both connectors;
its real component is negative on the initial connector and positive on the final connector. We
select a small positive Morse length, then shrink the critical-value interval by continuity. The
resulting connector supplies all endpoint anchors used by the compiled curvature campaigns.
-/

noncomputable section
open Complex Filter Set
open scoped unitInterval
namespace PoincareChapterVI

/-- Analyticity of the inverse-Morse root supplies a quantitative linear bound near the
collision.  The constant remains internal: the selector below converts it into any requested
dyadic endpoint radius before data reaches the finite certificate. -/
theorem eventually_norm_chapterVIDCriticalMorseRootPoint_sub_collision_le :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ point : ℂ × ℂ in nhds (0, 0),
      ‖chapterVIDCriticalMorseRootPoint point - chapterVIDCollisionLift‖ ≤
        C * ‖point‖ := by
  have hbig :=
    analyticAt_chapterVIDCriticalMorseRootPoint.differentiableAt.isBigO_sub
  obtain ⟨C, hC⟩ := hbig.bound
  refine ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  filter_upwards [hC] with point hpoint
  have hzero : ((0, 0) : ℂ × ℂ) = 0 := rfl
  rw [hzero, sub_zero] at hpoint
  have hpoint' :
      ‖chapterVIDCriticalMorseRootPoint point - chapterVIDCollisionLift‖ ≤
        C * ‖point‖ := by
    have hrootZero : chapterVIDCriticalMorseRootPoint (0 : ℂ × ℂ) =
        chapterVIDCollisionLift := by
      simpa only [show (0 : ℂ × ℂ) = (0, 0) from rfl] using
        chapterVIDCriticalMorseRootPoint_base
    rw [hrootZero] at hpoint
    exact hpoint
  exact hpoint'.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg point))

def chapterVIDInitialBaseEndpointDerivative (L : ℝ) : ℝ :=
  (chapterVIDRootCoordinateCollisionFactorPlusDerivative chapterVIDZRootBase
      (chapterVIDCriticalMorseRootPoint (0, ((-L : ℝ) : ℂ))) *
    (chapterVIDCriticalMorseRootPoint (0, ((-L : ℝ) : ℂ)) -
      chapterVIDOuterArcPoint .initial (1, 1))).im

def chapterVIDFinalBaseEndpointDerivative (L : ℝ) : ℝ :=
  (chapterVIDRootCoordinateCollisionFactorPlusDerivative chapterVIDZRootBase
      (chapterVIDCriticalMorseRootPoint (0, (L : ℂ))) *
    (chapterVIDOuterArcPoint .final (1, 0) -
      chapterVIDCriticalMorseRootPoint (0, (L : ℂ)))).im

/-- Real part of the initial affine-path derivative at the inverse-Morse endpoint, with the
critical parameter collapsed to `D`.  Unlike the imaginary anchor above, the required
orientation is negative on the initial connector. -/
def chapterVIDInitialBaseEndpointRealDerivative (L : ℝ) : ℝ :=
  (chapterVIDRootCoordinateCollisionFactorPlusDerivative chapterVIDZRootBase
      (chapterVIDCriticalMorseRootPoint (0, ((-L : ℝ) : ℂ))) *
    (chapterVIDCriticalMorseRootPoint (0, ((-L : ℝ) : ℂ)) -
      chapterVIDOuterArcPoint .initial (1, 1))).re

/-- Real part of the final affine-path derivative at the inverse-Morse endpoint, with the
critical parameter collapsed to `D`.  Its required orientation is positive. -/
def chapterVIDFinalBaseEndpointRealDerivative (L : ℝ) : ℝ :=
  (chapterVIDRootCoordinateCollisionFactorPlusDerivative chapterVIDZRootBase
      (chapterVIDCriticalMorseRootPoint (0, (L : ℂ))) *
    (chapterVIDOuterArcPoint .final (1, 0) -
      chapterVIDCriticalMorseRootPoint (0, (L : ℂ)))).re

theorem hasDerivAt_chapterVIDCriticalMorseRootFiber_zero :
    HasDerivAt (fun v : ℂ ↦ chapterVIDCriticalMorseRootPoint (0, v))
      (deriv chapterVIDGlobalContourFromMorse 0) 0 := by
  have hpoint : AnalyticAt ℂ
      (fun v : ℂ ↦ chapterVIDCriticalMorseRootPoint (0, v)) 0 :=
    analyticAt_chapterVIDCriticalMorseRootPoint.comp
      (analyticAt_const.prod analyticAt_id)
  have h := hpoint.differentiableAt.hasDerivAt
  have heq : deriv (fun v : ℂ ↦ chapterVIDCriticalMorseRootPoint (0, v)) 0 =
      deriv chapterVIDGlobalContourFromMorse 0 := by
    rw [← chapterVIDCriticalMorseRootFiberDerivative_base,
      chapterVIFiberDerivative_eq_deriv
        analyticAt_chapterVIDCriticalMorseRootPoint]
  rw [heq] at h
  exact h

/-- The scale-normalized inverse-Morse displacement converges to its exact complex derivative.
This is the directional information which a terminal interval certificate needs; a norm-only
big-O estimate cannot determine the endpoint sign. -/
theorem tendsto_chapterVIDCriticalMorseRootFiber_normalizedDelta :
    Tendsto
      (fun v : ℂ ↦
        (chapterVIDCriticalMorseRootPoint (0, v) - chapterVIDCollisionLift) / v)
      (nhdsWithin 0 {0}ᶜ)
      (nhds (deriv chapterVIDGlobalContourFromMorse 0)) := by
  have h := hasDerivAt_chapterVIDCriticalMorseRootFiber_zero.tendsto_slope_zero
  simpa only [zero_add, chapterVIDCriticalMorseRootPoint_base, smul_eq_mul,
    div_eq_inv_mul] using h

/-- A concrete open cone around the limiting derivative.  The derivative is purely imaginary
and points downward, so the radius `-Im(d)/2` stays strictly inside the correct half-plane. -/
theorem eventually_chapterVIDCriticalMorseRootFiber_normalizedDelta_mem_directionCone :
    ∀ᶠ v : ℂ in nhdsWithin 0 {0}ᶜ,
      ‖(chapterVIDCriticalMorseRootPoint (0, v) - chapterVIDCollisionLift) / v -
          deriv chapterVIDGlobalContourFromMorse 0‖ <
        -(deriv chapterVIDGlobalContourFromMorse 0).im / 2 := by
  have hradius : 0 < -(deriv chapterVIDGlobalContourFromMorse 0).im / 2 := by
    linarith [deriv_chapterVIDGlobalContourFromMorse_im_neg]
  let U : Set ℂ := {z |
    ‖z - deriv chapterVIDGlobalContourFromMorse 0‖ <
      -(deriv chapterVIDGlobalContourFromMorse 0).im / 2}
  have hU : U ∈ nhds (deriv chapterVIDGlobalContourFromMorse 0) := by
    have hUeq : U = Metric.ball (deriv chapterVIDGlobalContourFromMorse 0)
        (-(deriv chapterVIDGlobalContourFromMorse 0).im / 2) := by
      ext z
      simp only [U, Set.mem_ofPred_eq, Metric.mem_ball, dist_eq_norm]
    rw [hUeq]
    exact Metric.ball_mem_nhds _ hradius
  exact tendsto_chapterVIDCriticalMorseRootFiber_normalizedDelta.eventually hU

theorem eventually_chapterVIDCriticalMorseRootFiber_normalizedDelta_components :
    ∀ᶠ v : ℂ in nhdsWithin 0 {0}ᶜ,
      |((chapterVIDCriticalMorseRootPoint (0, v) - chapterVIDCollisionLift) / v).re| <
          -(deriv chapterVIDGlobalContourFromMorse 0).im / 2 ∧
        ((chapterVIDCriticalMorseRootPoint (0, v) - chapterVIDCollisionLift) / v).im <
          (deriv chapterVIDGlobalContourFromMorse 0).im / 2 := by
  filter_upwards
    [eventually_chapterVIDCriticalMorseRootFiber_normalizedDelta_mem_directionCone]
      with v hv
  let q := (chapterVIDCriticalMorseRootPoint (0, v) - chapterVIDCollisionLift) / v
  let d := deriv chapterVIDGlobalContourFromMorse 0
  have hreNorm : |(q - d).re| < -d.im / 2 :=
    (Complex.abs_re_le_norm (q - d)).trans_lt hv
  have himNorm : |(q - d).im| < -d.im / 2 :=
    (Complex.abs_im_le_norm (q - d)).trans_lt hv
  have hdRe : d.re = 0 := deriv_chapterVIDGlobalContourFromMorse_re_zero
  constructor
  · simpa only [Complex.sub_re, hdRe, sub_zero, q, d] using hreNorm
  · have himUpper := (abs_lt.mp himNorm).2
    dsimp only [q, d] at himUpper
    rw [Complex.sub_im] at himUpper
    linarith

/-- Scale-normalized displacement of either local connector endpoint.  The sign in the
denominator follows the actual Morse coordinate, so both sides converge to the same derivative. -/
def chapterVIDNormalizedLocalEndpointDelta
    (side : ChapterVIDOuterArcSide) (k L : ℝ) : ℂ :=
  match side with
  | .initial =>
      (chapterVIDCriticalMorseRootPoint ((k : ℂ), ((-L : ℝ) : ℂ)) -
        chapterVIDCollisionLift) / ((-L : ℝ) : ℂ)
  | .final =>
      (chapterVIDCriticalMorseRootPoint ((k : ℂ), (L : ℂ)) -
        chapterVIDCollisionLift) / (L : ℂ)

theorem ChapterVIDPrincipalGlobalRootModel.continuousAt_normalizedLocalEndpointDelta_zero
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalGlobalRootModel massProduct b d)
    (side : ChapterVIDOuterArcSide) :
    ContinuousAt
      (fun k : ℝ ↦ chapterVIDNormalizedLocalEndpointDelta side k model.L) 0 := by
  have hk0 : (0 : ℝ) ∈ Set.Icc 0 model.δ := ⟨le_rfl, model.δ_pos.le⟩
  cases side with
  | initial =>
      have hroot := (model.root_analyticAt 0 hk0 (-model.L) Set.left_mem_uIcc).continuousAt
      have hcomp := hroot.comp_of_eq
        (Complex.continuous_ofReal.continuousAt.prodMk continuousAt_const) rfl
      exact (hcomp.sub_const chapterVIDCollisionLift).div_const
        (((-model.L : ℝ) : ℂ))
  | final =>
      have hroot := (model.root_analyticAt 0 hk0 model.L Set.right_mem_uIcc).continuousAt
      have hcomp := hroot.comp_of_eq
        (Complex.continuous_ofReal.continuousAt.prodMk continuousAt_const) rfl
      exact (hcomp.sub_const chapterVIDCollisionLift).div_const (model.L : ℂ)

@[simp] theorem chapterVIDOuterArcPoint_initial_D :
    chapterVIDOuterArcPoint .initial (1, 1) =
      (‖chapterVIDCollisionLift‖ : ℂ) * Complex.I := by
  simp [chapterVIDOuterArcPoint]

@[simp] theorem chapterVIDOuterArcPoint_final_D :
    chapterVIDOuterArcPoint .final (1, 0) =
      -Complex.I * (‖chapterVIDCollisionLift‖ : ℂ) := by
  simp [chapterVIDOuterArcPoint, chapterVIDRationalOuterArcUnit]
  ring

set_option backward.isDefEq.respectTransparency.types false in
theorem hasDerivAt_chapterVIDInitialBaseEndpointDerivative :
    HasDerivAt chapterVIDInitialBaseEndpointDerivative
      ((chapterVIDRootCoordinateCollisionFactorPlusSecondDerivative
          chapterVIDZRootBase chapterVIDCollisionLift *
        (deriv chapterVIDGlobalContourFromMorse 0 * (-1 : ℂ)) *
        (chapterVIDCollisionLift -
          (‖chapterVIDCollisionLift‖ : ℂ) * Complex.I)).im) 0 := by
  let root : ℂ → ℂ := fun w ↦
    chapterVIDCriticalMorseRootPoint (0, (-1 : ℂ) * w)
  have hroot : HasDerivAt root
      (deriv chapterVIDGlobalContourFromMorse 0 * (-1 : ℂ)) 0 := by
    have houter : HasDerivAt
        (fun v : ℂ ↦ chapterVIDCriticalMorseRootPoint (0, v))
        (deriv chapterVIDGlobalContourFromMorse 0) ((-1 : ℂ) * 0) := by
      simpa using hasDerivAt_chapterVIDCriticalMorseRootFiber_zero
    have hinner := (hasDerivAt_id (0 : ℂ)).const_mul (-1 : ℂ)
    have h := houter.comp (0 : ℂ) hinner
    change HasDerivAt
      ((fun v : ℂ ↦ chapterVIDCriticalMorseRootPoint (0, v)) ∘
        fun w : ℂ ↦ (-1 : ℂ) * w) _ _
    simpa only [mul_one] using h
  have hrootZero : root 0 = chapterVIDCollisionLift := by
    simp [root, chapterVIDCriticalMorseRootPoint_base]
  have hfactorAt : HasDerivAt
      (chapterVIDRootCoordinateCollisionFactorPlusDerivative chapterVIDZRootBase)
      (chapterVIDRootCoordinateCollisionFactorPlusSecondDerivative
        chapterVIDZRootBase (root 0)) (root 0) := by
    rw [hrootZero]
    exact hasDerivAt_chapterVIDRootCoordinateCollisionFactorPlusDerivative
      chapterVIDCollisionLift_ne_zero
  have hfactor := hfactorAt.comp 0 hroot
  have hdelta := hroot.sub_const
    ((‖chapterVIDCollisionLift‖ : ℂ) * Complex.I)
  have hprod := hfactor.mul hdelta
  change HasDerivAt
    (fun w : ℂ ↦
      chapterVIDRootCoordinateCollisionFactorPlusDerivative chapterVIDZRootBase
          (root w) *
        (root w - (‖chapterVIDCollisionLift‖ : ℂ) * Complex.I))
    (chapterVIDRootCoordinateCollisionFactorPlusSecondDerivative
          chapterVIDZRootBase (root 0) *
        (deriv chapterVIDGlobalContourFromMorse 0 * (-1 : ℂ)) *
          (root 0 - (‖chapterVIDCollisionLift‖ : ℂ) * Complex.I) +
      chapterVIDRootCoordinateCollisionFactorPlusDerivative chapterVIDZRootBase
          (root 0) *
            (deriv chapterVIDGlobalContourFromMorse 0 * (-1 : ℂ))) 0 at hprod
  rw [hrootZero, chapterVIDRootCoordinateCollisionFactorPlusDerivative_base,
    zero_mul, add_zero] at hprod
  have hprod' : HasDerivAt
      (fun w : ℂ ↦
        chapterVIDRootCoordinateCollisionFactorPlusDerivative chapterVIDZRootBase
            (root w) *
          (root w - (‖chapterVIDCollisionLift‖ : ℂ) * Complex.I))
      (chapterVIDRootCoordinateCollisionFactorPlusSecondDerivative
          chapterVIDZRootBase chapterVIDCollisionLift *
        (deriv chapterVIDGlobalContourFromMorse 0 * (-1 : ℂ)) *
        (chapterVIDCollisionLift -
          (‖chapterVIDCollisionLift‖ : ℂ) * Complex.I)) 0 := by
    exact hprod
  have him := (hprod'.mul_const (-Complex.I)).real_of_complex
  change HasDerivAt (fun L : ℝ ↦
    (chapterVIDRootCoordinateCollisionFactorPlusDerivative chapterVIDZRootBase
        (chapterVIDCriticalMorseRootPoint (0, ((-L : ℝ) : ℂ))) *
      (chapterVIDCriticalMorseRootPoint (0, ((-L : ℝ) : ℂ)) -
        chapterVIDOuterArcPoint .initial (1, 1))).im) _ 0
  rw [chapterVIDOuterArcPoint_initial_D]
  convert him using 1 <;>
    simp [root, Complex.mul_re, Complex.mul_im]

theorem deriv_chapterVIDInitialBaseEndpointDerivative_pos :
    0 < deriv chapterVIDInitialBaseEndpointDerivative 0 := by
  rw [hasDerivAt_chapterVIDInitialBaseEndpointDerivative.deriv]
  have hfRe :=
    chapterVIDRootCoordinateCollisionFactorPlusSecondDerivative_base_re_neg
  have hfIm := chapterVIDRootCoordinateCollisionFactorPlusSecondDerivative_base_im
  have hdRe := deriv_chapterVIDGlobalContourFromMorse_re_zero
  have hdIm := deriv_chapterVIDGlobalContourFromMorse_im_neg
  have hR : 0 < ‖chapterVIDCollisionLift‖ :=
    norm_pos_iff.mpr chapterVIDCollisionLift_ne_zero
  have hcRe : chapterVIDCollisionLift.re = -‖chapterVIDCollisionLift‖ := by
    rw [chapterVIDCollisionLift_eq_neg_norm]
    simp
  have hcIm : chapterVIDCollisionLift.im = 0 := by
    rw [chapterVIDCollisionLift_eq_neg_norm]
    simp
  simp only [Complex.mul_im, Complex.mul_re, Complex.sub_re, Complex.sub_im,
    Complex.neg_re, Complex.ofReal_re,
    Complex.neg_im, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    Complex.one_re, Complex.one_im, mul_zero, mul_one, sub_zero, neg_zero]
  rw [hfIm, hdRe, hcRe, hcIm]
  norm_num
  exact mul_pos (mul_pos_of_neg_of_neg hfRe hdIm) hR

set_option backward.isDefEq.respectTransparency.types false in
theorem hasDerivAt_chapterVIDInitialBaseEndpointRealDerivative :
    HasDerivAt chapterVIDInitialBaseEndpointRealDerivative
      ((chapterVIDRootCoordinateCollisionFactorPlusSecondDerivative
          chapterVIDZRootBase chapterVIDCollisionLift *
        (deriv chapterVIDGlobalContourFromMorse 0 * (-1 : ℂ)) *
        (chapterVIDCollisionLift -
          (‖chapterVIDCollisionLift‖ : ℂ) * Complex.I)).re) 0 := by
  let root : ℂ → ℂ := fun w ↦
    chapterVIDCriticalMorseRootPoint (0, (-1 : ℂ) * w)
  have hroot : HasDerivAt root
      (deriv chapterVIDGlobalContourFromMorse 0 * (-1 : ℂ)) 0 := by
    have houter : HasDerivAt
        (fun v : ℂ ↦ chapterVIDCriticalMorseRootPoint (0, v))
        (deriv chapterVIDGlobalContourFromMorse 0) ((-1 : ℂ) * 0) := by
      simpa using hasDerivAt_chapterVIDCriticalMorseRootFiber_zero
    have hinner := (hasDerivAt_id (0 : ℂ)).const_mul (-1 : ℂ)
    have h := houter.comp (0 : ℂ) hinner
    change HasDerivAt
      ((fun v : ℂ ↦ chapterVIDCriticalMorseRootPoint (0, v)) ∘
        fun w : ℂ ↦ (-1 : ℂ) * w) _ _
    simpa only [mul_one] using h
  have hrootZero : root 0 = chapterVIDCollisionLift := by
    simp [root, chapterVIDCriticalMorseRootPoint_base]
  have hfactorAt : HasDerivAt
      (chapterVIDRootCoordinateCollisionFactorPlusDerivative chapterVIDZRootBase)
      (chapterVIDRootCoordinateCollisionFactorPlusSecondDerivative
        chapterVIDZRootBase (root 0)) (root 0) := by
    rw [hrootZero]
    exact hasDerivAt_chapterVIDRootCoordinateCollisionFactorPlusDerivative
      chapterVIDCollisionLift_ne_zero
  have hfactor := hfactorAt.comp 0 hroot
  have hdelta := hroot.sub_const
    ((‖chapterVIDCollisionLift‖ : ℂ) * Complex.I)
  have hprod := hfactor.mul hdelta
  change HasDerivAt
    (fun w : ℂ ↦
      chapterVIDRootCoordinateCollisionFactorPlusDerivative chapterVIDZRootBase
          (root w) *
        (root w - (‖chapterVIDCollisionLift‖ : ℂ) * Complex.I))
    (chapterVIDRootCoordinateCollisionFactorPlusSecondDerivative
          chapterVIDZRootBase (root 0) *
        (deriv chapterVIDGlobalContourFromMorse 0 * (-1 : ℂ)) *
          (root 0 - (‖chapterVIDCollisionLift‖ : ℂ) * Complex.I) +
      chapterVIDRootCoordinateCollisionFactorPlusDerivative chapterVIDZRootBase
          (root 0) *
            (deriv chapterVIDGlobalContourFromMorse 0 * (-1 : ℂ))) 0 at hprod
  rw [hrootZero, chapterVIDRootCoordinateCollisionFactorPlusDerivative_base,
    zero_mul, add_zero] at hprod
  have hre := hprod.real_of_complex
  change HasDerivAt (fun L : ℝ ↦
    (chapterVIDRootCoordinateCollisionFactorPlusDerivative chapterVIDZRootBase
        (chapterVIDCriticalMorseRootPoint (0, ((-L : ℝ) : ℂ))) *
      (chapterVIDCriticalMorseRootPoint (0, ((-L : ℝ) : ℂ)) -
        chapterVIDOuterArcPoint .initial (1, 1))).re) _ 0
  rw [chapterVIDOuterArcPoint_initial_D]
  convert hre using 1 <;>
    simp [root, Complex.mul_re, Complex.mul_im]

theorem deriv_chapterVIDInitialBaseEndpointRealDerivative_neg :
    deriv chapterVIDInitialBaseEndpointRealDerivative 0 < 0 := by
  rw [hasDerivAt_chapterVIDInitialBaseEndpointRealDerivative.deriv]
  have hfRe :=
    chapterVIDRootCoordinateCollisionFactorPlusSecondDerivative_base_re_neg
  have hfIm := chapterVIDRootCoordinateCollisionFactorPlusSecondDerivative_base_im
  have hdRe := deriv_chapterVIDGlobalContourFromMorse_re_zero
  have hdIm := deriv_chapterVIDGlobalContourFromMorse_im_neg
  have hR : 0 < ‖chapterVIDCollisionLift‖ :=
    norm_pos_iff.mpr chapterVIDCollisionLift_ne_zero
  have hcRe : chapterVIDCollisionLift.re = -‖chapterVIDCollisionLift‖ := by
    rw [chapterVIDCollisionLift_eq_neg_norm]
    simp
  have hcIm : chapterVIDCollisionLift.im = 0 := by
    rw [chapterVIDCollisionLift_eq_neg_norm]
    simp
  simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
    Complex.neg_re, Complex.ofReal_re, Complex.neg_im, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im,
    mul_zero, mul_one, sub_zero, neg_zero]
  rw [hfIm, hdRe, hcRe, hcIm]
  norm_num
  exact mul_pos (mul_pos_of_neg_of_neg hfRe hdIm) hR

set_option backward.isDefEq.respectTransparency.types false in
theorem hasDerivAt_chapterVIDFinalBaseEndpointDerivative :
    HasDerivAt chapterVIDFinalBaseEndpointDerivative
      ((chapterVIDRootCoordinateCollisionFactorPlusSecondDerivative
          chapterVIDZRootBase chapterVIDCollisionLift *
        deriv chapterVIDGlobalContourFromMorse 0 *
        (-Complex.I * (‖chapterVIDCollisionLift‖ : ℂ) -
          chapterVIDCollisionLift)).im) 0 := by
  let root : ℂ → ℂ := fun w ↦ chapterVIDCriticalMorseRootPoint (0, w)
  have hroot : HasDerivAt root (deriv chapterVIDGlobalContourFromMorse 0) 0 := by
    simpa only [root] using hasDerivAt_chapterVIDCriticalMorseRootFiber_zero
  have hrootZero : root 0 = chapterVIDCollisionLift := by
    simp [root, chapterVIDCriticalMorseRootPoint_base]
  have hfactorAt : HasDerivAt
      (chapterVIDRootCoordinateCollisionFactorPlusDerivative chapterVIDZRootBase)
      (chapterVIDRootCoordinateCollisionFactorPlusSecondDerivative
        chapterVIDZRootBase (root 0)) (root 0) := by
    rw [hrootZero]
    exact hasDerivAt_chapterVIDRootCoordinateCollisionFactorPlusDerivative
      chapterVIDCollisionLift_ne_zero
  have hfactor := hfactorAt.comp 0 hroot
  have hdelta := (hasDerivAt_const (0 : ℂ)
    (-Complex.I * (‖chapterVIDCollisionLift‖ : ℂ))).sub hroot
  have hprod := hfactor.mul hdelta
  simp only [Function.comp_apply, Pi.sub_apply, zero_sub] at hprod
  rw [hrootZero, chapterVIDRootCoordinateCollisionFactorPlusDerivative_base,
    zero_mul, add_zero] at hprod
  have him := (hprod.mul_const (-Complex.I)).real_of_complex
  change HasDerivAt (fun L : ℝ ↦
    (chapterVIDRootCoordinateCollisionFactorPlusDerivative chapterVIDZRootBase
        (chapterVIDCriticalMorseRootPoint (0, (L : ℂ))) *
      (chapterVIDOuterArcPoint .final (1, 0) -
        chapterVIDCriticalMorseRootPoint (0, (L : ℂ)))).im) _ 0
  rw [chapterVIDOuterArcPoint_final_D]
  convert him using 1 <;>
    simp [root, Complex.mul_re, Complex.mul_im]

theorem deriv_chapterVIDFinalBaseEndpointDerivative_pos :
    0 < deriv chapterVIDFinalBaseEndpointDerivative 0 := by
  rw [hasDerivAt_chapterVIDFinalBaseEndpointDerivative.deriv]
  have hfRe :=
    chapterVIDRootCoordinateCollisionFactorPlusSecondDerivative_base_re_neg
  have hfIm := chapterVIDRootCoordinateCollisionFactorPlusSecondDerivative_base_im
  have hdRe := deriv_chapterVIDGlobalContourFromMorse_re_zero
  have hdIm := deriv_chapterVIDGlobalContourFromMorse_im_neg
  have hR : 0 < ‖chapterVIDCollisionLift‖ :=
    norm_pos_iff.mpr chapterVIDCollisionLift_ne_zero
  have hcRe : chapterVIDCollisionLift.re = -‖chapterVIDCollisionLift‖ := by
    rw [chapterVIDCollisionLift_eq_neg_norm]
    simp
  have hcIm : chapterVIDCollisionLift.im = 0 := by
    rw [chapterVIDCollisionLift_eq_neg_norm]
    simp
  simp only [Complex.mul_im, Complex.mul_re, Complex.sub_re, Complex.sub_im,
    Complex.neg_re, Complex.ofReal_re, Complex.neg_im, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, sub_zero, zero_mul,
    neg_zero, zero_sub]
  rw [hfIm, hdRe, hcRe, hcIm]
  norm_num
  exact mul_pos (mul_pos_of_neg_of_neg hfRe hdIm) hR

set_option backward.isDefEq.respectTransparency.types false in
theorem hasDerivAt_chapterVIDFinalBaseEndpointRealDerivative :
    HasDerivAt chapterVIDFinalBaseEndpointRealDerivative
      ((chapterVIDRootCoordinateCollisionFactorPlusSecondDerivative
          chapterVIDZRootBase chapterVIDCollisionLift *
        deriv chapterVIDGlobalContourFromMorse 0 *
        (-Complex.I * (‖chapterVIDCollisionLift‖ : ℂ) -
          chapterVIDCollisionLift)).re) 0 := by
  let root : ℂ → ℂ := fun w ↦ chapterVIDCriticalMorseRootPoint (0, w)
  have hroot : HasDerivAt root (deriv chapterVIDGlobalContourFromMorse 0) 0 := by
    simpa only [root] using hasDerivAt_chapterVIDCriticalMorseRootFiber_zero
  have hrootZero : root 0 = chapterVIDCollisionLift := by
    simp [root, chapterVIDCriticalMorseRootPoint_base]
  have hfactorAt : HasDerivAt
      (chapterVIDRootCoordinateCollisionFactorPlusDerivative chapterVIDZRootBase)
      (chapterVIDRootCoordinateCollisionFactorPlusSecondDerivative
        chapterVIDZRootBase (root 0)) (root 0) := by
    rw [hrootZero]
    exact hasDerivAt_chapterVIDRootCoordinateCollisionFactorPlusDerivative
      chapterVIDCollisionLift_ne_zero
  have hfactor := hfactorAt.comp 0 hroot
  have hdelta := (hasDerivAt_const (0 : ℂ)
    (-Complex.I * (‖chapterVIDCollisionLift‖ : ℂ))).sub hroot
  have hprod := hfactor.mul hdelta
  simp only [Function.comp_apply, Pi.sub_apply, zero_sub] at hprod
  rw [hrootZero, chapterVIDRootCoordinateCollisionFactorPlusDerivative_base,
    zero_mul, add_zero] at hprod
  have hre := hprod.real_of_complex
  change HasDerivAt (fun L : ℝ ↦
    (chapterVIDRootCoordinateCollisionFactorPlusDerivative chapterVIDZRootBase
        (chapterVIDCriticalMorseRootPoint (0, (L : ℂ))) *
      (chapterVIDOuterArcPoint .final (1, 0) -
        chapterVIDCriticalMorseRootPoint (0, (L : ℂ)))).re) _ 0
  rw [chapterVIDOuterArcPoint_final_D]
  convert hre using 1 <;>
    simp [root, Complex.mul_re, Complex.mul_im]

theorem deriv_chapterVIDFinalBaseEndpointRealDerivative_pos :
    0 < deriv chapterVIDFinalBaseEndpointRealDerivative 0 := by
  rw [hasDerivAt_chapterVIDFinalBaseEndpointRealDerivative.deriv]
  have hfRe :=
    chapterVIDRootCoordinateCollisionFactorPlusSecondDerivative_base_re_neg
  have hfIm := chapterVIDRootCoordinateCollisionFactorPlusSecondDerivative_base_im
  have hdRe := deriv_chapterVIDGlobalContourFromMorse_re_zero
  have hdIm := deriv_chapterVIDGlobalContourFromMorse_im_neg
  have hR : 0 < ‖chapterVIDCollisionLift‖ :=
    norm_pos_iff.mpr chapterVIDCollisionLift_ne_zero
  have hcRe : chapterVIDCollisionLift.re = -‖chapterVIDCollisionLift‖ := by
    rw [chapterVIDCollisionLift_eq_neg_norm]
    simp
  have hcIm : chapterVIDCollisionLift.im = 0 := by
    rw [chapterVIDCollisionLift_eq_neg_norm]
    simp
  simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
    Complex.neg_re, Complex.ofReal_re, Complex.neg_im, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, sub_zero, zero_mul,
    neg_zero, zero_sub]
  rw [hfIm, hdRe, hcRe, hcIm]
  norm_num
  exact mul_pos (mul_pos_of_neg_of_neg hfRe hdIm) hR

@[simp] theorem chapterVIDInitialBaseEndpointDerivative_zero : chapterVIDInitialBaseEndpointDerivative 0 = 0 := by
  simp [chapterVIDInitialBaseEndpointDerivative, chapterVIDCriticalMorseRootPoint_base,
    chapterVIDRootCoordinateCollisionFactorPlusDerivative_base]

@[simp] theorem chapterVIDFinalBaseEndpointDerivative_zero : chapterVIDFinalBaseEndpointDerivative 0 = 0 := by
  simp [chapterVIDFinalBaseEndpointDerivative, chapterVIDCriticalMorseRootPoint_base,
    chapterVIDRootCoordinateCollisionFactorPlusDerivative_base]

@[simp] theorem chapterVIDInitialBaseEndpointRealDerivative_zero :
    chapterVIDInitialBaseEndpointRealDerivative 0 = 0 := by
  simp [chapterVIDInitialBaseEndpointRealDerivative, chapterVIDCriticalMorseRootPoint_base,
    chapterVIDRootCoordinateCollisionFactorPlusDerivative_base]

@[simp] theorem chapterVIDFinalBaseEndpointRealDerivative_zero :
    chapterVIDFinalBaseEndpointRealDerivative 0 = 0 := by
  simp [chapterVIDFinalBaseEndpointRealDerivative, chapterVIDCriticalMorseRootPoint_base,
    chapterVIDRootCoordinateCollisionFactorPlusDerivative_base]

theorem eventually_chapterVIDInitialBaseEndpointDerivative_pos :
    ∀ᶠ L : ℝ in nhdsWithin 0 (Set.Ioi 0), 0 < chapterVIDInitialBaseEndpointDerivative L := by
  have hsign := eventually_nhdsWithin_sign_eq_of_deriv_pos
    deriv_chapterVIDInitialBaseEndpointDerivative_pos chapterVIDInitialBaseEndpointDerivative_zero
  filter_upwards [hsign.filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with L hsignL hL
  have hLsign : SignType.sign L = 1 := sign_pos hL
  rw [sub_zero, hLsign] at hsignL
  exact sign_eq_one_iff.mp hsignL

theorem eventually_chapterVIDFinalBaseEndpointDerivative_pos :
    ∀ᶠ L : ℝ in nhdsWithin 0 (Set.Ioi 0), 0 < chapterVIDFinalBaseEndpointDerivative L := by
  have hsign := eventually_nhdsWithin_sign_eq_of_deriv_pos
    deriv_chapterVIDFinalBaseEndpointDerivative_pos chapterVIDFinalBaseEndpointDerivative_zero
  filter_upwards [hsign.filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with L hsignL hL
  have hLsign : SignType.sign L = 1 := sign_pos hL
  rw [sub_zero, hLsign] at hsignL
  exact sign_eq_one_iff.mp hsignL

theorem eventually_chapterVIDInitialBaseEndpointRealDerivative_neg :
    ∀ᶠ L : ℝ in nhdsWithin 0 (Set.Ioi 0),
      chapterVIDInitialBaseEndpointRealDerivative L < 0 := by
  have hsign := eventually_nhdsWithin_sign_eq_of_deriv_neg
    deriv_chapterVIDInitialBaseEndpointRealDerivative_neg
      chapterVIDInitialBaseEndpointRealDerivative_zero
  filter_upwards [hsign.filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with L hsignL hL
  have hnegLsign : SignType.sign (-L) = -1 :=
    sign_eq_neg_one_iff.mpr (neg_neg_of_pos hL)
  rw [zero_sub, hnegLsign] at hsignL
  exact sign_eq_neg_one_iff.mp hsignL

theorem eventually_chapterVIDFinalBaseEndpointRealDerivative_pos :
    ∀ᶠ L : ℝ in nhdsWithin 0 (Set.Ioi 0),
      0 < chapterVIDFinalBaseEndpointRealDerivative L := by
  have hsign := eventually_nhdsWithin_sign_eq_of_deriv_pos
    deriv_chapterVIDFinalBaseEndpointRealDerivative_pos
      chapterVIDFinalBaseEndpointRealDerivative_zero
  filter_upwards [hsign.filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with L hsignL hL
  have hLsign : SignType.sign L = 1 := sign_pos hL
  rw [sub_zero, hLsign] at hsignL
  exact sign_eq_one_iff.mp hsignL

def chapterVIDEndpointDerivativeValue
    (side : ChapterVIDOuterArcSide) (k L : ℝ) : ℝ :=
  match side with
  | .initial =>
      (chapterVIDRootCoordinateCollisionFactorPlusDerivative
          (chapterVIDCriticalParameterRootAtD (k : ℂ))
          (chapterVIDCriticalMorseRootPoint
            ((k : ℂ), ((-L : ℝ) : ℂ))) *
        (chapterVIDCriticalMorseRootPoint
            ((k : ℂ), ((-L : ℝ) : ℂ)) -
          chapterVIDOuterArcPoint .initial
            (chapterVIDCriticalToGlobalParameter k, 1))).im
  | .final =>
      (chapterVIDRootCoordinateCollisionFactorPlusDerivative
          (chapterVIDCriticalParameterRootAtD (k : ℂ))
          (chapterVIDCriticalMorseRootPoint ((k : ℂ), (L : ℂ))) *
        (chapterVIDOuterArcPoint .final
            (chapterVIDCriticalToGlobalParameter k, 0) -
          chapterVIDCriticalMorseRootPoint ((k : ℂ), (L : ℂ)))).im

/-- The real component of the same literal affine-path derivative.  This is the endpoint anchor
for the compiled real-curvature route. -/
def chapterVIDEndpointRealDerivativeValue
    (side : ChapterVIDOuterArcSide) (k L : ℝ) : ℝ :=
  match side with
  | .initial =>
      (chapterVIDRootCoordinateCollisionFactorPlusDerivative
          (chapterVIDCriticalParameterRootAtD (k : ℂ))
          (chapterVIDCriticalMorseRootPoint
            ((k : ℂ), ((-L : ℝ) : ℂ))) *
        (chapterVIDCriticalMorseRootPoint
            ((k : ℂ), ((-L : ℝ) : ℂ)) -
          chapterVIDOuterArcPoint .initial
            (chapterVIDCriticalToGlobalParameter k, 1))).re
  | .final =>
      (chapterVIDRootCoordinateCollisionFactorPlusDerivative
          (chapterVIDCriticalParameterRootAtD (k : ℂ))
          (chapterVIDCriticalMorseRootPoint ((k : ℂ), (L : ℂ))) *
        (chapterVIDOuterArcPoint .final
            (chapterVIDCriticalToGlobalParameter k, 0) -
          chapterVIDCriticalMorseRootPoint ((k : ℂ), (L : ℂ)))).re

@[simp] theorem chapterVIDEndpointDerivativeValue_initial_zero (L : ℝ) :
    chapterVIDEndpointDerivativeValue .initial 0 L = chapterVIDInitialBaseEndpointDerivative L := by
  simp [chapterVIDEndpointDerivativeValue, chapterVIDInitialBaseEndpointDerivative]

@[simp] theorem chapterVIDEndpointDerivativeValue_final_zero (L : ℝ) :
    chapterVIDEndpointDerivativeValue .final 0 L = chapterVIDFinalBaseEndpointDerivative L := by
  simp [chapterVIDEndpointDerivativeValue, chapterVIDFinalBaseEndpointDerivative]

@[simp] theorem chapterVIDEndpointRealDerivativeValue_initial_zero (L : ℝ) :
    chapterVIDEndpointRealDerivativeValue .initial 0 L =
      chapterVIDInitialBaseEndpointRealDerivative L := by
  simp [chapterVIDEndpointRealDerivativeValue,
    chapterVIDInitialBaseEndpointRealDerivative]

@[simp] theorem chapterVIDEndpointRealDerivativeValue_final_zero (L : ℝ) :
    chapterVIDEndpointRealDerivativeValue .final 0 L =
      chapterVIDFinalBaseEndpointRealDerivative L := by
  simp [chapterVIDEndpointRealDerivativeValue,
    chapterVIDFinalBaseEndpointRealDerivative]

theorem continuousAt_chapterVIDRootCoordinateCollisionFactorPlusDerivative_comp
    {x : ℝ} {zeta coordinate : ℝ → ℂ}
    (hzeta : ContinuousAt zeta x) (hcoordinate : ContinuousAt coordinate x)
    (hcoordinateNe : coordinate x ≠ 0) :
    ContinuousAt (fun k ↦
      chapterVIDRootCoordinateCollisionFactorPlusDerivative
        (zeta k) (coordinate k)) x := by
  have hinv : ContinuousAt (fun k ↦ (coordinate k)⁻¹) x :=
    hcoordinate.inv₀ hcoordinateNe
  have hcontour : ContinuousAt
      (fun k ↦ chapterVIDRootToOriginalContour (coordinate k)) x :=
    (analyticAt_chapterVIDRootToOriginalContour hcoordinateNe).continuousAt.comp_of_eq
      hcoordinate rfl
  have hanomaly : ContinuousAt (fun k ↦
      chapterVIDRootSecondAnomaly (zeta k) (coordinate k)) x := by
    unfold chapterVIDRootSecondAnomaly
    exact hzeta.mul hcontour
  unfold chapterVIDRootCoordinateCollisionFactorPlusDerivative
  exact (continuousAt_const.mul
      ((continuousAt_const.mul (hcoordinate.pow 2)).sub
        (continuousAt_const.mul (hinv.pow 4)))).sub
    ((continuousAt_const.mul hanomaly).mul hinv) |>.add
    ((continuousAt_const.mul hanomaly).mul
      ((hinv.pow 4).add (hcoordinate.pow 2)))

theorem continuousAt_chapterVIDEndpointDerivativeValue
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalGlobalRootModel massProduct b d)
    (side : ChapterVIDOuterArcSide) (L : ℝ)
    (hL : L ∈ Set.uIcc (-model.L) model.L)
    (hnegL : -L ∈ Set.uIcc (-model.L) model.L) :
    ContinuousAt (fun k : ℝ ↦ chapterVIDEndpointDerivativeValue side k L) 0 := by
  have hk0 : (0 : ℝ) ∈ Set.Icc 0 model.δ :=
    ⟨le_rfl, model.δ_pos.le⟩
  have hzeta : ContinuousAt
      (fun k : ℝ ↦ chapterVIDCriticalParameterRootAtD (k : ℂ)) 0 :=
    (model.parameterRoot_analyticAt 0 hk0).continuousAt.comp_of_eq
      Complex.continuous_ofReal.continuousAt rfl
  have hparameter : ContinuousAt chapterVIDCriticalToGlobalParameter 0 :=
    continuousAt_chapterVIDCriticalToGlobalParameter
  cases side with
  | initial =>
      have hroot : ContinuousAt (fun k : ℝ ↦
          chapterVIDCriticalMorseRootPoint
            ((k : ℂ), ((-L : ℝ) : ℂ))) 0 :=
        (model.root_analyticAt 0 hk0 (-L) hnegL).continuousAt.comp_of_eq
          (Complex.continuous_ofReal.continuousAt.prodMk continuousAt_const) rfl
      have hrootNe := model.root_ne_zero 0 hk0 (-L) hnegL
      unfold chapterVIDEndpointDerivativeValue
      apply Complex.continuous_im.continuousAt.comp_of_eq _ rfl
      apply ContinuousAt.mul
      · exact continuousAt_chapterVIDRootCoordinateCollisionFactorPlusDerivative_comp hzeta hroot hrootNe
      · exact hroot.sub
          ((continuous_chapterVIDOuterArcPoint .initial).continuousAt.comp_of_eq
            (hparameter.prodMk continuousAt_const) rfl)
  | final =>
      have hroot : ContinuousAt (fun k : ℝ ↦
          chapterVIDCriticalMorseRootPoint ((k : ℂ), (L : ℂ))) 0 :=
        (model.root_analyticAt 0 hk0 L hL).continuousAt.comp_of_eq
          (Complex.continuous_ofReal.continuousAt.prodMk continuousAt_const) rfl
      have hrootNe := model.root_ne_zero 0 hk0 L hL
      unfold chapterVIDEndpointDerivativeValue
      apply Complex.continuous_im.continuousAt.comp_of_eq _ rfl
      apply ContinuousAt.mul
      · exact continuousAt_chapterVIDRootCoordinateCollisionFactorPlusDerivative_comp hzeta hroot hrootNe
      · exact
          ((continuous_chapterVIDOuterArcPoint .final).continuousAt.comp_of_eq
            (hparameter.prodMk continuousAt_const) rfl).sub hroot

theorem continuousAt_chapterVIDEndpointRealDerivativeValue
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalGlobalRootModel massProduct b d)
    (side : ChapterVIDOuterArcSide) (L : ℝ)
    (hL : L ∈ Set.uIcc (-model.L) model.L)
    (hnegL : -L ∈ Set.uIcc (-model.L) model.L) :
    ContinuousAt (fun k : ℝ ↦ chapterVIDEndpointRealDerivativeValue side k L) 0 := by
  have hk0 : (0 : ℝ) ∈ Set.Icc 0 model.δ :=
    ⟨le_rfl, model.δ_pos.le⟩
  have hzeta : ContinuousAt
      (fun k : ℝ ↦ chapterVIDCriticalParameterRootAtD (k : ℂ)) 0 :=
    (model.parameterRoot_analyticAt 0 hk0).continuousAt.comp_of_eq
      Complex.continuous_ofReal.continuousAt rfl
  have hparameter : ContinuousAt chapterVIDCriticalToGlobalParameter 0 :=
    continuousAt_chapterVIDCriticalToGlobalParameter
  cases side with
  | initial =>
      have hroot : ContinuousAt (fun k : ℝ ↦
          chapterVIDCriticalMorseRootPoint
            ((k : ℂ), ((-L : ℝ) : ℂ))) 0 :=
        (model.root_analyticAt 0 hk0 (-L) hnegL).continuousAt.comp_of_eq
          (Complex.continuous_ofReal.continuousAt.prodMk continuousAt_const) rfl
      have hrootNe := model.root_ne_zero 0 hk0 (-L) hnegL
      unfold chapterVIDEndpointRealDerivativeValue
      apply Complex.continuous_re.continuousAt.comp_of_eq _ rfl
      apply ContinuousAt.mul
      · exact continuousAt_chapterVIDRootCoordinateCollisionFactorPlusDerivative_comp
          hzeta hroot hrootNe
      · exact hroot.sub
          ((continuous_chapterVIDOuterArcPoint .initial).continuousAt.comp_of_eq
            (hparameter.prodMk continuousAt_const) rfl)
  | final =>
      have hroot : ContinuousAt (fun k : ℝ ↦
          chapterVIDCriticalMorseRootPoint ((k : ℂ), (L : ℂ))) 0 :=
        (model.root_analyticAt 0 hk0 L hL).continuousAt.comp_of_eq
          (Complex.continuous_ofReal.continuousAt.prodMk continuousAt_const) rfl
      have hrootNe := model.root_ne_zero 0 hk0 L hL
      unfold chapterVIDEndpointRealDerivativeValue
      apply Complex.continuous_re.continuousAt.comp_of_eq _ rfl
      apply ContinuousAt.mul
      · exact continuousAt_chapterVIDRootCoordinateCollisionFactorPlusDerivative_comp
          hzeta hroot hrootNe
      · exact
          ((continuous_chapterVIDOuterArcPoint .final).continuousAt.comp_of_eq
            (hparameter.prodMk continuousAt_const) rfl).sub hroot

theorem lineDerivativeImag_local_eq_chapterVIDEndpointDerivativeValue
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) :
    ChapterVIDConnectorFactorTerminal.lineDerivativeImag model side
        (ChapterVIDConnectorSeamCompiledGrid.localParameter side : ℝ) =
      chapterVIDEndpointDerivativeValue side model.κ model.rootModel.L := by
  have hk : model.κ ∈ Set.Icc 0 model.κ := ⟨model.κ_pos.le, le_rfl⟩
  have hroot := model.parameterRoot_eq_global model.κ hk
  cases side with
  | initial =>
      simp only [ChapterVIDConnectorFactorTerminal.lineDerivativeImag,
        chapterVIDRootCoordinateCollisionFactorPlusLineDerivativeImag,
        ChapterVIDConnectorSeamCompiledGrid.localParameter,
        ChapterVIDPrincipalConnectorModel.connectorParameterRoot,
        ChapterVIDPrincipalConnectorModel.criticalValue_zero, hroot,
        chapterVIDEndpointDerivativeValue,
        ChapterVIDPrincipalGlobalRootModel.connectorSource,
        ChapterVIDPrincipalGlobalRootModel.connectorTarget,
        ChapterVIDPrincipalGlobalRootModel.localConnectorEndpoint,
        ChapterVIDPrincipalGlobalRootModel.outerConnectorEndpoint,
        AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
      simp
  | final =>
      simp only [ChapterVIDConnectorFactorTerminal.lineDerivativeImag,
        chapterVIDRootCoordinateCollisionFactorPlusLineDerivativeImag,
        ChapterVIDConnectorSeamCompiledGrid.localParameter,
        ChapterVIDPrincipalConnectorModel.connectorParameterRoot,
        ChapterVIDPrincipalConnectorModel.criticalValue_zero, hroot,
        chapterVIDEndpointDerivativeValue,
        ChapterVIDPrincipalGlobalRootModel.connectorSource,
        ChapterVIDPrincipalGlobalRootModel.connectorTarget,
        ChapterVIDPrincipalGlobalRootModel.localConnectorEndpoint,
        ChapterVIDPrincipalGlobalRootModel.outerConnectorEndpoint,
        AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
      simp

def ChapterVIDOrientedGlobalRootModel.restrictLength
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDOrientedGlobalRootModel massProduct b d)
    (L' : ℝ) (hL' : 0 < L') (hLle : L' ≤ model.L) :
    ChapterVIDOrientedGlobalRootModel massProduct b d where
  toChapterVIDPrincipalGlobalRootModel :=
    model.toChapterVIDPrincipalGlobalRootModel.restrict
      model.δ L' model.δ_pos hL' le_rfl hLle
  rootFiberDerivative_im_neg := by
    intro k hk v hv
    change k ∈ Set.Icc 0 model.δ at hk
    change v ∈ Set.uIcc (-L') L' at hv
    apply model.rootFiberDerivative_im_neg k hk v
    rw [Set.uIcc_of_le (by linarith [hL'])] at hv
    rw [Set.uIcc_of_le (by linarith [model.L_pos])]
    exact ⟨by linarith [hv.1, hLle], by linarith [hv.2, hLle]⟩
  rootCenter_im_zero := model.rootCenter_im_zero

def ChapterVIDPrincipalConnectorModel.restrictParameter
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (κ' : ℝ) (hκ' : 0 < κ') (hκle : κ' ≤ model.κ) :
    ChapterVIDPrincipalConnectorModel massProduct b d where
  rootModel := model.rootModel
  κ := κ'
  κ_pos := hκ'
  κ_le_delta := hκle.trans model.κ_le_delta
  parameterRoot_eq_global := by
    intro k hk
    exact model.parameterRoot_eq_global k ⟨hk.1, hk.2.trans hκle⟩
  globalParameter_mem_terminalCell := by
    intro k hk
    exact model.globalParameter_mem_terminalCell k ⟨hk.1, hk.2.trans hκle⟩

/-- The outer endpoint is continuous in the literal critical value at the collision.  This form
is more useful to the homogeneous compiler input than continuity in the connector's unit
parameter, because it compares the selected endpoint at `κ` directly with its collapsed value at
zero. -/
theorem ChapterVIDPrincipalGlobalRootModel.continuousAt_outerConnectorEndpoint_zero
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalGlobalRootModel massProduct b d)
    (side : ChapterVIDOuterArcSide) :
    ContinuousAt (fun k : ℝ ↦ model.outerConnectorEndpoint side k) 0 := by
  have hk0 : (0 : ℝ) ∈ Set.Icc 0 model.δ := ⟨le_rfl, model.δ_pos.le⟩
  have hinverse := model.parameterInverse_analyticAt 0 hk0
  have hcritical : ContinuousAt (fun k : ℝ ↦ (k : ℂ)) 0 :=
    Complex.continuous_ofReal.continuousAt
  have hinverseComp : ContinuousAt
      (fun k : ℝ ↦ chapterVIDCriticalParameterInverseAtD (k : ℂ)) 0 :=
    hinverse.continuousAt.comp_of_eq hcritical rfl
  have hreal : ContinuousAt
      (fun k : ℝ ↦ (chapterVIDCriticalParameterInverseAtD (k : ℂ)).re) 0 :=
    Complex.continuous_re.continuousAt.comp_of_eq hinverseComp rfl
  have hraw : ContinuousAt chapterVIDCriticalToGlobalParameterRaw 0 := by
    unfold chapterVIDCriticalToGlobalParameterRaw
    exact (continuousAt_const.sub hreal).div_const _
  have hparameter : ContinuousAt chapterVIDCriticalToGlobalParameter 0 := by
    unfold chapterVIDCriticalToGlobalParameter
    exact (continuous_projIcc (h := zero_le_one)).continuousAt.comp_of_eq hraw rfl
  cases side
  · exact (continuous_chapterVIDOuterArcPoint .initial).continuousAt.comp_of_eq
      (hparameter.prodMk continuousAt_const) rfl
  · exact (continuous_chapterVIDOuterArcPoint .final).continuousAt.comp_of_eq
      (hparameter.prodMk continuousAt_const) rfl

structure ChapterVIDAnchoredConnectorModel
    (massProduct : ℂ) (b d : ℤ)
    extends ChapterVIDOrientedConnectorModel massProduct b d where
  initialAnchor :
    ChapterVIDConnectorFactorTerminal.EndpointDerivativeAnchor
      toChapterVIDOrientedConnectorModel.toChapterVIDPrincipalConnectorModel .initial
  finalAnchor :
    ChapterVIDConnectorFactorTerminal.EndpointDerivativeAnchor
      toChapterVIDOrientedConnectorModel.toChapterVIDPrincipalConnectorModel .final
  initialRealAnchor :
    chapterVIDEndpointRealDerivativeValue .initial
      toChapterVIDOrientedConnectorModel.toChapterVIDPrincipalConnectorModel.κ
      toChapterVIDOrientedConnectorModel.toChapterVIDPrincipalConnectorModel.rootModel.L < 0
  finalRealAnchor :
    0 < chapterVIDEndpointRealDerivativeValue .final
      toChapterVIDOrientedConnectorModel.toChapterVIDPrincipalConnectorModel.κ
      toChapterVIDOrientedConnectorModel.toChapterVIDPrincipalConnectorModel.rootModel.L
  /-- The critical-value perturbation is subordinate to the inverse-Morse endpoint scale.  This
  relation is retained by the dependency-preserving terminal certificate. -/
  parameter_le_length_sq :
    toChapterVIDOrientedConnectorModel.toChapterVIDPrincipalConnectorModel.κ ≤
      toChapterVIDOrientedConnectorModel.toChapterVIDPrincipalConnectorModel.rootModel.L ^ 2
  /-- The actual relative cubic-root parameter perturbation, not merely its source coordinate,
  is subordinate to the same Morse scale. -/
  parameterRootRelativeDelta_norm_le_length_sq :
    ‖toChapterVIDOrientedConnectorModel.toChapterVIDPrincipalConnectorModel.connectorParameterRoot 0 /
        chapterVIDZRootBase - 1‖ ≤
      toChapterVIDOrientedConnectorModel.toChapterVIDPrincipalConnectorModel.rootModel.L ^ 2
  /-- The actual outer endpoint motion is also subordinate to `L²`.  Retaining this relation lets
  a compiled trace derive the connector direction from the collapsed direction and the two
  normalized moving inputs instead of enclosing those quantities independently. -/
  outerEndpointDelta_norm_le_length_sq :
    ∀ side : ChapterVIDOuterArcSide,
      ‖ChapterVIDPrincipalGlobalRootModel.outerConnectorEndpoint
          toChapterVIDOrientedConnectorModel.toChapterVIDPrincipalConnectorModel.rootModel side
            toChapterVIDOrientedConnectorModel.toChapterVIDPrincipalConnectorModel.κ -
        ChapterVIDPrincipalGlobalRootModel.outerConnectorEndpoint
          toChapterVIDOrientedConnectorModel.toChapterVIDPrincipalConnectorModel.rootModel
            side 0‖ ≤
        toChapterVIDOrientedConnectorModel.toChapterVIDPrincipalConnectorModel.rootModel.L ^ 2
  /-- The actual initial moving endpoint retains the inverse-Morse derivative direction after
  the critical parameter is moved from zero to `κ`. -/
  initialNormalizedLocalDelta_mem_directionCone :
    ‖chapterVIDNormalizedLocalEndpointDelta .initial
        toChapterVIDOrientedConnectorModel.toChapterVIDPrincipalConnectorModel.κ
        toChapterVIDOrientedConnectorModel.toChapterVIDPrincipalConnectorModel.rootModel.L -
      deriv chapterVIDGlobalContourFromMorse 0‖ <
        -(deriv chapterVIDGlobalContourFromMorse 0).im / 2
  /-- The corresponding directional cone condition on the final moving endpoint. -/
  finalNormalizedLocalDelta_mem_directionCone :
    ‖chapterVIDNormalizedLocalEndpointDelta .final
        toChapterVIDOrientedConnectorModel.toChapterVIDPrincipalConnectorModel.κ
        toChapterVIDOrientedConnectorModel.toChapterVIDPrincipalConnectorModel.rootModel.L -
      deriv chapterVIDGlobalContourFromMorse 0‖ <
        -(deriv chapterVIDGlobalContourFromMorse 0).im / 2

theorem ChapterVIDAnchoredConnectorModel.normalizedLocalEndpointDelta_im_lt_half_slope
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDAnchoredConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) :
    (chapterVIDNormalizedLocalEndpointDelta side model.κ model.rootModel.L).im <
      (deriv chapterVIDGlobalContourFromMorse 0).im / 2 := by
  let q := chapterVIDNormalizedLocalEndpointDelta side model.κ model.rootModel.L
  let slope := deriv chapterVIDGlobalContourFromMorse 0
  have hcone : ‖q - slope‖ < -slope.im / 2 := by
    cases side with
    | initial => exact model.initialNormalizedLocalDelta_mem_directionCone
    | final => exact model.finalNormalizedLocalDelta_mem_directionCone
  have him := (Complex.abs_im_le_norm (q - slope)).trans_lt hcone
  have himUpper := (abs_lt.mp him).2
  rw [Complex.sub_im] at himUpper
  linarith

theorem ChapterVIDAnchoredConnectorModel.normalizedLocalEndpointDelta_im_neg
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDAnchoredConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) :
    (chapterVIDNormalizedLocalEndpointDelta side model.κ model.rootModel.L).im < 0 := by
  have hhalf := model.normalizedLocalEndpointDelta_im_lt_half_slope side
  have hslope := deriv_chapterVIDGlobalContourFromMorse_im_neg
  linarith

theorem ChapterVIDAnchoredConnectorModel.initialLocalEndpointDelta_im_pos
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDAnchoredConnectorModel massProduct b d) :
    0 < (model.rootModel.localConnectorEndpoint .initial (model.criticalValue 0) -
      chapterVIDCollisionLift).im := by
  have hq := model.normalizedLocalEndpointDelta_im_neg .initial
  rw [ChapterVIDPrincipalConnectorModel.criticalValue_zero]
  unfold chapterVIDNormalizedLocalEndpointDelta at hq
  have hLne : ((-model.rootModel.L : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (neg_ne_zero.mpr model.rootModel.L_pos.ne')
  have heq :
      chapterVIDCriticalMorseRootPoint
          ((model.κ : ℂ), ((-model.rootModel.L : ℝ) : ℂ)) -
          chapterVIDCollisionLift =
        ((chapterVIDCriticalMorseRootPoint
          ((model.κ : ℂ), ((-model.rootModel.L : ℝ) : ℂ)) -
          chapterVIDCollisionLift) / ((-model.rootModel.L : ℝ) : ℂ)) *
            ((-model.rootModel.L : ℝ) : ℂ) := by
    field_simp
  have heim := congrArg Complex.im heq
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero] at heim
  rw [ChapterVIDPrincipalGlobalRootModel.localConnectorEndpoint]
  rw [heim]
  simpa only [zero_add, chapterVIDNormalizedLocalEndpointDelta] using
    mul_pos_of_neg_of_neg hq (neg_neg_of_pos model.rootModel.L_pos)

theorem ChapterVIDAnchoredConnectorModel.finalLocalEndpointDelta_im_neg
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDAnchoredConnectorModel massProduct b d) :
    (model.rootModel.localConnectorEndpoint .final (model.criticalValue 0) -
      chapterVIDCollisionLift).im < 0 := by
  have hq := model.normalizedLocalEndpointDelta_im_neg .final
  rw [ChapterVIDPrincipalConnectorModel.criticalValue_zero]
  unfold chapterVIDNormalizedLocalEndpointDelta at hq
  have hLne : (model.rootModel.L : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr model.rootModel.L_pos.ne'
  have heq :
      chapterVIDCriticalMorseRootPoint ((model.κ : ℂ), (model.rootModel.L : ℂ)) -
          chapterVIDCollisionLift =
        ((chapterVIDCriticalMorseRootPoint
          ((model.κ : ℂ), (model.rootModel.L : ℂ)) -
          chapterVIDCollisionLift) / (model.rootModel.L : ℂ)) *
            (model.rootModel.L : ℂ) := by
    field_simp
  have heim := congrArg Complex.im heq
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero] at heim
  rw [ChapterVIDPrincipalGlobalRootModel.localConnectorEndpoint]
  rw [heim]
  simpa only [zero_add, chapterVIDNormalizedLocalEndpointDelta] using
    mul_neg_of_neg_of_pos hq model.rootModel.L_pos

/-- The initial endpoint displacement has a uniform first-order margin in the selected Morse
length.  This is the scale-aware lower bound consumed by a homogeneous finite certificate. -/
theorem ChapterVIDAnchoredConnectorModel.length_mul_half_slope_lt_initialLocalEndpointDelta_im
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDAnchoredConnectorModel massProduct b d) :
    model.rootModel.L * (-(deriv chapterVIDGlobalContourFromMorse 0).im / 2) <
      (model.rootModel.localConnectorEndpoint .initial (model.criticalValue 0) -
        chapterVIDCollisionLift).im := by
  have hq := model.normalizedLocalEndpointDelta_im_lt_half_slope .initial
  rw [ChapterVIDPrincipalConnectorModel.criticalValue_zero]
  unfold chapterVIDNormalizedLocalEndpointDelta at hq
  have hLne : ((-model.rootModel.L : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (neg_ne_zero.mpr model.rootModel.L_pos.ne')
  have heq :
      chapterVIDCriticalMorseRootPoint
          ((model.κ : ℂ), ((-model.rootModel.L : ℝ) : ℂ)) -
          chapterVIDCollisionLift =
        ((chapterVIDCriticalMorseRootPoint
          ((model.κ : ℂ), ((-model.rootModel.L : ℝ) : ℂ)) -
          chapterVIDCollisionLift) / ((-model.rootModel.L : ℝ) : ℂ)) *
            ((-model.rootModel.L : ℝ) : ℂ) := by
    field_simp
  have heim := congrArg Complex.im heq
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero] at heim
  rw [ChapterVIDPrincipalGlobalRootModel.localConnectorEndpoint, heim]
  have hL := model.rootModel.L_pos
  change
    ((chapterVIDCriticalMorseRootPoint
      ((model.κ : ℂ), ((-model.rootModel.L : ℝ) : ℂ)) -
      chapterVIDCollisionLift) / ((-model.rootModel.L : ℝ) : ℂ)).im <
        (deriv chapterVIDGlobalContourFromMorse 0).im / 2 at hq
  have hmul := mul_lt_mul_of_neg_left hq (neg_neg_of_pos hL)
  calc
    model.rootModel.L * (-(deriv chapterVIDGlobalContourFromMorse 0).im / 2) =
        (-model.rootModel.L) * ((deriv chapterVIDGlobalContourFromMorse 0).im / 2) := by
          ring
    _ < (-model.rootModel.L) *
        ((chapterVIDCriticalMorseRootPoint
          ((model.κ : ℂ), ((-model.rootModel.L : ℝ) : ℂ)) -
          chapterVIDCollisionLift) / ((-model.rootModel.L : ℝ) : ℂ)).im := hmul
    _ = 0 + ((chapterVIDCriticalMorseRootPoint
          ((model.κ : ℂ), ((-model.rootModel.L : ℝ) : ℂ)) -
          chapterVIDCollisionLift) / ((-model.rootModel.L : ℝ) : ℂ)).im *
          -model.rootModel.L := by ring

/-- The final displacement has the opposite signed margin, with the same Morse-length scale. -/
theorem ChapterVIDAnchoredConnectorModel.finalLocalEndpointDelta_im_lt_length_mul_half_slope
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDAnchoredConnectorModel massProduct b d) :
    (model.rootModel.localConnectorEndpoint .final (model.criticalValue 0) -
        chapterVIDCollisionLift).im <
      model.rootModel.L * ((deriv chapterVIDGlobalContourFromMorse 0).im / 2) := by
  have hq := model.normalizedLocalEndpointDelta_im_lt_half_slope .final
  rw [ChapterVIDPrincipalConnectorModel.criticalValue_zero]
  unfold chapterVIDNormalizedLocalEndpointDelta at hq
  have hLne : (model.rootModel.L : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr model.rootModel.L_pos.ne'
  have heq :
      chapterVIDCriticalMorseRootPoint ((model.κ : ℂ), (model.rootModel.L : ℂ)) -
          chapterVIDCollisionLift =
        ((chapterVIDCriticalMorseRootPoint
          ((model.κ : ℂ), (model.rootModel.L : ℂ)) -
          chapterVIDCollisionLift) / (model.rootModel.L : ℂ)) *
            (model.rootModel.L : ℂ) := by
    field_simp
  have heim := congrArg Complex.im heq
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero] at heim
  rw [ChapterVIDPrincipalGlobalRootModel.localConnectorEndpoint, heim]
  simpa only [zero_add, chapterVIDNormalizedLocalEndpointDelta, mul_comm] using
    (mul_lt_mul_of_pos_right hq model.rootModel.L_pos)

theorem exists_chapterVIDAnchoredConnectorModel_bounded
    (massProduct : ℂ) (b d : ℤ)
    (Lmax κmax : ℝ) (hLmaxPos : 0 < Lmax) (hκmaxPos : 0 < κmax) :
    ∃ model : ChapterVIDAnchoredConnectorModel massProduct b d,
      model.toChapterVIDPrincipalConnectorModel.rootModel.L ≤ Lmax ∧
        model.toChapterVIDPrincipalConnectorModel.κ ≤ κmax := by
  obtain ⟨oriented⟩ := exists_chapterVIDOrientedGlobalRootModel massProduct b d
  have hlengthEventually :=
    (eventually_chapterVIDInitialBaseEndpointDerivative_pos.and
      eventually_chapterVIDFinalBaseEndpointDerivative_pos).and
    (eventually_chapterVIDInitialBaseEndpointRealDerivative_neg.and
      eventually_chapterVIDFinalBaseEndpointRealDerivative_pos)
  obtain ⟨εL, hεL, hlengthBall⟩ := Metric.mem_nhdsWithin_iff.mp hlengthEventually
  obtain ⟨εCone, hεCone, hconeBall⟩ := Metric.mem_nhdsWithin_iff.mp
    eventually_chapterVIDCriticalMorseRootFiber_normalizedDelta_mem_directionCone
  let L' := min (min (min (oriented.L / 2) (εL / 2)) (Lmax / 2)) (εCone / 2)
  have hL' : 0 < L' := by
    dsimp [L']
    exact lt_min
      (lt_min
        (lt_min (div_pos oriented.L_pos (by norm_num))
          (div_pos hεL (by norm_num)))
        (div_pos hLmaxPos (by norm_num)))
      (div_pos hεCone (by norm_num))
  have hLle : L' ≤ oriented.L := by
    exact (min_le_left _ _).trans ((min_le_left _ _).trans
      ((min_le_left _ _).trans (by linarith [oriented.L_pos])))
  have hLmax : L' ≤ Lmax := by
    exact (min_le_left _ _).trans
      ((min_le_right _ _).trans (by linarith [hLmaxPos]))
  have hLball : L' ∈ Metric.ball (0 : ℝ) εL := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hL']
    have := (min_le_left (min (min (oriented.L / 2) (εL / 2)) (Lmax / 2))
      (εCone / 2)).trans ((min_le_left _ _).trans
        (min_le_right (oriented.L / 2) (εL / 2)))
    linarith
  have hbaseSigns :
      (0 < chapterVIDInitialBaseEndpointDerivative L' ∧
        0 < chapterVIDFinalBaseEndpointDerivative L') ∧
      (chapterVIDInitialBaseEndpointRealDerivative L' < 0 ∧
        0 < chapterVIDFinalBaseEndpointRealDerivative L') :=
    hlengthBall ⟨hLball, hL'⟩
  have hLComplexBall : (L' : ℂ) ∈ Metric.ball (0 : ℂ) εCone := by
    rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hL']
    have := min_le_right
      (min (min (oriented.L / 2) (εL / 2)) (Lmax / 2)) (εCone / 2)
    linarith
  have hnegLComplexBall : ((-L' : ℝ) : ℂ) ∈ Metric.ball (0 : ℂ) εCone := by
    rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
      abs_neg, abs_of_pos hL']
    have := min_le_right
      (min (min (oriented.L / 2) (εL / 2)) (Lmax / 2)) (εCone / 2)
    linarith
  have hinitialDirectionAtZero :
      ‖chapterVIDNormalizedLocalEndpointDelta .initial 0 L' -
          deriv chapterVIDGlobalContourFromMorse 0‖ <
        -(deriv chapterVIDGlobalContourFromMorse 0).im / 2 := by
    apply hconeBall
    refine ⟨hnegLComplexBall, ?_⟩
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using
      (Complex.ofReal_ne_zero.mpr (neg_ne_zero.mpr hL'.ne'))
  have hfinalDirectionAtZero :
      ‖chapterVIDNormalizedLocalEndpointDelta .final 0 L' -
          deriv chapterVIDGlobalContourFromMorse 0‖ <
        -(deriv chapterVIDGlobalContourFromMorse 0).im / 2 := by
    apply hconeBall
    refine ⟨hLComplexBall, ?_⟩
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using
      (Complex.ofReal_ne_zero.mpr hL'.ne')
  let root := oriented.restrictLength L' hL' hLle
  obtain ⟨connector, hroot⟩ :=
    exists_chapterVIDPrincipalConnectorModel_of_rootModel
      root.toChapterVIDPrincipalGlobalRootModel
  let orientedConnector : ChapterVIDOrientedConnectorModel massProduct b d := {
    toChapterVIDPrincipalConnectorModel := connector
    rootFiberDerivative_im_neg := by
      intro k hk v hv
      rw [hroot] at hk hv
      exact root.rootFiberDerivative_im_neg k hk v hv
    rootCenter_im_zero := by
      intro k hk
      rw [hroot] at hk
      exact root.rootCenter_im_zero k hk }
  have hrootL : connector.rootModel.L = L' := by
    rw [hroot]
    rfl
  have hLmem : L' ∈ Set.uIcc (-connector.rootModel.L) connector.rootModel.L := by
    rw [hrootL]
    exact Set.right_mem_uIcc
  have hnegLmem : -L' ∈ Set.uIcc (-connector.rootModel.L) connector.rootModel.L := by
    rw [hrootL]
    exact Set.left_mem_uIcc
  have hinitCont := continuousAt_chapterVIDEndpointDerivativeValue connector.rootModel
    .initial L' hLmem hnegLmem
  have hfinalCont := continuousAt_chapterVIDEndpointDerivativeValue connector.rootModel
    .final L' hLmem hnegLmem
  have hinitRealCont :=
    continuousAt_chapterVIDEndpointRealDerivativeValue connector.rootModel
      .initial L' hLmem hnegLmem
  have hfinalRealCont :=
    continuousAt_chapterVIDEndpointRealDerivativeValue connector.rootModel
      .final L' hLmem hnegLmem
  have hinitAt : 0 < chapterVIDEndpointDerivativeValue .initial 0 L' := by
    simpa using hbaseSigns.1.1
  have hfinalAt : 0 < chapterVIDEndpointDerivativeValue .final 0 L' := by
    simpa using hbaseSigns.1.2
  have hinitRealAt : chapterVIDEndpointRealDerivativeValue .initial 0 L' < 0 := by
    simpa using hbaseSigns.2.1
  have hfinalRealAt : 0 < chapterVIDEndpointRealDerivativeValue .final 0 L' := by
    simpa using hbaseSigns.2.2
  have hpositive : ∀ᶠ k : ℝ in nhds 0,
      (0 < chapterVIDEndpointDerivativeValue .initial k L' ∧
        0 < chapterVIDEndpointDerivativeValue .final k L') ∧
      (chapterVIDEndpointRealDerivativeValue .initial k L' < 0 ∧
        0 < chapterVIDEndpointRealDerivativeValue .final k L') :=
    ((hinitCont.eventually (Ioi_mem_nhds hinitAt)).and
      (hfinalCont.eventually (Ioi_mem_nhds hfinalAt))).and
    ((hinitRealCont.eventually (Iio_mem_nhds hinitRealAt)).and
      (hfinalRealCont.eventually (Ioi_mem_nhds hfinalRealAt)))
  have hk0 : (0 : ℝ) ∈ Set.Icc 0 connector.rootModel.δ :=
    ⟨le_rfl, connector.rootModel.δ_pos.le⟩
  have hparameterRootContinuous : ContinuousAt
      (fun k : ℝ ↦ chapterVIDCriticalParameterRootAtD (k : ℂ)) 0 :=
    (connector.rootModel.parameterRoot_analyticAt 0 hk0).continuousAt.comp_of_eq
      Complex.continuous_ofReal.continuousAt rfl
  have hrelativeContinuous : ContinuousAt
      (fun k : ℝ ↦ ‖chapterVIDCriticalParameterRootAtD (k : ℂ) /
        chapterVIDZRootBase - 1‖) 0 :=
    ((hparameterRootContinuous.div_const chapterVIDZRootBase).sub_const 1).norm
  have hrelativeAt :
      ‖chapterVIDCriticalParameterRootAtD ((0 : ℝ) : ℂ) /
        chapterVIDZRootBase - 1‖ < L' ^ 2 := by
    simp [chapterVIDZRootBase_ne_zero, sq_pos_of_pos hL']
  have hrelativeSmall : ∀ᶠ k : ℝ in nhds 0,
      ‖chapterVIDCriticalParameterRootAtD (k : ℂ) /
        chapterVIDZRootBase - 1‖ < L' ^ 2 :=
    hrelativeContinuous.eventually (Iio_mem_nhds hrelativeAt)
  have hinitDirectionContinuous : ContinuousAt
      (fun k : ℝ ↦ ‖chapterVIDNormalizedLocalEndpointDelta .initial k L' -
        deriv chapterVIDGlobalContourFromMorse 0‖) 0 := by
    have h := connector.rootModel.continuousAt_normalizedLocalEndpointDelta_zero .initial
    rw [hrootL] at h
    exact (h.sub_const _).norm
  have hfinalDirectionContinuous : ContinuousAt
      (fun k : ℝ ↦ ‖chapterVIDNormalizedLocalEndpointDelta .final k L' -
        deriv chapterVIDGlobalContourFromMorse 0‖) 0 := by
    have h := connector.rootModel.continuousAt_normalizedLocalEndpointDelta_zero .final
    rw [hrootL] at h
    exact (h.sub_const _).norm
  have hdirectional : ∀ᶠ k : ℝ in nhds 0,
      ‖chapterVIDNormalizedLocalEndpointDelta .initial k L' -
          deriv chapterVIDGlobalContourFromMorse 0‖ <
            -(deriv chapterVIDGlobalContourFromMorse 0).im / 2 ∧
      ‖chapterVIDNormalizedLocalEndpointDelta .final k L' -
          deriv chapterVIDGlobalContourFromMorse 0‖ <
            -(deriv chapterVIDGlobalContourFromMorse 0).im / 2 :=
    (hinitDirectionContinuous.eventually (Iio_mem_nhds hinitialDirectionAtZero)).and
      (hfinalDirectionContinuous.eventually (Iio_mem_nhds hfinalDirectionAtZero))
  have hinitialOuterContinuous : ContinuousAt
      (fun k : ℝ ↦ ‖connector.rootModel.outerConnectorEndpoint .initial k -
        connector.rootModel.outerConnectorEndpoint .initial 0‖) 0 :=
    ((connector.rootModel.continuousAt_outerConnectorEndpoint_zero .initial).sub_const _).norm
  have hfinalOuterContinuous : ContinuousAt
      (fun k : ℝ ↦ ‖connector.rootModel.outerConnectorEndpoint .final k -
        connector.rootModel.outerConnectorEndpoint .final 0‖) 0 :=
    ((connector.rootModel.continuousAt_outerConnectorEndpoint_zero .final).sub_const _).norm
  have houterSmall : ∀ᶠ k : ℝ in nhds 0,
      ‖connector.rootModel.outerConnectorEndpoint .initial k -
          connector.rootModel.outerConnectorEndpoint .initial 0‖ < L' ^ 2 ∧
      ‖connector.rootModel.outerConnectorEndpoint .final k -
          connector.rootModel.outerConnectorEndpoint .final 0‖ < L' ^ 2 :=
    (hinitialOuterContinuous.eventually
      (Iio_mem_nhds (by simpa using sq_pos_of_pos hL'))).and
    (hfinalOuterContinuous.eventually
      (Iio_mem_nhds (by simpa using sq_pos_of_pos hL')))
  obtain ⟨εk, hεk, hkBall⟩ := Metric.mem_nhds_iff.mp
    (((hpositive.and hrelativeSmall).and hdirectional).and houterSmall)
  let κ' := min (min (min connector.κ (εk / 2)) (κmax / 2)) (L' ^ 2)
  have hκ' : 0 < κ' := by
    dsimp [κ']
    exact lt_min
      (lt_min (lt_min connector.κ_pos (by positivity))
        (div_pos hκmaxPos (by norm_num)))
      (sq_pos_of_pos hL')
  have hκle : κ' ≤ connector.κ :=
    (min_le_left _ _).trans
      ((min_le_left _ _).trans (min_le_left _ _))
  have hκmax : κ' ≤ κmax := by
    exact (min_le_left _ _).trans
      ((min_le_right _ _).trans (by linarith [hκmaxPos]))
  have hκscale : κ' ≤ L' ^ 2 := min_le_right _ _
  have hκSigns :
      (0 < chapterVIDEndpointDerivativeValue .initial κ' L' ∧
        0 < chapterVIDEndpointDerivativeValue .final κ' L') ∧
      (chapterVIDEndpointRealDerivativeValue .initial κ' L' < 0 ∧
        0 < chapterVIDEndpointRealDerivativeValue .final κ' L') := by
    exact (hkBall (by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hκ']
      have := (min_le_left (min (min connector.κ (εk / 2)) (κmax / 2)) (L' ^ 2)).trans
        ((min_le_left (min connector.κ (εk / 2)) (κmax / 2)).trans
          (min_le_right connector.κ (εk / 2)))
      linarith)).1.1.1
  have hκRelative :
      ‖chapterVIDCriticalParameterRootAtD (κ' : ℂ) /
        chapterVIDZRootBase - 1‖ ≤ L' ^ 2 := by
    exact (hkBall (by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hκ']
      have := (min_le_left (min (min connector.κ (εk / 2)) (κmax / 2)) (L' ^ 2)).trans
        ((min_le_left (min connector.κ (εk / 2)) (κmax / 2)).trans
          (min_le_right connector.κ (εk / 2)))
      linarith)).1.1.2.le
  have hκDirectional :
      ‖chapterVIDNormalizedLocalEndpointDelta .initial κ' L' -
          deriv chapterVIDGlobalContourFromMorse 0‖ <
            -(deriv chapterVIDGlobalContourFromMorse 0).im / 2 ∧
      ‖chapterVIDNormalizedLocalEndpointDelta .final κ' L' -
          deriv chapterVIDGlobalContourFromMorse 0‖ <
            -(deriv chapterVIDGlobalContourFromMorse 0).im / 2 := by
    exact (hkBall (by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hκ']
      have := (min_le_left (min (min connector.κ (εk / 2)) (κmax / 2)) (L' ^ 2)).trans
        ((min_le_left (min connector.κ (εk / 2)) (κmax / 2)).trans
          (min_le_right connector.κ (εk / 2)))
      linarith)).1.2
  have hκOuter : ∀ side : ChapterVIDOuterArcSide,
      ‖connector.rootModel.outerConnectorEndpoint side κ' -
        connector.rootModel.outerConnectorEndpoint side 0‖ ≤ L' ^ 2 := by
    have h := (hkBall (by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hκ']
      have := (min_le_left (min (min connector.κ (εk / 2)) (κmax / 2)) (L' ^ 2)).trans
        ((min_le_left (min connector.κ (εk / 2)) (κmax / 2)).trans
          (min_le_right connector.κ (εk / 2)))
      linarith)).2
    intro side
    cases side with
    | initial => exact h.1.le
    | final => exact h.2.le
  let restrictedConnector := connector.restrictParameter κ' hκ' hκle
  let restrictedOriented : ChapterVIDOrientedConnectorModel massProduct b d := {
    toChapterVIDPrincipalConnectorModel := restrictedConnector
    rootFiberDerivative_im_neg := orientedConnector.rootFiberDerivative_im_neg
    rootCenter_im_zero := orientedConnector.rootCenter_im_zero }
  refine ⟨{
    toChapterVIDOrientedConnectorModel := restrictedOriented
    initialAnchor := ⟨?_⟩
    finalAnchor := ⟨?_⟩
    initialRealAnchor := ?_
    finalRealAnchor := ?_
    parameter_le_length_sq := ?_
    parameterRootRelativeDelta_norm_le_length_sq := ?_
    outerEndpointDelta_norm_le_length_sq := ?_
    initialNormalizedLocalDelta_mem_directionCone := ?_
    finalNormalizedLocalDelta_mem_directionCone := ?_ }, ?_, ?_⟩
  · rw [lineDerivativeImag_local_eq_chapterVIDEndpointDerivativeValue]
    dsimp only [restrictedOriented, restrictedConnector,
      ChapterVIDPrincipalConnectorModel.restrictParameter]
    rw [hrootL]
    exact hκSigns.1.1.le
  · rw [lineDerivativeImag_local_eq_chapterVIDEndpointDerivativeValue]
    dsimp only [restrictedOriented, restrictedConnector,
      ChapterVIDPrincipalConnectorModel.restrictParameter]
    rw [hrootL]
    exact hκSigns.1.2.le
  · dsimp only [restrictedOriented, restrictedConnector,
      ChapterVIDPrincipalConnectorModel.restrictParameter]
    rw [hrootL]
    exact hκSigns.2.1
  · dsimp only [restrictedOriented, restrictedConnector,
      ChapterVIDPrincipalConnectorModel.restrictParameter]
    rw [hrootL]
    exact hκSigns.2.2
  · dsimp only [restrictedOriented, restrictedConnector,
      ChapterVIDPrincipalConnectorModel.restrictParameter]
    rw [hrootL]
    exact hκscale
  · dsimp only [restrictedOriented, restrictedConnector,
      ChapterVIDPrincipalConnectorModel.restrictParameter,
      ChapterVIDPrincipalConnectorModel.connectorParameterRoot,
      ChapterVIDPrincipalConnectorModel.criticalValue]
    rw [hrootL]
    simpa using hκRelative
  · intro side
    dsimp only [restrictedOriented, restrictedConnector,
      ChapterVIDPrincipalConnectorModel.restrictParameter]
    rw [hrootL]
    exact hκOuter side
  · dsimp only [restrictedOriented, restrictedConnector,
      ChapterVIDPrincipalConnectorModel.restrictParameter]
    rw [hrootL]
    exact hκDirectional.1
  · dsimp only [restrictedOriented, restrictedConnector,
      ChapterVIDPrincipalConnectorModel.restrictParameter]
    rw [hrootL]
    exact hκDirectional.2
  · dsimp only [restrictedOriented, restrictedConnector,
      ChapterVIDPrincipalConnectorModel.restrictParameter]
    rw [hrootL]
    exact hLmax
  · dsimp only [restrictedOriented, restrictedConnector,
      ChapterVIDPrincipalConnectorModel.restrictParameter]
    exact hκmax

/-- The inverse-Morse endpoint input required by a compiled certificate can be made smaller than
any prescribed positive real radius.  This is the quantitative bridge from analyticity to a
fixed rational box: a campaign first chooses its dyadic radius, then invokes this selector. -/
theorem exists_chapterVIDAnchoredConnectorModel_with_local_endpoint_bound
    (massProduct : ℂ) (b d : ℤ)
    (Lmax κmax endpointRadius : ℝ)
    (hLmaxPos : 0 < Lmax) (hκmaxPos : 0 < κmax)
    (hEndpointRadiusPos : 0 < endpointRadius) :
    ∃ model : ChapterVIDAnchoredConnectorModel massProduct b d,
      model.toChapterVIDPrincipalConnectorModel.rootModel.L ≤ Lmax ∧
      model.toChapterVIDPrincipalConnectorModel.κ ≤ κmax ∧
      (∀ side : ChapterVIDOuterArcSide,
        ‖model.toChapterVIDPrincipalConnectorModel.rootModel.localConnectorEndpoint side
            (model.toChapterVIDPrincipalConnectorModel.criticalValue 0) -
          chapterVIDCollisionLift‖ ≤ endpointRadius) := by
  obtain ⟨C, hC, hrootEventually⟩ :=
    eventually_norm_chapterVIDCriticalMorseRootPoint_sub_collision_le
  obtain ⟨ε, hε, hrootBall⟩ := Metric.mem_nhds_iff.mp hrootEventually
  let selectedLmax :=
    min Lmax (min (ε / 2) (min (1 / 2) (endpointRadius / (2 * C))))
  have hselectedLmax : 0 < selectedLmax := by
    dsimp only [selectedLmax]
    exact lt_min hLmaxPos
      (lt_min (div_pos hε (by norm_num))
        (lt_min (by norm_num) (div_pos hEndpointRadiusPos (mul_pos (by norm_num) hC))))
  obtain ⟨model, hmodelL, hmodelK⟩ :=
    exists_chapterVIDAnchoredConnectorModel_bounded massProduct b d selectedLmax κmax
      hselectedLmax hκmaxPos
  have hLmax : model.toChapterVIDPrincipalConnectorModel.rootModel.L ≤ Lmax :=
    hmodelL.trans (min_le_left _ _)
  have hLepsilon : model.toChapterVIDPrincipalConnectorModel.rootModel.L ≤ ε / 2 :=
    hmodelL.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hLhalf : model.toChapterVIDPrincipalConnectorModel.rootModel.L ≤ 1 / 2 :=
    hmodelL.trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))
  have hLradius : model.toChapterVIDPrincipalConnectorModel.rootModel.L ≤
      endpointRadius / (2 * C) :=
    hmodelL.trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _)))
  have hkLeL : model.toChapterVIDPrincipalConnectorModel.κ ≤
      model.toChapterVIDPrincipalConnectorModel.rootModel.L := by
    calc
      model.toChapterVIDPrincipalConnectorModel.κ ≤
          model.toChapterVIDPrincipalConnectorModel.rootModel.L ^ 2 :=
        model.parameter_le_length_sq
      _ ≤ model.toChapterVIDPrincipalConnectorModel.rootModel.L := by
        nlinarith [model.toChapterVIDPrincipalConnectorModel.rootModel.L_pos]
  have hCL : C * model.toChapterVIDPrincipalConnectorModel.rootModel.L ≤ endpointRadius := by
    calc
      C * model.toChapterVIDPrincipalConnectorModel.rootModel.L ≤
          C * (endpointRadius / (2 * C)) :=
        mul_le_mul_of_nonneg_left hLradius hC.le
      _ = endpointRadius / 2 := by field_simp [hC.ne']
      _ ≤ endpointRadius := by linarith
  refine ⟨model, hLmax, hmodelK, ?_⟩
  intro side
  have hpointNorm (v : ℂ) (hv : ‖v‖ =
      model.toChapterVIDPrincipalConnectorModel.rootModel.L) :
      ‖((model.toChapterVIDPrincipalConnectorModel.κ : ℂ), v)‖ =
        model.toChapterVIDPrincipalConnectorModel.rootModel.L := by
    rw [Prod.norm_def, hv]
    simp only [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos model.toChapterVIDPrincipalConnectorModel.κ_pos]
    exact max_eq_right hkLeL
  have hinitialNorm :
      ‖((model.toChapterVIDPrincipalConnectorModel.κ : ℂ),
          ((-model.toChapterVIDPrincipalConnectorModel.rootModel.L : ℝ) : ℂ))‖ =
        model.toChapterVIDPrincipalConnectorModel.rootModel.L := by
    apply hpointNorm
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_neg,
      abs_of_pos model.toChapterVIDPrincipalConnectorModel.rootModel.L_pos]
  have hfinalNorm :
      ‖((model.toChapterVIDPrincipalConnectorModel.κ : ℂ),
          (model.toChapterVIDPrincipalConnectorModel.rootModel.L : ℂ))‖ =
        model.toChapterVIDPrincipalConnectorModel.rootModel.L := by
    apply hpointNorm
    simp only [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos model.toChapterVIDPrincipalConnectorModel.rootModel.L_pos]
  have hinitialMem :
      ((model.toChapterVIDPrincipalConnectorModel.κ : ℂ),
          ((-model.toChapterVIDPrincipalConnectorModel.rootModel.L : ℝ) : ℂ)) ∈
        Metric.ball ((0, 0) : ℂ × ℂ) ε := by
    rw [Metric.mem_ball]
    have hzero : ((0, 0) : ℂ × ℂ) = 0 := rfl
    rw [hzero, dist_zero_right]
    rw [hinitialNorm]
    linarith
  have hfinalMem :
      ((model.toChapterVIDPrincipalConnectorModel.κ : ℂ),
          (model.toChapterVIDPrincipalConnectorModel.rootModel.L : ℂ)) ∈
        Metric.ball ((0, 0) : ℂ × ℂ) ε := by
    rw [Metric.mem_ball]
    have hzero : ((0, 0) : ℂ × ℂ) = 0 := rfl
    rw [hzero, dist_zero_right]
    rw [hfinalNorm]
    linarith
  cases side with
  | initial =>
      have hbound := hrootBall hinitialMem
      change ‖chapterVIDCriticalMorseRootPoint
          ((model.toChapterVIDPrincipalConnectorModel.κ : ℂ),
            ((-model.toChapterVIDPrincipalConnectorModel.rootModel.L : ℝ) : ℂ)) -
          chapterVIDCollisionLift‖ ≤ C *
            ‖((model.toChapterVIDPrincipalConnectorModel.κ : ℂ),
              ((-model.toChapterVIDPrincipalConnectorModel.rootModel.L : ℝ) : ℂ))‖ at hbound
      rw [hinitialNorm] at hbound
      simpa only [ChapterVIDPrincipalGlobalRootModel.localConnectorEndpoint,
        ChapterVIDPrincipalConnectorModel.criticalValue_zero] using
        hbound.trans hCL
  | final =>
      have hbound := hrootBall hfinalMem
      change ‖chapterVIDCriticalMorseRootPoint
          ((model.toChapterVIDPrincipalConnectorModel.κ : ℂ),
            (model.toChapterVIDPrincipalConnectorModel.rootModel.L : ℂ)) -
          chapterVIDCollisionLift‖ ≤ C *
            ‖((model.toChapterVIDPrincipalConnectorModel.κ : ℂ),
              (model.toChapterVIDPrincipalConnectorModel.rootModel.L : ℂ))‖ at hbound
      rw [hfinalNorm] at hbound
      simpa only [ChapterVIDPrincipalGlobalRootModel.localConnectorEndpoint,
        ChapterVIDPrincipalConnectorModel.criticalValue_zero] using
        hbound.trans hCL

/-- An anchored connector exists without prescribing numerical bounds.  The bounded form above is
the one used by a concrete finite campaign; this compatibility wrapper preserves the simpler
analytic API. -/
theorem exists_chapterVIDAnchoredConnectorModel
    (massProduct : ℂ) (b d : ℤ) :
    Nonempty (ChapterVIDAnchoredConnectorModel massProduct b d) := by
  obtain ⟨model, _, _⟩ :=
    exists_chapterVIDAnchoredConnectorModel_bounded massProduct b d 1 1
      (by norm_num) (by norm_num)
  exact ⟨model⟩

/-- The selected anchors discharge the sole analytic hypothesis of the compiled 30-cell
terminal campaign. Thus the literal first-factor path derivative is strictly positive at every
non-endpoint point of either terminal interval. -/
theorem ChapterVIDAnchoredConnectorModel.terminalLineDerivativeImag_pos
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDAnchoredConnectorModel massProduct b d)
    (run :
      ChapterVIDConnectorFactorSecondDerivativeReference.ReferenceCompiledRunVerdict)
    (side : ChapterVIDOuterArcSide)
    (x : ℝ)
    (hx : x ∈ ChapterVIDConnectorFactorTerminal.terminalInterval side)
    (hne : x ≠
      (ChapterVIDConnectorSeamCompiledGrid.localParameter side : ℝ)) :
    0 < ChapterVIDConnectorFactorTerminal.lineDerivativeImag
      model.toChapterVIDPrincipalConnectorModel side x := by
  cases side with
  | initial =>
      exact ChapterVIDConnectorFactorTerminal.ReferenceCompiledRunVerdict.lineDerivativeImag_pos_of_anchor
        run
        model.toChapterVIDPrincipalConnectorModel .initial
        model.initialAnchor x hx hne
  | final =>
      exact ChapterVIDConnectorFactorTerminal.ReferenceCompiledRunVerdict.lineDerivativeImag_pos_of_anchor
        run
        model.toChapterVIDPrincipalConnectorModel .final
        model.finalAnchor x hx hne

end PoincareChapterVI
