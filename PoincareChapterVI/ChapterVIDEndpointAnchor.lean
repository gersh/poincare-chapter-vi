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
      toChapterVIDOrientedConnectorModel.toChapterVIDPrincipalConnectorModel.rootModel.L ≤ 0
  finalRealAnchor :
    0 ≤ chapterVIDEndpointRealDerivativeValue .final
      toChapterVIDOrientedConnectorModel.toChapterVIDPrincipalConnectorModel.κ
      toChapterVIDOrientedConnectorModel.toChapterVIDPrincipalConnectorModel.rootModel.L

theorem exists_chapterVIDAnchoredConnectorModel
    (massProduct : ℂ) (b d : ℤ) :
    Nonempty (ChapterVIDAnchoredConnectorModel massProduct b d) := by
  obtain ⟨oriented⟩ := exists_chapterVIDOrientedGlobalRootModel massProduct b d
  have hlengthEventually :=
    (eventually_chapterVIDInitialBaseEndpointDerivative_pos.and
      eventually_chapterVIDFinalBaseEndpointDerivative_pos).and
    (eventually_chapterVIDInitialBaseEndpointRealDerivative_neg.and
      eventually_chapterVIDFinalBaseEndpointRealDerivative_pos)
  obtain ⟨εL, hεL, hlengthBall⟩ := Metric.mem_nhdsWithin_iff.mp hlengthEventually
  let L' := min (oriented.L / 2) (εL / 2)
  have hL' : 0 < L' := by
    dsimp [L']
    exact lt_min (div_pos oriented.L_pos (by norm_num))
      (div_pos hεL (by norm_num))
  have hLle : L' ≤ oriented.L := by
    exact (min_le_left _ _).trans (by linarith [oriented.L_pos])
  have hLball : L' ∈ Metric.ball (0 : ℝ) εL := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hL']
    have := min_le_right (oriented.L / 2) (εL / 2)
    linarith
  have hbaseSigns :
      (0 < chapterVIDInitialBaseEndpointDerivative L' ∧
        0 < chapterVIDFinalBaseEndpointDerivative L') ∧
      (chapterVIDInitialBaseEndpointRealDerivative L' < 0 ∧
        0 < chapterVIDFinalBaseEndpointRealDerivative L') :=
    hlengthBall ⟨hLball, hL'⟩
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
  obtain ⟨εk, hεk, hkBall⟩ := Metric.mem_nhds_iff.mp hpositive
  let κ' := min connector.κ (εk / 2)
  have hκ' : 0 < κ' := by
    dsimp [κ']
    exact lt_min connector.κ_pos (by positivity)
  have hκle : κ' ≤ connector.κ := min_le_left _ _
  have hκSigns :
      (0 < chapterVIDEndpointDerivativeValue .initial κ' L' ∧
        0 < chapterVIDEndpointDerivativeValue .final κ' L') ∧
      (chapterVIDEndpointRealDerivativeValue .initial κ' L' < 0 ∧
        0 < chapterVIDEndpointRealDerivativeValue .final κ' L') := by
    apply hkBall
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hκ']
    have := min_le_right connector.κ (εk / 2)
    linarith
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
    finalRealAnchor := ?_ }⟩
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
    exact hκSigns.2.1.le
  · dsimp only [restrictedOriented, restrictedConnector,
      ChapterVIDPrincipalConnectorModel.restrictParameter]
    rw [hrootL]
    exact hκSigns.2.2.le

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
