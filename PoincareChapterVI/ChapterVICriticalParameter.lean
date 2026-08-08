/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import PoincareChapterVI.ChapterVIMorseAmplitude

/-!
# Using the moving critical value as Poincaré's pinch parameter

Poincaré's local formula uses the constant term `k` of the quadratic as the external parameter.
The source construction first produces it as the analytic critical value `k(z)`.  Provided the
finite transversality check `k'(z_D) ≠ 0`, the complex inverse function theorem makes `k` itself a
local coordinate.  In the resulting `(k,v)` chart the literal source radicand is exactly `k+v²`.

The nonzero-derivative premise is intentionally visible: for the concrete point D it is a finite
source-algebra calculation suitable for a LeanCompCert certificate, while the inverse-function
and analytic conclusions remain ordinary kernel-checked mathematics.
-/

noncomputable section

open Filter Set
open scoped Topology

namespace PoincareChapterVI

/-- The source-algebra quantity whose nonvanishing makes the collision transverse to the external
`z` parameter.  It is the first-coordinate partial derivative of the literal radicand at D. -/
def chapterVIDParameterDerivative : ℂ :=
  fderiv ℂ chapterVIDRadicand (chapterVIDZBase, chapterVIDTBase) (1, 0)

/-- Because the chosen center is fiber-critical, differentiating the critical value along the
center kills the center-motion term.  Thus the only finite transversality calculation required is
the first-coordinate partial derivative of the original source radicand. -/
theorem deriv_chapterVIDCriticalValue_eq_parameterDerivative :
    deriv chapterVIDCriticalValue chapterVIDZBase =
      chapterVIDParameterDerivative := by
  have hcenterDeriv :=
    analyticAt_chapterVIDCriticalCenter.hasStrictDerivAt.hasDerivAt
  have hpair : HasDerivAt
      (fun z : ℂ ↦ (z, chapterVIDCriticalCenter z))
      (1, deriv chapterVIDCriticalCenter chapterVIDZBase) chapterVIDZBase :=
    (hasDerivAt_id chapterVIDZBase).prodMk hcenterDeriv
  have hradicand : HasFDerivAt chapterVIDRadicand
      (fderiv ℂ chapterVIDRadicand (chapterVIDZBase, chapterVIDTBase))
      (chapterVIDZBase, chapterVIDCriticalCenter chapterVIDZBase) := by
    simpa only [chapterVIDCriticalCenter_base] using
      analyticAt_chapterVIDRadicand.hasStrictFDerivAt.hasFDerivAt
  have hcriticalDeriv :=
    hradicand.comp_hasDerivAt chapterVIDZBase hpair
  have hfiberZero :
      fderiv ℂ chapterVIDRadicand (chapterVIDZBase, chapterVIDTBase) (0, 1) = 0 := by
    have hzero :=
      eventually_chapterVIDCriticalCenter_fiberDerivative_eq_zero.self_of_nhds
    rw [chapterVIDCriticalCenter_base] at hzero
    exact hzero
  have hlinear :
      fderiv ℂ chapterVIDRadicand (chapterVIDZBase, chapterVIDTBase)
          (1, deriv chapterVIDCriticalCenter chapterVIDZBase) =
      fderiv ℂ chapterVIDRadicand (chapterVIDZBase, chapterVIDTBase) (1, 0) := by
    have hvector :
        ((1 : ℂ), deriv chapterVIDCriticalCenter chapterVIDZBase) =
          ((1 : ℂ), (0 : ℂ)) +
            deriv chapterVIDCriticalCenter chapterVIDZBase •
              ((0 : ℂ), (1 : ℂ)) := by
      ext <;> simp
    rw [hvector]
    rw [map_add, map_smul, hfiberZero]
    simp
  unfold chapterVIDParameterDerivative
  rw [← hlinear]
  unfold chapterVIDCriticalValue
  simpa only [Function.comp_def] using hcriticalDeriv.deriv

/-- The local inverse `k ↦ z(k)` of the moving critical value, conditional on transversality. -/
def chapterVIDCriticalParameterInverse
    (htransverse : deriv chapterVIDCriticalValue chapterVIDZBase ≠ 0) : ℂ → ℂ :=
  analyticAt_chapterVIDCriticalValue.hasStrictDerivAt.localInverse
    chapterVIDCriticalValue
    (deriv chapterVIDCriticalValue chapterVIDZBase)
    chapterVIDZBase htransverse

@[simp]
theorem chapterVIDCriticalParameterInverse_zero
    (htransverse : deriv chapterVIDCriticalValue chapterVIDZBase ≠ 0) :
    chapterVIDCriticalParameterInverse htransverse 0 = chapterVIDZBase := by
  have hleft :=
    (analyticAt_chapterVIDCriticalValue.hasStrictDerivAt.eventually_left_inverse
      htransverse).self_of_nhds
  unfold chapterVIDCriticalParameterInverse
  simpa only [chapterVIDCriticalValue_base] using hleft

/-- The critical value of `z(k)` is locally exactly `k`. -/
theorem eventually_chapterVIDCriticalValue_criticalParameterInverse
    (htransverse : deriv chapterVIDCriticalValue chapterVIDZBase ≠ 0) :
    ∀ᶠ k in 𝓝 (0 : ℂ),
      chapterVIDCriticalValue
        (chapterVIDCriticalParameterInverse htransverse k) = k := by
  unfold chapterVIDCriticalParameterInverse
  simpa only [chapterVIDCriticalValue_base] using
    (analyticAt_chapterVIDCriticalValue.hasStrictDerivAt.eventually_right_inverse
      htransverse)

/-- The inverse critical-parameter coordinate is analytic at the singular value. -/
theorem analyticAt_chapterVIDCriticalParameterInverse
    (htransverse : deriv chapterVIDCriticalValue chapterVIDZBase ≠ 0) :
    AnalyticAt ℂ (chapterVIDCriticalParameterInverse htransverse) 0 := by
  simpa only [chapterVIDCriticalParameterInverse, chapterVIDCriticalValue_base] using
    analyticAt_chapterVIDCriticalValue.analyticAt_localInverse htransverse

/-- Its derivative is the reciprocal of `k'(z_D)`. -/
theorem hasDerivAt_chapterVIDCriticalParameterInverse
    (htransverse : deriv chapterVIDCriticalValue chapterVIDZBase ≠ 0) :
    HasDerivAt (chapterVIDCriticalParameterInverse htransverse)
      (deriv chapterVIDCriticalValue chapterVIDZBase)⁻¹ 0 := by
  simpa only [chapterVIDCriticalParameterInverse, chapterVIDCriticalValue_base] using
    analyticAt_chapterVIDCriticalValue.hasStrictDerivAt.to_localInverse htransverse
      |>.hasDerivAt

/-- Joint change from Poincaré's `(k,v)` normal coordinates back to `(z,v)`. -/
def chapterVIDCriticalMorseParameterMap
    (htransverse : deriv chapterVIDCriticalValue chapterVIDZBase ≠ 0)
    (point : ℂ × ℂ) : ℂ × ℂ :=
  (chapterVIDCriticalParameterInverse htransverse point.1, point.2)

@[simp]
theorem chapterVIDCriticalMorseParameterMap_base
    (htransverse : deriv chapterVIDCriticalValue chapterVIDZBase ≠ 0) :
    chapterVIDCriticalMorseParameterMap htransverse (0, 0) =
      (chapterVIDZBase, 0) := by
  simp [chapterVIDCriticalMorseParameterMap]

theorem analyticAt_chapterVIDCriticalMorseParameterMap
    (htransverse : deriv chapterVIDCriticalValue chapterVIDZBase ≠ 0) :
    AnalyticAt ℂ (chapterVIDCriticalMorseParameterMap htransverse) (0, 0) := by
  have hfst : AnalyticAt ℂ (fun point : ℂ × ℂ ↦ point.1) (0, 0) :=
    analyticAt_fst
  have hfirst : AnalyticAt ℂ (fun point : ℂ × ℂ ↦
      chapterVIDCriticalParameterInverse htransverse point.1) (0, 0) := by
    simpa only [Function.comp_def] using
      (analyticAt_chapterVIDCriticalParameterInverse htransverse).comp_of_eq hfst rfl
  have hsecond : AnalyticAt ℂ (fun point : ℂ × ℂ ↦ point.2) (0, 0) :=
    analyticAt_snd
  unfold chapterVIDCriticalMorseParameterMap
  exact hfirst.prod hsecond

/-- The original source point expressed directly in the true quadratic parameters `(k,v)`. -/
def chapterVIDCriticalMorseSourcePoint
    (htransverse : deriv chapterVIDCriticalValue chapterVIDZBase ≠ 0)
    (point : ℂ × ℂ) : ℂ × ℂ :=
  chapterVIDMorseSourcePoint
    (chapterVIDCriticalMorseParameterMap htransverse point)

@[simp]
theorem chapterVIDCriticalMorseSourcePoint_base
    (htransverse : deriv chapterVIDCriticalValue chapterVIDZBase ≠ 0) :
    chapterVIDCriticalMorseSourcePoint htransverse (0, 0) =
      (chapterVIDZBase, chapterVIDTBase) := by
  simp [chapterVIDCriticalMorseSourcePoint]

theorem analyticAt_chapterVIDCriticalMorseSourcePoint
    (htransverse : deriv chapterVIDCriticalValue chapterVIDZBase ≠ 0) :
    AnalyticAt ℂ (chapterVIDCriticalMorseSourcePoint htransverse) (0, 0) := by
  exact analyticAt_chapterVIDMorseSourcePoint.comp_of_eq
    (analyticAt_chapterVIDCriticalMorseParameterMap htransverse)
    (chapterVIDCriticalMorseParameterMap_base htransverse)

/-- After replacing `z` by the actual critical value `k`, the literal Poincaré source radicand is
exactly `k+v²` on a neighborhood of the pinch. -/
theorem eventually_chapterVIDRadicand_criticalMorseSourcePoint_eq
    (htransverse : deriv chapterVIDCriticalValue chapterVIDZBase ≠ 0) :
    ∀ᶠ point in 𝓝 ((0 : ℂ), (0 : ℂ)),
      chapterVIDRadicand
          (chapterVIDCriticalMorseSourcePoint htransverse point) =
        point.1 + point.2 ^ 2 := by
  have htendsto : Tendsto (chapterVIDCriticalMorseParameterMap htransverse)
      (𝓝 ((0 : ℂ), (0 : ℂ))) (𝓝 (chapterVIDZBase, (0 : ℂ))) :=
    by
      have hcontinuous :=
        (analyticAt_chapterVIDCriticalMorseParameterMap htransverse).continuousAt
      change Tendsto (chapterVIDCriticalMorseParameterMap htransverse)
        (𝓝 ((0 : ℂ), (0 : ℂ)))
        (𝓝 (chapterVIDCriticalMorseParameterMap htransverse (0, 0))) at hcontinuous
      rw [chapterVIDCriticalMorseParameterMap_base] at hcontinuous
      exact hcontinuous
  have hnormal := htendsto.eventually
    eventually_chapterVIDRadicand_morseSourcePoint_eq
  have hright : ∀ᶠ point in 𝓝 ((0 : ℂ), (0 : ℂ)),
      chapterVIDCriticalValue
          (chapterVIDCriticalParameterInverse htransverse point.1) = point.1 :=
    by
      have hfst : Tendsto (fun point : ℂ × ℂ ↦ point.1)
          (𝓝 ((0 : ℂ), (0 : ℂ))) (𝓝 (0 : ℂ)) := continuousAt_fst
      exact hfst.eventually
        (eventually_chapterVIDCriticalValue_criticalParameterInverse htransverse)
  filter_upwards [hnormal, hright] with point hnormalPoint hrightPoint
  simpa only [chapterVIDCriticalMorseSourcePoint,
    chapterVIDCriticalMorseParameterMap] using hnormalPoint.trans
      (congrArg (fun value ↦ value + point.2 ^ 2) hrightPoint)

/-- The complete analytic numerator and differential amplitude in `(k,v)` coordinates. -/
def chapterVIDCriticalMorseAmplitude
    (htransverse : deriv chapterVIDCriticalValue chapterVIDZBase ≠ 0)
    (sourceAmplitude : ℂ × ℂ → ℂ) (point : ℂ × ℂ) : ℂ :=
  chapterVIDMorseAmplitude sourceAmplitude
    (chapterVIDCriticalMorseParameterMap htransverse point)

theorem analyticAt_chapterVIDCriticalMorseAmplitude
    (htransverse : deriv chapterVIDCriticalValue chapterVIDZBase ≠ 0)
    {sourceAmplitude : ℂ × ℂ → ℂ}
    (hsource : AnalyticAt ℂ sourceAmplitude
      (chapterVIDZBase, chapterVIDTBase)) :
    AnalyticAt ℂ
      (chapterVIDCriticalMorseAmplitude htransverse sourceAmplitude) (0, 0) := by
  exact (analyticAt_chapterVIDMorseAmplitude hsource).comp_of_eq
    (analyticAt_chapterVIDCriticalMorseParameterMap htransverse)
    (chapterVIDCriticalMorseParameterMap_base htransverse)

theorem chapterVIDCriticalMorseAmplitude_base
    (htransverse : deriv chapterVIDCriticalValue chapterVIDZBase ≠ 0)
    (sourceAmplitude : ℂ × ℂ → ℂ) :
    chapterVIDCriticalMorseAmplitude htransverse sourceAmplitude (0, 0) =
      sourceAmplitude (chapterVIDZBase, chapterVIDTBase) *
        chapterVIDMorseRootBase⁻¹ := by
  simp [chapterVIDCriticalMorseAmplitude, chapterVIDMorseAmplitude_base]

end PoincareChapterVI
