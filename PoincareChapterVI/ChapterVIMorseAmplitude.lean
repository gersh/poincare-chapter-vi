/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.ChapterVIContourTransport
import PoincareChapterVI.ChapterVIParametricMorse

/-!
# The analytic amplitude in Poincaré's Morse coordinate

The parametric Morse coordinate gives the exact radicand normal form, but a contour integral also
contains the differential `dt`.  This file proves that the inverse fiber coordinate has an
analytic, nonvanishing vertical Jacobian.  Consequently any analytic source amplitude `a(z,t)`
pulls back to the analytic amplitude

`θ(z,v) = a(z,t(z,v)) ∂t/∂v`

and the inverse-square-root one-form takes Poincaré's local form

`θ(z,v) dv / root(k(z) + v²)`.

The square-root sheet remains explicit in the final identity; no global or principal branch is
silently selected at the pinch.
-/

noncomputable section

open Filter Set
open scoped Topology

namespace PoincareChapterVI

/-- The fiber component `u(z,v)` of the analytic local inverse to the Morse map. -/
def chapterVIDMorseFiberInverse (point : ℂ × ℂ) : ℂ :=
  (chapterVIDMorseInverse point).2

@[simp]
theorem chapterVIDMorseFiberInverse_base :
    chapterVIDMorseFiberInverse (chapterVIDZBase, (0 : ℂ)) = 0 := by
  simp [chapterVIDMorseFiberInverse]

/-- The inverse fiber coordinate is jointly analytic at the pinch. -/
theorem analyticAt_chapterVIDMorseFiberInverse :
    AnalyticAt ℂ chapterVIDMorseFiberInverse (chapterVIDZBase, (0 : ℂ)) := by
  have hsnd : AnalyticAt ℂ (fun point : ℂ × ℂ ↦ point.2)
      (chapterVIDZBase, (0 : ℂ)) := analyticAt_snd
  unfold chapterVIDMorseFiberInverse
  simpa only [Function.comp_def] using
    hsnd.comp_of_eq analyticAt_chapterVIDMorseInverse chapterVIDMorseInverse_base

/-- Evaluation of a scalar-valued derivative in the vertical fiber direction `(0,1)`. -/
def chapterVIVerticalDerivativeEvaluation :
    ((ℂ × ℂ) →L[ℂ] ℂ) →L[ℂ] ℂ :=
  (ContinuousLinearMap.apply ℂ ℂ) (0, 1)

/-- The Jacobian `∂u/∂v` of the inverse fiber coordinate. -/
def chapterVIDMorseJacobian (point : ℂ × ℂ) : ℂ :=
  chapterVIVerticalDerivativeEvaluation
    (fderiv ℂ chapterVIDMorseFiberInverse point)

/-- The inverse Morse map has derivative the inverse of the forward linear equivalence. -/
theorem hasFDerivAt_chapterVIDMorseInverse :
    HasFDerivAt chapterVIDMorseInverse
      (chapterVIDMorseLinearEquiv.symm : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ))
      (chapterVIDZBase, (0 : ℂ)) := by
  simpa only [chapterVIDMorseInverse, chapterVIDMorseMap_base] using
    hasStrictFDerivAt_chapterVIDMorseMap.to_localInverse.hasFDerivAt

/-- The inverse linearized Morse coordinate divides the vertical direction by `S(D,0)`. -/
theorem chapterVIDMorseLinearEquiv_symm_vertical :
    chapterVIDMorseLinearEquiv.symm (0, 1) =
      (0, chapterVIDMorseRootBase⁻¹) := by
  apply chapterVIDMorseLinearEquiv.injective
  rw [ContinuousLinearEquiv.apply_symm_apply]
  simp [chapterVIDMorseLinearEquiv_apply, chapterVIDMorseRootBase_ne_zero]

/-- The inverse fiber Jacobian at the pinch is exactly `S(D,0)⁻¹`. -/
theorem chapterVIDMorseJacobian_base :
    chapterVIDMorseJacobian (chapterVIDZBase, (0 : ℂ)) =
      chapterVIDMorseRootBase⁻¹ := by
  have hfiber := hasFDerivAt_chapterVIDMorseInverse.snd
  rw [chapterVIDMorseJacobian]
  unfold chapterVIDMorseFiberInverse
  rw [hfiber.fderiv]
  change (chapterVIDMorseLinearEquiv.symm (0, 1)).2 = _
  rw [chapterVIDMorseLinearEquiv_symm_vertical]

/-- The inverse fiber Jacobian is analytic jointly in `(z,v)`. -/
theorem analyticAt_chapterVIDMorseJacobian :
    AnalyticAt ℂ chapterVIDMorseJacobian (chapterVIDZBase, (0 : ℂ)) := by
  exact (chapterVIVerticalDerivativeEvaluation.analyticAt _).comp
    analyticAt_chapterVIDMorseFiberInverse.fderiv

/-- The inverse fiber Jacobian stays nonzero on a neighborhood of the pinch. -/
theorem eventually_chapterVIDMorseJacobian_ne_zero :
    ∀ᶠ point in 𝓝 (chapterVIDZBase, (0 : ℂ)),
      chapterVIDMorseJacobian point ≠ 0 := by
  apply analyticAt_chapterVIDMorseJacobian.continuousAt.eventually_ne
  rw [chapterVIDMorseJacobian_base]
  exact inv_ne_zero chapterVIDMorseRootBase_ne_zero

/-- Near the pinch, the first component of the inverse Morse map is the unchanged parameter `z`.
This follows from the local right-inverse identity rather than from any implementation detail of
the inverse function theorem. -/
theorem eventually_chapterVIDMorseInverse_fst :
    ∀ᶠ point in 𝓝 (chapterVIDZBase, (0 : ℂ)),
      (chapterVIDMorseInverse point).1 = point.1 := by
  filter_upwards [eventually_chapterVIDMorseInverse_right] with point hpoint
  have hfirst := congrArg Prod.fst hpoint
  simpa [chapterVIDMorseMap] using hfirst

/-- Reconstruct the original `(z,t)` source point from the Morse coordinates `(z,v)`. -/
def chapterVIDMorseSourcePoint (point : ℂ × ℂ) : ℂ × ℂ :=
  (point.1,
    chapterVIDCriticalCenter point.1 + chapterVIDMorseFiberInverse point)

@[simp]
theorem chapterVIDMorseSourcePoint_base :
    chapterVIDMorseSourcePoint (chapterVIDZBase, (0 : ℂ)) =
      (chapterVIDZBase, chapterVIDTBase) := by
  simp [chapterVIDMorseSourcePoint, chapterVIDCriticalCenter_base]

/-- The reconstructed original source point is jointly analytic. -/
theorem analyticAt_chapterVIDMorseSourcePoint :
    AnalyticAt ℂ chapterVIDMorseSourcePoint (chapterVIDZBase, (0 : ℂ)) := by
  have hfst : AnalyticAt ℂ (fun point : ℂ × ℂ ↦ point.1)
      (chapterVIDZBase, (0 : ℂ)) := analyticAt_fst
  have hcenter : AnalyticAt ℂ (fun point : ℂ × ℂ ↦
      chapterVIDCriticalCenter point.1) (chapterVIDZBase, (0 : ℂ)) := by
    simpa only [Function.comp_def] using
      analyticAt_chapterVIDCriticalCenter.comp_of_eq hfst rfl
  have hsecond := hcenter.add analyticAt_chapterVIDMorseFiberInverse
  unfold chapterVIDMorseSourcePoint
  simpa only [chapterVIDMorseFiberInverse, Function.comp_apply,
    Pi.add_apply] using analyticAt_fst.prod hsecond

/-- The literal source radicand has Poincaré's exact moving quadratic form in the reconstructed
Morse chart. -/
theorem eventually_chapterVIDRadicand_morseSourcePoint_eq :
    ∀ᶠ point in 𝓝 (chapterVIDZBase, (0 : ℂ)),
      chapterVIDRadicand (chapterVIDMorseSourcePoint point) =
        chapterVIDCriticalValue point.1 + point.2 ^ 2 := by
  filter_upwards [eventually_chapterVIDTranslatedRadicand_comp_morseInverse_eq,
      eventually_chapterVIDMorseInverse_fst] with point hnormal hfirst
  rw [← hnormal]
  simp only [chapterVIDTranslatedRadicand, chapterVIDMorseSourcePoint,
    chapterVIDMorseFiberInverse]
  rw [hfirst]

set_option backward.isDefEq.respectTransparency.types false in
/-- On a neighborhood of the pinch, `chapterVIDMorseJacobian (z,v)` is the one-variable
derivative of `v ↦ u(z,v)`. -/
theorem eventually_hasDerivAt_chapterVIDMorseFiberInverse :
    ∀ᶠ point in 𝓝 (chapterVIDZBase, (0 : ℂ)),
      HasDerivAt
        (chapterVIDMorseFiberInverse ∘ fun v : ℂ ↦ (point.1, v))
        (chapterVIDMorseJacobian point) point.2 := by
  filter_upwards [analyticAt_chapterVIDMorseInverse.eventually_analyticAt]
    with point hpoint
  have hinsertion : HasDerivAt (fun v : ℂ ↦ (point.1, v)) (0, 1) point.2 := by
    convert (hasDerivAt_const (x := point.2) (c := point.1)).prodMk
      (hasDerivAt_id (x := point.2)) using 1 <;> ext <;> simp
  have hsnd : AnalyticAt ℂ (fun p : ℂ × ℂ ↦ p.2)
      (chapterVIDMorseInverse point) := analyticAt_snd
  have hfiber : AnalyticAt ℂ chapterVIDMorseFiberInverse point := by
    unfold chapterVIDMorseFiberInverse
    exact hsnd.comp hpoint
  have hcomp : HasDerivAt
      (chapterVIDMorseFiberInverse ∘ fun v : ℂ ↦ (point.1, v))
      (fderiv ℂ chapterVIDMorseFiberInverse point (0, 1)) point.2 :=
    HasFDerivAt.comp_hasDerivAt point.2
      hfiber.hasStrictFDerivAt.hasFDerivAt hinsertion
  change HasDerivAt
    (chapterVIDMorseFiberInverse ∘ fun v : ℂ ↦ (point.1, v))
    (fderiv ℂ chapterVIDMorseFiberInverse point (0, 1)) point.2
  exact hcomp

/-- Pull an arbitrary analytic numerator in the source `(z,t)` coordinates through the Morse
coordinate, including the differential Jacobian. -/
def chapterVIDMorseAmplitude
    (sourceAmplitude : ℂ × ℂ → ℂ) (point : ℂ × ℂ) : ℂ :=
  sourceAmplitude (chapterVIDMorseSourcePoint point) *
    chapterVIDMorseJacobian point

/-- An analytic source numerator produces an analytic Morse-chart amplitude. -/
theorem analyticAt_chapterVIDMorseAmplitude
    {sourceAmplitude : ℂ × ℂ → ℂ}
    (hsource : AnalyticAt ℂ sourceAmplitude
      (chapterVIDZBase, chapterVIDTBase)) :
    AnalyticAt ℂ (chapterVIDMorseAmplitude sourceAmplitude)
      (chapterVIDZBase, (0 : ℂ)) := by
  exact (hsource.comp_of_eq analyticAt_chapterVIDMorseSourcePoint
      chapterVIDMorseSourcePoint_base).mul
    analyticAt_chapterVIDMorseJacobian

/-- The transformed amplitude's base value is the source numerator times `S(D,0)⁻¹`. -/
theorem chapterVIDMorseAmplitude_base (sourceAmplitude : ℂ × ℂ → ℂ) :
    chapterVIDMorseAmplitude sourceAmplitude (chapterVIDZBase, (0 : ℂ)) =
      sourceAmplitude (chapterVIDZBase, chapterVIDTBase) *
        chapterVIDMorseRootBase⁻¹ := by
  simp [chapterVIDMorseAmplitude, chapterVIDMorseJacobian_base]

/-- A nonzero analytic source numerator produces a nonzero local Morse amplitude. -/
theorem chapterVIDMorseAmplitude_base_ne_zero
    {sourceAmplitude : ℂ × ℂ → ℂ}
    (hsource : sourceAmplitude (chapterVIDZBase, chapterVIDTBase) ≠ 0) :
    chapterVIDMorseAmplitude sourceAmplitude (chapterVIDZBase, (0 : ℂ)) ≠ 0 := by
  rw [chapterVIDMorseAmplitude_base]
  exact mul_ne_zero hsource (inv_ne_zero chapterVIDMorseRootBase_ne_zero)

theorem eventually_chapterVIDMorseAmplitude_ne_zero
    {sourceAmplitude : ℂ × ℂ → ℂ}
    (hanalytic : AnalyticAt ℂ sourceAmplitude
      (chapterVIDZBase, chapterVIDTBase))
    (hnonzero : sourceAmplitude (chapterVIDZBase, chapterVIDTBase) ≠ 0) :
    ∀ᶠ point in 𝓝 (chapterVIDZBase, (0 : ℂ)),
      chapterVIDMorseAmplitude sourceAmplitude point ≠ 0 := by
  exact (analyticAt_chapterVIDMorseAmplitude hanalytic).continuousAt.eventually_ne
    (chapterVIDMorseAmplitude_base_ne_zero hnonzero)

/-- Exact pullback identity for the inverse-root one-form.  `sourceRoot` and `normalRoot` encode
the same locally selected square-root sheet in the two coordinates.  The statement keeps this
sheet compatibility as a hypothesis instead of making an invalid principal-root choice across
the pinch. -/
theorem chapterVIDMorse_pullback_inverseRoot_oneForm
    (sourceAmplitude sourceRoot : ℂ × ℂ → ℂ)
    (normalRoot : ℂ × ℂ → ℂ) (point : ℂ × ℂ) (direction : ℂ)
    (hroot : sourceRoot (chapterVIDMorseSourcePoint point) = normalRoot point) :
    chapterVIComplexScalarOneForm
        (fun t ↦ sourceAmplitude (point.1, t) / sourceRoot (point.1, t))
        (chapterVIDMorseSourcePoint point).2
        (direction * chapterVIDMorseJacobian point) =
      chapterVIComplexScalarOneForm
        (fun v ↦ chapterVIDMorseAmplitude sourceAmplitude (point.1, v) /
          normalRoot (point.1, v))
        point.2 direction := by
  simp only [chapterVIComplexScalarOneForm_apply]
  simp only [chapterVIDMorseSourcePoint] at hroot ⊢
  rw [hroot]
  unfold chapterVIDMorseAmplitude chapterVIDMorseSourcePoint
  ring

end PoincareChapterVI
