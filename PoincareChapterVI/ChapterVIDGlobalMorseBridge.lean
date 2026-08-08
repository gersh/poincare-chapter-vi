/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.ChapterVIDGlobalLocalBridge
import PoincareChapterVI.ChapterVIMorseAmplitude

/-!
# The global D contour in Poincare's local Morse coordinate

The explicit global pinch is constructed in `u=x^(1/3)`, while the local logarithmic calculation
uses the Morse fiber coordinate `v`.  This file supplies the missing local coordinate
identification.  After the certified cubic deck transformation, the exact `u -> t` map is
unramified at D.  Centering `t` and applying the forward Morse map therefore gives an analytic
`u -> v` coordinate with nonzero derivative.

Its canonical local inverse turns a straight Morse segment back into the actual global `u`
coordinate.  Near D, the resulting centered point is exactly the inverse Morse chart, and the
resulting `(z,t)` source point is exactly `chapterVIDMorseSourcePoint`.  Thus the global contour
coordinate and the local logarithmic segment agree as analytic germs, not just at their common
endpoint.  This is still a local statement; continuation of a square-root sheet around the two
remaining global arcs is separate.
-/

noncomputable section

open Complex Real Filter Set
open scoped Topology unitInterval

namespace PoincareChapterVI

/-- The global `u` coordinate, expressed as a centered source point in the local `t` chart. -/
noncomputable def chapterVIDGlobalCenteredContourPoint (u : ℂ) : ℂ × ℂ :=
  (chapterVIDZBase,
    chapterVIDDeckedRootToLocalContour u -
      chapterVIDCriticalCenter chapterVIDZBase)

@[simp]
theorem chapterVIDGlobalCenteredContourPoint_collision :
    chapterVIDGlobalCenteredContourPoint chapterVIDCollisionLift =
      (chapterVIDZBase, 0) := by
  simp [chapterVIDGlobalCenteredContourPoint, chapterVIDTBase]

theorem analyticAt_chapterVIDGlobalCenteredContourPoint :
    AnalyticAt ℂ chapterVIDGlobalCenteredContourPoint chapterVIDCollisionLift := by
  unfold chapterVIDGlobalCenteredContourPoint
  exact analyticAt_const.prod
    (analyticAt_chapterVIDDeckedRootToLocalContour_collision.sub analyticAt_const)

/-- The local Morse fiber coordinate of Poincare's exact global `u` coordinate on the singular
parameter fiber. -/
noncomputable def chapterVIDGlobalMorseFiberCoordinate (u : ℂ) : ℂ :=
  (chapterVIDMorseMap (chapterVIDGlobalCenteredContourPoint u)).2

@[simp]
theorem chapterVIDGlobalMorseFiberCoordinate_collision :
    chapterVIDGlobalMorseFiberCoordinate chapterVIDCollisionLift = 0 := by
  simp [chapterVIDGlobalMorseFiberCoordinate]

theorem analyticAt_chapterVIDGlobalMorseFiberCoordinate :
    AnalyticAt ℂ chapterVIDGlobalMorseFiberCoordinate chapterVIDCollisionLift := by
  have hmorse := analyticAt_chapterVIDMorseMap.comp_of_eq
    analyticAt_chapterVIDGlobalCenteredContourPoint
    chapterVIDGlobalCenteredContourPoint_collision
  exact analyticAt_snd.comp_of_eq hmorse rfl

/-- The derivative of the global-to-Morse fiber coordinate is the product of the exact
`u -> t` derivative and the nonzero square root of the prepared unit. -/
theorem deriv_chapterVIDGlobalMorseFiberCoordinate :
    deriv chapterVIDGlobalMorseFiberCoordinate chapterVIDCollisionLift =
      deriv chapterVIDDeckedRootToLocalContour chapterVIDCollisionLift *
        chapterVIDMorseRootBase := by
  have hdeck :=
    analyticAt_chapterVIDDeckedRootToLocalContour_collision.differentiableAt.hasDerivAt
  have hpoint : HasDerivAt chapterVIDGlobalCenteredContourPoint
      (0, deriv chapterVIDDeckedRootToLocalContour chapterVIDCollisionLift)
      chapterVIDCollisionLift := by
    unfold chapterVIDGlobalCenteredContourPoint
    convert (hasDerivAt_const chapterVIDCollisionLift chapterVIDZBase).prodMk
      (hdeck.sub_const (chapterVIDCriticalCenter chapterVIDZBase)) using 1
  have hmorseBase : HasFDerivAt chapterVIDMorseMap
      (chapterVIDMorseLinearEquiv : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ))
      (chapterVIDGlobalCenteredContourPoint chapterVIDCollisionLift) := by
    simpa only [chapterVIDGlobalCenteredContourPoint_collision] using
      hasFDerivAt_chapterVIDMorseMap
  have hmorse := hmorseBase.comp_hasDerivAt chapterVIDCollisionLift hpoint
  have hsndBase : HasFDerivAt Prod.snd (ContinuousLinearMap.snd ℂ ℂ ℂ)
      ((chapterVIDMorseMap ∘ chapterVIDGlobalCenteredContourPoint)
        chapterVIDCollisionLift) := by
    simpa only [Function.comp_apply, chapterVIDGlobalCenteredContourPoint_collision,
      chapterVIDMorseMap_base] using
      (hasFDerivAt_snd (𝕜 := ℂ) (p := (chapterVIDZBase, (0 : ℂ))))
  have hsnd := hsndBase.comp_hasDerivAt chapterVIDCollisionLift hmorse
  have hderiv := hsnd.deriv
  change deriv chapterVIDGlobalMorseFiberCoordinate chapterVIDCollisionLift = _ at hderiv
  rw [hderiv]
  change (chapterVIDMorseLinearEquiv
    (0, deriv chapterVIDDeckedRootToLocalContour chapterVIDCollisionLift)).2 = _
  rw [chapterVIDMorseLinearEquiv_apply]

theorem deriv_chapterVIDGlobalMorseFiberCoordinate_ne_zero :
    deriv chapterVIDGlobalMorseFiberCoordinate chapterVIDCollisionLift ≠ 0 := by
  rw [deriv_chapterVIDGlobalMorseFiberCoordinate]
  exact mul_ne_zero deriv_chapterVIDDeckedRootToLocalContour_collision_ne_zero
    chapterVIDMorseRootBase_ne_zero

theorem hasStrictDerivAt_chapterVIDGlobalMorseFiberCoordinate :
    HasStrictDerivAt chapterVIDGlobalMorseFiberCoordinate
      (deriv chapterVIDGlobalMorseFiberCoordinate chapterVIDCollisionLift)
      chapterVIDCollisionLift :=
  analyticAt_chapterVIDGlobalMorseFiberCoordinate.hasStrictDerivAt

/-- The canonical local analytic map from a Morse fiber coordinate back to the actual global
`u=x^(1/3)` contour coordinate. -/
noncomputable def chapterVIDGlobalContourFromMorse : ℂ → ℂ :=
  hasStrictDerivAt_chapterVIDGlobalMorseFiberCoordinate.localInverse
    chapterVIDGlobalMorseFiberCoordinate
    (deriv chapterVIDGlobalMorseFiberCoordinate chapterVIDCollisionLift)
    chapterVIDCollisionLift deriv_chapterVIDGlobalMorseFiberCoordinate_ne_zero

@[simp]
theorem chapterVIDGlobalContourFromMorse_zero :
    chapterVIDGlobalContourFromMorse 0 = chapterVIDCollisionLift := by
  have hleft :=
    (hasStrictDerivAt_chapterVIDGlobalMorseFiberCoordinate.eventually_left_inverse
      deriv_chapterVIDGlobalMorseFiberCoordinate_ne_zero).self_of_nhds
  simpa only [chapterVIDGlobalContourFromMorse,
    chapterVIDGlobalMorseFiberCoordinate_collision] using hleft

/-- The inverse global contour has the reciprocal derivative of the forward Morse coordinate.
This is the exact first-order datum needed to orient the two inverse-Morse endpoints, rather than
an opaque consequence of analyticity. -/
theorem hasStrictDerivAt_chapterVIDGlobalContourFromMorse :
    HasStrictDerivAt chapterVIDGlobalContourFromMorse
      (deriv chapterVIDGlobalMorseFiberCoordinate chapterVIDCollisionLift)⁻¹ 0 := by
  simpa only [chapterVIDGlobalContourFromMorse,
    chapterVIDGlobalMorseFiberCoordinate_collision] using
    hasStrictDerivAt_chapterVIDGlobalMorseFiberCoordinate.to_localInverse
      deriv_chapterVIDGlobalMorseFiberCoordinate_ne_zero

theorem deriv_chapterVIDGlobalContourFromMorse :
    deriv chapterVIDGlobalContourFromMorse 0 =
      (deriv chapterVIDGlobalMorseFiberCoordinate chapterVIDCollisionLift)⁻¹ :=
  hasStrictDerivAt_chapterVIDGlobalContourFromMorse.hasDerivAt.deriv

theorem analyticAt_chapterVIDGlobalContourFromMorse :
    AnalyticAt ℂ chapterVIDGlobalContourFromMorse 0 := by
  simpa only [chapterVIDGlobalContourFromMorse,
    chapterVIDGlobalMorseFiberCoordinate_collision] using
    analyticAt_chapterVIDGlobalMorseFiberCoordinate.analyticAt_localInverse
      deriv_chapterVIDGlobalMorseFiberCoordinate_ne_zero

theorem eventually_chapterVIDGlobalMorseFiberCoordinate_contourFromMorse :
    (fun v ↦ chapterVIDGlobalMorseFiberCoordinate
      (chapterVIDGlobalContourFromMorse v)) =ᶠ[𝓝 0] fun v ↦ v := by
  change ∀ᶠ v in 𝓝 0,
    chapterVIDGlobalMorseFiberCoordinate (chapterVIDGlobalContourFromMorse v) = v
  simpa only [chapterVIDGlobalContourFromMorse,
    chapterVIDGlobalMorseFiberCoordinate_collision] using
    (HasStrictDerivAt.eventually_right_inverse
      hasStrictDerivAt_chapterVIDGlobalMorseFiberCoordinate
      deriv_chapterVIDGlobalMorseFiberCoordinate_ne_zero)

/-- Pulling the straight `v` coordinate back to global `u`, and then centering the exact source
`t`, gives precisely the inverse Morse chart near D. -/
theorem eventually_chapterVIDGlobalCenteredContourPoint_contourFromMorse :
    (fun v ↦ chapterVIDGlobalCenteredContourPoint
      (chapterVIDGlobalContourFromMorse v)) =ᶠ[𝓝 0]
      fun v ↦ chapterVIDMorseInverse (chapterVIDZBase, v) := by
  have htendInv : Tendsto chapterVIDGlobalContourFromMorse
      (𝓝 0) (𝓝 chapterVIDCollisionLift) := by
    rw [← chapterVIDGlobalContourFromMorse_zero]
    exact analyticAt_chapterVIDGlobalContourFromMorse.continuousAt
  have htendPoint : Tendsto
      (fun v ↦ chapterVIDGlobalCenteredContourPoint
        (chapterVIDGlobalContourFromMorse v))
      (𝓝 0) (𝓝 (chapterVIDZBase, 0)) := by
    rw [← chapterVIDGlobalCenteredContourPoint_collision]
    change Tendsto
      (chapterVIDGlobalCenteredContourPoint ∘ chapterVIDGlobalContourFromMorse)
      (𝓝 0)
      (𝓝 (chapterVIDGlobalCenteredContourPoint chapterVIDCollisionLift))
    exact Filter.Tendsto.comp
      analyticAt_chapterVIDGlobalCenteredContourPoint.continuousAt htendInv
  have hleft := htendPoint.eventually eventually_chapterVIDMorseInverse_left
  filter_upwards
    [hleft, eventually_chapterVIDGlobalMorseFiberCoordinate_contourFromMorse]
      with v hleftv hrightv
  symm
  calc
    chapterVIDMorseInverse (chapterVIDZBase, v) =
        chapterVIDMorseInverse
          (chapterVIDMorseMap
            (chapterVIDGlobalCenteredContourPoint
              (chapterVIDGlobalContourFromMorse v))) := by
      congr 1
      ext
      · simp [chapterVIDMorseMap, chapterVIDGlobalCenteredContourPoint]
      · exact hrightv.symm
    _ = chapterVIDGlobalCenteredContourPoint
        (chapterVIDGlobalContourFromMorse v) := hleftv

/-- The source point obtained from the global contour coordinate pulled back along a straight
Morse segment. -/
noncomputable def chapterVIDGlobalSourceContourFromMorse (v : ℂ) : ℂ × ℂ :=
  (chapterVIDZBase,
    chapterVIDDeckedRootToLocalContour (chapterVIDGlobalContourFromMorse v))

/-- After the canonical base-point normalization, the source contour reconstructed from the
Morse coordinate uses Poincaré's literal global `u -> t` map with no deck correction. -/
@[simp]
theorem chapterVIDGlobalSourceContourFromMorse_eq (v : ℂ) :
    chapterVIDGlobalSourceContourFromMorse v =
      (chapterVIDZBase,
        chapterVIDRootToOriginalContour (chapterVIDGlobalContourFromMorse v)) := by
  simp [chapterVIDGlobalSourceContourFromMorse]

/-- The preceding global source point is exactly Poincare's reconstructed local Morse source
point near D.  This is the precise local correspondence needed to transport the logarithmic
middle segment into the explicit global contour coordinate. -/
theorem eventually_chapterVIDGlobalSourceContourFromMorse_eq_morseSourcePoint :
    chapterVIDGlobalSourceContourFromMorse =ᶠ[𝓝 0]
      fun v ↦ chapterVIDMorseSourcePoint (chapterVIDZBase, v) := by
  filter_upwards
    [eventually_chapterVIDGlobalCenteredContourPoint_contourFromMorse]
      with v hv
  have hsnd := congrArg Prod.snd hv
  ext
  · rfl
  · simp only [chapterVIDGlobalSourceContourFromMorse,
      chapterVIDMorseSourcePoint, chapterVIDMorseFiberInverse]
    simp only [chapterVIDGlobalCenteredContourPoint] at hsnd
    rw [← hsnd]
    ring

end PoincareChapterVI
