/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.ChapterVIDGlobalMorseBridge
import PoincareChapterVI.ChapterVIPrincipalIntegrand

/-!
# The moving local Morse contour in Poincare's global root coordinate

The compiled contour is evaluated in `u = x^(1/3)`, whereas the exact local vanishing cycle is
constructed in the original source coordinate `t`. Poincare's map `u -> t` is unramified at D.
This file constructs its canonical local inverse and applies it jointly to the moving `(k,v)`
Morse source point.

Consequently the endpoints of the local middle path can be stated in the same explicit root
coordinate as the outer quarters and the future connector certificates. This is an analytic
germ theorem; a compact rectangle on which the identities hold is extracted downstream.
-/

noncomputable section

open Filter Topology

namespace PoincareChapterVI

/-- Poincare's exact root-to-source map has a strict nonzero derivative at D. -/
theorem hasStrictDerivAt_chapterVIDRootToOriginalContour_collision :
    HasStrictDerivAt chapterVIDRootToOriginalContour
      (deriv chapterVIDRootToOriginalContour chapterVIDCollisionLift)
      chapterVIDCollisionLift :=
  (analyticAt_chapterVIDRootToOriginalContour
    chapterVIDCollisionLift_ne_zero).hasStrictDerivAt

/-- The canonical local inverse from the original source coordinate `t` back to
`u = x^(1/3)`. -/
noncomputable def chapterVIDOriginalContourToRoot : ℂ → ℂ :=
  hasStrictDerivAt_chapterVIDRootToOriginalContour_collision.localInverse
    chapterVIDRootToOriginalContour
    (deriv chapterVIDRootToOriginalContour chapterVIDCollisionLift)
    chapterVIDCollisionLift deriv_chapterVIDRootToOriginalContour_collision_ne_zero

@[simp]
theorem chapterVIDOriginalContourToRoot_base :
    chapterVIDOriginalContourToRoot chapterVIDTBase = chapterVIDCollisionLift := by
  have hleft :=
    (hasStrictDerivAt_chapterVIDRootToOriginalContour_collision.eventually_left_inverse
      deriv_chapterVIDRootToOriginalContour_collision_ne_zero).self_of_nhds
  have hbase : chapterVIDRootToOriginalContour chapterVIDCollisionLift =
      chapterVIDTBase := rfl
  rw [hbase] at hleft
  simpa only [chapterVIDOriginalContourToRoot] using hleft

theorem analyticAt_chapterVIDOriginalContourToRoot :
    AnalyticAt ℂ chapterVIDOriginalContourToRoot chapterVIDTBase := by
  have h := (analyticAt_chapterVIDRootToOriginalContour
    chapterVIDCollisionLift_ne_zero).analyticAt_localInverse
      deriv_chapterVIDRootToOriginalContour_collision_ne_zero
  have hbase : chapterVIDRootToOriginalContour chapterVIDCollisionLift =
      chapterVIDTBase := rfl
  rw [hbase] at h
  simpa only [chapterVIDOriginalContourToRoot] using h

/-- Near D, changing from `u` to `t` and back recovers the original root coordinate. -/
theorem eventually_chapterVIDOriginalContourToRoot_rootToOriginalContour :
    (chapterVIDOriginalContourToRoot ∘ chapterVIDRootToOriginalContour) =ᶠ[
      𝓝 chapterVIDCollisionLift] id := by
  change ∀ᶠ u in 𝓝 chapterVIDCollisionLift,
    chapterVIDOriginalContourToRoot (chapterVIDRootToOriginalContour u) = u
  simpa only [chapterVIDOriginalContourToRoot] using
    hasStrictDerivAt_chapterVIDRootToOriginalContour_collision.eventually_left_inverse
      deriv_chapterVIDRootToOriginalContour_collision_ne_zero

/-- Near D, changing from `t` to `u` and back recovers the original source coordinate. -/
theorem eventually_chapterVIDRootToOriginalContour_originalContourToRoot :
    (chapterVIDRootToOriginalContour ∘ chapterVIDOriginalContourToRoot) =ᶠ[
      𝓝 chapterVIDTBase] id := by
  have h := HasStrictDerivAt.eventually_right_inverse
    hasStrictDerivAt_chapterVIDRootToOriginalContour_collision
    deriv_chapterVIDRootToOriginalContour_collision_ne_zero
  have hbase : chapterVIDRootToOriginalContour chapterVIDCollisionLift =
      chapterVIDTBase := rfl
  rw [hbase] at h
  change ∀ᶠ t in 𝓝 chapterVIDTBase,
    chapterVIDRootToOriginalContour (chapterVIDOriginalContourToRoot t) = t
  simpa only [chapterVIDOriginalContourToRoot] using h

theorem tendsto_chapterVIDOriginalContourToRoot :
    Tendsto chapterVIDOriginalContourToRoot
      (𝓝 chapterVIDTBase) (𝓝 chapterVIDCollisionLift) := by
  rw [← chapterVIDOriginalContourToRoot_base]
  exact analyticAt_chapterVIDOriginalContourToRoot.continuousAt

/-- The exact moving local source point, expressed in the global `u` coordinate. -/
noncomputable def chapterVIDCriticalMorseRootPoint (point : ℂ × ℂ) : ℂ :=
  chapterVIDOriginalContourToRoot
    (chapterVIDCriticalMorseSourcePointAtD point).2

@[simp]
theorem chapterVIDCriticalMorseRootPoint_base :
    chapterVIDCriticalMorseRootPoint (0, 0) = chapterVIDCollisionLift := by
  simp [chapterVIDCriticalMorseRootPoint]

theorem analyticAt_chapterVIDCriticalMorseRootPoint :
    AnalyticAt ℂ chapterVIDCriticalMorseRootPoint (0, 0) := by
  have hsource := analyticAt_chapterVIDCriticalMorseSourcePoint
    deriv_chapterVIDCriticalValue_ne_zero
  have hsnd : AnalyticAt ℂ
      (fun point : ℂ × ℂ ↦ (chapterVIDCriticalMorseSourcePointAtD point).2)
      (0, 0) := by
    change AnalyticAt ℂ
      ((fun p : ℂ × ℂ ↦ p.2) ∘
        chapterVIDCriticalMorseSourcePoint
          deriv_chapterVIDCriticalValue_ne_zero) (0, 0)
    exact analyticAt_snd.comp_of_eq hsource
      (chapterVIDCriticalMorseSourcePoint_base
        deriv_chapterVIDCriticalValue_ne_zero)
  exact analyticAt_chapterVIDOriginalContourToRoot.comp_of_eq hsnd (by simp)

/-- The moving root point maps to exactly the local Morse source point, not merely to a point
with the same first-order expansion. -/
theorem eventually_chapterVIDRootToOriginalContour_criticalMorseRootPoint :
    ∀ᶠ point : ℂ × ℂ in 𝓝 (0, 0),
      chapterVIDRootToOriginalContour (chapterVIDCriticalMorseRootPoint point) =
        (chapterVIDCriticalMorseSourcePointAtD point).2 := by
  have htendsto : Tendsto
      (fun point : ℂ × ℂ ↦ (chapterVIDCriticalMorseSourcePointAtD point).2)
      (𝓝 (0, 0)) (𝓝 chapterVIDTBase) := by
    have hsource := analyticAt_chapterVIDCriticalMorseSourcePoint
      deriv_chapterVIDCriticalValue_ne_zero
    have hsnd := analyticAt_snd.comp_of_eq hsource
      (chapterVIDCriticalMorseSourcePoint_base
        deriv_chapterVIDCriticalValue_ne_zero)
    change Tendsto
      ((fun p : ℂ × ℂ ↦ p.2) ∘
        chapterVIDCriticalMorseSourcePoint
          deriv_chapterVIDCriticalValue_ne_zero)
      (𝓝 (0, 0)) (𝓝 chapterVIDTBase)
    rw [← show
      ((fun p : ℂ × ℂ ↦ p.2) ∘
        chapterVIDCriticalMorseSourcePoint
          deriv_chapterVIDCriticalValue_ne_zero) (0, 0) = chapterVIDTBase by
      simp]
    exact hsnd.continuousAt
  exact htendsto.eventually
    eventually_chapterVIDRootToOriginalContour_originalContourToRoot

/-- The moving root coordinate remains away from the ramification point after shrinking the
Morse neighborhood. -/
theorem eventually_chapterVIDCriticalMorseRootPoint_ne_zero :
    ∀ᶠ point : ℂ × ℂ in 𝓝 (0, 0),
      chapterVIDCriticalMorseRootPoint point ≠ 0 := by
  have htendsto : Tendsto chapterVIDCriticalMorseRootPoint
      (𝓝 (0, 0)) (𝓝 chapterVIDCollisionLift) := by
    rw [← chapterVIDCriticalMorseRootPoint_base]
    exact analyticAt_chapterVIDCriticalMorseRootPoint.continuousAt
  exact htendsto.eventually
    (eventually_ne_nhds chapterVIDCollisionLift_ne_zero)

/-- The local cubic root of the source parameter, pulled back to the true critical-value
coordinate. -/
def chapterVIDCriticalParameterRootAtD (k : ℂ) : ℂ :=
  chapterVIDZRoot (chapterVIDCriticalParameterInverseAtD k)

@[simp]
theorem chapterVIDCriticalParameterRootAtD_zero :
    chapterVIDCriticalParameterRootAtD 0 = chapterVIDZRootBase := by
  simp [chapterVIDCriticalParameterRootAtD]

theorem analyticAt_chapterVIDCriticalParameterRootAtD :
    AnalyticAt ℂ chapterVIDCriticalParameterRootAtD 0 := by
  exact analyticAt_chapterVIDZRoot.comp_of_eq
    analyticAt_chapterVIDCriticalParameterInverseAtD (by simp)

theorem eventually_chapterVIDCriticalParameterRootAtD_pow :
    ∀ᶠ k : ℂ in 𝓝 0,
      chapterVIDCriticalParameterRootAtD k ^ 3 =
        chapterVIDCriticalParameterInverseAtD k := by
  have htendsto : Tendsto chapterVIDCriticalParameterInverseAtD
      (𝓝 0) (𝓝 chapterVIDZBase) := by
    rw [← chapterVIDCriticalParameterInverseAtD_zero]
    exact analyticAt_chapterVIDCriticalParameterInverseAtD.continuousAt
  filter_upwards [htendsto.eventually eventually_chapterVIDZRoot_pow] with k hk
  simpa only [chapterVIDCriticalParameterRootAtD, zpow_ofNat] using hk

end PoincareChapterVI
