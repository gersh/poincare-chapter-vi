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

/-- At D, the transformed second anomaly selected by the global root coordinates is exactly
the anomaly used to normalize the local Kepler inverses. -/
@[simp]
theorem chapterVIDRootSecondAnomaly_base :
    chapterVIDRootSecondAnomaly chapterVIDZRootBase chapterVIDCollisionLift =
      chapterVIDY := by
  rw [chapterVIDZRootBase_eq_commonParameterRootPath_one]
  have h := chapterVIDInsideRootSecondAnomaly_eq_curveThree (1 : unitInterval)
  have h' : chapterVIDRootSecondAnomaly
      (chapterVIDCommonParameterRootPath 1) chapterVIDCollisionLift =
        (chapterVIDCurveThreeY chapterVIDRoot : ℂ) := by
    simpa using h
  exact h'.trans chapterVIDCurveThreeY_at_root

/-- Near D, Poincaré's selected local inverse coordinates recover the literal global root
coordinates `(u³, ζ t(u))`. This is the branch-sensitive bridge needed to compare the local
Morse square root with the compiled root-coordinate square root. -/
theorem eventually_chapterVIDPoincareAnomalyPair_rootCoordinates :
    ∀ᶠ point : ℂ × ℂ in 𝓝 (chapterVIDZRootBase, chapterVIDCollisionLift),
      chapterVIPoincareAnomalyPair (-1) 3 chapterVIDEccentricity 0
          (chapterVIDX, chapterVIDY) chapterVIDX_ne_zero chapterVIDY_ne_zero
          chapterVID_firstKeplerCritical chapterVID_secondKeplerCritical (by norm_num)
          (point.1 ^ 3, chapterVIDRootToOriginalContour point.2) =
        (point.2 ^ 3, chapterVIDRootSecondAnomaly point.1 point.2) := by
  have htendX : Tendsto (fun point : ℂ × ℂ ↦ point.2 ^ 3)
      (𝓝 (chapterVIDZRootBase, chapterVIDCollisionLift)) (𝓝 chapterVIDX) := by
    rw [← chapterVIDCollisionLift_pow]
    exact (continuousAt_snd.pow 3)
  have hfirst := htendX.eventually
    (eventually_chapterVIKeplerLocalInverse_exponential chapterVIDEccentricity
      chapterVIDX chapterVIDX_ne_zero chapterVID_firstKeplerCritical)
  have htendY : Tendsto
      (fun point : ℂ × ℂ ↦ chapterVIDRootSecondAnomaly point.1 point.2)
      (𝓝 (chapterVIDZRootBase, chapterVIDCollisionLift)) (𝓝 chapterVIDY) := by
    rw [← chapterVIDRootSecondAnomaly_base]
    exact continuousAt_fst.mul
      ((analyticAt_chapterVIDRootToOriginalContour
        chapterVIDCollisionLift_ne_zero).continuousAt.comp_of_eq continuousAt_snd rfl)
  let secondMeanBase := chapterVIKeplerExponential 0 chapterVIDY
  have hsecondMeanBase : secondMeanBase ≠ 0 :=
    chapterVIKeplerExponential_ne_zero 0 chapterVIDY_ne_zero
  have hsecondMeanBase_eq : secondMeanBase = chapterVIDY := by
    simp [secondMeanBase, chapterVIKeplerExponential]
  have htendY' : Tendsto
      (fun point : ℂ × ℂ ↦ chapterVIDRootSecondAnomaly point.1 point.2)
      (𝓝 (chapterVIDZRootBase, chapterVIDCollisionLift)) (𝓝 secondMeanBase) := by
    rw [hsecondMeanBase_eq]
    exact htendY
  have hpower := htendY'.eventually
    (eventually_chapterVIPowerLocalInverse_zpow 3 secondMeanBase hsecondMeanBase
      (by norm_num))
  have hsecond := htendY.eventually
    (eventually_chapterVIKeplerLocalInverse_exponential 0 chapterVIDY
      chapterVIDY_ne_zero chapterVID_secondKeplerCritical)
  have hune : ∀ᶠ point : ℂ × ℂ in
      𝓝 (chapterVIDZRootBase, chapterVIDCollisionLift), point.2 ≠ 0 :=
    continuousAt_snd.eventually (eventually_ne_nhds chapterVIDCollisionLift_ne_zero)
  filter_upwards [hfirst, hpower, hsecond, hune] with point hfirst hpower hsecond hu
  apply Prod.ext
  · simp only [chapterVIPoincareAnomalyPair]
    rw [zpow_ofNat, chapterVIDRootToOriginalContour_pow]
    exact hfirst
  · have ht : chapterVIDRootToOriginalContour point.2 ≠ 0 :=
      chapterVIDRootToOriginalContour_ne_zero hu
    have hinput : point.1 ^ (3 : ℕ) /
        (chapterVIDRootToOriginalContour point.2 ^ (3 : ℤ)) ^ (-1 : ℤ) =
          chapterVIDRootSecondAnomaly point.1 point.2 ^ (3 : ℤ) := by
      simp only [zpow_neg_one, zpow_ofNat, chapterVIDRootSecondAnomaly]
      field_simp
    unfold chapterVIPoincareAnomalyPair
    dsimp only
    rw [hinput, hpower]
    simpa only [chapterVIKeplerExponential, zero_div, zero_mul,
      Complex.exp_zero, mul_one] using hsecond

/-- Therefore the global root-coordinate radicand is not a surrogate: near D it is literally
Poincaré's convergent source radicand evaluated after the exact `u ↦ t` change. -/
theorem eventually_chapterVIDRadicand_rootCoordinates :
    ∀ᶠ point : ℂ × ℂ in 𝓝 (chapterVIDZRootBase, chapterVIDCollisionLift),
      chapterVIDRadicand
          (point.1 ^ 3, chapterVIDRootToOriginalContour point.2) =
        chapterVIDRootCoordinateRadicand point.1 point.2 := by
  filter_upwards [eventually_chapterVIDPoincareAnomalyPair_rootCoordinates]
    with point hpair
  change chapterVIPlanarSourceRadicand chapterVIDEccentricity chapterVIDComplement
      0 1 2 2
        (chapterVIPoincareAnomalyPair (-1) 3 chapterVIDEccentricity 0
          (chapterVIDX, chapterVIDY) chapterVIDX_ne_zero chapterVIDY_ne_zero
          chapterVID_firstKeplerCritical chapterVID_secondKeplerCritical (by norm_num)
          (point.1 ^ 3, chapterVIDRootToOriginalContour point.2)).1
        (chapterVIPoincareAnomalyPair (-1) 3 chapterVIDEccentricity 0
          (chapterVIDX, chapterVIDY) chapterVIDX_ne_zero chapterVIDY_ne_zero
          chapterVID_firstKeplerCritical chapterVID_secondKeplerCritical (by norm_num)
          (point.1 ^ 3, chapterVIDRootToOriginalContour point.2)).2 =
    chapterVIPlanarSourceRadicand chapterVIDEccentricity chapterVIDComplement
      0 1 2 2 (point.2 ^ 3) (chapterVIDRootSecondAnomaly point.1 point.2)
  rw [hpair]

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

/-- On the moving Morse germ, the literal root-coordinate radicand and the local convergent
source radicand agree exactly. All local inverse branches have now been identified. -/
theorem eventually_chapterVIDRootCoordinateRadicand_criticalMorseRootPoint :
    ∀ᶠ point : ℂ × ℂ in 𝓝 (0, 0),
      chapterVIDRootCoordinateRadicand
          (chapterVIDCriticalParameterRootAtD point.1)
          (chapterVIDCriticalMorseRootPoint point) =
        chapterVIDRadicand (chapterVIDCriticalMorseSourcePointAtD point) := by
  have hζ : AnalyticAt ℂ
      (fun point : ℂ × ℂ ↦ chapterVIDCriticalParameterRootAtD point.1) (0, 0) :=
    analyticAt_chapterVIDCriticalParameterRootAtD.comp_of_eq analyticAt_fst rfl
  have hu : AnalyticAt ℂ chapterVIDCriticalMorseRootPoint (0, 0) :=
    analyticAt_chapterVIDCriticalMorseRootPoint
  have htendsto : Tendsto
      (fun point : ℂ × ℂ ↦
        (chapterVIDCriticalParameterRootAtD point.1,
          chapterVIDCriticalMorseRootPoint point))
      (𝓝 (0, 0)) (𝓝 (chapterVIDZRootBase, chapterVIDCollisionLift)) := by
    rw [← show
      (chapterVIDCriticalParameterRootAtD (0 : ℂ),
        chapterVIDCriticalMorseRootPoint (0, 0)) =
          (chapterVIDZRootBase, chapterVIDCollisionLift) by simp]
    exact (hζ.prod hu).continuousAt
  have hrad := htendsto.eventually eventually_chapterVIDRadicand_rootCoordinates
  have hfst : Tendsto (fun point : ℂ × ℂ ↦ point.1)
      (𝓝 (0, 0)) (𝓝 0) := continuousAt_fst
  have hparameter := hfst.eventually
    eventually_chapterVIDCriticalParameterRootAtD_pow
  filter_upwards [hrad,
    eventually_chapterVIDRootToOriginalContour_criticalMorseRootPoint,
    hparameter] with point hrad hsource hparameter
  rw [← hrad, hparameter, hsource]
  rfl

end PoincareChapterVI
