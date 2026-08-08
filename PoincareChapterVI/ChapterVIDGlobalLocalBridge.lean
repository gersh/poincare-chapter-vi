/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.ChapterVIDRootCoordinates
import PoincareChapterVI.ChapterVIJointPreparation

/-!
# From Poincaré's global D branches to the local logarithmic model

The §97 admissibility argument is most transparent in `u=x^(1/3)`, whereas §§99–100 return to
the original contour variable `t`.  This file proves that the explicit endpoint of the global
`u`-path maps to the same source point D as the local analytic germ.  The `z^(1/3)` choice is now
normalized directly to the global positive-real lift; the separate cubic deck transformation
below concerns Poincare's contour variable `t`.
-/

noncomputable section

open Complex Real
open scoped Topology unitInterval

namespace PoincareChapterVI

/-- The original `t` coordinate obtained from the endpoint of the explicit global `u` path. -/
noncomputable def chapterVIDGlobalTBase : ℂ :=
  chapterVIDRootToOriginalContour chapterVIDCollisionLift

/-- The local analytic construction is normalized at exactly the endpoint of the global
contour; there is no residual cubic deck ambiguity. -/
@[simp]
theorem chapterVIDGlobalTBase_eq_tBase :
    chapterVIDGlobalTBase = chapterVIDTBase := by
  rfl

@[simp]
theorem chapterVIDGlobalTBase_pow :
    chapterVIDGlobalTBase ^ (3 : ℤ) =
      chapterVIKeplerExponential chapterVIDEccentricity chapterVIDX := by
  unfold chapterVIDGlobalTBase
  rw [zpow_ofNat, chapterVIDRootToOriginalContour_pow,
    chapterVIDCollisionLift_pow]

theorem chapterVIDGlobalTBase_ne_zero : chapterVIDGlobalTBase ≠ 0 := by
  apply chapterVIDRootToOriginalContour_ne_zero
  intro hzero
  have hpow := congrArg (fun z : ℂ ↦ z ^ 3) hzero
  rw [chapterVIDCollisionLift_pow, zero_pow (by norm_num)] at hpow
  exact chapterVIDX_ne_zero hpow

/-- The explicit global collision lift does not meet the ramification point `u=0`. -/
theorem chapterVIDCollisionLift_ne_zero : chapterVIDCollisionLift ≠ 0 := by
  intro hzero
  have hpow := congrArg (fun z : ℂ ↦ z ^ 3) hzero
  rw [chapterVIDCollisionLift_pow, zero_pow (by norm_num)] at hpow
  exact chapterVIDX_ne_zero hpow

/-- Poincaré's exact `u ↦ t` coordinate change is unramified at the collision.  The proof
differentiates its certified cubing identity and reduces nonvanishing to the first Kepler
criticality condition already verified at D. -/
theorem deriv_chapterVIDRootToOriginalContour_collision_ne_zero :
    deriv chapterVIDRootToOriginalContour chapterVIDCollisionLift ≠ 0 := by
  let u := chapterVIDCollisionLift
  have hu : u ≠ 0 := chapterVIDCollisionLift_ne_zero
  have hx : u ^ 3 ≠ 0 := pow_ne_zero 3 hu
  have hf :=
    (analyticAt_chapterVIDRootToOriginalContour hu).differentiableAt.hasDerivAt
  have hleft := hf.pow 3
  have hright :=
    (hasDerivAt_chapterVIKeplerExponential chapterVIDEccentricity hx).comp u
      ((hasDerivAt_id u).pow 3)
  have hrightRoot := hright.congr_of_eventuallyEq
    (Filter.Eventually.of_forall
      (fun w : ℂ ↦ chapterVIDRootToOriginalContour_pow w))
  have hderivEq := hleft.unique hrightRoot
  intro hzero
  rw [hzero, mul_zero] at hderivEq
  have hcritical :
      chapterVIKeplerExponentialDerivative chapterVIDEccentricity (u ^ 3) ≠ 0 := by
    simpa [u, chapterVIDCollisionLift_pow] using chapterVID_firstKeplerCritical
  have hinner : (↑3 * id u ^ (3 - 1) * 1 : ℂ) ≠ 0 := by
    simp only [id_eq, Nat.reduceSubDiff, mul_one]
    exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hu)
  exact hcritical ((mul_eq_zero.mp hderivEq.symm).resolve_right hinner)

/-- The explicit global endpoint maps back to the anomaly pair `(x_D,y_D)` used to define the
local inverse branches. -/
theorem chapterVIDGlobalTBase_anomalyPair :
    chapterVIPoincareAnomalyPair (-1) 3 chapterVIDEccentricity 0
        (chapterVIDX, chapterVIDY) chapterVIDX_ne_zero chapterVIDY_ne_zero
        chapterVID_firstKeplerCritical chapterVID_secondKeplerCritical (by norm_num)
        (chapterVIDZBase, chapterVIDGlobalTBase) =
      (chapterVIDX, chapterVIDY) := by
  exact chapterVIPoincareAnomalyPair_apply_base (-1) 3 chapterVIDEccentricity 0
    (chapterVIDX, chapterVIDY) chapterVIDX_ne_zero chapterVIDY_ne_zero
    chapterVID_firstKeplerCritical chapterVID_secondKeplerCritical (by norm_num)
    chapterVIDGlobalTBase chapterVIDGlobalTBase_pow

/-- The local construction's selected `t_D` differs from the global endpoint by this deck
multiplier. -/
noncomputable def chapterVIDTDeckMultiplier : ℂ :=
  chapterVIDTBase * chapterVIDGlobalTBase⁻¹

@[simp]
theorem chapterVIDTDeckMultiplier_eq_one :
    chapterVIDTDeckMultiplier = 1 := by
  unfold chapterVIDTDeckMultiplier
  rw [chapterVIDGlobalTBase_eq_tBase]
  exact mul_inv_cancel₀ chapterVIDTBase_ne_zero

theorem chapterVIDTDeckMultiplier_mul_global :
    chapterVIDTDeckMultiplier * chapterVIDGlobalTBase = chapterVIDTBase := by
  rw [chapterVIDTDeckMultiplier_eq_one, one_mul,
    chapterVIDGlobalTBase_eq_tBase]

theorem chapterVIDTDeckMultiplier_pow_three :
    chapterVIDTDeckMultiplier ^ 3 = 1 := by
  unfold chapterVIDTDeckMultiplier
  rw [mul_pow, inv_pow, ← zpow_ofNat, chapterVIDTBase_pow,
    ← zpow_ofNat, chapterVIDGlobalTBase_pow]
  exact mul_inv_cancel₀
    (chapterVIKeplerExponential_ne_zero chapterVIDEccentricity chapterVIDX_ne_zero)

theorem chapterVIDTDeckMultiplier_ne_zero : chapterVIDTDeckMultiplier ≠ 0 := by
  intro hzero
  have hpow := chapterVIDTDeckMultiplier_pow_three
  rw [hzero, zero_pow (by norm_num)] at hpow
  norm_num at hpow

/-- The exact global `u` coordinate, followed by the unique cubic deck transformation that
matches the local inverse branch selected in the Morse construction. -/
noncomputable def chapterVIDDeckedRootToLocalContour (u : ℂ) : ℂ :=
  chapterVIDTDeckMultiplier * chapterVIDRootToOriginalContour u

@[simp]
theorem chapterVIDDeckedRootToLocalContour_eq (u : ℂ) :
    chapterVIDDeckedRootToLocalContour u =
      chapterVIDRootToOriginalContour u := by
  simp [chapterVIDDeckedRootToLocalContour]

@[simp]
theorem chapterVIDDeckedRootToLocalContour_collision :
    chapterVIDDeckedRootToLocalContour chapterVIDCollisionLift = chapterVIDTBase := by
  exact chapterVIDTDeckMultiplier_mul_global

theorem analyticAt_chapterVIDDeckedRootToLocalContour_collision :
    AnalyticAt ℂ chapterVIDDeckedRootToLocalContour chapterVIDCollisionLift := by
  unfold chapterVIDDeckedRootToLocalContour
  exact analyticAt_const.mul
    (analyticAt_chapterVIDRootToOriginalContour chapterVIDCollisionLift_ne_zero)

/-- The global contour coordinate enters the selected local source chart transversely.  Thus
the global D pinch and the local logarithmic segment are related by a genuine local analytic
coordinate, not merely by equality of their endpoint values. -/
theorem deriv_chapterVIDDeckedRootToLocalContour_collision_ne_zero :
    deriv chapterVIDDeckedRootToLocalContour chapterVIDCollisionLift ≠ 0 := by
  have hroot :=
    (analyticAt_chapterVIDRootToOriginalContour
      chapterVIDCollisionLift_ne_zero).differentiableAt.hasDerivAt
  have hdeck := hroot.const_mul chapterVIDTDeckMultiplier
  have hderiv :
      deriv chapterVIDDeckedRootToLocalContour chapterVIDCollisionLift =
        chapterVIDTDeckMultiplier *
          deriv chapterVIDRootToOriginalContour chapterVIDCollisionLift := by
    exact hdeck.deriv
  rw [hderiv]
  exact mul_ne_zero chapterVIDTDeckMultiplier_ne_zero
    deriv_chapterVIDRootToOriginalContour_collision_ne_zero

/-- The explicit endpoint is itself a genuine order-two zero of Poincaré's literal convergent
`(z,t)` radicand. -/
theorem analyticOrderAt_chapterVIDRadicand_globalTBase_eq_two :
    analyticOrderAt (fun w ↦ chapterVIDRadicand (chapterVIDZBase, w))
      chapterVIDGlobalTBase = 2 := by
  apply analyticOrderAt_chapterVIPoincareRadicand_sourceFiber_eq_two
    (-1) 3 chapterVIDEccentricity chapterVIDComplement 0 1 2 2
    (chapterVIDX, chapterVIDY) chapterVIDX_ne_zero chapterVIDY_ne_zero
    chapterVID_firstKeplerCritical chapterVID_secondKeplerCritical (by norm_num)
    chapterVIDGlobalTBase chapterVIDGlobalTBase_ne_zero chapterVIDGlobalTBase_pow
  · rw [chapterVIPoincareCollisionFactorPlus_apply_base
      (-1) 3 chapterVIDEccentricity chapterVIDComplement 0 1 2
      (chapterVIDX, chapterVIDY) chapterVIDX_ne_zero chapterVIDY_ne_zero
      chapterVID_firstKeplerCritical chapterVID_secondKeplerCritical (by norm_num)
      chapterVIDGlobalTBase chapterVIDGlobalTBase_pow]
    exact chapterVID_collisionFactorPlus
  · exact deriv_chapterVIDPoincareCollisionFactorPlus_eq_zero
      chapterVIDGlobalTBase_ne_zero chapterVIDGlobalTBase_pow
  · exact deriv_deriv_chapterVIDPoincareCollisionFactorPlus_ne_zero
      chapterVIDGlobalTBase_ne_zero chapterVIDGlobalTBase_pow
  · rw [chapterVIPoincareCollisionFactorMinus_apply_base
      (-1) 3 chapterVIDEccentricity chapterVIDComplement 0 1 2
      (chapterVIDX, chapterVIDY) chapterVIDX_ne_zero chapterVIDY_ne_zero
      chapterVID_firstKeplerCritical chapterVID_secondKeplerCritical (by norm_num)
      chapterVIDGlobalTBase chapterVIDGlobalTBase_pow]
    exact chapterVID_collisionFactorMinus_ne_zero

/-- The global pinch and the local logarithmic model are based at the same source point, up to
the explicitly certified cubic deck transformation.  The remaining global task is therefore
cycle placement, not identification of the singularity or its local analytic type. -/
structure ChapterVIDGlobalLocalPinchBridge where
  globalPinch : ChapterVIDRootCoordinatePinch
  globalT : ℂ
  globalT_pow : globalT ^ (3 : ℤ) =
    chapterVIKeplerExponential chapterVIDEccentricity chapterVIDX
  globalAnomalyPair :
    chapterVIPoincareAnomalyPair (-1) 3 chapterVIDEccentricity 0
        (chapterVIDX, chapterVIDY) chapterVIDX_ne_zero chapterVIDY_ne_zero
        chapterVID_firstKeplerCritical chapterVID_secondKeplerCritical (by norm_num)
        (chapterVIDZBase, globalT) = (chapterVIDX, chapterVIDY)
  localDeckMultiplier : ℂ
  localDeckMultiplier_pow : localDeckMultiplier ^ 3 = 1
  localDeckMultiplier_mul_global : localDeckMultiplier * globalT = chapterVIDTBase
  globalFiberOrder :
    analyticOrderAt (fun w ↦ chapterVIDRadicand (chapterVIDZBase, w)) globalT = 2

noncomputable def chapterVIDGlobalLocalPinchBridge : ChapterVIDGlobalLocalPinchBridge where
  globalPinch := chapterVIDRootCoordinatePinch
  globalT := chapterVIDGlobalTBase
  globalT_pow := chapterVIDGlobalTBase_pow
  globalAnomalyPair := chapterVIDGlobalTBase_anomalyPair
  localDeckMultiplier := chapterVIDTDeckMultiplier
  localDeckMultiplier_pow := chapterVIDTDeckMultiplier_pow_three
  localDeckMultiplier_mul_global := chapterVIDTDeckMultiplier_mul_global
  globalFiberOrder := analyticOrderAt_chapterVIDRadicand_globalTBase_eq_two

/-- The globally certified D pinch reaches the same nondegenerate local singularity whose
prepared inverse branch has a nonzero logarithmic coefficient. -/
theorem chapterVIDGlobalPinch_reaches_nonzeroLocalLogModel :
    analyticOrderAt (fun w ↦ chapterVIDRadicand (chapterVIDZBase, w))
        chapterVIDGlobalTBase = 2 ∧
      chapterVIDCenteredFiberAmplitude 0 ≠ 0 :=
  ⟨analyticOrderAt_chapterVIDRadicand_globalTBase_eq_two,
    chapterVIDCenteredFiberAmplitude_zero_ne⟩

end PoincareChapterVI
