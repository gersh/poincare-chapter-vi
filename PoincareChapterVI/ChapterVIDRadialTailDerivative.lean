/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.ChapterVIDRadialTailReduction
import PoincareChapterVI.ChapterVILeanCompCertCartesianFactorDerivativeTrace

/-!
# Exact total derivative used by the radial-tail certificate

The connector derivative tables differentiate only in the contour coordinate `u`.  Along the
radial tail both `ζ` and `u` vary.  This file gives a sparse total-derivative formula for the two
literal collision factors and their product, and proves the real-parameter chain rule.  The
formula uses the same anomaly and Laurent primitives as the existing Cartesian interval traces.
-/

noncomputable section

open Complex

namespace PoincareChapterVI

/-- Sparse first collision factor used by the polar certificate. -/
def chapterVIDRadialTailFactorPlus (ζ u : ℂ) : ℂ :=
  (1 / 10001 : ℂ) * (10000 * u ^ 3 + (u ^ 3)⁻¹ - 200) -
    2 * chapterVIDRootSecondAnomaly ζ u

/-- Sparse companion collision factor used by the polar certificate. -/
def chapterVIDRadialTailFactorMinus (ζ u : ℂ) : ℂ :=
  (1 / 10001 : ℂ) * (u ^ 3 + 10000 * (u ^ 3)⁻¹ - 200) -
    2 * (chapterVIDRootSecondAnomaly ζ u)⁻¹

theorem chapterVIDRadialTailFactorPlus_eq
    {ζ u : ℂ} (hζ : ζ ≠ 0) (hu : u ≠ 0) :
    chapterVIDRadialTailFactorPlus ζ u =
      chapterVIDRootCoordinateCollisionFactorPlus ζ u := by
  rw [chapterVIDRootCoordinateCollisionFactorPlus_eq_polarCertificateFormula hζ hu]
  norm_num [chapterVIDRadialTailFactorPlus]

theorem chapterVIDRadialTailFactorMinus_eq
    {ζ u : ℂ} (hζ : ζ ≠ 0) (hu : u ≠ 0) :
    chapterVIDRadialTailFactorMinus ζ u =
      chapterVIDRootCoordinateCollisionFactorMinus ζ u := by
  rw [chapterVIDRootCoordinateCollisionFactorMinus_eq_polarCertificateFormula hζ hu]
  norm_num [chapterVIDRadialTailFactorMinus]

/-- Total derivative of the transformed second anomaly when both inputs move. -/
def chapterVIDRadialTailAnomalyDerivative
    (ζ u ζdot udot : ℂ) : ℂ :=
  ζdot * chapterVIDRootSecondAnomaly 1 u +
    ζ * (chapterVIDRootSecondAnomaly 1 u *
      chapterVIDRootSecondAnomalyLogDerivative u * udot)

/-- Total derivative of the sparse first collision factor. -/
def chapterVIDRadialTailFactorPlusDerivative
    (ζ u ζdot udot : ℂ) : ℂ :=
  (1 / 10001 : ℂ) *
      (30000 * u ^ 2 * udot - 3 * (u ^ 3)⁻¹ * u⁻¹ * udot) -
    2 * chapterVIDRadialTailAnomalyDerivative ζ u ζdot udot

/-- Total derivative of the sparse companion collision factor. -/
def chapterVIDRadialTailFactorMinusDerivative
    (ζ u ζdot udot : ℂ) : ℂ :=
  (1 / 10001 : ℂ) *
      (3 * u ^ 2 * udot - 30000 * (u ^ 3)⁻¹ * u⁻¹ * udot) +
    2 * (chapterVIDRootSecondAnomaly ζ u)⁻¹ ^ 2 *
      chapterVIDRadialTailAnomalyDerivative ζ u ζdot udot

/-- Product-rule total derivative of Poincare's literal transformed radicand. -/
def chapterVIDRadialTailRadicandDerivative
    (ζ u ζdot udot : ℂ) : ℂ :=
  chapterVIDRadialTailFactorPlusDerivative ζ u ζdot udot *
      chapterVIDRadialTailFactorMinus ζ u +
    chapterVIDRadialTailFactorPlus ζ u *
      chapterVIDRadialTailFactorMinusDerivative ζ u ζdot udot

/-- Cancellation-preserving form of the total derivative.  The two `4L` terms produced by the
raw product rule have already cancelled in this expression. -/
def chapterVIDRadialTailRadicandDerivativeReduced
    (ζ u ζlog udot : ℂ) : ℂ :=
  let y := chapterVIDRootSecondAnomaly ζ u
  let A := (1 / 10001 : ℂ) * (10000 * u ^ 3 + (u ^ 3)⁻¹ - 200)
  let B := (1 / 10001 : ℂ) * (u ^ 3 + 10000 * (u ^ 3)⁻¹ - 200)
  let a := (1 / 10001 : ℂ) *
    (30000 * u ^ 2 * udot - 3 * (u ^ 3)⁻¹ * u⁻¹ * udot)
  let b := (1 / 10001 : ℂ) *
    (3 * u ^ 2 * udot - 30000 * (u ^ 3)⁻¹ * u⁻¹ * udot)
  let L := chapterVIDRootSecondAnomalyLogDerivative u * udot + ζlog
  a * B + A * b - 2 * (a * y⁻¹ + y * b) + 2 * L * (A * y⁻¹ - y * B)

theorem chapterVIDRadialTailRadicandDerivative_eq_reduced
    {ζ u ζlog udot : ℂ} (hζ : ζ ≠ 0) (hu : u ≠ 0) :
    chapterVIDRadialTailRadicandDerivative ζ u (ζlog * ζ) udot =
      chapterVIDRadialTailRadicandDerivativeReduced ζ u ζlog udot := by
  have hy : chapterVIDRootSecondAnomaly ζ u ≠ 0 :=
    mul_ne_zero hζ (chapterVIDRootToOriginalContour_ne_zero hu)
  unfold chapterVIDRadialTailRadicandDerivativeReduced
    chapterVIDRadialTailRadicandDerivative
    chapterVIDRadialTailFactorPlusDerivative
    chapterVIDRadialTailFactorMinusDerivative
    chapterVIDRadialTailAnomalyDerivative
    chapterVIDRadialTailFactorPlus chapterVIDRadialTailFactorMinus
  have hanomaly :
      ζlog * ζ * chapterVIDRootSecondAnomaly 1 u +
          ζ * (chapterVIDRootSecondAnomaly 1 u *
            chapterVIDRootSecondAnomalyLogDerivative u * udot) =
        chapterVIDRootSecondAnomaly ζ u *
          (chapterVIDRootSecondAnomalyLogDerivative u * udot + ζlog) := by
    unfold chapterVIDRootSecondAnomaly
    ring
  rw [hanomaly]
  field_simp [hy]
  ring

/-- Exact chain rule for the moving transformed anomaly. -/
theorem hasDerivAt_chapterVIDRootSecondAnomaly_comp
    {ζ u : ℝ → ℂ} {s : ℝ} {ζdot udot : ℂ}
    (hζ : HasDerivAt ζ ζdot s) (hu : HasDerivAt u udot s)
    (hu0 : u s ≠ 0) :
    HasDerivAt (fun x ↦ chapterVIDRootSecondAnomaly (ζ x) (u x))
      (chapterVIDRadialTailAnomalyDerivative (ζ s) (u s) ζdot udot) s := by
  have hbaseComplex := hasDerivAt_chapterVIDRootSecondAnomaly
    (ζ := (1 : ℂ)) hu0
  have hbase : HasDerivAt
      (fun x : ℝ ↦ chapterVIDRootSecondAnomaly 1 (u x))
      (chapterVIDRootSecondAnomaly 1 (u s) *
        chapterVIDRootSecondAnomalyLogDerivative (u s) * udot) s := by
    apply (hbaseComplex.scomp s hu).congr_deriv
    simp only [smul_eq_mul]
    ring
  have hproduct := hζ.mul hbase
  have hproduct' : HasDerivAt
      (fun x : ℝ ↦ ζ x * chapterVIDRootSecondAnomaly 1 (u x))
      (chapterVIDRadialTailAnomalyDerivative (ζ s) (u s) ζdot udot) s := by
    apply hproduct.congr_deriv
    unfold chapterVIDRadialTailAnomalyDerivative
    ring
  apply hproduct'.congr_of_eventuallyEq
  filter_upwards [] with x
  unfold chapterVIDRootSecondAnomaly
  ring

/-- Exact chain rule for the first sparse collision factor. -/
theorem hasDerivAt_chapterVIDRadialTailFactorPlus_comp
    {ζ u : ℝ → ℂ} {s : ℝ} {ζdot udot : ℂ}
    (hζ : HasDerivAt ζ ζdot s) (hu : HasDerivAt u udot s)
    (hu0 : u s ≠ 0) :
    HasDerivAt (fun x ↦ chapterVIDRadialTailFactorPlus (ζ x) (u x))
      (chapterVIDRadialTailFactorPlusDerivative (ζ s) (u s) ζdot udot) s := by
  have hu3 := hu.pow 3
  have hu3ne : u s ^ 3 ≠ 0 := pow_ne_zero 3 hu0
  have hinv := hu3.inv hu3ne
  have hy := hasDerivAt_chapterVIDRootSecondAnomaly_comp hζ hu hu0
  have h := ((hasDerivAt_const s (1 / 10001 : ℂ)).mul
    ((((hasDerivAt_const s (10000 : ℂ)).mul hu3).add hinv).sub_const 200)).sub
      ((hasDerivAt_const s (2 : ℂ)).mul hy)
  have h' : HasDerivAt
      (fun x : ℝ ↦ (1 / 10001 : ℂ) *
        ((10000 : ℂ) * u x ^ 3 + (u x ^ 3)⁻¹ - 200) -
          2 * chapterVIDRootSecondAnomaly (ζ x) (u x))
      (chapterVIDRadialTailFactorPlusDerivative (ζ s) (u s) ζdot udot) s := by
    apply h.congr_deriv
    unfold chapterVIDRadialTailFactorPlusDerivative
    simp only [Pi.pow_apply]
    field_simp [hu0]
    ring
  apply h'.congr_of_eventuallyEq
  filter_upwards [] with x
  rfl

/-- Exact chain rule for the companion sparse collision factor. -/
theorem hasDerivAt_chapterVIDRadialTailFactorMinus_comp
    {ζ u : ℝ → ℂ} {s : ℝ} {ζdot udot : ℂ}
    (hζ : HasDerivAt ζ ζdot s) (hu : HasDerivAt u udot s)
    (hζ0 : ζ s ≠ 0) (hu0 : u s ≠ 0) :
    HasDerivAt (fun x ↦ chapterVIDRadialTailFactorMinus (ζ x) (u x))
      (chapterVIDRadialTailFactorMinusDerivative (ζ s) (u s) ζdot udot) s := by
  have hu3 := hu.pow 3
  have hu3ne : u s ^ 3 ≠ 0 := pow_ne_zero 3 hu0
  have hinv := hu3.inv hu3ne
  have hy := hasDerivAt_chapterVIDRootSecondAnomaly_comp hζ hu hu0
  have hy0 : chapterVIDRootSecondAnomaly (ζ s) (u s) ≠ 0 :=
    mul_ne_zero hζ0 (chapterVIDRootToOriginalContour_ne_zero hu0)
  have hyinv := hy.inv hy0
  have h := ((hasDerivAt_const s (1 / 10001 : ℂ)).mul
    (((hu3.add ((hasDerivAt_const s (10000 : ℂ)).mul hinv)).sub_const 200))).sub
      ((hasDerivAt_const s (2 : ℂ)).mul hyinv)
  have h' : HasDerivAt
      (fun x : ℝ ↦ (1 / 10001 : ℂ) *
        (u x ^ 3 + 10000 * (u x ^ 3)⁻¹ - 200) -
          2 * (chapterVIDRootSecondAnomaly (ζ x) (u x))⁻¹)
      (chapterVIDRadialTailFactorMinusDerivative (ζ s) (u s) ζdot udot) s := by
    apply h.congr_deriv
    unfold chapterVIDRadialTailFactorMinusDerivative
    simp only [Pi.pow_apply]
    field_simp [hu0, hy0]
    ring
  apply h'.congr_of_eventuallyEq
  filter_upwards [] with x
  rfl

/-- The named total derivative differentiates the literal transformed radicand along arbitrary
real differentiable input paths. -/
theorem hasDerivAt_chapterVIDRootCoordinateRadicand_comp
    {ζ u : ℝ → ℂ} {s : ℝ} {ζdot udot : ℂ}
    (hζ : HasDerivAt ζ ζdot s) (hu : HasDerivAt u udot s)
    (hζ0 : ζ s ≠ 0) (hu0 : u s ≠ 0) :
    HasDerivAt (fun x ↦ chapterVIDRootCoordinateRadicand (ζ x) (u x))
      (chapterVIDRadialTailRadicandDerivative (ζ s) (u s) ζdot udot) s := by
  have hplus := hasDerivAt_chapterVIDRadialTailFactorPlus_comp hζ hu hu0
  have hminus := hasDerivAt_chapterVIDRadialTailFactorMinus_comp hζ hu hζ0 hu0
  have hproduct := hplus.mul hminus
  have hproduct' : HasDerivAt
      (fun x : ℝ ↦ chapterVIDRadialTailFactorPlus (ζ x) (u x) *
        chapterVIDRadialTailFactorMinus (ζ x) (u x))
      (chapterVIDRadialTailRadicandDerivative (ζ s) (u s) ζdot udot) s := by
    apply hproduct.congr_deriv
    unfold chapterVIDRadialTailRadicandDerivative
    ring
  apply hproduct'.congr_of_eventuallyEq
  filter_upwards [hζ.continuousAt.eventually_ne hζ0,
    hu.continuousAt.eventually_ne hu0] with x hζx hux
  rw [chapterVIDRootCoordinateRadicand_eq_factors,
    ← chapterVIDRadialTailFactorPlus_eq hζx hux,
    ← chapterVIDRadialTailFactorMinus_eq hζx hux]

end PoincareChapterVI
