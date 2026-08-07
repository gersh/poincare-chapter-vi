/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# The Jacobian rescaling in Poincaré's Chapter VI, §102

Poincaré considers six singular points `z₁, ..., z₆`, depending on five orbital parameters,
and introduces one additional scaling parameter `ζ`. He reduces the six-by-six Jacobian of
`zᵢ / ζ` to the five-by-five Jacobian of the ratios `z₂ / z₁, ..., z₆ / z₁`.

This file verifies the determinant identity at the level of the values `zᵢ` and their table of
parameter derivatives. It does not prove that the singular points exist, vary analytically, or
satisfy the rank conclusion asserted earlier in §102.
-/

noncomputable section

namespace PoincareChapterVI

open Matrix

/-- The six-by-six matrix obtained by adjoining the column `-z` to a table of derivatives with
respect to five parameters. -/
def chapterVIAugmentedDerivativeMatrix
    (z : Fin 6 → ℂ) (derivative : Matrix (Fin 6) (Fin 5) ℂ) :
    Matrix (Fin 6) (Fin 6) ℂ :=
  fun i j ↦ Fin.cases (-z i) (derivative i) j

@[simp]
theorem chapterVIAugmentedDerivativeMatrix_zero
    (z : Fin 6 → ℂ) (derivative : Matrix (Fin 6) (Fin 5) ℂ) (i : Fin 6) :
    chapterVIAugmentedDerivativeMatrix z derivative i 0 = -z i :=
  rfl

@[simp]
theorem chapterVIAugmentedDerivativeMatrix_succ
    (z : Fin 6 → ℂ) (derivative : Matrix (Fin 6) (Fin 5) ℂ)
    (i : Fin 6) (j : Fin 5) :
    chapterVIAugmentedDerivativeMatrix z derivative i j.succ = derivative i j :=
  rfl

/-- The derivative table given by the quotient rule for
`z_(i+1) / z_1`, with the derivatives supplied separately. -/
def chapterVIRatioDerivativeMatrix
    (z : Fin 6 → ℂ) (derivative : Matrix (Fin 6) (Fin 5) ℂ) :
    Matrix (Fin 5) (Fin 5) ℂ :=
  fun i j ↦
    (z 0 * derivative i.succ j - z i.succ * derivative 0 j) / z 0 ^ 2

/-- The row-reduced derivative table before the final quotient-rule scaling. -/
def chapterVIReducedDerivativeMatrix
    (z : Fin 6 → ℂ) (derivative : Matrix (Fin 6) (Fin 5) ℂ) :
    Matrix (Fin 5) (Fin 5) ℂ :=
  fun i j ↦ derivative i.succ j - (z i.succ / z 0) * derivative 0 j

/-- The determinant identity behind the Jacobian calculation in §102 before introducing the
extra scaling parameter `ζ`. -/
theorem chapterVI_augmentedDerivative_det
    (z : Fin 6 → ℂ) (derivative : Matrix (Fin 6) (Fin 5) ℂ)
    (hz : z 0 ≠ 0) :
    (chapterVIAugmentedDerivativeMatrix z derivative).det =
      -z 0 ^ 6 * (chapterVIRatioDerivativeMatrix z derivative).det := by
  let augmented := chapterVIAugmentedDerivativeMatrix z derivative
  let stepOne := updateRow augmented 1
    (augmented 1 + (-z 1 / z 0) • augmented 0)
  let stepTwo := updateRow stepOne 2
    (stepOne 2 + (-z 2 / z 0) • stepOne 0)
  let stepThree := updateRow stepTwo 3
    (stepTwo 3 + (-z 3 / z 0) • stepTwo 0)
  let stepFour := updateRow stepThree 4
    (stepThree 4 + (-z 4 / z 0) • stepThree 0)
  let stepFive := updateRow stepFour 5
    (stepFour 5 + (-z 5 / z 0) • stepFour 0)
  let reduced := chapterVIReducedDerivativeMatrix z derivative
  let eliminated := stepFive
  have hstepOne : stepOne.det = augmented.det := by
    exact det_updateRow_add_smul_self augmented (by decide) (-z 1 / z 0)
  have hstepTwo : stepTwo.det = stepOne.det := by
    exact det_updateRow_add_smul_self stepOne (by decide) (-z 2 / z 0)
  have hstepThree : stepThree.det = stepTwo.det := by
    exact det_updateRow_add_smul_self stepTwo (by decide) (-z 3 / z 0)
  have hstepFour : stepFour.det = stepThree.det := by
    exact det_updateRow_add_smul_self stepThree (by decide) (-z 4 / z 0)
  have hstepFive : stepFive.det = stepFour.det := by
    exact det_updateRow_add_smul_self stepFour (by decide) (-z 5 / z 0)
  have heliminated : eliminated.det = augmented.det := by
    rw [show eliminated = stepFive from rfl, hstepFive, hstepFour, hstepThree, hstepTwo,
      hstepOne]
  have heliminatedZero : eliminated 0 0 = -z 0 := by
    simp [eliminated, stepFive, stepFour, stepThree, stepTwo, stepOne, augmented]
  have heliminatedSuccZero (i : Fin 5) : eliminated i.succ 0 = 0 := by
    fin_cases i <;>
      simp [eliminated, stepFive, stepFour, stepThree, stepTwo, stepOne, augmented,
        updateRow_apply, hz]
  have hminor : eliminated.submatrix (0 : Fin 6).succAbove Fin.succ = reduced := by
    ext i j
    simp only [Matrix.submatrix_apply, Fin.succAbove_zero]
    fin_cases i <;>
      simp [eliminated, stepFive, stepFour, stepThree, stepTwo, stepOne, augmented, reduced,
        chapterVIAugmentedDerivativeMatrix, chapterVIReducedDerivativeMatrix,
        updateRow_apply] <;>
      field_simp [hz] <;> ring
  have heliminatedDet : eliminated.det = -z 0 * reduced.det := by
    rw [det_succ_column_zero, Fin.sum_univ_succ]
    rw [hminor]
    simp [heliminatedZero, heliminatedSuccZero]
  have hratio : chapterVIRatioDerivativeMatrix z derivative = (z 0)⁻¹ • reduced := by
    ext i j
    simp only [chapterVIRatioDerivativeMatrix, reduced, chapterVIReducedDerivativeMatrix,
      Matrix.smul_apply, smul_eq_mul]
    field_simp [hz]
  have hratioDet : (chapterVIRatioDerivativeMatrix z derivative).det =
      (z 0)⁻¹ ^ 5 * reduced.det := by
    rw [hratio, det_smul]
    norm_num
  calc
    (chapterVIAugmentedDerivativeMatrix z derivative).det = augmented.det := rfl
    _ = eliminated.det := heliminated.symm
    _ = -z 0 * reduced.det := heliminatedDet
    _ = -z 0 ^ 6 * (chapterVIRatioDerivativeMatrix z derivative).det := by
      rw [hratioDet]
      field_simp [hz]

/-- The scaled six-by-six Jacobian is a scalar multiple of an augmented derivative matrix. -/
theorem chapterVI_scaledJacobian_eq_smul
    (z : Fin 6 → ℂ) (derivative : Matrix (Fin 6) (Fin 5) ℂ) (ζ : ℂ) (hζ : ζ ≠ 0) :
    (fun i : Fin 6 ↦ fun j : Fin 6 ↦
      Fin.cases (-z i / ζ ^ 2) (fun parameter ↦ derivative i parameter / ζ) j) =
      ζ⁻¹ • chapterVIAugmentedDerivativeMatrix (fun i ↦ z i / ζ) derivative := by
  ext i j
  refine Fin.cases ?_ (fun parameter ↦ ?_) j
  · change -z i / ζ ^ 2 = ζ⁻¹ * (-(z i / ζ))
    field_simp [hζ]
  · change derivative i parameter / ζ = ζ⁻¹ * derivative i parameter
    field_simp [hζ]

/-- Scaling every singular point by `ζ⁻¹` scales its five ratio derivatives by `ζ`. -/
theorem chapterVI_ratioDerivative_scaled
    (z : Fin 6 → ℂ) (derivative : Matrix (Fin 6) (Fin 5) ℂ) (ζ : ℂ)
    (hz : z 0 ≠ 0) (hζ : ζ ≠ 0) :
    chapterVIRatioDerivativeMatrix (fun i ↦ z i / ζ) derivative =
      ζ • chapterVIRatioDerivativeMatrix z derivative := by
  ext i j
  simp only [chapterVIRatioDerivativeMatrix, Matrix.smul_apply, smul_eq_mul]
  field_simp [hz, hζ]

/-- The scalar simplification that produces Poincaré's power `ζ⁻⁷`. -/
theorem chapterVI_scaledJacobian_factor
    (z₁ ζ determinant : ℂ) (hζ : ζ ≠ 0) :
    ζ⁻¹ ^ 6 * (-(z₁ / ζ) ^ 6 * (ζ ^ 5 * determinant)) =
      (-z₁ ^ 6 / ζ ^ 7) * determinant := by
  field_simp [hζ]

/-- Poincaré's exact §102 Jacobian factor. The matrix on the left is the derivative table of
the six functions `zᵢ / ζ` with respect to `ζ` and the five orbital parameters. -/
theorem chapterVI_scaledSingularities_jacobian_det
    (z : Fin 6 → ℂ) (derivative : Matrix (Fin 6) (Fin 5) ℂ) (ζ : ℂ)
    (hz : z 0 ≠ 0) (hζ : ζ ≠ 0) :
    det (fun i : Fin 6 ↦ fun j : Fin 6 ↦
      Fin.cases (-z i / ζ ^ 2) (fun parameter ↦ derivative i parameter / ζ) j) =
      (-z 0 ^ 6 / ζ ^ 7) * (chapterVIRatioDerivativeMatrix z derivative).det := by
  let scaledPoint : Fin 6 → ℂ := fun i ↦ z i / ζ
  have hscaledPoint : scaledPoint 0 ≠ 0 := div_ne_zero hz hζ
  have hratioDet : (chapterVIRatioDerivativeMatrix scaledPoint derivative).det =
      ζ ^ 5 * (chapterVIRatioDerivativeMatrix z derivative).det := by
    rw [show chapterVIRatioDerivativeMatrix scaledPoint derivative =
      ζ • chapterVIRatioDerivativeMatrix z derivative from
        chapterVI_ratioDerivative_scaled z derivative ζ hz hζ, det_smul]
    norm_num
  calc
    det (fun i : Fin 6 ↦ fun j : Fin 6 ↦
        Fin.cases (-z i / ζ ^ 2) (fun parameter ↦ derivative i parameter / ζ) j) =
        det (ζ⁻¹ • chapterVIAugmentedDerivativeMatrix scaledPoint derivative) := by
      rw [chapterVI_scaledJacobian_eq_smul z derivative ζ hζ]
    _ = ζ⁻¹ ^ 6 * (chapterVIAugmentedDerivativeMatrix scaledPoint derivative).det := by
      rw [det_smul]
      norm_num
    _ = ζ⁻¹ ^ 6 *
        (-scaledPoint 0 ^ 6 * (chapterVIRatioDerivativeMatrix scaledPoint derivative).det) := by
      rw [chapterVI_augmentedDerivative_det scaledPoint derivative hscaledPoint]
    _ = ζ⁻¹ ^ 6 * (-scaledPoint 0 ^ 6 *
        (ζ ^ 5 * (chapterVIRatioDerivativeMatrix z derivative).det)) := by rw [hratioDet]
    _ = (-z 0 ^ 6 / ζ ^ 7) * (chapterVIRatioDerivativeMatrix z derivative).det := by
      exact chapterVI_scaledJacobian_factor (z 0) ζ
        (chapterVIRatioDerivativeMatrix z derivative).det hζ

end PoincareChapterVI
