/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.Section103.Certificate
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.NumberTheory.Zsqrtd.GaussianInt

/-!
# The geometric origin of the Chapter VI, §103 certificate

This file derives the coefficient matrix in `ChapterVISection103Certificate` from an exact pair
of spatial Kepler ellipses.  It keeps the calculation finite: a homogenized coordinate difference
has the five monomial slots

`x²y`, `xy²`, `xyz`, `xz²`, `yz²`,

and the coefficient of a monomial in the directional derivative of
`P = ∑ᵢ Uᵢ²` is obtained by convolution of those five slots.

The first ellipse has eccentricity `3/5` and minor-axis factor `4/5`.  The second has eccentricity
`5/13`, minor-axis factor `12/13`, and semimajor-axis ratio `2`.  Its plane is obtained from the
first by the rational rotation associated to the quaternion `(1,2,3,4)`.

This supplies a checked bridge from the geometric inputs to the nonsingular minor.  It is not a
substitute for the projective Bézout and local-intersection arguments earlier in §103.
-/

noncomputable section

open scoped BigOperators

namespace PoincareChapterVI

private abbrev Vec3 := Fin 3 → ℂ

private abbrev Exp3 := Fin 3 → ℕ

private def firstMajorAxis : Vec3 := ![1, 0, 0]

private def firstMinorAxis : Vec3 := ![0, 1, 0]

/-- First column of the rational rotation associated to `(1,2,3,4)`. -/
private def secondMajorAxis : Vec3 := ![-2 / 3, 2 / 3, 1 / 3]

/-- Second column of the rational rotation associated to `(1,2,3,4)`. -/
private def secondMinorAxis : Vec3 := ![2 / 15, -1 / 3, 14 / 15]

/-- The three standard infinitesimal rotation generators. -/
private def rotationGenerator : Fin 3 → Matrix (Fin 3) (Fin 3) ℂ :=
  ![!![0, 0, 0; 0, 0, -1; 0, 1, 0],
    !![0, 0, 1; 0, 0, 0; -1, 0, 0],
    !![0, -1, 0; 1, 0, 0; 0, 0, 0]]

/-- The five exponent vectors of Poincaré's homogenized cubic coordinate differences. -/
private def cubicExponent : Fin 5 → Exp3 :=
  ![![2, 1, 0], ![1, 2, 0], ![1, 1, 1], ![1, 0, 2], ![0, 1, 2]]

/-- The coefficients `(A,B,C,D,E)` in
`U = A x²y + B xy² + C xyz + D xz² + E yz²`. -/
private def coordinateCoefficient : Fin 5 → Vec3 :=
  ![fun i ↦ firstMajorAxis i / 2 - Complex.I * (4 / 5 : ℂ) * firstMinorAxis i / 2,
    fun i ↦ -2 *
      (secondMajorAxis i / 2 - Complex.I * (12 / 13 : ℂ) * secondMinorAxis i / 2),
    fun i ↦ -(3 / 5 : ℂ) * firstMajorAxis i +
      2 * (5 / 13 : ℂ) * secondMajorAxis i,
    fun i ↦ -2 *
      (secondMajorAxis i / 2 + Complex.I * (12 / 13 : ℂ) * secondMinorAxis i / 2),
    fun i ↦ firstMajorAxis i / 2 + Complex.I * (4 / 5 : ℂ) * firstMinorAxis i / 2]

/-- Public access to the five coefficient vectors of the homogenized coordinate difference.
This is the source-level input used to derive the reduced degree-seven equation below. -/
def chapterVISection103CubicCoefficient (slot : Fin 5) (coordinate : Fin 3) : ℂ :=
  coordinateCoefficient slot coordinate

/-- Explicit complex presentation of the cubic coefficients, convenient for exact finite
normalization certificates. -/
def chapterVISection103CubicComplexCoefficient : Fin 5 → Fin 3 → ℂ :=
  ![![1 / 2, -(2 / 5) * Complex.I, 0],
    ![2 / 3 + (8 / 65) * Complex.I, -2 / 3 - (4 / 13) * Complex.I,
      -1 / 3 + (56 / 65) * Complex.I],
    ![-217 / 195, 20 / 39, 10 / 39],
    ![2 / 3 - (8 / 65) * Complex.I, -2 / 3 + (4 / 13) * Complex.I,
      -1 / 3 - (56 / 65) * Complex.I],
    ![1 / 2, (2 / 5) * Complex.I, 0]]

/-- Kernel-checked normalization of the physical ellipse data to the explicit cubic table. -/
theorem chapterVISection103_cubicCoefficient_eq_complexTable
    (slot : Fin 5) (coordinate : Fin 3) :
    chapterVISection103CubicCoefficient slot coordinate =
      chapterVISection103CubicComplexCoefficient slot coordinate := by
  fin_cases slot <;> fin_cases coordinate <;> apply Complex.ext <;>
    norm_num [chapterVISection103CubicCoefficient,
      chapterVISection103CubicComplexCoefficient, coordinateCoefficient,
      firstMajorAxis, firstMinorAxis, secondMajorAxis, secondMinorAxis,
      Complex.mul_re, Complex.mul_im]

/-- Derivative of the five coefficient vectors under one infinitesimal rotation of the second
ellipse. -/
private def coordinateCoefficientDerivative (axis : Fin 3) : Fin 5 → Vec3 :=
  let majorDerivative := (rotationGenerator axis).mulVec secondMajorAxis
  let minorDerivative := (rotationGenerator axis).mulVec secondMinorAxis
  ![fun _ ↦ 0,
    fun i ↦ -2 *
      (majorDerivative i / 2 - Complex.I * (12 / 13 : ℂ) * minorDerivative i / 2),
    fun i ↦ 2 * (5 / 13 : ℂ) * majorDerivative i,
    fun i ↦ -2 *
      (majorDerivative i / 2 + Complex.I * (12 / 13 : ℂ) * minorDerivative i / 2),
    fun _ ↦ 0]

/-- The three monomials used for the nonsingular rotation minor. -/
private def rotationMinorExponent : Fin 3 → Exp3 :=
  ![![1, 1, 4], ![1, 2, 3], ![2, 1, 3]]

/-- Boolean coordinate test for equality between a sum of exponent vectors and a target. -/
private def exponentsAddTo (left right : Fin 5) (target : Exp3) : Bool :=
  cubicExponent left 0 + cubicExponent right 0 == target 0 &&
    cubicExponent left 1 + cubicExponent right 1 == target 1 &&
    cubicExponent left 2 + cubicExponent right 2 == target 2

/-- Finite convolution formula for one coefficient of
`dP = 2 ∑ᵢ Uᵢ dUᵢ`. -/
private def directionalCoefficient (target : Exp3) (axis : Fin 3) : ℂ :=
  2 * ∑ coordinate : Fin 3, ∑ left : Fin 5, ∑ right : Fin 5,
    if exponentsAddTo left right target then
      coordinateCoefficient left coordinate *
        coordinateCoefficientDerivative axis right coordinate
    else 0

/-- Finite convolution formula for one coefficient of `P = ∑ᵢ Uᵢ²`. -/
private def curveCoefficient (target : Exp3) : ℂ :=
  ∑ coordinate : Fin 3, ∑ left : Fin 5, ∑ right : Fin 5,
    if exponentsAddTo left right target then
      coordinateCoefficient left coordinate * coordinateCoefficient right coordinate
    else 0

/-- The coefficient of `x^a y^b` in the affine polynomial `P(x,y,1)`. -/
def chapterVISection103AffineCoefficient (a b : Fin 5) : ℂ :=
  curveCoefficient ![a.val, b.val, 6 - a.val - b.val]

/-- Exact Gaussian-integer coefficients of `50700 * P(x,y,1)`. -/
def chapterVISection103AffineGaussianCoefficient : Fin 5 → Fin 5 → GaussianInt :=
  !![⟨0, 0⟩, ⟨0, 0⟩, ⟨4563, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩;
     ⟨0, 0⟩, ⟨21320, -33280⟩, ⟨-56420, 20800⟩, ⟨46280, -20800⟩, ⟨0, 0⟩;
     ⟨7500, 0⟩, ⟨-118560, 7488⟩, ⟨308826, 0⟩, ⟨-118560, -7488⟩, ⟨7500, 0⟩;
     ⟨0, 0⟩, ⟨46280, 20800⟩, ⟨-56420, -20800⟩, ⟨21320, 33280⟩, ⟨0, 0⟩;
     ⟨0, 0⟩, ⟨0, 0⟩, ⟨4563, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]

/-- The same cleared coefficient table embedded explicitly in `ℂ`. -/
def chapterVISection103AffineClearedComplexCoefficient : Fin 5 → Fin 5 → ℂ :=
  !![0, 0, 4563, 0, 0;
     0, 21320 - 33280 * Complex.I, -56420 + 20800 * Complex.I,
       46280 - 20800 * Complex.I, 0;
     7500, -118560 + 7488 * Complex.I, 308826,
       -118560 - 7488 * Complex.I, 7500;
     0, 46280 + 20800 * Complex.I, -56420 - 20800 * Complex.I,
       21320 + 33280 * Complex.I, 0;
     0, 0, 4563, 0, 0]

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 100000 in
/-- Direct normalization of the geometric convolution to the cleared complex table. -/
theorem chapterVISection103_affineCoefficient_eq_clearedComplex
    (a b : Fin 5) :
    50700 * chapterVISection103AffineCoefficient a b =
      chapterVISection103AffineClearedComplexCoefficient a b := by
  fin_cases a <;> fin_cases b <;> apply Complex.ext <;>
    norm_num (config := { maxSteps := 1000000 })
      [chapterVISection103AffineCoefficient, curveCoefficient, exponentsAddTo,
      cubicExponent, coordinateCoefficient, firstMajorAxis, firstMinorAxis,
      secondMajorAxis, secondMinorAxis, Fin.sum_univ_succ, Matrix.cons_val_two,
      Complex.mul_re, Complex.mul_im, chapterVISection103AffineClearedComplexCoefficient]

/-- The Gaussian and complex presentations of the cleared table agree. -/
theorem chapterVISection103_gaussianCoefficient_toComplex
    (a b : Fin 5) :
    (chapterVISection103AffineGaussianCoefficient a b : ℂ) =
      chapterVISection103AffineClearedComplexCoefficient a b := by
  fin_cases a <;> fin_cases b <;>
    norm_num [chapterVISection103AffineGaussianCoefficient,
      chapterVISection103AffineClearedComplexCoefficient, GaussianInt.toComplex_def,
      sub_eq_add_neg]

/-- Checked bridge from the geometric convolution to the integral coefficient table used by the
Ruppert rank certificate. -/
theorem chapterVISection103_affineCoefficient_eq_gaussian
    (a b : Fin 5) :
    50700 * chapterVISection103AffineCoefficient a b =
      (chapterVISection103AffineGaussianCoefficient a b : ℂ) := by
  rw [chapterVISection103_affineCoefficient_eq_clearedComplex,
    chapterVISection103_gaussianCoefficient_toComplex]

/-- The minor calculated directly from the two ellipses and the infinitesimal rotations. -/
private def derivedRotationMinor : Matrix (Fin 3) (Fin 3) ℂ :=
  fun row axis ↦ directionalCoefficient (rotationMinorExponent row) axis

set_option maxHeartbeats 1000000 in
-- This exhaustively normalizes nine finite convolutions with 3 × 5 × 5 summands each.
/-- Exact finite calculation identifying the geometrically derived coefficient matrix with the
explicit certificate matrix. -/
theorem chapterVISection103_derivedRotationMinor_eq :
    derivedRotationMinor = chapterVISection103RotationMinor := by
  ext row axis
  fin_cases row <;> fin_cases axis <;> apply Complex.ext <;>
    norm_num [derivedRotationMinor, directionalCoefficient, rotationMinorExponent,
      exponentsAddTo, cubicExponent, coordinateCoefficient, coordinateCoefficientDerivative,
      rotationGenerator, firstMajorAxis, firstMinorAxis, secondMajorAxis, secondMinorAxis,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Matrix.cons_val_two,
      Complex.mul_re, Complex.mul_im, chapterVISection103RotationMinor]

/-- Consequently the coefficient minor derived from the physical ellipse data is nonsingular. -/
theorem chapterVISection103_derivedRotationMinor_det_ne_zero :
    derivedRotationMinor.det ≠ 0 := by
  rw [chapterVISection103_derivedRotationMinor_eq]
  exact chapterVISection103RotationMinor_det_ne_zero

/-- The coefficient of `y²z⁴` in `P` is nonzero.  This is the first row used to eliminate a
possible projective rescaling of the curve. -/
theorem chapterVISection103_curveCoefficient_y_sq_z_four :
    curveCoefficient ![0, 2, 4] = (9 / 100 : ℂ) := by
  apply Complex.ext <;>
    norm_num [curveCoefficient, exponentsAddTo, cubicExponent, coordinateCoefficient,
      firstMajorAxis, firstMinorAxis, secondMajorAxis, secondMinorAxis,
      Fin.sum_univ_succ, Matrix.cons_val_two, Complex.mul_re, Complex.mul_im]

/-- Every infinitesimal relative rotation has zero `y²z⁴` coefficient. -/
theorem chapterVISection103_directionalCoefficient_y_sq_z_four (axis : Fin 3) :
    directionalCoefficient ![0, 2, 4] axis = 0 := by
  fin_cases axis <;> apply Complex.ext <;>
    norm_num [directionalCoefficient, exponentsAddTo, cubicExponent, coordinateCoefficient,
      coordinateCoefficientDerivative, rotationGenerator, firstMajorAxis, firstMinorAxis,
      secondMajorAxis, secondMinorAxis, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      Matrix.cons_val_two, Complex.mul_re, Complex.mul_im]

/-- No nonzero infinitesimal relative rotation preserves the projective curve.  If the variation
were `scale • P`, comparison of `y²z⁴` first forces `scale = 0`; nonsingularity of the remaining
three coefficient rows then forces the rotation vector to vanish. -/
theorem chapterVISection103_no_projective_infinitesimal_rotation
    (rotation : Fin 3 → ℂ) (scale : ℂ) (remainingCurveCoefficients : Fin 3 → ℂ)
    (hfirst :
      (∑ axis, directionalCoefficient ![0, 2, 4] axis * rotation axis) =
        scale * curveCoefficient ![0, 2, 4])
    (hremaining :
      derivedRotationMinor.mulVec rotation =
        fun row ↦ scale * remainingCurveCoefficients row) :
    rotation = 0 ∧ scale = 0 := by
  have hscale : scale = 0 := by
    rw [chapterVISection103_curveCoefficient_y_sq_z_four] at hfirst
    simp only [chapterVISection103_directionalCoefficient_y_sq_z_four, zero_mul,
      Finset.sum_const_zero] at hfirst
    exact (mul_eq_zero.mp hfirst.symm).resolve_right (by norm_num)
  subst scale
  simp only [zero_mul] at hremaining
  exact ⟨Matrix.eq_zero_of_mulVec_eq_zero
    chapterVISection103_derivedRotationMinor_det_ne_zero hremaining, rfl⟩

end PoincareChapterVI
