/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import Mathlib.Analysis.Calculus.Deriv.Prod
import PoincareChapterVI.Section103.RotationSource

/-!
# A genuine rotation family for Poincaré's Section 103 sextic

`RotationSource` identifies the three certified sextics with a finite convolution described as
an infinitesimal rotation.  Here that infinitesimal description is integrated to an actual local
family using the rational Cayley parametrization of each coordinate rotation.  We prove that the
major and minor axes, and then every cubic coefficient, have the claimed derivative at the base
configuration.
-/

noncomputable section

namespace PoincareChapterVI.RotationFamily

open scoped BigOperators
open RotationSource

private abbrev Vec3 := Fin 3 → ℂ
private abbrev Mat3 := Matrix (Fin 3) (Fin 3) ℂ

-- Keep the overlapping complex calculus instances coherent on Lean 4.33-rc2.
@[reducible] local instance (priority := 20000) complexNormedAddCommGroupForCalculus :
    NormedAddCommGroup ℂ :=
  { Complex.instNormedAddCommGroup with
    toAddCommGroup :=
      DenselyNormedField.toNontriviallyNormedField.toDivisionRing.toAddCommGroup }

@[reducible] local instance (priority := 20000) complexAddCommGroupForCalculus :
    AddCommGroup ℂ :=
  complexNormedAddCommGroupForCalculus.toAddCommGroup

attribute [local instance 20000] NormedAlgebra.toNormedSpace NormedSpace.toModule

private theorem complexAddCommGroupForCalculus_eq_field :
    complexAddCommGroupForCalculus =
      DenselyNormedField.toNontriviallyNormedField.toDivisionRing.toAddCommGroup := by
  rfl

/-- The skew generator for an arbitrary complexified infinitesimal relative rotation. -/
def infinitesimalRotation (rotation : Fin 3 → ℂ) : Mat3 :=
  ∑ axis, rotation axis • rotationGenerator axis

/-- Cosine coordinate in the rational Cayley parametrization, regular at the origin. -/
def cayleyCos (angle : ℂ) : ℂ :=
  (1 - angle ^ 2 / 4) / (1 + angle ^ 2 / 4)

/-- Sine coordinate in the rational Cayley parametrization, regular at the origin. -/
def cayleySin (angle : ℂ) : ℂ :=
  angle / (1 + angle ^ 2 / 4)

/-- The three standard one-parameter complex orthogonal rotations in Cayley coordinates. -/
def axisRotation : Fin 3 → ℂ → Mat3 :=
  ![fun angle ↦
      !![1, 0, 0;
         0, cayleyCos angle, -cayleySin angle;
         0, cayleySin angle, cayleyCos angle],
    fun angle ↦
      !![cayleyCos angle, 0, cayleySin angle;
         0, 1, 0;
         -cayleySin angle, 0, cayleyCos angle],
    fun angle ↦
      !![cayleyCos angle, -cayleySin angle, 0;
         cayleySin angle, cayleyCos angle, 0;
         0, 0, 1]]

/-- A genuine one-parameter complex orthogonal motion with arbitrary tangent vector. -/
def rotationMatrix (rotation : Fin 3 → ℂ) (γ : ℂ) : Mat3 :=
  axisRotation 0 (γ * rotation 0) *
    axisRotation 1 (γ * rotation 1) *
      axisRotation 2 (γ * rotation 2)

@[simp] theorem axisRotation_zero (axis : Fin 3) : axisRotation axis 0 = 1 := by
  fin_cases axis <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [axisRotation, cayleyCos, cayleySin]

/-- The moving major axis of the second ellipse. -/
def movingMajorAxis (rotation : Fin 3 → ℂ) (γ : ℂ) : Vec3 :=
  (rotationMatrix rotation γ).mulVec secondMajorAxis

/-- The moving minor axis of the second ellipse. -/
def movingMinorAxis (rotation : Fin 3 → ℂ) (γ : ℂ) : Vec3 :=
  (rotationMatrix rotation γ).mulVec secondMinorAxis

@[simp] theorem rotationMatrix_zero (rotation : Fin 3 → ℂ) :
    rotationMatrix rotation 0 = 1 := by
  simp [rotationMatrix]

@[simp] theorem movingMajorAxis_zero (rotation : Fin 3 → ℂ) :
    movingMajorAxis rotation 0 = secondMajorAxis := by
  simp [movingMajorAxis]

@[simp] theorem movingMinorAxis_zero (rotation : Fin 3 → ℂ) :
    movingMinorAxis rotation 0 = secondMinorAxis := by
  simp [movingMinorAxis]

theorem cayleyCos_sq_add_cayleySin_sq
    (angle : ℂ) (hregular : 1 + angle ^ 2 / 4 ≠ 0) :
    cayleyCos angle ^ 2 + cayleySin angle ^ 2 = 1 := by
  have hregular' : 4 + angle ^ 2 ≠ 0 := by
    intro h
    apply hregular
    rw [show 1 + angle ^ 2 / 4 = (4 + angle ^ 2) / 4 by ring, h]
    norm_num
  unfold cayleyCos cayleySin
  field_simp [hregular, hregular']
  ring

theorem axisRotation_transpose_mul_self (axis : Fin 3) (angle : ℂ)
    (hregular : 1 + angle ^ 2 / 4 ≠ 0) :
    Matrix.transpose (axisRotation axis angle) * axisRotation axis angle = 1 := by
  fin_cases axis <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [axisRotation, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ]
  all_goals first
    | simpa [pow_two, add_comm] using cayleyCos_sq_add_cayleySin_sq angle hregular
    | ring

/-- The Cayley family is genuinely orthogonal wherever its three rational denominators are
nonzero, not merely a formal first-order perturbation. -/
theorem rotationMatrix_transpose_mul_self (rotation : Fin 3 → ℂ) (γ : ℂ)
    (hregular : ∀ axis, 1 + (γ * rotation axis) ^ 2 / 4 ≠ 0) :
    Matrix.transpose (rotationMatrix rotation γ) * rotationMatrix rotation γ = 1 := by
  let A := axisRotation 0 (γ * rotation 0)
  let B := axisRotation 1 (γ * rotation 1)
  let C := axisRotation 2 (γ * rotation 2)
  change Matrix.transpose (A * B * C) * (A * B * C) = 1
  rw [Matrix.transpose_mul, Matrix.transpose_mul]
  calc
    Matrix.transpose C * (Matrix.transpose B * Matrix.transpose A) * (A * B * C) =
        Matrix.transpose C * Matrix.transpose B *
          (Matrix.transpose A * A) * B * C := by noncomm_ring
    _ = Matrix.transpose C * Matrix.transpose B * 1 * B * C := by
      rw [show Matrix.transpose A * A = 1 by
        exact axisRotation_transpose_mul_self 0 (γ * rotation 0) (hregular 0)]
    _ = Matrix.transpose C * (Matrix.transpose B * B) * C := by
      simp only [Matrix.mul_one]
      noncomm_ring
    _ = Matrix.transpose C * 1 * C := by
      rw [show Matrix.transpose B * B = 1 by
        exact axisRotation_transpose_mul_self 1 (γ * rotation 1) (hregular 1)]
    _ = Matrix.transpose C * C := by simp
    _ = 1 := axisRotation_transpose_mul_self 2 (γ * rotation 2) (hregular 2)

private theorem hasDerivAt_axisRotation_entry_zero
    (axis : Fin 3) (speed : ℂ) (i j : Fin 3) :
    HasDerivAt (fun γ ↦ axisRotation axis (γ * speed) i j)
      (speed * rotationGenerator axis i j) 0 := by
  unfold complexAddCommGroupForCalculus complexNormedAddCommGroupForCalculus
  have hlinear : HasDerivAt (fun γ : ℂ ↦ γ * speed) _ 0 :=
    hasDerivAt_mul_const speed
  have hsquare := hlinear.pow 2
  have hdenominator := (hsquare.div_const 4).const_add 1
  have hsin := hlinear.div hdenominator (by norm_num :
    (1 + ((0 : ℂ) * speed) ^ 2 / 4) ≠ 0)
  have hnumerator := (hsquare.div_const 4).const_sub 1
  have hcos := hnumerator.div hdenominator (by norm_num :
    (1 + ((0 : ℂ) * speed) ^ 2 / 4) ≠ 0)
  have hsin' : HasDerivAt (fun γ : ℂ ↦ cayleySin (γ * speed)) speed 0 := by
    convert hsin using 1
    · exact complexAddCommGroupForCalculus_eq_field
    · funext γ
      rfl
    · norm_num
  have hcos' : HasDerivAt (fun γ : ℂ ↦ cayleyCos (γ * speed)) 0 0 := by
    convert hcos using 1
    · exact complexAddCommGroupForCalculus_eq_field
    · funext γ
      rfl
    · norm_num
  have hnegsin' : HasDerivAt (fun γ : ℂ ↦ -cayleySin (γ * speed)) (-speed) 0 :=
    hsin'.neg
  have hzero : HasDerivAt (fun _ : ℂ ↦ (0 : ℂ)) 0 0 :=
    hasDerivAt_const (0 : ℂ) (0 : ℂ)
  have hone : HasDerivAt (fun _ : ℂ ↦ (1 : ℂ)) 0 0 :=
    hasDerivAt_const (0 : ℂ) (1 : ℂ)
  fin_cases axis <;> fin_cases i <;> fin_cases j <;>
    norm_num [axisRotation, rotationGenerator] <;> assumption

theorem hasDerivAt_rotationMatrix_entry_zero
    (rotation : Fin 3 → ℂ) (i j : Fin 3) :
    HasDerivAt (fun γ ↦ rotationMatrix rotation γ i j)
      (infinitesimalRotation rotation i j) 0 := by
  simp only [rotationMatrix, Matrix.mul_apply]
  have hproduct (k l : Fin 3) :
      HasDerivAt (fun γ ↦
        axisRotation 0 (γ * rotation 0) i k *
          axisRotation 1 (γ * rotation 1) k l *
            axisRotation 2 (γ * rotation 2) l j)
        (rotation 0 * rotationGenerator 0 i k * axisRotation 1 0 k l *
            axisRotation 2 0 l j +
          axisRotation 0 0 i k * (rotation 1 * rotationGenerator 1 k l) *
            axisRotation 2 0 l j +
          axisRotation 0 0 i k * axisRotation 1 0 k l *
            (rotation 2 * rotationGenerator 2 l j)) 0 := by
    convert ((hasDerivAt_axisRotation_entry_zero 0 (rotation 0) i k).mul
      (hasDerivAt_axisRotation_entry_zero 1 (rotation 1) k l)).mul
        (hasDerivAt_axisRotation_entry_zero 2 (rotation 2) l j) using 1
    all_goals try rfl
    simp only [zero_mul, axisRotation_zero, Pi.mul_apply]
    noncomm_ring
  convert HasDerivAt.sum (u := Finset.univ) (fun l _ ↦
    HasDerivAt.sum (u := Finset.univ) (fun k _ ↦ hproduct k l)) using 1
  · funext γ
    simp only [Finset.sum_mul, Finset.sum_apply]
  ·
    fin_cases i <;> fin_cases j <;>
      norm_num [axisRotation_zero, infinitesimalRotation, rotationGenerator,
        Matrix.one_apply, Fin.sum_univ_succ, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons, Fin.isValue] <;> simp

theorem hasDerivAt_movingMajorAxis_zero (rotation : Fin 3 → ℂ) :
    HasDerivAt (movingMajorAxis rotation)
      ((infinitesimalRotation rotation).mulVec secondMajorAxis) 0 := by
  rw [hasDerivAt_pi]
  intro i
  simp only [movingMajorAxis, Matrix.mulVec, dotProduct]
  exact HasDerivAt.sum (u := Finset.univ) fun j _ ↦
    (hasDerivAt_rotationMatrix_entry_zero rotation i j).mul_const (secondMajorAxis j)

theorem hasDerivAt_movingMinorAxis_zero (rotation : Fin 3 → ℂ) :
    HasDerivAt (movingMinorAxis rotation)
      ((infinitesimalRotation rotation).mulVec secondMinorAxis) 0 := by
  rw [hasDerivAt_pi]
  intro i
  simp only [movingMinorAxis, Matrix.mulVec, dotProduct]
  exact HasDerivAt.sum (u := Finset.univ) fun j _ ↦
    (hasDerivAt_rotationMatrix_entry_zero rotation i j).mul_const (secondMinorAxis j)

/-- The coefficient vectors of the moving cubic coordinate difference.  Writing the family as
the base coefficient plus the changes in the moving axes keeps the already-audited source table
as the unique base point. -/
def movingCubicCoefficient (rotation : Fin 3 → ℂ) (γ : ℂ) : Fin 5 → Vec3 :=
  let majorChange := movingMajorAxis rotation γ - secondMajorAxis
  let minorChange := movingMinorAxis rotation γ - secondMinorAxis
  ![chapterVISection103CubicCoefficient 0,
    fun coordinate ↦ chapterVISection103CubicCoefficient 1 coordinate - 2 *
      (majorChange coordinate / 2 -
        Complex.I * (12 / 13 : ℂ) * minorChange coordinate / 2),
    fun coordinate ↦ chapterVISection103CubicCoefficient 2 coordinate +
      2 * (5 / 13 : ℂ) * majorChange coordinate,
    fun coordinate ↦ chapterVISection103CubicCoefficient 3 coordinate - 2 *
      (majorChange coordinate / 2 +
        Complex.I * (12 / 13 : ℂ) * minorChange coordinate / 2),
    chapterVISection103CubicCoefficient 4]

/-- The derivative of the cubic coefficient table for an arbitrary rotation vector. -/
def combinedCubicCoefficientDerivative
    (rotation : Fin 3 → ℂ) (slot : Fin 5) (coordinate : Fin 3) : ℂ :=
  ∑ axis, rotation axis * cubicCoefficientDerivative axis slot coordinate

@[simp] theorem movingCubicCoefficient_zero
    (rotation : Fin 3 → ℂ) (slot : Fin 5) (coordinate : Fin 3) :
    movingCubicCoefficient rotation 0 slot coordinate =
      chapterVISection103CubicCoefficient slot coordinate := by
  fin_cases slot <;> simp [movingCubicCoefficient]

private theorem infinitesimalRotation_mulVec
    (rotation : Fin 3 → ℂ) (vector : Vec3) (coordinate : Fin 3) :
    ((infinitesimalRotation rotation).mulVec vector) coordinate =
      ∑ axis, rotation axis * ((rotationGenerator axis).mulVec vector) coordinate := by
  simp [infinitesimalRotation, Matrix.sum_mulVec, Matrix.smul_mulVec]

theorem hasDerivAt_movingCubicCoefficient_zero
    (rotation : Fin 3 → ℂ) (slot : Fin 5) (coordinate : Fin 3) :
    HasDerivAt (fun γ ↦ movingCubicCoefficient rotation γ slot coordinate)
      (combinedCubicCoefficientDerivative rotation slot coordinate) 0 := by
  have hmajor := hasDerivAt_pi.mp (hasDerivAt_movingMajorAxis_zero rotation) coordinate
  have hminor := hasDerivAt_pi.mp (hasDerivAt_movingMinorAxis_zero rotation) coordinate
  fin_cases slot
  · simpa [movingCubicCoefficient, combinedCubicCoefficientDerivative,
      cubicCoefficientDerivative] using
      (hasDerivAt_const (0 : ℂ)
        (chapterVISection103CubicCoefficient 0 coordinate))
  · convert ((((hmajor.sub_const (secondMajorAxis coordinate)).div_const 2).sub
      (((hminor.sub_const (secondMinorAxis coordinate)).const_mul
        (Complex.I * (12 / 13 : ℂ))).div_const 2)).const_mul (-2)).add_const
          (chapterVISection103CubicCoefficient 1 coordinate) using 1
    · funext γ
      norm_num [movingCubicCoefficient]
      ring
    · norm_num [combinedCubicCoefficientDerivative, cubicCoefficientDerivative,
        infinitesimalRotation_mulVec, Fin.sum_univ_succ]
      ring
  · convert (hmajor.sub_const (secondMajorAxis coordinate)).const_mul
      (2 * (5 / 13 : ℂ)) |>.add_const
        (chapterVISection103CubicCoefficient 2 coordinate) using 1
    · funext γ
      norm_num [movingCubicCoefficient]
      ring
    · norm_num [combinedCubicCoefficientDerivative, cubicCoefficientDerivative,
        infinitesimalRotation_mulVec, Fin.sum_univ_succ]
      ring
  · convert ((((hmajor.sub_const (secondMajorAxis coordinate)).div_const 2).add
      (((hminor.sub_const (secondMinorAxis coordinate)).const_mul
        (Complex.I * (12 / 13 : ℂ))).div_const 2)).const_mul (-2)).add_const
          (chapterVISection103CubicCoefficient 3 coordinate) using 1
    · funext γ
      norm_num [movingCubicCoefficient]
      ring
    · norm_num [combinedCubicCoefficientDerivative, cubicCoefficientDerivative,
        infinitesimalRotation_mulVec, Fin.sum_univ_succ]
      ring
  · simpa [movingCubicCoefficient, combinedCubicCoefficientDerivative,
      cubicCoefficientDerivative] using
      (hasDerivAt_const (0 : ℂ)
        (chapterVISection103CubicCoefficient 4 coordinate))

/-- The affine value of one of the five homogeneous cubic monomials, after setting `z = 1`. -/
def affineCubicMonomial (point : Fin 2 → ℂ) (slot : Fin 5) : ℂ :=
  point 0 ^ cubicExponent slot 0 * point 1 ^ cubicExponent slot 1

/-- One coordinate of the moving cubic vector at an affine point. -/
def movingAffineCubic (rotation : Fin 3 → ℂ) (γ : ℂ)
    (point : Fin 2 → ℂ) (coordinate : Fin 3) : ℂ :=
  ∑ slot, movingCubicCoefficient rotation γ slot coordinate *
    affineCubicMonomial point slot

/-- Poincaré's moving squared-distance sextic in the affine chart `z = 1`. -/
def movingAffineDistance (rotation : Fin 3 → ℂ) (γ : ℂ)
    (point : Fin 2 → ℂ) : ℂ :=
  ∑ coordinate, (movingAffineCubic rotation γ point coordinate) ^ 2

def affineCubicValue (point : Fin 2 → ℂ) (coordinate : Fin 3) : ℂ :=
  ∑ slot, chapterVISection103CubicCoefficient slot coordinate *
    affineCubicMonomial point slot

def affineCubicDirectionalValue (rotation : Fin 3 → ℂ)
    (point : Fin 2 → ℂ) (coordinate : Fin 3) : ℂ :=
  ∑ slot, combinedCubicCoefficientDerivative rotation slot coordinate *
    affineCubicMonomial point slot

@[simp] theorem movingAffineCubic_zero (rotation : Fin 3 → ℂ)
    (point : Fin 2 → ℂ) (coordinate : Fin 3) :
    movingAffineCubic rotation 0 point coordinate = affineCubicValue point coordinate := by
  simp [movingAffineCubic, affineCubicValue]

theorem hasDerivAt_movingAffineCubic_zero (rotation : Fin 3 → ℂ)
    (point : Fin 2 → ℂ) (coordinate : Fin 3) :
    HasDerivAt (fun γ ↦ movingAffineCubic rotation γ point coordinate)
      (affineCubicDirectionalValue rotation point coordinate) 0 := by
  exact HasDerivAt.sum (u := Finset.univ) fun slot _ ↦
    (hasDerivAt_movingCubicCoefficient_zero rotation slot coordinate).mul_const
      (affineCubicMonomial point slot)

/-- The derivative of the actual moving squared distance is the source-level convolution
`2 ∑ Uᵢ dUᵢ`. -/
theorem hasDerivAt_movingAffineDistance_zero (rotation : Fin 3 → ℂ)
    (point : Fin 2 → ℂ) :
    HasDerivAt (fun γ ↦ movingAffineDistance rotation γ point)
      (2 * ∑ coordinate, affineCubicValue point coordinate *
        affineCubicDirectionalValue rotation point coordinate) 0 := by
  have hcoordinate (coordinate : Fin 3) :
      HasDerivAt (fun γ ↦ (movingAffineCubic rotation γ point coordinate) ^ 2)
        (2 * affineCubicValue point coordinate *
          affineCubicDirectionalValue rotation point coordinate) 0 := by
    convert (hasDerivAt_movingAffineCubic_zero rotation point coordinate).pow 2 using 1
    all_goals try rfl
    all_goals try simp
  convert HasDerivAt.sum (u := Finset.univ) (fun coordinate _ ↦ hcoordinate coordinate) using 1
  all_goals try rfl
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro coordinate _
  ring

set_option maxHeartbeats 10000000 in
/-- The derivative just computed is exactly evaluation of the affine source polynomial used by
the certified restriction calculation.  This is the direct correspondence between the genuine
moving ellipse and the coefficient-level `affineDirectionalPolynomial`. -/
theorem movingAffineDistance_derivative_eq_eval (rotation : Fin 3 → ℂ)
    (point : Fin 2 → ℂ) :
    2 * ∑ coordinate, affineCubicValue point coordinate *
        affineCubicDirectionalValue rotation point coordinate =
      MvPolynomial.eval point
        (∑ axis, rotation axis • affineDirectionalPolynomial axis) := by
  simp [affineCubicValue, affineCubicDirectionalValue,
    combinedCubicCoefficientDerivative, affineCubicMonomial,
    affineDirectionalPolynomial, directionalCoefficient, exponentsAddTo,
    cubicExponent, Section103Resultant.bivarMonomial,
    MvPolynomial.eval_monomial, Finsupp.prod_fintype, Fin.sum_univ_succ]
  ring

/-- Final physical source bridge: differentiating the actual Cayley rotation family gives the
polynomial evaluated by the Section 103 finite certificate. -/
theorem hasDerivAt_movingAffineDistance_eq_source (rotation : Fin 3 → ℂ)
    (point : Fin 2 → ℂ) :
    HasDerivAt (fun γ ↦ movingAffineDistance rotation γ point)
      (MvPolynomial.eval point
        (∑ axis, rotation axis • affineDirectionalPolynomial axis)) 0 := by
  rw [← movingAffineDistance_derivative_eq_eval]
  exact hasDerivAt_movingAffineDistance_zero rotation point
end PoincareChapterVI.RotationFamily
