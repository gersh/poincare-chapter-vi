/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.Section103.RotationRestriction

/-!
# Source bridge for the Section 103 infinitesimal rotations

The certificate generator clears and reduces three sextics.  This file identifies those sextics
with the derivatives obtained by infinitesimally rotating Poincaré's second Kepler ellipse in the
three coordinate directions.  Thus the finite restriction calculation is connected to the
geometric family, rather than merely to an independently supplied coefficient table.
-/

noncomputable section

namespace PoincareChapterVI.RotationSource

open scoped BigOperators
open AffineEliminationData
open AffineEliminationCertificate
open AffineIntersectionCount
open RotationRestrictionData
open RotationRestriction
open RotationRestrictionCertificate

private abbrev Vec3 := Fin 3 → ℂ
private abbrev Exp3 := Fin 3 → ℕ
private abbrev Bivar := MvPolynomial (Fin 2) ℂ

/-- Major axis of the second ellipse (the first column of Poincaré's rational rotation). -/
def secondMajorAxis : Vec3 := ![-2 / 3, 2 / 3, 1 / 3]

/-- Minor axis of the second ellipse (the second column of Poincaré's rational rotation). -/
def secondMinorAxis : Vec3 := ![2 / 15, -1 / 3, 14 / 15]

/-- Standard infinitesimal generators of spatial rotations. -/
def rotationGenerator : Fin 3 → Matrix (Fin 3) (Fin 3) ℂ :=
  ![!![0, 0, 0; 0, 0, -1; 0, 1, 0],
    !![0, 0, 1; 0, 0, 0; -1, 0, 0],
    !![0, -1, 0; 1, 0, 0; 0, 0, 0]]

/-- Exponents of the five monomials in each homogenized cubic coordinate difference. -/
def cubicExponent : Fin 5 → Exp3 :=
  ![![2, 1, 0], ![1, 2, 0], ![1, 1, 1], ![1, 0, 2], ![0, 1, 2]]

/-- Derivative of the cubic coefficient vectors under a rotation of the second ellipse. -/
def cubicCoefficientDerivative (axis : Fin 3) : Fin 5 → Vec3 :=
  let majorDerivative := (rotationGenerator axis).mulVec secondMajorAxis
  let minorDerivative := (rotationGenerator axis).mulVec secondMinorAxis
  ![fun _ ↦ 0,
    fun coordinate ↦ -2 *
      (majorDerivative coordinate / 2 -
        Complex.I * (12 / 13 : ℂ) * minorDerivative coordinate / 2),
    fun coordinate ↦ 2 * (5 / 13 : ℂ) * majorDerivative coordinate,
    fun coordinate ↦ -2 *
      (majorDerivative coordinate / 2 +
        Complex.I * (12 / 13 : ℂ) * minorDerivative coordinate / 2),
    fun _ ↦ 0]

def exponentsAddTo (left right : Fin 5) (target : Exp3) : Bool :=
  cubicExponent left 0 + cubicExponent right 0 == target 0 &&
    cubicExponent left 1 + cubicExponent right 1 == target 1 &&
    cubicExponent left 2 + cubicExponent right 2 == target 2

/-- The source-level convolution `2 ∑ᵢ Uᵢ dUᵢ` for one homogeneous coefficient. -/
def directionalCoefficient (target : Exp3) (axis : Fin 3) : ℂ :=
  2 * ∑ coordinate : Fin 3, ∑ left : Fin 5, ∑ right : Fin 5,
    if exponentsAddTo left right target then
      chapterVISection103CubicCoefficient left coordinate *
        cubicCoefficientDerivative axis right coordinate
    else 0

/-- Affinization at `z = 1` of the source-level infinitesimal rotation sextic. -/
def affineDirectionalPolynomial (axis : Fin 3) : Bivar :=
  ∑ a : Fin 5, ∑ b : Fin 5,
    MvPolynomial.monomial (Section103Resultant.bivarMonomial a.val b.val)
      (directionalCoefficient ![a.val, b.val, 6 - a.val - b.val] axis)

theorem qiToComplex_qiI : Section103Source.qiToComplex qiI = Complex.I := by
  apply Complex.ext <;> norm_num [qiI, Section103Source.qiToComplex]

@[simp] theorem qiToComplex_natCast (n : ℕ) :
    Section103Source.qiToComplex (n : Section103Source.QI) = (n : ℂ) :=
  map_natCast Section103Source.qiToComplex n

@[simp] theorem qiToComplex_ofNat (n : ℕ) [n.AtLeastTwo] :
    Section103Source.qiToComplex (ofNat(n) : Section103Source.QI) =
      (ofNat(n) : ℂ) := by
  apply Complex.ext <;>
    simp [Section103Source.qiToComplex, QuadraticAlgebra.re_ofNat,
      QuadraticAlgebra.im_ofNat]

theorem cubicCoefficient_toComplex (slot : Fin 5) (coordinate : Fin 3) :
    Section103Source.qiToComplex (Section103Source.cubicCoefficient slot coordinate) =
      chapterVISection103CubicCoefficient slot coordinate := by
  rw [chapterVISection103_cubicCoefficient_eq_complexTable]
  fin_cases slot <;> fin_cases coordinate <;> apply Complex.ext <;>
    norm_num [Section103Source.cubicCoefficient,
      chapterVISection103CubicComplexCoefficient, Section103Source.qiToComplex,
      Complex.mul_re, Complex.mul_im]

set_option maxHeartbeats 10000000 in
theorem cubicCoefficientDerivative_toComplex
    (axis : Fin 3) (slot : Fin 5) (coordinate : Fin 3) :
    Section103Source.qiToComplex
        (cubicCoefficientDerivativeQI axis slot coordinate) =
      cubicCoefficientDerivative axis slot coordinate := by
  fin_cases axis <;> fin_cases slot <;> fin_cases coordinate <;>
    norm_num [cubicCoefficientDerivativeQI, cubicCoefficientDerivative,
      rotationGeneratorQI, rotationGenerator, secondMajorAxisQI, secondMajorAxis,
      secondMinorAxisQI, secondMinorAxis, qiToComplex_qiI,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Matrix.cons_val_two,
      map_div₀, qiToComplex_natCast]

theorem directionalCoefficient_toComplex (target : Exp3) (axis : Fin 3) :
    Section103Source.qiToComplex (directionalCoefficientQI target axis) =
      directionalCoefficient target axis := by
  have hexponents (left right : Fin 5) :
      exponentsAddToQI left right target = exponentsAddTo left right target := rfl
  have hterm (coordinate : Fin 3) (left right : Fin 5) :
      Section103Source.qiToComplex
          (if exponentsAddToQI left right target then
            Section103Source.cubicCoefficient left coordinate *
              cubicCoefficientDerivativeQI axis right coordinate
          else 0) =
        if exponentsAddTo left right target then
          chapterVISection103CubicCoefficient left coordinate *
            cubicCoefficientDerivative axis right coordinate
        else 0 := by
    rw [hexponents]
    split <;> simp [*, cubicCoefficient_toComplex,
      cubicCoefficientDerivative_toComplex]
  simp only [directionalCoefficientQI, directionalCoefficient, map_mul,
    map_sum, qiToComplex_ofNat]
  simp_rw [hterm]

theorem toMv_sourceDirectionSparse (axis : Fin 3) :
    toMv (sourceDirectionSparse axis) = affineDirectionalPolynomial axis := by
  simp [sourceDirectionSparse, affineDirectionalPolynomial, toMv, termToMv,
    directionalCoefficient_toComplex, expFinsupp,
    Section103Resultant.bivarMonomial, Fin.sum_univ_succ,
    MvPolynomial.monomial_eq]
  ring

/-- The generated integral sextics are exactly `975` times the source derivatives.  The large
finite coefficient comparison is the LeanCompCert certificate `source_direction_certificate`;
the preceding lemmas prove that its `ℚ[i]` source model denotes the physical complex formula. -/
theorem cleared_direction_eq_source (axis : Fin 3) :
    toMv (direction axis) = (directionScale : ℂ) • affineDirectionalPolynomial axis := by
  calc
    toMv (direction axis) = toMv (scaledSourceDirection axis) :=
      toMv_eq_of_normalMap_beq (source_direction_certificate axis)
    _ = (directionScale : ℂ) • toMv (sourceDirectionSparse axis) := by
      rw [scaledSourceDirection, toMv_scaleNat]
    _ = (directionScale : ℂ) • affineDirectionalPolynomial axis := by
      rw [toMv_sourceDirectionSparse]

/-- A nonzero infinitesimal rotation cannot vanish at all twenty-four certified finite
intersections of Poincaré's two Section 103 curves. -/
theorem rotation_eq_zero_of_source_vanishes
    (rotation : Fin 3 → ℂ)
    (hvanish : ∀ point ∈ finiteIntersectionPoints,
      MvPolynomial.eval point
        (∑ axis, rotation axis • affineDirectionalPolynomial axis) = 0) :
    rotation = 0 := by
  apply rotation_eq_zero_of_clearedPolynomial_vanishes rotation
  intro point hpoint
  have h := hvanish point hpoint
  have hpolynomial : clearedRotationPolynomial rotation =
      (directionScale : ℂ) •
        ∑ axis, rotation axis • affineDirectionalPolynomial axis := by
    simp only [clearedRotationPolynomial]
    simp_rw [← MvPolynomial.smul_eq_C_mul, cleared_direction_eq_source]
    simp [smul_smul, mul_comm, Finset.smul_sum]
  rw [hpolynomial, MvPolynomial.smul_eq_C_mul, map_mul,
    MvPolynomial.eval_C]
  simp [h]

end PoincareChapterVI.RotationSource
