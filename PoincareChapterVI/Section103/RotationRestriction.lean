/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.Section103.AffineIntersectionCount
import PoincareChapterVI.Section103.RotationRestrictionCertificateChecks

/-!
# Infinitesimal rotations restricted to the twenty-four finite points

This file replaces the limiting step in Poincaré's final §103 paragraph by an exact tangent-space
calculation.  The three infinitesimal rotation sextics are reduced in the radical coordinate
algebra of the twenty-four finite intersections.  Three coefficients of their univariate
remainders form a nonsingular matrix, so no nonzero relative rotation can vanish at every one of
the twenty-four points.
-/

noncomputable section

namespace PoincareChapterVI.RotationRestriction

open scoped BigOperators
open AffineEliminationData
open AffineEliminationCertificate
open AffineIntersectionCount
open RotationRestrictionData
open RotationRestrictionCertificate

private abbrev Bivar := MvPolynomial (Fin 2) ℂ

theorem toMv_scaleNat (scalar : ℕ) (polynomial : Sparse) :
    toMv (scaleNat scalar polynomial) = (scalar : ℂ) • toMv polynomial := by
  induction polynomial with
  | nil => simp [scaleNat, toMv]
  | cons term rest ih =>
      change termToMv ⟨term.exp, (scalar : QI) * term.coeff⟩ +
          toMv (scaleNat scalar rest) = _
      rw [ih, MvPolynomial.smul_eq_C_mul]
      simp only [termToMv, map_mul, map_natCast, toMv, List.map_cons,
        List.sum_cons]
      rw [MvPolynomial.smul_eq_C_mul, mul_add,
        MvPolynomial.C_mul_monomial, MvPolynomial.C_eq_coe_nat]

theorem reduced_shape_mv :
    toMv reducedShape =
      toMv shapePolynomial + toMv reducedShapeQuotient * toMv residualPolynomial := by
  have h := toMv_eq_of_normalMap_beq reduced_shape_certificate
  simpa [reducedShapeRight, toMv_add, toMv_mul] using h

theorem direction_reduction_mv (axis : Fin 3) :
    (remainderScale axis : ℂ) • toMv (direction axis) =
      toMv (directionShapeQuotient axis) * toMv reducedShape +
        (toMv (directionResidualQuotient axis) * toMv residualPolynomial +
          toMv (directionRemainder axis)) := by
  have h : toMv (directionLeft axis) = toMv (directionRight axis) := by
    fin_cases axis
    · exact toMv_eq_of_normalMap_beq direction_zero_certificate
    · exact toMv_eq_of_normalMap_beq direction_one_certificate
    · exact toMv_eq_of_normalMap_beq direction_two_certificate
  simpa [directionLeft, directionRight, toMv_scaleNat, toMv_add, toMv_mul] using h

def rotationRemainderQICoefficients (axis : Fin 3) : List QI :=
  (directionRemainder axis).reverse.map Term.coeff

def rotationRemainderPolynomial (axis : Fin 3) : Polynomial ℂ :=
  polynomialOfCoefficientList
    ((rotationRemainderQICoefficients axis).map Section103Source.qiToComplex)

theorem rotationRemainderQICoefficients_length (axis : Fin 3) :
    (rotationRemainderQICoefficients axis).length = 24 := by
  fin_cases axis <;> rfl

theorem rotationRemainderPolynomial_natDegree_le (axis : Fin 3) :
    (rotationRemainderPolynomial axis).natDegree ≤ 23 := by
  simpa [rotationRemainderPolynomial, List.length_map,
    rotationRemainderQICoefficients_length] using
    polynomialOfCoefficientList_natDegree_le ℂ
      ((rotationRemainderQICoefficients axis).map Section103Source.qiToComplex)

theorem sparseToPolynomial_directionRemainder (axis : Fin 3) :
    sparseToPolynomial (directionRemainder axis) = rotationRemainderPolynomial axis := by
  fin_cases axis <;>
    simp [rotationRemainderPolynomial, rotationRemainderQICoefficients,
      directionRemainder, RotationRestrictionData.directionRemainder,
      directionRemainder0, directionRemainder1, directionRemainder2,
      sparseToPolynomial, polynomialOfCoefficientList]
  all_goals simp only [← Polynomial.C_mul_X_pow_eq_monomial]
  all_goals ring_nf

theorem toMv_directionRemainder (axis : Fin 3) :
    toMv (directionRemainder axis) = embedY (rotationRemainderPolynomial axis) := by
  have hx : ∀ term ∈ directionRemainder axis, term.exp.x = 0 := by
    intro term hterm
    have hall := List.all_eq_true.mp (remainder_has_no_x_certificate axis)
    have hcheck := hall term hterm
    simpa [remainderHasNoX] using hcheck
  rw [toMv_eq_embedY_sparseToPolynomial _ hx,
    sparseToPolynomial_directionRemainder]

theorem toMv_residualPolynomial :
    toMv residualPolynomial = embedY residualPolynomialComplex := by
  have hx : ∀ term ∈ residualPolynomial, term.exp.x = 0 := by
    intro term hterm
    have hall := List.all_eq_true.mp residual_has_no_x_certificate
    have hcheck := hall term hterm
    simpa [residualHasNoX] using hcheck
  exact toMv_eq_embedY_sparseToPolynomial residualPolynomial hx

theorem eval_reducedShape_at_residualPoint {root : ℂ}
    (hroot : root ∈ residualRoots) :
    MvPolynomial.eval (residualPoint root) (toMv reducedShape) = 0 := by
  rw [reduced_shape_mv]
  simp only [map_add, map_mul]
  rw [toMv_shapePolynomial, toMv_residualPolynomial]
  simp [eval_embedY, residualPoint,
    (mem_residualRoots_iff root).mp hroot]

theorem eval_direction_reduction {root : ℂ} (hroot : root ∈ residualRoots)
    (axis : Fin 3) :
    (remainderScale axis : ℂ) *
        MvPolynomial.eval (residualPoint root) (toMv (direction axis)) =
      (rotationRemainderPolynomial axis).eval root := by
  have h := congrArg (MvPolynomial.eval (residualPoint root))
    (direction_reduction_mv axis)
  rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C,
    map_add, map_mul, map_add, map_mul,
    eval_reducedShape_at_residualPoint hroot, toMv_residualPolynomial,
    toMv_directionRemainder] at h
  simpa [eval_embedY, residualPoint,
    (mem_residualRoots_iff root).mp hroot] using h

private abbrev F53 := ZMod 53

private instance : Fact (Nat.Prime 53) := ⟨by decide⟩

def restrictionMinorComplex : Matrix (Fin 3) (Fin 3) ℂ :=
  RotationRestrictionData.restrictionMinor.map GaussianInt.toComplex

theorem modularMinorZMod_det_ne_zero : modularMinorZMod.det ≠ 0 := by
  intro hzero
  have hdet := congrArg Matrix.det modular_inverse_mul_minor_certificate
  rw [Matrix.det_mul, Matrix.det_one, hzero, mul_zero] at hdet
  exact zero_ne_one hdet

theorem restrictionMinor_det_ne_zero :
    RotationRestrictionData.restrictionMinor.det ≠ 0 := by
  intro hzero
  have hmap := RotationRestrictionCertificate.gaussianMod53.map_det
    RotationRestrictionData.restrictionMinor
  have hspecialization := restriction_minor_mod53_certificate
  change RotationRestrictionCertificate.gaussianMod53.mapMatrix
      RotationRestrictionData.restrictionMinor = modularMinorZMod at hspecialization
  rw [hzero, map_zero, hspecialization] at hmap
  exact modularMinorZMod_det_ne_zero hmap.symm

theorem restrictionMinorComplex_det_ne_zero : restrictionMinorComplex.det ≠ 0 := by
  intro hzero
  have hmap := GaussianInt.toComplex.map_det
    RotationRestrictionData.restrictionMinor
  change GaussianInt.toComplex RotationRestrictionData.restrictionMinor.det =
    restrictionMinorComplex.det at hmap
  rw [hzero] at hmap
  exact restrictionMinor_det_ne_zero (GaussianInt.toComplex_eq_zero.mp hmap)

theorem rotationRemainderPolynomial_coeff (row axis : Fin 3) :
    (rotationRemainderPolynomial axis).coeff row.val =
      GaussianInt.toComplex (RotationRestrictionData.restrictionMinor row axis) := by
  rw [rotationRemainderPolynomial, polynomialOfCoefficientList_coeff]
  have hcertificate := restriction_minor_coefficient_certificate row axis
  change (rotationRemainderQICoefficients axis).getD row.val 0 =
    RotationRestrictionCertificate.gaussianToQI
      (RotationRestrictionData.restrictionMinor row axis) at hcertificate
  rw [← map_zero Section103Source.qiToComplex, List.getD_map, hcertificate]
  simp [RotationRestrictionCertificate.gaussianToQI,
    Section103Source.qiToComplex, GaussianInt.toComplex_def]

theorem polynomial_eq_zero_of_vanishes_on_residualRoots
    (polynomial : Polynomial ℂ) (hdegree : polynomial.natDegree ≤ 23)
    (hvanish : ∀ root ∈ residualRoots, polynomial.eval root = 0) :
    polynomial = 0 := by
  by_contra hnonzero
  have hsubset : residualRoots ⊆ polynomial.roots.toFinset := by
    intro root hroot
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hnonzero]
    exact hvanish root hroot
  have h24 : 24 ≤ polynomial.roots.toFinset.card := by
    rw [← residualRoots_card]
    exact Finset.card_le_card hsubset
  have hfinite : polynomial.roots.toFinset.card ≤ polynomial.roots.card :=
    Multiset.toFinset_card_le _
  have hpolynomial := polynomial.card_roots'
  omega

def normalizedRotation (rotation : Fin 3 → ℂ) (axis : Fin 3) : ℂ :=
  rotation axis / (remainderScale axis : ℂ)

def rotationRemainderCombination (rotation : Fin 3 → ℂ) : Polynomial ℂ :=
  ∑ axis, Polynomial.C (normalizedRotation rotation axis) *
    rotationRemainderPolynomial axis

theorem rotationRemainderCombination_natDegree_le (rotation : Fin 3 → ℂ) :
    (rotationRemainderCombination rotation).natDegree ≤ 23 := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro axis _
  exact (Polynomial.natDegree_C_mul_le _ _).trans
    (rotationRemainderPolynomial_natDegree_le axis)

def clearedRotationPolynomial (rotation : Fin 3 → ℂ) : Bivar :=
  ∑ axis, MvPolynomial.C (rotation axis) * toMv (direction axis)

theorem remainderScale_ne_zero (axis : Fin 3) : (remainderScale axis : ℂ) ≠ 0 := by
  fin_cases axis <;> norm_num [remainderScale]

theorem rotationRemainderCombination_eval {rotation : Fin 3 → ℂ}
    {root : ℂ} (hroot : root ∈ residualRoots) :
    (rotationRemainderCombination rotation).eval root =
      MvPolynomial.eval (residualPoint root) (clearedRotationPolynomial rotation) := by
  simp only [rotationRemainderCombination, Polynomial.eval_finsetSum,
    Polynomial.eval_mul, Polynomial.eval_C, clearedRotationPolynomial,
    map_sum, map_mul, MvPolynomial.eval_C]
  apply Finset.sum_congr rfl
  intro axis _
  rw [← eval_direction_reduction hroot axis]
  simp only [normalizedRotation]
  field_simp [remainderScale_ne_zero axis]

theorem rotation_eq_zero_of_clearedPolynomial_vanishes
    (rotation : Fin 3 → ℂ)
    (hvanish : ∀ point ∈ finiteIntersectionPoints,
      MvPolynomial.eval point (clearedRotationPolynomial rotation) = 0) :
    rotation = 0 := by
  have hcombinationVanishes : ∀ root ∈ residualRoots,
      (rotationRemainderCombination rotation).eval root = 0 := by
    intro root hroot
    rw [rotationRemainderCombination_eval hroot]
    apply hvanish
    rw [finiteIntersectionPoints, Finset.mem_image]
    exact ⟨root, hroot, rfl⟩
  have hcombination : rotationRemainderCombination rotation = 0 :=
    polynomial_eq_zero_of_vanishes_on_residualRoots _
      (rotationRemainderCombination_natDegree_le rotation) hcombinationVanishes
  have hcoeff : ∀ row : Fin 3,
      ∑ axis : Fin 3,
        normalizedRotation rotation axis *
          GaussianInt.toComplex
            (RotationRestrictionData.restrictionMinor row axis) = 0 := by
    intro row
    have h := congrArg (fun polynomial : Polynomial ℂ ↦ polynomial.coeff row.val)
      hcombination
    simpa [rotationRemainderCombination, Polynomial.coeff_C_mul,
      rotationRemainderPolynomial_coeff] using h
  have hmul : restrictionMinorComplex.mulVec (normalizedRotation rotation) = 0 := by
    funext row
    simpa [restrictionMinorComplex, Matrix.mulVec, dotProduct, mul_comm] using hcoeff row
  have hnormalized : normalizedRotation rotation = 0 :=
    Matrix.eq_zero_of_mulVec_eq_zero restrictionMinorComplex_det_ne_zero hmul
  funext axis
  have haxis := congrFun hnormalized axis
  simpa [normalizedRotation, remainderScale_ne_zero axis] using haxis

end PoincareChapterVI.RotationRestriction
