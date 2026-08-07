/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.Section103.RuppertBounds
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.Algebra.CharZero.AddMonoidHom

/-!
# Sharp normalization of factor-derived Ruppert solutions

The raw pair associated to a factorization has `y`-degree at most three in its second
component, while Ruppert's criterion requires degree at most two. This file regards a bivariate
polynomial as a univariate polynomial in `y` over `ℂ[x]`, proves compatibility with `∂y`, and
checks that subtracting `deg_y(a) / 4` times the gradient cancels the coefficient of `y³`.
-/

noncomputable section

namespace PoincareChapterVI

private abbrev Bivar := MvPolynomial (Fin 2) ℂ
private abbrev YCoeff := MvPolynomial {j : Fin 2 // j ≠ 1} ℂ

private instance : CharZero YCoeff :=
  CharZero.of_addMonoidHom (MvPolynomial.C : ℂ →+* YCoeff).toAddMonoidHom
    MvPolynomial.C_1 (MvPolynomial.C_injective _ _)

private theorem chapterVI_quarter_mul_four :
    (MvPolynomial.C (1 / 4 : ℂ) : YCoeff) * 4 = 1 := by
  change MvPolynomial.C (1 / 4 : ℂ) * MvPolynomial.C (4 : ℂ) = MvPolynomial.C 1
  rw [← MvPolynomial.C_mul]
  norm_num

def chapterVIAsPolynomialY : Bivar ≃ₐ[ℂ] Polynomial YCoeff :=
  (MvPolynomial.renameEquiv ℂ (Equiv.optionSubtypeNe (1 : Fin 2)).symm).trans
    (MvPolynomial.optionEquivLeft ℂ {j : Fin 2 // j ≠ 1})

@[simp] theorem chapterVI_asPolynomialY_X_zero :
    chapterVIAsPolynomialY (MvPolynomial.X 0) =
      Polynomial.C (MvPolynomial.X ⟨0, by decide⟩) := by
  simp [chapterVIAsPolynomialY, Equiv.optionSubtypeNe_symm_apply]

@[simp] theorem chapterVI_asPolynomialY_X_one :
    chapterVIAsPolynomialY (MvPolynomial.X 1) = Polynomial.X := by
  simp [chapterVIAsPolynomialY, Equiv.optionSubtypeNe_symm_apply]

theorem chapterVI_asPolynomialY_pderiv (p : Bivar) :
    chapterVIAsPolynomialY (MvPolynomial.pderiv 1 p) =
      (chapterVIAsPolynomialY p).derivative := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [chapterVIAsPolynomialY]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
      rw [MvPolynomial.pderiv_mul]
      fin_cases i <;> simp [hp]

theorem chapterVI_natDegree_asPolynomialY (p : Bivar) :
    (chapterVIAsPolynomialY p).natDegree = p.degreeOf (1 : Fin 2) := by
  simpa [chapterVIAsPolynomialY] using
    (MvPolynomial.degreeOf_eq_natDegree (R := ℂ) (1 : Fin 2) p).symm

private theorem chapterVI_normalizedFactor_coefficient_three
    (A B : Polynomial YCoeff) (hA : A ≠ 0) (hB : B ≠ 0)
    (hdegree : A.natDegree + B.natDegree = 4) :
    (B * A.derivative -
      ((A.natDegree : ℂ) / 4) • (A * B).derivative).coeff 3 = 0 := by
  by_cases hdegreeA : A.natDegree = 0
  · have hderivative : A.derivative = 0 := Polynomial.derivative_eq_zero.mpr hdegreeA
    simp [hdegreeA, hderivative]
  · have hderivativeDegree : A.derivative.natDegree = A.natDegree - 1 :=
      Polynomial.natDegree_derivative A
    have hsum : B.natDegree + A.derivative.natDegree = 3 := by omega
    have hleft : (B * A.derivative).coeff 3 =
        B.leadingCoeff * (A.leadingCoeff * (A.natDegree : YCoeff)) := by
      rw [← hsum, Polynomial.coeff_mul_degree_add_degree,
        Polynomial.leadingCoeff_derivative]
    have hproductDegree : (A * B).natDegree = 4 := by
      rw [Polynomial.natDegree_mul hA hB, hdegree]
    have hright : (A * B).derivative.coeff 3 =
        (A.leadingCoeff * B.leadingCoeff) * (4 : YCoeff) := by
      rw [Polynomial.coeff_derivative]
      norm_num
      rw [← hproductDegree, Polynomial.coeff_natDegree,
        Polynomial.leadingCoeff_mul]
    rw [Polynomial.coeff_sub, hleft, Polynomial.coeff_smul, hright]
    simp only [Algebra.smul_def]
    norm_num [div_eq_mul_inv]
    calc
      B.leadingCoeff * (A.leadingCoeff * (A.natDegree : YCoeff)) -
          (A.natDegree : YCoeff) * MvPolynomial.C (1 / 4) *
            (A.leadingCoeff * B.leadingCoeff * 4) =
        B.leadingCoeff * A.leadingCoeff * (A.natDegree : YCoeff) -
          B.leadingCoeff * A.leadingCoeff * (A.natDegree : YCoeff) *
            (MvPolynomial.C (1 / 4) * 4) := by ring
      _ = 0 := by rw [chapterVI_quarter_mul_four]; ring

private theorem chapterVI_normalizedFactor_natDegree_le_two
    (A B : Polynomial YCoeff) (hA : A ≠ 0) (hB : B ≠ 0)
    (hdegree : A.natDegree + B.natDegree = 4)
    (hbound : (B * A.derivative -
      ((A.natDegree : ℂ) / 4) • (A * B).derivative).natDegree ≤ 3) :
    (B * A.derivative -
      ((A.natDegree : ℂ) / 4) • (A * B).derivative).natDegree ≤ 2 := by
  exact Polynomial.natDegree_le_pred hbound
    (chapterVI_normalizedFactor_coefficient_three A B hA hB hdegree)

theorem chapterVI_normalizedFactor_y_bidegree
    (a b : Bivar) (ha : a ≠ 0) (hb : b ≠ 0)
    (hfactor : chapterVISection103AffinePolynomial = a * b) :
    chapterVIHasBidegreeAtMost 4 2
      (b * MvPolynomial.pderiv 1 a -
        ((a.degreeOf 1 : ℂ) / 4) •
          MvPolynomial.pderiv 1 chapterVISection103AffinePolynomial) := by
  let scalar : ℂ := (a.degreeOf 1 : ℂ) / 4
  let normalized := b * MvPolynomial.pderiv 1 a -
    scalar • MvPolynomial.pderiv 1 chapterVISection103AffinePolynomial
  have hpreliminary :=
    (chapterVI_normalizedFactor_preliminary_bidegrees a b ha hb hfactor scalar).2
  have hx : normalized.degreeOf (0 : Fin 2) ≤ 4 :=
    (chapterVI_hasBidegreeAtMost_iff_degreeOf 4 3 normalized).mp hpreliminary |>.1
  let A := chapterVIAsPolynomialY a
  let B := chapterVIAsPolynomialY b
  have hA : A ≠ 0 := fun hzero ↦ ha (chapterVIAsPolynomialY.injective (by simpa [A] using hzero))
  have hB : B ≠ 0 := fun hzero ↦ hb (chapterVIAsPolynomialY.injective (by simpa [B] using hzero))
  have hdegree : A.natDegree + B.natDegree = 4 := by
    dsimp only [A, B]
    rw [chapterVI_natDegree_asPolynomialY, chapterVI_natDegree_asPolynomialY]
    exact (chapterVI_factor_degree_sums a b ha hb hfactor).2
  have hmapped : chapterVIAsPolynomialY normalized =
      B * A.derivative - ((A.natDegree : ℂ) / 4) • (A * B).derivative := by
    dsimp only [normalized, scalar, A, B]
    rw [map_sub, map_mul, chapterVI_asPolynomialY_pderiv,
      map_smul, chapterVI_asPolynomialY_pderiv, hfactor, map_mul,
      chapterVI_natDegree_asPolynomialY]
  have hmappedBound : (chapterVIAsPolynomialY normalized).natDegree ≤ 3 := by
    rw [chapterVI_natDegree_asPolynomialY]
    exact (chapterVI_hasBidegreeAtMost_iff_degreeOf 4 3 normalized).mp hpreliminary |>.2
  have hy : normalized.degreeOf (1 : Fin 2) ≤ 2 := by
    rw [← chapterVI_natDegree_asPolynomialY]
    rw [hmapped] at hmappedBound ⊢
    exact chapterVI_normalizedFactor_natDegree_le_two A B hA hB hdegree hmappedBound
  exact (chapterVI_hasBidegreeAtMost_iff_degreeOf 4 2 normalized).mpr ⟨hx, hy⟩

/-- Both components of the normalized solution attached to a nonzero factorization satisfy
Ruppert's sharp degree boxes. -/
theorem chapterVI_normalizedFactor_bidegrees
    (a b : Bivar) (ha : a ≠ 0) (hb : b ≠ 0)
    (hfactor : chapterVISection103AffinePolynomial = a * b) :
    chapterVIHasBidegreeAtMost 3 4
        (b * MvPolynomial.pderiv 0 a -
          ((a.degreeOf 1 : ℂ) / 4) •
            MvPolynomial.pderiv 0 chapterVISection103AffinePolynomial) ∧
      chapterVIHasBidegreeAtMost 4 2
        (b * MvPolynomial.pderiv 1 a -
          ((a.degreeOf 1 : ℂ) / 4) •
            MvPolynomial.pderiv 1 chapterVISection103AffinePolynomial) := by
  constructor
  · exact (chapterVI_normalizedFactor_preliminary_bidegrees a b ha hb hfactor _).1
  · exact chapterVI_normalizedFactor_y_bidegree a b ha hb hfactor

/-- The full-rank certificate forces both components of every normalized factor-derived
solution to vanish. The next irreducibility step is to show that a proper factor cannot have
this property. -/
theorem chapterVI_normalizedFactor_components_eq_zero
    (a b : Bivar) (ha : a ≠ 0) (hb : b ≠ 0)
    (hfactor : chapterVISection103AffinePolynomial = a * b) :
    b * MvPolynomial.pderiv 0 a -
          ((a.degreeOf 1 : ℂ) / 4) •
            MvPolynomial.pderiv 0 chapterVISection103AffinePolynomial = 0 ∧
      b * MvPolynomial.pderiv 1 a -
          ((a.degreeOf 1 : ℂ) / 4) •
            MvPolynomial.pderiv 1 chapterVISection103AffinePolynomial = 0 := by
  apply chapterVI_boundedRuppertKernel_trivial
  · exact (chapterVI_normalizedFactor_bidegrees a b ha hb hfactor).1
  · exact (chapterVI_normalizedFactor_bidegrees a b ha hb hfactor).2
  · rw [hfactor]
    exact chapterVI_ruppertExpression_normalizedFactor
      (MvPolynomial.pderiv (0 : Fin 2)) (MvPolynomial.pderiv (1 : Fin 2))
      (fun p ↦ chapterVI_pderiv_commute 0 1 p) a b ((a.degreeOf 1 : ℂ) / 4)

end PoincareChapterVI
