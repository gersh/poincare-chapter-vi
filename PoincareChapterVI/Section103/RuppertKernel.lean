/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.Section103.RuppertCertificate

/-!
# The polynomial meaning of the Chapter VI Ruppert certificate

This module connects the exact bivariate polynomial from Poincaré's §103 geometry to the
`64 × 35` matrix certified in `RuppertCertificate`. The first twenty coordinates encode a
polynomial `g` of bidegree at most `(3,4)` and the last fifteen encode a polynomial `h` of
bidegree at most `(4,2)`. Lean expands the cleared Ruppert differential expression and proves
that its 35 selected coefficients are precisely multiplication by the certified square minor.

Consequently the differential expression has trivial kernel on this explicit bounded-degree
encoding. The separate remaining step for the full irreducibility theorem is to prove that every
polynomial satisfying the stated bidegree bounds is represented by this encoding, and then to
verify the sharp bounds for a normalized solution arising from a hypothetical factorization.
-/

noncomputable section

open scoped BigOperators

namespace PoincareChapterVI

private abbrev ChapterVIBivar := MvPolynomial (Fin 2) ℂ

private def chapterVIXVar : Fin 2 := 0
private def chapterVIYVar : Fin 2 := 1

private def chapterVIRuppertGColumn (s : Fin 4) (t : Fin 5) : Fin 35 :=
  ⟨s.val * 5 + t.val, by omega⟩

private def chapterVIRuppertHColumn (s : Fin 5) (t : Fin 3) : Fin 35 :=
  ⟨20 + s.val * 3 + t.val, by omega⟩

def chapterVIBivariateMonomial (a b : Nat) : Fin 2 →₀ Nat :=
  Finsupp.single chapterVIXVar a + Finsupp.single chapterVIYVar b

private def chapterVIBivariateTerm (a b : Nat) (c : ℂ) : ChapterVIBivar :=
  MvPolynomial.monomial (chapterVIBivariateMonomial a b) c

private theorem chapterVI_pderiv_bivariateTerm_y (a b : Nat) (c : ℂ) :
    MvPolynomial.pderiv chapterVIYVar (chapterVIBivariateTerm a b c) =
      chapterVIBivariateTerm a (b - 1) (b * c) := by
  cases b with
  | zero => simp [chapterVIBivariateTerm, chapterVIBivariateMonomial, chapterVIYVar, chapterVIXVar]
  | succ b =>
      rw [chapterVIBivariateTerm, MvPolynomial.pderiv_monomial]
      have hexponent :
          chapterVIBivariateMonomial a (b + 1) - Finsupp.single chapterVIYVar 1 = chapterVIBivariateMonomial a b := by
        ext i
        fin_cases i <;> simp [chapterVIBivariateMonomial, chapterVIXVar, chapterVIYVar]
      rw [hexponent]
      simp [chapterVIBivariateTerm, chapterVIBivariateMonomial, chapterVIXVar, chapterVIYVar, mul_comm]

private theorem chapterVI_pderiv_bivariateTerm_x (a b : Nat) (c : ℂ) :
    MvPolynomial.pderiv chapterVIXVar (chapterVIBivariateTerm a b c) =
      chapterVIBivariateTerm (a - 1) b (a * c) := by
  cases a with
  | zero => simp [chapterVIBivariateTerm, chapterVIBivariateMonomial, chapterVIYVar, chapterVIXVar]
  | succ a =>
      rw [chapterVIBivariateTerm, MvPolynomial.pderiv_monomial]
      have hexponent :
          chapterVIBivariateMonomial (a + 1) b - Finsupp.single chapterVIXVar 1 = chapterVIBivariateMonomial a b := by
        ext i
        fin_cases i <;> simp [chapterVIBivariateMonomial, chapterVIXVar, chapterVIYVar]
      rw [hexponent]
      simp [chapterVIBivariateTerm, chapterVIBivariateMonomial, chapterVIXVar, chapterVIYVar, mul_comm]

private theorem chapterVI_bivariateTerm_mul (a b s t : Nat) (c d : ℂ) :
    chapterVIBivariateTerm a b c * chapterVIBivariateTerm s t d = chapterVIBivariateTerm (a + s) (b + t) (c * d) := by
  rw [chapterVIBivariateTerm, chapterVIBivariateTerm, MvPolynomial.monomial_mul]
  have hexponent : chapterVIBivariateMonomial a b + chapterVIBivariateMonomial s t = chapterVIBivariateMonomial (a + s) (b + t) := by
    ext i
    fin_cases i <;> simp [chapterVIBivariateMonomial, chapterVIXVar, chapterVIYVar]
  rw [hexponent, chapterVIBivariateTerm]

def chapterVISection103AffinePolynomial : ChapterVIBivar :=
  ∑ a : Fin 5, ∑ b : Fin 5,
    chapterVIBivariateTerm a.val b.val (chapterVISection103AffineGaussianCoefficient a b : ℂ)

def chapterVIRuppertGPolynomial (v : Fin 35 → ℂ) : ChapterVIBivar :=
  ∑ s : Fin 4, ∑ t : Fin 5, chapterVIBivariateTerm s.val t.val (v (chapterVIRuppertGColumn s t))

def chapterVIRuppertHPolynomial (v : Fin 35 → ℂ) : ChapterVIBivar :=
  ∑ s : Fin 5, ∑ t : Fin 3, chapterVIBivariateTerm s.val t.val (v (chapterVIRuppertHColumn s t))

private def chapterVIRuppertGy (v : Fin 35 → ℂ) : ChapterVIBivar :=
  ∑ s : Fin 4, ∑ t : Fin 5,
    chapterVIBivariateTerm s.val (t.val - 1) (t.val * v (chapterVIRuppertGColumn s t))

private def chapterVIRuppertGx (v : Fin 35 → ℂ) : ChapterVIBivar :=
  ∑ s : Fin 4, ∑ t : Fin 5,
    chapterVIBivariateTerm (s.val - 1) t.val (s.val * v (chapterVIRuppertGColumn s t))

private def chapterVIRuppertHy (v : Fin 35 → ℂ) : ChapterVIBivar :=
  ∑ s : Fin 5, ∑ t : Fin 3,
    chapterVIBivariateTerm s.val (t.val - 1) (t.val * v (chapterVIRuppertHColumn s t))

private def chapterVIRuppertHx (v : Fin 35 → ℂ) : ChapterVIBivar :=
  ∑ s : Fin 5, ∑ t : Fin 3,
    chapterVIBivariateTerm (s.val - 1) t.val (s.val * v (chapterVIRuppertHColumn s t))

private def chapterVIRuppertFy : ChapterVIBivar :=
  ∑ a : Fin 5, ∑ b : Fin 5,
    chapterVIBivariateTerm a.val (b.val - 1)
      (b.val * (chapterVISection103AffineGaussianCoefficient a b : ℂ))

private def chapterVIRuppertFx : ChapterVIBivar :=
  ∑ a : Fin 5, ∑ b : Fin 5,
    chapterVIBivariateTerm (a.val - 1) b.val
      (a.val * (chapterVISection103AffineGaussianCoefficient a b : ℂ))

private theorem chapterVI_pderiv_ruppertG_y (v : Fin 35 → ℂ) :
    MvPolynomial.pderiv chapterVIYVar (chapterVIRuppertGPolynomial v) = chapterVIRuppertGy v := by
  simp [chapterVIRuppertGPolynomial, chapterVIRuppertGy, map_sum, chapterVI_pderiv_bivariateTerm_y]

private theorem chapterVI_pderiv_ruppertH_x (v : Fin 35 → ℂ) :
    MvPolynomial.pderiv chapterVIXVar (chapterVIRuppertHPolynomial v) = chapterVIRuppertHx v := by
  simp [chapterVIRuppertHPolynomial, chapterVIRuppertHx, map_sum, chapterVI_pderiv_bivariateTerm_x]

private theorem chapterVI_pderiv_section103Polynomial_y : MvPolynomial.pderiv chapterVIYVar chapterVISection103AffinePolynomial = chapterVIRuppertFy := by
  simp [chapterVISection103AffinePolynomial, chapterVIRuppertFy, map_sum, chapterVI_pderiv_bivariateTerm_y]

private theorem chapterVI_pderiv_section103Polynomial_x : MvPolynomial.pderiv chapterVIXVar chapterVISection103AffinePolynomial = chapterVIRuppertFx := by
  simp [chapterVISection103AffinePolynomial, chapterVIRuppertFx, map_sum, chapterVI_pderiv_bivariateTerm_x]

def chapterVIRuppertExpanded (v : Fin 35 → ℂ) : ChapterVIBivar :=
  (∑ a : Fin 5, ∑ b : Fin 5, ∑ s : Fin 4, ∑ t : Fin 5,
    chapterVIBivariateTerm (a.val + s.val) (b.val + (t.val - 1))
      ((chapterVISection103AffineGaussianCoefficient a b : ℂ) * t.val * v (chapterVIRuppertGColumn s t))) +
  (∑ s : Fin 5, ∑ t : Fin 3, ∑ a : Fin 5, ∑ b : Fin 5,
    chapterVIBivariateTerm (s.val + (a.val - 1)) (t.val + b.val)
      (v (chapterVIRuppertHColumn s t) * a.val *
        (chapterVISection103AffineGaussianCoefficient a b : ℂ))) -
  (∑ s : Fin 4, ∑ t : Fin 5, ∑ a : Fin 5, ∑ b : Fin 5,
    chapterVIBivariateTerm (s.val + a.val) (t.val + (b.val - 1))
      (v (chapterVIRuppertGColumn s t) * b.val *
        (chapterVISection103AffineGaussianCoefficient a b : ℂ))) -
  (∑ a : Fin 5, ∑ b : Fin 5, ∑ s : Fin 5, ∑ t : Fin 3,
    chapterVIBivariateTerm (a.val + (s.val - 1)) (b.val + t.val)
      ((chapterVISection103AffineGaussianCoefficient a b : ℂ) * s.val * v (chapterVIRuppertHColumn s t)))

set_option maxHeartbeats 2000000 in
private theorem chapterVI_section103Polynomial_mul_ruppertGy (v : Fin 35 → ℂ) :
    chapterVISection103AffinePolynomial * chapterVIRuppertGy v =
      ∑ a : Fin 5, ∑ b : Fin 5, ∑ s : Fin 4, ∑ t : Fin 5,
        chapterVIBivariateTerm (a.val + s.val) (b.val + (t.val - 1))
          ((chapterVISection103AffineGaussianCoefficient a b : ℂ) * t.val *
            v (chapterVIRuppertGColumn s t)) := by
  unfold chapterVISection103AffinePolynomial chapterVIRuppertGy
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  rw [chapterVI_bivariateTerm_mul]
  congr 1
  ring

set_option maxHeartbeats 2000000 in
private theorem chapterVI_ruppertH_mul_section103Fx (v : Fin 35 → ℂ) :
    chapterVIRuppertHPolynomial v * chapterVIRuppertFx =
      ∑ s : Fin 5, ∑ t : Fin 3, ∑ a : Fin 5, ∑ b : Fin 5,
        chapterVIBivariateTerm (s.val + (a.val - 1)) (t.val + b.val)
          (v (chapterVIRuppertHColumn s t) * a.val *
            (chapterVISection103AffineGaussianCoefficient a b : ℂ)) := by
  unfold chapterVIRuppertHPolynomial chapterVIRuppertFx
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro t _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [chapterVI_bivariateTerm_mul]
  congr 1
  ring

set_option maxHeartbeats 2000000 in
private theorem chapterVI_ruppertG_mul_section103Fy (v : Fin 35 → ℂ) :
    chapterVIRuppertGPolynomial v * chapterVIRuppertFy =
      ∑ s : Fin 4, ∑ t : Fin 5, ∑ a : Fin 5, ∑ b : Fin 5,
        chapterVIBivariateTerm (s.val + a.val) (t.val + (b.val - 1))
          (v (chapterVIRuppertGColumn s t) * b.val *
            (chapterVISection103AffineGaussianCoefficient a b : ℂ)) := by
  unfold chapterVIRuppertGPolynomial chapterVIRuppertFy
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro t _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [chapterVI_bivariateTerm_mul]
  congr 1
  ring

set_option maxHeartbeats 2000000 in
private theorem chapterVI_section103Polynomial_mul_ruppertHx (v : Fin 35 → ℂ) :
    chapterVISection103AffinePolynomial * chapterVIRuppertHx v =
      ∑ a : Fin 5, ∑ b : Fin 5, ∑ s : Fin 5, ∑ t : Fin 3,
        chapterVIBivariateTerm (a.val + (s.val - 1)) (b.val + t.val)
          ((chapterVISection103AffineGaussianCoefficient a b : ℂ) * s.val *
            v (chapterVIRuppertHColumn s t)) := by
  unfold chapterVISection103AffinePolynomial chapterVIRuppertHx
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  rw [chapterVI_bivariateTerm_mul]
  congr 1
  ring

set_option maxHeartbeats 2000000 in
theorem chapterVI_ruppertExpression_eq_expanded (v : Fin 35 → ℂ) :
    chapterVIRuppertExpression (MvPolynomial.pderiv chapterVIXVar) (MvPolynomial.pderiv chapterVIYVar)
      chapterVISection103AffinePolynomial (chapterVIRuppertGPolynomial v) (chapterVIRuppertHPolynomial v) = chapterVIRuppertExpanded v := by
  unfold chapterVIRuppertExpression chapterVIRuppertExpanded
  rw [chapterVI_pderiv_ruppertG_y, chapterVI_pderiv_ruppertH_x, chapterVI_pderiv_section103Polynomial_y, chapterVI_pderiv_section103Polynomial_x]
  rw [chapterVI_section103Polynomial_mul_ruppertGy, chapterVI_ruppertH_mul_section103Fx, chapterVI_ruppertG_mul_section103Fy, chapterVI_section103Polynomial_mul_ruppertHx]

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 100000 in
theorem chapterVI_ruppertPivotCoefficient_eq (v : Fin 35 → ℂ) (row : Fin 35) :
    MvPolynomial.coeff
      (chapterVIBivariateMonomial ((chapterVIRuppertPivotRow row).val / 8)
        ((chapterVIRuppertPivotRow row).val % 8))
      (chapterVIRuppertExpression (MvPolynomial.pderiv chapterVIXVar) (MvPolynomial.pderiv chapterVIYVar)
        chapterVISection103AffinePolynomial (chapterVIRuppertGPolynomial v) (chapterVIRuppertHPolynomial v)) =
      (chapterVIComplexRuppertMinor.mulVec v) row := by
  rw [chapterVI_ruppertExpression_eq_expanded]
  fin_cases row <;>
    norm_num [chapterVIRuppertExpanded, chapterVIBivariateTerm, chapterVIBivariateMonomial,
      chapterVIXVar, chapterVIYVar, chapterVIComplexRuppertMatrix, chapterVIRuppertGaussianMatrix,
      chapterVIComplexRuppertMinor, chapterVIRuppertGaussianMinor,
      chapterVIRuppertPivotRow, chapterVIRuppertMatrixOf, Matrix.mulVec, dotProduct,
      chapterVIRuppertGColumn, chapterVIRuppertHColumn,
      MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, Finsupp.ext_iff,
      Fin.sum_univ_succ, chapterVISection103AffineGaussianCoefficient,
      GaussianInt.toComplex_def, Fin.succ] <;> ring

theorem chapterVI_encodedRuppertKernel_trivial (v : Fin 35 → ℂ)
    (h : chapterVIRuppertExpression (MvPolynomial.pderiv chapterVIXVar) (MvPolynomial.pderiv chapterVIYVar)
      chapterVISection103AffinePolynomial (chapterVIRuppertGPolynomial v) (chapterVIRuppertHPolynomial v) = 0) : v = 0 := by
  apply Matrix.eq_zero_of_mulVec_eq_zero chapterVIComplexRuppertMinor_det_ne_zero
  funext row
  rw [← chapterVI_ruppertPivotCoefficient_eq]
  rw [h]
  exact MvPolynomial.coeff_zero (R := ℂ) _

end PoincareChapterVI
