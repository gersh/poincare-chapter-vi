/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.PDeriv

/-!
# The polynomial identity in Poincaré's Chapter VI, §103

Poincaré writes a degree-six polynomial as `P = ∑ Uᵢ²` and sets
`Vᵢ = x ∂Uᵢ/∂x - Uᵢ`. Direct differentiation gives

`x ∂P/∂x = 2 ∑ Vᵢ Uᵢ + 2 P`.

The 1892 printing has `+ P` instead of `+ 2 P`. The next step is restricted to `P = 0`, where
the two formulas agree. This file verifies both the corrected polynomial identity and its
on-curve consequence. It does not formalize the subsequent intersection-multiplicity count.
-/

noncomputable section

namespace PoincareChapterVI

open MvPolynomial
open scoped BigOperators

/-- Poincaré's `P = U₁² + U₂² + U₃²` from §103, abstracted from the displayed coefficients. -/
def chapterVICurvePolynomial {σ R : Type*} [CommRing R] (U : Fin 3 → MvPolynomial σ R) :
    MvPolynomial σ R :=
  ∑ i, U i ^ 2

/-- Poincaré's auxiliary polynomial `Vᵢ = x ∂Uᵢ/∂x - Uᵢ`. -/
def chapterVICurveAuxiliary {σ R : Type*} [CommRing R] (x : σ)
    (U : Fin 3 → MvPolynomial σ R) (i : Fin 3) : MvPolynomial σ R :=
  X x * pderiv x (U i) - U i

/-- The five-term cubic form `U = A x²y + B xy² + C xy + D x + E y` displayed in §103. -/
def chapterVICubicForm {σ R : Type*} [CommRing R] (x y : σ) (A B C D E : R) :
    MvPolynomial σ R :=
  MvPolynomial.C A * X x ^ 2 * X y + MvPolynomial.C B * X x * X y ^ 2 +
    MvPolynomial.C C * X x * X y + MvPolynomial.C D * X x + MvPolynomial.C E * X y

/-- The source's displayed simplification
`x ∂U/∂x - U = A x²y - E y` for its five-term cubic form. -/
theorem chapterVI_cubicForm_auxiliary
    {σ R : Type*} [CommRing R] (x y : σ) (A B C D E : R) (hxy : y ≠ x) :
    X x * pderiv x (chapterVICubicForm x y A B C D E) -
        chapterVICubicForm x y A B C D E =
      MvPolynomial.C A * X x ^ 2 * X y - MvPolynomial.C E * X y := by
  simp only [chapterVICubicForm, map_add, pderiv_mul, pderiv_pow, pderiv_C,
    pderiv_X_self, pderiv_X_of_ne hxy, Nat.reduceSubDiff, pow_one]
  ring

/-- The analogous simplification in the second variable,
`y ∂U/∂y - U = B xy² - D x`. -/
theorem chapterVI_cubicForm_auxiliary_second
    {σ R : Type*} [CommRing R] (x y : σ) (A B C D E : R) (hxy : x ≠ y) :
    X y * pderiv y (chapterVICubicForm x y A B C D E) -
        chapterVICubicForm x y A B C D E =
      MvPolynomial.C B * X x * X y ^ 2 - MvPolynomial.C D * X x := by
  simp only [chapterVICubicForm, map_add, pderiv_mul, pderiv_pow, pderiv_C,
    pderiv_X_self, pderiv_X_of_ne hxy, Nat.reduceSubDiff, pow_one]
  ring

/-- The corrected form of the displayed differential identity in §103. The printed `+ P`
must be `+ 2 P` before restricting to the curve `P = 0`. -/
theorem chapterVI_curvePolynomial_derivative
    {σ R : Type*} [CommRing R] (x : σ) (U : Fin 3 → MvPolynomial σ R) :
    X x * pderiv x (chapterVICurvePolynomial U) =
      2 * ∑ i, chapterVICurveAuxiliary x U i * U i +
        2 * chapterVICurvePolynomial U := by
  simp only [chapterVICurvePolynomial, chapterVICurveAuxiliary, map_sum, pderiv_pow,
    Nat.reduceSubDiff, pow_one]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- On the curve `P = 0`, the correction term vanishes, giving the identity used in the next
line of §103. -/
theorem chapterVI_curvePolynomial_derivative_on_curve
    {σ R : Type*} [CommRing R] (x : σ) (U : Fin 3 → MvPolynomial σ R)
    (hP : chapterVICurvePolynomial U = 0) :
    X x * pderiv x (chapterVICurvePolynomial U) =
      2 * ∑ i, chapterVICurveAuxiliary x U i * U i := by
  rw [chapterVI_curvePolynomial_derivative, hP, mul_zero, add_zero]

/-- Exact reduction of the ninth-degree derivative equation modulo `P`, abstracting the
calculation that produces Poincaré's curve `R` in §103. If the two auxiliary polynomials carry
the displayed factors `y` and `x`, respectively, then `Q` differs from `2xyR` by a multiple of
`P`. -/
theorem chapterVI_derivativeCurveEquation_reduction
    {σ R : Type*} [CommRing R] (x y : σ) (U Wₓ Wᵧ : Fin 3 → MvPolynomial σ R)
    (α β : MvPolynomial σ R)
    (hauxX : ∀ i, chapterVICurveAuxiliary x U i = X y * Wₓ i)
    (hauxY : ∀ i, chapterVICurveAuxiliary y U i = X x * Wᵧ i) :
    α * X x ^ 2 * pderiv x (chapterVICurvePolynomial U) -
        β * X y ^ 2 * pderiv y (chapterVICurvePolynomial U) =
      2 * X x * X y *
          (α * ∑ i, Wₓ i * U i - β * ∑ i, Wᵧ i * U i) +
        2 * (α * X x - β * X y) * chapterVICurvePolynomial U := by
  rw [show α * X x ^ 2 * pderiv x (chapterVICurvePolynomial U) =
      α * X x * (X x * pderiv x (chapterVICurvePolynomial U)) by ring,
    show β * X y ^ 2 * pderiv y (chapterVICurvePolynomial U) =
      β * X y * (X y * pderiv y (chapterVICurvePolynomial U)) by ring,
    chapterVI_curvePolynomial_derivative, chapterVI_curvePolynomial_derivative]
  have hxsum : (∑ i, chapterVICurveAuxiliary x U i * U i) =
      X y * ∑ i, Wₓ i * U i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [hauxX]
    ring
  have hysum : (∑ i, chapterVICurveAuxiliary y U i * U i) =
      X x * ∑ i, Wᵧ i * U i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [hauxY]
    ring
  rw [hxsum, hysum]
  ring

/-- The three cubic forms in Poincaré's representation of `P`, with coefficient families left
abstract. -/
def chapterVICubicFamily {σ R : Type*} [CommRing R] (x y : σ)
    (A B C D E : Fin 3 → R) (i : Fin 3) : MvPolynomial σ R :=
  chapterVICubicForm x y (A i) (B i) (C i) (D i) (E i)

/-- The factor left after extracting `y` from `x ∂Uᵢ/∂x - Uᵢ`. -/
def chapterVICubicFirstReduced {σ R : Type*} [CommRing R] (x : σ)
    (A E : Fin 3 → R) (i : Fin 3) : MvPolynomial σ R :=
  MvPolynomial.C (A i) * X x ^ 2 - MvPolynomial.C (E i)

/-- The factor left after extracting `x` from `y ∂Uᵢ/∂y - Uᵢ`. -/
def chapterVICubicSecondReduced {σ R : Type*} [CommRing R] (y : σ)
    (B D : Fin 3 → R) (i : Fin 3) : MvPolynomial σ R :=
  MvPolynomial.C (B i) * X y ^ 2 - MvPolynomial.C (D i)

/-- Poincaré's exact reduction of the derivative equation for his displayed cubic forms. The
arbitrary factors `α` and `β` stand for the two parameter-dependent quadratic factors in §103.
The identity makes precise both the removable factor `2xy` on `P = 0` and the multiple of `P`
discarded in the source. -/
theorem chapterVI_cubicDerivativeCurveEquation_reduction
    {σ R : Type*} [CommRing R] (x y : σ) (hxy : x ≠ y)
    (A B C D E : Fin 3 → R) (α β : MvPolynomial σ R) :
    let U := chapterVICubicFamily x y A B C D E
    α * X x ^ 2 * pderiv x (chapterVICurvePolynomial U) -
        β * X y ^ 2 * pderiv y (chapterVICurvePolynomial U) =
      2 * X x * X y *
          (α * ∑ i, chapterVICubicFirstReduced x A E i * U i -
            β * ∑ i, chapterVICubicSecondReduced y B D i * U i) +
        2 * (α * X x - β * X y) * chapterVICurvePolynomial U := by
  dsimp only
  apply chapterVI_derivativeCurveEquation_reduction
  · intro i
    rw [chapterVICurveAuxiliary, chapterVICubicFamily,
      chapterVI_cubicForm_auxiliary x y _ _ _ _ _ hxy.symm]
    unfold chapterVICubicFirstReduced
    ring
  · intro i
    rw [chapterVICurveAuxiliary, chapterVICubicFamily,
      chapterVI_cubicForm_auxiliary_second x y _ _ _ _ _ hxy]
    unfold chapterVICubicSecondReduced
    ring

/-- The degree estimate behind the phrase "the curve `R = 0` is only of the seventh degree" in
§103. This theorem exposes the exact hypotheses: the two outside factors have degree at most two,
the reduced auxiliary factors degree at most two, and the three cubic forms degree at most three.
-/
theorem chapterVI_reducedCurve_totalDegree_le_seven
    {σ R : Type*} [CommRing R] (U Wₓ Wᵧ : Fin 3 → MvPolynomial σ R)
    (α β : MvPolynomial σ R)
    (hU : ∀ i, (U i).totalDegree ≤ 3)
    (hWₓ : ∀ i, (Wₓ i).totalDegree ≤ 2)
    (hWᵧ : ∀ i, (Wᵧ i).totalDegree ≤ 2)
    (hα : α.totalDegree ≤ 2) (hβ : β.totalDegree ≤ 2) :
    (α * ∑ i, Wₓ i * U i - β * ∑ i, Wᵧ i * U i).totalDegree ≤ 7 := by
  have hxProduct (i : Fin 3) : (Wₓ i * U i).totalDegree ≤ 5 :=
    (totalDegree_mul _ _).trans ((Nat.add_le_add (hWₓ i) (hU i)).trans (by norm_num))
  have hyProduct (i : Fin 3) : (Wᵧ i * U i).totalDegree ≤ 5 :=
    (totalDegree_mul _ _).trans ((Nat.add_le_add (hWᵧ i) (hU i)).trans (by norm_num))
  have hxSum : (∑ i, Wₓ i * U i).totalDegree ≤ 5 :=
    totalDegree_finsetSum_le fun i _ ↦ hxProduct i
  have hySum : (∑ i, Wᵧ i * U i).totalDegree ≤ 5 :=
    totalDegree_finsetSum_le fun i _ ↦ hyProduct i
  have hx : (α * ∑ i, Wₓ i * U i).totalDegree ≤ 7 :=
    (totalDegree_mul _ _).trans ((Nat.add_le_add hα hxSum).trans (by norm_num))
  have hy : (β * ∑ i, Wᵧ i * U i).totalDegree ≤ 7 :=
    (totalDegree_mul _ _).trans ((Nat.add_le_add hβ hySum).trans (by norm_num))
  exact (totalDegree_sub _ _).trans (max_le hx hy)

end PoincareChapterVI
