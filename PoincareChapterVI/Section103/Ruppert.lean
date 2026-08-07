/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import Mathlib.Algebra.MvPolynomial.PDeriv

/-!
# The algebraic core of the Ruppert repair to Chapter VI, §103

Poincaré's intersection count yields a common component, whereas his text immediately concludes
that the two degree-six curves coincide.  One clean repair is to prove that his polynomial `P` is
absolutely irreducible.  Ruppert's criterion reduces absolute irreducibility of a bivariate
polynomial in characteristic zero to the full rank of a finite matrix.

This file verifies the quotient-rule identity behind the direction of Ruppert's criterion needed
here: every proper factor produces a solution of the linear differential equation.  Degree bounds,
the exact rank certificate for Poincaré's polynomial, and the resulting irreducibility theorem are
separate remaining steps.
-/

noncomputable section

namespace PoincareChapterVI

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- Polynomial form of
`∂y (g / f) = ∂x (h / f)`, with denominators cleared. -/
def chapterVIRuppertExpression
    (Dx Dy : Derivation R A A) (f g h : A) : A :=
  f * Dy g + h * Dx f - g * Dy f - f * Dx h

/-- A factorization `f = a b` produces the standard Ruppert solution
`g = b ∂x a`, `h = b ∂y a`, provided the two derivations commute. -/
theorem chapterVI_ruppertExpression_factor
    (Dx Dy : Derivation R A A)
    (hcommute : ∀ p : A, Dy (Dx p) = Dx (Dy p))
    (a b : A) :
    chapterVIRuppertExpression Dx Dy (a * b) (b * Dx a) (b * Dy a) = 0 := by
  simp only [chapterVIRuppertExpression, Derivation.leibniz, smul_eq_mul]
  rw [hcommute]
  ring

/-- Thus, in a domain, triviality of every Ruppert solution rules out a factor whose derivative
is nonzero.  This is the logical step used after a full-rank matrix certificate. -/
theorem chapterVI_no_factor_of_ruppert_solutions_trivial
    [IsDomain A]
    (Dx Dy : Derivation R A A)
    (hcommute : ∀ p : A, Dy (Dx p) = Dx (Dy p))
    (f a b : A) (hf : f = a * b) (hb : b ≠ 0)
    (htrivial : ∀ g h : A,
      chapterVIRuppertExpression Dx Dy f g h = 0 → g = 0 ∧ h = 0)
    (hderivative : Dx a ≠ 0 ∨ Dy a ≠ 0) : False := by
  have hsolution : chapterVIRuppertExpression Dx Dy f (b * Dx a) (b * Dy a) = 0 := by
    rw [hf]
    exact chapterVI_ruppertExpression_factor Dx Dy hcommute a b
  rcases htrivial _ _ hsolution with ⟨hx, hy⟩
  rcases hderivative with hax | hay
  · exact hax ((mul_eq_zero.mp hx).resolve_left hb)
  · exact hay ((mul_eq_zero.mp hy).resolve_left hb)

/-- Formal partial derivatives of multivariate polynomials commute. -/
theorem chapterVI_pderiv_commute
    {σ : Type*}
    (i j : σ) (p : MvPolynomial σ R) :
    MvPolynomial.pderiv j (MvPolynomial.pderiv i p) =
      MvPolynomial.pderiv i (MvPolynomial.pderiv j p) := by
  classical
  ext monomial
  simp only [MvPolynomial.coeff_pderiv]
  by_cases hij : i = j
  · subst j
    ring
  · simp only [Finsupp.add_apply, Finsupp.single_eq_of_ne hij,
      Finsupp.single_eq_of_ne (Ne.symm hij), add_zero]
    have hexponents :
        monomial + Finsupp.single j 1 + Finsupp.single i 1 =
          monomial + Finsupp.single i 1 + Finsupp.single j 1 := by
      abel
    rw [hexponents]
    ring

/-- Specialization of the factor-to-kernel identity to bivariate polynomial partial derivatives.
This is the exact differential equation used to build the finite Ruppert matrix. -/
theorem chapterVI_mvPolynomial_ruppertExpression_factor
    {σ : Type*}
    (x y : σ) (a b : MvPolynomial σ R) :
    chapterVIRuppertExpression (MvPolynomial.pderiv x) (MvPolynomial.pderiv y)
      (a * b) (b * MvPolynomial.pderiv x a) (b * MvPolynomial.pderiv y a) = 0 :=
  chapterVI_ruppertExpression_factor _ _
    (fun p ↦ chapterVI_pderiv_commute x y p) a b

end PoincareChapterVI
