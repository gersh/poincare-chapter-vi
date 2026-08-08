/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import Mathlib.Analysis.Complex.SqrtDeriv

/-!
# Compatible square-root branches for Poincaré's prepared pinch

In Chapter VI, §99, Poincaré writes the local radicand as

`((t-h)²+k) ψ₁`.

A formal factorization alone is insufficient: the contour integrand needs a compatible analytic
square-root branch.  This file supplies the local branch construction on any domain where both
the quadratic factor and the analytic unit take values in `Complex.slitPlane`.  On such a domain,
the product of the two principal square roots is holomorphic, squares to the prepared radicand,
and has a holomorphic inverse.

The remaining source work is geometric: construct a neighborhood of Poincaré's transported cycle
on which the actual prepared factors satisfy these slit-plane hypotheses.
-/

noncomputable section

open Set

namespace PoincareChapterVI

/-- The principal complex square root really squares to its input on the slit plane. -/
theorem Complex.sq_sqrt_of_mem_slitPlane {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    Complex.sqrt z ^ 2 = z := by
  have hz0 : z ≠ 0 := Complex.slitPlane_ne_zero hz
  rw [sqrt_eq_exp hz0, pow_two, ← Complex.exp_add]
  convert Complex.exp_log hz0 using 1
  ring_nf

/-- Consequently, the principal square root does not vanish on the slit plane. -/
theorem Complex.sqrt_ne_zero_of_mem_slitPlane {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    Complex.sqrt z ≠ 0 := by
  intro hsqrt
  have := Complex.sq_sqrt_of_mem_slitPlane hz
  rw [hsqrt, zero_pow (by norm_num)] at this
  exact Complex.slitPlane_ne_zero hz this.symm

/-- The compatible square-root branch of a prepared radicand `quadratic * unit`. -/
def chapterVIPreparedSquareRoot
    (quadratic unit : ℂ → ℂ) (z : ℂ) : ℂ :=
  Complex.sqrt (quadratic z) * Complex.sqrt (unit z)

/-- The inverse branch occurring in the prepared local contour integrand. -/
def chapterVIPreparedInverseSquareRoot
    (quadratic unit : ℂ → ℂ) (z : ℂ) : ℂ :=
  (chapterVIPreparedSquareRoot quadratic unit z)⁻¹

/-- Pointwise correctness of the compatible prepared square-root branch. -/
theorem chapterVIPreparedSquareRoot_sq
    {quadratic unit : ℂ → ℂ} {z : ℂ}
    (hquadratic : quadratic z ∈ Complex.slitPlane)
    (hunit : unit z ∈ Complex.slitPlane) :
    chapterVIPreparedSquareRoot quadratic unit z ^ 2 = quadratic z * unit z := by
  rw [chapterVIPreparedSquareRoot, mul_pow,
    Complex.sq_sqrt_of_mem_slitPlane hquadratic,
    Complex.sq_sqrt_of_mem_slitPlane hunit]

/-- The prepared square-root branch is nonzero wherever both factors lie in the slit plane. -/
theorem chapterVIPreparedSquareRoot_ne_zero
    {quadratic unit : ℂ → ℂ} {z : ℂ}
    (hquadratic : quadratic z ∈ Complex.slitPlane)
    (hunit : unit z ∈ Complex.slitPlane) :
    chapterVIPreparedSquareRoot quadratic unit z ≠ 0 := by
  exact mul_ne_zero
    (Complex.sqrt_ne_zero_of_mem_slitPlane hquadratic)
    (Complex.sqrt_ne_zero_of_mem_slitPlane hunit)

/-- The inverse branch is the product of the two inverse principal branches. -/
theorem chapterVIPreparedInverseSquareRoot_eq
    (quadratic unit : ℂ → ℂ) (z : ℂ) :
    chapterVIPreparedInverseSquareRoot quadratic unit z =
      (Complex.sqrt (quadratic z))⁻¹ * (Complex.sqrt (unit z))⁻¹ := by
  simp [chapterVIPreparedInverseSquareRoot, chapterVIPreparedSquareRoot, mul_comm]

/-- Algebraic correctness of the inverse square-root branch. -/
theorem chapterVIPreparedInverseSquareRoot_sq_mul
    {quadratic unit : ℂ → ℂ} {z : ℂ}
    (hquadratic : quadratic z ∈ Complex.slitPlane)
    (hunit : unit z ∈ Complex.slitPlane) :
    chapterVIPreparedInverseSquareRoot quadratic unit z ^ 2 *
        (quadratic z * unit z) = 1 := by
  rw [← chapterVIPreparedSquareRoot_sq hquadratic hunit]
  have hbranch := chapterVIPreparedSquareRoot_ne_zero hquadratic hunit
  simp [chapterVIPreparedInverseSquareRoot, hbranch]

/-- Holomorphicity of the compatible square-root branch on a common slit-plane chart. -/
theorem differentiableOn_chapterVIPreparedSquareRoot
    {quadratic unit : ℂ → ℂ} {s : Set ℂ}
    (hquadratic : DifferentiableOn ℂ quadratic s)
    (hunit : DifferentiableOn ℂ unit s)
    (hquadraticMap : MapsTo quadratic s Complex.slitPlane)
    (hunitMap : MapsTo unit s Complex.slitPlane) :
    DifferentiableOn ℂ (chapterVIPreparedSquareRoot quadratic unit) s := by
  exact (Complex.differentiableOn_sqrt.fun_comp hquadratic hquadraticMap).mul
    (Complex.differentiableOn_sqrt.fun_comp hunit hunitMap)

/-- Holomorphicity of the inverse branch used by the local contour integrand. -/
theorem differentiableOn_chapterVIPreparedInverseSquareRoot
    {quadratic unit : ℂ → ℂ} {s : Set ℂ}
    (hquadratic : DifferentiableOn ℂ quadratic s)
    (hunit : DifferentiableOn ℂ unit s)
    (hquadraticMap : MapsTo quadratic s Complex.slitPlane)
    (hunitMap : MapsTo unit s Complex.slitPlane) :
    DifferentiableOn ℂ (chapterVIPreparedInverseSquareRoot quadratic unit) s := by
  apply (differentiableOn_chapterVIPreparedSquareRoot
    hquadratic hunit hquadraticMap hunitMap).inv
  intro z hz
  exact chapterVIPreparedSquareRoot_ne_zero (hquadraticMap hz) (hunitMap hz)

end PoincareChapterVI
