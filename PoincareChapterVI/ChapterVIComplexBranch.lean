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
    {X : Type*} (quadratic unit : X → ℂ) (x : X) : ℂ :=
  Complex.sqrt (quadratic x) * Complex.sqrt (unit x)

/-- The inverse branch occurring in the prepared local contour integrand. -/
def chapterVIPreparedInverseSquareRoot
    {X : Type*} (quadratic unit : X → ℂ) (x : X) : ℂ :=
  (chapterVIPreparedSquareRoot quadratic unit x)⁻¹

/-- Pointwise correctness of the compatible prepared square-root branch. -/
theorem chapterVIPreparedSquareRoot_sq
    {X : Type*} {quadratic unit : X → ℂ} {x : X}
    (hquadratic : quadratic x ∈ Complex.slitPlane)
    (hunit : unit x ∈ Complex.slitPlane) :
    chapterVIPreparedSquareRoot quadratic unit x ^ 2 = quadratic x * unit x := by
  rw [chapterVIPreparedSquareRoot, mul_pow,
    Complex.sq_sqrt_of_mem_slitPlane hquadratic,
    Complex.sq_sqrt_of_mem_slitPlane hunit]

/-- The prepared square-root branch is nonzero wherever both factors lie in the slit plane. -/
theorem chapterVIPreparedSquareRoot_ne_zero
    {X : Type*} {quadratic unit : X → ℂ} {x : X}
    (hquadratic : quadratic x ∈ Complex.slitPlane)
    (hunit : unit x ∈ Complex.slitPlane) :
    chapterVIPreparedSquareRoot quadratic unit x ≠ 0 := by
  exact mul_ne_zero
    (Complex.sqrt_ne_zero_of_mem_slitPlane hquadratic)
    (Complex.sqrt_ne_zero_of_mem_slitPlane hunit)

/-- The inverse branch is the product of the two inverse principal branches. -/
theorem chapterVIPreparedInverseSquareRoot_eq
    {X : Type*} (quadratic unit : X → ℂ) (x : X) :
    chapterVIPreparedInverseSquareRoot quadratic unit x =
      (Complex.sqrt (quadratic x))⁻¹ * (Complex.sqrt (unit x))⁻¹ := by
  simp [chapterVIPreparedInverseSquareRoot, chapterVIPreparedSquareRoot, mul_comm]

/-- Algebraic correctness of the inverse square-root branch. -/
theorem chapterVIPreparedInverseSquareRoot_sq_mul
    {X : Type*} {quadratic unit : X → ℂ} {x : X}
    (hquadratic : quadratic x ∈ Complex.slitPlane)
    (hunit : unit x ∈ Complex.slitPlane) :
    chapterVIPreparedInverseSquareRoot quadratic unit x ^ 2 *
        (quadratic x * unit x) = 1 := by
  rw [← chapterVIPreparedSquareRoot_sq hquadratic hunit]
  have hbranch := chapterVIPreparedSquareRoot_ne_zero hquadratic hunit
  simp [chapterVIPreparedInverseSquareRoot, hbranch]

/-- Holomorphicity of the compatible square-root branch on a common slit-plane chart. -/
theorem differentiableOn_chapterVIPreparedSquareRoot
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    {quadratic unit : X → ℂ} {s : Set X}
    (hquadratic : DifferentiableOn ℂ quadratic s)
    (hunit : DifferentiableOn ℂ unit s)
    (hquadraticMap : MapsTo quadratic s Complex.slitPlane)
    (hunitMap : MapsTo unit s Complex.slitPlane) :
    DifferentiableOn ℂ (chapterVIPreparedSquareRoot quadratic unit) s := by
  exact (Complex.differentiableOn_sqrt.fun_comp hquadratic hquadraticMap).mul
    (Complex.differentiableOn_sqrt.fun_comp hunit hunitMap)

/-- Holomorphicity of the inverse branch used by the local contour integrand. -/
theorem differentiableOn_chapterVIPreparedInverseSquareRoot
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    {quadratic unit : X → ℂ} {s : Set X}
    (hquadratic : DifferentiableOn ℂ quadratic s)
    (hunit : DifferentiableOn ℂ unit s)
    (hquadraticMap : MapsTo quadratic s Complex.slitPlane)
    (hunitMap : MapsTo unit s Complex.slitPlane) :
    DifferentiableOn ℂ (chapterVIPreparedInverseSquareRoot quadratic unit) s := by
  apply (differentiableOn_chapterVIPreparedSquareRoot
    hquadratic hunit hquadraticMap hunitMap).inv
  intro z hz
  exact chapterVIPreparedSquareRoot_ne_zero (hquadraticMap hz) (hunitMap hz)

/-- An open common branch chart for the two factors of a prepared radicand.  The protected set
may be a point, a contour, or a joint parameter-contour family. -/
structure ChapterVIPreparedBranchChart
    {X : Type*} [TopologicalSpace X]
    (quadratic unit : X → ℂ) (carrier : Set X) where
  domain : Set X
  isOpen_domain : IsOpen domain
  carrier_subset : carrier ⊆ domain
  quadratic_mapsTo : MapsTo quadratic domain Complex.slitPlane
  unit_mapsTo : MapsTo unit domain Complex.slitPlane

/-- Continuity promotes slit-plane values on the protected cycle to an open common branch chart.
No compactness assumption is needed: the intersection of the two slit-plane preimages already is
an open neighborhood of the entire protected set. -/
def ChapterVIPreparedBranchChart.of_continuous
    {X : Type*} [TopologicalSpace X]
    {quadratic unit : X → ℂ} {carrier : Set X}
    (hquadratic : Continuous quadratic) (hunit : Continuous unit)
    (hquadraticCarrier : MapsTo quadratic carrier Complex.slitPlane)
    (hunitCarrier : MapsTo unit carrier Complex.slitPlane) :
    ChapterVIPreparedBranchChart quadratic unit carrier where
  domain := quadratic ⁻¹' Complex.slitPlane ∩ unit ⁻¹' Complex.slitPlane
  isOpen_domain :=
    (Complex.isOpen_slitPlane.preimage hquadratic).inter
      (Complex.isOpen_slitPlane.preimage hunit)
  carrier_subset := fun _ hx ↦
    ⟨hquadraticCarrier hx, hunitCarrier hx⟩
  quadratic_mapsTo := fun _ hx ↦ hx.1
  unit_mapsTo := fun _ hx ↦ hx.2

/-- The inverse prepared branch is holomorphic on the automatically constructed joint chart. -/
theorem ChapterVIPreparedBranchChart.differentiableOn_inverseSquareRoot
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    {quadratic unit : X → ℂ} {carrier : Set X}
    (chart : ChapterVIPreparedBranchChart quadratic unit carrier)
    (hquadratic : Differentiable ℂ quadratic)
    (hunit : Differentiable ℂ unit) :
    DifferentiableOn ℂ (chapterVIPreparedInverseSquareRoot quadratic unit) chart.domain := by
  exact differentiableOn_chapterVIPreparedInverseSquareRoot
    hquadratic.differentiableOn hunit.differentiableOn
    chart.quadratic_mapsTo chart.unit_mapsTo

/-- Pointwise correctness of the inverse branch everywhere on a common branch chart. -/
theorem ChapterVIPreparedBranchChart.inverseSquareRoot_sq_mul
    {X : Type*} [TopologicalSpace X]
    {quadratic unit : X → ℂ} {carrier : Set X}
    (chart : ChapterVIPreparedBranchChart quadratic unit carrier)
    {x : X} (hx : x ∈ chart.domain) :
    chapterVIPreparedInverseSquareRoot quadratic unit x ^ 2 *
        (quadratic x * unit x) = 1 :=
  chapterVIPreparedInverseSquareRoot_sq_mul
    (chart.quadratic_mapsTo hx) (chart.unit_mapsTo hx)

end PoincareChapterVI
