/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import PoincareChapterVI.ChapterVISingularityAlgebra

/-!
# The constant-singular-value tangent in Poincaré's variables

Section 96 writes the singularity parameter as

`z = x^a y^c exp(a τ/(1+τ²) (x⁻¹-x) + c τ'/(1+τ'²) (y⁻¹-y))`.

Its logarithmic differential has coefficients

`a (x-τ)(1-τx)/(x²(1+τ²))` and
`c (y-τ')(1-τ'y)/(y²(1+τ'²))`.

This file verifies the formula and proves that the polynomial vector field used by Poincaré to
form `Q` and the reduced curve `R` is tangent to every level set of `z`.
-/

noncomputable section

namespace PoincareChapterVI.SingularityParameterTangent

open Complex
open Filter
open scoped Topology

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

/-- The exponential scale appearing after the tangent-half-angle substitution. -/
def halfAngleScale (exponent : ℤ) (τ : ℂ) : ℂ :=
  (exponent : ℂ) * τ / (1 + τ ^ 2)

/-- Poincaré's `z`, specialized to the half-angle parameters `τ,τ'`. -/
def halfAngleSingularityParameter
    (a c : ℤ) (τ τ' x y : ℂ) : ℂ :=
  chapterVISingularityParameter a c (halfAngleScale a τ) (halfAngleScale c τ') x y

/-- One coefficient of the logarithmic differential `dz/z`. -/
def halfAngleLogCoefficient (exponent : ℤ) (τ x : ℂ) : ℂ :=
  (exponent : ℂ) * (x - τ) * (1 - τ * x) / (x ^ 2 * (1 + τ ^ 2))

/-- The logarithmic differential of the singularity parameter on a velocity `(dx,dy)`. -/
def singularityLogDifferential
    (a c : ℤ) (τ τ' x y : ℂ) (velocity : ℂ × ℂ) : ℂ :=
  halfAngleLogCoefficient a τ x * velocity.1 +
    halfAngleLogCoefficient c τ' y * velocity.2

/-- The polynomial tangent vector appearing in Poincaré's displayed equation `Q = 0`. -/
def constantSingularityTangent
    (a c : ℤ) (τ τ' x y : ℂ) : ℂ × ℂ :=
  ((c : ℂ) * x ^ 2 * (1 + τ ^ 2) * (y - τ') * (1 - τ' * y),
    -(a : ℂ) * y ^ 2 * (1 + τ' ^ 2) * (x - τ) * (1 - τ * x))

/-- Direct logarithmic differentiation of the half-angle exponential gives the factored
coefficient used in §103. -/
theorem halfAngleLogCoefficient_eq
    (exponent : ℤ) (τ x : ℂ)
    (hx : x ≠ 0) (hτ : 1 + τ ^ 2 ≠ 0) :
    (exponent : ℂ) / x - halfAngleScale exponent τ * (1 / x ^ 2 + 1) =
      halfAngleLogCoefficient exponent τ x := by
  unfold halfAngleScale halfAngleLogCoefficient
  field_simp
  ring

/-- The vector used to form `Q` is tangent to the level set of Poincaré's singularity
parameter. -/
theorem singularityLogDifferential_constantSingularityTangent
    (a c : ℤ) (τ τ' x y : ℂ)
    (hx : x ≠ 0) (hy : y ≠ 0)
    (hτ : 1 + τ ^ 2 ≠ 0) (hτ' : 1 + τ' ^ 2 ≠ 0) :
    singularityLogDifferential a c τ τ' x y
      (constantSingularityTangent a c τ τ' x y) = 0 := by
  unfold singularityLogDifferential halfAngleLogCoefficient constantSingularityTangent
  field_simp
  ring

/-- The half-angle singularity parameter is nonzero away from the coordinate axes. -/
theorem halfAngleSingularityParameter_ne_zero
    (a c : ℤ) (τ τ' : ℂ) {x y : ℂ} (hx : x ≠ 0) (hy : y ≠ 0) :
    halfAngleSingularityParameter a c τ τ' x y ≠ 0 := by
  unfold halfAngleSingularityParameter chapterVISingularityParameter
  exact mul_ne_zero (mul_ne_zero (zpow_ne_zero _ hx) (zpow_ne_zero _ hy))
    (Complex.exp_ne_zero _)

/-- Chain-rule form of the logarithmic differential: along any differentiable `(x,y)` path,
the derivative of Poincaré's singularity parameter is `z` times the displayed covector. -/
theorem hasDerivAt_halfAngleSingularityParameter
    (a c : ℤ) (τ τ' : ℂ) {x y : ℂ → ℂ} {γ dx dy : ℂ}
    (hx : HasDerivAt x dx γ) (hy : HasDerivAt y dy γ)
    (hxne : x γ ≠ 0) (hyne : y γ ≠ 0)
    (hτ : 1 + τ ^ 2 ≠ 0) (hτ' : 1 + τ' ^ 2 ≠ 0) :
    HasDerivAt
      (fun parameter ↦ halfAngleSingularityParameter a c τ τ' (x parameter) (y parameter))
      (halfAngleSingularityParameter a c τ τ' (x γ) (y γ) *
        singularityLogDifferential a c τ τ' (x γ) (y γ) (dx, dy)) γ := by
  unfold complexAddCommGroupForCalculus complexNormedAddCommGroupForCalculus
  have hxpow : HasDerivAt (fun parameter ↦ x parameter ^ a)
      ((a : ℂ) * x γ ^ (a - 1) * dx) γ :=
    (hasDerivAt_zpow a (x γ) (Or.inl hxne)).comp γ hx
  have hypow : HasDerivAt (fun parameter ↦ y parameter ^ c)
      ((c : ℂ) * y γ ^ (c - 1) * dy) γ :=
    (hasDerivAt_zpow c (y γ) (Or.inl hyne)).comp γ hy
  have hxexponent : HasDerivAt
      (fun parameter ↦ halfAngleScale a τ * ((x parameter)⁻¹ - x parameter))
      (halfAngleScale a τ * (-dx / (x γ) ^ 2 - dx)) γ := by
    convert (hx.inv hxne).sub hx |>.const_mul (halfAngleScale a τ) using 1
    all_goals rfl
  have hyexponent : HasDerivAt
      (fun parameter ↦ halfAngleScale c τ' * ((y parameter)⁻¹ - y parameter))
      (halfAngleScale c τ' * (-dy / (y γ) ^ 2 - dy)) γ := by
    convert (hy.inv hyne).sub hy |>.const_mul (halfAngleScale c τ') using 1
    all_goals rfl
  have hexponential := (hxexponent.add hyexponent).cexp
  have hproduct := hxpow.mul (hypow.mul hexponential)
  convert hproduct using 1
  · exact complexAddCommGroupForCalculus_eq_field
  · funext parameter
    unfold halfAngleSingularityParameter chapterVISingularityParameter
    simp only [Pi.mul_apply, Pi.add_apply]
    ring
  · rw [zpow_sub_one₀ hxne, zpow_sub_one₀ hyne]
    simp only [Pi.mul_apply, Pi.add_apply]
    unfold halfAngleSingularityParameter chapterVISingularityParameter
    unfold singularityLogDifferential
    rw [← halfAngleLogCoefficient_eq a τ (x γ) hxne hτ,
      ← halfAngleLogCoefficient_eq c τ' (y γ) hyne hτ']
    field_simp
    ring

/-- If Poincaré's singularity parameter is locally constant along a differentiable path, its
velocity lies in the kernel of the displayed logarithmic differential.  This is the rigorous
chain-rule justification for the `dz = 0` step in §103. -/
theorem singularityLogDifferential_eq_zero_of_eventually_constant
    (a c : ℤ) (τ τ' : ℂ) {x y : ℂ → ℂ} {γ dx dy : ℂ}
    (hx : HasDerivAt x dx γ) (hy : HasDerivAt y dy γ)
    (hxne : x γ ≠ 0) (hyne : y γ ≠ 0)
    (hτ : 1 + τ ^ 2 ≠ 0) (hτ' : 1 + τ' ^ 2 ≠ 0)
    (hconstant :
      (fun parameter ↦ halfAngleSingularityParameter a c τ τ' (x parameter) (y parameter))
        =ᶠ[nhds γ]
      (fun _ ↦ halfAngleSingularityParameter a c τ τ' (x γ) (y γ))) :
    singularityLogDifferential a c τ τ' (x γ) (y γ) (dx, dy) = 0 := by
  let zPath :=
    fun parameter ↦ halfAngleSingularityParameter a c τ τ' (x parameter) (y parameter)
  have hz : HasDerivAt zPath
      (halfAngleSingularityParameter a c τ τ' (x γ) (y γ) *
        singularityLogDifferential a c τ τ' (x γ) (y γ) (dx, dy)) γ :=
    hasDerivAt_halfAngleSingularityParameter a c τ τ' hx hy hxne hyne hτ hτ'
  have hzero : HasDerivAt zPath 0 γ :=
    hconstant.hasDerivAt_iff.mpr (hasDerivAt_const γ _)
  have hproduct := hz.unique hzero
  exact (mul_eq_zero.mp hproduct).resolve_left
    (halfAngleSingularityParameter_ne_zero a c τ τ' hxne hyne)

end PoincareChapterVI.SingularityParameterTangent
