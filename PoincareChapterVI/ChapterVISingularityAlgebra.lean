/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex

/-!
# Algebra behind Poincaré's Chapter VI singularity equations

This file verifies exact algebraic reductions in §96 of Poincaré's first volume. It treats the
planar complexified Kepler coordinates, the first-kind collision equations, the tangent-half-angle
form of the Kepler branch equation, and the reciprocal symmetry of equations (7) and (8).

The printed equation (10) on p. 290 contains `x² - 1`, although it is derived immediately from
`1 - sin φ cos u = -β` and is then called reciprocal. The derivation formally verified below gives
`x² + 1`; with that correction both equations (9) and (10) have the stated reciprocal symmetry.
-/

noncomputable section

open Complex
open scoped ComplexConjugate

namespace PoincareChapterVI

/-- Poincaré's complex planar Kepler coordinate `ξ` in §96. -/
def chapterVIPlanarKeplerCoordinate (φ u : ℝ) : ℂ :=
  Real.cos u - Real.sin φ + I * (Real.cos φ * Real.sin u)

/-- The companion coordinate `ξ₀`, obtained by changing the sign of the imaginary component. -/
def chapterVIPlanarKeplerCoordinateConjugate (φ u : ℝ) : ℂ :=
  Real.cos u - Real.sin φ - I * (Real.cos φ * Real.sin u)

/-- The identity `ξ ξ₀ = (1 - sin φ cos u)²` used to derive equations (9) and (10) in §96. -/
theorem chapterVI_planarKeplerCoordinate_mul_conjugate (φ u : ℝ) :
    chapterVIPlanarKeplerCoordinate φ u *
        chapterVIPlanarKeplerCoordinateConjugate φ u =
      ((1 - Real.sin φ * Real.cos u) ^ 2 : ℝ) := by
  have hreal :
      (Real.cos u - Real.sin φ) ^ 2 + (Real.cos φ * Real.sin u) ^ 2 =
        (1 - Real.sin φ * Real.cos u) ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq u, Real.sin_sq_add_cos_sq φ]
  have hconjugate : chapterVIPlanarKeplerCoordinateConjugate φ u =
      conj (chapterVIPlanarKeplerCoordinate φ u) := by
    apply Complex.ext <;>
      simp [chapterVIPlanarKeplerCoordinate, chapterVIPlanarKeplerCoordinateConjugate]
  rw [hconjugate, Complex.mul_conj]
  norm_cast
  simpa only [Complex.normSq_apply, chapterVIPlanarKeplerCoordinate, add_re, add_im,
    sub_re, sub_im, mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im, zero_mul,
    mul_zero, sub_zero, zero_sub, add_zero, zero_add, neg_neg, mul_one, one_mul,
    pow_two] using hreal

/-- The cleared polynomial form of Poincaré's first-kind equations (9) and (10).

The parameter `sign` is `1` for equation (9) and `-1` for the corrected equation (10). -/
def chapterVIFirstKindCollisionPolynomial
    (eccentricity beta sign x : ℂ) : ℂ :=
  2 * x - eccentricity * (x ^ 2 + 1) - 2 * sign * beta * x

/-- Clearing the denominator in
`1 - e (x + x⁻¹) / 2 = sign * β` gives the first-kind collision polynomial. -/
theorem chapterVI_firstKindCollisionEquation_iff
    {eccentricity beta sign x : ℂ} (hx : x ≠ 0) :
    1 - eccentricity * ((x + x⁻¹) / 2) = sign * beta ↔
      chapterVIFirstKindCollisionPolynomial eccentricity beta sign x = 0 := by
  unfold chapterVIFirstKindCollisionPolynomial
  field_simp [hx]
  constructor
  · exact sub_eq_zero.mpr
  · exact sub_eq_zero.mp

/-- The first-kind collision polynomial is reciprocal. -/
theorem chapterVI_firstKindCollisionPolynomial_reciprocal
    (eccentricity beta sign : ℂ) {x : ℂ} (hx : x ≠ 0) :
    x ^ 2 * chapterVIFirstKindCollisionPolynomial eccentricity beta sign x⁻¹ =
      chapterVIFirstKindCollisionPolynomial eccentricity beta sign x := by
  unfold chapterVIFirstKindCollisionPolynomial
  field_simp [hx]
  ring

/-- Hence every nonzero first-kind collision root has its inverse as another root. -/
theorem chapterVI_firstKindCollisionRoot_inv
    (eccentricity beta sign : ℂ) {x : ℂ} (hx : x ≠ 0)
    (hroot : chapterVIFirstKindCollisionPolynomial eccentricity beta sign x = 0) :
    chapterVIFirstKindCollisionPolynomial eccentricity beta sign x⁻¹ = 0 := by
  have hreciprocal :=
    chapterVI_firstKindCollisionPolynomial_reciprocal eccentricity beta sign hx
  rw [hroot] at hreciprocal
  exact (mul_eq_zero.mp hreciprocal).resolve_left (pow_ne_zero 2 hx)

/-- Equation (1) of §96 after substituting `sin φ = 2τ / (1 + τ²)` and clearing the
denominator. -/
def chapterVIKeplerBranchPolynomial (τ x : ℂ) : ℂ :=
  2 * x * (1 + τ ^ 2) - 2 * τ * (x ^ 2 + 1)

/-- The exact factorization behind Poincaré's two solutions `x = τ` and `x = 1/τ`. -/
theorem chapterVI_keplerBranchPolynomial_factor (τ x : ℂ) :
    chapterVIKeplerBranchPolynomial τ x = -2 * (x - τ) * (τ * x - 1) := by
  unfold chapterVIKeplerBranchPolynomial
  ring

/-- The tangent-half-angle parameter is one root of equation (1). -/
@[simp]
theorem chapterVI_keplerBranchPolynomial_self (τ : ℂ) :
    chapterVIKeplerBranchPolynomial τ τ = 0 := by
  rw [chapterVI_keplerBranchPolynomial_factor]
  ring

/-- For nonzero `τ`, its inverse is the other root of equation (1). -/
@[simp]
theorem chapterVI_keplerBranchPolynomial_inv {τ : ℂ} (hτ : τ ≠ 0) :
    chapterVIKeplerBranchPolynomial τ τ⁻¹ = 0 := by
  rw [chapterVI_keplerBranchPolynomial_factor]
  simp [hτ]

/-- Equation (1) has precisely the two roots stated by Poincaré, with a repeated root allowed. -/
theorem chapterVI_keplerBranchPolynomial_eq_zero_iff (τ x : ℂ) :
    chapterVIKeplerBranchPolynomial τ x = 0 ↔ x = τ ∨ τ * x = 1 := by
  rw [chapterVI_keplerBranchPolynomial_factor]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with hproduct | hsecond
    · have hfirst : x - τ = 0 :=
        (mul_eq_zero.mp hproduct).resolve_left (by norm_num)
      exact Or.inl (sub_eq_zero.mp hfirst)
    · exact Or.inr (sub_eq_zero.mp hsecond)
  · rintro (rfl | hroot)
    · ring
    · rw [hroot]
      ring

/-- The trigonometric identities used when Poincaré sets `τ = tan (φ / 2)`. The exclusion
`cos φ ≠ -1` is the usual pole of the rational half-angle expression for cosine. -/
theorem chapterVI_tangentHalfAngle_relations (φ : ℝ) (hφ : Real.cos φ ≠ -1) :
    (1 + Real.tan (φ / 2) ^ 2) * Real.sin φ = 2 * Real.tan (φ / 2) ∧
      (1 + Real.tan (φ / 2) ^ 2) * Real.cos φ =
        1 - Real.tan (φ / 2) ^ 2 := by
  have hdenominator : 1 + Real.tan (φ / 2) ^ 2 ≠ 0 := by positivity
  constructor
  · rw [Real.sin_eq_two_mul_tan_half_div_one_add_tan_half_sq]
    field_simp
  · rw [Real.cos_eq_two_mul_tan_half_div_one_sub_tan_half_sq φ hφ]
    field_simp

/-- The numerator multiplying `1 / (2x)` in the planar collision equation `ξ = βη`. -/
def chapterVIPlanarDistanceFactorPlus (eccentricity complement x : ℂ) : ℂ :=
  (x ^ 2 + 1) - 2 * x * eccentricity + complement * (x ^ 2 - 1)

/-- The conjugate numerator multiplying `1 / (2x)` in `ξ₀ = β₀η₀`. -/
def chapterVIPlanarDistanceFactorMinus (eccentricity complement x : ℂ) : ℂ :=
  (x ^ 2 + 1) - 2 * x * eccentricity - complement * (x ^ 2 - 1)

/-- Poincaré's coordinate `ξ`, after the substitution `x = exp(iu)`, written as a Laurent
function of `x`.  The parameters are `sin φ` and `cos φ`. -/
def chapterVIPlanarKeplerLaurentPlus (eccentricity complement x : ℂ) : ℂ :=
  chapterVIPlanarDistanceFactorPlus eccentricity complement x / (2 * x)

/-- The companion coordinate `ξ₀`, after `x = exp(iu)`, as a Laurent function of `x`. -/
def chapterVIPlanarKeplerLaurentMinus (eccentricity complement x : ℂ) : ℂ :=
  chapterVIPlanarDistanceFactorMinus eccentricity complement x / (2 * x)

/-- The Laurent formula is Poincaré's original trigonometric coordinate when
`x = exp(iu)`. -/
theorem chapterVI_planarKeplerLaurentPlus_exp (φ u : ℝ) :
    chapterVIPlanarKeplerLaurentPlus (Real.sin φ) (Real.cos φ)
        (exp ((u : ℂ) * I)) =
      chapterVIPlanarKeplerCoordinate φ u := by
  rw [chapterVIPlanarKeplerLaurentPlus, div_eq_iff]
  · simp only [chapterVIPlanarDistanceFactorPlus, chapterVIPlanarKeplerCoordinate,
      exp_mul_I, ofReal_cos, ofReal_sin]
    ring_nf
    simp only [I_sq]
    rw [Complex.cos_sq' (u : ℂ)]
    ring
  · exact mul_ne_zero (by norm_num) (exp_ne_zero _)

/-- The same source identification for `ξ₀`. -/
theorem chapterVI_planarKeplerLaurentMinus_exp (φ u : ℝ) :
    chapterVIPlanarKeplerLaurentMinus (Real.sin φ) (Real.cos φ)
        (exp ((u : ℂ) * I)) =
      chapterVIPlanarKeplerCoordinateConjugate φ u := by
  rw [chapterVIPlanarKeplerLaurentMinus, div_eq_iff]
  · simp only [chapterVIPlanarDistanceFactorMinus, chapterVIPlanarKeplerCoordinateConjugate,
      exp_mul_I, ofReal_cos, ofReal_sin]
    ring_nf
    simp only [I_sq]
    rw [Complex.cos_sq' (u : ℂ)]
    ring
  · exact mul_ne_zero (by norm_num) (exp_ne_zero _)

/-- The first collision factor `H = ξ - βη` from §96, in Poincaré's Laurent variables. -/
def chapterVIPlanarCollisionFactorPlus
    (firstEccentricity firstComplement secondEccentricity secondComplement beta x y : ℂ) : ℂ :=
  chapterVIPlanarKeplerLaurentPlus firstEccentricity firstComplement x -
    beta * chapterVIPlanarKeplerLaurentPlus secondEccentricity secondComplement y

/-- The conjugate collision factor `H₀ = ξ₀ - β₀η₀` from §96. -/
def chapterVIPlanarCollisionFactorMinus
    (firstEccentricity firstComplement secondEccentricity secondComplement betaZero x y : ℂ) : ℂ :=
  chapterVIPlanarKeplerLaurentMinus firstEccentricity firstComplement x -
    betaZero * chapterVIPlanarKeplerLaurentMinus secondEccentricity secondComplement y

/-- The actual planar radicand displayed by Poincaré in §96:
`(ξ - βη) (ξ₀ - β₀η₀)`. -/
def chapterVIPlanarSourceRadicand
    (firstEccentricity firstComplement secondEccentricity secondComplement beta betaZero x y : ℂ) :
    ℂ :=
  chapterVIPlanarCollisionFactorPlus firstEccentricity firstComplement
      secondEccentricity secondComplement beta x y *
    chapterVIPlanarCollisionFactorMinus firstEccentricity firstComplement
      secondEccentricity secondComplement betaZero x y

/-- The Laurent radicand specializes exactly to the product `(ξ - βη)(ξ₀ - β₀η₀)` printed
in §96.  This is the concrete source radicand underlying the abstract convergent series `ψ(z,t)`
used later in §99. -/
theorem chapterVI_planarSourceRadicand_exp
    (φ φ' u u' : ℝ) (beta betaZero : ℂ) :
    chapterVIPlanarSourceRadicand (Real.sin φ) (Real.cos φ)
        (Real.sin φ') (Real.cos φ') beta betaZero
        (exp ((u : ℂ) * I)) (exp ((u' : ℂ) * I)) =
      (chapterVIPlanarKeplerCoordinate φ u -
          beta * chapterVIPlanarKeplerCoordinate φ' u') *
        (chapterVIPlanarKeplerCoordinateConjugate φ u -
          betaZero * chapterVIPlanarKeplerCoordinateConjugate φ' u') := by
  simp only [chapterVIPlanarSourceRadicand, chapterVIPlanarCollisionFactorPlus,
    chapterVIPlanarCollisionFactorMinus, chapterVI_planarKeplerLaurentPlus_exp,
    chapterVI_planarKeplerLaurentMinus_exp]

/-- Poincaré's general planar equation (3), before the second eccentricity is specialized to
zero, with the denominators `2xy` cleared. -/
def chapterVIPlanarCollisionEquationThreeGeneral
    (firstEccentricity firstComplement secondEccentricity secondComplement beta x y : ℂ) : ℂ :=
  y * chapterVIPlanarDistanceFactorPlus firstEccentricity firstComplement x -
    beta * x * chapterVIPlanarDistanceFactorPlus secondEccentricity secondComplement y

/-- Poincaré's general planar equation (4), with the denominators `2xy` cleared. -/
def chapterVIPlanarCollisionEquationFourGeneral
    (firstEccentricity firstComplement secondEccentricity secondComplement betaZero x y : ℂ) :
    ℂ :=
  y * chapterVIPlanarDistanceFactorMinus firstEccentricity firstComplement x -
    betaZero * x * chapterVIPlanarDistanceFactorMinus secondEccentricity secondComplement y

/-- Exact source identification of the first Laurent collision factor. -/
theorem chapterVI_planarCollisionFactorPlus_eq_cleared
    (firstEccentricity firstComplement secondEccentricity secondComplement beta : ℂ)
    {x y : ℂ} (hx : x ≠ 0) (hy : y ≠ 0) :
    (2 * x * y) * chapterVIPlanarCollisionFactorPlus firstEccentricity firstComplement
        secondEccentricity secondComplement beta x y =
      chapterVIPlanarCollisionEquationThreeGeneral firstEccentricity firstComplement
        secondEccentricity secondComplement beta x y := by
  unfold chapterVIPlanarCollisionFactorPlus chapterVIPlanarKeplerLaurentPlus
    chapterVIPlanarCollisionEquationThreeGeneral
  field_simp [hx, hy]

/-- Exact source identification of the conjugate Laurent collision factor. -/
theorem chapterVI_planarCollisionFactorMinus_eq_cleared
    (firstEccentricity firstComplement secondEccentricity secondComplement betaZero : ℂ)
    {x y : ℂ} (hx : x ≠ 0) (hy : y ≠ 0) :
    (2 * x * y) * chapterVIPlanarCollisionFactorMinus firstEccentricity firstComplement
        secondEccentricity secondComplement betaZero x y =
      chapterVIPlanarCollisionEquationFourGeneral firstEccentricity firstComplement
        secondEccentricity secondComplement betaZero x y := by
  unfold chapterVIPlanarCollisionFactorMinus chapterVIPlanarKeplerLaurentMinus
    chapterVIPlanarCollisionEquationFourGeneral
  field_simp [hx, hy]

/-- Clearing the Laurent denominator in Poincaré's actual §96 radicand gives the product of
his displayed algebraic collision equations (3) and (4). -/
theorem chapterVI_planarSourceRadicand_eq_cleared
    (firstEccentricity firstComplement secondEccentricity secondComplement beta betaZero : ℂ)
    {x y : ℂ} (hx : x ≠ 0) (hy : y ≠ 0) :
    (2 * x * y) ^ 2 * chapterVIPlanarSourceRadicand firstEccentricity firstComplement
        secondEccentricity secondComplement beta betaZero x y =
      chapterVIPlanarCollisionEquationThreeGeneral firstEccentricity firstComplement
          secondEccentricity secondComplement beta x y *
        chapterVIPlanarCollisionEquationFourGeneral firstEccentricity firstComplement
          secondEccentricity secondComplement betaZero x y := by
  unfold chapterVIPlanarSourceRadicand
  rw [pow_two]
  have hplus := chapterVI_planarCollisionFactorPlus_eq_cleared
    firstEccentricity firstComplement secondEccentricity secondComplement beta hx hy
  have hminus := chapterVI_planarCollisionFactorMinus_eq_cleared
    firstEccentricity firstComplement secondEccentricity secondComplement betaZero hx hy
  calc
    (2 * x * y) * (2 * x * y) *
        (chapterVIPlanarCollisionFactorPlus firstEccentricity firstComplement
            secondEccentricity secondComplement beta x y *
          chapterVIPlanarCollisionFactorMinus firstEccentricity firstComplement
            secondEccentricity secondComplement betaZero x y) =
        ((2 * x * y) * chapterVIPlanarCollisionFactorPlus firstEccentricity firstComplement
            secondEccentricity secondComplement beta x y) *
          ((2 * x * y) * chapterVIPlanarCollisionFactorMinus firstEccentricity firstComplement
            secondEccentricity secondComplement betaZero x y) := by ring
    _ = _ := by rw [hplus, hminus]

/-- The tangent-half-angle substitution turns the `ξ` numerator into `2(x - τ)²`. -/
theorem chapterVI_planarDistanceFactorPlus_halfAngle
    (τ eccentricity complement x : ℂ)
    (hsine : (1 + τ ^ 2) * eccentricity = 2 * τ)
    (hcosine : (1 + τ ^ 2) * complement = 1 - τ ^ 2) :
    (1 + τ ^ 2) * chapterVIPlanarDistanceFactorPlus eccentricity complement x =
      2 * (x - τ) ^ 2 := by
  calc
    (1 + τ ^ 2) * chapterVIPlanarDistanceFactorPlus eccentricity complement x =
        (1 + τ ^ 2) * (x ^ 2 + 1) -
          2 * x * ((1 + τ ^ 2) * eccentricity) +
          ((1 + τ ^ 2) * complement) * (x ^ 2 - 1) := by
      unfold chapterVIPlanarDistanceFactorPlus
      ring
    _ = (1 + τ ^ 2) * (x ^ 2 + 1) - 2 * x * (2 * τ) +
        (1 - τ ^ 2) * (x ^ 2 - 1) := by rw [hsine, hcosine]
    _ = 2 * (x - τ) ^ 2 := by ring

/-- The conjugate numerator becomes `2(1 - τx)²`. -/
theorem chapterVI_planarDistanceFactorMinus_halfAngle
    (τ eccentricity complement x : ℂ)
    (hsine : (1 + τ ^ 2) * eccentricity = 2 * τ)
    (hcosine : (1 + τ ^ 2) * complement = 1 - τ ^ 2) :
    (1 + τ ^ 2) * chapterVIPlanarDistanceFactorMinus eccentricity complement x =
      2 * (1 - τ * x) ^ 2 := by
  calc
    (1 + τ ^ 2) * chapterVIPlanarDistanceFactorMinus eccentricity complement x =
        (1 + τ ^ 2) * (x ^ 2 + 1) -
          2 * x * ((1 + τ ^ 2) * eccentricity) -
          ((1 + τ ^ 2) * complement) * (x ^ 2 - 1) := by
      unfold chapterVIPlanarDistanceFactorMinus
      ring
    _ = (1 + τ ^ 2) * (x ^ 2 + 1) - 2 * x * (2 * τ) -
        (1 - τ ^ 2) * (x ^ 2 - 1) := by rw [hsine, hcosine]
    _ = 2 * (1 - τ * x) ^ 2 := by ring

/-- With both eccentricities retained, Poincaré's equation (3) becomes the cubic displayed in
§98 after the two tangent-half-angle substitutions. -/
theorem chapterVI_planarCollisionEquationThreeGeneral_halfAngle
    (τ τ' firstEccentricity firstComplement secondEccentricity secondComplement beta x y : ℂ)
    (hfirstSine : (1 + τ ^ 2) * firstEccentricity = 2 * τ)
    (hfirstCosine : (1 + τ ^ 2) * firstComplement = 1 - τ ^ 2)
    (hsecondSine : (1 + τ' ^ 2) * secondEccentricity = 2 * τ')
    (hsecondCosine : (1 + τ' ^ 2) * secondComplement = 1 - τ' ^ 2) :
    (1 + τ ^ 2) * (1 + τ' ^ 2) *
        chapterVIPlanarCollisionEquationThreeGeneral firstEccentricity firstComplement
          secondEccentricity secondComplement beta x y =
      2 * (y * (x - τ) ^ 2 * (1 + τ' ^ 2) -
        beta * x * (y - τ') ^ 2 * (1 + τ ^ 2)) := by
  unfold chapterVIPlanarCollisionEquationThreeGeneral
  calc
    (1 + τ ^ 2) * (1 + τ' ^ 2) *
        (y * chapterVIPlanarDistanceFactorPlus firstEccentricity firstComplement x -
          beta * x *
            chapterVIPlanarDistanceFactorPlus secondEccentricity secondComplement y) =
      y * ((1 + τ ^ 2) * chapterVIPlanarDistanceFactorPlus
          firstEccentricity firstComplement x) * (1 + τ' ^ 2) -
        beta * x * ((1 + τ' ^ 2) * chapterVIPlanarDistanceFactorPlus
          secondEccentricity secondComplement y) * (1 + τ ^ 2) := by ring
    _ = y * (2 * (x - τ) ^ 2) * (1 + τ' ^ 2) -
        beta * x * (2 * (y - τ') ^ 2) * (1 + τ ^ 2) := by
      rw [chapterVI_planarDistanceFactorPlus_halfAngle τ _ _ _ hfirstSine hfirstCosine,
        chapterVI_planarDistanceFactorPlus_halfAngle τ' _ _ _ hsecondSine hsecondCosine]
    _ = _ := by ring

/-- The corresponding two-eccentricity reduction of Poincaré's equation (4). -/
theorem chapterVI_planarCollisionEquationFourGeneral_halfAngle
    (τ τ' firstEccentricity firstComplement secondEccentricity secondComplement betaZero x y : ℂ)
    (hfirstSine : (1 + τ ^ 2) * firstEccentricity = 2 * τ)
    (hfirstCosine : (1 + τ ^ 2) * firstComplement = 1 - τ ^ 2)
    (hsecondSine : (1 + τ' ^ 2) * secondEccentricity = 2 * τ')
    (hsecondCosine : (1 + τ' ^ 2) * secondComplement = 1 - τ' ^ 2) :
    (1 + τ ^ 2) * (1 + τ' ^ 2) *
        chapterVIPlanarCollisionEquationFourGeneral firstEccentricity firstComplement
          secondEccentricity secondComplement betaZero x y =
      2 * (y * (1 - τ * x) ^ 2 * (1 + τ' ^ 2) -
        betaZero * x * (1 - τ' * y) ^ 2 * (1 + τ ^ 2)) := by
  unfold chapterVIPlanarCollisionEquationFourGeneral
  calc
    (1 + τ ^ 2) * (1 + τ' ^ 2) *
        (y * chapterVIPlanarDistanceFactorMinus firstEccentricity firstComplement x -
          betaZero * x *
            chapterVIPlanarDistanceFactorMinus secondEccentricity secondComplement y) =
      y * ((1 + τ ^ 2) * chapterVIPlanarDistanceFactorMinus
          firstEccentricity firstComplement x) * (1 + τ' ^ 2) -
        betaZero * x * ((1 + τ' ^ 2) * chapterVIPlanarDistanceFactorMinus
          secondEccentricity secondComplement y) * (1 + τ ^ 2) := by ring
    _ = y * (2 * (1 - τ * x) ^ 2) * (1 + τ' ^ 2) -
        betaZero * x * (2 * (1 - τ' * y) ^ 2) * (1 + τ ^ 2) := by
      rw [chapterVI_planarDistanceFactorMinus_halfAngle τ _ _ _ hfirstSine hfirstCosine,
        chapterVI_planarDistanceFactorMinus_halfAngle τ' _ _ _ hsecondSine hsecondCosine]
    _ = _ := by ring

/-- Poincaré's planar equation (3), with the second orbit circular. -/
def chapterVIPlanarCollisionEquationThree
    (eccentricity complement beta x y : ℂ) : ℂ :=
  chapterVIPlanarDistanceFactorPlus eccentricity complement x - 2 * beta * x * y

/-- Poincaré's planar equation (4), with the second orbit circular. -/
def chapterVIPlanarCollisionEquationFour
    (eccentricity complement beta x y : ℂ) : ℂ :=
  y * chapterVIPlanarDistanceFactorMinus eccentricity complement x - 2 * beta * x

/-- The circular-second-orbit equation (3) used in §96 is exactly the general source equation,
after removing the harmless nonzero factor `y`. -/
theorem chapterVI_planarCollisionEquationThreeGeneral_secondCircular
    (eccentricity complement beta x y : ℂ) :
    chapterVIPlanarCollisionEquationThreeGeneral eccentricity complement 0 1 beta x y =
      y * chapterVIPlanarCollisionEquationThree eccentricity complement beta x y := by
  unfold chapterVIPlanarCollisionEquationThreeGeneral chapterVIPlanarCollisionEquationThree
    chapterVIPlanarDistanceFactorPlus
  ring

/-- The circular-second-orbit equation (4) is literally the corresponding general equation. -/
theorem chapterVI_planarCollisionEquationFourGeneral_secondCircular
    (eccentricity complement beta x y : ℂ) :
    chapterVIPlanarCollisionEquationFourGeneral eccentricity complement 0 1 beta x y =
      chapterVIPlanarCollisionEquationFour eccentricity complement beta x y := by
  unfold chapterVIPlanarCollisionEquationFourGeneral chapterVIPlanarCollisionEquationFour
    chapterVIPlanarDistanceFactorMinus
  ring

/-- After the half-angle substitution, equation (3) is exactly Poincaré's displayed rational
formula with all denominators cleared. -/
theorem chapterVI_planarCollisionEquationThree_halfAngle
    (τ eccentricity complement beta x y : ℂ)
    (hsine : (1 + τ ^ 2) * eccentricity = 2 * τ)
    (hcosine : (1 + τ ^ 2) * complement = 1 - τ ^ 2) :
    (1 + τ ^ 2) *
        chapterVIPlanarCollisionEquationThree eccentricity complement beta x y =
      2 * ((x - τ) ^ 2 - beta * (1 + τ ^ 2) * x * y) := by
  unfold chapterVIPlanarCollisionEquationThree
  rw [mul_sub, chapterVI_planarDistanceFactorPlus_halfAngle τ _ _ _ hsine hcosine]
  ring

/-- After the half-angle substitution, equation (4) is exactly Poincaré's displayed rational
formula with all denominators cleared. -/
theorem chapterVI_planarCollisionEquationFour_halfAngle
    (τ eccentricity complement beta x y : ℂ)
    (hsine : (1 + τ ^ 2) * eccentricity = 2 * τ)
    (hcosine : (1 + τ ^ 2) * complement = 1 - τ ^ 2) :
    (1 + τ ^ 2) *
        chapterVIPlanarCollisionEquationFour eccentricity complement beta x y =
      2 * (y * (1 - τ * x) ^ 2 - beta * (1 + τ ^ 2) * x) := by
  unfold chapterVIPlanarCollisionEquationFour
  calc
    (1 + τ ^ 2) *
          (y * chapterVIPlanarDistanceFactorMinus eccentricity complement x -
            2 * beta * x) =
        y * ((1 + τ ^ 2) *
          chapterVIPlanarDistanceFactorMinus eccentricity complement x) -
            (1 + τ ^ 2) * (2 * beta * x) := by ring
    _ = y * (2 * (1 - τ * x) ^ 2) - (1 + τ ^ 2) * (2 * beta * x) := by
      rw [chapterVI_planarDistanceFactorMinus_halfAngle τ _ _ _ hsine hcosine]
    _ = 2 * (y * (1 - τ * x) ^ 2 - beta * (1 + τ ^ 2) * x) := by ring

/-- Equation (7) of §96 after the tangent-half-angle substitution and clearing denominators. -/
def chapterVISecondKindPolynomialSeven (a c τ x : ℂ) : ℂ :=
  c * (x + τ) * (1 + τ ^ 2) * x + a * (x - τ) ^ 2 * (1 - τ * x)

/-- Equation (8) of §96 after the tangent-half-angle substitution and clearing denominators. -/
def chapterVISecondKindPolynomialEight (a c τ x : ℂ) : ℂ :=
  c * (1 + τ * x) * (1 + τ ^ 2) * x + a * (1 - τ * x) ^ 2 * (x - τ)

/-- Equations (7) and (8) are exchanged by `x ↦ x⁻¹`, exactly as stated in §96. -/
theorem chapterVI_secondKindPolynomial_reciprocal
    (a c τ : ℂ) {x : ℂ} (hx : x ≠ 0) :
    x ^ 3 * chapterVISecondKindPolynomialSeven a c τ x⁻¹ =
      chapterVISecondKindPolynomialEight a c τ x := by
  unfold chapterVISecondKindPolynomialSeven chapterVISecondKindPolynomialEight
  field_simp [hx]

/-- A nonzero root of equation (7) gives an inverse root of equation (8). -/
theorem chapterVI_secondKindPolynomialEight_inv_root
    (a c τ : ℂ) {x : ℂ} (hx : x ≠ 0)
    (hroot : chapterVISecondKindPolynomialSeven a c τ x = 0) :
    chapterVISecondKindPolynomialEight a c τ x⁻¹ = 0 := by
  have hreciprocal := chapterVI_secondKindPolynomial_reciprocal a c τ (inv_ne_zero hx)
  simp only [inv_inv] at hreciprocal
  simpa only [hroot, mul_zero] using hreciprocal.symm

/-- The discriminant of Poincaré's small-eccentricity quadratic (12). -/
theorem chapterVI_equationTwelve_discriminant
    (a c φ : ℝ) :
    (2 * φ * (c - 2 * a)) ^ 2 -
        4 * (4 * (a + c)) * (a * φ ^ 2) =
      4 * φ ^ 2 * (c ^ 2 - 8 * a * c) := by
  ring

/-- In particular, the approximate equation (12) has nonnegative discriminant when `a` and `c`
have opposite signs, as asserted near the end of §96. -/
theorem chapterVI_equationTwelve_discriminant_nonnegative
    {a c φ : ℝ} (hopposite : a * c ≤ 0) :
    0 ≤ (2 * φ * (c - 2 * a)) ^ 2 -
      4 * (4 * (a + c)) * (a * φ ^ 2) := by
  rw [chapterVI_equationTwelve_discriminant]
  have hfactor : 0 ≤ c ^ 2 - 8 * a * c := by
    nlinarith [sq_nonneg c]
  positivity

/-- Poincaré's §96 parameter `z`, written in variables `x` and `y` with arbitrary complex
coefficients in the exponential. -/
def chapterVISingularityParameter
    (a c : ℤ) (firstScale secondScale x y : ℂ) : ℂ :=
  x ^ a * y ^ c *
    exp (firstScale * (x⁻¹ - x) + secondScale * (y⁻¹ - y))

/-- The §96 parameter is inverted when both complex eccentric-anomaly variables are inverted. -/
theorem chapterVI_singularityParameter_inv
    (a c : ℤ) (firstScale secondScale : ℂ) {x y : ℂ} :
    chapterVISingularityParameter a c firstScale secondScale x⁻¹ y⁻¹ =
      (chapterVISingularityParameter a c firstScale secondScale x y)⁻¹ := by
  unfold chapterVISingularityParameter
  simp only [inv_inv, inv_zpow]
  rw [show firstScale * (x - x⁻¹) + secondScale * (y - y⁻¹) =
      -(firstScale * (x⁻¹ - x) + secondScale * (y⁻¹ - y)) by ring]
  rw [exp_neg]
  simp only [mul_inv_rev]
  ring

end PoincareChapterVI
