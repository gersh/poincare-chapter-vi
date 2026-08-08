/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import LeanCompCert.Verified.Decide
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Topology.Order.IntermediateValue
import PoincareChapterVI.ChapterVISourceCoordinates

/-!
# A certified concrete point D from Poincaré's §96 discussion

Poincaré labels by `D` the negative small root of equation (7), paired with the collision
curve (3).  He works under open small-eccentricity hypotheses rather than specifying numerical
parameters.  This file begins a rigorous concrete instance in that regime:

* `a = -1`, `c = 3`;
* `τ = 1/100`, so the first eccentricity is `2τ/(1+τ²)`;
* `β = 2`, and the second orbit is circular.

After clearing denominators, equation (7) is

`2500 x³ + 500025 x² + 12501 x - 25 = 0`.

LeanCompCert certifies the endpoint signs.  The ordinary intermediate-value and derivative
theorems then produce the unique real `D` root in `(-27/1000, -26/1000)`.  Later certificate
files can use this isolated algebraic number without importing an untrusted numerical root.
-/

namespace PoincareChapterVI

noncomputable section

/-- Integer evaluation of the cleared D cubic at the rational `numerator / denominator`,
multiplied by `denominator³`. -/
def chapterVIDScaledEval (numerator denominator : ℤ) : ℤ :=
  2500 * numerator ^ 3 + 500025 * numerator ^ 2 * denominator +
    12501 * numerator * denominator ^ 2 - 25 * denominator ^ 3

/-- The compiled finite certificate isolating the sign change for the small negative D root. -/
theorem chapterVID_endpoint_certificate :
    0 < chapterVIDScaledEval (-27) 1000 ∧
      chapterVIDScaledEval (-26) 1000 < 0 := by
  verified_decide

/-- Cleared form of Poincaré's equation (7) at the concrete parameters. -/
def chapterVIDPolynomial (x : ℝ) : ℝ :=
  2500 * x ^ 3 + 500025 * x ^ 2 + 12501 * x - 25

theorem chapterVID_scaled_eval_sound (numerator denominator : ℤ)
    (hdenominator : denominator ≠ 0) :
    (denominator : ℝ) ^ 3 *
        chapterVIDPolynomial ((numerator : ℝ) / (denominator : ℝ)) =
      (chapterVIDScaledEval numerator denominator : ℤ) := by
  unfold chapterVIDPolynomial chapterVIDScaledEval
  field_simp [Int.cast_ne_zero.mpr hdenominator]
  push_cast
  ring

theorem chapterVIDPolynomial_left_pos :
    0 < chapterVIDPolynomial (-27 / 1000) := by
  have hcert : (0 : ℝ) < (chapterVIDScaledEval (-27) 1000 : ℤ) := by
    exact_mod_cast chapterVID_endpoint_certificate.1
  have hs := chapterVID_scaled_eval_sound (-27) 1000 (by norm_num)
  norm_num only [Int.cast_ofNat] at hs
  nlinarith

theorem chapterVIDPolynomial_right_neg :
    chapterVIDPolynomial (-26 / 1000) < 0 := by
  have hcert : ((chapterVIDScaledEval (-26) 1000 : ℤ) : ℝ) < 0 := by
    exact_mod_cast chapterVID_endpoint_certificate.2
  have hs := chapterVID_scaled_eval_sound (-26) 1000 (by norm_num)
  norm_num only [Int.cast_ofNat] at hs
  nlinarith

theorem hasDerivAt_chapterVIDPolynomial (x : ℝ) :
    HasDerivAt chapterVIDPolynomial
      (7500 * x ^ 2 + 1000050 * x + 12501) x := by
  unfold chapterVIDPolynomial
  convert (((((hasDerivAt_id x).pow 3).const_mul 2500).add
      (((hasDerivAt_id x).pow 2).const_mul 500025)).add
      ((hasDerivAt_id x).const_mul 12501)).sub (hasDerivAt_const x 25) using 1
  · rfl
  · rfl
  · funext y
    simp only [Pi.add_apply, Pi.sub_apply, Pi.pow_apply, id_eq]
  · norm_num [id_eq]
    ring

theorem continuous_chapterVIDPolynomial : Continuous chapterVIDPolynomial := by
  unfold chapterVIDPolynomial
  fun_prop

theorem chapterVIDPolynomial_deriv_neg
    {x : ℝ} (hx : x ∈ Set.Icc (-27 / 1000) (-26 / 1000)) :
    deriv chapterVIDPolynomial x < 0 := by
  rw [(hasDerivAt_chapterVIDPolynomial x).deriv]
  have hprod : 0 ≤ (1 - x) * (1 + x) := by
    apply mul_nonneg <;> nlinarith [hx.1, hx.2]
  nlinarith [hx.1, hx.2]

theorem chapterVIDPolynomial_strictAntiOn :
    StrictAntiOn chapterVIDPolynomial (Set.Icc (-27 / 1000) (-26 / 1000)) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
  · exact continuous_chapterVIDPolynomial.continuousOn
  · intro x hx
    exact chapterVIDPolynomial_deriv_neg (interior_subset hx)

/-- Existence and uniqueness of the concrete small negative D root. -/
theorem existsUnique_chapterVIDRoot :
    ∃! x : ℝ, x ∈ Set.Icc (-27 / 1000) (-26 / 1000) ∧ chapterVIDPolynomial x = 0 := by
  have hinterval :
      (0 : ℝ) ∈ Set.Icc
        (chapterVIDPolynomial (-26 / 1000)) (chapterVIDPolynomial (-27 / 1000)) :=
    ⟨chapterVIDPolynomial_right_neg.le, chapterVIDPolynomial_left_pos.le⟩
  obtain ⟨x, hx, hroot⟩ :=
    intermediate_value_Icc' (show (-27 / 1000 : ℝ) ≤ -26 / 1000 by norm_num)
      continuous_chapterVIDPolynomial.continuousOn hinterval
  refine ⟨x, ⟨hx, hroot⟩, ?_⟩
  intro y hy
  exact (chapterVIDPolynomial_strictAntiOn.injOn hx hy.1 (hroot.trans hy.2.symm)).symm

/-- The rigorously isolated real coordinate of Poincaré's point D in the concrete instance. -/
noncomputable def chapterVIDRoot : ℝ :=
  Classical.choose existsUnique_chapterVIDRoot

theorem chapterVIDRoot_mem :
    chapterVIDRoot ∈ Set.Icc (-27 / 1000) (-26 / 1000) :=
  (Classical.choose_spec existsUnique_chapterVIDRoot).1.1

theorem chapterVIDRoot_isRoot : chapterVIDPolynomial chapterVIDRoot = 0 :=
  (Classical.choose_spec existsUnique_chapterVIDRoot).1.2

theorem chapterVIDRoot_deriv_neg : deriv chapterVIDPolynomial chapterVIDRoot < 0 :=
  chapterVIDPolynomial_deriv_neg chapterVIDRoot_mem

theorem chapterVIDRoot_deriv_ne_zero : deriv chapterVIDPolynomial chapterVIDRoot ≠ 0 :=
  chapterVIDRoot_deriv_neg.ne

theorem chapterVIDRoot_unique
    {x : ℝ} (hx : x ∈ Set.Icc (-27 / 1000) (-26 / 1000))
    (hroot : chapterVIDPolynomial x = 0) :
    x = chapterVIDRoot :=
  (Classical.choose_spec existsUnique_chapterVIDRoot).2 x ⟨hx, hroot⟩

/-- The cleared cubic is exactly Poincaré's equation (7) for the chosen parameters. -/
theorem chapterVIDPolynomial_eq_secondKindSeven (x : ℝ) :
    chapterVIDPolynomial x = 250000 *
      chapterVISecondKindPolynomialSeven (-1) 3 (1 / 100) x := by
  unfold chapterVIDPolynomial chapterVISecondKindPolynomialSeven
  norm_num
  ring

theorem chapterVIDRoot_secondKindSeven :
    chapterVISecondKindPolynomialSeven (-1) 3 (1 / 100) chapterVIDRoot = 0 := by
  have h := chapterVIDPolynomial_eq_secondKindSeven chapterVIDRoot
  rw [chapterVIDRoot_isRoot] at h
  exact (mul_eq_zero.mp h.symm).resolve_left (by norm_num)

/-- The exact half-angle eccentricity and complementary factor for `τ = 1/100`. -/
def chapterVIDEccentricity : ℂ := 200 / 10001

def chapterVIDComplement : ℂ := 9999 / 10001

/-- The two anomaly coordinates of the concrete point D.  The second coordinate is equation
(3), solved for `y`, with `β = 2`. -/
noncomputable def chapterVIDX : ℂ := chapterVIDRoot

noncomputable def chapterVIDY : ℂ :=
  (chapterVIDX - 1 / 100) ^ 2 / (2 * (1 + (1 / 100 : ℂ) ^ 2) * chapterVIDX)

theorem chapterVIDRoot_lt_zero : chapterVIDRoot < 0 := by
  nlinarith [chapterVIDRoot_mem.2]

theorem chapterVIDX_ne_zero : chapterVIDX ≠ 0 := by
  unfold chapterVIDX
  exact Complex.ofReal_ne_zero.mpr chapterVIDRoot_lt_zero.ne

theorem chapterVIDX_sub_tau_ne_zero : chapterVIDX - 1 / 100 ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  norm_num [chapterVIDX] at hre
  nlinarith [chapterVIDRoot_lt_zero]

theorem chapterVID_one_sub_tau_mul_x_ne_zero :
    1 - (1 / 100 : ℂ) * chapterVIDX ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  norm_num [chapterVIDX] at hre
  nlinarith [chapterVIDRoot_lt_zero]

theorem chapterVIDY_ne_zero : chapterVIDY ≠ 0 := by
  unfold chapterVIDY
  exact div_ne_zero (pow_ne_zero _ chapterVIDX_sub_tau_ne_zero)
    (mul_ne_zero (mul_ne_zero (by norm_num) (by norm_num)) chapterVIDX_ne_zero)

theorem chapterVID_firstKeplerCritical :
    chapterVIKeplerExponentialDerivative chapterVIDEccentricity chapterVIDX ≠ 0 := by
  rw [chapterVIKeplerExponentialDerivative_ne_zero_iff
    chapterVIDEccentricity chapterVIDX_ne_zero]
  intro hzero
  have halgebraic :
      100 * chapterVIDX ^ 2 - 10001 * chapterVIDX + 100 = 0 := by
    field_simp [chapterVIDX_ne_zero] at hzero
    norm_num [chapterVIDEccentricity] at hzero
    linear_combination (-10001 / 2) * hzero
  have hreal :
      100 * chapterVIDRoot ^ 2 - 10001 * chapterVIDRoot + 100 = 0 := by
    change 100 * (chapterVIDRoot : ℂ) ^ 2 -
      10001 * (chapterVIDRoot : ℂ) + 100 = 0 at halgebraic
    rw [← Complex.ofReal_pow] at halgebraic
    have hre := congrArg Complex.re halgebraic
    have hpow : ((chapterVIDRoot : ℂ) ^ 2).re = chapterVIDRoot ^ 2 := by
      rw [← Complex.ofReal_pow]
      exact Complex.ofReal_re _
    norm_num [hpow] at hre ⊢
    exact hre
  nlinarith [sq_nonneg chapterVIDRoot, chapterVIDRoot_lt_zero]

theorem chapterVID_secondKeplerCritical :
    chapterVIKeplerExponentialDerivative 0 chapterVIDY ≠ 0 := by
  unfold chapterVIKeplerExponentialDerivative
  norm_num

theorem chapterVID_halfAngle_sine :
    (1 + (1 / 100 : ℂ) ^ 2) * chapterVIDEccentricity = 2 * (1 / 100 : ℂ) := by
  norm_num [chapterVIDEccentricity]

theorem chapterVID_halfAngle_cosine :
    (1 + (1 / 100 : ℂ) ^ 2) * chapterVIDComplement =
      1 - (1 / 100 : ℂ) ^ 2 := by
  norm_num [chapterVIDComplement]

/-- Point D lies exactly on Poincaré's first collision curve (3). -/
theorem chapterVID_collisionEquationThree :
    chapterVIPlanarCollisionEquationThree chapterVIDEccentricity chapterVIDComplement
      2 chapterVIDX chapterVIDY = 0 := by
  have h := chapterVI_planarCollisionEquationThree_halfAngle
    (1 / 100 : ℂ) chapterVIDEccentricity chapterVIDComplement 2 chapterVIDX chapterVIDY
    chapterVID_halfAngle_sine chapterVID_halfAngle_cosine
  have hcurve :
      (chapterVIDX - 1 / 100) ^ 2 -
        2 * (1 + (1 / 100 : ℂ) ^ 2) * chapterVIDX * chapterVIDY = 0 := by
    unfold chapterVIDY
    (field_simp [chapterVIDX_ne_zero]; ring)
  rw [hcurve, mul_zero] at h
  exact (mul_eq_zero.mp h).resolve_left (by norm_num)

/-- Consequently, the literal source factor `H = ξ-βη` vanishes at D. -/
theorem chapterVID_collisionFactorPlus :
    chapterVIPlanarCollisionFactorPlus chapterVIDEccentricity chapterVIDComplement
      0 1 2 chapterVIDX chapterVIDY = 0 := by
  have hclear := chapterVI_planarCollisionFactorPlus_eq_cleared
    chapterVIDEccentricity chapterVIDComplement 0 1 2
    chapterVIDX_ne_zero chapterVIDY_ne_zero
  rw [chapterVI_planarCollisionEquationThreeGeneral_secondCircular] at hclear
  rw [chapterVID_collisionEquationThree, mul_zero] at hclear
  exact (mul_eq_zero.mp hclear).resolve_left
    (mul_ne_zero (mul_ne_zero (by norm_num) chapterVIDX_ne_zero) chapterVIDY_ne_zero)

/-- The companion source factor `H₀` does not vanish at the same real D point. -/
theorem chapterVID_collisionFactorMinus_ne_zero :
    chapterVIPlanarCollisionFactorMinus chapterVIDEccentricity chapterVIDComplement
      0 1 2 chapterVIDX chapterVIDY ≠ 0 := by
  intro hzero
  have hclear := chapterVI_planarCollisionFactorMinus_eq_cleared
    chapterVIDEccentricity chapterVIDComplement 0 1 2
    chapterVIDX_ne_zero chapterVIDY_ne_zero
  rw [hzero, mul_zero] at hclear
  simp only [chapterVIPlanarCollisionEquationFourGeneral,
    chapterVIPlanarDistanceFactorMinus] at hclear
  have hcomplex :
      20000 - 4000400 * chapterVIDX - 600080006 * chapterVIDX ^ 2 -
        4000400 * chapterVIDX ^ 3 + 20000 * chapterVIDX ^ 4 = 0 := by
    unfold chapterVIDY at hclear
    field_simp [chapterVIDX_ne_zero] at hclear
    norm_num [chapterVIDEccentricity, chapterVIDComplement] at hclear
    ring_nf at hclear
    simpa only [mul_comm] using hclear.symm
  have hrealExpanded :
      20000 - 4000400 * chapterVIDRoot - 600080006 * chapterVIDRoot ^ 2 -
        4000400 * chapterVIDRoot ^ 3 + 20000 * chapterVIDRoot ^ 4 = 0 := by
    change 20000 - 4000400 * (chapterVIDRoot : ℂ) -
      600080006 * (chapterVIDRoot : ℂ) ^ 2 -
      4000400 * (chapterVIDRoot : ℂ) ^ 3 +
      20000 * (chapterVIDRoot : ℂ) ^ 4 = 0 at hcomplex
    rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_pow] at hcomplex
    have hre := congrArg Complex.re hcomplex
    have hpow (n : ℕ) : ((chapterVIDRoot : ℂ) ^ n).re = chapterVIDRoot ^ n := by
      rw [← Complex.ofReal_pow]
      exact Complex.ofReal_re _
    norm_num [hpow] at hre ⊢
    exact hre
  have hreal :
      (chapterVIDRoot + 100) * (100 * chapterVIDRoot + 1) *
        (100 * chapterVIDRoot ^ 2 - 30003 * chapterVIDRoot + 100) = 0 := by
    nlinarith [hrealExpanded]
  rcases mul_eq_zero.mp hreal with hleft | hquadratic
  · rcases mul_eq_zero.mp hleft with hfar | hnear
    · nlinarith [chapterVIDRoot_mem.1]
    · nlinarith [chapterVIDRoot_mem.1, chapterVIDRoot_mem.2]
  · nlinarith [sq_nonneg chapterVIDRoot, chapterVIDRoot_lt_zero]

end
end PoincareChapterVI
