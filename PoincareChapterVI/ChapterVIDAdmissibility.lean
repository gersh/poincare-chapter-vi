/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import Mathlib.Analysis.Complex.ExponentialBounds
import PoincareChapterVI.ChapterVIDCandidate
import PoincareChapterVI.ChapterVIWindingObstruction

/-!
# The decisive real inequalities in Poincaré's admissibility argument for D

Section 97 follows the real collision branch

`y=(x-τ)²/(β(1+τ²)x)`

from D toward B'.  For the concrete values `τ=1/100`, `β=2`, `a=-1`, and `c=3`, Poincaré's
decisive comparison is that the parameter still has modulus below one when the branch crosses
`x=-1`, whereas it has modulus above one at `B'`, whose abscissa is `x=-100`.  Hence the level
`|z|=1` is reached with `|x|>1` on this branch.

This file proves the two endpoint inequalities exactly.  The intervening monotonicity and branch
continuation are kept separate so that their calculus proof cannot be mistaken for a finite
certificate.
-/

noncomputable section

open Real

namespace PoincareChapterVI

/-- Poincaré's collision curve (3), specialized to the concrete D parameters. -/
def chapterVIDCurveThreeY (x : ℝ) : ℝ :=
  (x - 1 / 100) ^ 2 / (2 * (1 + (1 / 100 : ℝ) ^ 2) * x)

/-- The modulus of Poincaré's parameter `z` along the same real negative branch. -/
def chapterVIDCurveThreeParameterModulus (x : ℝ) : ℝ :=
  |chapterVIDCurveThreeY x| ^ 3 / |x| *
    Real.exp ((-100 / 10001 : ℝ) * (x⁻¹ - x))

theorem chapterVIDCurveThreeY_neg_one :
    chapterVIDCurveThreeY (-1) = -(10201 / 20002) := by
  norm_num [chapterVIDCurveThreeY]

/-- Poincaré's p. 310 comparison: at `x=-1`, the modulus is still below one. -/
theorem chapterVIDCurveThreeParameterModulus_neg_one_lt_one :
    chapterVIDCurveThreeParameterModulus (-1) < 1 := by
  rw [chapterVIDCurveThreeParameterModulus, chapterVIDCurveThreeY_neg_one]
  norm_num

theorem chapterVIDCurveThreeY_neg_hundred :
    chapterVIDCurveThreeY (-100) = -(10001 / 200) := by
  norm_num [chapterVIDCurveThreeY]

theorem chapterVIDCurveThreeParameterModulus_neg_hundred_eq :
    chapterVIDCurveThreeParameterModulus (-100) =
      (10001 / 200 : ℝ) ^ 3 / 100 * Real.exp (-9999 / 10001) := by
  rw [chapterVIDCurveThreeParameterModulus, chapterVIDCurveThreeY_neg_hundred]
  norm_num

/-- At the crossing B', `x=-100`, the same branch has already passed above `|z|=1`. -/
theorem one_lt_chapterVIDCurveThreeParameterModulus_neg_hundred :
    1 < chapterVIDCurveThreeParameterModulus (-100) := by
  rw [chapterVIDCurveThreeParameterModulus_neg_hundred_eq]
  have hexponent : (-1 : ℝ) < -9999 / 10001 := by norm_num
  have hexp : Real.exp (-1) < Real.exp (-9999 / 10001) :=
    Real.exp_lt_exp.mpr hexponent
  have hlower := Real.exp_neg_one_gt_d9
  have hpositive : 0 < Real.exp (-9999 / 10001) := Real.exp_pos _
  nlinarith

/-- The two rational abscissas used above really are the negative intersections B and B' of
Poincaré's collision curves (3) and (4). -/
theorem chapterVID_curveThree_curveFour_negative_intersections (x : ℝ) :
    (x - 1 / 100) ^ 2 * (1 - (1 / 100) * x) ^ 2 -
        4 * (1 + (1 / 100 : ℝ) ^ 2) ^ 2 * x ^ 2 =
      (x + 100) * (100 * x + 1) *
        (100 * x ^ 2 - 30003 * x + 100) / 100000000 := by
  ring

/-! ## Monotonicity from D toward B' -/

/-- The logarithmic derivative of the branch modulus, written in the factored form whose
numerator is exactly D's cubic. -/
def chapterVIDCurveThreeLogDerivative (x : ℝ) : ℝ :=
  4 * chapterVIDPolynomial x / (10001 * x ^ 2 * (100 * x - 1))

theorem chapterVIDCurveThreeLogDerivative_eq (x : ℝ)
    (hx : x ≠ 0) (hxtau : x ≠ 1 / 100) :
    chapterVIDCurveThreeLogDerivative x =
      3 * (2 / (x - 1 / 100) - 1 / x) - 1 / x +
        (-100 / 10001) * (-1 / x ^ 2 - 1) := by
  have hlinear : 100 * x - 1 ≠ 0 := by
    intro hzero
    apply hxtau
    linarith
  have hlinear' : -1 + x * 100 ≠ 0 := by
    simpa [mul_comm, sub_eq_add_neg, add_comm] using hlinear
  have hlinear'' : x * 100 - 1 ≠ 0 := by
    simpa [mul_comm] using hlinear
  unfold chapterVIDCurveThreeLogDerivative chapterVIDPolynomial
  field_simp [hx, hxtau, hlinear, hlinear', hlinear'']; ring

/-- The D cubic is strictly decreasing throughout the entire interval from B' to D. -/
theorem chapterVIDPolynomial_deriv_neg_BPrime_to_D
    {x : ℝ} (hx : x ∈ Set.Icc (-100) (-26 / 1000)) :
    deriv chapterVIDPolynomial x < 0 := by
  rcases hx with ⟨hxleft, hxright⟩
  rw [(hasDerivAt_chapterVIDPolynomial x).deriv]
  by_cases hleft : x ≤ -1
  · have hsquare : x ^ 2 ≤ -100 * x := by
      have hxnonpos : x ≤ 0 := hleft.trans (by norm_num)
      nlinarith [mul_nonpos_of_nonneg_of_nonpos (by linarith : 0 ≤ x + 100) hxnonpos]
    nlinarith [hxleft, hxright]
  · have hxgt : -1 < x := lt_of_not_ge hleft
    have hsquare : x ^ 2 ≤ 1 := by
      nlinarith [mul_nonneg (by linarith : 0 ≤ 1 - x) (by linarith : 0 ≤ 1 + x)]
    nlinarith [hxright]

theorem chapterVIDPolynomial_strictAntiOn_BPrime_to_D :
    StrictAntiOn chapterVIDPolynomial (Set.Icc (-100) (-26 / 1000)) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
  · exact continuous_chapterVIDPolynomial.continuousOn
  · intro x hx
    exact chapterVIDPolynomial_deriv_neg_BPrime_to_D (interior_subset hx)

/-- To the left of D and before B', the cubic numerator is positive. -/
theorem chapterVIDPolynomial_pos_left_of_D
    {x : ℝ} (hxleft : -100 ≤ x) (hxD : x < chapterVIDRoot) :
    0 < chapterVIDPolynomial x := by
  have hxright : x ≤ -26 / 1000 :=
    hxD.le.trans chapterVIDRoot_mem.2
  have hxmem : x ∈ Set.Icc (-100) (-26 / 1000) := ⟨hxleft, hxright⟩
  have hDmem : chapterVIDRoot ∈ Set.Icc (-100) (-26 / 1000) := by
    constructor <;> nlinarith [chapterVIDRoot_mem.1, chapterVIDRoot_mem.2]
  have hstrict := chapterVIDPolynomial_strictAntiOn_BPrime_to_D hxmem hDmem hxD
  rw [chapterVIDRoot_isRoot] at hstrict
  exact hstrict

/-- Therefore the logarithmic derivative is negative along the open branch from D to B'. -/
theorem chapterVIDCurveThreeLogDerivative_neg
    {x : ℝ} (hxleft : -100 ≤ x) (hxD : x < chapterVIDRoot) :
    chapterVIDCurveThreeLogDerivative x < 0 := by
  have hxneg : x < 0 := hxD.trans chapterVIDRoot_lt_zero
  have hp := chapterVIDPolynomial_pos_left_of_D hxleft hxD
  unfold chapterVIDCurveThreeLogDerivative
  have hx2 : 0 < x ^ 2 := sq_pos_of_ne_zero (ne_of_lt hxneg)
  have hlinear : 100 * x - 1 < 0 := by nlinarith
  have hdenom : 10001 * x ^ 2 * (100 * x - 1) < 0 :=
    mul_neg_of_pos_of_neg (mul_pos (by norm_num) hx2) hlinear
  exact div_neg_of_pos_of_neg (mul_pos (by norm_num) hp) hdenom

/-! ## Calculus of the branch modulus -/

theorem chapterVIDCurveThreeY_neg {x : ℝ} (hx : x < 0) :
    chapterVIDCurveThreeY x < 0 := by
  have hnumerator : 0 < (x - 1 / 100) ^ 2 := by
    exact sq_pos_of_ne_zero (by nlinarith)
  have hdenominator : 2 * (1 + (1 / 100 : ℝ) ^ 2) * x < 0 := by
    exact mul_neg_of_pos_of_neg (by norm_num) hx
  exact div_neg_of_pos_of_neg hnumerator hdenominator

theorem hasDerivAt_chapterVIDCurveThreeY_raw
    {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt chapterVIDCurveThreeY
      ((2 * (x - 1 / 100) * (2 * (1 + (1 / 100 : ℝ) ^ 2) * x) -
          (x - 1 / 100) ^ 2 * (2 * (1 + (1 / 100 : ℝ) ^ 2))) /
        (2 * (1 + (1 / 100 : ℝ) ^ 2) * x) ^ 2) x := by
  let denominator : ℝ := 2 * (1 + (1 / 100 : ℝ) ^ 2)
  have hdenominator : denominator ≠ 0 := by
    dsimp [denominator]
    norm_num
  have hquotient :=
    (((hasDerivAt_id x).sub_const (1 / 100)).pow 2).div
      ((hasDerivAt_id x).const_mul denominator)
      (mul_ne_zero hdenominator hx)
  change HasDerivAt
    ((fun x : ℝ ↦ x - 1 / 100) ^ 2 /
      fun y : ℝ ↦ 2 * (1 + (1 / 100 : ℝ) ^ 2) * y) _ x
  simpa [denominator, id_eq] using hquotient

theorem hasDerivAt_chapterVIDCurveThreeY
    {x : ℝ} (hx : x ≠ 0) (hxtau : x ≠ 1 / 100) :
    HasDerivAt chapterVIDCurveThreeY
      (chapterVIDCurveThreeY x * (2 / (x - 1 / 100) - 1 / x)) x := by
  have hlinear : -1 + x * 100 ≠ 0 := by
    intro hzero
    apply hxtau
    linarith
  have hlinear' : x * 100 - 1 ≠ 0 := by
    simpa [sub_eq_add_neg, add_comm] using hlinear
  convert hasDerivAt_chapterVIDCurveThreeY_raw hx using 1
  unfold chapterVIDCurveThreeY
  field_simp [hx, hxtau, hlinear, hlinear']

/-- The same modulus formula with the signs on the negative real branch made explicit.  This
version is convenient for differentiation; the next theorem identifies it with Poincaré's
absolute-value formula. -/
def chapterVIDCurveThreeSmoothParameter (x : ℝ) : ℝ :=
  (-chapterVIDCurveThreeY x) ^ 3 / (-x) *
    Real.exp ((-100 / 10001 : ℝ) * (x⁻¹ - x))

theorem chapterVIDCurveThreeSmoothParameter_eq_modulus
    {x : ℝ} (hx : x < 0) :
    chapterVIDCurveThreeSmoothParameter x =
      chapterVIDCurveThreeParameterModulus x := by
  have hy := chapterVIDCurveThreeY_neg hx
  rw [chapterVIDCurveThreeSmoothParameter, chapterVIDCurveThreeParameterModulus,
    abs_of_neg hx, abs_of_neg hy]

theorem deriv_chapterVIDCurveThreeSmoothParameter
    {x : ℝ} (hx : x < 0) :
    deriv chapterVIDCurveThreeSmoothParameter x =
      chapterVIDCurveThreeSmoothParameter x * chapterVIDCurveThreeLogDerivative x := by
  have hx0 : x ≠ 0 := ne_of_lt hx
  have hxtau : x ≠ 1 / 100 := by nlinarith
  let yLogDerivative : ℝ := 2 / (x - 1 / 100) - 1 / x
  let exponentDerivative : ℝ :=
    (-100 / 10001 : ℝ) * (-1 / x ^ 2 - 1)
  have hy : HasDerivAt chapterVIDCurveThreeY
      (chapterVIDCurveThreeY x * yLogDerivative) x := by
    simpa [yLogDerivative] using hasDerivAt_chapterVIDCurveThreeY hx0 hxtau
  have hminusY : HasDerivAt (fun t ↦ -chapterVIDCurveThreeY t)
      (-(chapterVIDCurveThreeY x * yLogDerivative)) x := hy.neg
  have hquotient := (hminusY.pow 3).div (hasDerivAt_id x).neg (neg_ne_zero.mpr hx0)
  have hinvSub := (hasDerivAt_inv hx0).sub (hasDerivAt_id x)
  have hinvSub' := hinvSub.congr_deriv (show (-(x ^ 2)⁻¹ - 1 : ℝ) =
      -1 / x ^ 2 - 1 by simp [div_eq_mul_inv])
  have hexponent : HasDerivAt
      (fun t : ℝ ↦ (-100 / 10001 : ℝ) * (t⁻¹ - t)) exponentDerivative x := by
    simpa [exponentDerivative] using hinvSub'.const_mul (-100 / 10001 : ℝ)
  have hexponential := hexponent.exp
  have hproduct := hquotient.mul hexponential
  have hfun : chapterVIDCurveThreeSmoothParameter =
      ((fun t : ℝ ↦ -chapterVIDCurveThreeY t) ^ 3 / -(id : ℝ → ℝ)) *
        (fun t : ℝ ↦ Real.exp ((-100 / 10001 : ℝ) * (t⁻¹ - t))) := by
    funext t
    simp [chapterVIDCurveThreeSmoothParameter, id_eq]
  rw [hfun, hproduct.deriv, chapterVIDCurveThreeLogDerivative_eq x hx0 hxtau]
  simp only [Pi.mul_apply, Pi.div_apply, Pi.pow_apply, Pi.neg_apply, id_eq]
  dsimp [yLogDerivative, exponentDerivative]
  field_simp [hx0, hxtau]

theorem chapterVIDCurveThreeSmoothParameter_pos
    {x : ℝ} (hx : x < 0) : 0 < chapterVIDCurveThreeSmoothParameter x := by
  have hy := chapterVIDCurveThreeY_neg hx
  unfold chapterVIDCurveThreeSmoothParameter
  exact mul_pos (div_pos (pow_pos (neg_pos.mpr hy) _) (neg_pos.mpr hx)) (Real.exp_pos _)

theorem continuousOn_chapterVIDCurveThreeSmoothParameter_BPrime_to_negOne :
    ContinuousOn chapterVIDCurveThreeSmoothParameter (Set.Icc (-100) (-1)) := by
  apply continuousOn_of_forall_continuousAt
  intro x hx
  have hxneg : x < 0 := lt_of_le_of_lt hx.2 (by norm_num)
  have hx0 : x ≠ 0 := ne_of_lt hxneg
  have hdenominator : 2 * (1 + (1 / 100 : ℝ) ^ 2) * x ≠ 0 := by
    exact mul_ne_zero (by norm_num) hx0
  unfold chapterVIDCurveThreeSmoothParameter chapterVIDCurveThreeY
  fun_prop (disch := simp [hx0])

/-- The branch modulus strictly decreases as the real abscissa runs from B' toward D. -/
theorem chapterVIDCurveThreeSmoothParameter_strictAntiOn_BPrime_to_negOne :
    StrictAntiOn chapterVIDCurveThreeSmoothParameter (Set.Icc (-100) (-1)) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
    continuousOn_chapterVIDCurveThreeSmoothParameter_BPrime_to_negOne
  intro x hx
  have hxmem : x ∈ Set.Icc (-100) (-1) := interior_subset hx
  have hxneg : x < 0 := lt_of_le_of_lt hxmem.2 (by norm_num)
  rw [deriv_chapterVIDCurveThreeSmoothParameter hxneg]
  exact mul_neg_of_pos_of_neg
    (chapterVIDCurveThreeSmoothParameter_pos hxneg)
    (chapterVIDCurveThreeLogDerivative_neg hxmem.1
      (lt_of_le_of_lt hxmem.2 (by
        have := chapterVIDRoot_mem.1
        norm_num at this ⊢
        linarith)))

theorem chapterVIDCurveThreeSmoothParameter_neg_hundred_gt_one :
    1 < chapterVIDCurveThreeSmoothParameter (-100) := by
  rw [chapterVIDCurveThreeSmoothParameter_eq_modulus (by norm_num)]
  exact one_lt_chapterVIDCurveThreeParameterModulus_neg_hundred

theorem chapterVIDCurveThreeSmoothParameter_neg_one_lt_one :
    chapterVIDCurveThreeSmoothParameter (-1) < 1 := by
  rw [chapterVIDCurveThreeSmoothParameter_eq_modulus (by norm_num)]
  exact chapterVIDCurveThreeParameterModulus_neg_one_lt_one

/-! ## The two continuations through B -/

/-- Poincaré's collision curve (4), specialized to the same parameters. -/
def chapterVIDCurveFourY (x : ℝ) : ℝ :=
  2 * (1 + (1 / 100 : ℝ) ^ 2) * x / (1 - (1 / 100) * x) ^ 2

def chapterVIDCurveFourParameterModulus (x : ℝ) : ℝ :=
  |chapterVIDCurveFourY x| ^ 3 / |x| *
    Real.exp ((-100 / 10001 : ℝ) * (x⁻¹ - x))

/-- Curves (3) and (4) meet at Poincaré's point B, `x=-τ`. -/
theorem chapterVIDCurveThree_curveFour_parameter_eq_at_B :
    chapterVIDCurveThreeParameterModulus (-1 / 100) =
      chapterVIDCurveFourParameterModulus (-1 / 100) := by
  norm_num [chapterVIDCurveThreeParameterModulus, chapterVIDCurveFourParameterModulus,
    chapterVIDCurveThreeY, chapterVIDCurveFourY]

theorem chapterVIDCurveThreeParameterModulus_B_lt_one :
    chapterVIDCurveThreeParameterModulus (-1 / 100) < 1 := by
  rw [chapterVIDCurveThreeParameterModulus]
  have hexponent : (9999 / 10001 : ℝ) < 1 := by norm_num
  have hexp : Real.exp (9999 / 10001) < Real.exp 1 :=
    Real.exp_lt_exp.mpr hexponent
  have hupper := Real.exp_one_lt_three
  norm_num [chapterVIDCurveThreeY]
  nlinarith [Real.exp_pos (9999 / 10001)]

theorem one_lt_chapterVIDCurveThreeParameterModulus_near_P :
    1 < chapterVIDCurveThreeParameterModulus (-1 / 1000) := by
  rw [chapterVIDCurveThreeParameterModulus]
  have hexponent : (999999 / 100010 : ℝ) > 3 := by norm_num
  have hexp : Real.exp 3 < Real.exp (999999 / 100010) :=
    Real.exp_lt_exp.mpr hexponent
  have hone := Real.exp_one_gt_two
  have hthree : 8 < Real.exp 3 := by
    rw [show (3 : ℝ) = 1 + 1 + 1 by norm_num, Real.exp_add, Real.exp_add]
    nlinarith [Real.exp_pos 1]
  norm_num [chapterVIDCurveThreeY]
  nlinarith [Real.exp_pos (999999 / 100010)]

theorem chapterVIDCurveFourParameterModulus_B_lt_one :
    chapterVIDCurveFourParameterModulus (-1 / 100) < 1 := by
  rw [← chapterVIDCurveThree_curveFour_parameter_eq_at_B]
  exact chapterVIDCurveThreeParameterModulus_B_lt_one

theorem one_lt_chapterVIDCurveFourParameterModulus_neg_one :
    1 < chapterVIDCurveFourParameterModulus (-1) := by
  norm_num [chapterVIDCurveFourParameterModulus, chapterVIDCurveFourY]

theorem continuousOn_chapterVIDCurveThreeParameterModulus_B_to_P :
    ContinuousOn chapterVIDCurveThreeParameterModulus
      (Set.Icc (-1 / 100) (-1 / 1000)) := by
  apply continuousOn_of_forall_continuousAt
  intro x hx
  have hxneg : x < 0 := lt_of_le_of_lt hx.2 (by norm_num)
  have hx0 : x ≠ 0 := ne_of_lt hxneg
  have hdenominator : 2 * (1 + (1 / 100 : ℝ) ^ 2) * x ≠ 0 := by
    exact mul_ne_zero (by norm_num) hx0
  unfold chapterVIDCurveThreeParameterModulus chapterVIDCurveThreeY
  fun_prop (disch := simp [hx0])

theorem continuousOn_chapterVIDCurveFourParameterModulus_negOne_to_B :
    ContinuousOn chapterVIDCurveFourParameterModulus
      (Set.Icc (-1) (-1 / 100)) := by
  apply continuousOn_of_forall_continuousAt
  intro x hx
  have hxneg : x < 0 := lt_of_le_of_lt hx.2 (by norm_num)
  have hx0 : x ≠ 0 := ne_of_lt hxneg
  have hlinear : 1 - (1 / 100 : ℝ) * x ≠ 0 := by nlinarith
  have hlinearPow : (1 - (1 / 100 : ℝ) * x) ^ 2 ≠ 0 :=
    pow_ne_zero _ hlinear
  unfold chapterVIDCurveFourParameterModulus chapterVIDCurveFourY
  fun_prop (disch := simp [hx0])

/-- The BP continuation reaches `|z|=1` while `-τ<x<0`, hence inside the unit circle. -/
theorem exists_chapterVIDCurveThree_unit_parameter_inside :
    ∃ x : ℝ, x ∈ Set.Ioo (-1 / 100) (-1 / 1000) ∧
      chapterVIDCurveThreeParameterModulus x = 1 := by
  have hone : (1 : ℝ) ∈ Set.Icc
      (chapterVIDCurveThreeParameterModulus (-1 / 100))
      (chapterVIDCurveThreeParameterModulus (-1 / 1000)) :=
    ⟨chapterVIDCurveThreeParameterModulus_B_lt_one.le,
      one_lt_chapterVIDCurveThreeParameterModulus_near_P.le⟩
  rcases intermediate_value_Icc (show (-1 / 100 : ℝ) ≤ -1 / 1000 by norm_num)
      continuousOn_chapterVIDCurveThreeParameterModulus_B_to_P hone with
    ⟨x, hx, hxeq⟩
  have hxleft : -1 / 100 < x := by
    refine lt_of_le_of_ne hx.1 ?_
    intro h
    subst x
    linarith [chapterVIDCurveThreeParameterModulus_B_lt_one]
  have hxright : x < -1 / 1000 := by
    refine lt_of_le_of_ne hx.2 ?_
    intro h
    subst x
    linarith [one_lt_chapterVIDCurveThreeParameterModulus_near_P]
  exact ⟨x, ⟨hxleft, hxright⟩, hxeq⟩

/-- The BD' continuation reaches `|z|=1` before `x=-1`, so it is inside as well. -/
theorem exists_chapterVIDCurveFour_unit_parameter_inside :
    ∃ x : ℝ, x ∈ Set.Ioo (-1) (-1 / 100) ∧
      chapterVIDCurveFourParameterModulus x = 1 := by
  have hone : (1 : ℝ) ∈ Set.Icc
      (chapterVIDCurveFourParameterModulus (-1 / 100))
      (chapterVIDCurveFourParameterModulus (-1)) :=
    ⟨chapterVIDCurveFourParameterModulus_B_lt_one.le,
      one_lt_chapterVIDCurveFourParameterModulus_neg_one.le⟩
  rcases intermediate_value_Icc' (show (-1 : ℝ) ≤ -1 / 100 by norm_num)
      continuousOn_chapterVIDCurveFourParameterModulus_negOne_to_B hone with
    ⟨x, hx, hxeq⟩
  have hxleft : -1 < x := by
    refine lt_of_le_of_ne hx.1 ?_
    intro h
    subst x
    linarith [one_lt_chapterVIDCurveFourParameterModulus_neg_one]
  have hxright : x < -1 / 100 := by
    refine lt_of_le_of_ne hx.2 ?_
    intro h
    subst x
    linarith [chapterVIDCurveFourParameterModulus_B_lt_one]
  exact ⟨x, ⟨hxleft, hxright⟩, hxeq⟩

/-- Both descendants of the D→B branch have final abscissa of modulus below one. -/
theorem chapterVID_two_unit_parameter_abscissas_inside :
    ∃ x₁ x₂ : ℝ,
      chapterVIDCurveThreeParameterModulus x₁ = 1 ∧ |x₁| < 1 ∧
      chapterVIDCurveFourParameterModulus x₂ = 1 ∧ |x₂| < 1 := by
  rcases exists_chapterVIDCurveThree_unit_parameter_inside with ⟨x₁, hx₁, h₁⟩
  rcases exists_chapterVIDCurveFour_unit_parameter_inside with ⟨x₂, hx₂, h₂⟩
  refine ⟨x₁, x₂, h₁, ?_, h₂, ?_⟩
  · rw [abs_of_neg (hx₁.2.trans (by norm_num))]
    linarith [hx₁.1]
  · rw [abs_of_neg (hx₂.2.trans (by norm_num))]
    linarith [hx₂.1]

/-- The point where the continued D branch first returns to `|z|=1` exists, is unique on the
segment from B' to `x=-1`, and has `|x|>1`, exactly as Poincaré asserts in §97. -/
theorem existsUnique_chapterVIDCurveThree_unit_parameter_outside :
    ∃! x : ℝ, x ∈ Set.Ioo (-100) (-1) ∧
      chapterVIDCurveThreeParameterModulus x = 1 := by
  have hone : (1 : ℝ) ∈ Set.Icc
      (chapterVIDCurveThreeSmoothParameter (-1))
      (chapterVIDCurveThreeSmoothParameter (-100)) :=
    ⟨chapterVIDCurveThreeSmoothParameter_neg_one_lt_one.le,
      chapterVIDCurveThreeSmoothParameter_neg_hundred_gt_one.le⟩
  rcases intermediate_value_Icc' (show (-100 : ℝ) ≤ -1 by norm_num)
      continuousOn_chapterVIDCurveThreeSmoothParameter_BPrime_to_negOne hone with
    ⟨x, hx, hxeq⟩
  have hxleft : -100 < x := by
    refine lt_of_le_of_ne hx.1 ?_
    intro hxeqleft
    subst x
    linarith [chapterVIDCurveThreeSmoothParameter_neg_hundred_gt_one]
  have hxright : x < -1 := by
    refine lt_of_le_of_ne hx.2 ?_
    intro hxeqright
    subst x
    linarith [chapterVIDCurveThreeSmoothParameter_neg_one_lt_one]
  refine ⟨x, ⟨⟨hxleft, hxright⟩, ?_⟩, ?_⟩
  · rw [← chapterVIDCurveThreeSmoothParameter_eq_modulus (hxright.trans (by norm_num))]
    exact hxeq
  · intro y hy
    apply chapterVIDCurveThreeSmoothParameter_strictAntiOn_BPrime_to_negOne.injOn
      ⟨hy.1.1.le, hy.1.2.le⟩ hx
    rw [chapterVIDCurveThreeSmoothParameter_eq_modulus
        (hy.1.2.trans (by norm_num)), hy.2, hxeq]

theorem chapterVIDCurveThree_unit_parameter_has_abscissa_norm_gt_one :
    ∃ x : ℝ, chapterVIDCurveThreeParameterModulus x = 1 ∧ 1 < |x| := by
  rcases existsUnique_chapterVIDCurveThree_unit_parameter_outside.exists with
    ⟨x, hx, hparameter⟩
  refine ⟨x, hparameter, ?_⟩
  rw [abs_of_neg (hx.2.trans (by norm_num))]
  simpa using neg_lt_neg hx.2

/-- The exact terminal configuration in Poincaré's figure 4: after D's right-hand branch reaches
B it has two descendants inside the unit circle, while D's left-hand descendant ends outside.
The interval bounds also record the order of the three real branches, so this statement does not
hide a numerical plot. -/
theorem chapterVID_admissibility_terminal_configuration :
    ∃ xBP xBDPrime xDBPrime : ℝ,
      (-1 / 100 < xBP ∧ xBP < 0) ∧
      (-1 < xBDPrime ∧ xBDPrime < -1 / 100) ∧
      (xDBPrime < -1) ∧
      chapterVIDCurveThreeParameterModulus xBP = 1 ∧
      chapterVIDCurveFourParameterModulus xBDPrime = 1 ∧
      chapterVIDCurveThreeParameterModulus xDBPrime = 1 ∧
      |xBP| < 1 ∧ |xBDPrime| < 1 ∧ 1 < |xDBPrime| := by
  rcases exists_chapterVIDCurveThree_unit_parameter_inside with ⟨xBP, hxBP, hBP⟩
  rcases exists_chapterVIDCurveFour_unit_parameter_inside with ⟨xBD, hxBD, hBD⟩
  rcases existsUnique_chapterVIDCurveThree_unit_parameter_outside.exists with
    ⟨xDB, hxDB, hDB⟩
  refine ⟨xBP, xBD, xDB,
    ⟨hxBP.1, hxBP.2.trans (by norm_num)⟩, hxBD,
    hxDB.2, hBP, hBD, hDB, ?_, ?_, ?_⟩
  · rw [abs_of_neg (hxBP.2.trans (by norm_num))]
    linarith [hxBP.1]
  · rw [abs_of_neg (hxBD.2.trans (by norm_num))]
    linarith [hxBD.1]
  · rw [abs_of_neg (hxDB.2.trans (by norm_num))]
    simpa using neg_lt_neg hxDB.2

end PoincareChapterVI
