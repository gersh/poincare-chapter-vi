/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
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
open scoped Topology unitInterval

namespace PoincareChapterVI

/-! ## The `x^(1/3)` contour coordinate -/

/-- Any cubic lift has norm below one exactly when its `x` coordinate does.  This is the precise
bridge from Poincaré's real figure in the `x`-plane to his integration contour in the
`x^(1/c)`-plane for `c=3`. -/
theorem chapterVI_norm_cubicLift_lt_one_iff
    {lift : ℂ} {x : ℝ} (hlift : lift ^ 3 = (x : ℂ)) :
    ‖lift‖ < 1 ↔ |x| < 1 := by
  have hnorm : ‖lift‖ ^ 3 = |x| := by
    rw [← norm_pow, hlift, Complex.norm_real, Real.norm_eq_abs]
  calc
    ‖lift‖ < 1 ↔ ‖lift‖ ^ 3 < 1 :=
      (pow_lt_one_iff_of_nonneg (norm_nonneg lift) (by norm_num)).symm
    _ ↔ |x| < 1 := by rw [hnorm]

theorem chapterVI_one_lt_norm_cubicLift_iff
    {lift : ℂ} {x : ℝ} (hlift : lift ^ 3 = (x : ℂ)) :
    1 < ‖lift‖ ↔ 1 < |x| := by
  have hnorm : ‖lift‖ ^ 3 = |x| := by
    rw [← norm_pow, hlift, Complex.norm_real, Real.norm_eq_abs]
  calc
    1 < ‖lift‖ ↔ 1 < ‖lift‖ ^ 3 :=
      (one_lt_pow_iff_of_nonneg (norm_nonneg lift) (by norm_num)).symm
    _ ↔ 1 < |x| := by rw [hnorm]

/-- A fixed cubic lift, used only to state a concrete source-facing corollary.  Sheet-sensitive
arguments retain the equation `lift^3=x` explicitly and do not rely on any principal-root cut. -/
noncomputable def chapterVIChosenCubicLift (x : ℂ) : ℂ :=
  Classical.choose (IsAlgClosed.exists_pow_nat_eq x (show 0 < 3 by norm_num))

@[simp]
theorem chapterVIChosenCubicLift_pow (x : ℂ) :
    chapterVIChosenCubicLift x ^ 3 = x :=
  Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq x (show 0 < 3 by norm_num))

/-- A continuous cubic-root branch on the negative real axis.  It differs from Poincaré's
argument-`π/3` choice by a fixed cube root of unity, which has no effect on inside/outside winding
data. -/
noncomputable def chapterVINegativeRealCubicLift (x : ℝ) : ℂ :=
  -(max (-x) 0 ^ ((3 : ℝ)⁻¹) : ℝ)

theorem continuous_chapterVINegativeRealCubicLift :
    Continuous chapterVINegativeRealCubicLift := by
  unfold chapterVINegativeRealCubicLift
  fun_prop (disch := norm_num)

@[simp]
theorem chapterVINegativeRealCubicLift_pow
    {x : ℝ} (hx : x ≤ 0) :
    chapterVINegativeRealCubicLift x ^ 3 = (x : ℂ) := by
  have hnonneg : 0 ≤ -x := neg_nonneg.mpr hx
  have hrpow : ((-x) ^ ((3 : ℝ)⁻¹)) ^ (3 : ℕ) = -x :=
    Real.rpow_inv_natCast_pow hnonneg (by norm_num)
  have hreal : (-((-x) ^ ((3 : ℝ)⁻¹))) ^ (3 : ℕ) = x := by
    calc
      (-((-x) ^ ((3 : ℝ)⁻¹))) ^ (3 : ℕ) =
          -(((-x) ^ ((3 : ℝ)⁻¹)) ^ (3 : ℕ)) := by ring
      _ = -(-x) := by rw [hrpow]
      _ = x := by ring
  unfold chapterVINegativeRealCubicLift
  rw [max_eq_left hnonneg]
  exact_mod_cast hreal

/-- The affine path descending across a real closed interval, bundled in that interval. -/
def chapterVIDescendingIccPath (a b : ℝ) (hab : a ≤ b) :
    Path (⟨b, ⟨hab, le_rfl⟩⟩ : Set.Icc a b)
      (⟨a, ⟨le_rfl, hab⟩⟩ : Set.Icc a b) where
  toFun s := ⟨AffineMap.lineMap b a (s : ℝ), by
    have hs0 := s.property.1
    have hs1 := s.property.2
    constructor <;>
      simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, smul_eq_mul] <;>
        nlinarith⟩
  continuous_toFun := by fun_prop
  source' := by
    apply Subtype.ext
    simp [AffineMap.lineMap_apply]
  target' := by
    apply Subtype.ext
    simp [AffineMap.lineMap_apply]

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

/-! ## Identification with Poincaré's source equations -/

/-- Every nonzero point of the concrete curve (3), not just D, satisfies Poincaré's cleared
collision equation.  This is the algebraic link needed to interpret the branch paths below as
paths of singularities of the source integrand. -/
theorem chapterVID_curveThree_collisionEquation
    {x : ℝ} (hx : x ≠ 0) :
    chapterVIPlanarCollisionEquationThree chapterVIDEccentricity chapterVIDComplement
      2 (x : ℂ) (chapterVIDCurveThreeY x : ℂ) = 0 := by
  have h := chapterVI_planarCollisionEquationThree_halfAngle
    (1 / 100 : ℂ) chapterVIDEccentricity chapterVIDComplement 2
    (x : ℂ) (chapterVIDCurveThreeY x : ℂ)
    chapterVID_halfAngle_sine chapterVID_halfAngle_cosine
  have hxcomplex : (x : ℂ) ≠ 0 := by exact_mod_cast hx
  have hcurve :
      ((x : ℂ) - 1 / 100) ^ 2 -
        2 * (1 + (1 / 100 : ℂ) ^ 2) * (x : ℂ) *
          (chapterVIDCurveThreeY x : ℂ) = 0 := by
    unfold chapterVIDCurveThreeY
    push_cast
    field_simp [hxcomplex]
    ring
  rw [hcurve, mul_zero] at h
  exact (mul_eq_zero.mp h).resolve_left (by norm_num)

/-- Along the negative real curve (3), the literal source factor `H = ξ-βη` vanishes.
The hypotheses also discharge the denominators introduced by Poincaré's planar coordinates. -/
theorem chapterVID_curveThree_collisionFactorPlus
    {x : ℝ} (hx : x < 0) :
    chapterVIPlanarCollisionFactorPlus chapterVIDEccentricity chapterVIDComplement
      0 1 2 (x : ℂ) (chapterVIDCurveThreeY x : ℂ) = 0 := by
  have hx0 : x ≠ 0 := ne_of_lt hx
  have hxcomplex : (x : ℂ) ≠ 0 := by exact_mod_cast hx0
  have hy : chapterVIDCurveThreeY x < 0 := by
    have hnumerator : 0 < (x - 1 / 100) ^ 2 :=
      sq_pos_of_ne_zero (by nlinarith)
    have hdenominator : 2 * (1 + (1 / 100 : ℝ) ^ 2) * x < 0 :=
      mul_neg_of_pos_of_neg (by norm_num) hx
    exact div_neg_of_pos_of_neg hnumerator hdenominator
  have hycomplex : (chapterVIDCurveThreeY x : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_lt hy)
  have hclear := chapterVI_planarCollisionFactorPlus_eq_cleared
    chapterVIDEccentricity chapterVIDComplement 0 1 2 hxcomplex hycomplex
  rw [chapterVI_planarCollisionEquationThreeGeneral_secondCircular] at hclear
  rw [chapterVID_curveThree_collisionEquation hx0, mul_zero] at hclear
  exact (mul_eq_zero.mp hclear).resolve_left
    (mul_ne_zero (mul_ne_zero (by norm_num) hxcomplex) hycomplex)

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

/-! The other real branch from D through B toward P. -/

theorem chapterVIDPolynomial_deriv_neg_D_to_turn
    {x : ℝ} (hx : x ∈ Set.Icc chapterVIDRoot (-13 / 1000)) :
    deriv chapterVIDPolynomial x < 0 := by
  rw [(hasDerivAt_chapterVIDPolynomial x).deriv]
  have hxleft : -27 / 1000 ≤ x := chapterVIDRoot_mem.1.trans hx.1
  have hsquare : x ^ 2 ≤ (27 / 1000 : ℝ) ^ 2 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ x + 27 / 1000)
      (by linarith [hx.2] : 0 ≤ 27 / 1000 - x)]
  nlinarith [hx.2]

theorem chapterVIDPolynomial_strictAntiOn_D_to_turn :
    StrictAntiOn chapterVIDPolynomial (Set.Icc chapterVIDRoot (-13 / 1000)) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
  · exact continuous_chapterVIDPolynomial.continuousOn
  · intro x hx
    exact chapterVIDPolynomial_deriv_neg_D_to_turn (interior_subset hx)

/-- No second root of D's cubic occurs between D and the BP endpoint. -/
theorem chapterVIDPolynomial_neg_right_of_D
    {x : ℝ} (hxD : chapterVIDRoot < x) (hxright : x ≤ -1 / 1000) :
    chapterVIDPolynomial x < 0 := by
  by_cases hxturn : x ≤ -13 / 1000
  · have hxmem : x ∈ Set.Icc chapterVIDRoot (-13 / 1000) := ⟨hxD.le, hxturn⟩
    have hDmem : chapterVIDRoot ∈ Set.Icc chapterVIDRoot (-13 / 1000) := by
      constructor
      · rfl
      · nlinarith [chapterVIDRoot_mem.2]
    have hstrict := chapterVIDPolynomial_strictAntiOn_D_to_turn hDmem hxmem hxD
    rw [chapterVIDRoot_isRoot] at hstrict
    linarith
  · have hxturn' : -13 / 1000 < x := lt_of_not_ge hxturn
    have hxneg : x < 0 := lt_of_le_of_lt hxright (by norm_num)
    have hproduct : (x + 13 / 1000) * (x + 1 / 1000) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
    have hcubic : x ^ 3 ≤ 0 := by
      calc
        x ^ 3 = x * x ^ 2 := by ring
        _ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hxneg.le (sq_nonneg x)
    unfold chapterVIDPolynomial
    nlinarith

theorem chapterVIDCurveThreeLogDerivative_pos
    {x : ℝ} (hxD : chapterVIDRoot < x) (hxright : x ≤ -1 / 1000) :
    0 < chapterVIDCurveThreeLogDerivative x := by
  have hxneg : x < 0 := lt_of_le_of_lt hxright (by norm_num)
  have hp := chapterVIDPolynomial_neg_right_of_D hxD hxright
  unfold chapterVIDCurveThreeLogDerivative
  have hx2 : 0 < x ^ 2 := sq_pos_of_ne_zero (ne_of_lt hxneg)
  have hlinear : 100 * x - 1 < 0 := by nlinarith
  have hdenom : 10001 * x ^ 2 * (100 * x - 1) < 0 :=
    mul_neg_of_pos_of_neg (mul_pos (by norm_num) hx2) hlinear
  exact div_pos_of_neg_of_neg (mul_neg_of_pos_of_neg (by norm_num) hp) hdenom

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

/-- On the negative curve (3), Poincaré's complex parameter `z` is the positive real number
used above to synchronize the two branches.  Thus the common real parameter is not an auxiliary
reparameterization: it is the source expression with `a=-1`, `c=3`, and the §97 scales. -/
theorem chapterVID_singularityParameter_curveThree_eq_smooth
    {x : ℝ} (hx : x < 0) :
    chapterVISingularityParameter (-1) 3 (-100 / 10001) 0
        (x : ℂ) (chapterVIDCurveThreeY x : ℂ) =
      (chapterVIDCurveThreeSmoothParameter x : ℂ) := by
  have hx0 : x ≠ 0 := ne_of_lt hx
  unfold chapterVISingularityParameter chapterVIDCurveThreeSmoothParameter
  simp only [zpow_neg_one, zpow_ofNat, zero_mul, add_zero]
  push_cast
  field_simp [hx0]

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

theorem continuousOn_chapterVIDCurveThreeSmoothParameter_BPrime_to_D :
    ContinuousOn chapterVIDCurveThreeSmoothParameter
      (Set.Icc (-100) chapterVIDRoot) := by
  apply continuousOn_of_forall_continuousAt
  intro x hx
  have hxneg : x < 0 := hx.2.trans_lt chapterVIDRoot_lt_zero
  have hx0 : x ≠ 0 := ne_of_lt hxneg
  have hdenominator : 2 * (1 + (1 / 100 : ℝ) ^ 2) * x ≠ 0 := by
    exact mul_ne_zero (by norm_num) hx0
  unfold chapterVIDCurveThreeSmoothParameter chapterVIDCurveThreeY
  fun_prop (disch := simp [hx0])

theorem chapterVIDCurveThreeSmoothParameter_strictAntiOn_BPrime_to_D :
    StrictAntiOn chapterVIDCurveThreeSmoothParameter
      (Set.Icc (-100) chapterVIDRoot) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
    continuousOn_chapterVIDCurveThreeSmoothParameter_BPrime_to_D
  intro x hx
  rw [interior_Icc] at hx
  have hxneg : x < 0 := hx.2.trans chapterVIDRoot_lt_zero
  rw [deriv_chapterVIDCurveThreeSmoothParameter hxneg]
  exact mul_neg_of_pos_of_neg
    (chapterVIDCurveThreeSmoothParameter_pos hxneg)
    (chapterVIDCurveThreeLogDerivative_neg hx.1.le hx.2)

theorem continuousOn_chapterVIDCurveThreeSmoothParameter_D_to_P :
    ContinuousOn chapterVIDCurveThreeSmoothParameter
      (Set.Icc chapterVIDRoot (-1 / 1000)) := by
  apply continuousOn_of_forall_continuousAt
  intro x hx
  have hxneg : x < 0 := lt_of_le_of_lt hx.2 (by norm_num)
  have hx0 : x ≠ 0 := ne_of_lt hxneg
  have hdenominator : 2 * (1 + (1 / 100 : ℝ) ^ 2) * x ≠ 0 := by
    exact mul_ne_zero (by norm_num) hx0
  unfold chapterVIDCurveThreeSmoothParameter chapterVIDCurveThreeY
  fun_prop (disch := simp [hx0])

/-- Along the whole selected inside branch D→B→P, the parameter modulus increases strictly.
This supplies the branch-invertibility needed to synchronize the two poles by the same external
`|z|` parameter. -/
theorem chapterVIDCurveThreeSmoothParameter_strictMonoOn_D_to_P :
    StrictMonoOn chapterVIDCurveThreeSmoothParameter
      (Set.Icc chapterVIDRoot (-1 / 1000)) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
    continuousOn_chapterVIDCurveThreeSmoothParameter_D_to_P
  intro x hx
  rw [interior_Icc] at hx
  have hxneg : x < 0 := hx.2.trans (by norm_num)
  rw [deriv_chapterVIDCurveThreeSmoothParameter hxneg]
  exact mul_pos
    (chapterVIDCurveThreeSmoothParameter_pos hxneg)
    (chapterVIDCurveThreeLogDerivative_pos hx.1 hx.2.le)

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

/-! ## Source-facing cubic lifts and the genuine-pinch obstruction -/

/-- A selected BP endpoint.  Its defining interval and `|z|=1` equation are exported below. -/
noncomputable def chapterVIDInsideEndpointX : ℝ :=
  Classical.choose exists_chapterVIDCurveThree_unit_parameter_inside

theorem chapterVIDInsideEndpointX_mem :
    chapterVIDInsideEndpointX ∈ Set.Ioo (-1 / 100) (-1 / 1000) :=
  (Classical.choose_spec exists_chapterVIDCurveThree_unit_parameter_inside).1

theorem chapterVIDInsideEndpointX_parameter :
    chapterVIDCurveThreeParameterModulus chapterVIDInsideEndpointX = 1 :=
  (Classical.choose_spec exists_chapterVIDCurveThree_unit_parameter_inside).2

def chapterVIDCriticalParameterModulus : ℝ :=
  chapterVIDCurveThreeSmoothParameter chapterVIDRoot

theorem chapterVIDRoot_lt_insideEndpointX :
    chapterVIDRoot < chapterVIDInsideEndpointX := by
  linarith [chapterVIDRoot_mem.2, chapterVIDInsideEndpointX_mem.1]

theorem chapterVIDInsideEndpointX_le_P :
    chapterVIDInsideEndpointX ≤ -1 / 1000 := chapterVIDInsideEndpointX_mem.2.le

theorem chapterVIDInsideEndpointX_smoothParameter :
    chapterVIDCurveThreeSmoothParameter chapterVIDInsideEndpointX = 1 := by
  rw [chapterVIDCurveThreeSmoothParameter_eq_modulus
    (chapterVIDInsideEndpointX_mem.2.trans (by norm_num))]
  exact chapterVIDInsideEndpointX_parameter

theorem chapterVIDCriticalParameterModulus_lt_one :
    chapterVIDCriticalParameterModulus < 1 := by
  unfold chapterVIDCriticalParameterModulus
  rw [← chapterVIDInsideEndpointX_smoothParameter]
  exact chapterVIDCurveThreeSmoothParameter_strictMonoOn_D_to_P
    ⟨le_rfl, chapterVIDRoot_mem.2.trans
      (by norm_num : (-26 / 1000 : ℝ) ≤ -1 / 1000)⟩
    ⟨chapterVIDRoot_lt_insideEndpointX.le, chapterVIDInsideEndpointX_le_P⟩
    chapterVIDRoot_lt_insideEndpointX

theorem chapterVIDInsideBranch_parameter_image :
    chapterVIDCurveThreeSmoothParameter ''
        Set.Icc chapterVIDRoot chapterVIDInsideEndpointX =
      Set.Icc chapterVIDCriticalParameterModulus 1 := by
  have hcontinuous := continuousOn_chapterVIDCurveThreeSmoothParameter_D_to_P.mono
    (Set.Icc_subset_Icc_right chapterVIDInsideEndpointX_le_P)
  have hmono :=
    (chapterVIDCurveThreeSmoothParameter_strictMonoOn_D_to_P.mono
      (Set.Icc_subset_Icc_right chapterVIDInsideEndpointX_le_P)).monotoneOn
  rw [hcontinuous.image_Icc_of_monotoneOn chapterVIDRoot_lt_insideEndpointX.le hmono]
  simp only [chapterVIDCriticalParameterModulus,
    chapterVIDInsideEndpointX_smoothParameter]

/-- The selected inside branch, parameterized order-isomorphically by the common modulus `|z|`. -/
noncomputable def chapterVIDInsideBranchOrderIso :
    Set.Icc chapterVIDRoot chapterVIDInsideEndpointX ≃o
      Set.Icc chapterVIDCriticalParameterModulus 1 :=
  (chapterVIDCurveThreeSmoothParameter_strictMonoOn_D_to_P.mono
      (Set.Icc_subset_Icc_right chapterVIDInsideEndpointX_le_P)).orderIso
      chapterVIDCurveThreeSmoothParameter
      (Set.Icc chapterVIDRoot chapterVIDInsideEndpointX) |>.trans
    (OrderIso.setCongr _ _ chapterVIDInsideBranch_parameter_image)

@[simp]
theorem chapterVIDInsideBranchOrderIso_apply
    (x : Set.Icc chapterVIDRoot chapterVIDInsideEndpointX) :
    (chapterVIDInsideBranchOrderIso x : ℝ) =
      chapterVIDCurveThreeSmoothParameter x := rfl

def chapterVIDInsideEndpointSubtype :
    Set.Icc chapterVIDRoot chapterVIDInsideEndpointX :=
  ⟨chapterVIDInsideEndpointX, ⟨chapterVIDRoot_lt_insideEndpointX.le, le_rfl⟩⟩

def chapterVIDCollisionInsideSubtype :
    Set.Icc chapterVIDRoot chapterVIDInsideEndpointX :=
  ⟨chapterVIDRoot, ⟨le_rfl, chapterVIDRoot_lt_insideEndpointX.le⟩⟩

def chapterVIDOneParameterSubtype :
    Set.Icc chapterVIDCriticalParameterModulus 1 :=
  ⟨1, ⟨chapterVIDCriticalParameterModulus_lt_one.le, le_rfl⟩⟩

def chapterVIDCriticalParameterSubtype :
    Set.Icc chapterVIDCriticalParameterModulus 1 :=
  ⟨chapterVIDCriticalParameterModulus,
    ⟨le_rfl, chapterVIDCriticalParameterModulus_lt_one.le⟩⟩

theorem chapterVIDInsideBranchOrderIso_symm_one :
    chapterVIDInsideBranchOrderIso.symm chapterVIDOneParameterSubtype =
      chapterVIDInsideEndpointSubtype := by
  apply chapterVIDInsideBranchOrderIso.injective
  rw [chapterVIDInsideBranchOrderIso.apply_symm_apply]
  apply Subtype.ext
  exact chapterVIDInsideEndpointX_smoothParameter.symm

theorem chapterVIDInsideBranchOrderIso_symm_critical :
    chapterVIDInsideBranchOrderIso.symm chapterVIDCriticalParameterSubtype =
      chapterVIDCollisionInsideSubtype := by
  apply chapterVIDInsideBranchOrderIso.injective
  rw [chapterVIDInsideBranchOrderIso.apply_symm_apply]
  rfl

/-- The inside singular point followed continuously from its `|z|=1` endpoint back to D, with
the external modulus as its path parameter. -/
noncomputable def chapterVIDInsideXSubtypePath :
    Path chapterVIDInsideEndpointSubtype chapterVIDCollisionInsideSubtype :=
  ((chapterVIDescendingIccPath chapterVIDCriticalParameterModulus 1
      chapterVIDCriticalParameterModulus_lt_one.le).map
      chapterVIDInsideBranchOrderIso.symm.continuous).cast
    chapterVIDInsideBranchOrderIso_symm_one.symm
    chapterVIDInsideBranchOrderIso_symm_critical.symm

noncomputable def chapterVIDInsideXPath :
    Path chapterVIDInsideEndpointX chapterVIDRoot :=
  chapterVIDInsideXSubtypePath.map continuous_subtype_val

/-- The selected exterior endpoint on DB'. -/
noncomputable def chapterVIDOutsideEndpointX : ℝ :=
  Classical.choose existsUnique_chapterVIDCurveThree_unit_parameter_outside

theorem chapterVIDOutsideEndpointX_mem :
    chapterVIDOutsideEndpointX ∈ Set.Ioo (-100) (-1) :=
  (Classical.choose_spec existsUnique_chapterVIDCurveThree_unit_parameter_outside).1.1

theorem chapterVIDOutsideEndpointX_parameter :
    chapterVIDCurveThreeParameterModulus chapterVIDOutsideEndpointX = 1 :=
  (Classical.choose_spec existsUnique_chapterVIDCurveThree_unit_parameter_outside).1.2

theorem chapterVIDOutsideEndpointX_le_root :
    chapterVIDOutsideEndpointX ≤ chapterVIDRoot := by
  linarith [chapterVIDOutsideEndpointX_mem.2, chapterVIDRoot_mem.1]

theorem chapterVIDOutsideEndpointX_ge_BPrime :
    -100 ≤ chapterVIDOutsideEndpointX := chapterVIDOutsideEndpointX_mem.1.le

theorem chapterVIDOutsideEndpointX_smoothParameter :
    chapterVIDCurveThreeSmoothParameter chapterVIDOutsideEndpointX = 1 := by
  rw [chapterVIDCurveThreeSmoothParameter_eq_modulus
    (chapterVIDOutsideEndpointX_mem.2.trans (by norm_num))]
  exact chapterVIDOutsideEndpointX_parameter

def chapterVIDOutsideNegativeParameter (x : ℝ) : ℝ :=
  -chapterVIDCurveThreeSmoothParameter x

theorem continuousOn_chapterVIDOutsideNegativeParameter :
    ContinuousOn chapterVIDOutsideNegativeParameter
      (Set.Icc chapterVIDOutsideEndpointX chapterVIDRoot) := by
  exact (continuousOn_chapterVIDCurveThreeSmoothParameter_BPrime_to_D.mono
    (Set.Icc_subset_Icc chapterVIDOutsideEndpointX_ge_BPrime le_rfl)).neg

theorem chapterVIDOutsideNegativeParameter_strictMonoOn :
    StrictMonoOn chapterVIDOutsideNegativeParameter
      (Set.Icc chapterVIDOutsideEndpointX chapterVIDRoot) := by
  intro x hx y hy hxy
  exact neg_lt_neg
    (chapterVIDCurveThreeSmoothParameter_strictAntiOn_BPrime_to_D
      (Set.Icc_subset_Icc chapterVIDOutsideEndpointX_ge_BPrime le_rfl hx)
      (Set.Icc_subset_Icc chapterVIDOutsideEndpointX_ge_BPrime le_rfl hy) hxy)

theorem chapterVIDOutsideNegativeParameter_image :
    chapterVIDOutsideNegativeParameter ''
        Set.Icc chapterVIDOutsideEndpointX chapterVIDRoot =
      Set.Icc (-1) (-chapterVIDCriticalParameterModulus) := by
  rw [continuousOn_chapterVIDOutsideNegativeParameter.image_Icc_of_monotoneOn
    chapterVIDOutsideEndpointX_le_root
    chapterVIDOutsideNegativeParameter_strictMonoOn.monotoneOn]
  simp [chapterVIDOutsideNegativeParameter, chapterVIDOutsideEndpointX_smoothParameter,
    chapterVIDCriticalParameterModulus]

noncomputable def chapterVIDOutsideBranchOrderIso :
    Set.Icc chapterVIDOutsideEndpointX chapterVIDRoot ≃o
      Set.Icc (-1) (-chapterVIDCriticalParameterModulus) :=
  chapterVIDOutsideNegativeParameter_strictMonoOn.orderIso
      chapterVIDOutsideNegativeParameter
      (Set.Icc chapterVIDOutsideEndpointX chapterVIDRoot) |>.trans
    (OrderIso.setCongr _ _ chapterVIDOutsideNegativeParameter_image)

@[simp]
theorem chapterVIDOutsideBranchOrderIso_apply
    (x : Set.Icc chapterVIDOutsideEndpointX chapterVIDRoot) :
    (chapterVIDOutsideBranchOrderIso x : ℝ) =
      chapterVIDOutsideNegativeParameter x := rfl

def chapterVIDOutsideEndpointSubtype :
    Set.Icc chapterVIDOutsideEndpointX chapterVIDRoot :=
  ⟨chapterVIDOutsideEndpointX, ⟨le_rfl, chapterVIDOutsideEndpointX_le_root⟩⟩

def chapterVIDCollisionOutsideSubtype :
    Set.Icc chapterVIDOutsideEndpointX chapterVIDRoot :=
  ⟨chapterVIDRoot, ⟨chapterVIDOutsideEndpointX_le_root, le_rfl⟩⟩

def chapterVIDNegativeOneParameterSubtype :
    Set.Icc (-1) (-chapterVIDCriticalParameterModulus) :=
  ⟨-1, ⟨le_rfl, neg_le_neg chapterVIDCriticalParameterModulus_lt_one.le⟩⟩

def chapterVIDNegativeCriticalParameterSubtype :
    Set.Icc (-1) (-chapterVIDCriticalParameterModulus) :=
  ⟨-chapterVIDCriticalParameterModulus,
    ⟨neg_le_neg chapterVIDCriticalParameterModulus_lt_one.le, le_rfl⟩⟩

theorem chapterVIDOutsideBranchOrderIso_symm_negOne :
    chapterVIDOutsideBranchOrderIso.symm chapterVIDNegativeOneParameterSubtype =
      chapterVIDOutsideEndpointSubtype := by
  apply chapterVIDOutsideBranchOrderIso.injective
  rw [chapterVIDOutsideBranchOrderIso.apply_symm_apply]
  apply Subtype.ext
  change (-1 : ℝ) = -chapterVIDCurveThreeSmoothParameter chapterVIDOutsideEndpointX
  rw [chapterVIDOutsideEndpointX_smoothParameter]

theorem chapterVIDOutsideBranchOrderIso_symm_negCritical :
    chapterVIDOutsideBranchOrderIso.symm chapterVIDNegativeCriticalParameterSubtype =
      chapterVIDCollisionOutsideSubtype := by
  apply chapterVIDOutsideBranchOrderIso.injective
  rw [chapterVIDOutsideBranchOrderIso.apply_symm_apply]
  rfl

noncomputable def chapterVIDOutsideXSubtypePath :
    Path chapterVIDOutsideEndpointSubtype chapterVIDCollisionOutsideSubtype :=
  (((chapterVIDescendingIccPath (-1) (-chapterVIDCriticalParameterModulus)
      (neg_le_neg chapterVIDCriticalParameterModulus_lt_one.le)).symm.map
      chapterVIDOutsideBranchOrderIso.symm.continuous).cast
    chapterVIDOutsideBranchOrderIso_symm_negOne.symm
    chapterVIDOutsideBranchOrderIso_symm_negCritical.symm)

noncomputable def chapterVIDOutsideXPath :
    Path chapterVIDOutsideEndpointX chapterVIDRoot :=
  chapterVIDOutsideXSubtypePath.map continuous_subtype_val

theorem chapterVIDInsideXPath_parameter (s : I) :
    chapterVIDCurveThreeSmoothParameter (chapterVIDInsideXPath s) =
      AffineMap.lineMap 1 chapterVIDCriticalParameterModulus (s : ℝ) := by
  change chapterVIDCurveThreeSmoothParameter
      (chapterVIDInsideBranchOrderIso.symm
        ((chapterVIDescendingIccPath chapterVIDCriticalParameterModulus 1
          chapterVIDCriticalParameterModulus_lt_one.le) s)) = _
  have h := chapterVIDInsideBranchOrderIso.apply_symm_apply
    ((chapterVIDescendingIccPath chapterVIDCriticalParameterModulus 1
      chapterVIDCriticalParameterModulus_lt_one.le) s)
  exact congrArg Subtype.val h

theorem chapterVIDOutsideXPath_negativeParameter (s : I) :
    chapterVIDOutsideNegativeParameter (chapterVIDOutsideXPath s) =
      AffineMap.lineMap (-1) (-chapterVIDCriticalParameterModulus) (s : ℝ) := by
  change chapterVIDOutsideNegativeParameter
      (chapterVIDOutsideBranchOrderIso.symm
        ((chapterVIDescendingIccPath (-1) (-chapterVIDCriticalParameterModulus)
          (neg_le_neg chapterVIDCriticalParameterModulus_lt_one.le)).symm s)) = _
  have h := chapterVIDOutsideBranchOrderIso.apply_symm_apply
    ((chapterVIDescendingIccPath (-1) (-chapterVIDCriticalParameterModulus)
      (neg_le_neg chapterVIDCriticalParameterModulus_lt_one.le)).symm s)
  calc
    chapterVIDOutsideNegativeParameter
        (chapterVIDOutsideBranchOrderIso.symm
          ((chapterVIDescendingIccPath (-1) (-chapterVIDCriticalParameterModulus)
            (neg_le_neg chapterVIDCriticalParameterModulus_lt_one.le)).symm s)) =
      (chapterVIDOutsideBranchOrderIso
        (chapterVIDOutsideBranchOrderIso.symm
          ((chapterVIDescendingIccPath (-1) (-chapterVIDCriticalParameterModulus)
            (neg_le_neg chapterVIDCriticalParameterModulus_lt_one.le)).symm s)) : ℝ) := rfl
    _ = ((chapterVIDescendingIccPath (-1) (-chapterVIDCriticalParameterModulus)
          (neg_le_neg chapterVIDCriticalParameterModulus_lt_one.le)).symm s : ℝ) :=
      congrArg Subtype.val h
    _ = AffineMap.lineMap (-1) (-chapterVIDCriticalParameterModulus) (s : ℝ) := by
      simp [chapterVIDescendingIccPath, Path.symm_apply, AffineMap.lineMap_apply,
        smul_eq_mul]
      ring

/-- Both canonical singular paths lie over the same external parameter modulus at every time. -/
theorem chapterVIDPolePaths_parameter_synchronized (s : I) :
    chapterVIDCurveThreeSmoothParameter (chapterVIDInsideXPath s) =
      chapterVIDCurveThreeSmoothParameter (chapterVIDOutsideXPath s) := by
  rw [chapterVIDInsideXPath_parameter s]
  have houtside := chapterVIDOutsideXPath_negativeParameter s
  unfold chapterVIDOutsideNegativeParameter at houtside
  simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, smul_eq_mul] at houtside ⊢
  nlinarith

theorem chapterVIDInsideXPath_mem (s : I) :
    chapterVIDInsideXPath s ∈ Set.Icc chapterVIDRoot chapterVIDInsideEndpointX := by
  change (chapterVIDInsideXSubtypePath s).1 ∈ _
  exact (chapterVIDInsideXSubtypePath s).2

theorem chapterVIDOutsideXPath_mem (s : I) :
    chapterVIDOutsideXPath s ∈ Set.Icc chapterVIDOutsideEndpointX chapterVIDRoot := by
  change (chapterVIDOutsideXSubtypePath s).1 ∈ _
  exact (chapterVIDOutsideXSubtypePath s).2

/-- The three selected points in Poincaré's actual `x^(1/3)` contour coordinate. -/
noncomputable def chapterVIDInsideEndpointLift : ℂ :=
  chapterVINegativeRealCubicLift chapterVIDInsideEndpointX

noncomputable def chapterVIDOutsideEndpointLift : ℂ :=
  chapterVINegativeRealCubicLift chapterVIDOutsideEndpointX

noncomputable def chapterVIDCollisionLift : ℂ :=
  chapterVINegativeRealCubicLift chapterVIDRoot

@[simp] theorem chapterVIDInsideEndpointLift_pow :
    chapterVIDInsideEndpointLift ^ 3 = (chapterVIDInsideEndpointX : ℂ) :=
  chapterVINegativeRealCubicLift_pow
    (chapterVIDInsideEndpointX_mem.2.trans (by norm_num)).le

@[simp] theorem chapterVIDOutsideEndpointLift_pow :
    chapterVIDOutsideEndpointLift ^ 3 = (chapterVIDOutsideEndpointX : ℂ) :=
  chapterVINegativeRealCubicLift_pow
    (chapterVIDOutsideEndpointX_mem.2.trans (by norm_num)).le

@[simp] theorem chapterVIDCollisionLift_pow :
    chapterVIDCollisionLift ^ 3 = chapterVIDX :=
  chapterVINegativeRealCubicLift_pow chapterVIDRoot_lt_zero.le

theorem chapterVIDInsideEndpointLift_norm_lt_one :
    ‖chapterVIDInsideEndpointLift‖ < 1 := by
  rw [chapterVI_norm_cubicLift_lt_one_iff chapterVIDInsideEndpointLift_pow]
  rw [abs_of_neg (chapterVIDInsideEndpointX_mem.2.trans (by norm_num))]
  linarith [chapterVIDInsideEndpointX_mem.1]

theorem one_lt_chapterVIDOutsideEndpointLift_norm :
    1 < ‖chapterVIDOutsideEndpointLift‖ := by
  rw [chapterVI_one_lt_norm_cubicLift_iff chapterVIDOutsideEndpointLift_pow]
  rw [abs_of_neg (chapterVIDOutsideEndpointX_mem.2.trans (by norm_num))]
  simpa using neg_lt_neg chapterVIDOutsideEndpointX_mem.2

/-- Canonical synchronized pole paths in Poincaré's `x^(1/3)` coordinate. -/
noncomputable def chapterVIDInsidePolePath :
    Path chapterVIDInsideEndpointLift chapterVIDCollisionLift :=
  chapterVIDInsideXPath.map continuous_chapterVINegativeRealCubicLift

noncomputable def chapterVIDOutsidePolePath :
    Path chapterVIDOutsideEndpointLift chapterVIDCollisionLift :=
  chapterVIDOutsideXPath.map continuous_chapterVINegativeRealCubicLift

@[simp]
theorem chapterVIDInsidePolePath_pow (s : I) :
    chapterVIDInsidePolePath s ^ 3 = (chapterVIDInsideXPath s : ℂ) := by
  change chapterVINegativeRealCubicLift (chapterVIDInsideXPath s) ^ 3 = _
  apply chapterVINegativeRealCubicLift_pow
  exact (chapterVIDInsideXPath_mem s).2.trans
    (chapterVIDInsideEndpointX_mem.2.le.trans (by norm_num))

@[simp]
theorem chapterVIDOutsidePolePath_pow (s : I) :
    chapterVIDOutsidePolePath s ^ 3 = (chapterVIDOutsideXPath s : ℂ) := by
  change chapterVINegativeRealCubicLift (chapterVIDOutsideXPath s) ^ 3 = _
  apply chapterVINegativeRealCubicLift_pow
  exact (chapterVIDOutsideXPath_mem s).2.trans chapterVIDRoot_lt_zero.le

theorem chapterVIDInsideXPath_neg (s : I) : chapterVIDInsideXPath s < 0 :=
  (chapterVIDInsideXPath_mem s).2.trans_lt
    (chapterVIDInsideEndpointX_mem.2.trans (by norm_num))

theorem chapterVIDOutsideXPath_neg (s : I) : chapterVIDOutsideXPath s < 0 :=
  (chapterVIDOutsideXPath_mem s).2.trans_lt chapterVIDRoot_lt_zero

/-- The inside cubic-lift path is pointwise a zero of Poincaré's literal source collision
factor after descending from the `x^(1/3)` coordinate to `x`. -/
theorem chapterVIDInsidePolePath_sourceCollision (s : I) :
    chapterVIPlanarCollisionFactorPlus chapterVIDEccentricity chapterVIDComplement
      0 1 2 (chapterVIDInsidePolePath s ^ 3)
        (chapterVIDCurveThreeY (chapterVIDInsideXPath s) : ℂ) = 0 := by
  rw [chapterVIDInsidePolePath_pow]
  exact chapterVID_curveThree_collisionFactorPlus (chapterVIDInsideXPath_neg s)

/-- The exterior cubic-lift path is the second pointwise zero of the same source factor. -/
theorem chapterVIDOutsidePolePath_sourceCollision (s : I) :
    chapterVIPlanarCollisionFactorPlus chapterVIDEccentricity chapterVIDComplement
      0 1 2 (chapterVIDOutsidePolePath s ^ 3)
        (chapterVIDCurveThreeY (chapterVIDOutsideXPath s) : ℂ) = 0 := by
  rw [chapterVIDOutsidePolePath_pow]
  exact chapterVID_curveThree_collisionFactorPlus (chapterVIDOutsideXPath_neg s)

/-- The common source singularity parameter followed by the two branches. -/
noncomputable def chapterVIDCommonSingularityParameter (s : I) : ℂ :=
  chapterVIDCurveThreeSmoothParameter (chapterVIDInsideXPath s)

theorem chapterVIDInsidePolePath_sourceParameter (s : I) :
    chapterVISingularityParameter (-1) 3 (-100 / 10001) 0
        (chapterVIDInsidePolePath s ^ 3)
        (chapterVIDCurveThreeY (chapterVIDInsideXPath s) : ℂ) =
      chapterVIDCommonSingularityParameter s := by
  rw [chapterVIDInsidePolePath_pow,
    chapterVID_singularityParameter_curveThree_eq_smooth (chapterVIDInsideXPath_neg s)]
  rfl

theorem chapterVIDOutsidePolePath_sourceParameter (s : I) :
    chapterVISingularityParameter (-1) 3 (-100 / 10001) 0
        (chapterVIDOutsidePolePath s ^ 3)
        (chapterVIDCurveThreeY (chapterVIDOutsideXPath s) : ℂ) =
      chapterVIDCommonSingularityParameter s := by
  rw [chapterVIDOutsidePolePath_pow,
    chapterVID_singularityParameter_curveThree_eq_smooth (chapterVIDOutsideXPath_neg s)]
  unfold chapterVIDCommonSingularityParameter
  exact_mod_cast (chapterVIDPolePaths_parameter_synchronized s).symm

/-- Source-faithful branch package: two cubic-lifted zeros of equation (3), synchronized by
Poincaré's actual complex parameter and coalescing at D. -/
structure ChapterVIDSynchronizedCollisionBranches where
  insidePole : Path chapterVIDInsideEndpointLift chapterVIDCollisionLift
  outsidePole : Path chapterVIDOutsideEndpointLift chapterVIDCollisionLift
  insideCollision : ∀ s : I,
    chapterVIPlanarCollisionFactorPlus chapterVIDEccentricity chapterVIDComplement
      0 1 2 (insidePole s ^ 3)
        (chapterVIDCurveThreeY (chapterVIDInsideXPath s) : ℂ) = 0
  outsideCollision : ∀ s : I,
    chapterVIPlanarCollisionFactorPlus chapterVIDEccentricity chapterVIDComplement
      0 1 2 (outsidePole s ^ 3)
        (chapterVIDCurveThreeY (chapterVIDOutsideXPath s) : ℂ) = 0
  insideParameter : ∀ s : I,
    chapterVISingularityParameter (-1) 3 (-100 / 10001) 0
        (insidePole s ^ 3)
        (chapterVIDCurveThreeY (chapterVIDInsideXPath s) : ℂ) =
      chapterVIDCommonSingularityParameter s
  outsideParameter : ∀ s : I,
    chapterVISingularityParameter (-1) 3 (-100 / 10001) 0
        (outsidePole s ^ 3)
        (chapterVIDCurveThreeY (chapterVIDOutsideXPath s) : ℂ) =
      chapterVIDCommonSingularityParameter s

noncomputable def chapterVIDSynchronizedCollisionBranches :
    ChapterVIDSynchronizedCollisionBranches where
  insidePole := chapterVIDInsidePolePath
  outsidePole := chapterVIDOutsidePolePath
  insideCollision := chapterVIDInsidePolePath_sourceCollision
  outsideCollision := chapterVIDOutsidePolePath_sourceCollision
  insideParameter := chapterVIDInsidePolePath_sourceParameter
  outsideParameter := chapterVIDOutsidePolePath_sourceParameter

/-- Concrete D corollary of the moving-pole winding obstruction.  Once the two actual singular
lifts are supplied as paths from the certified unit-parameter endpoints to D, no smooth
continuation of Poincaré's unit contour can avoid both all the way to their collision. -/
theorem chapterVID_not_both_movingPoleAvoidances
    {b : ℂ} {final : Path b b}
    (contour : ContinuousMap.Homotopy
      (chapterVIUnitCirclePath : C(I, ℂ)) (final : C(I, ℂ)))
    (insidePole : Path chapterVIDInsideEndpointLift chapterVIDCollisionLift)
    (outsidePole : Path chapterVIDOutsideEndpointLift chapterVIDCollisionLift)
    (hcontourClosed : ∀ s : I, contour (s, 0) = contour (s, 1)) :
    ¬ (Nonempty (ChapterVIMovingPoleAvoidance contour insidePole) ∧
      Nonempty (ChapterVIMovingPoleAvoidance contour outsidePole)) :=
  chapterVI_not_both_movingPoleAvoidances_of_coalescence
    contour insidePole outsidePole hcontourClosed
    chapterVIDInsideEndpointLift_norm_lt_one
    one_lt_chapterVIDOutsideEndpointLift_norm

/-- Fully instantiated branch-tracking form: the pole paths are the inverse-monotone
parameterizations constructed above, not additional user-supplied data. -/
theorem chapterVID_not_both_canonicalMovingPoleAvoidances
    {b : ℂ} {final : Path b b}
    (contour : ContinuousMap.Homotopy
      (chapterVIUnitCirclePath : C(I, ℂ)) (final : C(I, ℂ)))
    (hcontourClosed : ∀ s : I, contour (s, 0) = contour (s, 1)) :
    ¬ (Nonempty (ChapterVIMovingPoleAvoidance contour chapterVIDInsidePolePath) ∧
      Nonempty (ChapterVIMovingPoleAvoidance contour chapterVIDOutsidePolePath)) :=
  chapterVID_not_both_movingPoleAvoidances contour
    chapterVIDInsidePolePath chapterVIDOutsidePolePath hcontourClosed

end PoincareChapterVI
