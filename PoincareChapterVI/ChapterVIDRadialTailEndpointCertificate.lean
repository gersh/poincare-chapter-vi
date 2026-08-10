/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.ChapterVIDRadialTailEndpointSemantics
import PoincareChapterVI.ChapterVIDRadialTailCenteredCertificate
import PoincareChapterVI.ChapterVIDRadialTailEndpointKernel

namespace PoincareChapterVI
namespace ChapterVIDRadialTailEndpointTrace

open Complex Real Set
open scoped unitInterval
open ChapterVIFieldExpression Expr
open ChapterVIDRadialTailBaseCenteredSemantics
open ChapterVIDRadialTailTaylorSemantics
open ChapterVILeanCompCertAffineTrace
open ChapterVIDRadialTailCellInputTrace
open ChapterVIDRadialTailBaseCenteredAffineTrace
open ChapterVIDRadialTailEndpointCompiledGrid

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def unitPoint (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) : I := ⟨x, hx⟩

theorem eval_u_eq_exactU (side : ChapterVIDPinchingArcSide) (x : ℝ)
    (hx : x ∈ Icc (0 : ℝ) 1) :
    (u side).eval (exactValues side x) = exactU side (unitPoint x hx) 1 := by
  have hU := exactU_eq side (unitPoint x hx) (1 : I)
  change (u side).eval (exactValues side x) =
    exactU side (unitPoint x hx) ((1 : I) : ℝ)
  rw [hU, chapterVIDCertificateContourRadiusReal_eq,
    chapterVIDCertificateContourRadius_one, chapterVIDCollisionLift_eq_neg_norm,
    ← exactUnit_eq]
  cases side <;>
    simp [u, unit, quarter, r, t, collision, imaginaryUnit, exactValues,
      exactUnit, exactQuarter, unitPoint, Expr.eval] <;>
      rw [chapterVIDCollisionLift_eq_neg_norm] <;>
      simp only [norm_neg, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg _)] <;> ring

theorem eval_argument_eq_exactArgument (side : ChapterVIDPinchingArcSide) (x : ℝ)
    (hx : x ∈ Icc (0 : ℝ) 1) :
    (argument side).eval (baseValues x) = exactArgument side (unitPoint x hx) 1 := by
  rw [exactArgument_eq]
  unfold argument chapterVIDRootExponentialArgument
  have hu : (u side).eval (baseValues x) = exactU side (unitPoint x hx) 1 := by
    rw [show (u side).eval (baseValues x) = (u side).eval (exactValues side x) by
      cases side <;> rfl]
    exact eval_u_eq_exactU side x hx
  simp only [Expr.eval_mul, Expr.eval_sub, Expr.eval_pow, Expr.eval_inv, Expr.eval_var,
    Expr.eval_div]
  rw [hu]
  simp [r, collision, baseValues, Expr.eval]
  ring

theorem endpoint_argument_norm_le_one_third (side : ChapterVIDPinchingArcSide)
    (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    ‖exactArgument side (unitPoint x hx) 1‖ ≤ 1 / 3 := by
  have hprefix :
      (ChapterVIDPinchingArcPrefixCompiledGrid.prefixEnd : ℝ) ≤ (1 : ℝ) :=
    ChapterVIDPinchingArcPrefixCompiledGrid.prefixEnd_mem_Icc.2
  rcases ChapterVIDRadialTailCenteredCertificate.exists_radial_row
      (s := (1 : I)) hprefix with
    ⟨row, hrow⟩
  rcases ChapterVIDRadialTailCenteredCertificate.exists_radial_subcell row hrow with
    ⟨radial, hs⟩
  rcases ChapterVIDRadialTailCenteredCertificate.exists_angular_cell side row
      (unitPoint x hx) with ⟨angular, ht⟩
  exact ChapterVIDRadialTailCenteredCertificate.argument_norm_le_one_third
    side row radial angular (unitPoint x hx) hs ht

private theorem rectangle_real_contains {interval : ChapterVISignedDyadicInterval 40}
    {value : ℝ} (h : interval.Contains value) :
    (realRectangle interval).Contains (value : ℂ) := by
  constructor
  · simpa [realRectangle] using h
  · simpa [realRectangle, ChapterVIDRadialTailBaseConstants.zeroInterval] using
      ChapterVISignedDyadicInterval.pointInt_contains 40 0

private theorem rectangle_zero_contains :
    ChapterVIDRadialTailCellInputTrace.zeroRectangle.Contains (0 : ℂ) := by
  simpa [ChapterVIDRadialTailCellInputTrace.zeroRectangle] using
    ChapterVISignedDyadicComplexRectangle.pointInt_contains 40 0

theorem normalized_rational_cell {a b : ℚ} {x : ℝ}
    (hab : (a : ℝ) < b) (hx : x ∈ Icc (a : ℝ) (b : ℝ)) :
    |(x - ((a + b) / 2 : ℚ)) / ((b - a) / 2 : ℚ)| ≤ 1 := by
  rw [abs_le]
  have hpos : 0 < ((b : ℝ) - a) / 2 := by linarith
  push_cast at *
  constructor
  · rw [le_div_iff₀ hpos]
    nlinarith [hx.1]
  · rw [div_le_iff₀ hpos]
    nlinarith [hx.2]

theorem rationalTModel_contains {a b : ℚ} {x : ℝ}
    (hab : (a : ℝ) < b) (hx : x ∈ Icc (a : ℝ) (b : ℝ)) :
    (rationalTModel a b).Contains 0
      ((x - ((a + b) / 2 : ℚ)) / ((b - a) / 2 : ℚ)) (x : ℂ) := by
  let c : ℝ := (((a + b) / 2 : ℚ) : ℝ)
  let h : ℝ := (((b - a) / 2 : ℚ) : ℝ)
  refine ⟨c, 0, h, 0, ?_, rectangle_zero_contains, ?_, rectangle_zero_contains, ?_⟩
  · exact rectangle_real_contains (enclose_contains ((a + b) / 2))
  · exact rectangle_real_contains (enclose_contains ((b - a) / 2))
  · dsimp [c, h]
    push_cast
    norm_num
    norm_cast
    have hden : ((((b - a) / 2 : ℚ) : ℝ)) ≠ 0 := by
      push_cast
      linarith
    have hdiff : (((b - a : ℚ) : ℝ)) ≠ 0 := by
      push_cast
      linarith
    have hdiffC : (((b - a : ℚ) : ℂ)) ≠ 0 := by
      exact_mod_cast hdiff
    field_simp [hden, hdiff]
    ring

theorem pValue_one : pValue 1 = chapterVIDCriticalParameterSixthRoot := by
  unfold pValue chapterVIDCriticalParameterSixthRoot chapterVIDCertificateParameterReal
  norm_num

theorem exactZeta_one : exactZeta 1 = chapterVIDZRootBase := by
  unfold exactZeta pValue chapterVIDZRootBase
    chapterVIPositiveRealCubicLift chapterVIPositiveRealCubicValue
    chapterVIDCertificateParameterReal
  rw [max_eq_left chapterVIDCriticalParameterModulus_pos.le]
  norm_num
  have hr : (chapterVIDCriticalParameterModulus ^ (1 / 6 : ℝ)) ^ (2 : ℕ) =
      chapterVIDCriticalParameterModulus ^ (1 / 3 : ℝ) := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul chapterVIDCriticalParameterModulus_pos.le]
    norm_num
  exact_mod_cast hr

/-- The five-variable endpoint expression is Poincare's literal collision-factor product at
the endpoint parameter. -/
theorem endpointComplex_eq_exact_product
    (side : ChapterVIDPinchingArcSide) (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    endpointComplex side x =
      exactFactorPlus side (unitPoint x hx) 1 *
        exactFactorMinus side (unitPoint x hx) 1 := by
  have hu := eval_u_eq_exactU side x hx
  have harg : (argument side).eval (exactValues side x) =
      exactArgument side (unitPoint x hx) 1 := by
    rw [argument_eval_exact_eq_base]
    exact eval_argument_eq_exactArgument side x hx
  have huNe : exactU side (unitPoint x hx) 1 ≠ 0 := by
    change exactU side (unitPoint x hx) ((1 : I) : ℝ) ≠ 0
    rw [exactU_eq]
    apply mul_ne_zero
    · exact Complex.ofReal_ne_zero.mpr
        (chapterVIDRadialTailRealInputs_pos (by norm_num) (by norm_num)).2.ne'
    · intro hzero
      have hn := congrArg norm hzero
      rw [chapterVIDRadialTailFixedUnit,
        chapterVIDRationalPinchingArcUnit_norm side (unitPoint x hx)] at hn
      norm_num at hn
  have hζNe : exactZeta 1 ≠ 0 := by
    rw [exactZeta_one]
    exact chapterVIDZRootBase_ne_zero
  have hanomaly : (anomaly side).eval (exactValues side x) =
      exactAnomaly side (unitPoint x hx) 1 := by
    change chapterVIDY * Complex.exp ((argument side).eval (baseValues x)) *
      ((u side).eval (exactValues side x) * chapterVIDCollisionLift⁻¹) = _
    rw [hu, eval_argument_eq_exactArgument side x hx]
    unfold exactAnomaly exactMultiplierDelta exactExpRelative
    rw [exactZeta_one, div_self chapterVIDZRootBase_ne_zero]
    ring
  unfold endpointComplex radicand
  rw [Expr.eval_mul]
  congr 1
  · rw [exactFactorPlus_eq side (unitPoint x hx) 1 hζNe huNe]
    unfold factorPlus chapterVIDRadialTailFactorPlus
    simp only [Expr.eval_sub, Expr.eval_div, Expr.eval_add, Expr.eval_mul,
      Expr.eval_pow, Expr.eval_inv, Expr.eval_ofNat, Expr.eval_integer]
    rw [hu, hanomaly, exactAnomaly_eq]
    norm_num [Expr.eval]
    ring
  · rw [exactFactorMinus_eq]
    unfold factorMinus chapterVIDRadialTailFactorMinus
    simp only [Expr.eval_sub, Expr.eval_div, Expr.eval_add, Expr.eval_mul,
      Expr.eval_pow, Expr.eval_inv, Expr.eval_ofNat, Expr.eval_integer]
    rw [hu, hanomaly, exactAnomaly_eq]
    norm_num [Expr.eval]
    ring

theorem endpointComplex_eq_pinchingArcRadicand
    (side : ChapterVIDPinchingArcSide) (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    endpointComplex side x =
      chapterVIDPinchingArcRadicand side (1, unitPoint x hx) := by
  let tx : I := unitPoint x hx
  have huNe : exactU side tx 1 ≠ 0 := by
    change exactU side tx ((1 : I) : ℝ) ≠ 0
    rw [exactU_eq]
    apply mul_ne_zero
    · exact Complex.ofReal_ne_zero.mpr
        (chapterVIDRadialTailRealInputs_pos (by norm_num) (by norm_num)).2.ne'
    · intro hzero
      have hn := congrArg norm hzero
      rw [chapterVIDRadialTailFixedUnit,
        chapterVIDRationalPinchingArcUnit_norm side tx] at hn
      norm_num at hn
  have hζNe : exactZeta 1 ≠ 0 := by
    rw [exactZeta_one]
    exact chapterVIDZRootBase_ne_zero
  rw [endpointComplex_eq_exact_product side x hx,
    exactFactorPlus_eq side tx 1 hζNe huNe, exactFactorMinus_eq,
    chapterVIDRadialTailFactorPlus_eq hζNe huNe,
    chapterVIDRadialTailFactorMinus_eq hζNe huNe,
    ← chapterVIDRootCoordinateRadicand_eq_factors,
    ← chapterVIDRadialTailRadicandReal_eq side tx 1]
  unfold chapterVIDRadialTailRadicandReal
  change chapterVIDRootCoordinateRadicand (exactZeta ((1 : I) : ℝ))
      (exactU side tx ((1 : I) : ℝ)) = _
  rw [exactU_eq, exactZeta_eq]
  exact (chapterVIDRadialTailRealInputs_pos (by norm_num) (by norm_num)).1

def endpointRoot (side : ChapterVIDPinchingArcSide) (x : ℝ) : ℂ :=
  chapterVIDRootCoordinateRadicand chapterVIDZRootBase
    ((u side).eval (exactValues side x))

theorem exactU_endpoint_ne_zero (side : ChapterVIDPinchingArcSide)
    (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    exactU side (unitPoint x hx) 1 ≠ 0 := by
  change exactU side (unitPoint x hx) ((1 : I) : ℝ) ≠ 0
  rw [exactU_eq]
  apply mul_ne_zero
  · exact Complex.ofReal_ne_zero.mpr
      (chapterVIDRadialTailRealInputs_pos (by norm_num) (by norm_num)).2.ne'
  · intro hzero
    have hn := congrArg norm hzero
    rw [chapterVIDRadialTailFixedUnit,
      chapterVIDRationalPinchingArcUnit_norm side (unitPoint x hx)] at hn
    norm_num at hn

theorem endpointComplex_eq_endpointRoot (side : ChapterVIDPinchingArcSide)
    (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    endpointComplex side x = endpointRoot side x := by
  rw [endpointComplex_eq_exact_product side x hx,
    exactFactorPlus_eq side (unitPoint x hx) 1
      (by rw [exactZeta_one]; exact chapterVIDZRootBase_ne_zero)
      (exactU_endpoint_ne_zero side x hx),
    exactFactorMinus_eq,
    chapterVIDRadialTailFactorPlus_eq
      (by rw [exactZeta_one]; exact chapterVIDZRootBase_ne_zero)
      (exactU_endpoint_ne_zero side x hx),
    chapterVIDRadialTailFactorMinus_eq
      (by rw [exactZeta_one]; exact chapterVIDZRootBase_ne_zero)
      (exactU_endpoint_ne_zero side x hx),
    ← chapterVIDRootCoordinateRadicand_eq_factors, exactZeta_one,
    ← eval_u_eq_exactU side x hx]
  rfl

theorem endpoint_u_upper_one :
    (u .upper).eval (exactValues .upper 1) = chapterVIDCollisionLift := by
  let hx : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := by constructor <;> norm_num
  calc
    _ = exactU .upper (unitPoint 1 hx) 1 := eval_u_eq_exactU .upper 1 hx
    _ = chapterVIDCollisionLift := by
      change exactU .upper (unitPoint 1 hx) ((1 : I) : ℝ) = _
      rw [exactU_eq, chapterVIDCertificateContourRadiusReal_eq,
        chapterVIDCertificateContourRadius_one, chapterVIDCollisionLift_eq_neg_norm]
      simp [unitPoint, chapterVIDRadialTailFixedUnit, chapterVIDRationalPinchingArcUnit,
        chapterVIDRationalUnitQuarter, norm_neg, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg chapterVIDCollisionLift), Complex.I_mul_I]
      norm_num [div_eq_mul_inv]

theorem endpoint_u_lower_zero :
    (u .lower).eval (exactValues .lower 0) = chapterVIDCollisionLift := by
  let hx : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by constructor <;> norm_num
  calc
    _ = exactU .lower (unitPoint 0 hx) 1 := eval_u_eq_exactU .lower 0 hx
    _ = chapterVIDCollisionLift := by
      change exactU .lower (unitPoint 0 hx) ((1 : I) : ℝ) = _
      rw [exactU_eq, chapterVIDCertificateContourRadiusReal_eq,
        chapterVIDCertificateContourRadius_one, chapterVIDCollisionLift_eq_neg_norm]
      simp [unitPoint, chapterVIDRadialTailFixedUnit, chapterVIDRationalPinchingArcUnit,
        chapterVIDRationalUnitQuarter, norm_neg, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg chapterVIDCollisionLift)]

theorem base_radicand_derivative_zero (udot : ℂ) :
    chapterVIDRadialTailRadicandDerivative chapterVIDZRootBase
      chapterVIDCollisionLift 0 udot = 0 := by
  have hplusDerivative :
      chapterVIDRadialTailFactorPlusDerivative chapterVIDZRootBase
        chapterVIDCollisionLift 0 udot =
      chapterVIDRootCoordinateCollisionFactorPlusDerivative chapterVIDZRootBase
        chapterVIDCollisionLift * udot := by
    unfold chapterVIDRadialTailFactorPlusDerivative
      chapterVIDRadialTailAnomalyDerivative
      chapterVIDRootCoordinateCollisionFactorPlusDerivative
      chapterVIDRootSecondAnomalyLogDerivative chapterVIDRootSecondAnomaly
    ring
  have hplus : chapterVIDRadialTailFactorPlus chapterVIDZRootBase
      chapterVIDCollisionLift = 0 := by
    rw [chapterVIDRadialTailFactorPlus_eq chapterVIDZRootBase_ne_zero
      chapterVIDCollisionLift_ne_zero]
    exact chapterVIDRootCoordinateCollisionFactorPlus_base
  unfold chapterVIDRadialTailRadicandDerivative
  rw [hplusDerivative, chapterVIDRootCoordinateCollisionFactorPlusDerivative_base,
    hplus]
  ring

theorem endpointFirst_upper_one : endpointFirst .upper 1 = 0 := by
  let udot := (u .upper).directionalEval (exactValues .upper 1)
    (endpointVelocity .upper 1)
  have hroot : HasDerivAt (endpointRoot .upper) 0 1 := by
    have h := hasDerivAt_chapterVIDRootCoordinateRadicand_comp
      (hasDerivAt_const (x := (1 : ℝ)) chapterVIDZRootBase)
      (hasDerivAt_uEval .upper 1) chapterVIDZRootBase_ne_zero
      (by rw [endpoint_u_upper_one]; exact chapterVIDCollisionLift_ne_zero)
    rw [endpoint_u_upper_one, base_radicand_derivative_zero] at h
    exact h
  have hsemantic : HasDerivWithinAt (endpointComplex .upper) (endpointFirst .upper 1)
      (Icc (0 : ℝ) 1) 1 := (hasDerivAt_endpointComplex .upper 1).hasDerivWithinAt
  have hsame : HasDerivWithinAt (endpointRoot .upper) (endpointFirst .upper 1)
      (Icc (0 : ℝ) 1) 1 := hsemantic.congr
    (fun x hx ↦ (endpointComplex_eq_endpointRoot .upper x hx).symm)
    (endpointComplex_eq_endpointRoot .upper 1 (by constructor <;> norm_num)).symm
  exact (uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 1) 1 (by constructor <;> norm_num)).eq_deriv
    (Icc (0 : ℝ) 1) hsame hroot.hasDerivWithinAt

theorem endpointFirst_lower_zero : endpointFirst .lower 0 = 0 := by
  let udot := (u .lower).directionalEval (exactValues .lower 0)
    (endpointVelocity .lower 0)
  have hroot : HasDerivAt (endpointRoot .lower) 0 0 := by
    have h := hasDerivAt_chapterVIDRootCoordinateRadicand_comp
      (hasDerivAt_const (x := (0 : ℝ)) chapterVIDZRootBase)
      (hasDerivAt_uEval .lower 0) chapterVIDZRootBase_ne_zero
      (by rw [endpoint_u_lower_zero]; exact chapterVIDCollisionLift_ne_zero)
    rw [endpoint_u_lower_zero, base_radicand_derivative_zero] at h
    exact h
  have hsemantic : HasDerivWithinAt (endpointComplex .lower) (endpointFirst .lower 0)
      (Icc (0 : ℝ) 1) 0 := (hasDerivAt_endpointComplex .lower 0).hasDerivWithinAt
  have hsame : HasDerivWithinAt (endpointRoot .lower) (endpointFirst .lower 0)
      (Icc (0 : ℝ) 1) 0 := hsemantic.congr
    (fun x hx ↦ (endpointComplex_eq_endpointRoot .lower x hx).symm)
    (endpointComplex_eq_endpointRoot .lower 0 (by constructor <;> norm_num)).symm
  exact (uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 1) 0 (by constructor <;> norm_num)).eq_deriv
    (Icc (0 : ℝ) 1) hsame hroot.hasDerivWithinAt

theorem endpoint_exact_inputs_contain
    (side : ChapterVIDPinchingArcSide) {a b : ℚ} {x : ℝ}
    (hab : (a : ℝ) < b) (hx : x ∈ Icc (a : ℝ) (b : ℝ))
    (ha : 0 ≤ (a : ℝ)) (hb : (b : ℝ) ≤ 1) :
    let tx : I := unitPoint x ⟨ha.trans hx.1, hx.2.trans hb⟩
    let remainder := exactRemainder side tx 1
    let y := (x - ((a + b) / 2 : ℚ)) / ((b - a) / 2 : ℚ)
    ∀ i, (endpointInputsFromT side (rationalTModel a b) i).Contains 0 y
      (exactInputs tx 1 remainder i) := by
  dsimp
  have hy := normalized_rational_cell hab hx
  have harg := endpoint_argument_norm_le_one_third side x ⟨ha.trans hx.1, hx.2.trans hb⟩
  have hrem : ‖exactRemainder side
      (unitPoint x ⟨ha.trans hx.1, hx.2.trans hb⟩) 1‖ ≤ (1 / 3 : ℝ) ^ 6 / 512 := by
    unfold exactRemainder
    calc
      _ ≤ ‖exactArgument side (unitPoint x ⟨ha.trans hx.1, hx.2.trans hb⟩) 1‖ ^ 6 / 512 :=
        ChapterVILeanCompCertHighOrderAnomalyTrace.norm_exp_sub_expPolynomial_le
          (harg.trans (by norm_num))
      _ ≤ (1 / 3 : ℝ) ^ 6 / 512 := by gcongr
  intro i
  fin_cases i <;> simp [endpointInputsFromT,
    ChapterVIDRadialTailBaseCenteredAffineTrace.inputModels, exactInputs]
  · rw [pValue_one]
    exact ChapterVIDRadialTailBaseConstantTrace.pBase_contains 0 _
  · convert rationalTModel_contains hab hx using 1
    all_goals try rfl
    all_goals push_cast <;> ring
  · exact remainderModel_contains hrem 0 _
  · convert ChapterVIDRadialTailBaseConstantTrace.qdot_contains 0 _ using 1 <;>
      push_cast <;> ring
  · convert ChapterVIDRadialTailBaseConstantTrace.cdot_contains 0 _ (by norm_num) hy using 1 <;>
      push_cast <;> ring
  · exact ChapterVIDRadialTailCenteredCertificate.imaginaryUnit_contains 0 _
  · exact ChapterVIDRadialTailBaseConstantTrace.collisionModel_contains 0 _
  · apply ChapterVIDRadialTailBaseConstantTrace.collisionInv_contains 0 _ (by norm_num)
    convert hy using 1 <;> push_cast <;> ring
  · apply ChapterVIDRadialTailBaseConstantTrace.collisionSq_contains 0 _ (by norm_num)
    convert hy using 1 <;> push_cast <;> ring
  · simpa [collisionLift_inv_pow_three] using
      ChapterVIDRadialTailBaseConstantTrace.collisionInvCube_contains 0 _ (by norm_num)
        (by convert hy using 1 <;> push_cast <;> ring)
  · simpa [inv_pow] using
      ChapterVIDRadialTailBaseConstantTrace.collisionInvFourth_contains 0 _ (by norm_num)
        (by convert hy using 1 <;> push_cast <;> ring)
  · simpa [chapterVIDY_eq_ofReal] using
      ChapterVIDRadialTailBaseConstantTrace.yBase_contains 0 _
  · exact ChapterVIDRadialTailCenteredCertificate.zetaBase_contains 0 _
  all_goals exact zero_contains 40 0 _

theorem exponential_box_contains
    (side : ChapterVIDPinchingArcSide) {a b : ℚ} {x : ℝ}
    (hab : (a : ℝ) < b) (hx : x ∈ Icc (a : ℝ) (b : ℝ))
    (ha : 0 ≤ (a : ℝ)) (hb : (b : ℝ) ≤ 1)
    (hall : ∀ operation ∈
      (ChapterVIDRadialTailBaseCenteredAffineTrace.trace side
        (endpointInputsFromT side (rationalTModel a b))).operations, operation.Sound) :
    (boxesFromT side (rationalTModel a b) 3).Contains
      (Complex.exp ((argument side).eval (baseValues x))) := by
  let tx : I := unitPoint x ⟨ha.trans hx.1, hx.2.trans hb⟩
  let y : ℝ := (x - ((a + b) / 2 : ℚ)) / ((b - a) / 2 : ℚ)
  have hy : |y| ≤ 1 := normalized_rational_cell hab hx
  have hp := ProgramTrace.outputs_contain_of_allSound (by norm_num : |(0 : ℝ)| ≤ 1) hy hall
    (endpoint_exact_inputs_contain side hab hx ha hb) 27
  have heval := evalProgram_exactState side tx 1 27 (by norm_num
    [ChapterVIDRadialTailBaseCenteredProgram.program])
  have hout : ((ChapterVIDRadialTailBaseCenteredAffineTrace.trace side
      (endpointInputsFromT side (rationalTModel a b))).outputs 27).Contains 0 y
      (exactExpRelative side tx 1) := by
    rw [heval] at hp
    exact hp
  have hrange := Model.range_contains (by norm_num : |(0 : ℝ)| ≤ 1) hy hout
  change ((ChapterVIDRadialTailBaseCenteredAffineTrace.trace side
    (endpointInputsFromT side (rationalTModel a b))).outputs 27).range.Contains _
  convert hrange using 1
  rw [exactExpRelative, ← eval_argument_eq_exactArgument side x
    ⟨ha.trans hx.1, hx.2.trans hb⟩]

/-- Every analytic endpoint input is enclosed by the corresponding rectangular box used by the
jet checker.  The only nonconstant coordinate is the rational cell coordinate. -/
theorem endpoint_boxes_contain
    (side : ChapterVIDPinchingArcSide) {a b : ℚ} {x : ℝ}
    (hab : (a : ℝ) < b) (hx : x ∈ Icc (a : ℝ) (b : ℝ))
    (ha : 0 ≤ (a : ℝ)) (hb : (b : ℝ) ≤ 1)
    (hall : ∀ operation ∈
      (ChapterVIDRadialTailBaseCenteredAffineTrace.trace side
        (endpointInputsFromT side (rationalTModel a b))).operations, operation.Sound) :
    ∀ i, (boxesFromT side (rationalTModel a b) i).Contains
      (exactValues side x i) := by
  have hy := normalized_rational_cell hab hx
  intro i
  fin_cases i
  · exact Model.range_contains (by norm_num : |(0 : ℝ)| ≤ 1) hy
      (rationalTModel_contains hab hx)
  · exact Model.range_contains (by norm_num : |(0 : ℝ)| ≤ 1) hy
      (by simpa [exactValues] using
        ChapterVIDRadialTailBaseConstantTrace.collisionModel_contains 0 _)
  · exact Model.range_contains (by norm_num : |(0 : ℝ)| ≤ 1) hy
      (by simpa [exactValues] using
        ChapterVIDRadialTailBaseConstantTrace.yBase_contains 0 _)
  · simpa [exactValues] using exponential_box_contains side hab hx ha hb hall
  · exact Model.range_contains (by norm_num : |(0 : ℝ)| ≤ 1) hy
      (by simpa [exactValues] using
        ChapterVIDRadialTailCenteredCertificate.imaginaryUnit_contains 0 _)

theorem velocity_boxes_contain
    (side : ChapterVIDPinchingArcSide) {a b : ℚ} {x : ℝ}
    (hab : (a : ℝ) < b) (hx : x ∈ Icc (a : ℝ) (b : ℝ))
    (ha : 0 ≤ (a : ℝ)) (hb : (b : ℝ) ≤ 1)
    (hallBase : ∀ operation ∈
      (ChapterVIDRadialTailBaseCenteredAffineTrace.trace side
        (endpointInputsFromT side (rationalTModel a b))).operations, operation.Sound)
    (hallVelocity : ∀ i operation,
      operation ∈ (proposeTrace (boxesFromT side (rationalTModel a b))
        (velocity side i)).operations → operation.Sound) :
    ∀ i, (velocityBoxesFromT side (rationalTModel a b) i).Contains
      (endpointVelocity side x i) := by
  intro i
  rw [endpointVelocity_eq]
  exact Trace.output_contains_of_allSound _ (hallVelocity i)
    (endpoint_boxes_contain side hab hx ha hb hallBase)

private theorem positive_of_rectangle_lower_positive
    {rectangle : ChapterVISignedDyadicComplexRectangle 40} {z : ℂ}
    (hlower : 0 < rectangle.real.lower) (hz : rectangle.Contains z) :
    0 < z.re := by
  have hscale := ChapterVISignedDyadicInterval.scale_pos 40
  have hdyadic : 0 < (rectangle.real.lower : ℝ) /
      ChapterVISignedDyadicInterval.scale 40 := by
    exact div_pos (by exact_mod_cast hlower) hscale
  exact hdyadic.trans_le hz.1.1

/-- The finite jet table proves strict convexity throughout every upper collision-collar cell. -/
theorem upper_endpointSecond_pos (k : Fin 63) {x : ℝ}
    (hx : x ∈ Icc (upperLocalStart k : ℝ) (upperLocalEnd k : ℝ)) :
    0 < (endpointSecond .upper x).re := by
  have hab : (upperLocalStart k : ℝ) < (upperLocalEnd k : ℝ) := by
    simp [upperLocalStart, upperLocalEnd]
    linarith
  have ha : 0 ≤ (upperLocalStart k : ℝ) := by
    simp [upperLocalStart]
    positivity
  have hb : (upperLocalEnd k : ℝ) ≤ 1 := by
    simp [upperLocalEnd]
    rw [div_le_one (by norm_num : (0 : ℝ) < 1024)]
    have hk : (k.val : ℝ) ≤ 62 := by exact_mod_cast (Nat.le_pred_of_lt k.isLt)
    linarith
  have hboxes := endpoint_boxes_contain .upper hab hx ha hb
    (ChapterVIDRadialTailEndpointCompiledGrid.upper_base_operations_sound k)
  have hvelocity := velocity_boxes_contain .upper hab hx ha hb
    (ChapterVIDRadialTailEndpointCompiledGrid.upper_base_operations_sound k)
    (ChapterVIDRadialTailEndpointCompiledGrid.upper_velocity_operations_sound k)
  have hjet := JetTrace.outputs_contain_of_allSound
    (secondJetFromT .upper (upperLocalStart k) (upperLocalEnd k))
    (ChapterVIDRadialTailEndpointCompiledGrid.upper_curvature_operations_sound k)
    hboxes hvelocity
  apply positive_of_rectangle_lower_positive
    (ChapterVIDRadialTailEndpointCompiledGrid.upper_curvature_positive k)
  rw [endpointSecond_eq_directional_first]
  exact hjet.2

/-- The one lower collision-collar jet cell has strictly positive second derivative. -/
theorem lower_endpointSecond_pos {x : ℝ} (hx : x ∈ Icc (0 : ℝ) (1 / 1024 : ℝ)) :
    0 < (endpointSecond .lower x).re := by
  have hab : (((0 : ℚ) : ℝ)) < (((1 / 1024 : ℚ) : ℝ)) := by norm_num
  have hx' : x ∈ Icc ((0 : ℚ) : ℝ) (((1 / 1024 : ℚ) : ℝ)) := by
    convert hx using 1 <;> norm_num
  have hboxes := endpoint_boxes_contain .lower hab hx' (by norm_num) (by norm_num)
    ChapterVIDRadialTailEndpointCompiledGrid.lower_base_operations_sound
  have hvelocity := velocity_boxes_contain .lower hab hx' (by norm_num) (by norm_num)
    ChapterVIDRadialTailEndpointCompiledGrid.lower_base_operations_sound
    ChapterVIDRadialTailEndpointCompiledGrid.lower_velocity_operations_sound
  have hjet := JetTrace.outputs_contain_of_allSound
    (secondJetFromT .lower 0 (1 / 1024))
    ChapterVIDRadialTailEndpointCompiledGrid.lower_curvature_operations_sound
    hboxes hvelocity
  apply positive_of_rectangle_lower_positive
    ChapterVIDRadialTailEndpointCompiledGrid.lower_curvature_positive
  rw [endpointSecond_eq_directional_first]
  exact hjet.2

theorem endpointReal_upper_one : endpointReal .upper 1 = 0 := by
  unfold endpointReal
  rw [endpointComplex_eq_endpointRoot .upper 1 (by constructor <;> norm_num),
    endpointRoot, endpoint_u_upper_one, chapterVIDRootCoordinateRadicand_eq_factors,
    chapterVIDRootCoordinateCollisionFactorPlus_base]
  norm_num

theorem endpointReal_lower_zero : endpointReal .lower 0 = 0 := by
  unfold endpointReal
  rw [endpointComplex_eq_endpointRoot .lower 0 (by constructor <;> norm_num),
    endpointRoot, endpoint_u_lower_zero, chapterVIDRootCoordinateRadicand_eq_factors,
    chapterVIDRootCoordinateCollisionFactorPlus_base]
  norm_num

theorem upper_endpointSecond_pos_all {x : ℝ}
    (hx : x ∈ Icc (961 / 1024 : ℝ) 1) :
    0 < (endpointSecond .upper x).re := by
  by_cases hright : x = 1
  · subst x
    exact upper_endpointSecond_pos ⟨62, by omega⟩
      (by constructor <;> norm_num [upperLocalStart, upperLocalEnd])
  · let y : ℝ := 1024 * x - 961
    have hy0 : 0 ≤ y := by dsimp [y]; linarith [hx.1]
    have hy63 : y < 63 := by dsimp [y]; linarith [hx.2, lt_of_le_of_ne hx.2 hright]
    have hklt : Nat.floor y < 63 := (Nat.floor_lt hy0).2 (by exact_mod_cast hy63)
    let k : Fin 63 := ⟨Nat.floor y, hklt⟩
    exact upper_endpointSecond_pos k (by
      constructor
      · have hfloor := Nat.floor_le hy0
        change ((961 + k.val : ℚ) / 1024 : ℚ) ≤ x
        push_cast
        dsimp [k, y] at hfloor ⊢
        linarith
      · have hnext := Nat.lt_floor_add_one y
        change x ≤ ((962 + k.val : ℚ) / 1024 : ℚ)
        push_cast
        dsimp [k, y] at hnext ⊢
        linarith)

private theorem strictMonoOn_Icc_of_deriv_pos
    {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hcontinuous : ContinuousOn f (Icc a b))
    (hderiv : ∀ x ∈ Ioo a b, 0 < deriv f x) :
    StrictMonoOn f (Icc a b) := by
  exact strictMonoOn_of_deriv_pos (convex_Icc a b) hcontinuous fun x hx ↦
    hderiv x (by simpa [interior_Icc, hab] using hx)

theorem upper_local_endpointReal_nonneg {x : ℝ}
    (hx : x ∈ Icc (961 / 1024 : ℝ) 1) :
    0 ≤ endpointReal .upper x := by
  let g : ℝ → ℝ := fun y ↦ (endpointFirst .upper y).re
  have hg : StrictMonoOn g (Icc (961 / 1024 : ℝ) 1) := by
    apply strictMonoOn_Icc_of_deriv_pos (by norm_num)
    · intro y hy
      exact (hasSecondDerivAt_endpointReal .upper y).continuousAt.continuousWithinAt
    · intro y hy
      rw [(hasSecondDerivAt_endpointReal .upper y).deriv]
      exact upper_endpointSecond_pos_all ⟨hy.1.le, hy.2.le⟩
  have hf : StrictAntiOn (endpointReal .upper) (Icc (961 / 1024 : ℝ) 1) := by
    apply strictAntiOn_Icc_of_deriv_neg (by norm_num)
    · intro y hy
      exact (hasDerivAt_endpointReal .upper y).continuousAt.continuousWithinAt
    · intro y hy
      rw [(hasDerivAt_endpointReal .upper y).deriv]
      have hneg := hg ⟨hy.1.le, hy.2.le⟩ (by constructor <;> norm_num) hy.2
      simpa [g, endpointFirst_upper_one] using hneg
  by_cases hright : x = 1
  · rw [hright, endpointReal_upper_one]
  · have hlt : x < 1 := lt_of_le_of_ne hx.2 hright
    have h := hf hx (by constructor <;> norm_num) hlt
    rw [endpointReal_upper_one] at h
    exact h.le

theorem lower_local_endpointReal_nonneg {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) (1 / 1024 : ℝ)) :
    0 ≤ endpointReal .lower x := by
  let g : ℝ → ℝ := fun y ↦ (endpointFirst .lower y).re
  have hg : StrictMonoOn g (Icc (0 : ℝ) (1 / 1024 : ℝ)) := by
    apply strictMonoOn_Icc_of_deriv_pos (by norm_num)
    · intro y hy
      exact (hasSecondDerivAt_endpointReal .lower y).continuousAt.continuousWithinAt
    · intro y hy
      rw [(hasSecondDerivAt_endpointReal .lower y).deriv]
      exact lower_endpointSecond_pos ⟨hy.1.le, hy.2.le⟩
  have hf : StrictMonoOn (endpointReal .lower) (Icc (0 : ℝ) (1 / 1024 : ℝ)) := by
    apply strictMonoOn_Icc_of_deriv_pos (by norm_num)
    · intro y hy
      exact (hasDerivAt_endpointReal .lower y).continuousAt.continuousWithinAt
    · intro y hy
      rw [(hasDerivAt_endpointReal .lower y).deriv]
      have hpos := hg (by constructor <;> norm_num) ⟨hy.1.le, hy.2.le⟩ hy.1
      simpa [g, endpointFirst_lower_zero] using hpos
  by_cases hleft : x = 0
  · rw [hleft, endpointReal_lower_zero]
  · have hlt : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hleft)
    have h := hf (by constructor <;> norm_num) hx hlt
    rw [endpointReal_lower_zero] at h
    exact h.le

theorem normalized_direct_angular (side : ChapterVIDPinchingArcSide)
    (angular : Fin (angularCells side 0)) {x : ℝ}
    (hx : x ∈ Icc (angularStart side 0 angular : ℝ)
      (angularEnd side 0 angular : ℝ)) :
    |(x - angularCenter side 0 angular) / angularHalfWidth side 0 angular| ≤ 1 := by
  rw [abs_le]
  constructor <;> cases side <;> fin_cases angular <;>
    norm_num [angularCenter, angularHalfWidth, angularStart, angularEnd,
      angularCells, chapterVIQuadraticClusterNode] at hx ⊢ <;> linarith

theorem direct_angularStart_nonneg (side : ChapterVIDPinchingArcSide)
    (angular : Fin (angularCells side 0)) :
    0 ≤ (angularStart side 0 angular : ℝ) := by
  cases side <;> fin_cases angular <;>
    norm_num [angularStart, angularCells, chapterVIQuadraticClusterNode]

theorem direct_angularEnd_le_one (side : ChapterVIDPinchingArcSide)
    (angular : Fin (angularCells side 0)) :
    (angularEnd side 0 angular : ℝ) ≤ 1 := by
  cases side <;> fin_cases angular <;>
    norm_num [angularEnd, angularCells, chapterVIQuadraticClusterNode]

theorem direct_exact_inputs_contain
    (side : ChapterVIDPinchingArcSide) (angular : Fin (angularCells side 0))
    {x : ℝ} (hx : x ∈ Icc (angularStart side 0 angular : ℝ)
      (angularEnd side 0 angular : ℝ)) :
    let tx : I := unitPoint x (by
      constructor
      · exact (direct_angularStart_nonneg side angular).trans hx.1
      · exact hx.2.trans (direct_angularEnd_le_one side angular))
    let remainder := exactRemainder side tx 1
    let y := (x - angularCenter side 0 angular) / angularHalfWidth side 0 angular
    ∀ i, (directInputs side angular i).Contains 0 y
      (exactInputs tx 1 remainder i) := by
  dsimp
  have hy := normalized_direct_angular side angular hx
  let tx : I := unitPoint x ⟨(direct_angularStart_nonneg side angular).trans hx.1,
    hx.2.trans (direct_angularEnd_le_one side angular)⟩
  have harg := endpoint_argument_norm_le_one_third side x tx.property
  have hrem : ‖exactRemainder side tx 1‖ ≤ (1 / 3 : ℝ) ^ 6 / 512 := by
    unfold exactRemainder
    calc
      _ ≤ ‖exactArgument side tx 1‖ ^ 6 / 512 :=
        ChapterVILeanCompCertHighOrderAnomalyTrace.norm_exp_sub_expPolynomial_le
          (harg.trans (by norm_num))
      _ ≤ (1 / 3 : ℝ) ^ 6 / 512 := by gcongr
  intro i
  fin_cases i <;> simp [directInputs,
    ChapterVIDRadialTailBaseCenteredAffineTrace.inputModels, exactInputs]
  · rw [pValue_one]
    exact ChapterVIDRadialTailBaseConstantTrace.pBase_contains 0 _
  · exact tModel_contains side 0 angular hx
  · exact remainderModel_contains hrem 0 _
  · convert ChapterVIDRadialTailBaseConstantTrace.qdot_contains 0 _ using 1 <;>
      push_cast <;> ring
  · convert ChapterVIDRadialTailBaseConstantTrace.cdot_contains 0 _ (by norm_num) hy using 1 <;>
      push_cast <;> ring
  · exact ChapterVIDRadialTailCenteredCertificate.imaginaryUnit_contains 0 _
  · exact ChapterVIDRadialTailBaseConstantTrace.collisionModel_contains 0 _
  · apply ChapterVIDRadialTailBaseConstantTrace.collisionInv_contains 0 _ (by norm_num)
    exact hy
  · apply ChapterVIDRadialTailBaseConstantTrace.collisionSq_contains 0 _ (by norm_num)
    exact hy
  · simpa [collisionLift_inv_pow_three] using
      ChapterVIDRadialTailBaseConstantTrace.collisionInvCube_contains 0 _ (by norm_num) hy
  · simpa [inv_pow] using
      ChapterVIDRadialTailBaseConstantTrace.collisionInvFourth_contains 0 _ (by norm_num) hy
  · simpa [chapterVIDY_eq_ofReal] using
      ChapterVIDRadialTailBaseConstantTrace.yBase_contains 0 _
  · exact ChapterVIDRadialTailCenteredCertificate.zetaBase_contains 0 _
  all_goals exact zero_contains 40 0 _

/-- Semantic interpretation of one direct endpoint-table entry. -/
theorem direct_output_contains_exact_product
    (side : ChapterVIDPinchingArcSide) (angular : Fin (angularCells side 0))
    {x : ℝ} (hx : x ∈ Icc (angularStart side 0 angular : ℝ)
      (angularEnd side 0 angular : ℝ)) :
    (directOutput side angular).Contains
      (exactFactorPlus side (unitPoint x
          ⟨(direct_angularStart_nonneg side angular).trans hx.1,
            hx.2.trans (direct_angularEnd_le_one side angular)⟩) 1 *
       exactFactorMinus side (unitPoint x
          ⟨(direct_angularStart_nonneg side angular).trans hx.1,
            hx.2.trans (direct_angularEnd_le_one side angular)⟩) 1) := by
  let tx : I := unitPoint x
    ⟨(direct_angularStart_nonneg side angular).trans hx.1,
      hx.2.trans (direct_angularEnd_le_one side angular)⟩
  let y := (x - angularCenter side 0 angular) / angularHalfWidth side 0 angular
  have hy : |y| ≤ 1 := normalized_direct_angular side angular hx
  have hp := ProgramTrace.outputs_contain_of_allSound (by norm_num : |(0 : ℝ)| ≤ 1) hy
    (direct_program_operations_sound side angular)
    (direct_exact_inputs_contain side angular hx)
  have hplus := hp 51
  have hminus := hp 39
  rw [evalProgram_exactState side tx 1 51 (by norm_num
    [ChapterVIDRadialTailBaseCenteredProgram.program])] at hplus
  rw [evalProgram_exactState side tx 1 39 (by norm_num
    [ChapterVIDRadialTailBaseCenteredProgram.program])] at hminus
  have hproduct := proposeMul_output_contains (by norm_num : |(0 : ℝ)| ≤ 1) hy
    (direct_product_operations_sound side angular) hplus hminus
  have hrange := Model.range_contains (by norm_num : |(0 : ℝ)| ≤ 1) hy hproduct
  simpa [directOutput, directProductTrace, tx, exactState] using hrange

theorem upper_direct_endpointReal_pos (i : Fin 62) {x : ℝ}
    (hx : x ∈ Icc
      (angularStart .upper 0 ⟨i, by simp [angularCells]; omega⟩ : ℝ)
      (angularEnd .upper 0 ⟨i, by simp [angularCells]; omega⟩ : ℝ)) :
    0 < endpointReal .upper x := by
  let angular : Fin (angularCells .upper 0) :=
    ⟨i, by simp [angularCells]; omega⟩
  have hcontain := direct_output_contains_exact_product .upper angular hx
  have hpositive := positive_of_rectangle_lower_positive
    (upper_direct_positive i) hcontain
  unfold endpointReal
  rw [endpointComplex_eq_exact_product .upper x
    ⟨(direct_angularStart_nonneg .upper angular).trans hx.1,
      hx.2.trans (direct_angularEnd_le_one .upper angular)⟩]
  exact hpositive

theorem lower_direct_endpointReal_pos (i : Fin 124) {x : ℝ}
    (hx : x ∈ Icc
      (angularStart .lower 0 ⟨i + 4, by simp [angularCells]; omega⟩ : ℝ)
      (angularEnd .lower 0 ⟨i + 4, by simp [angularCells]; omega⟩ : ℝ)) :
    0 < endpointReal .lower x := by
  let angular : Fin (angularCells .lower 0) :=
    ⟨i + 4, by simp [angularCells]; omega⟩
  have hcontain := direct_output_contains_exact_product .lower angular hx
  have hpositive := positive_of_rectangle_lower_positive
    (lower_direct_positive i) hcontain
  unfold endpointReal
  rw [endpointComplex_eq_exact_product .lower x
    ⟨(direct_angularStart_nonneg .lower angular).trans hx.1,
      hx.2.trans (direct_angularEnd_le_one .lower angular)⟩]
  exact hpositive

theorem endpointReal_nonneg (side : ChapterVIDPinchingArcSide)
    (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    0 ≤ endpointReal side x := by
  cases side with
  | upper =>
      by_cases hlocal : (961 / 1024 : ℝ) ≤ x
      · exact upper_local_endpointReal_nonneg ⟨hlocal, hx.2⟩
      · have hstrict : x < (961 / 1024 : ℝ) := lt_of_not_ge hlocal
        let tx : I := unitPoint x hx
        obtain ⟨angular, hangular⟩ :=
          ChapterVIDRadialTailCenteredCertificate.exists_angular_cell .upper 0 tx
        change x ∈ Icc (angularStart .upper 0 angular : ℝ)
          (angularEnd .upper 0 angular : ℝ) at hangular
        have hi : angular.val < 62 := by
          by_contra hi
          have hi' : 62 ≤ angular.val := Nat.le_of_not_gt hi
          have hstart := hangular.1
          simp [angularStart, angularCells, chapterVIQuadraticClusterNode] at hstart
          have hcast : (62 : ℝ) ≤ angular.val := by exact_mod_cast hi'
          norm_num at hstrict
          nlinarith [sq_nonneg ((angular.val : ℝ) - 62)]
        let i : Fin 62 := ⟨angular.val, hi⟩
        have hangulareq :
            (⟨i, by simp [angularCells]; omega⟩ : Fin (angularCells .upper 0)) =
              angular := by ext; rfl
        exact (upper_direct_endpointReal_pos i (by simpa [hangulareq] using hangular)).le
  | lower =>
      by_cases hlocal : x ≤ (1 / 1024 : ℝ)
      · exact lower_local_endpointReal_nonneg ⟨hx.1, hlocal⟩
      · have hstrict : (1 / 1024 : ℝ) < x := lt_of_not_ge hlocal
        let tx : I := unitPoint x hx
        obtain ⟨angular, hangular⟩ :=
          ChapterVIDRadialTailCenteredCertificate.exists_angular_cell .lower 0 tx
        change x ∈ Icc (angularStart .lower 0 angular : ℝ)
          (angularEnd .lower 0 angular : ℝ) at hangular
        have hi : 4 ≤ angular.val := by
          by_contra hi
          have hi' : angular.val ≤ 3 := by omega
          have hend := hangular.2
          simp [angularEnd, angularCells, chapterVIQuadraticClusterNode] at hend
          have hcast : (angular.val : ℝ) ≤ 3 := by exact_mod_cast hi'
          have hnonneg : (0 : ℝ) ≤ angular.val := by positivity
          norm_num at hstrict
          nlinarith [sq_nonneg ((angular.val : ℝ) - 3)]
        have hjlt : angular.val - 4 < 124 := by
          have := angular.isLt
          simp [angularCells] at this
          omega
        let i : Fin 124 := ⟨angular.val - 4, hjlt⟩
        have hangulareq :
            (⟨i + 4, by simp [angularCells]; omega⟩ : Fin (angularCells .lower 0)) =
              angular := by ext; dsimp [i]; omega
        exact (lower_direct_endpointReal_pos i (by simpa [hangulareq] using hangular)).le

/-- The endpoint table, completed by the certified convex collision collars, proves the endpoint
nonnegativity hypothesis required by the radial-tail reduction. -/
theorem chapterVIDRadialTail_endpoint_nonneg
    (side : ChapterVIDPinchingArcSide) (t : I) :
    0 ≤ (chapterVIDPinchingArcRadicand side (1, t)).re := by
  have h := endpointReal_nonneg side t t.property
  unfold endpointReal at h
  rw [endpointComplex_eq_pinchingArcRadicand side t t.property] at h
  exact h

end
end ChapterVIDRadialTailEndpointTrace
end PoincareChapterVI
