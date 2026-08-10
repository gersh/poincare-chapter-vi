/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.ChapterVIDRadialTailCellInputTrace
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Convex.Deriv

/-! # Analytic semantics of the radial-tail Taylor inputs -/

noncomputable section

namespace PoincareChapterVI
namespace ChapterVIDRadialTailTaylorSemantics

set_option maxHeartbeats 0

open Real Set
open ChapterVILeanCompCertAffineTrace
open ChapterVIDRadialTailCellInputTrace

private theorem realRectangle_contains {interval : Interval} {value : ℝ}
    (hvalue : interval.Contains value) : (realRectangle interval).Contains (value : ℂ) := by
  constructor
  · simpa [realRectangle] using hvalue
  · simpa [realRectangle, ChapterVIDRadialTailBaseConstants.zeroInterval] using
      ChapterVISignedDyadicInterval.pointInt_contains 40 0

def pValue (s : ℝ) : ℝ :=
  chapterVIDCertificateParameterReal s ^ ((6 : ℝ)⁻¹)

def pVelocity (s : ℝ) : ℝ :=
  ((chapterVIDCriticalParameterModulus - 1) / 6) * (pValue s ^ 5)⁻¹

def pAcceleration (s : ℝ) : ℝ :=
  -5 * (chapterVIDCriticalParameterModulus - 1) ^ 2 / (36 * pValue s ^ 11)

theorem pValue_pos {s : ℝ} (hq : 0 < chapterVIDCertificateParameterReal s) :
    0 < pValue s := Real.rpow_pos_of_pos hq _

theorem pValue_pow_six {s : ℝ} (hq : 0 ≤ chapterVIDCertificateParameterReal s) :
    pValue s ^ 6 = chapterVIDCertificateParameterReal s := by
  exact Real.rpow_inv_natCast_pow hq (by norm_num)

theorem hasDerivAt_pValue {s : ℝ} (hq : 0 < chapterVIDCertificateParameterReal s) :
    HasDerivAt pValue (pVelocity s) s := by
  have h := (hasDerivAt_chapterVIDCertificateParameterReal s).rpow_const
    (p := (6 : ℝ)⁻¹) (Or.inl hq.ne')
  have hp := pValue_pos hq
  have hp6 := pValue_pow_six hq.le
  convert h using 1
  · rfl
  · unfold pVelocity pValue
    rw [Real.rpow_sub hq, Real.rpow_one]
    field_simp [hq.ne', hp.ne']
    unfold pValue at hp6
    convert congrArg (fun z : ℝ ↦ (chapterVIDCriticalParameterModulus - 1) * z) hp6.symm using 1 <;>
      ring

theorem hasDerivAt_pVelocity {s : ℝ} (hq : 0 < chapterVIDCertificateParameterReal s) :
    HasDerivAt pVelocity (pAcceleration s) s := by
  have hp := pValue_pos hq
  have hd := hasDerivAt_pValue hq
  have hinv := (hd.pow 5).inv (pow_ne_zero 5 hp.ne')
  have h := hinv.const_mul ((chapterVIDCriticalParameterModulus - 1) / 6)
  have h' : HasDerivAt
    (fun x ↦ ((chapterVIDCriticalParameterModulus - 1) / 6) * (pValue x ^ 5)⁻¹)
    (((chapterVIDCriticalParameterModulus - 1) / 6) *
      (-(5 * pValue s ^ (5 - 1) * pVelocity s) / (pValue s ^ 5) ^ 2)) s := by
    simpa only [Pi.pow_apply, Pi.inv_apply, Nat.cast_ofNat] using h
  have hcoefficient : pAcceleration s =
      ((chapterVIDCriticalParameterModulus - 1) / 6) *
        (-(5 * pValue s ^ (5 - 1) * pVelocity s) / (pValue s ^ 5) ^ 2) := by
    unfold pAcceleration pVelocity
    field_simp [hp.ne']
    ring
  rw [hcoefficient]
  exact h'

private theorem abs_sub_tangent_le
    {f f' f'' : ℝ → ℝ} {a b c s M h : ℝ}
    (hc : c ∈ Icc a b) (hs : s ∈ Icc a b)
    (hf : ∀ x ∈ Icc a b, HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ Icc a b, HasDerivAt f' (f'' x) x)
    (hbound : ∀ x ∈ Icc a b, |f'' x| ≤ M)
    (hdistance : ∀ x ∈ Icc a b, |x - c| ≤ h)
    (hM : 0 ≤ M) (hh : 0 ≤ h) :
    |f s - (f c + f' c * (s - c))| ≤ M * h ^ 2 := by
  have hderivDifference : ∀ x ∈ Icc a b, |f' x - f' c| ≤ M * h := by
    intro x hx
    have hlipschitz := (convex_Icc a b).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun y hy ↦ (hf' y hy).hasDerivWithinAt)
      (fun y hy ↦ by simpa [Real.norm_eq_abs] using hbound y hy) hc hx
    calc
      |f' x - f' c| = ‖f' x - f' c‖ := by rw [Real.norm_eq_abs]
      _ ≤ M * ‖x - c‖ := hlipschitz
      _ = M * |x - c| := by rw [Real.norm_eq_abs]
      _ ≤ M * h := mul_le_mul_of_nonneg_left (hdistance x hx) hM
  let g : ℝ → ℝ := fun x ↦ f x - f' c * x
  have hg : ∀ x ∈ Icc a b, HasDerivWithinAt g (f' x - f' c) (Icc a b) x := by
    intro x hx
    have hlinear : HasDerivAt (fun y : ℝ ↦ f' c * y) (f' c) x := by
      simpa using (hasDerivAt_id x).const_mul (f' c)
    exact ((hf x hx).sub hlinear).hasDerivWithinAt
  have hlipschitz := (convex_Icc a b).norm_image_sub_le_of_norm_hasDerivWithin_le hg
    (fun x hx ↦ by simpa [Real.norm_eq_abs] using hderivDifference x hx) hc hs
  calc
    |f s - (f c + f' c * (s - c))| = ‖g s - g c‖ := by
      simp only [g, Real.norm_eq_abs]
      congr 1
      ring
    _ ≤ M * h * ‖s - c‖ := hlipschitz
    _ = M * h * |s - c| := by rw [Real.norm_eq_abs]
    _ ≤ M * h * h := mul_le_mul_of_nonneg_left (hdistance s hs) (mul_nonneg hM hh)
    _ = M * h ^ 2 := by ring

def pLowerBound : Fin 6 → ℚ
  | 0 => 43 / 100
  | 1 => 39 / 100
  | 2 => 35 / 100
  | 3 => 32 / 100
  | 4 => 31 / 100
  | 5 => 3 / 10

private theorem row_interval_mem_Icc (row : Fin 6) (index : Fin 16)
    {s : ℝ} (hs : s ∈ Icc (radialStart row index : ℝ) (radialEnd row index : ℝ)) :
    s ∈ Icc (0 : ℝ) 1 := by
  constructor
  · have hstart : (0 : ℝ) ≤ radialStart row index := by
      fin_cases row <;> fin_cases index <;>
        norm_num [radialStart, rowStart, rowEnd, radialRow,
          chapterVICubicClusterNode]
    exact hstart.trans hs.1
  · have hend : (radialEnd row index : ℝ) ≤ 1 := by
      fin_cases row <;> fin_cases index <;>
        norm_num [radialEnd, rowStart, rowEnd, radialRow,
          chapterVICubicClusterNode]
    exact hs.2.trans hend

private theorem pValue_lower_bound (row : Fin 6) (index : Fin 16)
    {s : ℝ} (hs : s ∈ Icc (radialStart row index : ℝ) (radialEnd row index : ℝ)) :
    (pLowerBound row : ℝ) ≤ pValue s := by
  have hs01 := row_interval_mem_Icc row index hs
  have hq := (chapterVIDRadialTailRealInputs_pos hs01.1 hs01.2).1
  have hqD : (960379498 / (2 : ℝ) ^ 40) ≤
      chapterVIDCriticalParameterModulus := by
    simpa [ChapterVIDRadialTailBaseConstants.qD,
      ChapterVISignedDyadicInterval.Contains,
      ChapterVISignedDyadicInterval.toRealInterval,
      ChapterVISignedDyadicInterval.scale,
      ChapterVIRealInterval.Contains] using
        ChapterVIDRadialTailBaseConstants.qD_contains.1
  have hqLower : (pLowerBound row : ℝ) ^ 6 ≤ chapterVIDCertificateParameterReal s := by
    have hsEnd : s ≤ (rowEnd row : ℝ) := hs.2.trans (by
      fin_cases row <;> fin_cases index <;>
        norm_num [radialEnd, rowStart, rowEnd, radialRow, chapterVICubicClusterNode])
    have hsNonneg := hs01.1
    unfold chapterVIDCertificateParameterReal
    fin_cases row <;>
      norm_num [pLowerBound, rowEnd, radialRow, chapterVICubicClusterNode] at hsEnd ⊢ <;>
      nlinarith
  apply le_of_pow_le_pow_left₀ (by norm_num : 6 ≠ 0) (pValue_pos hq).le
  rw [pValue_pow_six hq.le]
  exact hqLower

private theorem pAcceleration_abs_le (row : Fin 6) (index : Fin 16)
    {s : ℝ} (hs : s ∈ Icc (radialStart row index : ℝ) (radialEnd row index : ℝ)) :
    |pAcceleration s| ≤ secondDerivativeBound row := by
  have hs01 := row_interval_mem_Icc row index hs
  have hq := (chapterVIDRadialTailRealInputs_pos hs01.1 hs01.2).1
  have hp := pValue_pos hq
  have hpLower := pValue_lower_bound row index hs
  have hqDLower : (960379498 / (2 : ℝ) ^ 40) ≤
      chapterVIDCriticalParameterModulus := by
    simpa [ChapterVIDRadialTailBaseConstants.qD,
      ChapterVISignedDyadicInterval.Contains,
      ChapterVISignedDyadicInterval.toRealInterval,
      ChapterVISignedDyadicInterval.scale,
      ChapterVIRealInterval.Contains] using
        ChapterVIDRadialTailBaseConstants.qD_contains.1
  have hqDUpper : chapterVIDCriticalParameterModulus ≤
      (960379499 / (2 : ℝ) ^ 40) := by
    simpa [ChapterVIDRadialTailBaseConstants.qD,
      ChapterVISignedDyadicInterval.Contains,
      ChapterVISignedDyadicInterval.toRealInterval,
      ChapterVISignedDyadicInterval.scale,
      ChapterVIRealInterval.Contains] using
        ChapterVIDRadialTailBaseConstants.qD_contains.2
  have hqdotAbs : |chapterVIDCriticalParameterModulus - 1| ≤ 1 := by
    rw [abs_of_nonpos]
    · linarith
    · linarith
  have hpow : (pLowerBound row : ℝ) ^ 11 ≤ pValue s ^ 11 := by
    have hlower : (0 : ℝ) ≤ pLowerBound row := by
      fin_cases row <;> norm_num [pLowerBound]
    exact pow_le_pow_left₀ hlower hpLower 11
  rw [pAcceleration, abs_div, abs_mul, abs_neg, abs_pow,
    abs_of_pos (mul_pos (by norm_num) (pow_pos hp 11))]
  norm_num only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 5)]
  rw [div_le_iff₀ (mul_pos (by norm_num) (pow_pos hp 11))]
  have hqdotSq : |chapterVIDCriticalParameterModulus - 1| ^ 2 ≤ 1 := by
    nlinarith [mul_self_le_mul_self (abs_nonneg _ ) hqdotAbs]
  calc
    5 * |chapterVIDCriticalParameterModulus - 1| ^ 2 ≤ 5 := by nlinarith
    _ ≤ (secondDerivativeBound row : ℝ) * (36 * (pLowerBound row : ℝ) ^ 11) := by
      fin_cases row <;> norm_num [secondDerivativeBound, pLowerBound]
    _ ≤ (secondDerivativeBound row : ℝ) * (36 * pValue s ^ 11) := by
      gcongr

private theorem normalized_parameter_bounds (row : Fin 6) (index : Fin 16)
    {s : ℝ} (hs : s ∈ Icc (radialStart row index : ℝ) (radialEnd row index : ℝ)) :
    let x := (s - radialCenter row index) / radialHalfWidth row index
    |x| ≤ 1 := by
  dsimp
  rw [abs_le]
  constructor <;> fin_cases row <;> fin_cases index <;>
    norm_num [radialCenter, radialHalfWidth, radialStart, radialEnd,
      rowStart, rowEnd, radialRow, chapterVICubicClusterNode] at hs ⊢ <;> linarith

theorem pModel_contains (row : Fin 6) (index : Fin 16)
    {s : ℝ} (hs : s ∈ Icc (radialStart row index : ℝ) (radialEnd row index : ℝ)) :
    let x := (s - radialCenter row index) / radialHalfWidth row index
    (pModel row index).Contains x 0 (pValue s : ℂ) := by
  dsimp
  let c : ℝ := radialCenter row index
  let h : ℝ := radialHalfWidth row index
  let x : ℝ := (s - c) / h
  let derivative := pVelocity c
  let residual := pValue s - (pValue c + derivative * (s - c))
  have hcellCenter : c ∈ Icc (radialStart row index : ℝ) (radialEnd row index : ℝ) := by
    fin_cases row <;> fin_cases index <;>
      norm_num [c, radialCenter, radialStart, radialEnd, rowStart, rowEnd,
        radialRow, chapterVICubicClusterNode]
  have hcenter := ChapterVIDRadialTailCellInputTrace.pCenter_contains row index
  have hradial := ChapterVIDRadialTailCellInputTrace.radialCoefficient_contains row index
  have hhpos : 0 < h := by
    fin_cases row <;> fin_cases index <;>
      norm_num [h, radialHalfWidth, radialStart, radialEnd, rowStart, rowEnd,
        radialRow, chapterVICubicClusterNode]
  have hnormalized : |x| ≤ 1 := by
    exact normalized_parameter_bounds row index hs
  have hTaylor : |residual| ≤ (secondDerivativeBound row : ℝ) * h ^ 2 := by
    dsimp [residual, derivative]
    apply abs_sub_tangent_le hcellCenter hs
    · intro y hy
      exact hasDerivAt_pValue
        (chapterVIDRadialTailRealInputs_pos
          (row_interval_mem_Icc row index hy).1 (row_interval_mem_Icc row index hy).2).1
    · intro y hy
      exact hasDerivAt_pVelocity
        (chapterVIDRadialTailRealInputs_pos
          (row_interval_mem_Icc row index hy).1 (row_interval_mem_Icc row index hy).2).1
    · exact fun y hy ↦ pAcceleration_abs_le row index hy
    · intro y hy
      rw [abs_le]
      constructor <;>
        dsimp [c, h, radialCenter, radialHalfWidth] at * <;>
        push_cast at * <;> linarith [hy.1, hy.2]
    · positivity
    · exact hhpos.le
  have hbudget : (secondDerivativeBound row : ℝ) * h ^ 2 ≤
      (errorBudget row index : ℝ) / ChapterVISignedDyadicInterval.scale 40 := by
    have henclose := (enclose_contains
      ((secondDerivativeBound row : ℚ) * radialHalfWidth row index ^ 2)).2
    change (secondDerivativeBound row : ℝ) * h ^ 2 ≤
      ((enclose ((secondDerivativeBound row : ℚ) * radialHalfWidth row index ^ 2)).upper + 1 : ℤ) /
        ChapterVISignedDyadicInterval.scale 40
    dsimp [h]
    have henclose' :
        (secondDerivativeBound row : ℝ) * (radialHalfWidth row index : ℝ) ^ 2 ≤
          ((enclose ((secondDerivativeBound row : ℚ) *
            radialHalfWidth row index ^ 2)).upper : ℝ) /
              ChapterVISignedDyadicInterval.scale 40 := by
      simpa [ChapterVISignedDyadicInterval.Contains,
        ChapterVISignedDyadicInterval.toRealInterval] using henclose
    exact henclose'.trans (by
      rw [div_le_div_iff_of_pos_right (ChapterVISignedDyadicInterval.scale_pos 40)]
      norm_num)
  have hresidualLower :
      -(errorBudget row index : ℝ) / ChapterVISignedDyadicInterval.scale 40 ≤ residual := by
    calc
      -(errorBudget row index : ℝ) / ChapterVISignedDyadicInterval.scale 40 =
          -((errorBudget row index : ℝ) / ChapterVISignedDyadicInterval.scale 40) := by ring
      _ ≤ -((secondDerivativeBound row : ℝ) * h ^ 2) := neg_le_neg hbudget
      _ ≤ residual := (abs_le.mp hTaylor).1
  have hresidualUpper : residual ≤
      (errorBudget row index : ℝ) / ChapterVISignedDyadicInterval.scale 40 := by
    have := (abs_le.mp hTaylor).2
    linarith
  have herror : (realRectangle
      ⟨-errorBudget row index, errorBudget row index⟩).Contains (residual : ℂ) := by
    apply realRectangle_contains
    exact ⟨by simpa [ChapterVISignedDyadicInterval.toRealInterval] using hresidualLower,
      by simpa [ChapterVISignedDyadicInterval.toRealInterval] using hresidualUpper⟩
  refine ⟨(pValue c : ℂ), (derivative * h : ℝ), 0, (residual : ℂ), ?_, ?_, ?_, ?_, ?_⟩
  · simpa [pModel, pValue, c] using realRectangle_contains hcenter
  · have hr := realRectangle_contains hradial
    convert (by simpa [pModel] using hr) using 1
    norm_cast
    dsimp [derivative, pVelocity, pValue, c, h]
    simp only [div_eq_mul_inv, mul_inv_rev]
    push_cast
    ring
  · simpa [pModel, zeroRectangle] using
      ChapterVISignedDyadicComplexRectangle.pointInt_contains 40 0
  · simpa [pModel] using herror
  · have hreconstruct :
        pValue s = pValue c + x * (derivative * h) + residual := by
      dsimp [x, residual]
      field_simp [hhpos.ne']
      ring
    have hc := congrArg (fun z : ℝ ↦ (z : ℂ)) hreconstruct
    simpa [x, c, h] using hc

theorem tModel_contains (side : ChapterVIDPinchingArcSide) (row : Fin 6)
    (index : Fin (angularCells side row)) {t : ℝ}
    (ht : t ∈ Icc (angularStart side row index : ℝ)
      (angularEnd side row index : ℝ)) :
    let y := (t - angularCenter side row index) / angularHalfWidth side row index
    (tModel side row index).Contains 0 y (t : ℂ) := by
  dsimp
  let c : ℝ := angularCenter side row index
  let h : ℝ := angularHalfWidth side row index
  let y : ℝ := (t - c) / h
  have hcells : 0 < angularCells side row := by
    cases side <;> fin_cases row <;> norm_num [angularCells]
  have hstartEnd : (angularStart side row index : ℝ) <
      (angularEnd side row index : ℝ) := by
    have hi : (index.val : ℚ) ^ 2 < ((index.val + 1 : ℕ) : ℚ) ^ 2 := by
      push_cast
      have hi0 : (0 : ℚ) ≤ index.val := by positivity
      nlinarith
    have hden : (0 : ℚ) < (angularCells side row : ℚ) ^ 2 := by positivity
    exact_mod_cast (div_lt_div_of_pos_right hi hden)
  have hhpos : 0 < h := by
    dsimp [h, angularHalfWidth]
    push_cast
    linarith
  have hy : |y| ≤ 1 := by
    rw [abs_le]
    constructor
    · rw [le_div_iff₀ hhpos]
      dsimp [y, c, h, angularCenter, angularHalfWidth] at *
      push_cast at *
      linarith [ht.1]
    · rw [div_le_iff₀ hhpos]
      dsimp [y, c, h, angularCenter, angularHalfWidth] at *
      push_cast at *
      linarith [ht.2]
  have hc := realRectangle_contains (enclose_contains (angularCenter side row index))
  have hh := realRectangle_contains (enclose_contains (angularHalfWidth side row index))
  refine ⟨(c : ℂ), 0, (h : ℂ), 0, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [tModel, c] using hc
  · simpa [tModel, zeroRectangle] using
      ChapterVISignedDyadicComplexRectangle.pointInt_contains 40 0
  · simpa [tModel, h] using hh
  · simpa [tModel, zeroRectangle] using
      ChapterVISignedDyadicComplexRectangle.pointInt_contains 40 0
  · have hreconstruct : t = c + y * h := by
      dsimp [y]
      field_simp [hhpos.ne']
      ring
    have hcast := congrArg (fun z : ℝ ↦ (z : ℂ)) hreconstruct
    simpa [y, c, h] using hcast

theorem remainderModel_contains {remainder : ℂ}
    (hrem : ‖remainder‖ ≤ (1 / 3 : ℝ) ^ 6 / 512)
    (radialParameter angularParameter : ℝ) :
    remainderModel.Contains radialParameter angularParameter remainder := by
  have hbudget : (1 / 3 : ℝ) ^ 6 / 512 ≤
      (remainderBudget : ℝ) / ChapterVISignedDyadicInterval.scale 40 := by
    norm_num [remainderBudget, ChapterVISignedDyadicInterval.scale]
  have hre : |remainder.re| ≤
      (remainderBudget : ℝ) / ChapterVISignedDyadicInterval.scale 40 :=
    (Complex.abs_re_le_norm remainder).trans (hrem.trans hbudget)
  have him : |remainder.im| ≤
      (remainderBudget : ℝ) / ChapterVISignedDyadicInterval.scale 40 :=
    (Complex.abs_im_le_norm remainder).trans (hrem.trans hbudget)
  have herror : (remainderModel.error).Contains remainder := by
    constructor
    · simp only [remainderModel, ChapterVISignedDyadicInterval.Contains,
        ChapterVISignedDyadicInterval.toRealInterval, ChapterVIRealInterval.Contains]
      change (((-remainderBudget : ℤ) : ℝ) /
          ChapterVISignedDyadicInterval.scale 40) ≤
        remainder.re ∧ remainder.re ≤
          (remainderBudget : ℝ) / ChapterVISignedDyadicInterval.scale 40
      exact ⟨by
        rw [show ((-remainderBudget : ℤ) : ℝ) /
            ChapterVISignedDyadicInterval.scale 40 =
          -((remainderBudget : ℝ) / ChapterVISignedDyadicInterval.scale 40) by
            rw [Int.cast_neg]
            ring]
        exact (abs_le.mp hre).1, (abs_le.mp hre).2⟩
    · simp only [remainderModel, ChapterVISignedDyadicInterval.Contains,
        ChapterVISignedDyadicInterval.toRealInterval, ChapterVIRealInterval.Contains]
      change (((-remainderBudget : ℤ) : ℝ) /
          ChapterVISignedDyadicInterval.scale 40) ≤
        remainder.im ∧ remainder.im ≤
          (remainderBudget : ℝ) / ChapterVISignedDyadicInterval.scale 40
      exact ⟨by
        rw [show ((-remainderBudget : ℤ) : ℝ) /
            ChapterVISignedDyadicInterval.scale 40 =
          -((remainderBudget : ℝ) / ChapterVISignedDyadicInterval.scale 40) by
            rw [Int.cast_neg]
            ring]
        exact (abs_le.mp him).1, (abs_le.mp him).2⟩
  refine ⟨0, 0, 0, remainder, ?_, ?_, ?_, herror, by ring⟩
  all_goals simpa [remainderModel, zeroRectangle] using
    ChapterVISignedDyadicComplexRectangle.pointInt_contains 40 0

end ChapterVIDRadialTailTaylorSemantics
end PoincareChapterVI
