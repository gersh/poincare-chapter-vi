/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.ChapterVIDRadialTailDerivative

/-!
# The total derivative on the actual radial tail

This file extends the certificate parameter and radius from the unit interval to the real line,
differentiates their elementary formulas, and substitutes those derivatives into the exact total
chain rule for Poincare's literal transformed radicand.  Consequently the remaining interval
certificate has a completely explicit target expression.
-/

noncomputable section

open Complex Real Set
open scoped unitInterval

namespace PoincareChapterVI

/-- Affine source parameter, extended from `I` to `ℝ`. -/
def chapterVIDCertificateParameterReal (s : ℝ) : ℝ :=
  1 + s * (chapterVIDCriticalParameterModulus - 1)

/-- Affine endpoint correction, extended from `I` to `ℝ`. -/
def chapterVIDCertificateContourCorrectionFactorReal (s : ℝ) : ℝ :=
  1 + s * (chapterVIDCertificateContourCorrection - 1)

/-- Positive parameter cube root used as `ζ`. -/
def chapterVIDCertificateZetaReal (s : ℝ) : ℝ :=
  chapterVIDCertificateParameterReal s ^ ((3 : ℝ)⁻¹)

/-- The certificate radius, extended by the same elementary formula to `ℝ`. -/
def chapterVIDCertificateContourRadiusReal (s : ℝ) : ℝ :=
  chapterVIDCertificateParameterReal s ^ ((6 : ℝ)⁻¹) *
    chapterVIDCertificateContourCorrectionFactorReal s

/-- Exact scalar velocity of `ζ(s)`. -/
def chapterVIDCertificateZetaVelocityReal (s : ℝ) : ℝ :=
  (chapterVIDCriticalParameterModulus - 1) * (3 : ℝ)⁻¹ *
    chapterVIDCertificateParameterReal s ^ ((3 : ℝ)⁻¹ - 1)

/-- Exact scalar velocity of the certificate radius. -/
def chapterVIDCertificateContourRadiusVelocityReal (s : ℝ) : ℝ :=
  ((chapterVIDCriticalParameterModulus - 1) * (6 : ℝ)⁻¹ *
      chapterVIDCertificateParameterReal s ^ ((6 : ℝ)⁻¹ - 1)) *
      chapterVIDCertificateContourCorrectionFactorReal s +
    chapterVIDCertificateParameterReal s ^ ((6 : ℝ)⁻¹) *
      (chapterVIDCertificateContourCorrection - 1)

theorem chapterVIDCertificateParameterReal_eq (s : I) :
    chapterVIDCertificateParameterReal s = chapterVIDCertificateParameter s := by
  simp only [chapterVIDCertificateParameterReal, chapterVIDCertificateParameter,
    AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, smul_eq_mul]
  ring

theorem chapterVIDCertificateContourCorrectionFactorReal_eq (s : I) :
    chapterVIDCertificateContourCorrectionFactorReal s =
      chapterVIDCertificateContourCorrectionFactor s := by
  simp only [chapterVIDCertificateContourCorrectionFactorReal,
    chapterVIDCertificateContourCorrectionFactor, AffineMap.lineMap_apply,
    vsub_eq_sub, vadd_eq_add, smul_eq_mul]
  ring

theorem chapterVIDCertificateZetaReal_eq (s : I) :
    chapterVIDCertificateZetaReal s =
      chapterVIDCertificateParameter s ^ ((3 : ℝ)⁻¹) := by
  rw [chapterVIDCertificateZetaReal, chapterVIDCertificateParameterReal_eq]

theorem chapterVIDCertificateContourRadiusReal_eq (s : I) :
    chapterVIDCertificateContourRadiusReal s =
      chapterVIDCertificateContourRadius s := by
  rw [chapterVIDCertificateContourRadiusReal,
    chapterVIDCertificateParameterReal_eq,
    chapterVIDCertificateContourCorrectionFactorReal_eq]
  rfl

theorem chapterVIDCertificateZetaVelocityReal_eq_log_mul (s : I) :
    chapterVIDCertificateZetaVelocityReal s =
      ((chapterVIDCriticalParameterModulus - 1) * (3 : ℝ)⁻¹ *
        (chapterVIDCertificateParameter s)⁻¹) *
        chapterVIDCertificateZetaReal s := by
  unfold chapterVIDCertificateZetaVelocityReal
  rw [chapterVIDCertificateParameterReal_eq,
    chapterVIDCertificateZetaReal_eq,
    Real.rpow_sub (chapterVIDCertificateParameter_pos s) _ _]
  rw [Real.rpow_one]
  field_simp [chapterVIDCertificateParameter_pos s |>.ne']

theorem chapterVIDCertificateContourRadiusVelocityReal_eq_log (s : I) :
    chapterVIDCertificateContourRadiusVelocityReal s =
      (((chapterVIDCriticalParameterModulus - 1) * (6 : ℝ)⁻¹ *
          (chapterVIDCertificateParameter s)⁻¹ *
          chapterVIDCertificateParameter s ^ ((6 : ℝ)⁻¹)) *
          chapterVIDCertificateContourCorrectionFactor s +
        chapterVIDCertificateParameter s ^ ((6 : ℝ)⁻¹) *
          (chapterVIDCertificateContourCorrection - 1)) := by
  unfold chapterVIDCertificateContourRadiusVelocityReal
  rw [chapterVIDCertificateParameterReal_eq,
    chapterVIDCertificateContourCorrectionFactorReal_eq,
    Real.rpow_sub (chapterVIDCertificateParameter_pos s) _ _, Real.rpow_one]
  field_simp [chapterVIDCertificateParameter_pos s |>.ne']

theorem hasDerivAt_chapterVIDCertificateParameterReal (s : ℝ) :
    HasDerivAt chapterVIDCertificateParameterReal
      (chapterVIDCriticalParameterModulus - 1) s := by
  change HasDerivAt
    (fun x : ℝ ↦ 1 + x * (chapterVIDCriticalParameterModulus - 1))
    (chapterVIDCriticalParameterModulus - 1) s
  simpa [add_comm] using
    ((hasDerivAt_id s).mul_const
      (chapterVIDCriticalParameterModulus - 1)).add_const 1

theorem hasDerivAt_chapterVIDCertificateContourCorrectionFactorReal (s : ℝ) :
    HasDerivAt chapterVIDCertificateContourCorrectionFactorReal
      (chapterVIDCertificateContourCorrection - 1) s := by
  change HasDerivAt
    (fun x : ℝ ↦ 1 + x * (chapterVIDCertificateContourCorrection - 1))
    (chapterVIDCertificateContourCorrection - 1) s
  simpa [add_comm] using
    ((hasDerivAt_id s).mul_const
      (chapterVIDCertificateContourCorrection - 1)).add_const 1

theorem hasDerivAt_chapterVIDCertificateZetaReal
    {s : ℝ} (hq : chapterVIDCertificateParameterReal s ≠ 0) :
    HasDerivAt chapterVIDCertificateZetaReal
      (chapterVIDCertificateZetaVelocityReal s) s := by
  change HasDerivAt
    (fun x ↦ chapterVIDCertificateParameterReal x ^ ((3 : ℝ)⁻¹))
    ((chapterVIDCriticalParameterModulus - 1) * (3 : ℝ)⁻¹ *
      chapterVIDCertificateParameterReal s ^ ((3 : ℝ)⁻¹ - 1)) s
  exact (hasDerivAt_chapterVIDCertificateParameterReal s).rpow_const (Or.inl hq)

theorem hasDerivAt_chapterVIDCertificateContourRadiusReal
    {s : ℝ} (hq : chapterVIDCertificateParameterReal s ≠ 0) :
    HasDerivAt chapterVIDCertificateContourRadiusReal
      (chapterVIDCertificateContourRadiusVelocityReal s) s := by
  have hsixth :=
    (hasDerivAt_chapterVIDCertificateParameterReal s).rpow_const (p := (6 : ℝ)⁻¹)
      (Or.inl hq)
  have hcorrection :=
    hasDerivAt_chapterVIDCertificateContourCorrectionFactorReal s
  change HasDerivAt
    (fun x ↦ chapterVIDCertificateParameterReal x ^ ((6 : ℝ)⁻¹) *
      chapterVIDCertificateContourCorrectionFactorReal x)
    (((chapterVIDCriticalParameterModulus - 1) * (6 : ℝ)⁻¹ *
        chapterVIDCertificateParameterReal s ^ ((6 : ℝ)⁻¹ - 1)) *
        chapterVIDCertificateContourCorrectionFactorReal s +
      chapterVIDCertificateParameterReal s ^ ((6 : ℝ)⁻¹) *
        (chapterVIDCertificateContourCorrection - 1)) s
  exact hsixth.mul hcorrection

/-- The fixed angular unit used on one of the two left-hand quarters. -/
def chapterVIDRadialTailFixedUnit
    (side : ChapterVIDPinchingArcSide) (t : I) : ℂ :=
  chapterVIDRationalPinchingArcUnit side t

/-- Real-line extension of the literal radial-tail radicand at a fixed angle. -/
def chapterVIDRadialTailRadicandReal
    (side : ChapterVIDPinchingArcSide) (t : I) (s : ℝ) : ℂ :=
  chapterVIDRootCoordinateRadicand
    (chapterVIDCertificateZetaReal s : ℂ)
    ((chapterVIDCertificateContourRadiusReal s : ℂ) *
      chapterVIDRadialTailFixedUnit side t)

/-- Exact total velocity inserted into the named radicand derivative. -/
def chapterVIDRadialTailActualDerivative
    (side : ChapterVIDPinchingArcSide) (t : I) (s : ℝ) : ℂ :=
  chapterVIDRadialTailRadicandDerivative
    (chapterVIDCertificateZetaReal s : ℂ)
    ((chapterVIDCertificateContourRadiusReal s : ℂ) *
      chapterVIDRadialTailFixedUnit side t)
    (chapterVIDCertificateZetaVelocityReal s : ℂ)
    ((chapterVIDCertificateContourRadiusVelocityReal s : ℂ) *
      chapterVIDRadialTailFixedUnit side t)

theorem chapterVIDRadialTailRadicandReal_eq
    (side : ChapterVIDPinchingArcSide) (t s : I) :
    chapterVIDRadialTailRadicandReal side t s =
      chapterVIDPinchingArcRadicand side (s, t) := by
  rw [chapterVIDRadialTailRadicandReal, chapterVIDPinchingArcRadicand,
    chapterVIDPinchingArcPoint,
    chapterVIDCertificateContourRadiusReal_eq,
    chapterVIDCertificateZetaReal_eq,
    chapterVIDCommonParameterRootPath_eq_certificateValue]
  rfl

/-- The explicit expression above is the derivative of the literal radial-tail radicand. -/
theorem hasDerivAt_chapterVIDRadialTailRadicandReal
    (side : ChapterVIDPinchingArcSide) (t : I) {s : ℝ}
    (hq : 0 < chapterVIDCertificateParameterReal s)
    (hr : 0 < chapterVIDCertificateContourRadiusReal s) :
    HasDerivAt (chapterVIDRadialTailRadicandReal side t)
      (chapterVIDRadialTailActualDerivative side t s) s := by
  have hζReal := hasDerivAt_chapterVIDCertificateZetaReal hq.ne'
  have hrReal := hasDerivAt_chapterVIDCertificateContourRadiusReal hq.ne'
  have hζ := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt s hζReal
  have hrComplex := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt s hrReal
  have hu := hrComplex.mul_const (chapterVIDRadialTailFixedUnit side t)
  apply hasDerivAt_chapterVIDRootCoordinateRadicand_comp hζ hu
  · exact Complex.ofReal_ne_zero.mpr
      (Real.rpow_pos_of_pos hq ((3 : ℝ)⁻¹)).ne'
  · exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne')
      (by
        intro hzero
        have hnorm : ‖chapterVIDRadialTailFixedUnit side t‖ = 1 := by
          simpa [chapterVIDRadialTailFixedUnit] using
            chapterVIDRationalPinchingArcUnit_norm side t
        rw [hzero, norm_zero] at hnorm
        norm_num at hnorm)

theorem hasDerivAt_chapterVIDRadialTailRadicandReal_re
    (side : ChapterVIDPinchingArcSide) (t : I) {s : ℝ}
    (hq : 0 < chapterVIDCertificateParameterReal s)
    (hr : 0 < chapterVIDCertificateContourRadiusReal s) :
    HasDerivAt (fun x ↦ (chapterVIDRadialTailRadicandReal side t x).re)
      (chapterVIDRadialTailActualDerivative side t s).re s := by
  exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt s
    (hasDerivAt_chapterVIDRadialTailRadicandReal side t hq hr)

/-- The explicit parameter and radius extensions remain positive on the complete unit interval. -/
theorem chapterVIDRadialTailRealInputs_pos
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    0 < chapterVIDCertificateParameterReal s ∧
      0 < chapterVIDCertificateContourRadiusReal s := by
  let st : I := ⟨s, hs0, hs1⟩
  have hq : 0 < chapterVIDCertificateParameterReal s := by
    rw [show s = (st : ℝ) by rfl, chapterVIDCertificateParameterReal_eq]
    exact chapterVIDCertificateParameter_pos st
  have hr : 0 < chapterVIDCertificateContourRadiusReal s := by
    rw [show s = (st : ℝ) by rfl, chapterVIDCertificateContourRadiusReal_eq]
    exact chapterVIDCertificateContourRadius_pos st
  exact ⟨hq, hr⟩

/-- A negative enclosure for the named explicit derivative implies the semantic strict radial
monotonicity required by the tail reduction. -/
theorem chapterVIDRadialTail_strictAnti_of_derivative_re_neg
    (side : ChapterVIDPinchingArcSide) (t : I)
    (hnegative : ∀ s : I,
      (ChapterVIDPinchingArcPrefixCompiledGrid.prefixEnd : ℝ) < (s : ℝ) →
      (s : ℝ) < 1 →
      (chapterVIDRadialTailActualDerivative side t s).re < 0) :
    StrictAntiOn
      (fun s : I ↦ (chapterVIDPinchingArcRadicand side (s, t)).re)
      chapterVIDRadialTail := by
  let a : ℝ := ChapterVIDPinchingArcPrefixCompiledGrid.prefixEnd
  let f : ℝ → ℝ := fun s ↦ (chapterVIDRadialTailRadicandReal side t s).re
  have ha0 : 0 ≤ a :=
    ChapterVIDPinchingArcPrefixCompiledGrid.prefixEnd_mem_Icc.1
  have hab : a < 1 := by
    rw [show a = (ChapterVIDPinchingArcPrefixCompiledGrid.prefixEnd : ℝ) by rfl,
      ChapterVIDPinchingArcPrefixCompiledGrid.prefixEnd_eq]
    norm_num
  have hhasDeriv : ∀ x ∈ Icc a 1,
      HasDerivAt f (chapterVIDRadialTailActualDerivative side t x).re x := by
    intro x hx
    have hinputs := chapterVIDRadialTailRealInputs_pos
      (ha0.trans hx.1) hx.2
    exact hasDerivAt_chapterVIDRadialTailRadicandReal_re side t hinputs.1 hinputs.2
  have hstrict : StrictAntiOn f (Icc a 1) := by
    apply strictAntiOn_Icc_of_deriv_neg hab
    · intro x hx
      exact (hhasDeriv x hx).continuousAt.continuousWithinAt
    · intro x hx
      rw [(hhasDeriv x ⟨hx.1.le, hx.2.le⟩).deriv]
      let sx : I := ⟨x, ha0.trans hx.1.le, hx.2.le⟩
      exact hnegative sx (by simpa [a, sx] using hx.1)
        (by simpa [sx] using hx.2)
  intro x hx y hy hxy
  have hxReal : (x : ℝ) ∈ Icc a 1 := ⟨hx, x.property.2⟩
  have hyReal : (y : ℝ) ∈ Icc a 1 := ⟨hy, y.property.2⟩
  change (chapterVIDPinchingArcRadicand side (y, t)).re <
    (chapterVIDPinchingArcRadicand side (x, t)).re
  rw [← chapterVIDRadialTailRadicandReal_eq side t x,
    ← chapterVIDRadialTailRadicandReal_eq side t y]
  exact hstrict hxReal hyReal hxy

/-- Final assembly interface for the finite tail computation.  The endpoint table supplies the
first argument and the derivative table supplies the second; all continuum reasoning is proved
above. -/
theorem chapterVIDRadialTailMonotonicityCertificate_of_tables
    (hendpoint : ∀ side t,
      0 ≤ (chapterVIDPinchingArcRadicand side (1, t)).re)
    (hderivative : ∀ side t (s : I),
      (ChapterVIDPinchingArcPrefixCompiledGrid.prefixEnd : ℝ) < (s : ℝ) →
      (s : ℝ) < 1 →
      (chapterVIDRadialTailActualDerivative side t s).re < 0) :
    ChapterVIDRadialTailMonotonicityCertificate where
  endpoint_nonneg := hendpoint
  radial_strictAnti := fun side t ↦
    chapterVIDRadialTail_strictAnti_of_derivative_re_neg side t
      (hderivative side t)

end PoincareChapterVI
