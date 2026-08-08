/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.ChapterVIDCertificateContour
import PoincareChapterVI.ChapterVISquareRootSheet
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Algebra.Module.LocallyConvex

/-!
# Concrete outer arcs for the D pinch

This file fixes the two compact outer quarters of the certificate-friendly radial contour. The first
runs from `1` to `i`; the second from `-i` to `1`.  The collision at `-1` is therefore confined to
the complementary middle arc.

For the compiled certificate the quarters use the exact rational parametrization

`((1-t²) + 2ti) / (1+t²)`, `0 ≤ t ≤ 1`,

rather than evaluating `sin`, `cos`, or `π`.  The final quarter is `-i` times the first.  Lean
proves algebraically that these points have norm one and the correct endpoints.

The literal transformed radicand on each rectangle is defined and proved continuous.  The only
remaining datum needed to construct its compatible square-root sheet is an instance of
`ChapterVIDOuterArcNonvanishingCertificate`: this is now the exact concrete target for the
LeanCompCert finite sample computation and the accompanying analytic Lipschitz bound.
-/

noncomputable section

open Complex Real Filter Set
open scoped Topology unitInterval

namespace PoincareChapterVI

/-- The two regular pieces complementary to the middle half of the pinched circle. -/
inductive ChapterVIDOuterArcSide
  | initial
  | final
  deriving DecidableEq

/-- Reparameterization of the unit interval onto `[0,1/4]` or `[3/4,1]`. -/
noncomputable def chapterVIDOuterArcTime
    (side : ChapterVIDOuterArcSide) (t : I) : I :=
  match side with
  | .initial =>
      ⟨(t : ℝ) / 4, by
        constructor <;> nlinarith [t.property.1, t.property.2]⟩
  | .final =>
      ⟨3 / 4 + (t : ℝ) / 4, by
        constructor <;> nlinarith [t.property.1, t.property.2]⟩

theorem continuous_chapterVIDOuterArcTime
    (side : ChapterVIDOuterArcSide) :
    Continuous (chapterVIDOuterArcTime side) := by
  cases side <;> unfold chapterVIDOuterArcTime <;> fun_prop

/-- Rational counterclockwise parametrization of the unit-circle quarter from `1` to `i`. -/
noncomputable def chapterVIDRationalUnitQuarter (t : I) : ℂ :=
  (((1 - (t : ℝ) ^ 2) / (1 + (t : ℝ) ^ 2) : ℝ) : ℂ) +
    (((2 * (t : ℝ)) / (1 + (t : ℝ) ^ 2) : ℝ) : ℂ) * Complex.I

theorem chapterVIDRationalUnitQuarter_denominator_pos (t : I) :
    0 < 1 + (t : ℝ) ^ 2 := by positivity

theorem continuous_chapterVIDRationalUnitQuarter :
    Continuous chapterVIDRationalUnitQuarter := by
  unfold chapterVIDRationalUnitQuarter
  have hden : ∀ t : I, 1 + (t : ℝ) ^ 2 ≠ 0 :=
    fun t ↦ ne_of_gt (chapterVIDRationalUnitQuarter_denominator_pos t)
  have hre : Continuous (fun t : I ↦
      (1 - (t : ℝ) ^ 2) / (1 + (t : ℝ) ^ 2)) :=
    (continuous_const.sub (continuous_subtype_val.pow 2)).div
      (continuous_const.add (continuous_subtype_val.pow 2)) hden
  have him : Continuous (fun t : I ↦
      (2 * (t : ℝ)) / (1 + (t : ℝ) ^ 2)) :=
    (continuous_const.mul continuous_subtype_val).div
      (continuous_const.add (continuous_subtype_val.pow 2)) hden
  exact (Complex.ofRealCLM.continuous.comp hre).add
    ((Complex.ofRealCLM.continuous.comp him).mul continuous_const)

@[simp]
theorem chapterVIDRationalUnitQuarter_zero :
    chapterVIDRationalUnitQuarter 0 = 1 := by
  norm_num [chapterVIDRationalUnitQuarter]

@[simp]
theorem chapterVIDRationalUnitQuarter_one :
    chapterVIDRationalUnitQuarter 1 = Complex.I := by
  norm_num [chapterVIDRationalUnitQuarter]

theorem chapterVIDRationalUnitQuarter_normSq (t : I) :
    Complex.normSq (chapterVIDRationalUnitQuarter t) = 1 := by
  rw [Complex.normSq_apply]
  simp only [chapterVIDRationalUnitQuarter, add_re, add_im, ofReal_re, ofReal_im,
    mul_re, mul_im, I_re, I_im, mul_zero, mul_one, sub_zero, add_zero]
  field_simp [ne_of_gt (chapterVIDRationalUnitQuarter_denominator_pos t)]
  ring

@[simp]
theorem chapterVIDRationalUnitQuarter_norm (t : I) :
    ‖chapterVIDRationalUnitQuarter t‖ = 1 := by
  have hsq := (Complex.normSq_eq_norm_sq
    (chapterVIDRationalUnitQuarter t)).symm
  rw [chapterVIDRationalUnitQuarter_normSq] at hsq
  nlinarith [norm_nonneg (chapterVIDRationalUnitQuarter t)]

theorem chapterVIDRationalUnitQuarter_re_nonneg (t : I) :
    0 ≤ (chapterVIDRationalUnitQuarter t).re := by
  simp only [chapterVIDRationalUnitQuarter, add_re, ofReal_re, mul_re, ofReal_im,
    I_re, I_im, mul_zero, zero_mul, sub_zero, add_zero]
  exact div_nonneg
    (by nlinarith [t.property.1, t.property.2,
      mul_self_le_mul_self t.property.1 t.property.2])
    (chapterVIDRationalUnitQuarter_denominator_pos t).le

theorem chapterVIDRationalUnitQuarter_im_nonneg (t : I) :
    0 ≤ (chapterVIDRationalUnitQuarter t).im := by
  simp only [chapterVIDRationalUnitQuarter, add_im, ofReal_im, mul_im, ofReal_re,
    I_re, I_im, mul_zero, mul_one, zero_add, add_zero]
  change 0 ≤ (2 * (t : ℝ)) / (1 + (t : ℝ) ^ 2)
  exact div_nonneg (mul_nonneg (by norm_num) t.property.1)
    (chapterVIDRationalUnitQuarter_denominator_pos t).le

/-- The rational unit-circle parametrization for either regular outer quarter. -/
noncomputable def chapterVIDRationalOuterArcUnit
    (side : ChapterVIDOuterArcSide) (t : I) : ℂ :=
  match side with
  | .initial => chapterVIDRationalUnitQuarter t
  | .final => -Complex.I * chapterVIDRationalUnitQuarter t

theorem continuous_chapterVIDRationalOuterArcUnit
    (side : ChapterVIDOuterArcSide) :
    Continuous (chapterVIDRationalOuterArcUnit side) := by
  cases side
  · exact continuous_chapterVIDRationalUnitQuarter
  · exact continuous_const.mul continuous_chapterVIDRationalUnitQuarter

@[simp]
theorem chapterVIDRationalOuterArcUnit_norm
    (side : ChapterVIDOuterArcSide) (t : I) :
    ‖chapterVIDRationalOuterArcUnit side t‖ = 1 := by
  cases side
  · exact chapterVIDRationalUnitQuarter_norm t
  · simp [chapterVIDRationalOuterArcUnit]

/-- Algebraic identification of the chosen points with the required closed outer quarters. -/
theorem chapterVIDRationalOuterArcUnit_quadrant
    (side : ChapterVIDOuterArcSide) (t : I) :
    match side with
    | .initial => 0 ≤ (chapterVIDRationalOuterArcUnit side t).re ∧
        0 ≤ (chapterVIDRationalOuterArcUnit side t).im
    | .final => 0 ≤ (chapterVIDRationalOuterArcUnit side t).re ∧
        (chapterVIDRationalOuterArcUnit side t).im ≤ 0 := by
  cases side
  · exact ⟨chapterVIDRationalUnitQuarter_re_nonneg t,
      chapterVIDRationalUnitQuarter_im_nonneg t⟩
  · simp only [chapterVIDRationalOuterArcUnit, neg_mul, I_mul_re, I_mul_im,
      neg_re, neg_im]
    exact ⟨by simpa using chapterVIDRationalUnitQuarter_im_nonneg t,
      by simpa using neg_nonpos.mpr (chapterVIDRationalUnitQuarter_re_nonneg t)⟩

@[simp]
theorem chapterVIDRationalOuterArcUnit_initial_zero :
    chapterVIDRationalOuterArcUnit .initial 0 = 1 := by simp [chapterVIDRationalOuterArcUnit]

@[simp]
theorem chapterVIDRationalOuterArcUnit_initial_one :
    chapterVIDRationalOuterArcUnit .initial 1 = Complex.I := by
  simp [chapterVIDRationalOuterArcUnit]

@[simp]
theorem chapterVIDRationalOuterArcUnit_final_zero :
    chapterVIDRationalOuterArcUnit .final 0 = -Complex.I := by
  simp [chapterVIDRationalOuterArcUnit]

@[simp]
theorem chapterVIDRationalOuterArcUnit_final_one :
    chapterVIDRationalOuterArcUnit .final 1 = 1 := by
  simp [chapterVIDRationalOuterArcUnit]

/-- A point on one of the two outer-arc parameter rectangles.  The first coordinate is the
radial continuation time and the second is the local arc parameter. -/
noncomputable def chapterVIDOuterArcPoint
  (side : ChapterVIDOuterArcSide) (st : I × I) : ℂ :=
  (chapterVIDCertificateContourRadius st.1 : ℂ) *
    chapterVIDRationalOuterArcUnit side st.2

theorem continuous_chapterVIDOuterArcPoint
    (side : ChapterVIDOuterArcSide) :
    Continuous (chapterVIDOuterArcPoint side) := by
  exact (Complex.ofRealCLM.continuous.comp
      (continuous_chapterVIDCertificateContourRadius.comp continuous_fst)).mul
    ((continuous_chapterVIDRationalOuterArcUnit side).comp continuous_snd)

theorem chapterVIDOuterArcPoint_norm
    (side : ChapterVIDOuterArcSide) (st : I × I) :
    ‖chapterVIDOuterArcPoint side st‖ = chapterVIDCertificateContourRadius st.1 := by
  rw [chapterVIDOuterArcPoint, norm_mul, chapterVIDRationalOuterArcUnit_norm,
    mul_one, norm_real, Real.norm_eq_abs,
    abs_of_pos (chapterVIDCertificateContourRadius_pos st.1)]

theorem chapterVIDOuterArcPoint_ne_zero
    (side : ChapterVIDOuterArcSide) (st : I × I) :
    chapterVIDOuterArcPoint side st ≠ 0 := by
  intro hzero
  have hnorm := congrArg norm hzero
  rw [chapterVIDOuterArcPoint_norm] at hnorm
  norm_num at hnorm
  exact (chapterVIDCertificateContourRadius_pos st.1).ne' hnorm

theorem chapterVIDCommonParameterRootPath_ne_zero (s : I) :
    chapterVIDCommonParameterRootPath s ≠ 0 := by
  intro hzero
  have hpow := congrArg (fun z : ℂ ↦ z ^ 3) hzero
  rw [chapterVIDCommonParameterRootPath_pow, zero_pow (by norm_num)] at hpow
  have hpos := chapterVIDCurveThreeSmoothParameter_pos
    (chapterVIDInsideXPath_neg s)
  exact (ofReal_ne_zero.mpr hpos.ne') hpow

/-- Poincare's literal transformed source radicand on an explicit outer-arc rectangle. -/
noncomputable def chapterVIDOuterArcRadicand
    (side : ChapterVIDOuterArcSide) (st : I × I) : ℂ :=
  chapterVIDRootCoordinateRadicand
    (chapterVIDCommonParameterRootPath st.1) (chapterVIDOuterArcPoint side st)

/-- The sparse expression evaluated by the compiled certificate.  It is deliberately stated
only with arithmetic, inversion, and one complex exponential; the theorem below identifies it
with Poincaré's literal transformed source radicand. -/
noncomputable def chapterVIDOuterArcCertificateFormula
    (side : ChapterVIDOuterArcSide) (st : I × I) : ℂ :=
  let ζ := chapterVIDCommonParameterRootPath st.1
  let u := chapterVIDOuterArcPoint side st
  let y := ζ * u * Complex.exp ((100 / 30003 : ℂ) * ((u ^ 3)⁻¹ - u ^ 3))
  (((100 * u ^ 3 - 1) ^ 2) / (10001 * u ^ 3) - 2 * y) *
    (((u ^ 3 - 100) ^ 2) / (10001 * u ^ 3) - 2 / y)

theorem chapterVIDOuterArcRadicand_eq_certificateFormula
    (side : ChapterVIDOuterArcSide) (st : I × I) :
    chapterVIDOuterArcRadicand side st =
      chapterVIDOuterArcCertificateFormula side st := by
  unfold chapterVIDOuterArcRadicand chapterVIDOuterArcCertificateFormula
  rw [chapterVIDRootCoordinateRadicand_eq_certificateFormula
    (chapterVIDCommonParameterRootPath_ne_zero st.1)
    (chapterVIDOuterArcPoint_ne_zero side st)]
  simp [chapterVIDRootSecondAnomaly, chapterVIDRootToOriginalContour, mul_assoc]

theorem continuous_chapterVIDOuterArcRadicand
    (side : ChapterVIDOuterArcSide) :
    Continuous (chapterVIDOuterArcRadicand side) := by
  rw [continuous_iff_continuousAt]
  intro st
  have hpair : ContinuousAt
      (fun st : I × I ↦
        (chapterVIDCommonParameterRootPath st.1,
          chapterVIDOuterArcPoint side st)) st :=
    (chapterVIDCommonParameterRootPath.continuous.comp continuous_fst).continuousAt.prodMk
      (continuous_chapterVIDOuterArcPoint side).continuousAt
  change ContinuousAt
    ((fun p : ℂ × ℂ ↦ chapterVIDRootCoordinateRadicand p.1 p.2) ∘
      fun st : I × I ↦
        (chapterVIDCommonParameterRootPath st.1,
          chapterVIDOuterArcPoint side st)) st
  exact Filter.Tendsto.comp
    (continuousAt_chapterVIDRootCoordinateRadicand
      (chapterVIDCommonParameterRootPath_ne_zero st.1)
      (chapterVIDOuterArcPoint_ne_zero side st)) hpair

/-- The precise finite-certificate type for either concrete D outer arc. -/
abbrev ChapterVIDOuterArcNonvanishingCertificate
    (side : ChapterVIDOuterArcSide) :=
  ChapterVIFiniteNonvanishingCover (chapterVIDOuterArcRadicand side)

/-- The cheaper concrete target used by the compiled sweep: certify a positive lower bound on
the real part at every sample, then use the same cover and Lipschitz estimate. -/
abbrev ChapterVIDOuterArcPositiveRealPartCertificate
    (side : ChapterVIDOuterArcSide) :=
  ChapterVIFinitePositiveRealPartCover (chapterVIDOuterArcRadicand side)

def ChapterVIDOuterArcPositiveRealPartCertificate.toNonvanishingCertificate
    {side : ChapterVIDOuterArcSide}
    (certificate : ChapterVIDOuterArcPositiveRealPartCertificate side) :
    ChapterVIDOuterArcNonvanishingCertificate side :=
  certificate.toNonvanishingCover

/-- Once the finite nonvanishing certificate is supplied, covering-space lifting constructs the
base-normalized square-root sheet on the entire concrete outer-arc rectangle. -/
theorem ChapterVIDOuterArcNonvanishingCertificate.exists_squareRootSheet
    {side : ChapterVIDOuterArcSide}
    (certificate : ChapterVIDOuterArcNonvanishingCertificate side)
    (base : I × I) (baseRoot : ℂ)
    (hbaseRoot : baseRoot ^ 2 = chapterVIDOuterArcRadicand side base) :
    ∃ sheet : ChapterVIContinuousSquareRootSheet
        (chapterVIDOuterArcRadicand side),
      sheet.root base = baseRoot := by
  let : ContractibleSpace I :=
    (convex_Icc (0 : ℝ) 1).contractibleSpace (by simp)
  let : LocallyPathConnectedSpace I :=
    (convex_Icc (0 : ℝ) 1).locallyPathConnectedSpace
  let : LocallyPathConnectedSpace (I × I) := by
    refine LocallyPathConnectedSpace.of_bases
      (p := fun (point : I × I) (sets : Set I × Set I) ↦
        (sets.1 ∈ 𝓝 point.1 ∧ IsPathConnected sets.1) ∧
          (sets.2 ∈ 𝓝 point.2 ∧ IsPathConnected sets.2))
      (s := fun _ sets ↦ sets.1 ×ˢ sets.2) ?_ ?_
    · intro point
      rw [nhds_prod_eq]
      exact (path_connected_basis point.1).prod (path_connected_basis point.2)
    · intro _ sets hsets
      exact hsets.1.2.prod hsets.2.2
  exact certificate.exists_continuousSquareRootSheet
    (continuous_chapterVIDOuterArcRadicand side) base baseRoot hbaseRoot

theorem ChapterVIDOuterArcPositiveRealPartCertificate.exists_squareRootSheet
    {side : ChapterVIDOuterArcSide}
    (certificate : ChapterVIDOuterArcPositiveRealPartCertificate side)
    (base : I × I) (baseRoot : ℂ)
    (hbaseRoot : baseRoot ^ 2 = chapterVIDOuterArcRadicand side base) :
    ∃ sheet : ChapterVIContinuousSquareRootSheet
        (chapterVIDOuterArcRadicand side),
      sheet.root base = baseRoot :=
  certificate.toNonvanishingCertificate.exists_squareRootSheet
    base baseRoot hbaseRoot

end PoincareChapterVI
