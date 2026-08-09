/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.ChapterVIDGlobalLiftedPrefix
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# A monotonicity reduction for the final radial tail

The raw positive-real-part margin tends to zero at the collision and is therefore a poor
interval quantity.  On the final `27 / 2744`, the useful bounded quantity is its radial
derivative.  If the real part is strictly decreasing in the global parameter and is nonnegative
on the collision circle, it is strictly positive at every pre-collision parameter.

This file formalizes that analytic reduction.  A subsequent compiled table only has to prove
the two hypotheses named in `ChapterVIDRadialTailMonotonicityCertificate`: a one-dimensional
endpoint inequality and a bounded two-dimensional monotonicity statement.
-/

noncomputable section

open Complex Real Set
open scoped unitInterval

namespace PoincareChapterVI

open ChapterVIDPinchingArcPrefixCompiledGrid

/-- The final radial strip, represented inside the unit interval. -/
def chapterVIDRadialTail : Set I :=
  {s | (prefixEnd : ℝ) ≤ (s : ℝ)}

/-- Exactly the two analytic facts needed on the tail.  `radial_strictAnti` is the semantic
output of the proposed derivative table; it is deliberately independent of how that table is
executed. -/
structure ChapterVIDRadialTailMonotonicityCertificate where
  endpoint_nonneg : ∀ side t,
    0 ≤ (chapterVIDPinchingArcRadicand side (1, t)).re
  radial_strictAnti : ∀ side t,
    StrictAntiOn
      (fun s : I ↦ (chapterVIDPinchingArcRadicand side (s, t)).re)
      chapterVIDRadialTail

namespace ChapterVIDRadialTailMonotonicityCertificate

/-- Strict radial monotonicity upgrades the nonnegative collision-circle value to strict
positivity at every earlier point in the final strip. -/
theorem tail_radicand_re_pos
    (certificate : ChapterVIDRadialTailMonotonicityCertificate)
    (side : ChapterVIDPinchingArcSide) (s t : I)
    (hprefix : (prefixEnd : ℝ) ≤ (s : ℝ)) (hpre : (s : ℝ) < 1) :
    0 < (chapterVIDPinchingArcRadicand side (s, t)).re := by
  have hs : s ∈ chapterVIDRadialTail := hprefix
  have hone : (1 : I) ∈ chapterVIDRadialTail := by
    change (prefixEnd : ℝ) ≤ 1
    exact prefixEnd_mem_Icc.2
  have hlt : s < (1 : I) := hpre
  exact (certificate.endpoint_nonneg side t).trans_lt
    (certificate.radial_strictAnti side t hs hone hlt)

/-- The old 44-shard prefix certificate and the new monotonicity certificate cover the complete
pre-collision radial family. -/
theorem full_precollision_radicand_re_pos
    (certificate : ChapterVIDRadialTailMonotonicityCertificate)
    (side : ChapterVIDPinchingArcSide) (s t : I) (hpre : (s : ℝ) < 1) :
    0 < (chapterVIDPinchingArcRadicand side (s, t)).re := by
  by_cases hprefix : (s : ℝ) ≤ prefixEnd
  · exact radicand_re_pos_reference side (s, t) hprefix
  · exact certificate.tail_radicand_re_pos side s t (le_of_not_ge hprefix) hpre

theorem full_precollision_radicand_ne_zero
    (certificate : ChapterVIDRadialTailMonotonicityCertificate)
    (side : ChapterVIDPinchingArcSide) (s t : I) (hpre : (s : ℝ) < 1) :
    chapterVIDPinchingArcRadicand side (s, t) ≠ 0 := by
  intro hzero
  have hpos := certificate.full_precollision_radicand_re_pos side s t hpre
  simp [hzero] at hpos

/-! ## The full pre-collision angular circle and its principal lift -/

/-- Literal transformed radicand on the standard angular certificate-radius circle, now using
the complete global parameter rather than the prefix rescaling. -/
def fullStandardRadicand (s t : I) : ℂ :=
  chapterVIDRootCoordinateRadicand (chapterVIDCommonParameterRootPath s)
    ((chapterVIDCertificateContourRadius s : ℂ) * chapterVIUnitCirclePath t)

theorem continuous_fullStandardRadicand :
    Continuous (fun st : I × I ↦ fullStandardRadicand st.1 st.2) := by
  exact continuous_chapterVIDRootCoordinateRadicand_comp
    (chapterVIDCommonParameterRootPath.continuous.comp continuous_fst)
    ((Complex.ofRealCLM.continuous.comp
        (continuous_chapterVIDCertificateContourRadius.comp continuous_fst)).mul
      (chapterVIUnitCirclePath.continuous.comp continuous_snd))
    (fun st ↦ chapterVIDCommonParameterRootPath_ne_zero st.1)
    (fun st ↦ mul_ne_zero
      (Complex.ofReal_ne_zero.mpr (chapterVIDCertificateContourRadius_pos st.1).ne')
      (by
        intro hzero
        have hnorm := chapterVIUnitCirclePath_norm st.2
        rw [hzero, norm_zero] at hnorm
        norm_num at hnorm))

/-- The prefix plus tail certificate covers every point of the ordinary angular circle before
the collision. -/
theorem fullStandardRadicand_re_pos
    (certificate : ChapterVIDRadialTailMonotonicityCertificate)
    (s t : I) (hpre : (s : ℝ) < 1) :
    0 < (fullStandardRadicand s t).re := by
  obtain ⟨side, u, hu⟩ := exists_chapterVIDCertifiedCircleQuarterUnit_eq
    (chapterVIUnitCirclePath_norm t)
  cases side with
  | rightUpper =>
      have h := ChapterVIDOuterArcPolarCompiledGrid.radicand_re_pos_of_run
        ChapterVIDOuterArcPolarCompiledGrid.referenceRunVerdict
        ChapterVIDOuterArcSide.initial (s, u)
      unfold fullStandardRadicand
      rw [← hu]
      simpa [chapterVIDCertifiedCircleQuarterUnit, chapterVIDOuterArcPoint,
        chapterVIDOuterArcRadicand] using h
  | leftUpper =>
      have h := certificate.full_precollision_radicand_re_pos
        ChapterVIDPinchingArcSide.upper s u hpre
      unfold fullStandardRadicand
      rw [← hu]
      simpa [chapterVIDCertifiedCircleQuarterUnit, chapterVIDPinchingArcRadicand,
        chapterVIDPinchingArcPoint] using h
  | leftLower =>
      have h := certificate.full_precollision_radicand_re_pos
        ChapterVIDPinchingArcSide.lower s u hpre
      unfold fullStandardRadicand
      rw [← hu]
      simpa [chapterVIDCertifiedCircleQuarterUnit, chapterVIDPinchingArcRadicand,
        chapterVIDPinchingArcPoint] using h
  | rightLower =>
      have h := ChapterVIDOuterArcPolarCompiledGrid.radicand_re_pos_of_run
        ChapterVIDOuterArcPolarCompiledGrid.referenceRunVerdict
        ChapterVIDOuterArcSide.final (s, u)
      unfold fullStandardRadicand
      rw [← hu]
      simpa [chapterVIDCertifiedCircleQuarterUnit, chapterVIDOuterArcPoint,
        chapterVIDOuterArcRadicand] using h

/-- The half-open global parameter interval, represented without duplicating its real bounds. -/
abbrev PrecollisionParameter := {s : I // (s : ℝ) < 1}

/-- The full angular-circle radicand restricted to the half-open parameter interval. -/
def fullStandardPrecollisionRadicand
    (point : PrecollisionParameter × I) : ℂ :=
  fullStandardRadicand point.1.1 point.2

theorem continuous_fullStandardPrecollisionRadicand :
    Continuous fullStandardPrecollisionRadicand := by
  let parameter : PrecollisionParameter × I → I := fun point ↦ point.1.1
  have hparameter : Continuous parameter := continuous_fst.subtype_val
  let contour : PrecollisionParameter × I → ℂ := fun point ↦
    (chapterVIDCertificateContourRadius (parameter point) : ℂ) *
      chapterVIUnitCirclePath point.2
  have hcontour : Continuous contour :=
    (Complex.ofRealCLM.continuous.comp
      (continuous_chapterVIDCertificateContourRadius.comp hparameter)).mul
      (chapterVIUnitCirclePath.continuous.comp continuous_snd)
  change Continuous (fun point ↦ chapterVIDRootCoordinateRadicand
    (chapterVIDCommonParameterRootPath (parameter point)) (contour point))
  exact continuous_chapterVIDRootCoordinateRadicand_comp
    (chapterVIDCommonParameterRootPath.continuous.comp hparameter) hcontour
    (fun point ↦ chapterVIDCommonParameterRootPath_ne_zero (parameter point))
    (fun point ↦ mul_ne_zero
      (Complex.ofReal_ne_zero.mpr
        (chapterVIDCertificateContourRadius_pos (parameter point)).ne')
      (by
        intro hzero
        have hnorm := chapterVIUnitCirclePath_norm point.2
        rw [hzero, norm_zero] at hnorm
        norm_num at hnorm))

set_option maxHeartbeats 800000 in
/-- The complete principal square-root lift of the standard moving circle, conditional only on
the two bounded tail tables. -/
def fullStandardPrincipalSheet
    (certificate : ChapterVIDRadialTailMonotonicityCertificate) :
    ChapterVIContinuousSquareRootSheet fullStandardPrecollisionRadicand where
  root point := Complex.sqrt (fullStandardPrecollisionRadicand point)
  continuous_root := by
    rw [continuous_iff_continuousAt]
    intro point
    apply (Complex.continuousAt_sqrt
      (Or.inl (certificate.fullStandardRadicand_re_pos
        point.1.1 point.2 point.1.2).le)).comp_of_eq
    · exact continuous_fullStandardPrecollisionRadicand.continuousAt
    · rfl
  root_sq point := by
    unfold Complex.sqrt
    exact Complex.cpow_nat_inv_pow (fullStandardPrecollisionRadicand point)
      (by norm_num : (2 : ℕ) ≠ 0)

theorem fullStandardPrincipalSheet_root_sq
    (certificate : ChapterVIDRadialTailMonotonicityCertificate)
    (s : PrecollisionParameter) (t : I) :
    (certificate.fullStandardPrincipalSheet.root (s, t)) ^ 2 =
      fullStandardPrecollisionRadicand (s, t) :=
  certificate.fullStandardPrincipalSheet.root_sq (s, t)

end ChapterVIDRadialTailMonotonicityCertificate

/-- Reusable calculus constructor: a continuous real trace with negative derivative is strictly
decreasing on a closed interval.  This is the bridge a verified derivative enclosure will use. -/
theorem strictAntiOn_Icc_of_deriv_neg
    {f : ℝ → ℝ} {a b : ℝ}
    (hab : a < b)
    (hcontinuous : ContinuousOn f (Set.Icc a b))
    (hderiv : ∀ x ∈ Set.Ioo a b, deriv f x < 0) :
    StrictAntiOn f (Set.Icc a b) := by
  exact strictAntiOn_of_deriv_neg (convex_Icc a b) hcontinuous fun x hx ↦
    hderiv x (by simpa [interior_Icc, hab] using hx)

end PoincareChapterVI
