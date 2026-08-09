/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.ChapterVIDPinchingArcPrefixAdmissibility
import PoincareChapterVI.ChapterVIDOuterArcRegularity

/-!
# A globally lifted full-circle prefix from Poincare's section 94 contour

The four rational quarters are concatenated into one literal closed path.  The compiled outer
tables cover the right half for every global parameter, while the new pinching-prefix tables cover
the left half through `2717 / 2744`.  Their positive-real conclusions put the entire radicand in
the principal square-root domain, so one continuous sheet exists on the complete prefix family
without a seam sign premise.
-/

noncomputable section

open Complex Real Set Topology
open scoped unitInterval

namespace PoincareChapterVI
namespace ChapterVIDGlobalLiftedPrefix

open ChapterVIDPinchingArcPrefixCompiledGrid

/-- Linear traversal of the certified global prefix. -/
def globalParameter (s : I) : I :=
  ⟨(prefixEnd : ℝ) * (s : ℝ),
    mul_nonneg prefixEnd_mem_Icc.1 s.property.1,
    (mul_le_of_le_one_right prefixEnd_mem_Icc.1 s.property.2).trans prefixEnd_mem_Icc.2⟩

theorem continuous_globalParameter : Continuous globalParameter := by
  exact Continuous.subtype_mk (continuous_const.mul continuous_subtype_val) _

@[simp] theorem globalParameter_zero : globalParameter 0 = 0 := by
  ext
  simp [globalParameter]

@[simp] theorem globalParameter_one : (globalParameter 1 : ℝ) = prefixEnd := by
  simp [globalParameter]

theorem globalParameter_le_prefixEnd (s : I) :
    (globalParameter s : ℝ) ≤ prefixEnd := by
  dsimp [globalParameter]
  exact mul_le_of_le_one_right prefixEnd_mem_Icc.1 s.property.2

/-- Either already certified right-hand quarter as a path. -/
def outerPath (side : ChapterVIDOuterArcSide) (s : I) :
    Path (chapterVIDOuterArcPoint side (globalParameter s, 0))
      (chapterVIDOuterArcPoint side (globalParameter s, 1)) where
  toFun t := chapterVIDOuterArcPoint side (globalParameter s, t)
  continuous_toFun := (continuous_chapterVIDOuterArcPoint side).comp
    (continuous_const.prodMk continuous_id)
  source' := rfl
  target' := rfl

/-- Upper-left rational quarter, from `i r(s)` to `-r(s)`. -/
def upperPinchingPath (s : I) :
    Path (chapterVIDOuterArcPoint .initial (globalParameter s, 1))
      (-(chapterVIDCertificateContourRadius (globalParameter s) : ℂ)) := by
  refine
    { toFun := fun t ↦ chapterVIDPinchingArcPoint .upper (globalParameter s, t)
      continuous_toFun := (continuous_chapterVIDPinchingArcPoint .upper).comp
        (continuous_const.prodMk continuous_id)
      source' := ?_
      target' := ?_ }
  · simp [chapterVIDPinchingArcPoint, chapterVIDOuterArcPoint,
      chapterVIDRationalPinchingArcUnit, chapterVIDRationalOuterArcUnit]
  · simp [chapterVIDPinchingArcPoint, chapterVIDRationalPinchingArcUnit]

/-- Lower-left rational quarter, from `-r(s)` to `-i r(s)`. -/
def lowerPinchingPath (s : I) :
    Path (-(chapterVIDCertificateContourRadius (globalParameter s) : ℂ))
      (chapterVIDOuterArcPoint .final (globalParameter s, 0)) := by
  refine
    { toFun := fun t ↦ chapterVIDPinchingArcPoint .lower (globalParameter s, t)
      continuous_toFun := (continuous_chapterVIDPinchingArcPoint .lower).comp
        (continuous_const.prodMk continuous_id)
      source' := ?_
      target' := ?_ }
  · simp [chapterVIDPinchingArcPoint, chapterVIDRationalPinchingArcUnit]
  · simp [chapterVIDPinchingArcPoint, chapterVIDOuterArcPoint,
      chapterVIDRationalPinchingArcUnit, chapterVIDRationalOuterArcUnit]

/-- The four certified quarters as one closed path, starting and ending on the positive ray. -/
def rootContour (s : I) :
    Path (chapterVIDOuterArcPoint .initial (globalParameter s, 0))
      (chapterVIDOuterArcPoint .initial (globalParameter s, 0)) :=
  (outerPath .initial s).trans
    ((upperPinchingPath s).trans
      ((lowerPinchingPath s).trans
        ((outerPath .final s).cast rfl
          (ChapterVIDOuterArcRegularity.outerArcPoint_initial_zero_eq_final_one
            (globalParameter s)))))

@[simp] theorem rootContour_closed (s : I) :
    rootContour s 0 = rootContour s 1 := by
  simp [rootContour]

private theorem trans_forall
    {a b c : ℂ} (first : Path a b) (second : Path b c) (predicate : ℂ → Prop)
    (hfirst : ∀ t, predicate (first t)) (hsecond : ∀ t, predicate (second t)) :
    ∀ t, predicate (first.trans second t) := by
  intro t
  have hmem : first.trans second t ∈ Set.range (first.trans second) := ⟨t, rfl⟩
  rw [Path.trans_range] at hmem
  rcases hmem with hmem | hmem
  · obtain ⟨u, hu⟩ := hmem
    rw [← hu]
    exact hfirst u
  · obtain ⟨u, hu⟩ := hmem
    rw [← hu]
    exact hsecond u

/-- Poincare's literal transformed radicand along the complete moving prefix contour. -/
def radicand (s t : I) : ℂ :=
  chapterVIDRootCoordinateRadicand (chapterVIDCommonParameterRootPath (globalParameter s))
    (rootContour s t)

theorem outer_radicand_re_pos
    (side : ChapterVIDOuterArcSide) (s t : I) :
    0 < (chapterVIDRootCoordinateRadicand
      (chapterVIDCommonParameterRootPath (globalParameter s))
      (outerPath side s t)).re := by
  change 0 < (chapterVIDOuterArcRadicand side (globalParameter s, t)).re
  exact ChapterVIDOuterArcPolarCompiledGrid.radicand_re_pos_of_run
    ChapterVIDOuterArcPolarCompiledGrid.referenceRunVerdict side (globalParameter s, t)

theorem pinching_radicand_re_pos
    (side : ChapterVIDPinchingArcSide) (s t : I) :
    0 < (chapterVIDRootCoordinateRadicand
      (chapterVIDCommonParameterRootPath (globalParameter s))
      (chapterVIDPinchingArcPoint side (globalParameter s, t))).re := by
  change 0 < (chapterVIDPinchingArcRadicand side (globalParameter s, t)).re
  exact radicand_re_pos_reference side (globalParameter s, t)
    (globalParameter_le_prefixEnd s)

/-! ## Transfer to Poincare's standard angular circle -/

/-- The certified radial family with the ordinary angular parametrization in the transformed
root coordinate. -/
def standardRootContour (s : I) :
    Path (chapterVIDCertificateContourRadius (globalParameter s) : ℂ)
      (chapterVIDCertificateContourRadius (globalParameter s) : ℂ) :=
  chapterVIDRadialCirclePath (chapterVIDCertificateContourRadius (globalParameter s))

@[simp] theorem standardRootContour_apply (s t : I) :
    standardRootContour s t =
      (chapterVIDCertificateContourRadius (globalParameter s) : ℂ) *
        chapterVIUnitCirclePath t := by
  simp [standardRootContour, chapterVIDRadialCirclePath_apply]

/-- At its initial parameter the certified family is definitionally the standard angular
root-coordinate unit circle, with no rational reparametrization left in the statement.  Its
image under the exact coordinate change is the source circle treated in
`chapterVIDUnitCircleCoordinateHomotopy`. -/
theorem standardRootContour_zero (t : I) :
    standardRootContour 0 t = chapterVIUnitCirclePath t := by
  simp [standardRootContour_apply]

/-- The literal transformed radicand on the standard angular circle. -/
def standardRadicand (s t : I) : ℂ :=
  chapterVIDRootCoordinateRadicand
    (chapterVIDCommonParameterRootPath (globalParameter s))
    (standardRootContour s t)

/-- Surjectivity of the rational quarters transfers the compiled result pointwise to the
ordinary angular parametrization. -/
theorem standardRadicand_re_pos (s t : I) :
    0 < (standardRadicand s t).re := by
  obtain ⟨side, u, hu⟩ := exists_chapterVIDCertifiedCircleQuarterUnit_eq
    (chapterVIUnitCirclePath_norm t)
  cases side with
  | rightUpper =>
      have h := outer_radicand_re_pos .initial s u
      change 0 < (chapterVIDRootCoordinateRadicand
        (chapterVIDCommonParameterRootPath (globalParameter s))
        ((chapterVIDCertificateContourRadius (globalParameter s) : ℂ) *
          chapterVIDRationalOuterArcUnit .initial u)).re at h
      simp only [standardRadicand, standardRootContour_apply]
      rw [← hu]
      simpa [chapterVIDCertifiedCircleQuarterUnit, chapterVIDOuterArcPoint,
        outerPath] using h
  | leftUpper =>
      have h := pinching_radicand_re_pos .upper s u
      simp only [standardRadicand, standardRootContour_apply]
      rw [← hu]
      simpa [chapterVIDCertifiedCircleQuarterUnit, chapterVIDPinchingArcPoint] using h
  | leftLower =>
      have h := pinching_radicand_re_pos .lower s u
      simp only [standardRadicand, standardRootContour_apply]
      rw [← hu]
      simpa [chapterVIDCertifiedCircleQuarterUnit, chapterVIDPinchingArcPoint] using h
  | rightLower =>
      have h := outer_radicand_re_pos .final s u
      change 0 < (chapterVIDRootCoordinateRadicand
        (chapterVIDCommonParameterRootPath (globalParameter s))
        ((chapterVIDCertificateContourRadius (globalParameter s) : ℂ) *
          chapterVIDRationalOuterArcUnit .final u)).re at h
      simp only [standardRadicand, standardRootContour_apply]
      rw [← hu]
      simpa [chapterVIDCertifiedCircleQuarterUnit, chapterVIDOuterArcPoint,
        outerPath] using h

theorem standardRadicand_ne_zero (s t : I) : standardRadicand s t ≠ 0 := by
  intro hzero
  have hpos := standardRadicand_re_pos s t
  simp [hzero] at hpos

theorem standardRootContour_ne_zero (s t : I) : standardRootContour s t ≠ 0 := by
  rw [standardRootContour_apply]
  exact mul_ne_zero
    (Complex.ofReal_ne_zero.mpr (chapterVIDCertificateContourRadius_pos _).ne')
    (by
      intro hzero
      have hnorm := chapterVIUnitCirclePath_norm t
      rw [hzero, norm_zero] at hnorm
      norm_num at hnorm)

theorem continuous_standardRootContour_family :
    Continuous ↿fun s : I ↦ standardRootContour s := by
  change Continuous (fun st : I × I ↦
    (chapterVIDCertificateContourRadius (globalParameter st.1) : ℂ) *
      chapterVIUnitCirclePath st.2)
  exact (Complex.ofRealCLM.continuous.comp
      (continuous_chapterVIDCertificateContourRadius.comp
        (continuous_globalParameter.comp continuous_fst))).mul
    (chapterVIUnitCirclePath.continuous.comp continuous_snd)

theorem continuous_standardRadicand :
    Continuous ↿fun s : I ↦ fun t : I ↦ standardRadicand s t := by
  exact continuous_chapterVIDRootCoordinateRadicand_comp
    (chapterVIDRootCoordinatePinch.parameterRoot.continuous.comp
      (continuous_globalParameter.comp continuous_fst))
    continuous_standardRootContour_family
    (fun st ↦ chapterVIDCommonParameterRootPath_ne_zero (globalParameter st.1))
    (fun st ↦ standardRootContour_ne_zero st.1 st.2)

/-- A single principal square-root sheet on the standard angular root-coordinate circle through
the complete certified prefix. -/
def standardPrincipalSheet :
    ChapterVIContinuousSquareRootSheet
      (fun st : I × I ↦ standardRadicand st.1 st.2) where
  root st := Complex.sqrt (standardRadicand st.1 st.2)
  continuous_root := by
    rw [continuous_iff_continuousAt]
    intro st
    exact (Complex.continuousAt_sqrt
      (Or.inl (standardRadicand_re_pos st.1 st.2).le)).comp_of_eq
        continuous_standardRadicand.continuousAt rfl
  root_sq st := by
    unfold Complex.sqrt
    exact Complex.cpow_nat_inv_pow (standardRadicand st.1 st.2)
      (by norm_num : (2 : ℕ) ≠ 0)

/-- The literal radicand stays in the open right half-plane on the entire global prefix. -/
theorem radicand_re_pos (s t : I) : 0 < (radicand s t).re := by
  unfold radicand rootContour
  let predicate : ℂ → Prop := fun u ↦
    0 < (chapterVIDRootCoordinateRadicand
      (chapterVIDCommonParameterRootPath (globalParameter s)) u).re
  exact trans_forall (outerPath .initial s)
    ((upperPinchingPath s).trans
      ((lowerPinchingPath s).trans
        ((outerPath .final s).cast rfl
          (ChapterVIDOuterArcRegularity.outerArcPoint_initial_zero_eq_final_one
            (globalParameter s))))) predicate
    (outer_radicand_re_pos .initial s)
    (trans_forall (upperPinchingPath s)
      ((lowerPinchingPath s).trans
        ((outerPath .final s).cast rfl
          (ChapterVIDOuterArcRegularity.outerArcPoint_initial_zero_eq_final_one
            (globalParameter s)))) predicate
      (pinching_radicand_re_pos .upper s)
      (trans_forall (lowerPinchingPath s)
        ((outerPath .final s).cast rfl
          (ChapterVIDOuterArcRegularity.outerArcPoint_initial_zero_eq_final_one
            (globalParameter s))) predicate
        (pinching_radicand_re_pos .lower s)
        (outer_radicand_re_pos .final s))) t

theorem radicand_ne_zero (s t : I) : radicand s t ≠ 0 := by
  intro hzero
  have hpos := radicand_re_pos s t
  simp [hzero] at hpos

theorem rootContour_ne_zero (s t : I) : rootContour s t ≠ 0 := by
  unfold rootContour
  exact trans_forall (outerPath .initial s)
    ((upperPinchingPath s).trans
      ((lowerPinchingPath s).trans
        ((outerPath .final s).cast rfl
          (ChapterVIDOuterArcRegularity.outerArcPoint_initial_zero_eq_final_one
            (globalParameter s))))) (fun u ↦ u ≠ 0)
    (fun t ↦ chapterVIDOuterArcPoint_ne_zero .initial (globalParameter s, t))
    (trans_forall (upperPinchingPath s)
      ((lowerPinchingPath s).trans
        ((outerPath .final s).cast rfl
          (ChapterVIDOuterArcRegularity.outerArcPoint_initial_zero_eq_final_one
            (globalParameter s)))) (fun u ↦ u ≠ 0)
      (fun t ↦ chapterVIDPinchingArcPoint_ne_zero .upper (globalParameter s, t))
      (trans_forall (lowerPinchingPath s)
        ((outerPath .final s).cast rfl
          (ChapterVIDOuterArcRegularity.outerArcPoint_initial_zero_eq_final_one
            (globalParameter s))) (fun u ↦ u ≠ 0)
        (fun t ↦ chapterVIDPinchingArcPoint_ne_zero .lower (globalParameter s, t))
        (fun t ↦ chapterVIDOuterArcPoint_ne_zero .final (globalParameter s, t)))) t

theorem continuous_rootContour_family : Continuous ↿fun s : I ↦ rootContour s := by
  unfold rootContour
  apply Path.trans_continuous_family
  · change Continuous (fun st : I × I ↦
      chapterVIDOuterArcPoint .initial (globalParameter st.1, st.2))
    exact (continuous_chapterVIDOuterArcPoint .initial).comp
      ((continuous_globalParameter.comp continuous_fst).prodMk continuous_snd)
  · apply Path.trans_continuous_family
    · change Continuous (fun st : I × I ↦
        chapterVIDPinchingArcPoint .upper (globalParameter st.1, st.2))
      exact (continuous_chapterVIDPinchingArcPoint .upper).comp
        ((continuous_globalParameter.comp continuous_fst).prodMk continuous_snd)
    · apply Path.trans_continuous_family
      · change Continuous (fun st : I × I ↦
          chapterVIDPinchingArcPoint .lower (globalParameter st.1, st.2))
        exact (continuous_chapterVIDPinchingArcPoint .lower).comp
          ((continuous_globalParameter.comp continuous_fst).prodMk continuous_snd)
      · change Continuous (fun st : I × I ↦
          chapterVIDOuterArcPoint .final (globalParameter st.1, st.2))
        exact (continuous_chapterVIDOuterArcPoint .final).comp
          ((continuous_globalParameter.comp continuous_fst).prodMk continuous_snd)

theorem continuous_radicand : Continuous ↿fun s : I ↦ fun t : I ↦ radicand s t := by
  exact continuous_chapterVIDRootCoordinateRadicand_comp
    (chapterVIDRootCoordinatePinch.parameterRoot.continuous.comp
      (continuous_globalParameter.comp continuous_fst))
    continuous_rootContour_family
    (fun st ↦ chapterVIDCommonParameterRootPath_ne_zero (globalParameter st.1))
    (fun st ↦ rootContour_ne_zero st.1 st.2)

/-- The full global prefix has one canonical continuous square-root sheet, namely the principal
root selected by the compiled positive-real certificate. -/
def principalSheet : ChapterVIContinuousSquareRootSheet (fun st : I × I ↦ radicand st.1 st.2) where
  root st := Complex.sqrt (radicand st.1 st.2)
  continuous_root := by
    rw [continuous_iff_continuousAt]
    intro st
    exact (Complex.continuousAt_sqrt (Or.inl (radicand_re_pos st.1 st.2).le)).comp_of_eq
      continuous_radicand.continuousAt rfl
  root_sq st := by
    unfold Complex.sqrt
    exact Complex.cpow_nat_inv_pow (radicand st.1 st.2) (by norm_num : (2 : ℕ) ≠ 0)

theorem principalSheet_root_sq (s t : I) :
    principalSheet.root (s, t) ^ 2 = radicand s t :=
  principalSheet.root_sq (s, t)

end ChapterVIDGlobalLiftedPrefix
end PoincareChapterVI
