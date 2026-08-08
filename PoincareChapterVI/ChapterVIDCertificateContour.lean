/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.ChapterVIDRadialContour
import PoincareChapterVI.ChapterVIDGlobalLocalBridge

/-!
# An explicit certificate-friendly radial contour through D

The pole-weighted radial contour is ideal for the qualitative inside/outside proof, but its
radius uses noncomputable inverse monotone branches.  A large compiled interval certificate is
easier to state for a radius given directly by elementary source data.

Writing `q(s)` for Poincare's affine positive source-parameter modulus, this file defines

`r(s) = q(s)^(1/6) * (r_D / q_D^(1/6))^s`.

The sixth-root scale follows the observed geometry of the two synchronized cubic branches.  Lean
proves that this radius is positive and continuous, starts at one, and ends at the exact collision
radius.  Therefore it gives another explicit homotopy from the literal unit circle to a circle
through D.  Unlike `ChapterVIDRadialContour.lean`, avoidance of the full source radicand is not
claimed here: that is deliberately the downstream finite nonvanishing-certificate obligation.
-/

noncomputable section

open Complex Real
open scoped Topology unitInterval

namespace PoincareChapterVI

/-- The affine positive source-parameter modulus used by the synchronized D branches. -/
noncomputable def chapterVIDCertificateParameter (s : I) : ℝ :=
  AffineMap.lineMap 1 chapterVIDCriticalParameterModulus (s : ℝ)

theorem chapterVIDCertificateParameter_pos (s : I) :
    0 < chapterVIDCertificateParameter s := by
  unfold chapterVIDCertificateParameter
  simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, smul_eq_mul]
  have hprod : 0 ≤ (1 - (s : ℝ)) *
      (1 - chapterVIDCriticalParameterModulus) :=
    mul_nonneg (by linarith [s.property.2])
      (by linarith [chapterVIDCriticalParameterModulus_lt_one])
  nlinarith [chapterVIDCriticalParameterModulus_pos]

theorem continuous_chapterVIDCertificateParameter :
    Continuous chapterVIDCertificateParameter := by
  unfold chapterVIDCertificateParameter
  fun_prop

@[simp]
theorem chapterVIDCertificateParameter_zero :
    chapterVIDCertificateParameter 0 = 1 := by
  simp [chapterVIDCertificateParameter, AffineMap.lineMap_apply]

@[simp]
theorem chapterVIDCertificateParameter_one :
    chapterVIDCertificateParameter 1 = chapterVIDCriticalParameterModulus := by
  simp [chapterVIDCertificateParameter, AffineMap.lineMap_apply]

/-- The positive real sixth root of the source parameter at D. -/
noncomputable def chapterVIDCriticalParameterSixthRoot : ℝ :=
  chapterVIDCriticalParameterModulus ^ ((6 : ℝ)⁻¹)

theorem chapterVIDCriticalParameterSixthRoot_pos :
    0 < chapterVIDCriticalParameterSixthRoot := by
  exact Real.rpow_pos_of_pos chapterVIDCriticalParameterModulus_pos _

/-- The small positive correction making the source sixth-root radius hit D exactly. -/
noncomputable def chapterVIDCertificateContourCorrection : ℝ :=
  ‖chapterVIDCollisionLift‖ / chapterVIDCriticalParameterSixthRoot

theorem chapterVIDCertificateContourCorrection_pos :
    0 < chapterVIDCertificateContourCorrection := by
  exact div_pos (norm_pos_iff.mpr chapterVIDCollisionLift_ne_zero)
    chapterVIDCriticalParameterSixthRoot_pos

/-- Directly executable formula for the certificate contour radius. -/
noncomputable def chapterVIDCertificateContourRadius (s : I) : ℝ :=
  chapterVIDCertificateParameter s ^ ((6 : ℝ)⁻¹) *
    chapterVIDCertificateContourCorrection ^ (s : ℝ)

theorem continuous_chapterVIDCertificateContourRadius :
    Continuous chapterVIDCertificateContourRadius := by
  unfold chapterVIDCertificateContourRadius
  exact (continuous_chapterVIDCertificateParameter.rpow_const
      (fun s ↦ Or.inl (chapterVIDCertificateParameter_pos s).ne')).mul
    (continuous_const.rpow continuous_subtype_val
      (fun _ ↦ Or.inl chapterVIDCertificateContourCorrection_pos.ne'))

theorem chapterVIDCertificateContourRadius_pos (s : I) :
    0 < chapterVIDCertificateContourRadius s := by
  unfold chapterVIDCertificateContourRadius
  exact mul_pos
    (Real.rpow_pos_of_pos (chapterVIDCertificateParameter_pos s) _)
    (Real.rpow_pos_of_pos chapterVIDCertificateContourCorrection_pos _)

@[simp]
theorem chapterVIDCertificateContourRadius_zero :
    chapterVIDCertificateContourRadius 0 = 1 := by
  simp [chapterVIDCertificateContourRadius]

@[simp]
theorem chapterVIDCertificateContourRadius_one :
    chapterVIDCertificateContourRadius 1 = ‖chapterVIDCollisionLift‖ := by
  unfold chapterVIDCertificateContourRadius chapterVIDCertificateParameter
    chapterVIDCertificateContourCorrection chapterVIDCriticalParameterSixthRoot
  simp only [Set.Icc.coe_one]
  rw [show AffineMap.lineMap 1 chapterVIDCriticalParameterModulus (1 : ℝ) =
    chapterVIDCriticalParameterModulus by simp [AffineMap.lineMap_apply]]
  simp only [Real.rpow_one]
  field_simp [ne_of_gt
    (Real.rpow_pos_of_pos chapterVIDCriticalParameterModulus_pos _)]

/-- The explicit certificate contour homotopy. -/
noncomputable def chapterVIDCertificateContourHomotopy : ContinuousMap.Homotopy
    (chapterVIUnitCirclePath : C(I, ℂ))
    (chapterVIDRadialCirclePath ‖chapterVIDCollisionLift‖ : C(I, ℂ)) where
  toFun st :=
    (chapterVIDCertificateContourRadius st.1 : ℂ) * chapterVIUnitCirclePath st.2
  continuous_toFun := by
    exact (Complex.ofRealCLM.continuous.comp
      (continuous_chapterVIDCertificateContourRadius.comp continuous_fst)).mul
      (chapterVIUnitCirclePath.continuous.comp continuous_snd)
  map_zero_left t := by simp
  map_one_left t := by simp [chapterVIDRadialCirclePath_apply]

@[simp]
theorem chapterVIDCertificateContourHomotopy_apply (s t : I) :
    chapterVIDCertificateContourHomotopy (s, t) =
      (chapterVIDCertificateContourRadius s : ℂ) * chapterVIUnitCirclePath t :=
  rfl

theorem chapterVIDCertificateContourHomotopy_norm (s t : I) :
    ‖chapterVIDCertificateContourHomotopy (s, t)‖ =
      chapterVIDCertificateContourRadius s := by
  rw [chapterVIDCertificateContourHomotopy_apply, norm_mul,
    chapterVIUnitCirclePath_norm, mul_one, norm_real, Real.norm_eq_abs,
    abs_of_pos (chapterVIDCertificateContourRadius_pos s)]

/-- The certificate contour reaches the exact global collision lift at its final half-turn. -/
theorem chapterVIDCertificateContour_collision :
    chapterVIDCertificateContourHomotopy (1, chapterVIDHalfTurn) =
      chapterVIDCollisionLift := by
  rw [chapterVIDCertificateContourHomotopy_apply,
    chapterVIDCertificateContourRadius_one, chapterVIUnitCirclePath_halfTurn]
  calc
    (‖chapterVIDCollisionLift‖ : ℂ) * -1 =
        -(‖chapterVIDCollisionLift‖ : ℂ) := by ring
    _ = chapterVIDCollisionLift := chapterVIDCollisionLift_eq_neg_norm.symm

end PoincareChapterVI
