/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.ChapterVIDOuterArcs
import PoincareChapterVI.ChapterVIIntervalCertificate

/-!
# Interval semantics for the compiled D outer-arc certificate

This file connects the generic signed-dyadic certificate semantics to the only transcendental
operation in the sparse outer-arc formula.  On the contour annulus, the exact complex exponential
is enclosed by its first-order polynomial and a rigorous norm remainder.  Consequently the
compiled sweep evaluates only rational complex arithmetic and widens by a checked scalar error.
-/

noncomputable section

open Complex Real
open scoped Topology unitInterval

namespace PoincareChapterVI

/-- Polynomial approximation to the circular second anomaly used by the compiled checker. -/
def chapterVIDRootSecondAnomalyLinearApprox (ζ u : ℂ) : ℂ :=
  ζ * chapterVIDRootToOriginalContourLinearApprox u

/-- First-order approximation to the reciprocal second anomaly.  Keeping this reciprocal in
polar form avoids applying a generic rectangular inverse to a narrow curved set. -/
def chapterVIDRootSecondAnomalyInvLinearApprox (ζ u : ℂ) : ℂ :=
  ζ⁻¹ * u⁻¹ * (1 - chapterVIDRootExponentialArgument u)

theorem norm_chapterVIDRootSecondAnomaly_sub_linearApprox_le
    {ζ u : ℂ} (hargument : ‖chapterVIDRootExponentialArgument u‖ ≤ 1) :
    ‖chapterVIDRootSecondAnomaly ζ u -
        chapterVIDRootSecondAnomalyLinearApprox ζ u‖ ≤
      ‖ζ‖ * (‖u‖ * ‖chapterVIDRootExponentialArgument u‖ ^ 2) := by
  unfold chapterVIDRootSecondAnomaly chapterVIDRootSecondAnomalyLinearApprox
  rw [← mul_sub, norm_mul]
  exact mul_le_mul_of_nonneg_left
    (norm_chapterVIDRootToOriginalContour_sub_linearApprox_le hargument)
    (norm_nonneg ζ)

/-- The matching first-order remainder bound for the reciprocal anomaly. -/
theorem norm_chapterVIDRootSecondAnomaly_inv_sub_invLinearApprox_le
    {ζ u : ℂ} (hζ : ζ ≠ 0) (hu : u ≠ 0)
    (hargument : ‖chapterVIDRootExponentialArgument u‖ ≤ 1) :
    ‖(chapterVIDRootSecondAnomaly ζ u)⁻¹ -
        chapterVIDRootSecondAnomalyInvLinearApprox ζ u‖ ≤
      ‖ζ⁻¹‖ * (‖u⁻¹‖ * ‖chapterVIDRootExponentialArgument u‖ ^ 2) := by
  have hnegative : ‖-chapterVIDRootExponentialArgument u‖ ≤ 1 := by
    simpa using hargument
  have hexponential := Complex.norm_exp_sub_one_sub_id_le hnegative
  have hexponential' :
      ‖Complex.exp (-chapterVIDRootExponentialArgument u) - 1 -
          (-chapterVIDRootExponentialArgument u)‖ ≤
        ‖chapterVIDRootExponentialArgument u‖ ^ 2 := by
    simpa using hexponential
  have hidentity :
      (chapterVIDRootSecondAnomaly ζ u)⁻¹ -
          chapterVIDRootSecondAnomalyInvLinearApprox ζ u =
        ζ⁻¹ * u⁻¹ *
          (Complex.exp (-chapterVIDRootExponentialArgument u) - 1 -
            (-chapterVIDRootExponentialArgument u)) := by
    unfold chapterVIDRootSecondAnomaly chapterVIDRootToOriginalContour
      chapterVIDRootSecondAnomalyInvLinearApprox
    rw [mul_inv_rev, mul_inv_rev, ← Complex.exp_neg]
    field_simp [hζ, hu]
    ring
  rw [hidentity, norm_mul, norm_mul]
  calc
    ‖ζ⁻¹‖ * ‖u⁻¹‖ *
        ‖Complex.exp (-chapterVIDRootExponentialArgument u) - 1 -
          -chapterVIDRootExponentialArgument u‖ =
      ‖ζ⁻¹‖ * (‖u⁻¹‖ *
        ‖Complex.exp (-chapterVIDRootExponentialArgument u) - 1 -
          -chapterVIDRootExponentialArgument u‖) := by ring
    _ ≤ ‖ζ⁻¹‖ * (‖u⁻¹‖ * ‖chapterVIDRootExponentialArgument u‖ ^ 2) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hexponential' (norm_nonneg u⁻¹))
        (norm_nonneg ζ⁻¹)

/-- The coarse radius bounds required by the exponential remainder theorem.  They are emitted
alongside the sample table and checked using the same signed-dyadic comparisons. -/
theorem norm_chapterVIDOuterArcExponentialArgument_le_one
    (side : ChapterVIDOuterArcSide) (st : I × I)
    (hlower : (1 / 5 : ℝ) ≤ chapterVIDCertificateContourRadius st.1)
    (hupper : chapterVIDCertificateContourRadius st.1 ≤ 1) :
    ‖chapterVIDRootExponentialArgument (chapterVIDOuterArcPoint side st)‖ ≤ 1 := by
  apply norm_chapterVIDRootExponentialArgument_le_one_of_mem_annulus
  · simpa [chapterVIDOuterArcPoint_norm] using hlower
  · simpa [chapterVIDOuterArcPoint_norm] using hupper

/-- Final semantic bridge for the exponential step of one compiled sample.  Once the checker
encloses the polynomial approximation, widening by the explicit remainder encloses the exact
second anomaly occurring in Poincaré's literal radicand. -/
theorem chapterVIDOuterArcSecondAnomaly_mem_widenedLinearApprox
    (side : ChapterVIDOuterArcSide) (st : I × I)
    (rectangle : ChapterVIComplexRectangle)
    (happroximation : rectangle.Contains
      (chapterVIDRootSecondAnomalyLinearApprox
        (chapterVIDCommonParameterRootPath st.1)
        (chapterVIDOuterArcPoint side st)))
    (hlower : (1 / 5 : ℝ) ≤ chapterVIDCertificateContourRadius st.1)
    (hupper : chapterVIDCertificateContourRadius st.1 ≤ 1) :
    (rectangle.widen
      (‖chapterVIDCommonParameterRootPath st.1‖ *
        (‖chapterVIDOuterArcPoint side st‖ *
          ‖chapterVIDRootExponentialArgument
            (chapterVIDOuterArcPoint side st)‖ ^ 2))).Contains
      (chapterVIDRootSecondAnomaly
        (chapterVIDCommonParameterRootPath st.1)
        (chapterVIDOuterArcPoint side st)) := by
  apply ChapterVIComplexRectangle.widen_contains_of_norm_sub_le happroximation
  exact norm_chapterVIDRootSecondAnomaly_sub_linearApprox_le
    (norm_chapterVIDOuterArcExponentialArgument_le_one side st hlower hupper)

end PoincareChapterVI
