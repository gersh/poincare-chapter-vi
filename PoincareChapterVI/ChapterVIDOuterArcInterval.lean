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
