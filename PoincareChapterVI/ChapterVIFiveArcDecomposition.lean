/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.ChapterVICycleDecomposition

/-!
# The five-piece source contour around Poincare's D pinch

The compiled D contour consists of two certified outer quarters, two regular connectors, and
the local pinched middle path. This file records the exact curve-integral identity for that
five-piece contour. It is purely geometric bookkeeping: nonvanishing and square-root-sheet
compatibility on the connector pieces are supplied separately.
-/

noncomputable section

open Complex

namespace PoincareChapterVI

/-- The closed contour obtained by adjoining two connector arcs to the three pieces used in the
local §99 decomposition. The order is outer initial, upper connector, pinched middle, lower
connector, outer final. -/
def chapterVIFiveArcContour
    {a b c d e : ℂ}
    (outerInitial : Path a b) (upperConnector : Path b c)
    (pinchArc : Path c d) (lowerConnector : Path d e)
    (outerFinal : Path e a) : Path a a :=
  outerInitial.trans
    (upperConnector.trans
      (pinchArc.trans (lowerConnector.trans outerFinal)))

/-- The normalized contribution of all four pieces that stay regular at the pinch. -/
def chapterVIFourRegularArcContribution
    {a b c d e : ℂ} (integrand : ℂ → ℂ → ℂ) (z : ℂ)
    (outerInitial : Path a b) (upperConnector : Path b c)
    (lowerConnector : Path d e) (outerFinal : Path e a) : ℂ :=
  (2 * Real.pi * Complex.I : ℂ)⁻¹ *
    ((∫ᶜ t in outerInitial, chapterVIComplexScalarOneForm (integrand z) t) +
      (∫ᶜ t in upperConnector, chapterVIComplexScalarOneForm (integrand z) t) +
      (∫ᶜ t in lowerConnector, chapterVIComplexScalarOneForm (integrand z) t) +
      ∫ᶜ t in outerFinal, chapterVIComplexScalarOneForm (integrand z) t)

/-- Exact five-piece localization: the full contour is its four regular pieces plus the sole
pinched middle piece. -/
theorem chapterVIPhiAlongPath_fiveArc_eq_regular_add_local
    {a b c d e : ℂ} {integrand : ℂ → ℂ → ℂ} {z : ℂ}
    {outerInitial : Path a b} {upperConnector : Path b c}
    {pinchArc : Path c d} {lowerConnector : Path d e}
    {outerFinal : Path e a}
    (hOuterInitial : CurveIntegrable
      (chapterVIComplexScalarOneForm (integrand z)) outerInitial)
    (hUpperConnector : CurveIntegrable
      (chapterVIComplexScalarOneForm (integrand z)) upperConnector)
    (hPinch : CurveIntegrable
      (chapterVIComplexScalarOneForm (integrand z)) pinchArc)
    (hLowerConnector : CurveIntegrable
      (chapterVIComplexScalarOneForm (integrand z)) lowerConnector)
    (hOuterFinal : CurveIntegrable
      (chapterVIComplexScalarOneForm (integrand z)) outerFinal) :
    chapterVIPhiAlongPath integrand z
        (chapterVIFiveArcContour outerInitial upperConnector pinchArc
          lowerConnector outerFinal) =
      chapterVIFourRegularArcContribution integrand z outerInitial upperConnector
          lowerConnector outerFinal +
        chapterVILocalArcContribution integrand z pinchArc := by
  unfold chapterVIPhiAlongPath chapterVIFiveArcContour
    chapterVIFourRegularArcContribution chapterVILocalArcContribution
  rw [curveIntegral_trans hOuterInitial
      (hUpperConnector.trans
        (hPinch.trans (hLowerConnector.trans hOuterFinal))),
    curveIntegral_trans hUpperConnector
      (hPinch.trans (hLowerConnector.trans hOuterFinal)),
    curveIntegral_trans hPinch (hLowerConnector.trans hOuterFinal),
    curveIntegral_trans hLowerConnector hOuterFinal]
  ring

/-- Source-facing form of the five-piece reduction. A checked deformation from the literal unit
circle transports `Phi` to the compiled contour; the preceding theorem then isolates the local
pinch. -/
theorem chapterVIPhi_eq_regular_add_local_of_fiveArcDeformation
    {a b c d : ℂ} {integrand : ℂ → ℂ → ℂ} {z : ℂ}
    {outerInitial : Path (1 : ℂ) a} {upperConnector : Path a b}
    {pinchArc : Path b c} {lowerConnector : Path c d}
    {outerFinal : Path d 1} {domain : Set ℂ}
    (deformation : ChapterVISmoothContourDeformation
      (chapterVIComplexScalarOneForm (integrand z)) chapterVIUnitCirclePath
      (chapterVIFiveArcContour outerInitial upperConnector pinchArc
        lowerConnector outerFinal) domain)
    (hOuterInitial : CurveIntegrable
      (chapterVIComplexScalarOneForm (integrand z)) outerInitial)
    (hUpperConnector : CurveIntegrable
      (chapterVIComplexScalarOneForm (integrand z)) upperConnector)
    (hPinch : CurveIntegrable
      (chapterVIComplexScalarOneForm (integrand z)) pinchArc)
    (hLowerConnector : CurveIntegrable
      (chapterVIComplexScalarOneForm (integrand z)) lowerConnector)
    (hOuterFinal : CurveIntegrable
      (chapterVIComplexScalarOneForm (integrand z)) outerFinal) :
    chapterVIPhi integrand z =
      chapterVIFourRegularArcContribution integrand z outerInitial upperConnector
          lowerConnector outerFinal +
        chapterVILocalArcContribution integrand z pinchArc := by
  rw [chapterVIPhi_eq_alongPath_of_unitCircleDeformation deformation]
  exact chapterVIPhiAlongPath_fiveArc_eq_regular_add_local hOuterInitial
    hUpperConnector hPinch hLowerConnector hOuterFinal

end PoincareChapterVI
