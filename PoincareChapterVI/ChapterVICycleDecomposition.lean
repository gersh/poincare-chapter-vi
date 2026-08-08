/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.ChapterVIPhi

/-!
# Poincaré's three-arc decomposition of the pinched contour

In §99 Poincaré splits one symmetric contour arc as

`C₀ = C₀' * C₀'' * C₀'''`.

The first and third pieces stay a positive distance from the two colliding singularities; only
the middle piece is pinched.  This file records the exact curve-integral identity behind that
localization.  It also combines the identity with the already checked deformation from the
literal §94 unit circle.  The theorem deliberately keeps that deformation as data: the local
double-zero calculation alone does not prove that the original cycle reaches this branch sheet.
-/

noncomputable section

open Complex

namespace PoincareChapterVI

/-- The concatenation `C₀' * C₀'' * C₀'''` used in §99.  Parenthesizing the last two arcs makes
the endpoint casts definitionally transparent. -/
def chapterVIThreeArcContour
    {a b c : ℂ} (initialArc : Path a b) (pinchArc : Path b c) (finalArc : Path c a) : Path a a :=
  initialArc.trans (pinchArc.trans finalArc)

/-- The normalized contribution of the two pieces kept away from the pinch. -/
def chapterVIRegularArcContribution
    {a b c : ℂ} (integrand : ℂ → ℂ → ℂ) (z : ℂ)
    (initialArc : Path a b) (finalArc : Path c a) : ℂ :=
  (2 * Real.pi * Complex.I : ℂ)⁻¹ *
    ((∫ᶜ t in initialArc, chapterVIComplexScalarOneForm (integrand z) t) +
      ∫ᶜ t in finalArc, chapterVIComplexScalarOneForm (integrand z) t)

/-- The normalized contribution of Poincaré's middle arc `C₀''`. -/
def chapterVILocalArcContribution
    {b c : ℂ} (integrand : ℂ → ℂ → ℂ) (z : ℂ) (pinchArc : Path b c) : ℂ :=
  (2 * Real.pi * Complex.I : ℂ)⁻¹ *
    ∫ᶜ t in pinchArc, chapterVIComplexScalarOneForm (integrand z) t

/-- Exact §99 localization: the full three-piece contour integral is the sum of its two regular
pieces and its middle pinched piece. -/
theorem chapterVIPhiAlongPath_threeArc_eq_regular_add_local
    {a b c : ℂ} {integrand : ℂ → ℂ → ℂ} {z : ℂ}
    {initialArc : Path a b} {pinchArc : Path b c} {finalArc : Path c a}
    (hinitial : CurveIntegrable
      (chapterVIComplexScalarOneForm (integrand z)) initialArc)
    (hpinch : CurveIntegrable
      (chapterVIComplexScalarOneForm (integrand z)) pinchArc)
    (hfinal : CurveIntegrable
      (chapterVIComplexScalarOneForm (integrand z)) finalArc) :
    chapterVIPhiAlongPath integrand z
        (chapterVIThreeArcContour initialArc pinchArc finalArc) =
      chapterVIRegularArcContribution integrand z initialArc finalArc +
        chapterVILocalArcContribution integrand z pinchArc := by
  unfold chapterVIPhiAlongPath chapterVIThreeArcContour
    chapterVIRegularArcContribution chapterVILocalArcContribution
  rw [curveIntegral_trans hinitial (hpinch.trans hfinal),
    curveIntegral_trans hpinch hfinal]
  ring

/-- Source-facing form of the §§95 and 99 reduction.  A checked deformation of the literal unit
circle to `C₀' * C₀'' * C₀'''` transports the original `Φ`; the preceding theorem then isolates
the sole local pinch contribution.  Constructing this deformation on the physical Riemann-sheet
lift remains the genuine-versus-apparent pinch obligation discussed by Poincaré in §§95--98. -/
theorem chapterVIPhi_eq_regular_add_local_of_threeArcDeformation
    {a b : ℂ} {integrand : ℂ → ℂ → ℂ} {z : ℂ}
    {initialArc : Path (1 : ℂ) a} {pinchArc : Path a b} {finalArc : Path b 1}
    {domain : Set ℂ}
    (deformation : ChapterVISmoothContourDeformation
      (chapterVIComplexScalarOneForm (integrand z))
      chapterVIUnitCirclePath (chapterVIThreeArcContour initialArc pinchArc finalArc) domain)
    (hinitial : CurveIntegrable
      (chapterVIComplexScalarOneForm (integrand z)) initialArc)
    (hpinch : CurveIntegrable
      (chapterVIComplexScalarOneForm (integrand z)) pinchArc)
    (hfinal : CurveIntegrable
      (chapterVIComplexScalarOneForm (integrand z)) finalArc) :
    chapterVIPhi integrand z =
      chapterVIRegularArcContribution integrand z initialArc finalArc +
        chapterVILocalArcContribution integrand z pinchArc := by
  rw [chapterVIPhi_eq_alongPath_of_unitCircleDeformation deformation]
  exact chapterVIPhiAlongPath_threeArc_eq_regular_add_local hinitial hpinch hfinal

end PoincareChapterVI
