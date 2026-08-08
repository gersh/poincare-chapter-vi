/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.ChapterVIDRootConnectors

/-!
# Finite limits from the compiled D connector certificates

For each concrete root-coordinate connector, two finite covers are sufficient:

* the affine root coordinate stays nonzero, so Poincare's exact `u -> t` change and its
  derivative vary continuously;
* the literal transformed source radicand stays nonzero, so its compatible square-root sheet
  exists.

This file proves that those covers automatically give the actual transformed connector integral
an ordinary finite collision limit. No integration is delegated to compiled code.
-/

noncomputable section

open Filter Set Topology
open scoped unitInterval

namespace PoincareChapterVI

/-- The complete finite-certificate input for one connector rectangle. -/
structure ChapterVIDConnectorCompiledCertificate
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) where
  coordinate : ChapterVIFiniteNonvanishingCover (model.rectanglePoint side)
  radicand : ChapterVIDConnectorNonvanishingCertificate model side

namespace ChapterVIDPrincipalConnectorModel

/-- Extend the compact connector root coordinate to a real integration parameter. -/
def rectanglePointReal
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) (point : I × ℝ) : ℂ :=
  model.rectanglePoint side
    (point.1, chapterVIConnectorClamp point.2)

theorem continuous_rectanglePointReal_of_certificate
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide}
    (certificate : ChapterVIDConnectorCompiledCertificate model side) :
    Continuous (model.rectanglePointReal side) :=
  certificate.coordinate.lipschitz.continuous.comp
    (continuous_fst.prodMk
      (continuous_chapterVIConnectorClamp.comp continuous_snd))

theorem rectanglePointReal_ne_zero_of_certificate
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide}
    (certificate : ChapterVIDConnectorCompiledCertificate model side)
    (point : I × ℝ) :
    model.rectanglePointReal side point ≠ 0 :=
  certificate.coordinate.ne_zero _

/-- The selected source-parameter cubic root over the compact connector family. -/
def connectorParameterRoot
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d) (s : I) : ℂ :=
  chapterVIDCriticalParameterRootAtD (model.criticalValue s : ℂ)

theorem continuous_connectorParameterRoot
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d) :
    Continuous model.connectorParameterRoot := by
  rw [continuous_iff_continuousAt]
  intro s
  have hanalytic := model.rootModel.parameterRoot_analyticAt
    (model.criticalValue s) (model.criticalValue_mem_rootModel s)
  have hline : ContinuousAt
      (fun q : I ↦ (model.criticalValue q : ℂ)) s :=
    Complex.ofRealCLM.continuous.continuousAt.comp_of_eq
      (continuous_ChapterVIDPrincipalConnectorModel_criticalValue model).continuousAt rfl
  exact hanalytic.continuousAt.comp_of_eq hline rfl

theorem connectorParameterRoot_ne_zero
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d) (s : I) :
    model.connectorParameterRoot s ≠ 0 := by
  rw [connectorParameterRoot,
    model.parameterRoot_eq_global (model.criticalValue s)
      (model.criticalValue_mem s)]
  exact chapterVIDCommonParameterRootPath_ne_zero _

/-- Poincare's original source contour coordinate along a connector. -/
def connectorSourceContour
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) (point : I × ℝ) : ℂ :=
  chapterVIDRootToOriginalContour (model.rectanglePointReal side point)

theorem continuous_connectorSourceContour_of_certificate
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide}
    (certificate : ChapterVIDConnectorCompiledCertificate model side) :
    Continuous (model.connectorSourceContour side) := by
  rw [continuous_iff_continuousAt]
  intro point
  exact (analyticAt_chapterVIDRootToOriginalContour
      (model.rectanglePointReal_ne_zero_of_certificate certificate point)).continuousAt.comp_of_eq
    (model.continuous_rectanglePointReal_of_certificate certificate).continuousAt rfl

/-- The literal principal numerator pulled back to one connector. -/
def connectorSourceNumerator
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide)
    (point : I × ℝ) : ℂ :=
  massProduct * model.connectorSourceContour side point ^ ((-1) * d - b * 3 - 1) *
    model.connectorParameterRoot point.1 ^ (-d)

theorem continuous_connectorSourceNumerator_of_certificate
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide}
    (certificate : ChapterVIDConnectorCompiledCertificate model side) :
    Continuous (model.connectorSourceNumerator side) := by
  unfold connectorSourceNumerator
  exact (continuous_const.mul
      ((model.continuous_connectorSourceContour_of_certificate certificate).zpow₀ _
        (fun point ↦ Or.inl
          (chapterVIDRootToOriginalContour_ne_zero
            (model.rectanglePointReal_ne_zero_of_certificate certificate point))))).mul
    ((model.continuous_connectorParameterRoot.comp continuous_fst).zpow₀ _
      (fun point ↦ Or.inl (model.connectorParameterRoot_ne_zero point.1)))

/-- Include the derivative of Poincare's exact `u -> t` map in the pulled-back numerator. The
remaining affine velocity is supplied by `chapterVIConnectorIntegral`. -/
def connectorTransformedNumerator
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide)
    (point : I × ℝ) : ℂ :=
  model.connectorSourceNumerator side point *
    ChapterVIDOuterArcRegularity.rootToSourceDerivative
      (model.rectanglePointReal side point)

theorem continuous_connectorTransformedNumerator_of_certificate
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide}
    (certificate : ChapterVIDConnectorCompiledCertificate model side) :
    Continuous (model.connectorTransformedNumerator side) := by
  unfold connectorTransformedNumerator
  exact (model.continuous_connectorSourceNumerator_of_certificate certificate).mul
    (ChapterVIDOuterArcRegularity.continuous_rootToSourceDerivative_comp
      (model.rectanglePointReal side)
      (model.continuous_rectanglePointReal_of_certificate certificate)
      (model.rectanglePointReal_ne_zero_of_certificate certificate))

/-- Root-coordinate source endpoint of a compact connector at parameter `s`. -/
def connectorRectangleSource
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) (s : I) : ℂ :=
  model.rectanglePoint side (s, 0)

/-- Root-coordinate target endpoint of a compact connector at parameter `s`. -/
def connectorRectangleTarget
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) (s : I) : ℂ :=
  model.rectanglePoint side (s, 1)

theorem continuous_connectorRectangleSource_of_certificate
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide}
    (certificate : ChapterVIDConnectorCompiledCertificate model side) :
    Continuous (model.connectorRectangleSource side) :=
  certificate.coordinate.lipschitz.continuous.comp
    (continuous_id.prodMk continuous_const)

theorem continuous_connectorRectangleTarget_of_certificate
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide}
    (certificate : ChapterVIDConnectorCompiledCertificate model side) :
    Continuous (model.connectorRectangleTarget side) :=
  certificate.coordinate.lipschitz.continuous.comp
    (continuous_id.prodMk continuous_const)

/-- The actual normalized connector integral, including Poincare's exact coordinate-change
Jacobian and the certificate-selected square-root sheet. -/
def connectorIntegral
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide)
    (sheet : ChapterVIContinuousSquareRootSheet (model.rectangleRadicand side)) :
    I → ℂ :=
  chapterVIConnectorIntegral
    (model.connectorTransformedNumerator side) sheet
    (model.connectorRectangleSource side) (model.connectorRectangleTarget side)

/-- The two compiled covers produce a compatible connector sheet and an ordinary finite
collision limit for the literal transformed integral. -/
theorem exists_sheet_tendsto_connectorIntegral_of_certificate
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide)
    (certificate : ChapterVIDConnectorCompiledCertificate model side) :
    ∃ sheet : ChapterVIContinuousSquareRootSheet (model.rectangleRadicand side),
      Tendsto (model.connectorIntegral side sheet)
        (𝓝 (1 : I))
        (𝓝 (model.connectorIntegral side sheet 1)) := by
  simpa only [connectorIntegral] using
    exists_sheet_tendsto_chapterVIConnectorIntegral
      certificate.radicand.lipschitz.continuous certificate.radicand
      (model.connectorTransformedNumerator side)
      (model.continuous_connectorTransformedNumerator_of_certificate certificate)
      (model.connectorRectangleSource side) (model.connectorRectangleTarget side)
      (model.continuous_connectorRectangleSource_of_certificate certificate)
      (model.continuous_connectorRectangleTarget_of_certificate certificate)

end ChapterVIDPrincipalConnectorModel

end PoincareChapterVI
