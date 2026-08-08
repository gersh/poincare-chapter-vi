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

/-- Connector-rectangle point on the boundary shared with a compiled outer quarter. -/
def connectorBoundaryPoint
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) (s : I) : I × I :=
  match side with
  | .initial => (s, 0)
  | .final => (s, 1)

/-- Corresponding point of the compiled outer-quarter rectangle. -/
def connectorOuterBoundaryPoint
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) (s : I) : I × I :=
  match side with
  | .initial =>
      (chapterVIDCriticalToGlobalParameter (model.criticalValue s), 1)
  | .final =>
      (chapterVIDCriticalToGlobalParameter (model.criticalValue s), 0)

theorem rectangleRadicand_connectorBoundaryPoint
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) (s : I) :
    model.rectangleRadicand side (model.connectorBoundaryPoint side s) =
      chapterVIDOuterArcRadicand side
        (model.connectorOuterBoundaryPoint side s) := by
  cases side
  · exact model.rectangleRadicand_initial_zero s
  · exact model.rectangleRadicand_final_one s

/-- The compact local critical-value interval maps continuously into the compiled global radial
parameter. -/
theorem continuous_connectorGlobalParameter
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d) :
    Continuous (fun s : I ↦
      chapterVIDCriticalToGlobalParameter (model.criticalValue s)) := by
  rw [continuous_iff_continuousAt]
  intro s
  have hkline : ContinuousAt
      (fun q : I ↦ (model.criticalValue q : ℂ)) s :=
    Complex.ofRealCLM.continuous.continuousAt.comp_of_eq
      (continuous_ChapterVIDPrincipalConnectorModel_criticalValue model).continuousAt rfl
  have hinverse : ContinuousAt
      (fun q : I ↦ chapterVIDCriticalParameterInverseAtD
        (model.criticalValue q : ℂ)) s :=
    (model.rootModel.parameterInverse_analyticAt
      (model.criticalValue s) (model.criticalValue_mem_rootModel s)).continuousAt.comp_of_eq
        hkline rfl
  have hreal : ContinuousAt
      (fun q : I ↦ (chapterVIDCriticalParameterInverseAtD
        (model.criticalValue q : ℂ)).re) s :=
    Complex.continuous_re.continuousAt.comp_of_eq hinverse rfl
  have hraw : ContinuousAt
      (fun q : I ↦ chapterVIDCriticalToGlobalParameterRaw
        (model.criticalValue q)) s := by
    unfold chapterVIDCriticalToGlobalParameterRaw
    exact (continuousAt_const.sub hreal).div_const _
  unfold chapterVIDCriticalToGlobalParameter
  exact (continuous_projIcc (h := zero_le_one)).continuousAt.comp_of_eq hraw rfl

theorem continuous_connectorBoundaryPoint
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) :
    Continuous (model.connectorBoundaryPoint side) := by
  cases side
  · exact continuous_id.prodMk continuous_const
  · exact continuous_id.prodMk continuous_const

theorem continuous_connectorOuterBoundaryPoint
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) :
    Continuous (model.connectorOuterBoundaryPoint side) := by
  cases side
  · exact model.continuous_connectorGlobalParameter.prodMk continuous_const
  · exact model.continuous_connectorGlobalParameter.prodMk continuous_const

/-- The canonical compiled outer root, restricted to the shared connector boundary. -/
def connectorOuterBoundaryRoot
    {massProduct : ℂ} {b d : ℤ}
    (run : ChapterVIDOuterArcPolarCompiledGrid.CompiledRunVerdict)
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) (s : I) : ℂ :=
  (ChapterVIDOuterArcRegularity.principalSheet run side).root
    (model.connectorOuterBoundaryPoint side s)

theorem continuous_connectorOuterBoundaryRoot
    {massProduct : ℂ} {b d : ℤ}
    (run : ChapterVIDOuterArcPolarCompiledGrid.CompiledRunVerdict)
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) :
    Continuous (model.connectorOuterBoundaryRoot run side) :=
  (ChapterVIDOuterArcRegularity.principalSheet run side).continuous_root.comp
    (model.continuous_connectorOuterBoundaryPoint side)

/-- A connector nonvanishing certificate can be normalized at any prescribed square root. -/
theorem ChapterVIDConnectorCompiledCertificate.exists_squareRootSheet
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide}
    (certificate : ChapterVIDConnectorCompiledCertificate model side)
    (base : I × I) (baseRoot : ℂ)
    (hbaseRoot : baseRoot ^ 2 = model.rectangleRadicand side base) :
    ∃ sheet : ChapterVIContinuousSquareRootSheet (model.rectangleRadicand side),
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
  exact certificate.radicand.exists_continuousSquareRootSheet
    certificate.radicand.lipschitz.continuous base baseRoot hbaseRoot

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

/-- Normalize the connector sheet to the canonical compiled outer sheet. Connectedness then
forces agreement along the entire shared boundary, eliminating the connector/outer sign choice. -/
theorem exists_sheet_boundary_eq_outer_tendsto_connectorIntegral
    {massProduct : ℂ} {b d : ℤ}
    (run : ChapterVIDOuterArcPolarCompiledGrid.CompiledRunVerdict)
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide)
    (certificate : ChapterVIDConnectorCompiledCertificate model side) :
    ∃ sheet : ChapterVIContinuousSquareRootSheet (model.rectangleRadicand side),
      (∀ s : I,
        sheet.root (model.connectorBoundaryPoint side s) =
          model.connectorOuterBoundaryRoot run side s) ∧
      Tendsto (model.connectorIntegral side sheet)
        (𝓝 (1 : I))
        (𝓝 (model.connectorIntegral side sheet 1)) := by
  let base : I × I := model.connectorBoundaryPoint side 0
  let baseRoot : ℂ := model.connectorOuterBoundaryRoot run side 0
  have hbaseRoot : baseRoot ^ 2 = model.rectangleRadicand side base := by
    unfold baseRoot base connectorOuterBoundaryRoot
    rw [(ChapterVIDOuterArcRegularity.principalSheet run side).root_sq]
    exact (model.rectangleRadicand_connectorBoundaryPoint side 0).symm
  obtain ⟨sheet, hsheetBase⟩ :=
    ChapterVIDConnectorCompiledCertificate.exists_squareRootSheet
      certificate base baseRoot hbaseRoot
  let connectorBoundarySheet : ChapterVIContinuousSquareRootSheet
      (fun s : I ↦ model.rectangleRadicand side
        (model.connectorBoundaryPoint side s)) := {
    root := fun s ↦ sheet.root (model.connectorBoundaryPoint side s)
    continuous_root := sheet.continuous_root.comp
      (model.continuous_connectorBoundaryPoint side)
    root_sq := fun s ↦ sheet.root_sq _ }
  let outerBoundarySheet : ChapterVIContinuousSquareRootSheet
      (fun s : I ↦ model.rectangleRadicand side
        (model.connectorBoundaryPoint side s)) := {
    root := model.connectorOuterBoundaryRoot run side
    continuous_root := model.continuous_connectorOuterBoundaryRoot run side
    root_sq := fun s ↦ by
      unfold connectorOuterBoundaryRoot
      rw [(ChapterVIDOuterArcRegularity.principalSheet run side).root_sq]
      exact (model.rectangleRadicand_connectorBoundaryPoint side s).symm }
  have hboundaryBase : connectorBoundarySheet.root 0 =
      outerBoundarySheet.root 0 := by
    exact hsheetBase
  have hboundary := connectorBoundarySheet.root_eq_of_eq_at outerBoundarySheet
    (fun s ↦ certificate.radicand.ne_zero _) 0 hboundaryBase
  have htendsto : Tendsto (model.connectorIntegral side sheet)
      (𝓝 (1 : I)) (𝓝 (model.connectorIntegral side sheet 1)) := by
    unfold connectorIntegral
    exact tendsto_chapterVIConnectorIntegral
      (model.connectorTransformedNumerator side) sheet
      (model.connectorRectangleSource side) (model.connectorRectangleTarget side)
      (model.continuous_connectorTransformedNumerator_of_certificate certificate)
      (model.continuous_connectorRectangleSource_of_certificate certificate)
      (model.continuous_connectorRectangleTarget_of_certificate certificate)
      certificate.radicand.ne_zero
  refine ⟨sheet, ?_, htendsto⟩
  intro s
  exact congrFun hboundary s

end ChapterVIDPrincipalConnectorModel

end PoincareChapterVI
