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

/-- Exactly the analytic information extracted from a finite nonvanishing certificate. Keeping
continuity separate from nonvanishing lets a compiled interval grid certify only the latter;
continuity remains an ordinary Lean theorem about the explicit analytic formula. -/
structure ChapterVIDContinuousNonzeroWitness
    {A : Type*} [TopologicalSpace A] (f : A → ℂ) where
  continuous : Continuous f
  ne_zero : ∀ x, f x ≠ 0

/-- A point-sample finite cover produces the more economical downstream witness. -/
theorem ChapterVIDContinuousNonzeroWitness.ofFiniteCover
    {A : Type*} [PseudoMetricSpace A] {f : A → ℂ}
    (certificate : ChapterVIFiniteNonvanishingCover f) :
    ChapterVIDContinuousNonzeroWitness f where
  continuous := certificate.lipschitz.continuous
  ne_zero := certificate.ne_zero

/-- The complete certificate input for one connector rectangle. Only the literal radicand
requires certification; coordinate continuity and nonvanishing follow from the exact connector
geometry. -/
structure ChapterVIDConnectorCompiledCertificate
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) where
  radicand : ChapterVIDContinuousNonzeroWitness (model.rectangleRadicand side)

/-- Construct the semantic certificate from the original point-sample finite-cover interface. -/
theorem ChapterVIDConnectorCompiledCertificate.ofFiniteCover
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide}
    (radicand : ChapterVIDConnectorNonvanishingCertificate model side) :
    ChapterVIDConnectorCompiledCertificate model side where
  radicand := ChapterVIDContinuousNonzeroWitness.ofFiniteCover radicand

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

/-- Connector-rectangle point on the boundary shared with the local Morse segment. -/
def connectorLocalBoundaryPoint
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) (s : I) : I × I :=
  match side with
  | .initial => (s, 1)
  | .final => (s, 0)

/-- The common positive-real normal-form radicand at either endpoint `v=±L`. -/
def connectorLocalBoundaryRadicand
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d) (s : I) : ℂ :=
  ((model.criticalValue s + model.rootModel.L ^ 2 : ℝ) : ℂ)

/-- Canonical positive square root used by the local logarithmic integral. -/
def connectorLocalBoundaryRoot
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d) (s : I) : ℂ :=
  Complex.sqrt (model.connectorLocalBoundaryRadicand s)

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

theorem rectangleRadicand_connectorLocalBoundaryPoint
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) (s : I) :
    model.rectangleRadicand side (model.connectorLocalBoundaryPoint side s) =
      model.connectorLocalBoundaryRadicand s := by
  cases side
  · simpa [connectorLocalBoundaryPoint, connectorLocalBoundaryRadicand] using
      model.rectangleRadicand_initial_one s
  · simpa [connectorLocalBoundaryPoint, connectorLocalBoundaryRadicand] using
      model.rectangleRadicand_final_zero s

theorem connectorLocalBoundaryRadicand_re_pos
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d) (s : I) :
    0 < (model.connectorLocalBoundaryRadicand s).re := by
  have hk : 0 ≤ model.criticalValue s := (model.criticalValue_mem s).1
  have hL : 0 < model.rootModel.L ^ 2 := sq_pos_of_pos model.rootModel.L_pos
  simp only [connectorLocalBoundaryRadicand, Complex.ofReal_re]
  nlinarith

theorem continuous_connectorLocalBoundaryRadicand
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d) :
    Continuous model.connectorLocalBoundaryRadicand := by
  unfold connectorLocalBoundaryRadicand
  exact Complex.ofRealCLM.continuous.comp
    ((continuous_ChapterVIDPrincipalConnectorModel_criticalValue model).add continuous_const)

theorem continuous_connectorLocalBoundaryRoot
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d) :
    Continuous model.connectorLocalBoundaryRoot := by
  rw [continuous_iff_continuousAt]
  intro s
  exact (Complex.continuousAt_sqrt
    (Or.inl (model.connectorLocalBoundaryRadicand_re_pos s).le)).comp_of_eq
      model.continuous_connectorLocalBoundaryRadicand.continuousAt rfl

theorem connectorLocalBoundaryRoot_sq
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d) (s : I) :
    model.connectorLocalBoundaryRoot s ^ 2 =
      model.connectorLocalBoundaryRadicand s := by
  unfold connectorLocalBoundaryRoot Complex.sqrt
  exact Complex.cpow_nat_inv_pow (model.connectorLocalBoundaryRadicand s)
    (by norm_num : (2 : ℕ) ≠ 0)

theorem connectorLocalBoundaryRoot_ne_zero
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d) (s : I) :
    model.connectorLocalBoundaryRoot s ≠ 0 := by
  intro hzero
  have hsq := model.connectorLocalBoundaryRoot_sq s
  rw [hzero, zero_pow (by norm_num)] at hsq
  have hpos := model.connectorLocalBoundaryRadicand_re_pos s
  have hre := congrArg Complex.re hsq
  simp only [Complex.zero_re] at hre
  linarith

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

theorem continuous_connectorLocalBoundaryPoint
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) :
    Continuous (model.connectorLocalBoundaryPoint side) := by
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
  exact exists_chapterVIContinuousSquareRootSheet _ certificate.radicand.continuous
    certificate.radicand.ne_zero base baseRoot hbaseRoot

/-- Along the seam with the local Morse segment, any connector sheet is globally either the
positive local sheet or its negative. The sign is constant; no pointwise branch ambiguity
remains. -/
theorem connectorSheet_eq_or_eq_neg_localBoundary
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide)
    (sheet : ChapterVIContinuousSquareRootSheet (model.rectangleRadicand side)) :
    (∀ s : I,
      sheet.root (model.connectorLocalBoundaryPoint side s) =
        model.connectorLocalBoundaryRoot s) ∨
    (∀ s : I,
      sheet.root (model.connectorLocalBoundaryPoint side s) =
        -model.connectorLocalBoundaryRoot s) := by
  let connectorRoot : I → ℂ := fun s ↦
    sheet.root (model.connectorLocalBoundaryPoint side s)
  let localRoot : I → ℂ := model.connectorLocalBoundaryRoot
  have hconnector : Continuous connectorRoot :=
    sheet.continuous_root.comp (model.continuous_connectorLocalBoundaryPoint side)
  have hlocal : Continuous localRoot :=
    model.continuous_connectorLocalBoundaryRoot
  have hsq : Set.EqOn (connectorRoot ^ 2) (localRoot ^ 2) Set.univ := by
    intro s _
    simp only [Pi.pow_apply, connectorRoot, localRoot]
    rw [sheet.root_sq, model.connectorLocalBoundaryRoot_sq]
    exact model.rectangleRadicand_connectorLocalBoundaryPoint side s
  have hne : ∀ {s : I}, s ∈ (Set.univ : Set I) → localRoot s ≠ 0 := by
    intro s _
    exact model.connectorLocalBoundaryRoot_ne_zero s
  rcases (isPreconnected_univ.eq_or_eq_neg_of_sq_eq
      hconnector.continuousOn hlocal.continuousOn hsq hne) with h | h
  · left
    intro s
    exact h (Set.mem_univ s)
  · right
    intro s
    simpa only [Pi.neg_apply] using h (Set.mem_univ s)

/-- Extend the compact connector root coordinate to a real integration parameter. -/
def rectanglePointReal
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) (point : I × ℝ) : ℂ :=
  model.rectanglePoint side
    (point.1, chapterVIConnectorClamp point.2)

theorem continuous_rectanglePointReal
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide} :
    Continuous (model.rectanglePointReal side) :=
  (model.continuous_rectanglePoint side).comp
    (continuous_fst.prodMk
      (continuous_chapterVIConnectorClamp.comp continuous_snd))

theorem rectanglePointReal_ne_zero
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide}
    (point : I × ℝ) :
    model.rectanglePointReal side point ≠ 0 :=
  model.rectanglePoint_ne_zero side _

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

/-- Once the connector coordinate excludes zero, continuity of the literal connector radicand
follows from its exact analytic formula. No separate radicand-continuity certificate is needed. -/
theorem continuous_rectangleRadicand_of_coordinate_ne_zero
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide)
    (hcoordinate : ∀ point, model.rectanglePoint side point ≠ 0) :
    Continuous (model.rectangleRadicand side) := by
  rw [show model.rectangleRadicand side = (fun point : I × I ↦
      chapterVIDRootCoordinateRadicand
        (model.connectorParameterRoot point.1) (model.rectanglePoint side point)) from rfl]
  exact continuous_chapterVIDRootCoordinateRadicand_comp
    (model.continuous_connectorParameterRoot.comp continuous_fst)
    (model.continuous_rectanglePoint side)
    (fun point ↦ model.connectorParameterRoot_ne_zero point.1)
    hcoordinate

/-- Poincare's original source contour coordinate along a connector. -/
def connectorSourceContour
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) (point : I × ℝ) : ℂ :=
  chapterVIDRootToOriginalContour (model.rectanglePointReal side point)

theorem continuous_connectorSourceContour
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide} :
    Continuous (model.connectorSourceContour side) := by
  rw [continuous_iff_continuousAt]
  intro point
  exact (analyticAt_chapterVIDRootToOriginalContour
      (model.rectanglePointReal_ne_zero point)).continuousAt.comp_of_eq
    model.continuous_rectanglePointReal.continuousAt rfl

/-- The literal principal numerator pulled back to one connector. -/
def connectorSourceNumerator
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide)
    (point : I × ℝ) : ℂ :=
  massProduct * model.connectorSourceContour side point ^ ((-1) * d - b * 3 - 1) *
    model.connectorParameterRoot point.1 ^ (-d)

theorem continuous_connectorSourceNumerator
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide} :
    Continuous (model.connectorSourceNumerator side) := by
  unfold connectorSourceNumerator
  exact (continuous_const.mul
      (model.continuous_connectorSourceContour.zpow₀ _
        (fun point ↦ Or.inl
          (chapterVIDRootToOriginalContour_ne_zero
            (model.rectanglePointReal_ne_zero point))))).mul
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

theorem continuous_connectorTransformedNumerator
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide} :
    Continuous (model.connectorTransformedNumerator side) := by
  unfold connectorTransformedNumerator
  exact model.continuous_connectorSourceNumerator.mul
    (ChapterVIDOuterArcRegularity.continuous_rootToSourceDerivative_comp
      (model.rectanglePointReal side)
      model.continuous_rectanglePointReal
      (model.rectanglePointReal_ne_zero))

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

theorem continuous_connectorRectangleSource
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide} :
    Continuous (model.connectorRectangleSource side) :=
  (model.continuous_rectanglePoint side).comp
    (continuous_id.prodMk continuous_const)

theorem continuous_connectorRectangleTarget
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide} :
    Continuous (model.connectorRectangleTarget side) :=
  (model.continuous_rectanglePoint side).comp
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
    exists_sheet_tendsto_chapterVIConnectorIntegral_of_ne_zero
      certificate.radicand.continuous certificate.radicand.ne_zero
      (model.connectorTransformedNumerator side)
      model.continuous_connectorTransformedNumerator
      (model.connectorRectangleSource side) (model.connectorRectangleTarget side)
      model.continuous_connectorRectangleSource
      model.continuous_connectorRectangleTarget

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
      model.continuous_connectorTransformedNumerator
      model.continuous_connectorRectangleSource
      model.continuous_connectorRectangleTarget
      certificate.radicand.ne_zero
  refine ⟨sheet, ?_, htendsto⟩
  intro s
  exact congrFun hboundary s

/-- Full seam-normalized connector package. The compiled certificate gives a finite connector
limit, the outer seam is fixed canonically, and the local seam has one globally constant sign
relative to the positive Morse square root. Either sign preserves a nonzero logarithmic
coefficient. -/
theorem exists_sheet_outer_boundary_local_sign_tendsto_connectorIntegral
    {massProduct : ℂ} {b d : ℤ}
    (run : ChapterVIDOuterArcPolarCompiledGrid.CompiledRunVerdict)
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide)
    (certificate : ChapterVIDConnectorCompiledCertificate model side) :
    ∃ sheet : ChapterVIContinuousSquareRootSheet (model.rectangleRadicand side),
      (∀ s : I,
        sheet.root (model.connectorBoundaryPoint side s) =
          model.connectorOuterBoundaryRoot run side s) ∧
      ((∀ s : I,
          sheet.root (model.connectorLocalBoundaryPoint side s) =
            model.connectorLocalBoundaryRoot s) ∨
        (∀ s : I,
          sheet.root (model.connectorLocalBoundaryPoint side s) =
            -model.connectorLocalBoundaryRoot s)) ∧
      Tendsto (model.connectorIntegral side sheet)
        (𝓝 (1 : I))
        (𝓝 (model.connectorIntegral side sheet 1)) := by
  obtain ⟨sheet, houter, htendsto⟩ :=
    model.exists_sheet_boundary_eq_outer_tendsto_connectorIntegral
      run side certificate
  exact ⟨sheet, houter,
    model.connectorSheet_eq_or_eq_neg_localBoundary side sheet, htendsto⟩

end ChapterVIDPrincipalConnectorModel

end PoincareChapterVI
