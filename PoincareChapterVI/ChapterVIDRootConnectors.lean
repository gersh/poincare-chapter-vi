/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.ChapterVIDGlobalRootModel
import PoincareChapterVI.ChapterVIDCompiledThreeArcContinuation
import PoincareChapterVI.ChapterVIConnectorRegularity

/-!
# Concrete root-coordinate connectors for the D contour

The upper connector runs from the endpoint `+i r(k)` of the initial compiled quarter to the
`v=-L` endpoint of the local Morse path. The lower connector runs from the `v=+L` endpoint to
`-i r(k)`, the start of the final compiled quarter. Both are affine segments in Poincare's
explicit `u = x^(1/3)` coordinate.

This file fixes those paths and their literal transformed radicands. The next finite artifact
must certify nonvanishing on the two resulting compact rectangles.
-/

noncomputable section

open Filter Set Topology
open scoped unitInterval

namespace PoincareChapterVI

/-- The local analytic cubic root and the global positive-real root agree along positive
critical values near D. -/
theorem eventually_chapterVIDCriticalParameterRootAtD_eq_global :
    ∀ᶠ k : ℝ in nhdsWithin 0 (Set.Ioi 0),
      chapterVIDCriticalParameterRootAtD (k : ℂ) =
        chapterVIDCommonParameterRootPath
          (chapterVIDCriticalToGlobalParameter k) := by
  have hglobal := tendsto_chapterVIDCriticalToGlobalParameter.eventually
    eventually_chapterVIDZRoot_commonParameterRootPath
  filter_upwards
    [eventually_chapterVIDCriticalToGlobalParameter_on_ray_unconditional,
      hglobal] with k hparameter hroot
  unfold chapterVIDCriticalParameterRootAtD
  rw [← hparameter]
  simpa only [zpow_ofNat] using hroot

/-- A compact positive critical-value interval on which the local Morse model and the compiled
global radial parameter use exactly the same cubic-root branch. -/
structure ChapterVIDPrincipalConnectorModel
    (massProduct : ℂ) (b d : ℤ) where
  rootModel : ChapterVIDPrincipalGlobalRootModel massProduct b d
  κ : ℝ
  κ_pos : 0 < κ
  κ_le_delta : κ ≤ rootModel.δ
  parameterRoot_eq_global : ∀ k ∈ Set.Icc 0 κ,
    chapterVIDCriticalParameterRootAtD (k : ℂ) =
      chapterVIDCommonParameterRootPath
        (chapterVIDCriticalToGlobalParameter k)

/-- The eventual branch agreement can always be made uniform on one compact interval. -/
theorem exists_chapterVIDPrincipalConnectorModel
    (massProduct : ℂ) (b d : ℤ) :
    Nonempty (ChapterVIDPrincipalConnectorModel massProduct b d) := by
  obtain ⟨rootModel⟩ :=
    exists_chapterVIDPrincipalGlobalRootModel massProduct b d
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhdsWithin_iff.mp
    eventually_chapterVIDCriticalParameterRootAtD_eq_global
  let κ : ℝ := min rootModel.δ (ε / 2)
  have hκ : 0 < κ := by
    dsimp [κ]
    exact lt_min rootModel.δ_pos (by positivity)
  have hκδ : κ ≤ rootModel.δ := min_le_left _ _
  refine ⟨{
    rootModel := rootModel
    κ := κ
    κ_pos := hκ
    κ_le_delta := hκδ
    parameterRoot_eq_global := ?_ }⟩
  intro k hk
  by_cases hkzero : k = 0
  · subst k
    change chapterVIDCriticalParameterRootAtD (0 : ℂ) =
      chapterVIDCommonParameterRootPath
        (chapterVIDCriticalToGlobalParameter 0)
    rw [chapterVIDCriticalParameterRootAtD_zero,
      chapterVIDCriticalToGlobalParameter_zero]
    exact chapterVIDZRootBase_eq_commonParameterRootPath_one
  · have hkpos : 0 < k := lt_of_le_of_ne hk.1 (Ne.symm hkzero)
    apply hεsub
    constructor
    · rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hkpos]
      have hκε : κ ≤ ε / 2 := min_le_right _ _
      linarith [hk.2]
    · exact hkpos

/-- Critical value `k` on the compact connector rectangle; `s=1` is the collision. -/
def ChapterVIDPrincipalConnectorModel.criticalValue
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (s : I) : ℝ :=
  model.κ * (1 - (s : ℝ))

theorem ChapterVIDPrincipalConnectorModel.criticalValue_mem
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d) (s : I) :
    model.criticalValue s ∈ Set.Icc 0 model.κ := by
  unfold ChapterVIDPrincipalConnectorModel.criticalValue
  constructor
  · exact mul_nonneg model.κ_pos.le (sub_nonneg.mpr s.property.2)
  · nlinarith [model.κ_pos, s.property.1]

theorem ChapterVIDPrincipalConnectorModel.criticalValue_mem_rootModel
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d) (s : I) :
    model.criticalValue s ∈ Set.Icc 0 model.rootModel.δ :=
  ⟨(model.criticalValue_mem s).1,
    (model.criticalValue_mem s).2.trans model.κ_le_delta⟩

theorem continuous_ChapterVIDPrincipalConnectorModel_criticalValue
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d) :
    Continuous model.criticalValue := by
  unfold ChapterVIDPrincipalConnectorModel.criticalValue
  fun_prop

@[simp]
theorem ChapterVIDPrincipalConnectorModel.criticalValue_zero
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d) :
    model.criticalValue 0 = model.κ := by
  simp [ChapterVIDPrincipalConnectorModel.criticalValue]

@[simp]
theorem ChapterVIDPrincipalConnectorModel.criticalValue_one
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d) :
    model.criticalValue 1 = 0 := by
  simp [ChapterVIDPrincipalConnectorModel.criticalValue]

/-- The endpoint of a compiled outer quarter that faces the local pinching region. -/
def ChapterVIDPrincipalGlobalRootModel.outerConnectorEndpoint
    {massProduct : ℂ} {b d : ℤ}
    (_model : ChapterVIDPrincipalGlobalRootModel massProduct b d)
    (side : ChapterVIDOuterArcSide) (k : ℝ) : ℂ :=
  match side with
  | .initial => chapterVIDOuterArcPoint .initial
      (chapterVIDCriticalToGlobalParameter k, 1)
  | .final => chapterVIDOuterArcPoint .final
      (chapterVIDCriticalToGlobalParameter k, 0)

/-- The corresponding endpoint of the root-coordinate local Morse path. -/
def ChapterVIDPrincipalGlobalRootModel.localConnectorEndpoint
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalGlobalRootModel massProduct b d)
    (side : ChapterVIDOuterArcSide) (k : ℝ) : ℂ :=
  match side with
  | .initial => chapterVIDCriticalMorseRootPoint
      ((k : ℂ), ((-model.L : ℝ) : ℂ))
  | .final => chapterVIDCriticalMorseRootPoint
      ((k : ℂ), (model.L : ℂ))

/-- Oriented source endpoint of either connector. -/
def ChapterVIDPrincipalGlobalRootModel.connectorSource
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalGlobalRootModel massProduct b d)
    (side : ChapterVIDOuterArcSide) (k : ℝ) : ℂ :=
  match side with
  | .initial => model.outerConnectorEndpoint .initial k
  | .final => model.localConnectorEndpoint .final k

/-- Oriented target endpoint of either connector. -/
def ChapterVIDPrincipalGlobalRootModel.connectorTarget
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalGlobalRootModel massProduct b d)
    (side : ChapterVIDOuterArcSide) (k : ℝ) : ℂ :=
  match side with
  | .initial => model.localConnectorEndpoint .initial k
  | .final => model.outerConnectorEndpoint .final k

/-- The affine root-coordinate point on a connector. -/
def ChapterVIDPrincipalGlobalRootModel.connectorPoint
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalGlobalRootModel massProduct b d)
    (side : ChapterVIDOuterArcSide) (point : ℝ × ℝ) : ℂ :=
  AffineMap.lineMap (model.connectorSource side point.1)
    (model.connectorTarget side point.1) point.2

/-- The actual connector as a path in Poincare's global root coordinate. -/
def ChapterVIDPrincipalGlobalRootModel.connectorPath
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalGlobalRootModel massProduct b d)
    (side : ChapterVIDOuterArcSide) (k : ℝ) :
    Path (model.connectorSource side k) (model.connectorTarget side k) :=
  Path.segment (model.connectorSource side k) (model.connectorTarget side k)

@[simp]
theorem ChapterVIDPrincipalGlobalRootModel.connectorPath_apply
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalGlobalRootModel massProduct b d)
    (side : ChapterVIDOuterArcSide) (k : ℝ) (t : I) :
    model.connectorPath side k t = model.connectorPoint side (k, t) := by
  simp [ChapterVIDPrincipalGlobalRootModel.connectorPath,
    ChapterVIDPrincipalGlobalRootModel.connectorPoint, Path.segment]

/-- The literal transformed source radicand on either connector. -/
def ChapterVIDPrincipalGlobalRootModel.connectorRadicand
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalGlobalRootModel massProduct b d)
    (side : ChapterVIDOuterArcSide) (point : ℝ × ℝ) : ℂ :=
  chapterVIDRootCoordinateRadicand
    (chapterVIDCriticalParameterRootAtD (point.1 : ℂ))
    (model.connectorPoint side point)

/-- The upper connector begins exactly where the initial compiled quarter ends. -/
theorem ChapterVIDPrincipalGlobalRootModel.initial_connector_source :
    ∀ {massProduct : ℂ} {b d : ℤ}
      (model : ChapterVIDPrincipalGlobalRootModel massProduct b d) (k : ℝ),
      model.connectorSource .initial k =
        chapterVIDOuterArcPoint .initial
          (chapterVIDCriticalToGlobalParameter k, 1) := by
  intros
  rfl

/-- The lower connector ends exactly where the final compiled quarter begins. -/
theorem ChapterVIDPrincipalGlobalRootModel.final_connector_target :
    ∀ {massProduct : ℂ} {b d : ℤ}
      (model : ChapterVIDPrincipalGlobalRootModel massProduct b d) (k : ℝ),
      model.connectorTarget .final k =
        chapterVIDOuterArcPoint .final
          (chapterVIDCriticalToGlobalParameter k, 0) := by
  intros
  rfl

/-- The upper connector ends at the source of the root-coordinate middle path. -/
theorem ChapterVIDPrincipalGlobalRootModel.initial_connector_target
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalGlobalRootModel massProduct b d)
    (k : ℝ) :
    model.connectorTarget .initial k =
      chapterVIDCriticalMorseRootPoint
        ((k : ℂ), ((-model.L : ℝ) : ℂ)) := by
  rfl

/-- The lower connector begins at the target of the root-coordinate middle path. -/
theorem ChapterVIDPrincipalGlobalRootModel.final_connector_source
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalGlobalRootModel massProduct b d)
    (k : ℝ) :
    model.connectorSource .final k =
      chapterVIDCriticalMorseRootPoint
        ((k : ℂ), (model.L : ℂ)) := by
  rfl

/-- At the local endpoint, changing back to Poincare's original contour coordinate agrees
exactly with the previously formalized local middle path. -/
theorem ChapterVIDPrincipalGlobalRootModel.rootToSource_localConnectorEndpoint
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalGlobalRootModel massProduct b d)
    (side : ChapterVIDOuterArcSide) (k : ℝ)
    (hk : k ∈ Set.Icc 0 model.δ) :
    chapterVIDRootToOriginalContour (model.localConnectorEndpoint side k) =
      match side with
      | .initial =>
          chapterVIDPrincipalLocalSourceFiber (k : ℂ) ((-model.L : ℝ) : ℂ)
      | .final =>
          chapterVIDPrincipalLocalSourceFiber (k : ℂ) (model.L : ℂ) := by
  cases side
  · exact model.root_source_eq k hk (-model.L)
      Set.left_mem_uIcc
  · exact model.root_source_eq k hk model.L
      Set.right_mem_uIcc

/-- A point on one of the two compact connector rectangles. -/
def ChapterVIDPrincipalConnectorModel.rectanglePoint
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) (st : I × I) : ℂ :=
  model.rootModel.connectorPoint side
    (model.criticalValue st.1, (st.2 : ℝ))

/-- The literal root-coordinate source radicand on a compact connector rectangle. -/
def ChapterVIDPrincipalConnectorModel.rectangleRadicand
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) (st : I × I) : ℂ :=
  chapterVIDRootCoordinateRadicand
    (chapterVIDCriticalParameterRootAtD (model.criticalValue st.1 : ℂ))
    (model.rectanglePoint side st)

/-- This is the exact finite-certificate target for either connector. -/
abbrev ChapterVIDConnectorNonvanishingCertificate
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) :=
  ChapterVIFiniteNonvanishingCover (model.rectangleRadicand side)

@[simp]
theorem ChapterVIDPrincipalConnectorModel.rectanglePoint_initial_zero
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d) (s : I) :
    model.rectanglePoint .initial (s, 0) =
      chapterVIDOuterArcPoint .initial
        (chapterVIDCriticalToGlobalParameter (model.criticalValue s), 1) := by
  simp [ChapterVIDPrincipalConnectorModel.rectanglePoint,
    ChapterVIDPrincipalGlobalRootModel.connectorPoint,
    ChapterVIDPrincipalGlobalRootModel.connectorSource,
    ChapterVIDPrincipalGlobalRootModel.outerConnectorEndpoint,
    AffineMap.lineMap_apply]

@[simp]
theorem ChapterVIDPrincipalConnectorModel.rectanglePoint_final_one
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d) (s : I) :
    model.rectanglePoint .final (s, 1) =
      chapterVIDOuterArcPoint .final
        (chapterVIDCriticalToGlobalParameter (model.criticalValue s), 0) := by
  simp [ChapterVIDPrincipalConnectorModel.rectanglePoint,
    ChapterVIDPrincipalGlobalRootModel.connectorPoint,
    ChapterVIDPrincipalGlobalRootModel.connectorTarget,
    ChapterVIDPrincipalGlobalRootModel.outerConnectorEndpoint,
    AffineMap.lineMap_apply]

/-- Along the shared upper boundary, the connector certificate evaluates exactly the same
literal radicand as the initial compiled outer quarter. -/
theorem ChapterVIDPrincipalConnectorModel.rectangleRadicand_initial_zero
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d) (s : I) :
    model.rectangleRadicand .initial (s, 0) =
      chapterVIDOuterArcRadicand .initial
        (chapterVIDCriticalToGlobalParameter (model.criticalValue s), 1) := by
  unfold ChapterVIDPrincipalConnectorModel.rectangleRadicand
    chapterVIDOuterArcRadicand
  rw [model.rectanglePoint_initial_zero]
  rw [model.parameterRoot_eq_global (model.criticalValue s)
    (model.criticalValue_mem s)]

/-- Along the shared lower boundary, the connector certificate evaluates exactly the same
literal radicand as the final compiled outer quarter. -/
theorem ChapterVIDPrincipalConnectorModel.rectangleRadicand_final_one
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d) (s : I) :
    model.rectangleRadicand .final (s, 1) =
      chapterVIDOuterArcRadicand .final
        (chapterVIDCriticalToGlobalParameter (model.criticalValue s), 0) := by
  unfold ChapterVIDPrincipalConnectorModel.rectangleRadicand
    chapterVIDOuterArcRadicand
  rw [model.rectanglePoint_final_one]
  rw [model.parameterRoot_eq_global (model.criticalValue s)
    (model.criticalValue_mem s)]

end PoincareChapterVI
