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

/-- The compact local endpoints remain strictly in the negative half-plane. This quantitative
normalization is obtained when the local analytic model is shrunk, so it does not belong in a
compiled certificate. -/
theorem ChapterVIDPrincipalGlobalRootModel.localConnectorEndpoint_re_neg
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalGlobalRootModel massProduct b d)
    (side : ChapterVIDOuterArcSide) (k : ℝ)
    (hk : k ∈ Set.Icc 0 model.δ) :
    (model.localConnectorEndpoint side k).re < 0 := by
  have hcollisionRe : chapterVIDCollisionLift.re = -‖chapterVIDCollisionLift‖ := by
    rw [chapterVIDCollisionLift_eq_neg_norm]
    simp
  have hnormPos : 0 < ‖chapterVIDCollisionLift‖ :=
    norm_pos_iff.mpr chapterVIDCollisionLift_ne_zero
  cases side with
  | initial =>
      have hclose := model.root_close k hk (-model.L) Set.left_mem_uIcc
      rw [Complex.dist_eq] at hclose
      have hre := Complex.re_le_norm
        (chapterVIDCriticalMorseRootPoint
          ((k : ℂ), ((-model.L : ℝ) : ℂ)) - chapterVIDCollisionLift)
      unfold ChapterVIDPrincipalGlobalRootModel.localConnectorEndpoint
      change
        (chapterVIDCriticalMorseRootPoint
          ((k : ℂ), ((-model.L : ℝ) : ℂ))).re - chapterVIDCollisionLift.re ≤ _ at hre
      linarith
  | final =>
      have hclose := model.root_close k hk model.L Set.right_mem_uIcc
      rw [Complex.dist_eq] at hclose
      have hre := Complex.re_le_norm
        (chapterVIDCriticalMorseRootPoint
          ((k : ℂ), (model.L : ℂ)) - chapterVIDCollisionLift)
      unfold ChapterVIDPrincipalGlobalRootModel.localConnectorEndpoint
      change
        (chapterVIDCriticalMorseRootPoint
          ((k : ℂ), (model.L : ℂ))).re - chapterVIDCollisionLift.re ≤ _ at hre
      linarith

/-- The two outer endpoints facing the local segment lie on the imaginary axis. -/
theorem ChapterVIDPrincipalGlobalRootModel.outerConnectorEndpoint_re
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalGlobalRootModel massProduct b d)
    (side : ChapterVIDOuterArcSide) (k : ℝ) :
    (model.outerConnectorEndpoint side k).re = 0 := by
  cases side <;>
    simp [ChapterVIDPrincipalGlobalRootModel.outerConnectorEndpoint,
      chapterVIDOuterArcPoint]

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

/-- The global outer endpoint varies continuously over the compact connector parameter. -/
theorem ChapterVIDPrincipalConnectorModel.continuous_outerConnectorEndpoint
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) :
    Continuous (fun s : I ↦
      model.rootModel.outerConnectorEndpoint side (model.criticalValue s)) := by
  rw [continuous_iff_continuousAt]
  intro s
  have hinverse := model.rootModel.parameterInverse_analyticAt
    (model.criticalValue s) (model.criticalValue_mem_rootModel s)
  have hcritical : ContinuousAt
      (fun q : I ↦ (model.criticalValue q : ℂ)) s :=
    Complex.ofRealCLM.continuous.continuousAt.comp_of_eq
      (continuous_ChapterVIDPrincipalConnectorModel_criticalValue model).continuousAt rfl
  have hinverseComp : ContinuousAt
      (fun q : I ↦ chapterVIDCriticalParameterInverseAtD
        (model.criticalValue q : ℂ)) s :=
    hinverse.continuousAt.comp_of_eq hcritical rfl
  have hreal : ContinuousAt
      (fun q : I ↦ (chapterVIDCriticalParameterInverseAtD
        (model.criticalValue q : ℂ)).re) s :=
    Complex.continuous_re.continuousAt.comp_of_eq hinverseComp rfl
  have hraw : ContinuousAt
      (fun q : I ↦ chapterVIDCriticalToGlobalParameterRaw
        (model.criticalValue q)) s := by
    unfold chapterVIDCriticalToGlobalParameterRaw
    exact (continuousAt_const.sub hreal).div_const _
  have hparameter : ContinuousAt
      (fun q : I ↦ chapterVIDCriticalToGlobalParameter
        (model.criticalValue q)) s := by
    unfold chapterVIDCriticalToGlobalParameter
    exact (continuous_projIcc (h := zero_le_one)).continuousAt.comp_of_eq hraw rfl
  cases side
  · exact (continuous_chapterVIDOuterArcPoint .initial).continuousAt.comp_of_eq
      (hparameter.prodMk continuousAt_const) rfl
  · exact (continuous_chapterVIDOuterArcPoint .final).continuousAt.comp_of_eq
      (hparameter.prodMk continuousAt_const) rfl

/-- The local inverse-Morse endpoint varies continuously on the same compact interval. -/
theorem ChapterVIDPrincipalConnectorModel.continuous_localConnectorEndpoint
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) :
    Continuous (fun s : I ↦
      model.rootModel.localConnectorEndpoint side (model.criticalValue s)) := by
  rw [continuous_iff_continuousAt]
  intro s
  have hcritical : ContinuousAt
      (fun q : I ↦ (model.criticalValue q : ℂ)) s :=
    Complex.ofRealCLM.continuous.continuousAt.comp_of_eq
      (continuous_ChapterVIDPrincipalConnectorModel_criticalValue model).continuousAt rfl
  cases side
  · have hroot := model.rootModel.root_analyticAt
      (model.criticalValue s) (model.criticalValue_mem_rootModel s)
      (-model.rootModel.L) Set.left_mem_uIcc
    exact hroot.continuousAt.comp_of_eq
      (hcritical.prodMk continuousAt_const) rfl
  · have hroot := model.rootModel.root_analyticAt
      (model.criticalValue s) (model.criticalValue_mem_rootModel s)
      model.rootModel.L Set.right_mem_uIcc
    exact hroot.continuousAt.comp_of_eq
      (hcritical.prodMk continuousAt_const) rfl

theorem ChapterVIDPrincipalConnectorModel.continuous_connectorSource
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) :
    Continuous (fun s : I ↦
      model.rootModel.connectorSource side (model.criticalValue s)) := by
  cases side
  · exact model.continuous_outerConnectorEndpoint .initial
  · exact model.continuous_localConnectorEndpoint .final

theorem ChapterVIDPrincipalConnectorModel.continuous_connectorTarget
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) :
    Continuous (fun s : I ↦
      model.rootModel.connectorTarget side (model.criticalValue s)) := by
  cases side
  · exact model.continuous_localConnectorEndpoint .initial
  · exact model.continuous_outerConnectorEndpoint .final

/-- Continuity of the affine root-coordinate connector is analytic and does not belong in the
compiled certificate. -/
theorem ChapterVIDPrincipalConnectorModel.continuous_rectanglePoint
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) :
    Continuous (model.rectanglePoint side) := by
  unfold ChapterVIDPrincipalConnectorModel.rectanglePoint
    ChapterVIDPrincipalGlobalRootModel.connectorPoint
  simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
  have hsource : Continuous (fun st : I × I ↦
      model.rootModel.connectorSource side (model.criticalValue st.1)) :=
    (model.continuous_connectorSource side).comp continuous_fst
  have htarget : Continuous (fun st : I × I ↦
      model.rootModel.connectorTarget side (model.criticalValue st.1)) :=
    (model.continuous_connectorTarget side).comp continuous_fst
  have hscalar : Continuous (fun st : I × I ↦ (st.2 : ℝ)) :=
    continuous_subtype_val.comp continuous_snd
  exact (hscalar.smul (htarget.sub hsource)).add hsource

/-- The affine connector coordinate never reaches the origin. Except at its outer endpoint its
real part is strictly negative; the outer endpoint itself has positive norm. Thus coordinate
nonvanishing is analytic geometry, not a finite-computation obligation. -/
theorem ChapterVIDPrincipalConnectorModel.rectanglePoint_ne_zero
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) (st : I × I) :
    model.rectanglePoint side st ≠ 0 := by
  have hlocal := model.rootModel.localConnectorEndpoint_re_neg side
    (model.criticalValue st.1) (model.criticalValue_mem_rootModel st.1)
  have houter := model.rootModel.outerConnectorEndpoint_re side
    (model.criticalValue st.1)
  cases side with
  | initial =>
      by_cases ht : (st.2 : ℝ) = 0
      · have hpoint : model.rectanglePoint .initial st =
            model.rootModel.outerConnectorEndpoint .initial
              (model.criticalValue st.1) := by
          simp [ChapterVIDPrincipalConnectorModel.rectanglePoint,
            ChapterVIDPrincipalGlobalRootModel.connectorPoint,
            ChapterVIDPrincipalGlobalRootModel.connectorSource,
            ChapterVIDPrincipalGlobalRootModel.connectorTarget,
            AffineMap.lineMap_apply, ht]
        rw [hpoint]
        exact chapterVIDOuterArcPoint_ne_zero .initial _
      · intro hzero
        have hre := congrArg Complex.re hzero
        simp only [Complex.zero_re] at hre
        unfold ChapterVIDPrincipalConnectorModel.rectanglePoint
          ChapterVIDPrincipalGlobalRootModel.connectorPoint
          ChapterVIDPrincipalGlobalRootModel.connectorSource
          ChapterVIDPrincipalGlobalRootModel.connectorTarget at hre
        simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add,
          Complex.add_re, Complex.smul_re, Complex.sub_re, smul_eq_mul] at hre
        have htpos : 0 < (st.2 : ℝ) :=
          lt_of_le_of_ne st.2.property.1 (Ne.symm ht)
        rw [houter, sub_zero, add_zero] at hre
        exact (mul_neg_of_pos_of_neg htpos hlocal).ne hre
  | final =>
      by_cases ht : (st.2 : ℝ) = 1
      · have hpoint : model.rectanglePoint .final st =
            model.rootModel.outerConnectorEndpoint .final
              (model.criticalValue st.1) := by
          simp [ChapterVIDPrincipalConnectorModel.rectanglePoint,
            ChapterVIDPrincipalGlobalRootModel.connectorPoint,
            ChapterVIDPrincipalGlobalRootModel.connectorSource,
            ChapterVIDPrincipalGlobalRootModel.connectorTarget,
            AffineMap.lineMap_apply, ht]
        rw [hpoint]
        exact chapterVIDOuterArcPoint_ne_zero .final _
      · intro hzero
        have hre := congrArg Complex.re hzero
        simp only [Complex.zero_re] at hre
        unfold ChapterVIDPrincipalConnectorModel.rectanglePoint
          ChapterVIDPrincipalGlobalRootModel.connectorPoint
          ChapterVIDPrincipalGlobalRootModel.connectorSource
          ChapterVIDPrincipalGlobalRootModel.connectorTarget at hre
        simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add,
          Complex.add_re, Complex.smul_re, Complex.sub_re, smul_eq_mul] at hre
        have htlt : (st.2 : ℝ) < 1 := lt_of_le_of_ne st.2.property.2 ht
        rw [houter, zero_sub] at hre
        have hrewrite :
            (st.2 : ℝ) * -(
                model.rootModel.localConnectorEndpoint .final
                  (model.criticalValue st.1)).re +
              (model.rootModel.localConnectorEndpoint .final
                (model.criticalValue st.1)).re =
              (1 - (st.2 : ℝ)) *
                (model.rootModel.localConnectorEndpoint .final
                  (model.criticalValue st.1)).re := by ring
        rw [hrewrite] at hre
        exact (mul_neg_of_pos_of_neg (sub_pos.mpr htlt) hlocal).ne hre

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

/-- On the boundary shared with the local middle path, the upper connector radicand is exactly
the prepared Morse radicand at `v=-L`. -/
theorem ChapterVIDPrincipalConnectorModel.rectangleRadicand_initial_one
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d) (s : I) :
    model.rectangleRadicand .initial (s, 1) =
      (model.criticalValue s : ℂ) + ((-model.rootModel.L : ℝ) : ℂ) ^ 2 := by
  have hk := model.criticalValue_mem_rootModel s
  have hroot := model.rootModel.root_radicand_eq
    (model.criticalValue s) hk (-model.rootModel.L) Set.left_mem_uIcc
  have hmorse := model.rootModel.radicand_eq
    (model.criticalValue s) hk (-model.rootModel.L) Set.left_mem_uIcc
  have hmorse' : chapterVIDRadicand
      (chapterVIDCriticalMorseSourcePointAtD
        ((model.criticalValue s : ℂ), ((-model.rootModel.L : ℝ) : ℂ))) =
      (model.criticalValue s : ℂ) + ((-model.rootModel.L : ℝ) : ℂ) ^ 2 := by
    simpa only [chapterVIDRealCriticalMorseSourcePoint] using hmorse
  unfold ChapterVIDPrincipalConnectorModel.rectangleRadicand
    ChapterVIDPrincipalConnectorModel.rectanglePoint
    ChapterVIDPrincipalGlobalRootModel.connectorPoint
    ChapterVIDPrincipalGlobalRootModel.connectorSource
    ChapterVIDPrincipalGlobalRootModel.connectorTarget
    ChapterVIDPrincipalGlobalRootModel.localConnectorEndpoint at ⊢
  simp only [AffineMap.lineMap_apply]
  simp
  simpa using hroot.trans hmorse'

/-- The lower connector has the same exact local-normal-form identity at `v=+L`. -/
theorem ChapterVIDPrincipalConnectorModel.rectangleRadicand_final_zero
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d) (s : I) :
    model.rectangleRadicand .final (s, 0) =
      (model.criticalValue s : ℂ) + ((model.rootModel.L : ℝ) : ℂ) ^ 2 := by
  have hk := model.criticalValue_mem_rootModel s
  have hroot := model.rootModel.root_radicand_eq
    (model.criticalValue s) hk model.rootModel.L Set.right_mem_uIcc
  have hmorse := model.rootModel.radicand_eq
    (model.criticalValue s) hk model.rootModel.L Set.right_mem_uIcc
  have hmorse' : chapterVIDRadicand
      (chapterVIDCriticalMorseSourcePointAtD
        ((model.criticalValue s : ℂ), (model.rootModel.L : ℂ))) =
      (model.criticalValue s : ℂ) + (model.rootModel.L : ℂ) ^ 2 := by
    simpa only [chapterVIDRealCriticalMorseSourcePoint] using hmorse
  unfold ChapterVIDPrincipalConnectorModel.rectangleRadicand
    ChapterVIDPrincipalConnectorModel.rectanglePoint
    ChapterVIDPrincipalGlobalRootModel.connectorPoint
    ChapterVIDPrincipalGlobalRootModel.connectorSource
    ChapterVIDPrincipalGlobalRootModel.connectorTarget
    ChapterVIDPrincipalGlobalRootModel.localConnectorEndpoint at ⊢
  simp only [AffineMap.lineMap_apply]
  simp
  exact hroot.trans hmorse'

end PoincareChapterVI
