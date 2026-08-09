/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.ChapterVIDConnectorFullBulk
import PoincareChapterVI.ChapterVIDConnectorPlacement
import PoincareChapterVI.ChapterVIFiveArcDecomposition

/-!
# The jointly moving five-piece contour at Poincare's point D

This file turns the five separately certified pieces into one actual closed path in the global
root coordinate.  Unlike the discarded fixed-unit-circle interface, its parameter and its cycle
move together.  The construction is geometric; the companion definitions below retain the five
piecewise square-root branches so that seam compatibility can be stated without pretending that
one current-parameter global square-root function has already been chosen.
-/

noncomputable section

open Complex Set Topology
open scoped unitInterval

namespace PoincareChapterVI
namespace ChapterVIDJointLiftedContour

/-- Either rational outer quarter as a genuine path in the global root coordinate. -/
def outerRootPath (side : ChapterVIDOuterArcSide) (s : I) :
    Path (chapterVIDOuterArcPoint side (s, 0))
      (chapterVIDOuterArcPoint side (s, 1)) where
  toFun t := chapterVIDOuterArcPoint side (s, t)
  continuous_toFun := (continuous_chapterVIDOuterArcPoint side).comp
    (continuous_const.prodMk continuous_id)
  source' := rfl
  target' := rfl

@[simp] theorem outerRootPath_apply
    (side : ChapterVIDOuterArcSide) (s t : I) :
    outerRootPath side s t = chapterVIDOuterArcPoint side (s, t) := by
  simp [outerRootPath]

/-- The two outer quarters meet at the same positive-real base point. -/
theorem outerRootPath_final_target_eq_initial_source (s : I) :
    chapterVIDOuterArcPoint .final (s, 1) =
      chapterVIDOuterArcPoint .initial (s, 0) := by
  exact (ChapterVIDOuterArcRegularity.outerArcPoint_initial_zero_eq_final_one s).symm

/-- The upper affine connector with its outer and local endpoints exposed in the type. -/
def upperConnectorPath
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d) (s : I) :
    Path
    (chapterVIDOuterArcPoint .initial
      (chapterVIDCriticalToGlobalParameter (model.criticalValue s), 0))
      (chapterVIDCriticalMorseRootPoint
        (((model.criticalValue s : ℝ) : ℂ), ((-model.rootModel.L : ℝ) : ℂ))) :=
  let k := model.criticalValue s
  (outerRootPath .initial (chapterVIDCriticalToGlobalParameter k)).trans
    ((model.rootModel.connectorPath .initial k).cast
      (model.rootModel.initial_connector_source k).symm
      (model.rootModel.initial_connector_target k).symm)

/-- The inverse-Morse middle segment followed by the lower affine connector. -/
def middleAndLowerPath
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d) (s : I) :
    Path (chapterVIDCriticalMorseRootPoint
      (((model.criticalValue s : ℝ) : ℂ), ((-model.rootModel.L : ℝ) : ℂ)))
    (chapterVIDOuterArcPoint .final
      (chapterVIDCriticalToGlobalParameter (model.criticalValue s), 0)) :=
  let k := model.criticalValue s
  (model.rootModel.rootPath k
      (model.criticalValue_mem_rootModel s)).trans
    ((model.rootModel.connectorPath .final k).cast (by rfl)
      (model.rootModel.final_connector_target k).symm)

/-- The final quarter, cast only at its endpoint to the common positive-real base point. -/
def closedOuterFinalPath
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d) (s : I) :
    Path
      (chapterVIDOuterArcPoint .final
        (chapterVIDCriticalToGlobalParameter (model.criticalValue s), 0))
      (chapterVIDOuterArcPoint .initial
        (chapterVIDCriticalToGlobalParameter (model.criticalValue s), 0)) := by
  let g := chapterVIDCriticalToGlobalParameter (model.criticalValue s)
  exact (outerRootPath .final g).cast rfl
    (ChapterVIDOuterArcRegularity.outerArcPoint_initial_zero_eq_final_one g)

/-- The actual closed root-coordinate contour obtained by concatenating the five pieces. -/
def rootContour
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d) (s : I) :
    Path
      (chapterVIDOuterArcPoint .initial
        (chapterVIDCriticalToGlobalParameter (model.criticalValue s), 0))
      (chapterVIDOuterArcPoint .initial
        (chapterVIDCriticalToGlobalParameter (model.criticalValue s), 0)) :=
  (upperConnectorPath model s).trans
    ((middleAndLowerPath model s).trans (closedOuterFinalPath model s))

/-- The five-piece contour is closed by construction, with no endpoint equality left as an
external premise. -/
theorem rootContour_source_eq_target
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d) (s : I) :
    rootContour model s 0 = rootContour model s 1 := by
  simp [rootContour]

/-- Concatenating two paths that avoid the root-coordinate origin preserves avoidance. -/
private theorem trans_ne_zero
    {a b c : ℂ} (first : Path a b) (second : Path b c)
    (hfirst : ∀ t, first t ≠ 0) (hsecond : ∀ t, second t ≠ 0) :
    ∀ t, first.trans second t ≠ 0 := by
  intro t
  have hmem : first.trans second t ∈ Set.range (first.trans second) := ⟨t, rfl⟩
  rw [Path.trans_range] at hmem
  rcases hmem with hmem | hmem
  · obtain ⟨u, hu⟩ := hmem
    rw [← hu]
    exact hfirst u
  · obtain ⟨u, hu⟩ := hmem
    rw [← hu]
    exact hsecond u

/-- A pointwise predicate inherited by both pieces is inherited by their concatenation. -/
private theorem trans_forall
    {X : Type*} [TopologicalSpace X] {a b c : X}
    (first : Path a b) (second : Path b c) (predicate : X → Prop)
    (hfirst : ∀ t, predicate (first t)) (hsecond : ∀ t, predicate (second t)) :
    ∀ t, predicate (first.trans second t) := by
  intro t
  have hmem : first.trans second t ∈ Set.range (first.trans second) := ⟨t, rfl⟩
  rw [Path.trans_range] at hmem
  rcases hmem with hmem | hmem
  · obtain ⟨u, hu⟩ := hmem
    rw [← hu]
    exact hfirst u
  · obtain ⟨u, hu⟩ := hmem
    rw [← hu]
    exact hsecond u

theorem outerRootPath_ne_zero
    (side : ChapterVIDOuterArcSide) (s t : I) :
    outerRootPath side s t ≠ 0 := by
  rw [outerRootPath_apply]
  exact chapterVIDOuterArcPoint_ne_zero side (s, t)

theorem connectorRootPath_ne_zero
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) (s t : I) :
    model.rootModel.connectorPath side (model.criticalValue s) t ≠ 0 := by
  rw [model.rootModel.connectorPath_apply]
  exact model.rectanglePoint_ne_zero side (s, t)

theorem middleRootPath_ne_zero
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d) (s t : I) :
    model.rootModel.rootPath (model.criticalValue s)
        (model.criticalValue_mem_rootModel s) t ≠ 0 := by
  rw [model.rootModel.rootPath_apply]
  apply model.rootModel.root_ne_zero (model.criticalValue s)
    (model.criticalValue_mem_rootModel s)
  rw [Set.uIcc_of_le (by linarith [model.rootModel.L_pos])]
  constructor <;>
    nlinarith [model.rootModel.L_pos, t.property.1, t.property.2]

theorem upperConnectorPath_ne_zero
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d) (s t : I) :
    upperConnectorPath model s t ≠ 0 := by
  apply trans_ne_zero
  · exact outerRootPath_ne_zero .initial _
  · exact connectorRootPath_ne_zero model .initial s

theorem middleAndLowerPath_ne_zero
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d) (s t : I) :
    middleAndLowerPath model s t ≠ 0 := by
  apply trans_ne_zero
  · exact middleRootPath_ne_zero model s
  · exact connectorRootPath_ne_zero model .final s

theorem closedOuterFinalPath_ne_zero
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d) (s t : I) :
    closedOuterFinalPath model s t ≠ 0 := by
  change outerRootPath .final
      (chapterVIDCriticalToGlobalParameter (model.criticalValue s)) t ≠ 0
  exact outerRootPath_ne_zero .final _ _

/-- Every pre-collision and collision member of the assembled five-piece contour avoids the
coordinate singularity `u=0`. -/
theorem rootContour_ne_zero
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d) (s t : I) :
    rootContour model s t ≠ 0 := by
  apply trans_ne_zero
  · exact upperConnectorPath_ne_zero model s
  · apply trans_ne_zero
    · exact middleAndLowerPath_ne_zero model s
    · exact closedOuterFinalPath_ne_zero model s

/-- The same jointly moving contour in Poincare's literal source coordinate, obtained through
his exact nonlinear `u -> t` map. -/
def sourceContour
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d) (s : I) :
    Path
      (chapterVIDRootToOriginalContour
        (chapterVIDOuterArcPoint .initial
          (chapterVIDCriticalToGlobalParameter (model.criticalValue s), 0)))
      (chapterVIDRootToOriginalContour
        (chapterVIDOuterArcPoint .initial
          (chapterVIDCriticalToGlobalParameter (model.criticalValue s), 0))) :=
  (rootContour model s).map' (by
    intro u hu
    obtain ⟨t, rfl⟩ := hu
    exact (analyticAt_chapterVIDRootToOriginalContour
      (rootContour_ne_zero model s t)).continuousAt.continuousWithinAt)

@[simp] theorem sourceContour_apply
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d) (s t : I) :
    sourceContour model s t = chapterVIDRootToOriginalContour (rootContour model s t) := by
  rfl

theorem sourceContour_closed
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d) (s : I) :
    sourceContour model s 0 = sourceContour model s 1 := by
  simp

/-- The literal transformed source radicand evaluated on the moving five-piece root contour. -/
def contourRadicand
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d) (s t : I) : ℂ :=
  chapterVIDRootCoordinateRadicand (model.connectorParameterRoot s)
    (rootContour model s t)

theorem outerRootPath_radicand_ne_zero
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) (s t : I) :
    chapterVIDRootCoordinateRadicand (model.connectorParameterRoot s)
      (outerRootPath side
        (chapterVIDCriticalToGlobalParameter (model.criticalValue s)) t) ≠ 0 := by
  rw [outerRootPath_apply]
  unfold ChapterVIDPrincipalConnectorModel.connectorParameterRoot
  rw [model.parameterRoot_eq_global (model.criticalValue s)
    (model.criticalValue_mem s)]
  exact ChapterVIDOuterArcPolarCompiledGrid.radicand_ne_zero_of_run
    ChapterVIDOuterArcPolarCompiledGrid.referenceRunVerdict side
      (chapterVIDCriticalToGlobalParameter (model.criticalValue s), t)

theorem middleRootPath_radicand_ne_zero
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    {s : I} (hs : s ≠ 1) (t : I) :
    chapterVIDRootCoordinateRadicand (model.connectorParameterRoot s)
      (model.rootModel.rootPath (model.criticalValue s)
        (model.criticalValue_mem_rootModel s) t) ≠ 0 := by
  let v : ℝ := 2 * model.rootModel.L * (t : ℝ) - model.rootModel.L
  have hv : v ∈ Set.uIcc (-model.rootModel.L) model.rootModel.L := by
    rw [Set.uIcc_of_le (by linarith [model.rootModel.L_pos])]
    constructor <;> dsimp [v] <;>
      nlinarith [model.rootModel.L_pos, t.property.1, t.property.2]
  have hk := model.criticalValue_mem_rootModel s
  have hroot := model.rootModel.root_radicand_eq
    (model.criticalValue s) hk v hv
  have hmorse := model.rootModel.radicand_eq
    (model.criticalValue s) hk v hv
  have hmorse' : chapterVIDRadicand
      (chapterVIDCriticalMorseSourcePointAtD
        ((model.criticalValue s : ℂ), (v : ℂ))) =
      (model.criticalValue s : ℂ) + (v : ℂ) ^ 2 := by
    simpa only [chapterVIDRealCriticalMorseSourcePoint] using hmorse
  have hkpos : 0 < model.criticalValue s := by
    unfold ChapterVIDPrincipalConnectorModel.criticalValue
    apply mul_pos model.κ_pos
    exact sub_pos.mpr (lt_of_le_of_ne s.property.2 (fun h ↦ hs (Subtype.ext h)))
  rw [model.rootModel.rootPath_apply]
  change chapterVIDRootCoordinateRadicand
      (chapterVIDCriticalParameterRootAtD (model.criticalValue s : ℂ))
      (chapterVIDCriticalMorseRootPoint ((model.criticalValue s : ℂ), (v : ℂ))) ≠ 0
  rw [hroot, hmorse']
  rw [show (model.criticalValue s : ℂ) + (v : ℂ) ^ 2 =
      ((model.criticalValue s + v ^ 2 : ℝ) : ℂ) by
    push_cast
    ring]
  exact Complex.ofReal_ne_zero.mpr
    (ne_of_gt (add_pos_of_pos_of_nonneg hkpos (sq_nonneg v)))

/-- The full-bulk and homogeneous certificates prove nonvanishing of the actual radicand on the
entire jointly moving five-piece contour at every positive critical value. -/
theorem contourRadicand_ne_zero
    {massProduct : ℂ} {b d : ℤ}
    (anchored : ChapterVIDAnchoredConnectorModel massProduct b d)
    (hL : anchored.rootModel.L ≤ 1 / (2 : ℝ) ^ 20)
    (uniform : ChapterVIDUniformAnchorData anchored (1 / (2 : ℝ) ^ 10))
    {s : I} (hs : s ≠ 1) (t : I) :
    contourRadicand anchored.toChapterVIDPrincipalConnectorModel s t ≠ 0 := by
  let model := anchored.toChapterVIDPrincipalConnectorModel
  let predicate : ℂ → Prop := fun u ↦
    chapterVIDRootCoordinateRadicand (model.connectorParameterRoot s) u ≠ 0
  have hconnector (side : ChapterVIDOuterArcSide) (τ : I) :
      predicate (model.rootModel.connectorPath side (model.criticalValue s) τ) := by
    rw [model.rootModel.connectorPath_apply]
    exact ChapterVIDConnectorFullBulk.radicand_ne_zero_on_puncturedRectangle
      anchored hL uniform side (s, τ) hs
  have hupper : ∀ τ, predicate (upperConnectorPath model s τ) := by
    apply trans_forall _ _ predicate
    · exact outerRootPath_radicand_ne_zero model .initial s
    · exact hconnector .initial
  have hmiddleLower : ∀ τ, predicate (middleAndLowerPath model s τ) := by
    apply trans_forall _ _ predicate
    · exact middleRootPath_radicand_ne_zero model hs
    · exact hconnector .final
  have hfinal : ∀ τ, predicate (closedOuterFinalPath model s τ) := by
    intro τ
    change predicate (outerRootPath .final
      (chapterVIDCriticalToGlobalParameter (model.criticalValue s)) τ)
    exact outerRootPath_radicand_ne_zero model .final s τ
  unfold contourRadicand rootContour
  change predicate ((upperConnectorPath model s).trans
    ((middleAndLowerPath model s).trans (closedOuterFinalPath model s)) t)
  exact trans_forall _ _ predicate hupper
    (trans_forall _ _ predicate hmiddleLower hfinal) t

theorem continuous_outerRootPath_family (side : ChapterVIDOuterArcSide) :
    Continuous ↿fun s : I ↦ outerRootPath side s := by
  change Continuous (fun st : I × I ↦ chapterVIDOuterArcPoint side st)
  exact continuous_chapterVIDOuterArcPoint side

theorem continuous_connectorRootPath_family
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) :
    Continuous ↿fun s : I ↦
      model.rootModel.connectorPath side (model.criticalValue s) := by
  change Continuous (fun st : I × I ↦ model.rectanglePoint side st)
  exact model.continuous_rectanglePoint side

/-- The compact critical-value interval has a genuinely continuous global radial parameter;
the unclamped inverse is analytic on this model's neighborhood. -/
theorem continuous_connectorGlobalParameter
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d) :
    Continuous (fun s : I ↦
      chapterVIDCriticalToGlobalParameter (model.criticalValue s)) := by
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
  unfold chapterVIDCriticalToGlobalParameter
  exact (continuous_projIcc (h := zero_le_one)).continuousAt.comp_of_eq hraw rfl

theorem continuous_middleRootPath_family
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d) :
    Continuous ↿fun s : I ↦ model.rootModel.rootPath (model.criticalValue s)
      (model.criticalValue_mem_rootModel s) := by
  rw [continuous_iff_continuousAt]
  intro st
  let v : ℝ := 2 * model.rootModel.L * (st.2 : ℝ) - model.rootModel.L
  have hv : v ∈ Set.uIcc (-model.rootModel.L) model.rootModel.L := by
    rw [Set.uIcc_of_le (by linarith [model.rootModel.L_pos])]
    constructor <;> dsimp [v] <;>
      nlinarith [model.rootModel.L_pos, st.2.property.1, st.2.property.2]
  have hroot := model.rootModel.root_analyticAt
    (model.criticalValue st.1) (model.criticalValue_mem_rootModel st.1) v hv
  have hinput : ContinuousAt (fun point : I × I ↦
      ((model.criticalValue point.1 : ℂ),
        model.rootModel.morseLine (point.2 : ℝ))) st := by
    exact ((Complex.ofRealCLM.continuous.comp
      ((continuous_ChapterVIDPrincipalConnectorModel_criticalValue model).comp
        continuous_fst)).prodMk (by
          unfold ChapterVIDPrincipalGlobalRootModel.morseLine
            chapterVIDPrincipalLocalMorseLine
          fun_prop)).continuousAt
  exact hroot.continuousAt.comp_of_eq hinput rfl

theorem continuous_upperConnectorPath_family
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d) :
    Continuous ↿fun s : I ↦ upperConnectorPath model s := by
  unfold upperConnectorPath
  have houter : Continuous ↿fun s : I ↦ outerRootPath .initial
      (chapterVIDCriticalToGlobalParameter (model.criticalValue s)) := by
    change Continuous (fun st : I × I ↦ chapterVIDOuterArcPoint .initial
      (chapterVIDCriticalToGlobalParameter (model.criticalValue st.1), st.2))
    exact (continuous_chapterVIDOuterArcPoint .initial).comp
      (((continuous_connectorGlobalParameter model).comp continuous_fst).prodMk
        continuous_snd)
  exact Path.trans_continuous_family _ houter _
    (continuous_connectorRootPath_family model .initial)

theorem continuous_middleAndLowerPath_family
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d) :
    Continuous ↿fun s : I ↦ middleAndLowerPath model s := by
  unfold middleAndLowerPath
  exact Path.trans_continuous_family _ (continuous_middleRootPath_family model) _
    (continuous_connectorRootPath_family model .final)

theorem continuous_closedOuterFinalPath_family
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d) :
    Continuous ↿fun s : I ↦ closedOuterFinalPath model s := by
  change Continuous (fun st : I × I ↦ chapterVIDOuterArcPoint .final
    (chapterVIDCriticalToGlobalParameter (model.criticalValue st.1), st.2))
  exact (continuous_chapterVIDOuterArcPoint .final).comp
    (((continuous_connectorGlobalParameter model).comp continuous_fst).prodMk
      continuous_snd)

/-- The assembled contour depends continuously on the critical-value parameter as well as on
its path parameter. -/
theorem continuous_rootContour_family
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d) :
    Continuous ↿fun s : I ↦ rootContour model s := by
  unfold rootContour
  exact Path.trans_continuous_family _ (continuous_upperConnectorPath_family model) _
    (Path.trans_continuous_family _ (continuous_middleAndLowerPath_family model) _
      (continuous_closedOuterFinalPath_family model))

/-- The five-piece root contour restricted to the genuine continuation interval, with the
collision endpoint removed.  Keeping both variables in one domain is essential: a square-root
sheet on this rectangle is the literal lift of the jointly moving contour. -/
def positiveContourPoint
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d) :
    ChapterVIDConnectorFullBulk.PositiveConnectorParameter × I → ℂ :=
  (fun point : I × I ↦ rootContour model point.1 point.2) ∘
    fun point ↦
      (ChapterVIDConnectorFullBulk.positiveParameterToUnit point.1, point.2)

theorem continuous_positiveContourPoint
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d) :
    Continuous (positiveContourPoint model) := by
  let inclusion :
      ChapterVIDConnectorFullBulk.PositiveConnectorParameter × I → I × I :=
    fun point ↦
      (ChapterVIDConnectorFullBulk.positiveParameterToUnit point.1, point.2)
  have hinclusion : Continuous inclusion :=
    (ChapterVIDConnectorFullBulk.continuous_positiveParameterToUnit.comp
      continuous_fst).prodMk continuous_snd
  have hcontour : Continuous (fun point : I × I ↦
      rootContour model point.1 point.2) :=
    continuous_rootContour_family model
  unfold positiveContourPoint
  exact hcontour.comp hinclusion

theorem positiveContourPoint_ne_zero
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (point : ChapterVIDConnectorFullBulk.PositiveConnectorParameter × I) :
    positiveContourPoint model point ≠ 0 :=
  rootContour_ne_zero model _ _

/-- The same moving cycle in Poincare's literal source contour coordinate. -/
def positiveSourceContourPoint
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d) :
    ChapterVIDConnectorFullBulk.PositiveConnectorParameter × I → ℂ :=
  fun point ↦ chapterVIDRootToOriginalContour (positiveContourPoint model point)

theorem continuous_positiveSourceContourPoint
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d) :
    Continuous (positiveSourceContourPoint model) := by
  rw [continuous_iff_continuousAt]
  intro point
  exact (analyticAt_chapterVIDRootToOriginalContour
    (positiveContourPoint_ne_zero model point)).continuousAt.comp
      (continuous_positiveContourPoint model).continuousAt

theorem positiveSourceContourPoint_closed
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (s : ChapterVIDConnectorFullBulk.PositiveConnectorParameter) :
    positiveSourceContourPoint model (s, 0) =
      positiveSourceContourPoint model (s, 1) := by
  unfold positiveSourceContourPoint positiveContourPoint
  simp only [Function.comp_apply]
  rw [rootContour_source_eq_target]

/-- Poincare's literal transformed radicand on the full positive-parameter moving contour. -/
def positiveContourRadicand
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d) :
    ChapterVIDConnectorFullBulk.PositiveConnectorParameter × I → ℂ :=
  fun point ↦ chapterVIDRootCoordinateRadicand
    (model.connectorParameterRoot
      (ChapterVIDConnectorFullBulk.positiveParameterToUnit point.1))
    (positiveContourPoint model point)

/-- The radicand lifted above is literally Poincare's planar source radicand evaluated at the
corresponding source anomaly and source contour point; no surrogate polynomial replaces it. -/
theorem positiveContourRadicand_eq_literalSource
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (point : ChapterVIDConnectorFullBulk.PositiveConnectorParameter × I) :
    positiveContourRadicand model point =
      chapterVIPlanarSourceRadicand
        chapterVIDEccentricity chapterVIDComplement 0 1 2 2
        (positiveContourPoint model point ^ 3)
        (chapterVIDRootSecondAnomaly
          (model.connectorParameterRoot
            (ChapterVIDConnectorFullBulk.positiveParameterToUnit point.1))
          (positiveContourPoint model point)) :=
  rfl

theorem continuous_positiveContourRadicand
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d) :
    Continuous (positiveContourRadicand model) := by
  exact continuous_chapterVIDRootCoordinateRadicand_comp
    (model.continuous_connectorParameterRoot.comp
      (ChapterVIDConnectorFullBulk.continuous_positiveParameterToUnit.comp
        continuous_fst))
    (continuous_positiveContourPoint model)
    (fun point ↦ model.connectorParameterRoot_ne_zero _)
    (positiveContourPoint_ne_zero model)

theorem positiveContourRadicand_ne_zero
    {massProduct : ℂ} {b d : ℤ}
    (anchored : ChapterVIDAnchoredConnectorModel massProduct b d)
    (hL : anchored.rootModel.L ≤ 1 / (2 : ℝ) ^ 20)
    (uniform : ChapterVIDUniformAnchorData anchored (1 / (2 : ℝ) ^ 10))
    (point : ChapterVIDConnectorFullBulk.PositiveConnectorParameter × I) :
    positiveContourRadicand anchored.toChapterVIDPrincipalConnectorModel point ≠ 0 := by
  apply contourRadicand_ne_zero anchored hL uniform
  intro heq
  have hvalue := congrArg Subtype.val heq
  exact point.1.property.2.ne hvalue

/-- The certified nonvanishing result constructs one continuous square-root branch on the
entire jointly moving contour, normalized by any chosen square root at one base point.  This is
the global lifted-cycle object that the separate piece certificates were designed to supply. -/
theorem exists_positiveContourSquareRootSheet
    {massProduct : ℂ} {b d : ℤ}
    (anchored : ChapterVIDAnchoredConnectorModel massProduct b d)
    (hL : anchored.rootModel.L ≤ 1 / (2 : ℝ) ^ 20)
    (uniform : ChapterVIDUniformAnchorData anchored (1 / (2 : ℝ) ^ 10))
    (base : ChapterVIDConnectorFullBulk.PositiveConnectorParameter × I)
    (baseRoot : ℂ)
    (hbaseRoot : baseRoot ^ 2 =
      positiveContourRadicand anchored.toChapterVIDPrincipalConnectorModel base) :
    ∃ sheet : ChapterVIContinuousSquareRootSheet
        (positiveContourRadicand anchored.toChapterVIDPrincipalConnectorModel),
      sheet.root base = baseRoot := by
  let : ContractibleSpace ChapterVIDConnectorFullBulk.PositiveConnectorParameter :=
    (convex_Ico (0 : ℝ) 1).contractibleSpace ⟨0, by norm_num⟩
  let : LocallyPathConnectedSpace
      ChapterVIDConnectorFullBulk.PositiveConnectorParameter :=
    (convex_Ico (0 : ℝ) 1).locallyPathConnectedSpace
  let : ContractibleSpace I :=
    (convex_Icc (0 : ℝ) 1).contractibleSpace (by simp)
  let : LocallyPathConnectedSpace I :=
    (convex_Icc (0 : ℝ) 1).locallyPathConnectedSpace
  let : LocallyPathConnectedSpace
      (ChapterVIDConnectorFullBulk.PositiveConnectorParameter × I) := by
    refine LocallyPathConnectedSpace.of_bases
      (p := fun (point : ChapterVIDConnectorFullBulk.PositiveConnectorParameter × I)
          (sets : Set ChapterVIDConnectorFullBulk.PositiveConnectorParameter × Set I) ↦
        (sets.1 ∈ nhds point.1 ∧ IsPathConnected sets.1) ∧
          (sets.2 ∈ nhds point.2 ∧ IsPathConnected sets.2))
      (s := fun _ sets ↦ sets.1 ×ˢ sets.2) ?_ ?_
    · intro point
      rw [nhds_prod_eq]
      exact (path_connected_basis point.1).prod (path_connected_basis point.2)
    · intro _ sets hsets
      exact hsets.1.2.prod hsets.2.2
  exact exists_chapterVIContinuousSquareRootSheet _
    (continuous_positiveContourRadicand anchored.toChapterVIDPrincipalConnectorModel)
    (positiveContourRadicand_ne_zero anchored hL uniform)
    base baseRoot hbaseRoot

/-- The initial point of the certified positive-parameter continuation rectangle. -/
def positiveContourBase :
    ChapterVIDConnectorFullBulk.PositiveConnectorParameter × I :=
  (⟨0, by norm_num⟩, 0)

/-! ### The five dyadic subintervals of the assembled path -/

def outerInitialTime (t : I) : I :=
  ⟨(t : ℝ) / 4, by constructor <;> nlinarith [t.property.1, t.property.2]⟩

def upperConnectorTime (t : I) : I :=
  ⟨((t : ℝ) + 1) / 4, by constructor <;> nlinarith [t.property.1, t.property.2]⟩

def middleTime (t : I) : I :=
  ⟨((t : ℝ) + 4) / 8, by constructor <;> nlinarith [t.property.1, t.property.2]⟩

def lowerConnectorTime (t : I) : I :=
  ⟨((t : ℝ) + 5) / 8, by constructor <;> nlinarith [t.property.1, t.property.2]⟩

def outerFinalTime (t : I) : I :=
  ⟨((t : ℝ) + 3) / 4, by constructor <;> nlinarith [t.property.1, t.property.2]⟩

theorem continuous_outerInitialTime : Continuous outerInitialTime := by
  exact Continuous.subtype_mk (continuous_subtype_val.div_const 4) _
theorem continuous_upperConnectorTime : Continuous upperConnectorTime := by
  exact Continuous.subtype_mk
    ((continuous_subtype_val.add continuous_const).div_const 4) _
theorem continuous_middleTime : Continuous middleTime := by
  exact Continuous.subtype_mk
    ((continuous_subtype_val.add continuous_const).div_const 8) _
theorem continuous_lowerConnectorTime : Continuous lowerConnectorTime := by
  exact Continuous.subtype_mk
    ((continuous_subtype_val.add continuous_const).div_const 8) _
theorem continuous_outerFinalTime : Continuous outerFinalTime := by
  exact Continuous.subtype_mk
    ((continuous_subtype_val.add continuous_const).div_const 4) _

theorem rootContour_outerInitialTime
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d) (s t : I) :
    rootContour model s (outerInitialTime t) =
      outerRootPath .initial
        (chapterVIDCriticalToGlobalParameter (model.criticalValue s)) t := by
  simp [rootContour, upperConnectorPath, Path.trans_apply, outerInitialTime]
  split_ifs <;> try nlinarith [t.property.1, t.property.2]
  congr 2
  apply Subtype.ext
  ring

theorem rootContour_upperConnectorTime
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d) (s t : I) :
    rootContour model s (upperConnectorTime t) =
      model.rootModel.connectorPath .initial (model.criticalValue s) t := by
  by_cases ht : t = 0
  · subst t
    norm_num [rootContour, upperConnectorPath, upperConnectorTime, Path.trans_apply,
      ChapterVIDPrincipalGlobalRootModel.connectorSource,
      ChapterVIDPrincipalGlobalRootModel.connectorTarget,
      ChapterVIDPrincipalGlobalRootModel.outerConnectorEndpoint,
      ChapterVIDPrincipalGlobalRootModel.localConnectorEndpoint]
  · have htpos : 0 < (t : ℝ) := lt_of_le_of_ne t.property.1
      (fun h ↦ ht (Subtype.ext h.symm))
    rw [rootContour, Path.trans_apply, dif_pos (by
      change ((t : ℝ) + 1) / 4 ≤ 1 / 2
      nlinarith [t.property.2])]
    unfold upperConnectorPath
    simp only [ChapterVIDPrincipalGlobalRootModel.connectorSource,
      ChapterVIDPrincipalGlobalRootModel.connectorTarget,
      ChapterVIDPrincipalGlobalRootModel.outerConnectorEndpoint,
      ChapterVIDPrincipalGlobalRootModel.localConnectorEndpoint]
    rw [Path.trans_apply, dif_neg (by
      change ¬ 2 * (((t : ℝ) + 1) / 4) ≤ 1 / 2
      nlinarith)]
    congr 1
    apply Subtype.ext
    change 2 * (2 * (((t : ℝ) + 1) / 4)) - 1 = (t : ℝ)
    ring

theorem rootContour_middleTime
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d) (s t : I) :
    rootContour model s (middleTime t) =
      model.rootModel.rootPath (model.criticalValue s)
        (model.criticalValue_mem_rootModel s) t := by
  by_cases ht : t = 0
  · subst t
    norm_num [rootContour, upperConnectorPath, middleAndLowerPath, middleTime,
      Path.trans_apply,
      ChapterVIDPrincipalGlobalRootModel.connectorSource,
      ChapterVIDPrincipalGlobalRootModel.connectorTarget,
      ChapterVIDPrincipalGlobalRootModel.outerConnectorEndpoint,
      ChapterVIDPrincipalGlobalRootModel.localConnectorEndpoint]
  · have htpos : 0 < (t : ℝ) := lt_of_le_of_ne t.property.1
      (fun h ↦ ht (Subtype.ext h.symm))
    rw [rootContour, Path.trans_apply, dif_neg (by
      change ¬ ((t : ℝ) + 4) / 8 ≤ 1 / 2
      nlinarith)]
    rw [Path.trans_apply, dif_pos (by
      change 2 * (((t : ℝ) + 4) / 8) - 1 ≤ 1 / 2
      nlinarith [t.property.2])]
    unfold middleAndLowerPath
    simp only [ChapterVIDPrincipalGlobalRootModel.connectorSource,
      ChapterVIDPrincipalGlobalRootModel.connectorTarget,
      ChapterVIDPrincipalGlobalRootModel.outerConnectorEndpoint,
      ChapterVIDPrincipalGlobalRootModel.localConnectorEndpoint]
    rw [Path.trans_apply, dif_pos (by
      change 2 * (2 * (((t : ℝ) + 4) / 8) - 1) ≤ 1 / 2
      nlinarith [t.property.2])]
    congr 1
    apply Subtype.ext
    change 2 * (2 * (2 * (((t : ℝ) + 4) / 8) - 1)) = (t : ℝ)
    ring

theorem rootContour_lowerConnectorTime
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d) (s t : I) :
    rootContour model s (lowerConnectorTime t) =
      model.rootModel.connectorPath .final (model.criticalValue s) t := by
  by_cases ht : t = 0
  · subst t
    norm_num [rootContour, upperConnectorPath, middleAndLowerPath, lowerConnectorTime,
      Path.trans_apply,
      ChapterVIDPrincipalGlobalRootModel.connectorSource,
      ChapterVIDPrincipalGlobalRootModel.connectorTarget,
      ChapterVIDPrincipalGlobalRootModel.outerConnectorEndpoint,
      ChapterVIDPrincipalGlobalRootModel.localConnectorEndpoint]
  · have htpos : 0 < (t : ℝ) := lt_of_le_of_ne t.property.1
      (fun h ↦ ht (Subtype.ext h.symm))
    rw [rootContour, Path.trans_apply, dif_neg (by
      change ¬ ((t : ℝ) + 5) / 8 ≤ 1 / 2
      nlinarith)]
    rw [Path.trans_apply, dif_pos (by
      change 2 * (((t : ℝ) + 5) / 8) - 1 ≤ 1 / 2
      nlinarith [t.property.2])]
    unfold middleAndLowerPath
    simp only [ChapterVIDPrincipalGlobalRootModel.connectorSource,
      ChapterVIDPrincipalGlobalRootModel.connectorTarget,
      ChapterVIDPrincipalGlobalRootModel.outerConnectorEndpoint,
      ChapterVIDPrincipalGlobalRootModel.localConnectorEndpoint]
    rw [Path.trans_apply, dif_neg (by
      change ¬ 2 * (2 * (((t : ℝ) + 5) / 8) - 1) ≤ 1 / 2
      nlinarith)]
    congr 1
    apply Subtype.ext
    change 2 * (2 * (2 * (((t : ℝ) + 5) / 8) - 1)) - 1 = (t : ℝ)
    ring

theorem rootContour_outerFinalTime
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d) (s t : I) :
    rootContour model s (outerFinalTime t) =
      outerRootPath .final
        (chapterVIDCriticalToGlobalParameter (model.criticalValue s)) t := by
  by_cases ht : t = 0
  · subst t
    norm_num [rootContour, upperConnectorPath, middleAndLowerPath,
      closedOuterFinalPath, outerFinalTime, Path.trans_apply,
      ChapterVIDPrincipalGlobalRootModel.connectorSource,
      ChapterVIDPrincipalGlobalRootModel.connectorTarget,
      ChapterVIDPrincipalGlobalRootModel.outerConnectorEndpoint,
      ChapterVIDPrincipalGlobalRootModel.localConnectorEndpoint]
  · have htpos : 0 < (t : ℝ) := lt_of_le_of_ne t.property.1
      (fun h ↦ ht (Subtype.ext h.symm))
    rw [rootContour, Path.trans_apply, dif_neg (by
      change ¬ ((t : ℝ) + 3) / 4 ≤ 1 / 2
      nlinarith)]
    rw [Path.trans_apply, dif_neg (by
      change ¬ 2 * (((t : ℝ) + 3) / 4) - 1 ≤ 1 / 2
      nlinarith)]
    change chapterVIDOuterArcPoint .final
      (chapterVIDCriticalToGlobalParameter (model.criticalValue s), _) = _
    congr 2
    apply Subtype.ext
    change 2 * (2 * (((t : ℝ) + 3) / 4) - 1) - 1 = (t : ℝ)
    ring

/-- At the base point, normalize the joint lift by Mathlib's principal complex square root.
The subsequent values are determined by continuation, not by reapplying `Complex.sqrt`. -/
theorem exists_principalBasedPositiveContourSquareRootSheet
    {massProduct : ℂ} {b d : ℤ}
    (anchored : ChapterVIDAnchoredConnectorModel massProduct b d)
    (hL : anchored.rootModel.L ≤ 1 / (2 : ℝ) ^ 20)
    (uniform : ChapterVIDUniformAnchorData anchored (1 / (2 : ℝ) ^ 10)) :
    ∃ sheet : ChapterVIContinuousSquareRootSheet
        (positiveContourRadicand anchored.toChapterVIDPrincipalConnectorModel),
      sheet.root positiveContourBase =
        Complex.sqrt (positiveContourRadicand
          anchored.toChapterVIDPrincipalConnectorModel positiveContourBase) := by
  apply exists_positiveContourSquareRootSheet anchored hL uniform
  unfold Complex.sqrt
  exact Complex.cpow_nat_inv_pow _ (by norm_num : (2 : ℕ) ≠ 0)

/-! ### Identification with the certified branches on each piece -/

private abbrev PositiveContourDomain :=
  ChapterVIDConnectorFullBulk.PositiveConnectorParameter × I

private def pieceMap (time : I → I) : PositiveContourDomain → PositiveContourDomain :=
  fun point ↦ (point.1, time point.2)

private theorem continuous_pieceMap {time : I → I} (htime : Continuous time) :
    Continuous (pieceMap time) :=
  continuous_fst.prodMk (htime.comp continuous_snd)

private def restrictJointSheet
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    (sheet : ChapterVIContinuousSquareRootSheet (positiveContourRadicand model))
    (time : I → I) (htime : Continuous time) :
    ChapterVIContinuousSquareRootSheet
      (positiveContourRadicand model ∘ pieceMap time) where
  root point := sheet.root (pieceMap time point)
  continuous_root := sheet.continuous_root.comp (continuous_pieceMap htime)
  root_sq point := sheet.root_sq (pieceMap time point)

private def outerRectangleMap
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d) :
    PositiveContourDomain → I × I :=
  fun point ↦
    (chapterVIDCriticalToGlobalParameter
      (model.criticalValue
        (ChapterVIDConnectorFullBulk.positiveParameterToUnit point.1)), point.2)

private theorem continuous_outerRectangleMap
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d) :
    Continuous (outerRectangleMap model) := by
  exact ((continuous_connectorGlobalParameter model).comp
      (ChapterVIDConnectorFullBulk.continuous_positiveParameterToUnit.comp
        continuous_fst)).prodMk continuous_snd

private theorem positiveContourRadicand_outerInitialTime
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (point : PositiveContourDomain) :
    positiveContourRadicand model (pieceMap outerInitialTime point) =
      chapterVIDOuterArcRadicand .initial (outerRectangleMap model point) := by
  unfold positiveContourRadicand positiveContourPoint pieceMap outerRectangleMap
  simp only [Function.comp_apply]
  rw [rootContour_outerInitialTime, outerRootPath_apply]
  unfold chapterVIDOuterArcRadicand
  unfold ChapterVIDPrincipalConnectorModel.connectorParameterRoot
  rw [model.parameterRoot_eq_global
    (model.criticalValue
      (ChapterVIDConnectorFullBulk.positiveParameterToUnit point.1))
    (model.criticalValue_mem
      (ChapterVIDConnectorFullBulk.positiveParameterToUnit point.1))]

private def principalInitialRestriction
    (run : ChapterVIDOuterArcPolarCompiledGrid.CompiledRunVerdict)
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d) :
    ChapterVIContinuousSquareRootSheet
      (positiveContourRadicand model ∘ pieceMap outerInitialTime) where
  root point := (ChapterVIDOuterArcRegularity.principalSheet run .initial).root
    (outerRectangleMap model point)
  continuous_root :=
    (ChapterVIDOuterArcRegularity.principalSheet run .initial).continuous_root.comp
      (continuous_outerRectangleMap model)
  root_sq point := by
    rw [(ChapterVIDOuterArcRegularity.principalSheet run .initial).root_sq]
    exact (positiveContourRadicand_outerInitialTime model point).symm

/-- A principal-base-normalized joint sheet agrees with the compiled principal square root on
the entire initial outer quarter, simultaneously for every positive critical value. -/
theorem jointSheet_eq_principalInitial
    (run : ChapterVIDOuterArcPolarCompiledGrid.CompiledRunVerdict)
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (sheet : ChapterVIContinuousSquareRootSheet (positiveContourRadicand model))
    (hbase : sheet.root positiveContourBase =
      Complex.sqrt (positiveContourRadicand model positiveContourBase)) :
    ∀ point : PositiveContourDomain,
      sheet.root (pieceMap outerInitialTime point) =
        (ChapterVIDOuterArcRegularity.principalSheet run .initial).root
          (outerRectangleMap model point) := by
  let : ContractibleSpace ChapterVIDConnectorFullBulk.PositiveConnectorParameter :=
    (convex_Ico (0 : ℝ) 1).contractibleSpace ⟨0, by norm_num⟩
  let : ContractibleSpace I :=
    (convex_Icc (0 : ℝ) 1).contractibleSpace (by simp)
  let joint := restrictJointSheet sheet outerInitialTime continuous_outerInitialTime
  let principal := principalInitialRestriction run model
  have hrad : ∀ point : PositiveContourDomain,
      (positiveContourRadicand model ∘ pieceMap outerInitialTime) point ≠ 0 := by
    intro point
    rw [Function.comp_apply]
    rw [positiveContourRadicand_outerInitialTime model point]
    exact ChapterVIDOuterArcPolarCompiledGrid.radicand_ne_zero_of_run run .initial
      (outerRectangleMap model point)
  have hbase' : joint.root positiveContourBase =
      principal.root positiveContourBase := by
    change sheet.root (pieceMap outerInitialTime positiveContourBase) =
      Complex.sqrt (chapterVIDOuterArcRadicand .initial
        (outerRectangleMap model positiveContourBase))
    rw [← positiveContourRadicand_outerInitialTime model positiveContourBase]
    rw [show pieceMap outerInitialTime positiveContourBase = positiveContourBase by
      apply Prod.ext
      · rfl
      · apply Subtype.ext
        norm_num [positiveContourBase, pieceMap, outerInitialTime]]
    exact hbase
  have heq := joint.root_eq_of_eq_at principal hrad positiveContourBase hbase'
  intro point
  exact congrFun heq point

private def connectorRectangleMap : PositiveContourDomain → I × I :=
  fun point ↦
    (ChapterVIDConnectorFullBulk.positiveParameterToUnit point.1, point.2)

private theorem continuous_connectorRectangleMap :
    Continuous connectorRectangleMap :=
  (ChapterVIDConnectorFullBulk.continuous_positiveParameterToUnit.comp
    continuous_fst).prodMk continuous_snd

private theorem positiveContourRadicand_upperConnectorTime
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (point : PositiveContourDomain) :
    positiveContourRadicand model (pieceMap upperConnectorTime point) =
      model.rectangleRadicand .initial (connectorRectangleMap point) := by
  unfold positiveContourRadicand positiveContourPoint pieceMap connectorRectangleMap
  simp only [Function.comp_apply]
  rw [rootContour_upperConnectorTime,
    model.rootModel.connectorPath_apply]
  rfl

private def initialConnectorRestriction
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (sheet : ChapterVIContinuousSquareRootSheet
      (model.rectangleRadicand .initial)) :
    ChapterVIContinuousSquareRootSheet
      (positiveContourRadicand model ∘ pieceMap upperConnectorTime) where
  root point := sheet.root (connectorRectangleMap point)
  continuous_root := sheet.continuous_root.comp continuous_connectorRectangleMap
  root_sq point := by
    rw [sheet.root_sq]
    exact (positiveContourRadicand_upperConnectorTime model point).symm

/-- The single joint sheet agrees on the entire upper connector with every connector sheet that
has been normalized to the compiled principal outer branch. -/
theorem jointSheet_eq_initialConnector
    (run : ChapterVIDOuterArcPolarCompiledGrid.CompiledRunVerdict)
    {massProduct : ℂ} {b d : ℤ}
    (anchored : ChapterVIDAnchoredConnectorModel massProduct b d)
    (hL : anchored.rootModel.L ≤ 1 / (2 : ℝ) ^ 20)
    (uniform : ChapterVIDUniformAnchorData anchored (1 / (2 : ℝ) ^ 10))
    (sheet : ChapterVIContinuousSquareRootSheet
      (positiveContourRadicand anchored.toChapterVIDPrincipalConnectorModel))
    (hbase : sheet.root positiveContourBase =
      Complex.sqrt (positiveContourRadicand
        anchored.toChapterVIDPrincipalConnectorModel positiveContourBase))
    (connectorSheet : ChapterVIContinuousSquareRootSheet
      (anchored.toChapterVIDPrincipalConnectorModel.rectangleRadicand .initial))
    (houter : ∀ s : I,
      connectorSheet.root
          (anchored.toChapterVIDPrincipalConnectorModel.connectorBoundaryPoint .initial s) =
        anchored.toChapterVIDPrincipalConnectorModel.connectorOuterBoundaryRoot
          run .initial s) :
    ∀ point : PositiveContourDomain,
      sheet.root (pieceMap upperConnectorTime point) =
        connectorSheet.root (connectorRectangleMap point) := by
  let : ContractibleSpace ChapterVIDConnectorFullBulk.PositiveConnectorParameter :=
    (convex_Ico (0 : ℝ) 1).contractibleSpace ⟨0, by norm_num⟩
  let : ContractibleSpace I :=
    (convex_Icc (0 : ℝ) 1).contractibleSpace (by simp)
  let model := anchored.toChapterVIDPrincipalConnectorModel
  let joint := restrictJointSheet sheet upperConnectorTime continuous_upperConnectorTime
  let connector := initialConnectorRestriction model connectorSheet
  have hrad : ∀ point : PositiveContourDomain,
      (positiveContourRadicand model ∘ pieceMap upperConnectorTime) point ≠ 0 := by
    intro point
    rw [Function.comp_apply]
    exact positiveContourRadicand_ne_zero anchored hL uniform _
  have hseam := jointSheet_eq_principalInitial run model sheet hbase
    (positiveContourBase.1, (1 : I))
  have hbase' : joint.root positiveContourBase = connector.root positiveContourBase := by
    change sheet.root (positiveContourBase.1,
        upperConnectorTime positiveContourBase.2) =
      connectorSheet.root
        (ChapterVIDConnectorFullBulk.positiveParameterToUnit positiveContourBase.1,
          positiveContourBase.2)
    rw [show upperConnectorTime positiveContourBase.2 = outerInitialTime (1 : I) by
      apply Subtype.ext
      norm_num [positiveContourBase, upperConnectorTime, outerInitialTime]]
    change sheet.root (pieceMap outerInitialTime (positiveContourBase.1, (1 : I))) = _
    rw [hseam]
    simpa [positiveContourBase, pieceMap, outerRectangleMap,
      ChapterVIDConnectorFullBulk.positiveParameterToUnit, model,
      ChapterVIDPrincipalConnectorModel.connectorOuterBoundaryRoot,
      ChapterVIDPrincipalConnectorModel.connectorOuterBoundaryPoint,
      ChapterVIDPrincipalConnectorModel.connectorBoundaryPoint] using (houter 0).symm
  have heq := joint.root_eq_of_eq_at connector hrad positiveContourBase hbase'
  intro point
  exact congrFun heq point

private theorem positiveContourRadicand_middle_re_pos
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (point : PositiveContourDomain) :
    0 < (positiveContourRadicand model (pieceMap middleTime point)).re := by
  let s := ChapterVIDConnectorFullBulk.positiveParameterToUnit point.1
  let v : ℝ := 2 * model.rootModel.L * (point.2 : ℝ) - model.rootModel.L
  have hv : v ∈ Set.uIcc (-model.rootModel.L) model.rootModel.L := by
    rw [Set.uIcc_of_le (by linarith [model.rootModel.L_pos])]
    constructor <;> dsimp [v] <;>
      nlinarith [model.rootModel.L_pos, point.2.property.1, point.2.property.2]
  have hsne : s ≠ 1 := by
    intro heq
    have hvalue := congrArg Subtype.val heq
    exact point.1.property.2.ne hvalue
  have hkpos : 0 < model.criticalValue s := by
    unfold ChapterVIDPrincipalConnectorModel.criticalValue
    apply mul_pos model.κ_pos
    exact sub_pos.mpr (lt_of_le_of_ne s.property.2
      (fun h ↦ hsne (Subtype.ext h)))
  have hroot := model.rootModel.root_radicand_eq
    (model.criticalValue s) (model.criticalValue_mem_rootModel s) v hv
  have hmorse := model.rootModel.radicand_eq
    (model.criticalValue s) (model.criticalValue_mem_rootModel s) v hv
  have hmorse' : chapterVIDRadicand
      (chapterVIDCriticalMorseSourcePointAtD
        ((model.criticalValue s : ℂ), (v : ℂ))) =
      (model.criticalValue s : ℂ) + (v : ℂ) ^ 2 := by
    simpa only [chapterVIDRealCriticalMorseSourcePoint] using hmorse
  unfold positiveContourRadicand positiveContourPoint pieceMap
  simp only [Function.comp_apply]
  rw [rootContour_middleTime]
  unfold ChapterVIDPrincipalConnectorModel.connectorParameterRoot
  change (chapterVIDRootCoordinateRadicand
      (chapterVIDCriticalParameterRootAtD (model.criticalValue s : ℂ))
      (chapterVIDCriticalMorseRootPoint
        ((model.criticalValue s : ℂ), (v : ℂ)))).re > 0
  rw [hroot, hmorse']
  rw [show (model.criticalValue s : ℂ) + (v : ℂ) ^ 2 =
      ((model.criticalValue s + v ^ 2 : ℝ) : ℂ) by
    push_cast
    ring]
  simp only [Complex.ofReal_re]
  exact add_pos_of_pos_of_nonneg hkpos (sq_nonneg v)

private def principalMiddleRestriction
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d) :
    ChapterVIContinuousSquareRootSheet
      (positiveContourRadicand model ∘ pieceMap middleTime) where
  root point := Complex.sqrt
    (positiveContourRadicand model (pieceMap middleTime point))
  continuous_root := by
    rw [continuous_iff_continuousAt]
    intro point
    exact (Complex.continuousAt_sqrt
      (Or.inl (positiveContourRadicand_middle_re_pos model point).le)).comp_of_eq
        ((continuous_positiveContourRadicand model).comp
          (continuous_pieceMap continuous_middleTime)).continuousAt rfl
  root_sq point := by
    unfold Complex.sqrt
    exact Complex.cpow_nat_inv_pow _ (by norm_num : (2 : ℕ) ≠ 0)

/-- If the upper connector has the positive local seam sign, the same global sheet is the
principal positive Morse square root on the entire middle arc. -/
theorem jointSheet_eq_principalMiddle
    (run : ChapterVIDOuterArcPolarCompiledGrid.CompiledRunVerdict)
    {massProduct : ℂ} {b d : ℤ}
    (anchored : ChapterVIDAnchoredConnectorModel massProduct b d)
    (hL : anchored.rootModel.L ≤ 1 / (2 : ℝ) ^ 20)
    (uniform : ChapterVIDUniformAnchorData anchored (1 / (2 : ℝ) ^ 10))
    (sheet : ChapterVIContinuousSquareRootSheet
      (positiveContourRadicand anchored.toChapterVIDPrincipalConnectorModel))
    (hbase : sheet.root positiveContourBase =
      Complex.sqrt (positiveContourRadicand
        anchored.toChapterVIDPrincipalConnectorModel positiveContourBase))
    (connectorSheet : ChapterVIContinuousSquareRootSheet
      (anchored.toChapterVIDPrincipalConnectorModel.rectangleRadicand .initial))
    (houter : ∀ s : I,
      connectorSheet.root
          (anchored.toChapterVIDPrincipalConnectorModel.connectorBoundaryPoint .initial s) =
        anchored.toChapterVIDPrincipalConnectorModel.connectorOuterBoundaryRoot
          run .initial s)
    (hlocal : ∀ s : I,
      connectorSheet.root
          (anchored.toChapterVIDPrincipalConnectorModel.connectorLocalBoundaryPoint .initial s) =
        anchored.toChapterVIDPrincipalConnectorModel.connectorLocalBoundaryRoot s) :
    ∀ point : PositiveContourDomain,
      sheet.root (pieceMap middleTime point) =
        Complex.sqrt (positiveContourRadicand
          anchored.toChapterVIDPrincipalConnectorModel (pieceMap middleTime point)) := by
  let : ContractibleSpace ChapterVIDConnectorFullBulk.PositiveConnectorParameter :=
    (convex_Ico (0 : ℝ) 1).contractibleSpace ⟨0, by norm_num⟩
  let : ContractibleSpace I :=
    (convex_Icc (0 : ℝ) 1).contractibleSpace (by simp)
  let model := anchored.toChapterVIDPrincipalConnectorModel
  let joint := restrictJointSheet sheet middleTime continuous_middleTime
  let middle := principalMiddleRestriction model
  have hrad : ∀ point : PositiveContourDomain,
      (positiveContourRadicand model ∘ pieceMap middleTime) point ≠ 0 := by
    intro point
    rw [Function.comp_apply]
    exact positiveContourRadicand_ne_zero anchored hL uniform _
  have hconnector := jointSheet_eq_initialConnector run anchored hL uniform
    sheet hbase connectorSheet houter (positiveContourBase.1, (1 : I))
  have hbase' : joint.root positiveContourBase = middle.root positiveContourBase := by
    change sheet.root (positiveContourBase.1, middleTime positiveContourBase.2) =
      Complex.sqrt (positiveContourRadicand model
        (positiveContourBase.1, middleTime positiveContourBase.2))
    rw [show middleTime positiveContourBase.2 = upperConnectorTime (1 : I) by
      apply Subtype.ext
      norm_num [positiveContourBase, middleTime, upperConnectorTime]]
    change sheet.root (pieceMap upperConnectorTime
        (positiveContourBase.1, (1 : I))) = _
    rw [hconnector]
    have hlocalZero := hlocal 0
    change connectorSheet.root (model.connectorLocalBoundaryPoint .initial 0) = _
    rw [hlocalZero]
    unfold ChapterVIDPrincipalConnectorModel.connectorLocalBoundaryRoot
    congr 1
    rw [← model.rectangleRadicand_connectorLocalBoundaryPoint .initial 0]
    exact (positiveContourRadicand_upperConnectorTime model
      (positiveContourBase.1, (1 : I))).symm
  have heq := joint.root_eq_of_eq_at middle hrad positiveContourBase hbase'
  intro point
  exact congrFun heq point

private theorem positiveContourRadicand_lowerConnectorTime
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (point : PositiveContourDomain) :
    positiveContourRadicand model (pieceMap lowerConnectorTime point) =
      model.rectangleRadicand .final (connectorRectangleMap point) := by
  unfold positiveContourRadicand positiveContourPoint pieceMap connectorRectangleMap
  simp only [Function.comp_apply]
  rw [rootContour_lowerConnectorTime,
    model.rootModel.connectorPath_apply]
  rfl

private def finalConnectorRestriction
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (sheet : ChapterVIContinuousSquareRootSheet
      (model.rectangleRadicand .final)) :
    ChapterVIContinuousSquareRootSheet
      (positiveContourRadicand model ∘ pieceMap lowerConnectorTime) where
  root point := sheet.root (connectorRectangleMap point)
  continuous_root := sheet.continuous_root.comp continuous_connectorRectangleMap
  root_sq point := by
    rw [sheet.root_sq]
    exact (positiveContourRadicand_lowerConnectorTime model point).symm

/-- Positive local-seam normalization propagates the joint lift from the Morse middle onto the
entire lower connector. -/
theorem jointSheet_eq_finalConnector
    (run : ChapterVIDOuterArcPolarCompiledGrid.CompiledRunVerdict)
    {massProduct : ℂ} {b d : ℤ}
    (anchored : ChapterVIDAnchoredConnectorModel massProduct b d)
    (hL : anchored.rootModel.L ≤ 1 / (2 : ℝ) ^ 20)
    (uniform : ChapterVIDUniformAnchorData anchored (1 / (2 : ℝ) ^ 10))
    (sheet : ChapterVIContinuousSquareRootSheet
      (positiveContourRadicand anchored.toChapterVIDPrincipalConnectorModel))
    (hbase : sheet.root positiveContourBase =
      Complex.sqrt (positiveContourRadicand
        anchored.toChapterVIDPrincipalConnectorModel positiveContourBase))
    (initialSheet : ChapterVIContinuousSquareRootSheet
      (anchored.toChapterVIDPrincipalConnectorModel.rectangleRadicand .initial))
    (hinitialOuter : ∀ s : I,
      initialSheet.root
          (anchored.toChapterVIDPrincipalConnectorModel.connectorBoundaryPoint .initial s) =
        anchored.toChapterVIDPrincipalConnectorModel.connectorOuterBoundaryRoot
          run .initial s)
    (hinitialLocal : ∀ s : I,
      initialSheet.root
          (anchored.toChapterVIDPrincipalConnectorModel.connectorLocalBoundaryPoint .initial s) =
        anchored.toChapterVIDPrincipalConnectorModel.connectorLocalBoundaryRoot s)
    (finalSheet : ChapterVIContinuousSquareRootSheet
      (anchored.toChapterVIDPrincipalConnectorModel.rectangleRadicand .final))
    (hfinalLocal : ∀ s : I,
      finalSheet.root
          (anchored.toChapterVIDPrincipalConnectorModel.connectorLocalBoundaryPoint .final s) =
        anchored.toChapterVIDPrincipalConnectorModel.connectorLocalBoundaryRoot s) :
    ∀ point : PositiveContourDomain,
      sheet.root (pieceMap lowerConnectorTime point) =
        finalSheet.root (connectorRectangleMap point) := by
  let : ContractibleSpace ChapterVIDConnectorFullBulk.PositiveConnectorParameter :=
    (convex_Ico (0 : ℝ) 1).contractibleSpace ⟨0, by norm_num⟩
  let : ContractibleSpace I :=
    (convex_Icc (0 : ℝ) 1).contractibleSpace (by simp)
  let model := anchored.toChapterVIDPrincipalConnectorModel
  let joint := restrictJointSheet sheet lowerConnectorTime continuous_lowerConnectorTime
  let connector := finalConnectorRestriction model finalSheet
  have hrad : ∀ point : PositiveContourDomain,
      (positiveContourRadicand model ∘ pieceMap lowerConnectorTime) point ≠ 0 := by
    intro point
    rw [Function.comp_apply]
    exact positiveContourRadicand_ne_zero anchored hL uniform _
  have hmiddle := jointSheet_eq_principalMiddle run anchored hL uniform sheet hbase
    initialSheet hinitialOuter hinitialLocal (positiveContourBase.1, (1 : I))
  have hbase' : joint.root positiveContourBase = connector.root positiveContourBase := by
    change sheet.root (positiveContourBase.1,
        lowerConnectorTime positiveContourBase.2) =
      finalSheet.root
        (ChapterVIDConnectorFullBulk.positiveParameterToUnit positiveContourBase.1,
          positiveContourBase.2)
    rw [show lowerConnectorTime positiveContourBase.2 = middleTime (1 : I) by
      apply Subtype.ext
      norm_num [positiveContourBase, lowerConnectorTime, middleTime]]
    change sheet.root (pieceMap middleTime
        (positiveContourBase.1, (1 : I))) = _
    rw [hmiddle]
    have hlocalZero := hfinalLocal 0
    change _ = finalSheet.root (model.connectorLocalBoundaryPoint .final 0)
    rw [hlocalZero]
    unfold ChapterVIDPrincipalConnectorModel.connectorLocalBoundaryRoot
    congr 1
    rw [← model.rectangleRadicand_connectorLocalBoundaryPoint .final 0]
    rw [show pieceMap middleTime (positiveContourBase.1, (1 : I)) =
        pieceMap lowerConnectorTime (positiveContourBase.1, (0 : I)) by
      apply Prod.ext
      · rfl
      · apply Subtype.ext
        norm_num [positiveContourBase, pieceMap, middleTime, lowerConnectorTime]]
    rw [positiveContourRadicand_lowerConnectorTime model
      (positiveContourBase.1, (0 : I))]
    congr 2
  have heq := joint.root_eq_of_eq_at connector hrad positiveContourBase hbase'
  intro point
  exact congrFun heq point

private theorem positiveContourRadicand_outerFinalTime
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (point : PositiveContourDomain) :
    positiveContourRadicand model (pieceMap outerFinalTime point) =
      chapterVIDOuterArcRadicand .final (outerRectangleMap model point) := by
  unfold positiveContourRadicand positiveContourPoint pieceMap outerRectangleMap
  simp only [Function.comp_apply]
  rw [rootContour_outerFinalTime, outerRootPath_apply]
  unfold chapterVIDOuterArcRadicand
  unfold ChapterVIDPrincipalConnectorModel.connectorParameterRoot
  rw [model.parameterRoot_eq_global
    (model.criticalValue
      (ChapterVIDConnectorFullBulk.positiveParameterToUnit point.1))
    (model.criticalValue_mem
      (ChapterVIDConnectorFullBulk.positiveParameterToUnit point.1))]

private def principalFinalRestriction
    (run : ChapterVIDOuterArcPolarCompiledGrid.CompiledRunVerdict)
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d) :
    ChapterVIContinuousSquareRootSheet
      (positiveContourRadicand model ∘ pieceMap outerFinalTime) where
  root point := (ChapterVIDOuterArcRegularity.principalSheet run .final).root
    (outerRectangleMap model point)
  continuous_root :=
    (ChapterVIDOuterArcRegularity.principalSheet run .final).continuous_root.comp
      (continuous_outerRectangleMap model)
  root_sq point := by
    rw [(ChapterVIDOuterArcRegularity.principalSheet run .final).root_sq]
    exact (positiveContourRadicand_outerFinalTime model point).symm

/-- The propagated joint sheet returns to the compiled principal branch on the complete final
outer quarter.  Together with the preceding four restriction theorems, this identifies all five
certified branches with one continuously lifted closed contour. -/
theorem jointSheet_eq_principalFinal
    (run : ChapterVIDOuterArcPolarCompiledGrid.CompiledRunVerdict)
    {massProduct : ℂ} {b d : ℤ}
    (anchored : ChapterVIDAnchoredConnectorModel massProduct b d)
    (hL : anchored.rootModel.L ≤ 1 / (2 : ℝ) ^ 20)
    (uniform : ChapterVIDUniformAnchorData anchored (1 / (2 : ℝ) ^ 10))
    (sheet : ChapterVIContinuousSquareRootSheet
      (positiveContourRadicand anchored.toChapterVIDPrincipalConnectorModel))
    (hbase : sheet.root positiveContourBase =
      Complex.sqrt (positiveContourRadicand
        anchored.toChapterVIDPrincipalConnectorModel positiveContourBase))
    (initialSheet : ChapterVIContinuousSquareRootSheet
      (anchored.toChapterVIDPrincipalConnectorModel.rectangleRadicand .initial))
    (hinitialOuter : ∀ s : I,
      initialSheet.root
          (anchored.toChapterVIDPrincipalConnectorModel.connectorBoundaryPoint .initial s) =
        anchored.toChapterVIDPrincipalConnectorModel.connectorOuterBoundaryRoot
          run .initial s)
    (hinitialLocal : ∀ s : I,
      initialSheet.root
          (anchored.toChapterVIDPrincipalConnectorModel.connectorLocalBoundaryPoint .initial s) =
        anchored.toChapterVIDPrincipalConnectorModel.connectorLocalBoundaryRoot s)
    (finalSheet : ChapterVIContinuousSquareRootSheet
      (anchored.toChapterVIDPrincipalConnectorModel.rectangleRadicand .final))
    (hfinalLocal : ∀ s : I,
      finalSheet.root
          (anchored.toChapterVIDPrincipalConnectorModel.connectorLocalBoundaryPoint .final s) =
        anchored.toChapterVIDPrincipalConnectorModel.connectorLocalBoundaryRoot s)
    (hfinalOuter : ∀ s : I,
      finalSheet.root
          (anchored.toChapterVIDPrincipalConnectorModel.connectorBoundaryPoint .final s) =
        anchored.toChapterVIDPrincipalConnectorModel.connectorOuterBoundaryRoot
          run .final s) :
    ∀ point : PositiveContourDomain,
      sheet.root (pieceMap outerFinalTime point) =
        (ChapterVIDOuterArcRegularity.principalSheet run .final).root
          (outerRectangleMap anchored.toChapterVIDPrincipalConnectorModel point) := by
  let : ContractibleSpace ChapterVIDConnectorFullBulk.PositiveConnectorParameter :=
    (convex_Ico (0 : ℝ) 1).contractibleSpace ⟨0, by norm_num⟩
  let : ContractibleSpace I :=
    (convex_Icc (0 : ℝ) 1).contractibleSpace (by simp)
  let model := anchored.toChapterVIDPrincipalConnectorModel
  let joint := restrictJointSheet sheet outerFinalTime continuous_outerFinalTime
  let principal := principalFinalRestriction run model
  have hrad : ∀ point : PositiveContourDomain,
      (positiveContourRadicand model ∘ pieceMap outerFinalTime) point ≠ 0 := by
    intro point
    rw [Function.comp_apply, positiveContourRadicand_outerFinalTime model point]
    exact ChapterVIDOuterArcPolarCompiledGrid.radicand_ne_zero_of_run run .final
      (outerRectangleMap model point)
  have hconnector := jointSheet_eq_finalConnector run anchored hL uniform sheet hbase
    initialSheet hinitialOuter hinitialLocal finalSheet hfinalLocal
      (positiveContourBase.1, (1 : I))
  have hbase' : joint.root positiveContourBase = principal.root positiveContourBase := by
    change sheet.root (positiveContourBase.1,
        outerFinalTime positiveContourBase.2) =
      (ChapterVIDOuterArcRegularity.principalSheet run .final).root
        (outerRectangleMap model positiveContourBase)
    rw [show outerFinalTime positiveContourBase.2 = lowerConnectorTime (1 : I) by
      apply Subtype.ext
      norm_num [positiveContourBase, outerFinalTime, lowerConnectorTime]]
    change sheet.root (pieceMap lowerConnectorTime
        (positiveContourBase.1, (1 : I))) = _
    rw [hconnector]
    simpa [positiveContourBase, connectorRectangleMap, outerRectangleMap,
      ChapterVIDConnectorFullBulk.positiveParameterToUnit, model,
      ChapterVIDPrincipalConnectorModel.connectorBoundaryPoint,
      ChapterVIDPrincipalConnectorModel.connectorOuterBoundaryPoint,
      ChapterVIDPrincipalConnectorModel.connectorOuterBoundaryRoot] using hfinalOuter 0
  have heq := joint.root_eq_of_eq_at principal hrad positiveContourBase hbase'
  intro point
  exact congrFun heq point

/-- Source-facing bundle of all five restriction equalities.  No branch sign remains once both
connector sheets satisfy the positive local seam convention. -/
theorem jointSheet_eq_allCertifiedPieces
    (run : ChapterVIDOuterArcPolarCompiledGrid.CompiledRunVerdict)
    {massProduct : ℂ} {b d : ℤ}
    (anchored : ChapterVIDAnchoredConnectorModel massProduct b d)
    (hL : anchored.rootModel.L ≤ 1 / (2 : ℝ) ^ 20)
    (uniform : ChapterVIDUniformAnchorData anchored (1 / (2 : ℝ) ^ 10))
    (sheet : ChapterVIContinuousSquareRootSheet
      (positiveContourRadicand anchored.toChapterVIDPrincipalConnectorModel))
    (hbase : sheet.root positiveContourBase =
      Complex.sqrt (positiveContourRadicand
        anchored.toChapterVIDPrincipalConnectorModel positiveContourBase))
    (compatible : ChapterVIDPrincipalConnectorModel.SeamCompatibleCertifiedConnectorPair
      run anchored.toChapterVIDPrincipalConnectorModel) :
    (∀ point : PositiveContourDomain,
      sheet.root (pieceMap outerInitialTime point) =
        (ChapterVIDOuterArcRegularity.principalSheet run .initial).root
          (outerRectangleMap anchored.toChapterVIDPrincipalConnectorModel point)) ∧
    (∀ point : PositiveContourDomain,
      sheet.root (pieceMap upperConnectorTime point) =
        compatible.pair.initialSheet.root (connectorRectangleMap point)) ∧
    (∀ point : PositiveContourDomain,
      sheet.root (pieceMap middleTime point) =
        Complex.sqrt (positiveContourRadicand
          anchored.toChapterVIDPrincipalConnectorModel (pieceMap middleTime point))) ∧
    (∀ point : PositiveContourDomain,
      sheet.root (pieceMap lowerConnectorTime point) =
        compatible.pair.finalSheet.root (connectorRectangleMap point)) ∧
    (∀ point : PositiveContourDomain,
      sheet.root (pieceMap outerFinalTime point) =
        (ChapterVIDOuterArcRegularity.principalSheet run .final).root
          (outerRectangleMap anchored.toChapterVIDPrincipalConnectorModel point)) := by
  refine ⟨jointSheet_eq_principalInitial run _ sheet hbase,
    jointSheet_eq_initialConnector run anchored hL uniform sheet hbase
      compatible.pair.initialSheet compatible.pair.initial_outer,
    jointSheet_eq_principalMiddle run anchored hL uniform sheet hbase
      compatible.pair.initialSheet compatible.pair.initial_outer compatible.initial_local,
    jointSheet_eq_finalConnector run anchored hL uniform sheet hbase
      compatible.pair.initialSheet compatible.pair.initial_outer compatible.initial_local
      compatible.pair.finalSheet compatible.final_local,
    jointSheet_eq_principalFinal run anchored hL uniform sheet hbase
      compatible.pair.initialSheet compatible.pair.initial_outer compatible.initial_local
      compatible.pair.finalSheet compatible.final_local compatible.pair.final_outer⟩

/-- End-to-end terminal lifted-contour theorem: the full-bulk certificate constructs a single
principal-based joint sheet, and a seam-compatible certified pair identifies its restrictions
with all five branches used in the logarithmic contribution. -/
theorem exists_jointSheet_eq_allCertifiedPieces
    (run : ChapterVIDOuterArcPolarCompiledGrid.CompiledRunVerdict)
    {massProduct : ℂ} {b d : ℤ}
    (anchored : ChapterVIDAnchoredConnectorModel massProduct b d)
    (hL : anchored.rootModel.L ≤ 1 / (2 : ℝ) ^ 20)
    (uniform : ChapterVIDUniformAnchorData anchored (1 / (2 : ℝ) ^ 10))
    (compatible : ChapterVIDPrincipalConnectorModel.SeamCompatibleCertifiedConnectorPair
      run anchored.toChapterVIDPrincipalConnectorModel) :
    ∃ sheet : ChapterVIContinuousSquareRootSheet
        (positiveContourRadicand anchored.toChapterVIDPrincipalConnectorModel),
      sheet.root positiveContourBase =
          Complex.sqrt (positiveContourRadicand
            anchored.toChapterVIDPrincipalConnectorModel positiveContourBase) ∧
        (∀ point : PositiveContourDomain,
          sheet.root (pieceMap outerInitialTime point) =
            (ChapterVIDOuterArcRegularity.principalSheet run .initial).root
              (outerRectangleMap anchored.toChapterVIDPrincipalConnectorModel point)) ∧
        (∀ point : PositiveContourDomain,
          sheet.root (pieceMap upperConnectorTime point) =
            compatible.pair.initialSheet.root (connectorRectangleMap point)) ∧
        (∀ point : PositiveContourDomain,
          sheet.root (pieceMap middleTime point) =
            Complex.sqrt (positiveContourRadicand
              anchored.toChapterVIDPrincipalConnectorModel (pieceMap middleTime point))) ∧
        (∀ point : PositiveContourDomain,
          sheet.root (pieceMap lowerConnectorTime point) =
            compatible.pair.finalSheet.root (connectorRectangleMap point)) ∧
        (∀ point : PositiveContourDomain,
          sheet.root (pieceMap outerFinalTime point) =
            (ChapterVIDOuterArcRegularity.principalSheet run .final).root
              (outerRectangleMap anchored.toChapterVIDPrincipalConnectorModel point)) := by
  obtain ⟨sheet, hbase⟩ :=
    exists_principalBasedPositiveContourSquareRootSheet anchored hL uniform
  exact ⟨sheet, hbase,
    jointSheet_eq_allCertifiedPieces run anchored hL uniform sheet hbase compatible⟩

end ChapterVIDJointLiftedContour
end PoincareChapterVI
