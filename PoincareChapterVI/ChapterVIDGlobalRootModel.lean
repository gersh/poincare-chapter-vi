/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.ChapterVIDMovingRootBridge
import PoincareChapterVI.ChapterVILocalVanishingCycle

/-!
# A compact local middle path in the global root coordinate

The analytic germ from `ChapterVIDMovingRootBridge` is shrunk to the same real rectangle used by
the local logarithmic calculation. On that rectangle the moving root coordinate is analytic,
nonzero, maps exactly to the literal source-coordinate middle path, and uses the correct cubic
root of the moving source parameter.

This produces the concrete middle path in `u = x^(1/3)` required to state the two connector
rectangles without any endpoint assumptions.
-/

noncomputable section

open Filter Set Topology
open scoped unitInterval

namespace PoincareChapterVI

/-- The local source model, strengthened so its complete compact rectangle lives on Poincare's
global root-coordinate sheet. -/
structure ChapterVIDPrincipalGlobalRootModel
    (massProduct : ℂ) (b d : ℤ)
    extends ChapterVIDPrincipalLocalSourceModel massProduct b d where
  root_analyticAt : ∀ k ∈ Set.Icc 0 δ, ∀ v ∈ Set.uIcc (-L) L,
    AnalyticAt ℂ chapterVIDCriticalMorseRootPoint ((k : ℂ), (v : ℂ))
  parameterInverse_analyticAt : ∀ k ∈ Set.Icc 0 δ,
    AnalyticAt ℂ chapterVIDCriticalParameterInverseAtD (k : ℂ)
  parameterRoot_analyticAt : ∀ k ∈ Set.Icc 0 δ,
    AnalyticAt ℂ chapterVIDCriticalParameterRootAtD (k : ℂ)
  root_source_eq : ∀ k ∈ Set.Icc 0 δ, ∀ v ∈ Set.uIcc (-L) L,
    chapterVIDRootToOriginalContour
        (chapterVIDCriticalMorseRootPoint ((k : ℂ), (v : ℂ))) =
      chapterVIDPrincipalLocalSourceFiber (k : ℂ) (v : ℂ)
  root_ne_zero : ∀ k ∈ Set.Icc 0 δ, ∀ v ∈ Set.uIcc (-L) L,
    chapterVIDCriticalMorseRootPoint ((k : ℂ), (v : ℂ)) ≠ 0
  parameterRoot_pow : ∀ k ∈ Set.Icc 0 δ,
    chapterVIDCriticalParameterRootAtD (k : ℂ) ^ 3 =
      chapterVIDCriticalParameterInverseAtD (k : ℂ)

/-- All analytic-germ identities can be imposed on one smaller compact positive rectangle. -/
theorem exists_chapterVIDPrincipalGlobalRootModel
    (massProduct : ℂ) (b d : ℤ) :
    Nonempty (ChapterVIDPrincipalGlobalRootModel massProduct b d) := by
  obtain ⟨model⟩ := exists_chapterVIDPrincipalLocalSourceModel massProduct b d
  have hanalytic :
      {point : ℂ × ℂ | AnalyticAt ℂ chapterVIDCriticalMorseRootPoint point} ∈
        𝓝 ((0 : ℂ), (0 : ℂ)) :=
    analyticAt_chapterVIDCriticalMorseRootPoint.eventually_analyticAt
  have hsource :
      {point : ℂ × ℂ |
        chapterVIDRootToOriginalContour
            (chapterVIDCriticalMorseRootPoint point) =
          (chapterVIDCriticalMorseSourcePointAtD point).2} ∈
        𝓝 ((0 : ℂ), (0 : ℂ)) :=
    eventually_chapterVIDRootToOriginalContour_criticalMorseRootPoint
  have hparameterInverseAnalytic :
      {k : ℂ | AnalyticAt ℂ chapterVIDCriticalParameterInverseAtD k} ∈ 𝓝 0 :=
    analyticAt_chapterVIDCriticalParameterInverseAtD.eventually_analyticAt
  have hparameterRootAnalytic :
      {k : ℂ | AnalyticAt ℂ chapterVIDCriticalParameterRootAtD k} ∈ 𝓝 0 :=
    analyticAt_chapterVIDCriticalParameterRootAtD.eventually_analyticAt
  have hne :
      {point : ℂ × ℂ | chapterVIDCriticalMorseRootPoint point ≠ 0} ∈
        𝓝 ((0 : ℂ), (0 : ℂ)) :=
    eventually_chapterVIDCriticalMorseRootPoint_ne_zero
  have hfst : Tendsto (fun point : ℂ × ℂ ↦ point.1)
      (𝓝 ((0 : ℂ), (0 : ℂ))) (𝓝 0) := continuousAt_fst
  have hparameter :
      {point : ℂ × ℂ |
        chapterVIDCriticalParameterRootAtD point.1 ^ 3 =
          chapterVIDCriticalParameterInverseAtD point.1} ∈
        𝓝 ((0 : ℂ), (0 : ℂ)) :=
    hfst.eventually eventually_chapterVIDCriticalParameterRootAtD_pow
  have hparameterInverseAnalytic' :
      {point : ℂ × ℂ |
        AnalyticAt ℂ chapterVIDCriticalParameterInverseAtD point.1} ∈
        𝓝 ((0 : ℂ), (0 : ℂ)) :=
    hfst.eventually hparameterInverseAnalytic
  have hparameterRootAnalytic' :
      {point : ℂ × ℂ |
        AnalyticAt ℂ chapterVIDCriticalParameterRootAtD point.1} ∈
        𝓝 ((0 : ℂ), (0 : ℂ)) :=
    hfst.eventually hparameterRootAnalytic
  have hall :
      {point : ℂ × ℂ |
        AnalyticAt ℂ chapterVIDCriticalMorseRootPoint point ∧
        AnalyticAt ℂ chapterVIDCriticalParameterInverseAtD point.1 ∧
        AnalyticAt ℂ chapterVIDCriticalParameterRootAtD point.1 ∧
        chapterVIDRootToOriginalContour
            (chapterVIDCriticalMorseRootPoint point) =
          (chapterVIDCriticalMorseSourcePointAtD point).2 ∧
        chapterVIDCriticalMorseRootPoint point ≠ 0 ∧
        chapterVIDCriticalParameterRootAtD point.1 ^ 3 =
          chapterVIDCriticalParameterInverseAtD point.1} ∈
        𝓝 ((0 : ℂ), (0 : ℂ)) := by
    filter_upwards [hanalytic, hparameterInverseAnalytic',
      hparameterRootAnalytic', hsource, hne, hparameter]
      with point ha hzi hzeta hs hn hp
    exact ⟨ha, hzi, hzeta, hs, hn, hp⟩
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hall
  let r : ℝ := min (min model.δ model.L) (ε / 2)
  have hr : 0 < r := by
    dsimp [r]
    exact lt_min (lt_min model.δ_pos model.L_pos) (by positivity)
  have hrδ : r ≤ model.δ := by
    exact (min_le_left (min model.δ model.L) (ε / 2)).trans
      (min_le_left model.δ model.L)
  have hrL : r ≤ model.L := by
    exact (min_le_left (min model.δ model.L) (ε / 2)).trans
      (min_le_right model.δ model.L)
  have hrε : r ≤ ε / 2 := min_le_right _ _
  have hrealPoint : ∀ k : ℝ, k ∈ Set.Icc 0 r →
      ∀ v : ℝ, v ∈ Set.uIcc (-r) r →
      (((k : ℂ), (v : ℂ)) : ℂ × ℂ) ∈ Metric.ball (0, 0) ε := by
    intro k hk v hv
    rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
    simp only [Complex.dist_eq, sub_zero, Complex.norm_real, Real.norm_eq_abs]
    rw [Set.uIcc_of_le (by linarith [hr])] at hv
    constructor
    · rw [abs_of_nonneg hk.1]
      linarith [hk.2, hrε]
    · rw [abs_lt]
      constructor <;> linarith [hv.1, hv.2, hrε]
  have hlocalSubset :
      Set.Icc (0 : ℝ) r ×ˢ Set.uIcc (-r) r ⊆
        Set.Icc 0 model.δ ×ˢ Set.uIcc (-model.L) model.L := by
    rintro ⟨k, v⟩ ⟨hk, hv⟩
    have hvSmall : v ∈ Set.Icc (-r) r := by
      rw [Set.uIcc_of_le (by linarith [hr])] at hv
      exact hv
    have hvLarge : v ∈ Set.uIcc (-model.L) model.L := by
      rw [Set.uIcc_of_le (by linarith [model.L_pos])]
      exact ⟨by linarith [hrL, hvSmall.1],
        by linarith [hrL, hvSmall.2]⟩
    exact ⟨⟨hk.1, hk.2.trans hrδ⟩, hvLarge⟩
  let localModel : ChapterVIDPrincipalLocalSourceModel massProduct b d := {
    δ := r
    L := r
    δ_pos := hr
    L_pos := hr
    amplitude_contDiffOn := model.amplitude_contDiffOn.mono hlocalSubset
    radicand_eq := by
      intro k hk v hv
      have hsub : (k, v) ∈
          Set.Icc 0 model.δ ×ˢ Set.uIcc (-model.L) model.L :=
        hlocalSubset ⟨hk, hv⟩
      exact model.radicand_eq k hsub.1 v hsub.2
    sourceFiber_hasDerivAt := by
      intro k hk v hv
      have hsub : (k, v) ∈
          Set.Icc 0 model.δ ×ˢ Set.uIcc (-model.L) model.L :=
        hlocalSubset ⟨hk, hv⟩
      exact model.sourceFiber_hasDerivAt k hsub.1 v hsub.2 }
  refine ⟨{
    toChapterVIDPrincipalLocalSourceModel := localModel
    root_analyticAt := ?_
    parameterInverse_analyticAt := ?_
    parameterRoot_analyticAt := ?_
    root_source_eq := ?_
    root_ne_zero := ?_
    parameterRoot_pow := ?_ }⟩
  · intro k hk v hv
    exact (hball (hrealPoint k hk v hv)).1
  · intro k hk
    have hv : (0 : ℝ) ∈ Set.uIcc (-r) r :=
      Set.mem_uIcc_of_le (by linarith) (by linarith)
    exact (hball (hrealPoint k hk 0 hv)).2.1
  · intro k hk
    have hv : (0 : ℝ) ∈ Set.uIcc (-r) r :=
      Set.mem_uIcc_of_le (by linarith) (by linarith)
    exact (hball (hrealPoint k hk 0 hv)).2.2.1
  · intro k hk v hv
    have hs := (hball (hrealPoint k hk v hv)).2.2.2.1
    simpa only [chapterVIDPrincipalLocalSourceFiber_eq] using hs
  · intro k hk v hv
    exact (hball (hrealPoint k hk v hv)).2.2.2.2.1
  · intro k hk
    have hv : (0 : ℝ) ∈ Set.uIcc (-r) r := by
      rw [Set.uIcc_of_le (by linarith [hr])]
      constructor <;> linarith
    exact (hball (hrealPoint k hk 0 hv)).2.2.2.2.2

/-- The affine real Morse coordinate along the compact middle segment. -/
def ChapterVIDPrincipalGlobalRootModel.morseLine
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalGlobalRootModel massProduct b d)
    (t : ℝ) : ℂ :=
  chapterVIDPrincipalLocalMorseLine model.L t

/-- Poincare's local middle path, now represented in the global root coordinate used by the
compiled outer and connector radicands. -/
def ChapterVIDPrincipalGlobalRootModel.rootPath
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalGlobalRootModel massProduct b d)
    (k : ℝ) (hk : k ∈ Set.Icc 0 model.δ) :
    Path
      (chapterVIDCriticalMorseRootPoint ((k : ℂ), ((-model.L : ℝ) : ℂ)))
      (chapterVIDCriticalMorseRootPoint ((k : ℂ), (model.L : ℂ))) where
  toFun τ := chapterVIDCriticalMorseRootPoint
    ((k : ℂ), model.morseLine τ)
  continuous_toFun := by
    rw [continuous_iff_continuousAt]
    intro τ
    let v : ℝ := 2 * model.L * (τ : ℝ) - model.L
    have hv : v ∈ Set.uIcc (-model.L) model.L := by
      rw [Set.uIcc_of_le (by linarith [model.L_pos])]
      constructor <;> dsimp [v] <;>
        nlinarith [model.L_pos, τ.property.1, τ.property.2]
    have hroot := model.root_analyticAt k hk v hv
    have hline : ContinuousAt
        (fun s : unitInterval ↦
          ((k : ℂ), model.morseLine (s : ℝ))) τ := by
      unfold ChapterVIDPrincipalGlobalRootModel.morseLine
        chapterVIDPrincipalLocalMorseLine
      fun_prop
    exact hroot.continuousAt.comp_of_eq hline rfl
  source' := by
    change chapterVIDCriticalMorseRootPoint
      ((k : ℂ), (((2 * model.L * 0 - model.L : ℝ) : ℂ))) = _
    congr 2
    push_cast
    ring
  target' := by
    change chapterVIDCriticalMorseRootPoint
      ((k : ℂ), (((2 * model.L * 1 - model.L : ℝ) : ℂ))) = _
    congr 2
    push_cast
    ring

@[simp]
theorem ChapterVIDPrincipalGlobalRootModel.rootPath_apply
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalGlobalRootModel massProduct b d)
    (k : ℝ) (hk : k ∈ Set.Icc 0 model.δ) (τ : I) :
    model.rootPath k hk τ = chapterVIDCriticalMorseRootPoint
      ((k : ℂ), model.morseLine τ) :=
  rfl

/-- Mapping the root-coordinate middle path through Poincare's exact `u -> t` change gives the
previously constructed literal local source path pointwise. -/
theorem ChapterVIDPrincipalGlobalRootModel.rootToSource_rootPath
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalGlobalRootModel massProduct b d)
    (k : ℝ) (hk : k ∈ Set.Icc 0 model.δ) (τ : I) :
    chapterVIDRootToOriginalContour (model.rootPath k hk τ) =
      model.toChapterVIDPrincipalLocalSourceModel.sourcePath k hk τ := by
  let v : ℝ := 2 * model.L * (τ : ℝ) - model.L
  have hv : v ∈ Set.uIcc (-model.L) model.L := by
    rw [Set.uIcc_of_le (by linarith [model.L_pos])]
    constructor <;> dsimp [v] <;>
      nlinarith [model.L_pos, τ.property.1, τ.property.2]
  have hsource := model.root_source_eq k hk v hv
  change chapterVIDRootToOriginalContour
      (chapterVIDCriticalMorseRootPoint
        ((k : ℂ), (((2 * model.L * (τ : ℝ) - model.L : ℝ) : ℂ)))) =
    chapterVIDPrincipalLocalSourceFiber (k : ℂ)
      (((2 * model.L * (τ : ℝ) - model.L : ℝ) : ℂ))
  exact hsource

end PoincareChapterVI
