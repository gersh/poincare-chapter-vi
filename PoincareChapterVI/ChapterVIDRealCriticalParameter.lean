/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.ChapterVIDTransversality
import PoincareChapterVI.ChapterVIRealLocalBranches
import Mathlib.Analysis.Calculus.Deriv.Star

/-!
# The real critical-parameter branch at D

This file separates the exact analytic part of the radial-placement argument from its finite
orientation calculation.  All constants and inverse-coordinate branches selected at D are shown
to respect complex conjugation.  A subsequent LeanCompCert certificate only has to determine
which direction the resulting real branch moves.
-/

noncomputable section

open Complex Filter Set Topology
open scoped ComplexConjugate ContDiff

namespace PoincareChapterVI

@[simp] theorem conj_chapterVIDEccentricity :
    conj chapterVIDEccentricity = chapterVIDEccentricity := by
  simp only [chapterVIDEccentricity, map_div₀, map_ofNat]

@[simp] theorem conj_chapterVIDComplement :
    conj chapterVIDComplement = chapterVIDComplement := by
  simp only [chapterVIDComplement, map_div₀, map_ofNat]

@[simp] theorem conj_chapterVIDX : conj chapterVIDX = chapterVIDX := by
  simp [chapterVIDX]

@[simp] theorem conj_chapterVIDY : conj chapterVIDY = chapterVIDY := by
  simp only [chapterVIDY, map_div₀, map_mul, map_add, map_sub, map_pow,
    map_one, map_ofNat, conj_chapterVIDX]

@[simp] theorem conj_chapterVIDCollisionLift :
    conj chapterVIDCollisionLift = chapterVIDCollisionLift := by
  unfold chapterVIDCollisionLift
  rw [chapterVINegativeRealCubicLift_eq_value]
  simp

@[simp] theorem conj_chapterVIDTBase : conj chapterVIDTBase = chapterVIDTBase := by
  unfold chapterVIDTBase chapterVIDCollisionLift
  rw [chapterVINegativeRealCubicLift_eq_value,
    chapterVIDRootToOriginalContour_ofReal]
  simp

@[simp] theorem conj_chapterVIDFirstMeanBase :
    conj (chapterVIKeplerExponential chapterVIDEccentricity chapterVIDX) =
      chapterVIKeplerExponential chapterVIDEccentricity chapterVIDX := by
  rw [← chapterVIKeplerExponential_conj conj_chapterVIDEccentricity chapterVIDX]
  simp

@[simp] theorem conj_chapterVIDSecondMeanBase :
    conj (chapterVIKeplerExponential 0 chapterVIDY) =
      chapterVIKeplerExponential 0 chapterVIDY := by
  rw [← chapterVIKeplerExponential_conj (by simp) chapterVIDY]
  simp

@[simp] theorem conj_chapterVIDZBase : conj chapterVIDZBase = chapterVIDZBase := by
  unfold chapterVIDZBase chapterVIContourBase chapterVIMeanToContourMap
  simp only [map_mul, map_zpow₀, conj_chapterVIDFirstMeanBase,
    conj_chapterVIDSecondMeanBase]

/-- Componentwise conjugation on Poincaré's literal source coordinates. -/
def chapterVIConjPoint (point : ℂ × ℂ) : ℂ × ℂ :=
  (conj point.1, conj point.2)

@[simp] theorem chapterVIConjPoint_base :
    chapterVIConjPoint (chapterVIDZBase, chapterVIDTBase) =
      (chapterVIDZBase, chapterVIDTBase) := by
  simp [chapterVIConjPoint]

/-- The complete locally selected anomaly pair commutes with conjugation near D. -/
theorem eventually_chapterVIDPoincareAnomalyPair_conj :
    ∀ᶠ point in nhds (chapterVIDZBase, chapterVIDTBase),
      chapterVIPoincareAnomalyPair (-1) 3 chapterVIDEccentricity 0
          (chapterVIDX, chapterVIDY) chapterVIDX_ne_zero chapterVIDY_ne_zero
          chapterVID_firstKeplerCritical chapterVID_secondKeplerCritical (by norm_num)
          (chapterVIConjPoint point) =
        (conj
            (chapterVIPoincareAnomalyPair (-1) 3 chapterVIDEccentricity 0
              (chapterVIDX, chapterVIDY) chapterVIDX_ne_zero chapterVIDY_ne_zero
              chapterVID_firstKeplerCritical chapterVID_secondKeplerCritical (by norm_num)
              point).1,
          conj
            (chapterVIPoincareAnomalyPair (-1) 3 chapterVIDEccentricity 0
              (chapterVIDX, chapterVIDY) chapterVIDX_ne_zero chapterVIDY_ne_zero
              chapterVID_firstKeplerCritical chapterVID_secondKeplerCritical (by norm_num)
              point).2) := by
  let firstMean : ℂ × ℂ → ℂ := fun point ↦ point.2 ^ (3 : ℤ)
  let secondMeanBase := chapterVIKeplerExponential 0 chapterVIDY
  let ratio : ℂ × ℂ → ℂ :=
    fun point ↦ point.1 / firstMean point ^ (-1 : ℤ)
  let secondMean : ℂ × ℂ → ℂ := fun point ↦
    chapterVIPowerLocalInverse 3 secondMeanBase
      (chapterVIKeplerExponential_ne_zero 0 chapterVIDY_ne_zero) (by norm_num)
      (ratio point)
  have hfirstMeanBase : firstMean (chapterVIDZBase, chapterVIDTBase) =
      chapterVIKeplerExponential chapterVIDEccentricity chapterVIDX := by
    simpa only [firstMean] using chapterVIDTBase_pow
  have hratioBase : ratio (chapterVIDZBase, chapterVIDTBase) =
      secondMeanBase ^ (3 : ℤ) := by
    simpa only [ratio, firstMean, secondMeanBase] using chapterVIDParameterInput_base
  have hsecondMeanBase : secondMean (chapterVIDZBase, chapterVIDTBase) =
      secondMeanBase := by
    unfold secondMean
    rw [hratioBase]
    exact chapterVIPowerLocalInverse_apply_base 3 secondMeanBase
      (chapterVIKeplerExponential_ne_zero 0 chapterVIDY_ne_zero) (by norm_num)
  have hfirstMeanTendsto : Tendsto firstMean
      (nhds (chapterVIDZBase, chapterVIDTBase))
      (nhds (chapterVIKeplerExponential chapterVIDEccentricity chapterVIDX)) := by
    have hcontinuous : ContinuousAt firstMean (chapterVIDZBase, chapterVIDTBase) := by
      unfold firstMean
      exact continuousAt_snd.zpow₀ 3 (Or.inl chapterVIDTBase_ne_zero)
    change Tendsto firstMean (nhds (chapterVIDZBase, chapterVIDTBase))
      (nhds (firstMean (chapterVIDZBase, chapterVIDTBase))) at hcontinuous
    rwa [hfirstMeanBase] at hcontinuous
  have hratioTendsto : Tendsto ratio
      (nhds (chapterVIDZBase, chapterVIDTBase))
      (nhds (secondMeanBase ^ (3 : ℤ))) := by
    have hcontinuous : ContinuousAt ratio (chapterVIDZBase, chapterVIDTBase) := by
      have hfirstContinuous : ContinuousAt firstMean
          (chapterVIDZBase, chapterVIDTBase) := by
        unfold firstMean
        exact continuousAt_snd.zpow₀ 3 (Or.inl chapterVIDTBase_ne_zero)
      have hfirstNe : firstMean (chapterVIDZBase, chapterVIDTBase) ≠ 0 := by
        rw [hfirstMeanBase]
        exact chapterVIKeplerExponential_ne_zero
          chapterVIDEccentricity chapterVIDX_ne_zero
      unfold ratio
      exact continuousAt_fst.div₀
        (hfirstContinuous.zpow₀ (-1) (Or.inl hfirstNe))
        (zpow_ne_zero _ hfirstNe)
    change Tendsto ratio (nhds (chapterVIDZBase, chapterVIDTBase))
      (nhds (ratio (chapterVIDZBase, chapterVIDTBase))) at hcontinuous
    rwa [hratioBase] at hcontinuous
  have hsecondMeanTendsto : Tendsto secondMean
      (nhds (chapterVIDZBase, chapterVIDTBase)) (nhds secondMeanBase) := by
    have hinverse :=
      (analyticAt_chapterVIPowerLocalInverse 3 secondMeanBase
        (chapterVIKeplerExponential_ne_zero 0 chapterVIDY_ne_zero) (by norm_num)).continuousAt
    have hcomp := hinverse.tendsto.comp hratioTendsto
    simpa only [Function.comp_def, secondMean,
      chapterVIPowerLocalInverse_apply_base] using hcomp
  have hpower := eventually_chapterVIPowerLocalInverse_conj 3 secondMeanBase
    (chapterVIKeplerExponential_ne_zero 0 chapterVIDY_ne_zero) (by norm_num)
    conj_chapterVIDSecondMeanBase
  have hfirst := eventually_chapterVIKeplerLocalInverse_conj
    chapterVIDEccentricity chapterVIDX chapterVIDX_ne_zero
    chapterVID_firstKeplerCritical conj_chapterVIDEccentricity conj_chapterVIDX
  have hsecond := eventually_chapterVIKeplerLocalInverse_conj
    0 chapterVIDY chapterVIDY_ne_zero chapterVID_secondKeplerCritical
    (by simp) conj_chapterVIDY
  filter_upwards [hratioTendsto.eventually hpower,
    hfirstMeanTendsto.eventually hfirst,
    hsecondMeanTendsto.eventually hsecond] with point hpowerPoint hfirstPoint hsecondPoint
  have hfirstConj : firstMean (chapterVIConjPoint point) = conj (firstMean point) := by
    unfold firstMean chapterVIConjPoint
    exact conj_zpow 3 point.2
  have hratioConj : ratio (chapterVIConjPoint point) = conj (ratio point) := by
    unfold ratio
    rw [hfirstConj]
    simp only [chapterVIConjPoint, map_div₀, map_zpow₀]
  have hsecondMeanConj : secondMean (chapterVIConjPoint point) =
      conj (secondMean point) := by
    unfold secondMean
    rw [hratioConj, hpowerPoint]
  unfold chapterVIPoincareAnomalyPair
  change
    (chapterVIKeplerLocalInverse chapterVIDEccentricity chapterVIDX chapterVIDX_ne_zero
        chapterVID_firstKeplerCritical (firstMean (chapterVIConjPoint point)),
      chapterVIKeplerLocalInverse 0 chapterVIDY chapterVIDY_ne_zero
        chapterVID_secondKeplerCritical (secondMean (chapterVIConjPoint point))) = _
  rw [hfirstConj, hfirstPoint, hsecondMeanConj, hsecondPoint]

/-- The concrete Laurent radicand has real coefficients and therefore commutes exactly with
conjugation. -/
theorem chapterVIDPlanarSourceRadicand_conj (x y : ℂ) :
    chapterVIPlanarSourceRadicand chapterVIDEccentricity chapterVIDComplement
        0 1 2 2 (conj x) (conj y) =
      conj (chapterVIPlanarSourceRadicand chapterVIDEccentricity chapterVIDComplement
        0 1 2 2 x y) := by
  unfold chapterVIPlanarSourceRadicand chapterVIPlanarCollisionFactorPlus
    chapterVIPlanarCollisionFactorMinus chapterVIPlanarKeplerLaurentPlus
    chapterVIPlanarKeplerLaurentMinus chapterVIPlanarDistanceFactorPlus
    chapterVIPlanarDistanceFactorMinus
  simp only [map_mul, map_sub, map_add, map_pow, map_div₀, map_zero, map_one,
    map_ofNat, conj_chapterVIDEccentricity, conj_chapterVIDComplement]

/-- Poincaré's literal analytic radicand commutes with conjugation on a full neighborhood of
the concrete double point D. -/
theorem eventually_chapterVIDRadicand_conj :
    ∀ᶠ point in nhds (chapterVIDZBase, chapterVIDTBase),
      chapterVIDRadicand (chapterVIConjPoint point) =
        conj (chapterVIDRadicand point) := by
  filter_upwards [eventually_chapterVIDPoincareAnomalyPair_conj] with point hpair
  change
    chapterVIPlanarSourceRadicand chapterVIDEccentricity chapterVIDComplement
        0 1 2 2
        (chapterVIPoincareAnomalyPair (-1) 3 chapterVIDEccentricity 0
          (chapterVIDX, chapterVIDY) chapterVIDX_ne_zero chapterVIDY_ne_zero
          chapterVID_firstKeplerCritical chapterVID_secondKeplerCritical (by norm_num)
          (chapterVIConjPoint point)).1
        (chapterVIPoincareAnomalyPair (-1) 3 chapterVIDEccentricity 0
          (chapterVIDX, chapterVIDY) chapterVIDX_ne_zero chapterVIDY_ne_zero
          chapterVID_firstKeplerCritical chapterVID_secondKeplerCritical (by norm_num)
          (chapterVIConjPoint point)).2 = _
  rw [hpair]
  exact chapterVIDPlanarSourceRadicand_conj _ _

/-- Differentiating the exact conjugation identity in the fiber variable shows that the critical
equation itself commutes with conjugation near D. -/
theorem eventually_chapterVIDFiberDerivative_conj :
    ∀ᶠ point in nhds (chapterVIDZBase, chapterVIDTBase),
      chapterVIFiberDerivative chapterVIDRadicand (chapterVIConjPoint point) =
        conj (chapterVIFiberDerivative chapterVIDRadicand point) := by
  let equalitySet : Set (ℂ × ℂ) := {point |
    chapterVIDRadicand (chapterVIConjPoint point) = conj (chapterVIDRadicand point)}
  have hequalityNhds : equalitySet ∈ nhds (chapterVIDZBase, chapterVIDTBase) := by
    change {point |
      chapterVIDRadicand (chapterVIConjPoint point) =
        conj (chapterVIDRadicand point)} ∈ nhds (chapterVIDZBase, chapterVIDTBase)
    exact eventually_chapterVIDRadicand_conj
  obtain ⟨domain, hdomainSubset, hdomainOpen, hbaseDomain⟩ :=
    mem_nhds_iff.mp hequalityNhds
  have hanalytic := analyticAt_chapterVIDRadicand.eventually_analyticAt
  have hconjTendsto : Tendsto chapterVIConjPoint
      (nhds (chapterVIDZBase, chapterVIDTBase))
      (nhds (chapterVIDZBase, chapterVIDTBase)) := by
    have hcontinuous : ContinuousAt chapterVIConjPoint
        (chapterVIDZBase, chapterVIDTBase) := by
      unfold chapterVIConjPoint
      fun_prop
    change Tendsto chapterVIConjPoint (nhds (chapterVIDZBase, chapterVIDTBase))
      (nhds (chapterVIConjPoint (chapterVIDZBase, chapterVIDTBase))) at hcontinuous
    simpa only [chapterVIConjPoint_base] using hcontinuous
  filter_upwards [mem_of_superset (hdomainOpen.mem_nhds hbaseDomain) (fun x hx ↦ hx),
    hanalytic, hconjTendsto.eventually hanalytic] with point hpointDomain
      hpointAnalytic hconjPointAnalytic
  have hsliceAnalytic : AnalyticAt ℂ
      (fun w ↦ chapterVIDRadicand (point.1, w)) point.2 := by
    exact hpointAnalytic.comp_of_eq (analyticAt_const.prod analyticAt_id) rfl
  have hconjSliceAnalytic : AnalyticAt ℂ
      (fun w ↦ chapterVIDRadicand (conj point.1, w)) (conj point.2) := by
    exact hconjPointAnalytic.comp_of_eq
      (analyticAt_const.prod analyticAt_id) (by simp [chapterVIConjPoint])
  have hpairTendsto : Tendsto (fun w : ℂ ↦ (point.1, conj w))
      (nhds (conj point.2)) (nhds point) := by
    have hcontinuous : ContinuousAt (fun w : ℂ ↦ (point.1, conj w))
        (conj point.2) := continuousAt_const.prodMk
          Complex.continuous_conj.continuousAt
    change Tendsto (fun w : ℂ ↦ (point.1, conj w)) (nhds (conj point.2))
      (nhds (point.1, conj (conj point.2))) at hcontinuous
    simpa using hcontinuous
  have hlocalEquality :
      (fun w ↦ chapterVIDRadicand (conj point.1, w)) =ᶠ[nhds (conj point.2)]
        (conj ∘ (fun w ↦ chapterVIDRadicand (point.1, w)) ∘ conj) := by
    have hmem : ∀ᶠ w in nhds (conj point.2), (point.1, conj w) ∈ domain :=
      hpairTendsto.eventually (hdomainOpen.mem_nhds hpointDomain)
    filter_upwards [hmem] with w hw
    have heq := hdomainSubset hw
    change chapterVIDRadicand (conj point.1, conj (conj w)) =
      conj (chapterVIDRadicand (point.1, conj w)) at heq
    simpa [Function.comp_apply] using heq
  have hreflected := hsliceAnalytic.hasStrictDerivAt.hasDerivAt.conj_conj
  have hleft := hreflected.congr_of_eventuallyEq hlocalEquality
  change chapterVIFiberDerivative chapterVIDRadicand
      (conj point.1, conj point.2) =
    conj (chapterVIFiberDerivative chapterVIDRadicand point)
  rw [chapterVIFiberDerivative_eq_deriv hconjPointAnalytic,
    chapterVIFiberDerivative_eq_deriv hpointAnalytic]
  exact hleft.deriv

/-- The analytic critical center selected by the complex implicit-function theorem commutes with
conjugation.  The proof uses the local uniqueness clause of that same theorem; no new branch is
chosen. -/
theorem eventually_chapterVIDCriticalCenter_conj :
    ∀ᶠ z in nhds chapterVIDZBase,
      chapterVIDCriticalCenter (conj z) =
        conj (chapterVIDCriticalCenter z) := by
  let critical : ℂ × ℂ → ℂ := chapterVIFiberDerivative chapterVIDRadicand
  have hf := analyticAt_chapterVIDRadicand
  have hfiber : AnalyticAt ℂ
      (fun w ↦ chapterVIDRadicand (chapterVIDZBase, w)) chapterVIDTBase :=
    hf.comp_of_eq (analyticAt_const.prod analyticAt_id) rfl
  have hjet := (analyticOrderAt_eq_two_iff hfiber).mp
    analyticOrderAt_chapterVIDPoincareRadicand_eq_two
  have hinvertible :
      (fderiv ℂ critical (chapterVIDZBase, chapterVIDTBase) ∘L
        ContinuousLinearMap.inr ℂ ℂ ℂ).IsInvertible := by
    exact chapterVICriticalDerivative_isInvertible hf hjet.2.2
  let cdf : ContDiffAt ℂ ω critical (chapterVIDZBase, chapterVIDTBase) :=
    (analyticAt_chapterVIFiberDerivative hf).contDiffAt
  let canonical : ℂ → ℂ := cdf.implicitFunction (by simp) hinvertible
  have hcriticalBase : critical (chapterVIDZBase, chapterVIDTBase) = 0 := by
    have hzero := eventually_chapterVIDCriticalCenter_fiberDerivative_eq_zero.self_of_nhds
    rw [chapterVIDCriticalCenter_base] at hzero
    exact hzero
  have hiff : ∀ᶠ point in nhds (chapterVIDZBase, chapterVIDTBase),
      critical point = critical (chapterVIDZBase, chapterVIDTBase) ↔
        canonical point.1 = point.2 := by
    simpa only [canonical, cdf] using
      cdf.eventually_apply_eq_iff_implicitFunction (by simp) hinvertible
  have hcenterGraphTendsto : Tendsto
      (fun z ↦ (z, chapterVIDCriticalCenter z))
      (nhds chapterVIDZBase) (nhds (chapterVIDZBase, chapterVIDTBase)) := by
    have hcontinuous : ContinuousAt
        (fun z ↦ (z, chapterVIDCriticalCenter z)) chapterVIDZBase :=
      continuousAt_id.prodMk analyticAt_chapterVIDCriticalCenter.continuousAt
    change Tendsto (fun z ↦ (z, chapterVIDCriticalCenter z))
      (nhds chapterVIDZBase)
      (nhds (chapterVIDZBase, chapterVIDCriticalCenter chapterVIDZBase)) at hcontinuous
    simpa only [chapterVIDCriticalCenter_base] using hcontinuous
  have hcanonicalCenter : ∀ᶠ z in nhds chapterVIDZBase,
      canonical z = chapterVIDCriticalCenter z := by
    filter_upwards [hcenterGraphTendsto.eventually hiff,
      eventually_chapterVIDCriticalCenter_fiberDerivative_eq_zero]
      with z hiffPoint hzero
    exact hiffPoint.mp (hzero.trans hcriticalBase.symm)
  let reflected : ℂ → ℂ := fun z ↦
    conj (chapterVIDCriticalCenter (conj z))
  have hreflectedBase : reflected chapterVIDZBase = chapterVIDTBase := by
    simp [reflected]
  have hreflectedGraphTendsto : Tendsto (fun z ↦ (z, reflected z))
      (nhds chapterVIDZBase) (nhds (chapterVIDZBase, chapterVIDTBase)) := by
    have hcontinuous : ContinuousAt (fun z ↦ (z, reflected z)) chapterVIDZBase := by
      have hinner : ContinuousAt
          (fun z ↦ chapterVIDCriticalCenter (conj z)) chapterVIDZBase := by
        have hcenterAtConj : ContinuousAt chapterVIDCriticalCenter
            (conj chapterVIDZBase) := by
          simpa only [conj_chapterVIDZBase] using
            analyticAt_chapterVIDCriticalCenter.continuousAt
        exact hcenterAtConj.comp_of_eq
          Complex.continuous_conj.continuousAt rfl
      have hreflectedContinuous : ContinuousAt reflected chapterVIDZBase := by
        unfold reflected
        exact Complex.continuous_conj.continuousAt.comp_of_eq hinner rfl
      exact continuousAt_id.prodMk hreflectedContinuous
    change Tendsto (fun z ↦ (z, reflected z)) (nhds chapterVIDZBase)
      (nhds (chapterVIDZBase, reflected chapterVIDZBase)) at hcontinuous
    rwa [hreflectedBase] at hcontinuous
  have hconjTendsto : Tendsto conj (nhds chapterVIDZBase) (nhds chapterVIDZBase) := by
    have hcontinuous := Complex.continuous_conj.continuousAt (x := chapterVIDZBase)
    change Tendsto conj (nhds chapterVIDZBase) (nhds (conj chapterVIDZBase)) at hcontinuous
    simpa only [conj_chapterVIDZBase] using hcontinuous
  have hinnerGraphTendsto : Tendsto
      (fun z ↦ (conj z, chapterVIDCriticalCenter (conj z)))
      (nhds chapterVIDZBase) (nhds (chapterVIDZBase, chapterVIDTBase)) := by
    exact hcenterGraphTendsto.comp hconjTendsto
  have hreflectedZero : ∀ᶠ z in nhds chapterVIDZBase,
      critical (z, reflected z) = 0 := by
    filter_upwards [hconjTendsto.eventually
        eventually_chapterVIDCriticalCenter_fiberDerivative_eq_zero,
      hinnerGraphTendsto.eventually eventually_chapterVIDFiberDerivative_conj]
      with z hzero hsymm
    change critical
      (chapterVIConjPoint (conj z, chapterVIDCriticalCenter (conj z))) = _ at hsymm
    simpa only [critical, reflected, chapterVIConjPoint, Complex.conj_conj, map_zero] using
      hsymm.trans (congrArg conj hzero)
  have hcanonicalReflected : ∀ᶠ z in nhds chapterVIDZBase,
      canonical z = reflected z := by
    filter_upwards [hreflectedGraphTendsto.eventually hiff, hreflectedZero]
      with z hiffPoint hzero
    exact hiffPoint.mp (hzero.trans hcriticalBase.symm)
  filter_upwards [hcanonicalCenter, hcanonicalReflected] with z hcenter hreflected
  have heq : chapterVIDCriticalCenter z = reflected z := hcenter.symm.trans hreflected
  have := congrArg conj heq
  simpa only [reflected, Complex.conj_conj] using this.symm

/-- The moving critical value is a real analytic germ: it commutes with conjugation near the
positive real source point `z_D`. -/
theorem eventually_chapterVIDCriticalValue_conj :
    ∀ᶠ z in nhds chapterVIDZBase,
      chapterVIDCriticalValue (conj z) = conj (chapterVIDCriticalValue z) := by
  have hgraphTendsto : Tendsto (fun z ↦ (z, chapterVIDCriticalCenter z))
      (nhds chapterVIDZBase) (nhds (chapterVIDZBase, chapterVIDTBase)) := by
    have hcontinuous : ContinuousAt
        (fun z ↦ (z, chapterVIDCriticalCenter z)) chapterVIDZBase :=
      continuousAt_id.prodMk analyticAt_chapterVIDCriticalCenter.continuousAt
    change Tendsto (fun z ↦ (z, chapterVIDCriticalCenter z))
      (nhds chapterVIDZBase)
      (nhds (chapterVIDZBase, chapterVIDCriticalCenter chapterVIDZBase)) at hcontinuous
    simpa only [chapterVIDCriticalCenter_base] using hcontinuous
  filter_upwards [eventually_chapterVIDCriticalCenter_conj,
    hgraphTendsto.eventually eventually_chapterVIDRadicand_conj]
    with z hcenter hradicand
  unfold chapterVIDCriticalValue
  rw [hcenter]
  simpa only [chapterVIConjPoint] using hradicand

/-- Consequently the canonical critical-value inverse sends real inputs to exactly real source
parameters near the singular value.  This is the non-finite half of radial placement. -/
theorem eventually_chapterVIDCriticalParameterInverseAtD_im_eq_zero :
    ∀ᶠ k : ℝ in nhds 0,
      (chapterVIDCriticalParameterInverseAtD (k : ℂ)).im = 0 := by
  let hf := analyticAt_chapterVIDCriticalValue.hasStrictDerivAt
  have hvalueIm : (chapterVIDCriticalValue chapterVIDZBase).im = 0 := by simp
  simpa only [chapterVIDCriticalParameterInverseAtD,
    chapterVIDCriticalParameterInverse, chapterVIDCriticalValue_base,
    Complex.zero_re] using
    eventually_localInverse_ofReal_im_eq_zero hf
      deriv_chapterVIDCriticalValue_ne_zero conj_chapterVIDZBase hvalueIm
      eventually_chapterVIDCriticalValue_conj

/-! ## Compiled-certificate-backed orientation -/

/-- The real second anomaly at D, separated from its coercion to `ℂ`. -/
def chapterVIDYReal : ℝ :=
  (chapterVIDRoot - 1 / 100) ^ 2 /
    (2 * (1 + (1 / 100 : ℝ) ^ 2) * chapterVIDRoot)

@[simp] theorem chapterVIDY_eq_ofReal : chapterVIDY = (chapterVIDYReal : ℂ) := by
  unfold chapterVIDY chapterVIDYReal chapterVIDX
  push_cast
  rfl

theorem chapterVIDYReal_neg : chapterVIDYReal < 0 := by
  have hx : chapterVIDRoot < 0 := chapterVIDRoot_lt_zero
  have hnum : 0 < (chapterVIDRoot - 1 / 100) ^ 2 := sq_pos_of_ne_zero (by linarith)
  have hden : 2 * (1 + (1 / 100 : ℝ) ^ 2) * chapterVIDRoot < 0 := by
    exact mul_neg_of_pos_of_neg (by positivity) chapterVIDRoot_lt_zero
  exact div_neg_of_pos_of_neg hnum hden

/-- The real first Kepler mean at D. -/
def chapterVIDFirstMeanReal : ℝ :=
  chapterVIDRoot * Real.exp
    ((100 / 10001 : ℝ) * (chapterVIDRoot⁻¹ - chapterVIDRoot))

@[simp] theorem chapterVIDFirstMean_eq_ofReal :
    chapterVIKeplerExponential chapterVIDEccentricity chapterVIDX =
      (chapterVIDFirstMeanReal : ℂ) := by
  unfold chapterVIDFirstMeanReal chapterVIKeplerExponential chapterVIDEccentricity chapterVIDX
  push_cast
  congr 2
  ring

theorem chapterVIDFirstMeanReal_neg : chapterVIDFirstMeanReal < 0 := by
  unfold chapterVIDFirstMeanReal
  exact mul_neg_of_neg_of_pos chapterVIDRoot_lt_zero (Real.exp_pos _)

/-- Exact source formula for the motion of the second anomaly along the external parameter. -/
theorem deriv_chapterVIDParameterY_eq :
    deriv chapterVIDParameterY chapterVIDZBase =
      ((3 : ℂ) * chapterVIDY ^ 2)⁻¹ *
        chapterVIKeplerExponential chapterVIDEccentricity chapterVIDX := by
  rw [hasDerivAt_chapterVIDParameterY.deriv,
    hasDerivAt_chapterVIDParameterSecondMean.deriv]
  rw [show chapterVIKeplerExponentialDerivative 0 chapterVIDY = 1 by
    simp [chapterVIKeplerExponentialDerivative]]
  rw [show chapterVIKeplerExponential 0 chapterVIDY = chapterVIDY by
    simp [chapterVIKeplerExponential]]
  rw [chapterVIDTBase_pow]
  field_simp [chapterVIKeplerExponential_ne_zero
    chapterVIDEccentricity chapterVIDX_ne_zero,
    chapterVIDY_ne_zero]
  norm_num
  ring

theorem deriv_chapterVIDParameterY_eq_ofReal :
    deriv chapterVIDParameterY chapterVIDZBase =
      (((3 : ℝ) * chapterVIDYReal ^ 2)⁻¹ * chapterVIDFirstMeanReal : ℝ) := by
  rw [deriv_chapterVIDParameterY_eq, chapterVIDY_eq_ofReal,
    chapterVIDFirstMean_eq_ofReal]
  push_cast
  rfl

theorem deriv_chapterVIDParameterY_re_neg :
    (deriv chapterVIDParameterY chapterVIDZBase).re < 0 := by
  rw [deriv_chapterVIDParameterY_eq_ofReal, ofReal_re]
  have hcoefficient : 0 < ((3 : ℝ) * chapterVIDYReal ^ 2)⁻¹ := by
    apply inv_pos.mpr
    exact mul_pos (by norm_num) (sq_pos_of_ne_zero chapterVIDYReal_neg.ne)
  exact mul_neg_of_pos_of_neg hcoefficient chapterVIDFirstMeanReal_neg

/-- Closed rational expression for the nonvanishing companion collision factor at D. -/
theorem chapterVIDY_rational_formula :
    chapterVIDY = (100 * chapterVIDX - 1) ^ 2 / (20002 * chapterVIDX) := by
  unfold chapterVIDY
  field_simp [chapterVIDX_ne_zero]
  ring

theorem chapterVIDParameterCollisionMinus_base_formula :
    chapterVIDParameterCollisionMinus chapterVIDZBase =
      ((chapterVIDX + 100) * (100 * chapterVIDX + 1) *
          (100 * chapterVIDX ^ 2 - 30003 * chapterVIDX + 100)) /
        (10001 * chapterVIDX * (100 * chapterVIDX - 1) ^ 2) := by
  unfold chapterVIDParameterCollisionMinus chapterVIDZBase
  rw [chapterVIPoincareCollisionFactorMinus_apply_base
    (-1) 3 chapterVIDEccentricity chapterVIDComplement 0 1 2
    (chapterVIDX, chapterVIDY) chapterVIDX_ne_zero chapterVIDY_ne_zero
    chapterVID_firstKeplerCritical chapterVID_secondKeplerCritical (by norm_num)
    chapterVIDTBase chapterVIDTBase_pow]
  unfold chapterVIPlanarCollisionFactorMinus chapterVIPlanarKeplerLaurentMinus
    chapterVIPlanarDistanceFactorMinus chapterVIDEccentricity chapterVIDComplement
  rw [chapterVIDY_rational_formula]
  have hlinear : 100 * chapterVIDX - 1 ≠ 0 := by
    intro h
    apply chapterVIDX_sub_tau_ne_zero
    apply mul_left_cancel₀ (show (100 : ℂ) ≠ 0 by norm_num)
    linear_combination h
  have hsquareEq : 1 - chapterVIDX * 200 + chapterVIDX ^ 2 * 10000 =
      (100 * chapterVIDX - 1) ^ 2 := by ring
  have hscaledSquareEq :
      10001 - chapterVIDX * 2000200 + chapterVIDX ^ 2 * 100010000 =
        10001 * (100 * chapterVIDX - 1) ^ 2 := by ring
  have hsquareExpression :
      1 - chapterVIDX * 200 + chapterVIDX ^ 2 * 10000 ≠ 0 := by
    rw [hsquareEq]
    exact pow_ne_zero 2 hlinear
  have hscaledSquareExpression :
      10001 - chapterVIDX * 2000200 + chapterVIDX ^ 2 * 100010000 ≠ 0 := by
    rw [hscaledSquareEq]
    exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hlinear)
  field_simp [chapterVIDX_ne_zero, chapterVIDX_sub_tau_ne_zero, hlinear,
    hsquareExpression, hscaledSquareExpression]
  all_goals ring_nf
  all_goals apply mul_left_cancel₀ hsquareExpression
  all_goals field_simp [hsquareExpression]
  all_goals ring

theorem chapterVIDParameterCollisionMinus_base_eq_ofReal :
    chapterVIDParameterCollisionMinus chapterVIDZBase =
      (((chapterVIDRoot + 100) * (100 * chapterVIDRoot + 1) *
          (100 * chapterVIDRoot ^ 2 - 30003 * chapterVIDRoot + 100)) /
        (10001 * chapterVIDRoot * (100 * chapterVIDRoot - 1) ^ 2) : ℝ) := by
  rw [chapterVIDParameterCollisionMinus_base_formula]
  unfold chapterVIDX
  push_cast
  ring_nf

theorem chapterVIDParameterCollisionMinus_base_re_pos :
    0 < (chapterVIDParameterCollisionMinus chapterVIDZBase).re := by
  rw [chapterVIDParameterCollisionMinus_base_eq_ofReal, ofReal_re]
  have hxLower := chapterVIDRoot_mem.1
  have hxUpper := chapterVIDRoot_mem.2
  have h₁ : 0 < chapterVIDRoot + 100 := by linarith
  have h₂ : 100 * chapterVIDRoot + 1 < 0 := by linarith
  have h₃ : 0 < 100 * chapterVIDRoot ^ 2 - 30003 * chapterVIDRoot + 100 := by
    nlinarith [sq_nonneg chapterVIDRoot]
  have hden : 10001 * chapterVIDRoot * (100 * chapterVIDRoot - 1) ^ 2 < 0 := by
    have hsquare : 0 < (100 * chapterVIDRoot - 1) ^ 2 :=
      sq_pos_of_ne_zero (by linarith)
    exact mul_neg_of_neg_of_pos
      (mul_neg_of_pos_of_neg (by norm_num) chapterVIDRoot_lt_zero) hsquare
  exact div_pos_of_neg_of_neg (mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg h₁ h₂) h₃)
    hden

/-- Exact product formula for the derivative of the moving critical value. -/
theorem deriv_chapterVIDCriticalValue_eq_collision_product :
    deriv chapterVIDCriticalValue chapterVIDZBase =
      (-2 * deriv chapterVIDParameterY chapterVIDZBase) *
        chapterVIDParameterCollisionMinus chapterVIDZBase := by
  rw [deriv_chapterVIDCriticalValue_eq_parameterDerivative,
    chapterVIDParameterDerivative_eq_sliceDeriv,
    chapterVIDRadicand_parameterSlice_eq]
  have hminus :=
    analyticAt_chapterVIDParameterCollisionMinus.hasStrictDerivAt.hasDerivAt
  have hproduct := hasDerivAt_chapterVIDParameterCollisionPlus.mul hminus
  rw [hproduct.deriv, chapterVIDParameterCollisionPlus_base]
  ring

/-- The orientation required by Poincaré's radial approach.  Its only finite input is the
LeanCompCert-isolated interval for `chapterVIDRoot`; all subsequent sign propagation is exact. -/
theorem deriv_chapterVIDCriticalValue_re_pos :
    0 < (deriv chapterVIDCriticalValue chapterVIDZBase).re := by
  rw [deriv_chapterVIDCriticalValue_eq_collision_product]
  have hfirstReal :
      (-2 * deriv chapterVIDParameterY chapterVIDZBase).im = 0 := by
    have hreal : (deriv chapterVIDParameterY chapterVIDZBase).im = 0 := by
      have h := congrArg Complex.im deriv_chapterVIDParameterY_eq_ofReal
      simpa only [Complex.ofReal_im] using h
    rw [mul_im]
    norm_num [hreal]
  have hsecondReal :
      (chapterVIDParameterCollisionMinus chapterVIDZBase).im = 0 := by
    have h := congrArg Complex.im chapterVIDParameterCollisionMinus_base_eq_ofReal
    simpa only [Complex.ofReal_im] using h
  rw [mul_re]
  simp only [hfirstReal, hsecondReal, mul_zero, sub_zero]
  exact mul_pos (by
    rw [mul_re]
    norm_num
    linarith [deriv_chapterVIDParameterY_re_neg])
    chapterVIDParameterCollisionMinus_base_re_pos

theorem deriv_chapterVIDCriticalValue_im_eq_zero :
    (deriv chapterVIDCriticalValue chapterVIDZBase).im = 0 := by
  rw [deriv_chapterVIDCriticalValue_eq_collision_product]
  have hfirst : (deriv chapterVIDParameterY chapterVIDZBase).im = 0 := by
    have h := congrArg Complex.im deriv_chapterVIDParameterY_eq_ofReal
    simpa only [Complex.ofReal_im] using h
  have hsecond : (chapterVIDParameterCollisionMinus chapterVIDZBase).im = 0 := by
    have h := congrArg Complex.im chapterVIDParameterCollisionMinus_base_eq_ofReal
    simpa only [Complex.ofReal_im] using h
  rw [mul_im]
  norm_num [hfirst, hsecond]

theorem chapterVIDCriticalParameterInverse_derivative_re_pos :
    0 < ((deriv chapterVIDCriticalValue chapterVIDZBase)⁻¹).re := by
  have hreal : deriv chapterVIDCriticalValue chapterVIDZBase =
      ((deriv chapterVIDCriticalValue chapterVIDZBase).re : ℂ) := by
    apply Complex.ext
    · simp
    · simpa only [Complex.ofReal_im] using deriv_chapterVIDCriticalValue_im_eq_zero
  rw [hreal, ← Complex.ofReal_inv, Complex.ofReal_re]
  exact inv_pos.mpr deriv_chapterVIDCriticalValue_re_pos

end PoincareChapterVI
