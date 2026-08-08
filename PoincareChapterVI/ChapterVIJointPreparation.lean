/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.ChapterVIAnalyticCentering
import PoincareChapterVI.ChapterVIAnalyticPreparation

/-!
# The centered Chapter VI germ as a convergent prepared germ

The two analytic Hadamard divisions of `ChapterVIAnalyticCentering.lean` produce the exact local
normal form `ψ(z,u) = u² U(z,u)` with a jointly analytic unit.  This file packages that result in
the generic `ChapterVIConvergentPreparedGerm` interface, with center and kappa identically zero.
Consequently all of the existing two-variable square-root, inverse-branch, and contour-transport
machinery applies to Poincaré's actual centered source radicand.
-/

noncomputable section

open Filter Set
open scoped Topology

namespace PoincareChapterVI

/-- The exact centered source germ has a convergent prepared-germ realization with completed
quadratic factor `u²`. -/
theorem exists_chapterVIDCenteredConvergentPreparedGerm :
    ∃ germ : ChapterVIConvergentPreparedGerm chapterVIDCenteredRadicand
        (chapterVIDZBase, (0 : ℂ)),
      germ.center = 0 ∧ germ.kappa = 0 := by
  obtain ⟨unit, hunitAnalytic, hunitBase, hfactor⟩ :=
    exists_chapterVIDCenteredJointAnalyticUnit
  obtain ⟨unitSeries, hunitSeries⟩ := hunitAnalytic
  obtain ⟨commonSeries, hradicandSeries⟩ :=
    exists_hasFPowerSeriesAt_chapterVIDCenteredRadicand
  have hpreparedEq : chapterVIDCenteredRadicand =ᶠ[nhds (chapterVIDZBase, (0 : ℂ))]
      (fun point : ℂ × ℂ ↦
        (((point.2 - (0 : ℂ)) ^ 2 + (0 : ℂ)) * unit point)) := by
    filter_upwards [hfactor] with point hpoint
    simpa using hpoint
  have hpreparedSeries : HasFPowerSeriesAt
      (fun point : ℂ × ℂ ↦
        (((point.2 - (0 : ℂ)) ^ 2 + (0 : ℂ)) * unit point))
      commonSeries (chapterVIDZBase, (0 : ℂ)) :=
    hradicandSeries.congr hpreparedEq
  let zeroSeries : FormalMultilinearSeries ℂ ℂ ℂ :=
    constFormalMultilinearSeries ℂ ℂ 0
  let germ : ChapterVIConvergentPreparedGerm chapterVIDCenteredRadicand
      (chapterVIDZBase, (0 : ℂ)) :=
    { center := 0
      kappa := 0
      unit := unit
      centerSeries := zeroSeries
      kappaSeries := zeroSeries
      unitSeries := unitSeries
      commonSeries := commonSeries
      centerHasFPowerSeries := hasFPowerSeriesAt_const
      kappaHasFPowerSeries := hasFPowerSeriesAt_const
      unitHasFPowerSeries := hunitSeries
      radicandHasFPowerSeries := hradicandSeries
      preparedHasFPowerSeries := hpreparedSeries
      center_base := rfl
      kappa_base := rfl
      unit_base_ne_zero := hunitBase }
  refine ⟨germ, ?_, ?_⟩ <;> rfl

/-- A fixed prepared-germ realization of the exact centered source radicand. -/
noncomputable def chapterVIDCenteredConvergentPreparedGerm :
    ChapterVIConvergentPreparedGerm chapterVIDCenteredRadicand
      (chapterVIDZBase, (0 : ℂ)) :=
  Classical.choose exists_chapterVIDCenteredConvergentPreparedGerm

@[simp]
theorem chapterVIDCenteredConvergentPreparedGerm_center :
    chapterVIDCenteredConvergentPreparedGerm.center = 0 :=
  (Classical.choose_spec exists_chapterVIDCenteredConvergentPreparedGerm).1

@[simp]
theorem chapterVIDCenteredConvergentPreparedGerm_kappa :
    chapterVIDCenteredConvergentPreparedGerm.kappa = 0 :=
  (Classical.choose_spec exists_chapterVIDCenteredConvergentPreparedGerm).2

/-- The prepared quadratic of the centered source germ is exactly the square of the centered
fiber coordinate. -/
@[simp]
theorem chapterVIDCenteredConvergentPreparedGerm_quadratic (point : ℂ × ℂ) :
    chapterVIDCenteredConvergentPreparedGerm.quadratic point = point.2 ^ 2 := by
  simp [ChapterVIConvergentPreparedGerm.quadratic]

/-- On the singular fiber, the joint prepared unit agrees as an analytic germ with the
one-variable unit used in the explicit pole and logarithm calculation. -/
theorem eventually_chapterVIDCenteredPreparedUnit_eq_fiberUnit :
    (fun u : ℂ ↦ chapterVIDCenteredConvergentPreparedGerm.unit
      (chapterVIDZBase, u)) =ᶠ[nhds 0] chapterVIDCenteredFiberUnit := by
  have hfactorJoint :=
    chapterVIDCenteredConvergentPreparedGerm.eventually_factorization
  have hsingularFiberMap : Filter.Tendsto
      (fun u : ℂ ↦ (chapterVIDZBase, u))
      (nhds 0) (nhds (chapterVIDZBase, (0 : ℂ))) :=
    continuousAt_const.prodMk continuousAt_id
  have hfactorJointFiber : ∀ᶠ u in nhds 0,
      chapterVIDCenteredRadicand (chapterVIDZBase, u) =
        u ^ 2 * chapterVIDCenteredConvergentPreparedGerm.unit
          (chapterVIDZBase, u) := by
    have hpulled := hsingularFiberMap.eventually hfactorJoint
    filter_upwards [hpulled] with u hu
    simpa using hu
  have hpunctured :
      (fun u : ℂ ↦ chapterVIDCenteredConvergentPreparedGerm.unit
        (chapterVIDZBase, u)) =ᶠ[nhdsWithin 0 ({0}ᶜ : Set ℂ)]
          chapterVIDCenteredFiberUnit := by
    filter_upwards [hfactorJointFiber.filter_mono nhdsWithin_le_nhds,
      eventually_chapterVIDCenteredRadicand_eq_sq_mul_fiberUnit.filter_mono
        nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with u hjoint hfiber hu
    apply mul_left_cancel₀ (pow_ne_zero 2 hu)
    exact hjoint.symm.trans hfiber
  have hjointUnitFiberAnalytic : AnalyticAt ℂ
      (fun u : ℂ ↦ chapterVIDCenteredConvergentPreparedGerm.unit
        (chapterVIDZBase, u)) 0 :=
    chapterVIDCenteredConvergentPreparedGerm.unitHasFPowerSeries.analyticAt.curry_right
  exact
    (hjointUnitFiberAnalytic.continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
      analyticAt_chapterVIDCenteredFiberUnit.continuousAt).mp hpunctured

/-- The automatically chosen unit-root germ in the joint prepared construction restricts to the
same root germ used in the singular-fiber logarithm calculation. -/
theorem eventually_chapterVIDCenteredPreparedUnitRoot_eq_fiberUnitRoot :
    (fun u : ℂ ↦ chapterVIDCenteredConvergentPreparedGerm.unitRootGerm.root
      (chapterVIDZBase, u)) =ᶠ[nhds 0]
        chapterVIDCenteredFiberUnitRootGerm.root := by
  have hunit := eventually_chapterVIDCenteredPreparedUnit_eq_fiberUnit
  have hbase := hunit.self_of_nhds
  by_cases hprincipal : chapterVIDCenteredConvergentPreparedGerm.unit
      (chapterVIDZBase, 0) ∈ Complex.slitPlane
  · have hfiberPrincipal : chapterVIDCenteredFiberUnit 0 ∈ Complex.slitPlane := by
      rwa [← hbase]
    filter_upwards [hunit] with u hu
    simp [ChapterVIConvergentPreparedGerm.unitRootGerm,
      chapterVIDCenteredFiberUnitRootGerm,
      ChapterVIHolomorphicSquareRootGerm.of_analyticAt,
      hprincipal, hfiberPrincipal, hu]
  · have hfiberPrincipal : chapterVIDCenteredFiberUnit 0 ∉ Complex.slitPlane := by
      rwa [← hbase]
    filter_upwards [hunit] with u hu
    simp [ChapterVIConvergentPreparedGerm.unitRootGerm,
      chapterVIDCenteredFiberUnitRootGerm,
      ChapterVIHolomorphicSquareRootGerm.of_analyticAt,
      hprincipal, hfiberPrincipal, hu]

/-- On the local square-root sheet for which the principal square root of `u²` is `u`, the joint
prepared inverse branch restricts to the singular-fiber branch used in the pole decomposition. -/
theorem eventually_chapterVIDCenteredPreparedInverseSquareRoot_eq_fiber
    : ∀ᶠ u in nhds (0 : ℂ),
      Complex.sqrt (u ^ 2) = u →
        chapterVIDCenteredConvergentPreparedGerm.inverseSquareRoot
            (chapterVIDZBase, u) =
          chapterVIDCenteredFiberInverseSquareRoot u := by
  filter_upwards [eventually_chapterVIDCenteredPreparedUnitRoot_eq_fiberUnitRoot]
    with u hroot hsqrt
  simp [ChapterVIConvergentPreparedGerm.inverseSquareRoot,
    chapterVIPreparedInverseSquareRootFromUnitGerm,
    chapterVIPreparedSquareRootFromUnitGerm,
    chapterVIDCenteredFiberInverseSquareRoot,
    chapterVIDCenteredFiberSquareRoot, hsqrt, hroot]

/-- On the sheet `sqrt (u²) = u`, the singular-fiber logarithmic primitive is also a primitive of
the restriction of the joint prepared inverse branch.  This is the precise bridge between the
two-variable preparation and the explicit Chapter VI logarithm calculation. -/
theorem exists_chapterVIDCenteredPreparedLogPrimitive :
    ∃ radius : ℝ, 0 < radius ∧
      ∃ regularPrimitive : ℂ → ℂ,
        regularPrimitive 0 = 0 ∧
        (∀ u ∈ Metric.ball (0 : ℂ) radius,
          HasDerivAt regularPrimitive (chapterVIDCenteredFiberRegular u) u) ∧
        ∀ u ∈ Metric.ball (0 : ℂ) radius ∩ Complex.slitPlane,
          Complex.sqrt (u ^ 2) = u →
          HasDerivAt
            (fun v ↦ chapterVIDCenteredFiberAmplitude 0 * Complex.log v +
              regularPrimitive v)
            (chapterVIDCenteredConvergentPreparedGerm.inverseSquareRoot
              (chapterVIDZBase, u)) u := by
  obtain ⟨radius, hradius, regularPrimitive, hregularZero,
      hregularDeriv, hlogDeriv⟩ :=
    exists_chapterVIDCenteredFiberLogPrimitive
  have hbranch :=
    eventually_chapterVIDCenteredPreparedInverseSquareRoot_eq_fiber
  obtain ⟨branchRadius, hbranchRadius, hbranchBall⟩ :=
    Metric.mem_nhds_iff.mp hbranch
  let commonRadius := min radius branchRadius
  have hcommonRadius : 0 < commonRadius := by
    exact lt_min hradius hbranchRadius
  refine ⟨commonRadius, hcommonRadius, regularPrimitive, hregularZero, ?_, ?_⟩
  · intro u hu
    exact hregularDeriv u
      (Metric.ball_subset_ball (min_le_left _ _) hu)
  · intro u hu hsqrt
    have huRadius : u ∈ Metric.ball (0 : ℂ) radius :=
      Metric.ball_subset_ball (min_le_left _ _) hu.1
    have huBranch : u ∈ Metric.ball (0 : ℂ) branchRadius :=
      Metric.ball_subset_ball (min_le_right _ _) hu.1
    have hbranchEq := hbranchBall huBranch hsqrt
    exact (hlogDeriv u ⟨huRadius, hu.2⟩).congr_deriv hbranchEq.symm

/-- Exact §100 local-arc formula on the selected sheet.  Every straight segment that remains in
the prepared branch chart, in the local slit-plane ball, and on the sheet `sqrt (u²)=u` integrates
to the endpoint jump of Poincaré's logarithmic primitive.  In particular the logarithmic
coefficient is the already-proved nonzero value `chapterVIDCenteredFiberAmplitude 0`. -/
theorem exists_chapterVIDCenteredPreparedLogSegmentIntegral :
    ∃ radius : ℝ, 0 < radius ∧
      ∃ regularPrimitive : ℂ → ℂ,
        regularPrimitive 0 = 0 ∧
        ∀ {start direction : ℂ},
          (∀ t ∈ Set.Icc (0 : ℝ) 1,
            let u := start + t • direction
            u ∈ Metric.ball (0 : ℂ) radius ∩ Complex.slitPlane ∧
              Complex.sqrt (u ^ 2) = u ∧
              u ∈ chapterVIDCenteredConvergentPreparedGerm.sliceBranchDomain
                chapterVIDZBase) →
          (∫ᶜ u in Path.segment start (start + direction),
            chapterVIComplexScalarOneForm
              (chapterVIDCenteredConvergentPreparedGerm.sliceInverseSquareRoot
                chapterVIDZBase) u) =
            chapterVIDCenteredFiberAmplitude 0 *
                (Complex.log (start + direction) - Complex.log start) +
              (regularPrimitive (start + direction) - regularPrimitive start) := by
  obtain ⟨radius, hradius, regularPrimitive, hregularZero,
      hregularDeriv, hlogDeriv⟩ :=
    exists_chapterVIDCenteredPreparedLogPrimitive
  refine ⟨radius, hradius, regularPrimitive, hregularZero, ?_⟩
  intro start direction hsegment
  let inverseBranch : ℂ → ℂ :=
    chapterVIDCenteredConvergentPreparedGerm.sliceInverseSquareRoot chapterVIDZBase
  let logPrimitive : ℂ → ℂ := fun u ↦
    chapterVIDCenteredFiberAmplitude 0 * Complex.log u + regularPrimitive u
  have hinverseContinuous : ContinuousOn inverseBranch
      (chapterVIDCenteredConvergentPreparedGerm.sliceBranchDomain chapterVIDZBase) :=
    (chapterVIDCenteredConvergentPreparedGerm
      |>.differentiableOn_sliceInverseSquareRoot chapterVIDZBase).continuousOn
  have hcont : ContinuousOn
      (fun t : ℝ ↦ inverseBranch (start + t • direction)) (Set.Icc 0 1) := by
    exact hinverseContinuous.comp (by fun_prop) fun t ht ↦ (hsegment t ht).2.2
  have hderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt logPrimitive (inverseBranch (start + t • direction))
        (start + t • direction) := by
    intro t ht
    obtain ⟨hu, hsqrt, hbranch⟩ := hsegment t ht
    simpa only [logPrimitive, inverseBranch,
      ChapterVIConvergentPreparedGerm.sliceInverseSquareRoot] using
      hlogDeriv (start + t • direction) hu hsqrt
  have hintegral := chapterVI_curveIntegral_segment_eq_sub_of_primitive hcont hderiv
  change
    (∫ᶜ u in Path.segment start (start + direction),
      chapterVIComplexScalarOneForm inverseBranch u) = _
  rw [hintegral]
  dsimp only [logPrimitive]
  ring

/-- The generic prepared inverse branch is holomorphic on its natural local two-variable chart. -/
theorem differentiableOn_chapterVIDCenteredPreparedInverseSquareRoot :
    DifferentiableOn ℂ chapterVIDCenteredConvergentPreparedGerm.inverseSquareRoot
      chapterVIDCenteredConvergentPreparedGerm.actualBranchDomain :=
  chapterVIDCenteredConvergentPreparedGerm
    |>.differentiableOn_inverseSquareRoot_actualBranchDomain

/-- On every point of the natural actual-branch chart, the prepared branch is an inverse square
root of Poincaré's exact centered source radicand. -/
theorem chapterVIDCenteredPreparedInverseSquareRoot_sq_mul
    {point : ℂ × ℂ}
    (hpoint : point ∈ chapterVIDCenteredConvergentPreparedGerm.actualBranchDomain) :
    chapterVIDCenteredConvergentPreparedGerm.inverseSquareRoot point ^ 2 *
      chapterVIDCenteredRadicand point = 1 :=
  chapterVIDCenteredConvergentPreparedGerm
    |>.inverseSquareRoot_sq_mul_radicand_of_mem_actualBranchDomain hpoint

/-- There is an open neighborhood of the pinch on whose natural punctured branch chart the
constructed joint inverse square root is certified against the actual centered radicand. -/
theorem exists_open_chapterVIDCenteredPreparedInverseSquareRoot_neighborhood :
    ∃ neighborhood : Set (ℂ × ℂ),
      IsOpen neighborhood ∧ (chapterVIDZBase, (0 : ℂ)) ∈ neighborhood ∧
      ∀ point ∈ neighborhood ∩
          chapterVIDCenteredConvergentPreparedGerm.branchDomain,
        chapterVIDCenteredConvergentPreparedGerm.inverseSquareRoot point ^ 2 *
          chapterVIDCenteredRadicand point = 1 :=
  chapterVIDCenteredConvergentPreparedGerm.exists_open_inverseSquareRoot_neighborhood

end PoincareChapterVI
