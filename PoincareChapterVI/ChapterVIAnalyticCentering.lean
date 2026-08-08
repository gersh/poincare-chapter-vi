import PoincareChapterVI.ChapterVIAnalyticCriticalCenter
import PoincareChapterVI.ChapterVIComplexBranch
import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
# Centering the exact Chapter VI radicand

This file makes the analytic critical center through D into a named germ and translates the exact
source radicand into coordinates centered on it.  The resulting germ is analytic, vanishes on the
entire parameter axis, has zero first fiber derivative along that axis near D, and has nonzero
second fiber derivative at D.

Thus the remaining convergent-preparation problem is no longer hidden inside a pointwise jet: it
is precisely analytic division of this centered germ by the square of its second coordinate.
-/

open Filter
open scoped Topology

namespace PoincareChapterVI

/-- A fixed analytic choice of Poincaré's moving critical center through D. -/
noncomputable def chapterVIDCriticalCenter : ℂ → ℂ :=
  Classical.choose exists_chapterVID_analyticCriticalCenter

/-- All properties of the chosen critical center, collected in the form supplied by the complex
implicit function theorem. -/
theorem chapterVIDCriticalCenter_spec :
    chapterVIDCriticalCenter chapterVIDZBase = chapterVIDTBase ∧
      AnalyticAt ℂ chapterVIDCriticalCenter chapterVIDZBase ∧
      (∀ᶠ z in nhds chapterVIDZBase,
        chapterVIFiberDerivative chapterVIDRadicand (z, chapterVIDCriticalCenter z) = 0) ∧
      (∀ᶠ z in nhds chapterVIDZBase,
        deriv (fun t ↦ chapterVIDRadicand (z, t)) (chapterVIDCriticalCenter z) = 0) :=
  Classical.choose_spec exists_chapterVID_analyticCriticalCenter

@[simp]
theorem chapterVIDCriticalCenter_base :
    chapterVIDCriticalCenter chapterVIDZBase = chapterVIDTBase :=
  chapterVIDCriticalCenter_spec.1

theorem analyticAt_chapterVIDCriticalCenter :
    AnalyticAt ℂ chapterVIDCriticalCenter chapterVIDZBase :=
  chapterVIDCriticalCenter_spec.2.1

theorem eventually_chapterVIDCriticalCenter_fiberDerivative_eq_zero :
    ∀ᶠ z in nhds chapterVIDZBase,
      chapterVIFiberDerivative chapterVIDRadicand (z, chapterVIDCriticalCenter z) = 0 :=
  chapterVIDCriticalCenter_spec.2.2.1

theorem eventually_deriv_chapterVIDRadicand_criticalCenter_eq_zero :
    ∀ᶠ z in nhds chapterVIDZBase,
      deriv (fun t ↦ chapterVIDRadicand (z, t)) (chapterVIDCriticalCenter z) = 0 :=
  chapterVIDCriticalCenter_spec.2.2.2

/-- The value of the radicand at its moving fiber-critical point. -/
noncomputable def chapterVIDCriticalValue (z : ℂ) : ℂ :=
  chapterVIDRadicand (z, chapterVIDCriticalCenter z)

/-- The moving critical value is a genuinely analytic parameter germ. -/
theorem analyticAt_chapterVIDCriticalValue :
    AnalyticAt ℂ chapterVIDCriticalValue chapterVIDZBase := by
  have hpair : AnalyticAt ℂ
      (fun z ↦ (z, chapterVIDCriticalCenter z)) chapterVIDZBase :=
    analyticAt_id.prod analyticAt_chapterVIDCriticalCenter
  have hcomp := analyticAt_chapterVIDRadicand.comp_of_eq hpair (by
    simp only [chapterVIDCriticalCenter_base])
  change AnalyticAt ℂ
    (fun z ↦ chapterVIDRadicand (z, chapterVIDCriticalCenter z)) chapterVIDZBase
  simpa only [Function.comp_def] using hcomp

/-- The critical value vanishes at the certified double point D. -/
@[simp]
theorem chapterVIDCriticalValue_base :
    chapterVIDCriticalValue chapterVIDZBase = 0 := by
  have hfiber : AnalyticAt ℂ
      (fun w ↦ chapterVIDRadicand (chapterVIDZBase, w)) chapterVIDTBase :=
    analyticAt_chapterVIDRadicand.comp (analyticAt_const.prod analyticAt_id)
  have hjet := (analyticOrderAt_eq_two_iff hfiber).mp
    analyticOrderAt_chapterVIDPoincareRadicand_eq_two
  simpa only [chapterVIDCriticalValue, chapterVIDCriticalCenter_base] using hjet.1

/-- The exact source radicand in a fiber coordinate centered at its analytic critical point, with
the moving critical value subtracted. -/
noncomputable def chapterVIDCenteredRadicand (point : ℂ × ℂ) : ℂ :=
  chapterVIDRadicand
      (point.1, chapterVIDCriticalCenter point.1 + point.2) -
    chapterVIDCriticalValue point.1

/-- The centered source radicand is a convergent analytic two-variable germ at `(z_D,0)`. -/
theorem analyticAt_chapterVIDCenteredRadicand :
    AnalyticAt ℂ chapterVIDCenteredRadicand (chapterVIDZBase, 0) := by
  have hcenterComp : AnalyticAt ℂ
      (fun point : ℂ × ℂ ↦ chapterVIDCriticalCenter point.1) (chapterVIDZBase, 0) := by
    have hfst : AnalyticAt ℂ (fun point : ℂ × ℂ ↦ point.1) (chapterVIDZBase, 0) :=
      analyticAt_fst
    simpa only [Function.comp_def] using
      analyticAt_chapterVIDCriticalCenter.comp_of_eq hfst rfl
  have hshift : AnalyticAt ℂ
      (fun point : ℂ × ℂ ↦
        (point.1, chapterVIDCriticalCenter point.1 + point.2))
      (chapterVIDZBase, 0) :=
    analyticAt_fst.prod (hcenterComp.add analyticAt_snd)
  have hradicand := analyticAt_chapterVIDRadicand.comp_of_eq hshift (by
    simp only [chapterVIDCriticalCenter_base, add_zero])
  have hvalue : AnalyticAt ℂ
      (fun point : ℂ × ℂ ↦ chapterVIDCriticalValue point.1) (chapterVIDZBase, 0) := by
    have hfst : AnalyticAt ℂ (fun point : ℂ × ℂ ↦ point.1) (chapterVIDZBase, 0) :=
      analyticAt_fst
    simpa only [Function.comp_def] using
      analyticAt_chapterVIDCriticalValue.comp_of_eq hfst rfl
  unfold chapterVIDCenteredRadicand
  convert hradicand.sub hvalue using 1
  funext point
  rfl

/-- A complete convergent power series represents the centered radicand; this is stronger than
any finite jet certificate. -/
theorem exists_hasFPowerSeriesAt_chapterVIDCenteredRadicand :
    ∃ series : FormalMultilinearSeries ℂ (ℂ × ℂ) ℂ,
      HasFPowerSeriesAt chapterVIDCenteredRadicand series (chapterVIDZBase, 0) :=
  analyticAt_chapterVIDCenteredRadicand

/-- Centering and subtracting the critical value makes the whole parameter axis vanish exactly,
not merely to finite order at D. -/
@[simp]
theorem chapterVIDCenteredRadicand_axis_eq_zero (z : ℂ) :
    chapterVIDCenteredRadicand (z, 0) = 0 := by
  simp [chapterVIDCenteredRadicand, chapterVIDCriticalValue]

/-- The first derivative in the centered fiber coordinate vanishes along the parameter axis on
a neighborhood of D. -/
theorem eventually_deriv_chapterVIDCenteredRadicand_axis_eq_zero :
    ∀ᶠ z in nhds chapterVIDZBase,
      deriv (fun u ↦ chapterVIDCenteredRadicand (z, u)) 0 = 0 := by
  filter_upwards [eventually_deriv_chapterVIDRadicand_criticalCenter_eq_zero] with z hz
  unfold chapterVIDCenteredRadicand
  simp only
  rw [deriv_sub_const,
    deriv_comp_const_add (fun w ↦ chapterVIDRadicand (z, w))
      (chapterVIDCriticalCenter z) 0, add_zero]
  exact hz

/-- At D, the centered fiber has zero first derivative. -/
theorem deriv_chapterVIDCenteredRadicand_eq_zero :
    deriv (fun u ↦ chapterVIDCenteredRadicand (chapterVIDZBase, u)) 0 = 0 := by
  have hfiber : AnalyticAt ℂ
      (fun w ↦ chapterVIDRadicand (chapterVIDZBase, w)) chapterVIDTBase :=
    analyticAt_chapterVIDRadicand.comp (analyticAt_const.prod analyticAt_id)
  have hjet := (analyticOrderAt_eq_two_iff hfiber).mp
    analyticOrderAt_chapterVIDPoincareRadicand_eq_two
  unfold chapterVIDCenteredRadicand
  simp only [chapterVIDCriticalCenter_base]
  change deriv (fun u ↦
    chapterVIDRadicand (chapterVIDZBase, chapterVIDTBase + u) -
      chapterVIDCriticalValue chapterVIDZBase) 0 = 0
  rw [deriv_sub_const,
    deriv_comp_const_add (fun w ↦ chapterVIDRadicand (chapterVIDZBase, w))
      chapterVIDTBase 0, add_zero]
  exact hjet.2.1

/-- At D, the centered fiber still has nonzero second derivative. -/
theorem deriv_deriv_chapterVIDCenteredRadicand_ne_zero :
    deriv (deriv (fun u ↦ chapterVIDCenteredRadicand (chapterVIDZBase, u))) 0 ≠ 0 := by
  have hfiber : AnalyticAt ℂ
      (fun w ↦ chapterVIDRadicand (chapterVIDZBase, w)) chapterVIDTBase :=
    analyticAt_chapterVIDRadicand.comp (analyticAt_const.prod analyticAt_id)
  have hjet := (analyticOrderAt_eq_two_iff hfiber).mp
    analyticOrderAt_chapterVIDPoincareRadicand_eq_two
  unfold chapterVIDCenteredRadicand
  simp only [chapterVIDCriticalCenter_base]
  change deriv (deriv (fun u ↦
    chapterVIDRadicand (chapterVIDZBase, chapterVIDTBase + u) -
      chapterVIDCriticalValue chapterVIDZBase)) 0 ≠ 0
  have hinner : deriv (fun u ↦
      chapterVIDRadicand (chapterVIDZBase, chapterVIDTBase + u) -
        chapterVIDCriticalValue chapterVIDZBase) =
      fun u ↦ deriv (fun w ↦ chapterVIDRadicand (chapterVIDZBase, w))
        (chapterVIDTBase + u) := by
    funext u
    rw [deriv_sub_const,
      deriv_comp_const_add (fun w ↦ chapterVIDRadicand (chapterVIDZBase, w))
        chapterVIDTBase u]
  rw [hinner,
    deriv_comp_const_add (deriv (fun w ↦ chapterVIDRadicand (chapterVIDZBase, w)))
      chapterVIDTBase 0, add_zero]
  exact hjet.2.2

/-- The centered convergent germ has exact fiber order two at the origin. -/
theorem analyticOrderAt_chapterVIDCenteredRadicand_eq_two :
    analyticOrderAt
      (fun u ↦ chapterVIDCenteredRadicand (chapterVIDZBase, u)) 0 = 2 := by
  have hfiber : AnalyticAt ℂ
      (fun u ↦ chapterVIDCenteredRadicand (chapterVIDZBase, u)) 0 :=
    analyticAt_chapterVIDCenteredRadicand.comp (analyticAt_const.prod analyticAt_id)
  exact (analyticOrderAt_eq_two_iff hfiber).mpr
    ⟨chapterVIDCenteredRadicand_axis_eq_zero chapterVIDZBase,
      deriv_chapterVIDCenteredRadicand_eq_zero,
      deriv_deriv_chapterVIDCenteredRadicand_ne_zero⟩

/-! ## Convergent square division on the singular fiber -/

/-- On the singular fiber itself, analytic order two supplies an actual convergent unit factor,
not merely a formal or finite-jet quotient. -/
theorem exists_chapterVIDCenteredFiberUnit :
    ∃ unit : ℂ → ℂ,
      AnalyticAt ℂ unit 0 ∧ unit 0 ≠ 0 ∧
        ∀ᶠ u in nhds 0,
          chapterVIDCenteredRadicand (chapterVIDZBase, u) = u ^ 2 * unit u := by
  have hfiber : AnalyticAt ℂ
      (fun u ↦ chapterVIDCenteredRadicand (chapterVIDZBase, u)) 0 :=
    analyticAt_chapterVIDCenteredRadicand.comp (analyticAt_const.prod analyticAt_id)
  simpa only [sub_zero, smul_eq_mul] using
    (hfiber.analyticOrderAt_eq_natCast (n := 2)).mp
      analyticOrderAt_chapterVIDCenteredRadicand_eq_two

/-- A fixed convergent choice of the nonvanishing unit in the singular-fiber square division. -/
noncomputable def chapterVIDCenteredFiberUnit : ℂ → ℂ :=
  Classical.choose exists_chapterVIDCenteredFiberUnit

theorem analyticAt_chapterVIDCenteredFiberUnit :
    AnalyticAt ℂ chapterVIDCenteredFiberUnit 0 :=
  (Classical.choose_spec exists_chapterVIDCenteredFiberUnit).1

@[simp]
theorem chapterVIDCenteredFiberUnit_zero_ne :
    chapterVIDCenteredFiberUnit 0 ≠ 0 :=
  (Classical.choose_spec exists_chapterVIDCenteredFiberUnit).2.1

/-- The convergent factorization by `u²` holds on an actual neighborhood of the pinch. -/
theorem eventually_chapterVIDCenteredRadicand_eq_sq_mul_fiberUnit :
    ∀ᶠ u in nhds 0,
      chapterVIDCenteredRadicand (chapterVIDZBase, u) =
        u ^ 2 * chapterVIDCenteredFiberUnit u :=
  (Classical.choose_spec exists_chapterVIDCenteredFiberUnit).2.2

/-- The singular-fiber unit remains nonzero throughout a neighborhood of the pinch. -/
theorem eventually_chapterVIDCenteredFiberUnit_ne_zero :
    ∀ᶠ u in nhds 0, chapterVIDCenteredFiberUnit u ≠ 0 :=
  analyticAt_chapterVIDCenteredFiberUnit.continuousAt.eventually_ne
    chapterVIDCenteredFiberUnit_zero_ne

/-! ## Fiberwise preparation near D -/

/-- The complete centered radicand remains analytic at `(z,0)` for every nearby parameter. -/
theorem eventually_analyticAt_chapterVIDCenteredRadicand_axis :
    ∀ᶠ z in nhds chapterVIDZBase,
      AnalyticAt ℂ chapterVIDCenteredRadicand (z, 0) := by
  have haxis : Tendsto (fun z : ℂ ↦ (z, (0 : ℂ)))
      (nhds chapterVIDZBase) (nhds (chapterVIDZBase, (0 : ℂ))) :=
    continuousAt_id.prodMk continuousAt_const
  exact haxis.eventually analyticAt_chapterVIDCenteredRadicand.eventually_analyticAt

/-- The second fiber derivative stays nonzero along the centered parameter axis near D. -/
theorem eventually_chapterVISecondFiberDerivative_centered_axis_ne_zero :
    ∀ᶠ z in nhds chapterVIDZBase,
      chapterVISecondFiberDerivative chapterVIDCenteredRadicand (z, 0) ≠ 0 := by
  have hsecondAnalytic :=
    analyticAt_chapterVISecondFiberDerivative analyticAt_chapterVIDCenteredRadicand
  have hsecondBase :
      chapterVISecondFiberDerivative chapterVIDCenteredRadicand
        (chapterVIDZBase, 0) ≠ 0 := by
    rw [chapterVISecondFiberDerivative_eq_deriv_deriv
      analyticAt_chapterVIDCenteredRadicand]
    exact deriv_deriv_chapterVIDCenteredRadicand_ne_zero
  have hsecondEventually := hsecondAnalytic.continuousAt.eventually_ne hsecondBase
  have haxis : Tendsto (fun z : ℂ ↦ (z, (0 : ℂ)))
      (nhds chapterVIDZBase) (nhds (chapterVIDZBase, (0 : ℂ))) :=
    continuousAt_id.prodMk continuousAt_const
  exact haxis.eventually hsecondEventually

/-- Every sufficiently nearby centered fiber has analytic order exactly two at its critical
point. -/
theorem eventually_analyticOrderAt_chapterVIDCenteredRadicand_axis_eq_two :
    ∀ᶠ z in nhds chapterVIDZBase,
      analyticOrderAt (fun u ↦ chapterVIDCenteredRadicand (z, u)) 0 = 2 := by
  filter_upwards [eventually_analyticAt_chapterVIDCenteredRadicand_axis,
    eventually_deriv_chapterVIDCenteredRadicand_axis_eq_zero,
    eventually_chapterVISecondFiberDerivative_centered_axis_ne_zero]
      with z hzAnalytic hzFirst hzSecond
  have hfiber : AnalyticAt ℂ (fun u ↦ chapterVIDCenteredRadicand (z, u)) 0 :=
    hzAnalytic.curry_right
  apply (analyticOrderAt_eq_two_iff hfiber).mpr
  refine ⟨chapterVIDCenteredRadicand_axis_eq_zero z, hzFirst, ?_⟩
  rw [← chapterVISecondFiberDerivative_eq_deriv_deriv hzAnalytic]
  exact hzSecond

/-- Consequently every nearby parameter fiber admits a convergent square division by a
nonvanishing one-variable analytic unit.  The remaining Weierstrass problem is to choose these
units *jointly analytically* in the parameter. -/
theorem eventually_exists_chapterVIDCenteredFiberUnit :
    ∀ᶠ z in nhds chapterVIDZBase,
      ∃ unit : ℂ → ℂ,
        AnalyticAt ℂ unit 0 ∧ unit 0 ≠ 0 ∧
          ∀ᶠ u in nhds 0,
            chapterVIDCenteredRadicand (z, u) = u ^ 2 * unit u := by
  filter_upwards [eventually_analyticAt_chapterVIDCenteredRadicand_axis,
    eventually_analyticOrderAt_chapterVIDCenteredRadicand_axis_eq_two]
      with z hzAnalytic hzOrder
  have hfiber : AnalyticAt ℂ (fun u ↦ chapterVIDCenteredRadicand (z, u)) 0 :=
    hzAnalytic.curry_right
  simpa only [sub_zero, smul_eq_mul] using
    (hfiber.analyticOrderAt_eq_natCast (n := 2)).mp hzOrder

/-! ## The actual inverse-square-root branch on the singular fiber -/

/-- A locally chosen holomorphic square root of the convergent singular-fiber unit. -/
noncomputable def chapterVIDCenteredFiberUnitRootGerm :
    ChapterVIHolomorphicSquareRootGerm chapterVIDCenteredFiberUnit 0 :=
  ChapterVIHolomorphicSquareRootGerm.of_analyticAt
    analyticAt_chapterVIDCenteredFiberUnit chapterVIDCenteredFiberUnit_zero_ne

/-- The square-root branch `u √U(u)` of the actual centered radicand on the singular fiber. -/
noncomputable def chapterVIDCenteredFiberSquareRoot (u : ℂ) : ℂ :=
  u * chapterVIDCenteredFiberUnitRootGerm.root u

/-- The corresponding inverse-square-root branch. -/
noncomputable def chapterVIDCenteredFiberInverseSquareRoot (u : ℂ) : ℂ :=
  (chapterVIDCenteredFiberSquareRoot u)⁻¹

/-- The square-root branch is holomorphic on the unit-root germ's domain. -/
theorem differentiableOn_chapterVIDCenteredFiberSquareRoot :
    DifferentiableOn ℂ chapterVIDCenteredFiberSquareRoot
      chapterVIDCenteredFiberUnitRootGerm.domain := by
  intro u hu
  exact differentiableAt_id.differentiableWithinAt.mul
    (chapterVIDCenteredFiberUnitRootGerm.differentiableOn_root u hu)

/-- The inverse branch is holomorphic off the pinching point. -/
theorem differentiableOn_chapterVIDCenteredFiberInverseSquareRoot :
    DifferentiableOn ℂ chapterVIDCenteredFiberInverseSquareRoot
      ({0}ᶜ ∩ chapterVIDCenteredFiberUnitRootGerm.domain) := by
  apply (differentiableOn_chapterVIDCenteredFiberSquareRoot.mono Set.inter_subset_right).inv
  intro u hu
  exact mul_ne_zero hu.1
    (chapterVIDCenteredFiberUnitRootGerm.root_ne_zero u hu.2)

/-- Wherever the convergent factorization holds, the constructed square root squares to the
*actual* centered source radicand. -/
theorem chapterVIDCenteredFiberSquareRoot_sq_eq
    {u : ℂ}
    (hfactor : chapterVIDCenteredRadicand (chapterVIDZBase, u) =
      u ^ 2 * chapterVIDCenteredFiberUnit u)
    (hroot : u ∈ chapterVIDCenteredFiberUnitRootGerm.domain) :
    chapterVIDCenteredFiberSquareRoot u ^ 2 =
      chapterVIDCenteredRadicand (chapterVIDZBase, u) := by
  rw [chapterVIDCenteredFiberSquareRoot, mul_pow,
    chapterVIDCenteredFiberUnitRootGerm.root_sq u hroot, hfactor]

/-- Algebraic correctness of the inverse branch for the actual radicand. -/
theorem chapterVIDCenteredFiberInverseSquareRoot_sq_mul
    {u : ℂ} (hu : u ≠ 0)
    (hfactor : chapterVIDCenteredRadicand (chapterVIDZBase, u) =
      u ^ 2 * chapterVIDCenteredFiberUnit u)
    (hroot : u ∈ chapterVIDCenteredFiberUnitRootGerm.domain) :
    chapterVIDCenteredFiberInverseSquareRoot u ^ 2 *
      chapterVIDCenteredRadicand (chapterVIDZBase, u) = 1 := by
  rw [← chapterVIDCenteredFiberSquareRoot_sq_eq hfactor hroot]
  have hsquareRoot : chapterVIDCenteredFiberSquareRoot u ≠ 0 :=
    mul_ne_zero hu (chapterVIDCenteredFiberUnitRootGerm.root_ne_zero u hroot)
  simp [chapterVIDCenteredFiberInverseSquareRoot, hsquareRoot]

/-- On an actual punctured neighborhood of the pinch, the holomorphic inverse branch squares
against the exact centered source radicand to one. -/
theorem eventually_chapterVIDCenteredFiberInverseSquareRoot_sq_mul :
    ∀ᶠ u in nhdsWithin (0 : ℂ) ({0}ᶜ : Set ℂ),
      chapterVIDCenteredFiberInverseSquareRoot u ^ 2 *
        chapterVIDCenteredRadicand (chapterVIDZBase, u) = 1 := by
  have hroot : ∀ᶠ u in nhds (0 : ℂ),
      u ∈ chapterVIDCenteredFiberUnitRootGerm.domain :=
    chapterVIDCenteredFiberUnitRootGerm.isOpen_domain.mem_nhds
      chapterVIDCenteredFiberUnitRootGerm.base_mem
  filter_upwards [self_mem_nhdsWithin,
    eventually_chapterVIDCenteredRadicand_eq_sq_mul_fiberUnit.filter_mono nhdsWithin_le_nhds,
    hroot.filter_mono nhdsWithin_le_nhds] with u hu hfactor huRoot
  exact chapterVIDCenteredFiberInverseSquareRoot_sq_mul hu hfactor huRoot

/-! ## Simple-pole decomposition on the singular fiber -/

/-- The analytic amplitude multiplying `1/u` in the singular-fiber inverse branch. -/
noncomputable def chapterVIDCenteredFiberAmplitude (u : ℂ) : ℂ :=
  (chapterVIDCenteredFiberUnitRootGerm.root u)⁻¹

/-- The chosen unit root is analytic at the pinch. -/
theorem analyticAt_chapterVIDCenteredFiberUnitRoot :
    AnalyticAt ℂ chapterVIDCenteredFiberUnitRootGerm.root 0 := by
  apply DifferentiableOn.analyticAt
    chapterVIDCenteredFiberUnitRootGerm.differentiableOn_root
  exact chapterVIDCenteredFiberUnitRootGerm.isOpen_domain.mem_nhds
    chapterVIDCenteredFiberUnitRootGerm.base_mem

/-- The pole amplitude is analytic and nonzero at the pinch. -/
theorem analyticAt_chapterVIDCenteredFiberAmplitude :
    AnalyticAt ℂ chapterVIDCenteredFiberAmplitude 0 := by
  exact analyticAt_chapterVIDCenteredFiberUnitRoot.inv
    (chapterVIDCenteredFiberUnitRootGerm.root_ne_zero 0
      chapterVIDCenteredFiberUnitRootGerm.base_mem)

@[simp]
theorem chapterVIDCenteredFiberAmplitude_zero_ne :
    chapterVIDCenteredFiberAmplitude 0 ≠ 0 := by
  exact inv_ne_zero
    (chapterVIDCenteredFiberUnitRootGerm.root_ne_zero 0
      chapterVIDCenteredFiberUnitRootGerm.base_mem)

/-- The removable divided difference of the pole amplitude. -/
noncomputable def chapterVIDCenteredFiberRegular (u : ℂ) : ℂ :=
  dslope chapterVIDCenteredFiberAmplitude 0 u

/-- Removing the constant term from the amplitude leaves an analytic regular factor. -/
theorem analyticAt_chapterVIDCenteredFiberRegular :
    AnalyticAt ℂ chapterVIDCenteredFiberRegular 0 := by
  rcases analyticAt_chapterVIDCenteredFiberAmplitude with ⟨series, hseries⟩
  exact ⟨series.fslope, hseries.has_fpower_series_dslope_fslope⟩

/-- Exact first-order decomposition of the analytic amplitude. -/
theorem chapterVIDCenteredFiberAmplitude_eq (u : ℂ) :
    chapterVIDCenteredFiberAmplitude u =
      chapterVIDCenteredFiberAmplitude 0 + u * chapterVIDCenteredFiberRegular u := by
  have hslope := sub_smul_dslope chapterVIDCenteredFiberAmplitude 0 u
  have hslope' : u * chapterVIDCenteredFiberRegular u =
      chapterVIDCenteredFiberAmplitude u - chapterVIDCenteredFiberAmplitude 0 := by
    simpa [chapterVIDCenteredFiberRegular, sub_zero, smul_eq_mul] using hslope
  calc
    chapterVIDCenteredFiberAmplitude u =
        (chapterVIDCenteredFiberAmplitude u - chapterVIDCenteredFiberAmplitude 0) +
          chapterVIDCenteredFiberAmplitude 0 := by ring
    _ = u * chapterVIDCenteredFiberRegular u +
          chapterVIDCenteredFiberAmplitude 0 := by rw [← hslope']
    _ = chapterVIDCenteredFiberAmplitude 0 +
          u * chapterVIDCenteredFiberRegular u := by ring

/-- The actual inverse-square-root branch is a nonzero simple pole plus a regular analytic
function.  This is the local function-level precursor of Poincaré's logarithmic contour term. -/
theorem chapterVIDCenteredFiberInverseSquareRoot_eq_pole_add_regular
    {u : ℂ} (hu : u ≠ 0) :
    chapterVIDCenteredFiberInverseSquareRoot u =
      chapterVIDCenteredFiberAmplitude 0 / u + chapterVIDCenteredFiberRegular u := by
  calc
    chapterVIDCenteredFiberInverseSquareRoot u =
        u⁻¹ * chapterVIDCenteredFiberAmplitude u := by
      simp [chapterVIDCenteredFiberInverseSquareRoot,
        chapterVIDCenteredFiberSquareRoot, chapterVIDCenteredFiberAmplitude, mul_inv_rev,
        mul_comm]
    _ = u⁻¹ * (chapterVIDCenteredFiberAmplitude 0 +
          u * chapterVIDCenteredFiberRegular u) := by
      rw [chapterVIDCenteredFiberAmplitude_eq]
    _ = chapterVIDCenteredFiberAmplitude 0 / u +
          chapterVIDCenteredFiberRegular u := by
      field_simp [hu]

/-- The simple-pole decomposition holds throughout a punctured neighborhood of the pinch. -/
theorem eventually_chapterVIDCenteredFiberInverseSquareRoot_eq_pole_add_regular :
    ∀ᶠ u in nhdsWithin (0 : ℂ) ({0}ᶜ : Set ℂ),
      chapterVIDCenteredFiberInverseSquareRoot u =
        chapterVIDCenteredFiberAmplitude 0 / u + chapterVIDCenteredFiberRegular u := by
  filter_upwards [self_mem_nhdsWithin] with u hu
  exact chapterVIDCenteredFiberInverseSquareRoot_eq_pole_add_regular hu

end PoincareChapterVI
