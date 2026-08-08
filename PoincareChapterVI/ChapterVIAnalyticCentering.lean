import PoincareChapterVI.ChapterVIAnalyticCriticalCenter
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

end PoincareChapterVI
