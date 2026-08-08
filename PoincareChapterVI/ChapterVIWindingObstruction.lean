/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import Mathlib.Analysis.Complex.CauchyIntegral
import PoincareChapterVI.ChapterVIPhi

/-!
# The winding obstruction behind Poincaré's admissible pinch

In the planar special case of §97, Poincaré follows the two singular points born at a double
point back to `|z|=1`.  If one ends inside the coefficient circle and the other outside, the
continued contour cannot pass to the double point while avoiding both.  The invariant is the
contour integral of `dt/(t-p)`.

This file supplies that topological implication.  The source-specific root tracking for the
concrete D instance is discharged separately in `ChapterVIDAdmissibility`.
-/

noncomputable section

open Complex Metric Set
open scoped Topology unitInterval

namespace PoincareChapterVI

/-- The normalized winding integral of a closed path about `point`.  Integrality is not needed
for the pinch obstruction; its values `1` and `0` on the unit circle suffice. -/
def chapterVIWindingIntegral
    {a : ℂ} (point : ℂ) (path : Path a a) : ℂ :=
  (2 * Real.pi * Complex.I : ℂ)⁻¹ *
    ∫ᶜ z in path, chapterVIComplexScalarOneForm (fun z ↦ (z - point)⁻¹) z

/-- The positively oriented unit circle has normalized winding integral one about every point
strictly inside it. -/
theorem chapterVIWindingIntegral_unitCircle_eq_one
    {point : ℂ} (hpoint : ‖point‖ < 1) :
    chapterVIWindingIntegral point chapterVIUnitCirclePath = 1 := by
  unfold chapterVIWindingIntegral
  rw [chapterVIUnitCirclePath_curveIntegral_eq_circleIntegral]
  rw [circleIntegral.integral_sub_inv_of_mem_ball]
  · field_simp
  · simpa [mem_ball, dist_zero_left] using hpoint

/-- The same winding integral is zero about a point strictly outside the unit circle. -/
theorem chapterVIWindingIntegral_unitCircle_eq_zero
    {point : ℂ} (hpoint : 1 < ‖point‖) :
    chapterVIWindingIntegral point chapterVIUnitCirclePath = 0 := by
  have hne_closed : ∀ z ∈ closedBall (0 : ℂ) 1, z - point ≠ 0 := by
    intro z hz hzero
    have hzp : z = point := sub_eq_zero.mp hzero
    rw [hzp, mem_closedBall_zero_iff] at hz
    exact (not_lt_of_ge hz) hpoint
  have hcontinuous : ContinuousOn (fun z : ℂ ↦ (z - point)⁻¹)
      (closedBall 0 1) := by
    intro z hz
    exact ((continuousAt_id.sub continuousAt_const).inv₀ (hne_closed z hz)).continuousWithinAt
  have hdifferentiable : ∀ z ∈ ball (0 : ℂ) 1 \ (∅ : Set ℂ),
      DifferentiableAt ℂ (fun z : ℂ ↦ (z - point)⁻¹) z := by
    intro z hz
    have hzclosed : z ∈ closedBall (0 : ℂ) 1 :=
      mem_closedBall_zero_iff.mpr (mem_ball_zero_iff.mp hz.1).le
    exact (differentiableAt_id.sub_const point).inv (hne_closed z hzclosed)
  have hintegral :
      (∮ z in C(0, 1), (z - point)⁻¹) = 0 :=
    circleIntegral_eq_zero_of_differentiable_on_off_countable
      (R := (1 : ℝ)) (c := (0 : ℂ)) zero_le_one countable_empty
      hcontinuous hdifferentiable
  unfold chapterVIWindingIntegral
  rw [chapterVIUnitCirclePath_curveIntegral_eq_circleIntegral, hintegral, mul_zero]

/-- Free closed homotopy cannot change the winding integral while staying in a domain whose
closure avoids the pole.  This is the rigorous contour-separation invariant used in §97. -/
theorem chapterVIWindingIntegral_eq_of_closedHomotopy
    {a b point : ℂ} {initial : Path a a} {final : Path b b}
    {domain : Set ℂ}
    (homotopy : ContinuousMap.Homotopy (initial : C(I, ℂ)) (final : C(I, ℂ)))
    (closed : ∀ s : I, homotopy (s, 0) = homotopy (s, 1))
    (mapsInterior : ∀ s ∈ Ioo (0 : I) 1, ∀ t ∈ Ioo (0 : I) 1,
      homotopy (s, t) ∈ domain)
    (hpole : point ∉ closure domain)
    (hcontDiff : ContDiffOn ℝ 2
      (fun st : ℝ × ℝ ↦
        Set.IccExtend zero_le_one (homotopy.extend st.1) st.2)
      (Icc 0 1)) :
    chapterVIWindingIntegral point initial = chapterVIWindingIntegral point final := by
  have hne_domain : ∀ z ∈ domain, z - point ≠ 0 := by
    intro z hz hzero
    apply hpole
    have hzp : z = point := sub_eq_zero.mp hzero
    rw [← hzp]
    exact subset_closure hz
  have hne_closure : ∀ z ∈ closure domain, z - point ≠ 0 := by
    intro z hz hzero
    apply hpole
    exact (sub_eq_zero.mp hzero) ▸ hz
  have hf : DifferentiableOn ℂ (fun z : ℂ ↦ (z - point)⁻¹) domain := by
    intro z hz
    exact ((differentiableAt_id.sub_const point).inv (hne_domain z hz)).differentiableWithinAt
  have hfClosure : ContinuousOn (fun z : ℂ ↦ (z - point)⁻¹) (closure domain) := by
    intro z hz
    exact ((continuousAt_id.sub continuousAt_const).inv₀
      (hne_closure z hz)).continuousWithinAt
  unfold chapterVIWindingIntegral
  rw [chapterVI_curveIntegral_eq_of_closed_holomorphic_homotopy
    homotopy closed mapsInterior hf hfClosure hcontDiff]

/-- Consequently, loops with distinct winding integrals admit no checked closed homotopy in a
common pole-avoiding domain. -/
theorem chapterVI_not_closedHomotopic_of_windingIntegral_ne
    {a b point : ℂ} {initial : Path a a} {final : Path b b}
    {domain : Set ℂ}
    (hne : chapterVIWindingIntegral point initial ≠
      chapterVIWindingIntegral point final) :
    ¬ ∃ (homotopy : ContinuousMap.Homotopy
        (initial : C(I, ℂ)) (final : C(I, ℂ))),
      (∀ s : I, homotopy (s, 0) = homotopy (s, 1)) ∧
      (∀ s ∈ Ioo (0 : I) 1, ∀ t ∈ Ioo (0 : I) 1,
        homotopy (s, t) ∈ domain) ∧
      point ∉ closure domain ∧
      ContDiffOn ℝ 2
        (fun st : ℝ × ℝ ↦
          Set.IccExtend zero_le_one (homotopy.extend st.1) st.2)
        (Icc 0 1) := by
  rintro ⟨homotopy, hclosed, hmaps, hpole, hsmooth⟩
  exact hne (chapterVIWindingIntegral_eq_of_closedHomotopy
    homotopy hclosed hmaps hpole hsmooth)

/-- Two singular-point lifts that begin on opposite sides of the coefficient contour cannot
coalesce while one closed contour is smoothly transported avoiding both.  In moving-pole
coordinates, the two contour transports end at the same translated loop, whereas their initial
winding integrals are `1` and `0`.

The translated homotopies are explicit arguments because this is the clean trust boundary for a
source application: all analytic branch tracking happens before this theorem, and only the
topological contradiction happens here. -/
theorem chapterVI_no_smooth_contour_avoiding_coalescing_poles
    {insideBase outsideBase finalBase : ℂ}
    {insideInitial : Path insideBase insideBase}
    {outsideInitial : Path outsideBase outsideBase}
    {commonFinal : Path finalBase finalBase}
    (hinside : chapterVIWindingIntegral 0 insideInitial = 1)
    (houtside : chapterVIWindingIntegral 0 outsideInitial = 0) :
    ¬ ∃ (insideDomain outsideDomain : Set ℂ)
        (insideHomotopy : ContinuousMap.Homotopy
          (insideInitial : C(I, ℂ)) (commonFinal : C(I, ℂ)))
        (outsideHomotopy : ContinuousMap.Homotopy
          (outsideInitial : C(I, ℂ)) (commonFinal : C(I, ℂ))),
      (∀ s : I, insideHomotopy (s, 0) = insideHomotopy (s, 1)) ∧
      (∀ s ∈ Ioo (0 : I) 1, ∀ t ∈ Ioo (0 : I) 1,
        insideHomotopy (s, t) ∈ insideDomain) ∧
      (0 : ℂ) ∉ closure insideDomain ∧
      ContDiffOn ℝ 2
        (fun st : ℝ × ℝ ↦
          Set.IccExtend zero_le_one (insideHomotopy.extend st.1) st.2)
        (Icc 0 1) ∧
      (∀ s : I, outsideHomotopy (s, 0) = outsideHomotopy (s, 1)) ∧
      (∀ s ∈ Ioo (0 : I) 1, ∀ t ∈ Ioo (0 : I) 1,
        outsideHomotopy (s, t) ∈ outsideDomain) ∧
      (0 : ℂ) ∉ closure outsideDomain ∧
      ContDiffOn ℝ 2
        (fun st : ℝ × ℝ ↦
          Set.IccExtend zero_le_one (outsideHomotopy.extend st.1) st.2)
        (Icc 0 1) := by
  rintro ⟨insideDomain, outsideDomain, insideHomotopy, outsideHomotopy,
    hiClosed, hiMaps, hiPole, hiSmooth,
    hoClosed, hoMaps, hoPole, hoSmooth⟩
  have hiInvariant := chapterVIWindingIntegral_eq_of_closedHomotopy
    insideHomotopy hiClosed hiMaps hiPole hiSmooth
  have hoInvariant := chapterVIWindingIntegral_eq_of_closedHomotopy
    outsideHomotopy hoClosed hoMaps hoPole hoSmooth
  rw [hinside] at hiInvariant
  rw [houtside] at hoInvariant
  exact one_ne_zero (hiInvariant.trans hoInvariant.symm)

end PoincareChapterVI
