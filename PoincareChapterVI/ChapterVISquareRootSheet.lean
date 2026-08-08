/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Homotopy.Contractible

/-!
# Continuous square-root sheets and finite nonvanishing certificates

Poincare's global continuation requires a compatible square root of the source radicand on each
outer-arc parameter rectangle.  The analytic-topological part is general: a continuous nonzero
complex function on a simply connected, locally path-connected space has a continuous square
root, uniquely fixed after choosing its value at one base point.  This file obtains that root by
lifting through the covering map `w -> w^2`.

The remaining source-specific task is proving that the radicand is nonzero on the compact
rectangles.  `ChapterVIFiniteNonvanishingCover` gives the exact interface for a compiled
LeanCompCert certificate: finitely many sample lower bounds plus a certified cover and a global
Lipschitz bound imply nonvanishing everywhere.  The compiled computation can discharge the large
finite sample table; the cover, Lipschitz estimate, and final continuum argument remain ordinary
kernel-checked Lean mathematics.
-/

noncomputable section

open Set Topology

namespace PoincareChapterVI

/-- A continuous square-root sheet of a complex-valued function. -/
structure ChapterVIContinuousSquareRootSheet
    {A : Type*} [TopologicalSpace A] (radicand : A → ℂ) where
  root : A → ℂ
  continuous_root : Continuous root
  root_sq : ∀ x, root x ^ 2 = radicand x

namespace ChapterVIContinuousSquareRootSheet

theorem root_ne_zero
    {A : Type*} [TopologicalSpace A] {radicand : A → ℂ}
    (sheet : ChapterVIContinuousSquareRootSheet radicand)
    {x : A} (hrad : radicand x ≠ 0) :
    sheet.root x ≠ 0 := by
  intro hzero
  apply hrad
  rw [← sheet.root_sq x, hzero]
  norm_num

end ChapterVIContinuousSquareRootSheet

/-- A base-point-normalized continuous square-root sheet exists on any simply connected,
locally path-connected parameter space, as soon as the radicand is continuous and nonzero. -/
theorem exists_chapterVIContinuousSquareRootSheet
    {A : Type*} [TopologicalSpace A] [SimplyConnectedSpace A]
    [LocallyPathConnectedSpace A]
    (radicand : A → ℂ) (hcontinuous : Continuous radicand)
    (hnonzero : ∀ x, radicand x ≠ 0)
    (base : A) (baseRoot : ℂ) (hbaseRoot : baseRoot ^ 2 = radicand base) :
    ∃ sheet : ChapterVIContinuousSquareRootSheet radicand,
      sheet.root base = baseRoot := by
  let radicandMap : C(A, ℂ) := ⟨radicand, hcontinuous⟩
  obtain ⟨rootMap, hrootMap, _⟩ :=
    (isCoveringMapOn_npow 2 (by norm_num : (2 : ℂ) ≠ 0)).existsUnique_continuousMap_lifts
      radicandMap hbaseRoot (by
        intro x
        change radicand x ≠ 0
        exact hnonzero x)
  exact ⟨{
    root := rootMap
    continuous_root := rootMap.continuous
    root_sq := fun x ↦ congrFun hrootMap.2 x }, hrootMap.1⟩

/-- Finite-cover data sufficient to turn finitely many checked sample values into a rigorous
nonvanishing statement on an entire parameter space.  `sampleNorm` is the part intended for a
compiled certificate when the sample set is large. -/
structure ChapterVIFiniteNonvanishingCover
    {A : Type*} [PseudoMetricSpace A] (radicand : A → ℂ) where
  samples : Finset A
  coverRadius : ℝ
  lipschitzConstant : NNReal
  sampleMargin : ℝ
  coverRadius_nonneg : 0 ≤ coverRadius
  sampleMargin_pos : 0 < sampleMargin
  covers : ∀ x : A, ∃ center ∈ samples, dist x center ≤ coverRadius
  lipschitz : LipschitzWith lipschitzConstant radicand
  sampleNorm : ∀ center ∈ samples, sampleMargin ≤ ‖radicand center‖
  error_lt_margin : (lipschitzConstant : ℝ) * coverRadius < sampleMargin

/-- A stronger and cheaper certificate specialized to functions whose real part stays positive
at the samples.  Its finite field is an ordered real comparison, so the compiled artifact need
not compute a complex norm or square components. -/
structure ChapterVIFinitePositiveRealPartCover
    {A : Type*} [PseudoMetricSpace A] (radicand : A → ℂ) where
  samples : Finset A
  coverRadius : ℝ
  lipschitzConstant : NNReal
  sampleMargin : ℝ
  coverRadius_nonneg : 0 ≤ coverRadius
  sampleMargin_pos : 0 < sampleMargin
  covers : ∀ x : A, ∃ center ∈ samples, dist x center ≤ coverRadius
  lipschitz : LipschitzWith lipschitzConstant radicand
  sampleRealPart : ∀ center ∈ samples, sampleMargin ≤ (radicand center).re
  error_lt_margin : (lipschitzConstant : ℝ) * coverRadius < sampleMargin

/-- A finite interval-box variant of the positive-real-part certificate.  Unlike a point-sample
certificate, each compiled row encloses the radicand on an entire cell.  This removes the need for
a separate global Lipschitz estimate when the interval evaluator already propagates input ranges. -/
structure ChapterVIFinitePositiveRealPartIndexedCover
    {A Cell : Type*} [Fintype Cell] (region : Cell → Set A)
    (radicand : A → ℂ) where
  margin : ℝ
  margin_pos : 0 < margin
  covers : ∀ x : A, ∃ cell : Cell, x ∈ region cell
  cellRealPart : ∀ cell : Cell, ∀ x ∈ region cell, margin ≤ (radicand x).re

theorem ChapterVIFinitePositiveRealPartIndexedCover.realPart_pos
    {A Cell : Type*} [Fintype Cell] {region : Cell → Set A}
    {radicand : A → ℂ}
    (certificate : ChapterVIFinitePositiveRealPartIndexedCover region radicand)
    (x : A) : 0 < (radicand x).re := by
  obtain ⟨cell, hx⟩ := certificate.covers x
  exact certificate.margin_pos.trans_le (certificate.cellRealPart cell x hx)

theorem ChapterVIFinitePositiveRealPartIndexedCover.ne_zero
    {A Cell : Type*} [Fintype Cell] {region : Cell → Set A}
    {radicand : A → ℂ}
    (certificate : ChapterVIFinitePositiveRealPartIndexedCover region radicand)
    (x : A) : radicand x ≠ 0 := by
  intro hzero
  have := certificate.realPart_pos x
  simp [hzero] at this

/-- An interval-box certificate can feed the same covering-space square-root construction without
passing through point samples or a Lipschitz estimate. -/
theorem ChapterVIFinitePositiveRealPartIndexedCover.exists_continuousSquareRootSheet
    {A Cell : Type*} [TopologicalSpace A] [Fintype Cell]
    [SimplyConnectedSpace A] [LocallyPathConnectedSpace A]
    {region : Cell → Set A} {radicand : A → ℂ}
    (certificate : ChapterVIFinitePositiveRealPartIndexedCover region radicand)
    (hcontinuous : Continuous radicand)
    (base : A) (baseRoot : ℂ) (hbaseRoot : baseRoot ^ 2 = radicand base) :
    ∃ sheet : ChapterVIContinuousSquareRootSheet radicand,
      sheet.root base = baseRoot :=
  exists_chapterVIContinuousSquareRootSheet radicand hcontinuous
    certificate.ne_zero base baseRoot hbaseRoot

/-- Forgetting the stronger positive-real-part information gives the general finite
nonvanishing certificate. -/
def ChapterVIFinitePositiveRealPartCover.toNonvanishingCover
    {A : Type*} [PseudoMetricSpace A] {radicand : A → ℂ}
    (certificate : ChapterVIFinitePositiveRealPartCover radicand) :
    ChapterVIFiniteNonvanishingCover radicand where
  samples := certificate.samples
  coverRadius := certificate.coverRadius
  lipschitzConstant := certificate.lipschitzConstant
  sampleMargin := certificate.sampleMargin
  coverRadius_nonneg := certificate.coverRadius_nonneg
  sampleMargin_pos := certificate.sampleMargin_pos
  covers := certificate.covers
  lipschitz := certificate.lipschitz
  sampleNorm center hcenter :=
    (certificate.sampleRealPart center hcenter).trans (Complex.re_le_norm _)
  error_lt_margin := certificate.error_lt_margin

/-- The finite-cover certificate proves that the source function cannot vanish between sample
points.  This is the continuum bridge that a compiled finite computation must not silently
assume. -/
theorem ChapterVIFiniteNonvanishingCover.ne_zero
    {A : Type*} [PseudoMetricSpace A] {radicand : A → ℂ}
    (certificate : ChapterVIFiniteNonvanishingCover radicand) (x : A) :
    radicand x ≠ 0 := by
  intro hzero
  obtain ⟨center, hcenter, hdist⟩ := certificate.covers x
  have hlip := certificate.lipschitz.dist_le_mul x center
  have hmargin : certificate.sampleMargin ≤
      (certificate.lipschitzConstant : ℝ) * certificate.coverRadius := by
    calc
      certificate.sampleMargin ≤ ‖radicand center‖ :=
        certificate.sampleNorm center hcenter
      _ = dist (radicand x) (radicand center) := by simp [hzero]
      _ ≤ (certificate.lipschitzConstant : ℝ) * dist x center := hlip
      _ ≤ (certificate.lipschitzConstant : ℝ) * certificate.coverRadius := by
        exact mul_le_mul_of_nonneg_left hdist certificate.lipschitzConstant.coe_nonneg
  exact (not_lt_of_ge hmargin) certificate.error_lt_margin

theorem ChapterVIFinitePositiveRealPartCover.ne_zero
    {A : Type*} [PseudoMetricSpace A] {radicand : A → ℂ}
    (certificate : ChapterVIFinitePositiveRealPartCover radicand) (x : A) :
    radicand x ≠ 0 :=
  certificate.toNonvanishingCover.ne_zero x

/-- A finite nonvanishing certificate, together with continuity, automatically produces the
compatible global square-root sheet. -/
theorem ChapterVIFiniteNonvanishingCover.exists_continuousSquareRootSheet
    {A : Type*} [PseudoMetricSpace A] [SimplyConnectedSpace A]
    [LocallyPathConnectedSpace A] {radicand : A → ℂ}
    (certificate : ChapterVIFiniteNonvanishingCover radicand)
    (hcontinuous : Continuous radicand)
    (base : A) (baseRoot : ℂ) (hbaseRoot : baseRoot ^ 2 = radicand base) :
    ∃ sheet : ChapterVIContinuousSquareRootSheet radicand,
      sheet.root base = baseRoot :=
  exists_chapterVIContinuousSquareRootSheet radicand hcontinuous
    certificate.ne_zero base baseRoot hbaseRoot

/-- Once an outer arc, its numerator, and its nonzero square-root sheet vary continuously, its
integral has an ordinary finite limit.  The `velocity` factor is the derivative of a chosen fixed-
interval parameterization of the arc. -/
theorem continuous_chapterVIParametricOuterArcIntegral
    {X : Type*} [TopologicalSpace X]
    (amplitude root velocity : X → ℝ → ℂ)
    (hamplitude : Continuous amplitude.uncurry)
    (hroot : Continuous root.uncurry)
    (hvelocity : Continuous velocity.uncurry)
    (hroot_ne : ∀ x t, root x t ≠ 0) :
    Continuous (fun x ↦ ∫ t in (0 : ℝ)..1,
      amplitude x t / root x t * velocity x t) := by
  have hintegrand : Continuous (fun point : X × ℝ ↦
      amplitude point.1 point.2 / root point.1 point.2 *
        velocity point.1 point.2) :=
    (hamplitude.div hroot (fun point ↦ hroot_ne point.1 point.2)).mul hvelocity
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    hintegrand 0 1

/-- Pointwise form of the preceding continuity theorem: the regular outer-arc contribution tends
to its finite endpoint integral. -/
theorem tendsto_chapterVIParametricOuterArcIntegral
    {X : Type*} [TopologicalSpace X]
    (amplitude root velocity : X → ℝ → ℂ)
    (hamplitude : Continuous amplitude.uncurry)
    (hroot : Continuous root.uncurry)
    (hvelocity : Continuous velocity.uncurry)
    (hroot_ne : ∀ x t, root x t ≠ 0) (endpoint : X) :
    Filter.Tendsto
      (fun x ↦ ∫ t in (0 : ℝ)..1,
        amplitude x t / root x t * velocity x t)
      (𝓝 endpoint)
      (𝓝 (∫ t in (0 : ℝ)..1,
        amplitude endpoint t / root endpoint t * velocity endpoint t)) :=
  (continuous_chapterVIParametricOuterArcIntegral amplitude root velocity
    hamplitude hroot hvelocity hroot_ne).continuousAt

end PoincareChapterVI
