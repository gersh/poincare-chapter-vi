/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.ChapterVILocalVanishingCycle
import PoincareChapterVI.ChapterVICycleDecomposition

/-!
# From Poincare's local cycle to the three-arc contour

`ChapterVICycleDecomposition` proves the exact identity `full = regular + local` after a checked
deformation of the original unit circle to Poincare's three arcs.  The local term has now been
identified with the literal principal source integrand and evaluated asymptotically.  This file
records the final analytic bookkeeping: if the two arcs away from the pinch are lower order than
`-log k`, the complete continued contour has the same nonzero logarithmic coefficient as the
middle arc.

The structure below intentionally exposes the remaining global continuation obligation.  It is
precisely the source-sheet realization of the existing three-arc identity plus regularity of the
outer arcs; no local calculation remains hidden in that hypothesis.
-/

noncomputable section

open Filter Topology
open scoped Interval

namespace PoincareChapterVI

/-- The normalized contribution of the literal principal middle cycle, in the convention used
by Poincare's `Φ`. -/
def chapterVIDPrincipalLocalPhiContribution
    (massProduct : ℂ) (b d : ℤ) (L k : ℝ) : ℂ :=
  (2 * Real.pi * Complex.I : ℂ)⁻¹ *
    chapterVIDPrincipalLocalVanishingCycleIntegral massProduct b d L k

/-- For every positive parameter, the local contribution is literally the normalized complex
curve integral on the straight middle path in the exact Morse chart. -/
theorem chapterVIDPrincipalLocalPhiContribution_eq_curveIntegral
    (massProduct : ℂ) (b d : ℤ) {L k : ℝ} (hk : 0 < k) :
    chapterVIDPrincipalLocalPhiContribution massProduct b d L k =
      (2 * Real.pi * Complex.I : ℂ)⁻¹ *
        (∫ᶜ v in Path.segment (-L : ℂ) (L : ℂ),
          chapterVIComplexScalarOneForm
            (chapterVIDPrincipalNormalIntegrand massProduct b d k) v) := by
  rw [chapterVIDPrincipalLocalPhiContribution,
    chapterVIDPrincipalNormal_curveIntegral_segment_eq massProduct b d hk]

/-- The normalized local contribution is the literal principal source curve integral on the
inverse-Morse path constructed by the compact local source model. -/
theorem ChapterVIDPrincipalLocalSourceModel.principalLocalPhiContribution_eq_sourceCurveIntegral
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalLocalSourceModel massProduct b d)
    {k : ℝ} (hkpos : 0 < k) (hkδ : k ≤ model.δ) :
    chapterVIDPrincipalLocalPhiContribution massProduct b d model.L k =
      (2 * Real.pi * Complex.I : ℂ)⁻¹ *
        (∫ᶜ t in model.sourcePath k ⟨hkpos.le, hkδ⟩,
          chapterVIComplexScalarOneForm
            (chapterVIDPrincipalPhiIntegrand massProduct b d
              chapterVIDPrincipalCollisionRoot
              (chapterVIDCriticalParameterInverseAtD (k : ℂ))) t) := by
  rw [chapterVIDPrincipalLocalPhiContribution,
    model.principalSource_curveIntegral_eq hkpos hkδ]

/-- The same identity expressed through the generic §99 three-arc API. -/
theorem chapterVIDPrincipalLocalPhiContribution_eq_localArcContribution
    (massProduct : ℂ) (b d : ℤ) {L k : ℝ} (hk : 0 < k) :
    chapterVIDPrincipalLocalPhiContribution massProduct b d L k =
      chapterVILocalArcContribution
        (fun _ v ↦ chapterVIDPrincipalNormalIntegrand massProduct b d k v)
        0 (Path.segment (-L : ℂ) (L : ℂ)) := by
  rw [chapterVIDPrincipalLocalPhiContribution_eq_curveIntegral massProduct b d hk]
  rfl

/-- The local `Φ` contribution has the expected normalized logarithmic coefficient. -/
theorem tendsto_chapterVIDPrincipalLocalPhiContribution
    {massProduct : ℂ} (b d : ℤ)
    (model : ChapterVIDPrincipalLocalSourceModel massProduct b d) :
    Tendsto
      (fun k : ℝ ↦ (-Real.log k)⁻¹ •
        chapterVIDPrincipalLocalPhiContribution massProduct b d model.L k)
      (𝓝[>] 0)
      (𝓝 ((2 * Real.pi * Complex.I : ℂ)⁻¹ *
        chapterVIDPrincipalMorseAmplitude massProduct b d (0, 0))) := by
  have hlocal : Tendsto
      (fun k : ℝ ↦ (-Real.log k)⁻¹ •
        chapterVIDPrincipalLocalVanishingCycleIntegral massProduct b d model.L k)
      (𝓝[>] 0)
      (𝓝 (chapterVIDPrincipalMorseAmplitude massProduct b d (0, 0))) := by
    simpa only [chapterVIDPrincipalLocalVanishingCycleIntegral,
      chapterVIDPrincipalRealMorseAmplitude_base] using
      tendsto_chapterVI_parametricQuadraticPinch_inv_neg_log_smul_of_contDiffOn_local
        (tendsto_chapterVIDPrincipalRealMorseAmplitude_center massProduct b d)
        model.δ_pos model.L_pos model.amplitude_contDiffOn
  have hmul := hlocal.const_mul (2 * Real.pi * Complex.I : ℂ)⁻¹
  apply hmul.congr'
  filter_upwards with k
  simp only [chapterVIDPrincipalLocalPhiContribution]
  change (2 * Real.pi * Complex.I : ℂ)⁻¹ *
      (((-Real.log k)⁻¹ : ℝ) •
        chapterVIDPrincipalLocalVanishingCycleIntegral massProduct b d model.L k) =
    ((-Real.log k)⁻¹ : ℝ) •
      ((2 * Real.pi * Complex.I : ℂ)⁻¹ *
        chapterVIDPrincipalLocalVanishingCycleIntegral massProduct b d model.L k)
  exact Algebra.mul_smul_comm ((-Real.log k)⁻¹ : ℝ)
    (2 * Real.pi * Complex.I : ℂ)⁻¹
    (chapterVIDPrincipalLocalVanishingCycleIntegral massProduct b d model.L k)

/-- The normalized local coefficient is nonzero for nonzero physical masses. -/
theorem chapterVIDPrincipalLocalPhi_logCoefficient_ne_zero
    {massProduct : ℂ} (b d : ℤ) (hmass : massProduct ≠ 0) :
    (2 * Real.pi * Complex.I : ℂ)⁻¹ *
      chapterVIDPrincipalMorseAmplitude massProduct b d (0, 0) ≠ 0 := by
  apply mul_ne_zero
  · apply inv_ne_zero
    exact mul_ne_zero
      (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero
  · exact chapterVIDPrincipalMorseAmplitude_base_ne_zero b d hmass

/-- Data still needed to place the proved local cycle into Poincare's full three-arc
continuation.  `decomposition` is supplied by the exact theorem
`chapterVIPhi_eq_regular_add_local_of_threeArcDeformation` once its source-sheet deformation and
branch compatibility have been constructed.  `regular_sublog` says that the two outer arcs stay
regular at the collision. -/
structure ChapterVIDPrincipalThreeArcContinuation
    (massProduct : ℂ) (b d : ℤ)
    (model : ChapterVIDPrincipalLocalSourceModel massProduct b d) where
  fullContribution : ℝ → ℂ
  regularContribution : ℝ → ℂ
  decomposition : ∀ᶠ k in 𝓝[>] (0 : ℝ),
    fullContribution k = regularContribution k +
      chapterVIDPrincipalLocalPhiContribution massProduct b d model.L k
  regular_sublog : Tendsto
    (fun k : ℝ ↦ (-Real.log k)⁻¹ • regularContribution k)
    (𝓝[>] 0) (𝓝 0)

/-- Any regular contribution with a finite limit is automatically lower order than Poincare's
logarithm.  Thus the outer-arc obligation can be discharged by ordinary continuity (or
analyticity) of those arc integrals at the collision parameter. -/
theorem tendsto_inv_neg_log_smul_zero_of_tendsto
    {regularContribution : ℝ → ℂ} {regularLimit : ℂ}
    (hregular : Tendsto regularContribution (𝓝[>] 0) (𝓝 regularLimit)) :
    Tendsto
      (fun k : ℝ ↦ (-Real.log k)⁻¹ • regularContribution k)
      (𝓝[>] 0) (𝓝 0) := by
  have hdenominator : Tendsto (fun k : ℝ ↦ -Real.log k) (𝓝[>] 0) atTop := by
    apply tendsto_neg_atTop_iff.mpr
    exact Real.tendsto_log_nhdsGT_zero
  have hinverse : Tendsto (fun k : ℝ ↦ (-Real.log k)⁻¹)
      (𝓝[>] 0) (𝓝 0) :=
    hdenominator.inv_tendsto_atTop
  simpa using hinverse.smul hregular

/-- Construct the three-arc asymptotic package from the more natural source-facing assertion
that the two outer-arc contributions have a finite limit. -/
def ChapterVIDPrincipalThreeArcContinuation.of_tendsto_regular
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalLocalSourceModel massProduct b d}
    (fullContribution regularContribution : ℝ → ℂ)
    (decomposition : ∀ᶠ k in 𝓝[>] (0 : ℝ),
      fullContribution k = regularContribution k +
        chapterVIDPrincipalLocalPhiContribution massProduct b d model.L k)
    {regularLimit : ℂ}
    (regular_tendsto : Tendsto regularContribution (𝓝[>] 0) (𝓝 regularLimit)) :
    ChapterVIDPrincipalThreeArcContinuation massProduct b d model where
  fullContribution := fullContribution
  regularContribution := regularContribution
  decomposition := decomposition
  regular_sublog :=
    tendsto_inv_neg_log_smul_zero_of_tendsto regular_tendsto

/-- Once the source-sheet three-arc continuation is supplied, the full continued principal
integral inherits the nonzero logarithmic coefficient proved on the middle cycle. -/
theorem ChapterVIDPrincipalThreeArcContinuation.tendsto_full_inv_neg_log_smul
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalLocalSourceModel massProduct b d}
    (continuation : ChapterVIDPrincipalThreeArcContinuation massProduct b d model) :
    Tendsto
      (fun k : ℝ ↦ (-Real.log k)⁻¹ • continuation.fullContribution k)
      (𝓝[>] 0)
      (𝓝 ((2 * Real.pi * Complex.I : ℂ)⁻¹ *
        chapterVIDPrincipalMorseAmplitude massProduct b d (0, 0))) := by
  have hsum := continuation.regular_sublog.add
    (tendsto_chapterVIDPrincipalLocalPhiContribution b d model)
  have hsum' : Tendsto
      (fun k : ℝ ↦
        (-Real.log k)⁻¹ • continuation.regularContribution k +
          (-Real.log k)⁻¹ •
            chapterVIDPrincipalLocalPhiContribution massProduct b d model.L k)
      (𝓝[>] 0)
      (𝓝 ((2 * Real.pi * Complex.I : ℂ)⁻¹ *
        chapterVIDPrincipalMorseAmplitude massProduct b d (0, 0))) := by
    simpa only [zero_add] using hsum
  apply hsum'.congr'
  filter_upwards [continuation.decomposition] with k hk
  rw [hk, smul_add]

/-- The coefficient obtained for the full three-arc continuation is genuinely nonzero. -/
theorem ChapterVIDPrincipalThreeArcContinuation.full_logCoefficient_ne_zero
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalLocalSourceModel massProduct b d}
    (_continuation : ChapterVIDPrincipalThreeArcContinuation massProduct b d model)
    (hmass : massProduct ≠ 0) :
    (2 * Real.pi * Complex.I : ℂ)⁻¹ *
      chapterVIDPrincipalMorseAmplitude massProduct b d (0, 0) ≠ 0 :=
  chapterVIDPrincipalLocalPhi_logCoefficient_ne_zero b d hmass

end PoincareChapterVI
