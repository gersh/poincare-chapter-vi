/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.ChapterVIThreeArcAsymptotic
import PoincareChapterVI.ChapterVIDOuterArcRegularity
import PoincareChapterVI.ChapterVIDRealCriticalParameter
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Complex.RealDeriv

/-!
# Compiled outer arcs and the principal three-arc continuation

The local middle curve is now a literal source-coordinate path, and the compiled polar
certificate proves that the two complementary outer integrals have a finite collision limit.
This file joins those two completed analytic statements.

The positive local critical value `k` is now synchronized unconditionally with the certified
global radial parameter. The remaining data are deliberately geometric: join the certified
quarter-arcs at `i` and `-i` to the endpoints of the local Morse segment by two regular
connectors, and prove the resulting source-contour decomposition. Once the connector
contribution has a finite limit, the nonzero logarithmic coefficient is automatic.
-/

noncomputable section

open Filter Topology

namespace PoincareChapterVI

/-- The affine radial time corresponding to the real part of the local inverse critical
parameter. The global source parameter runs from `1` to
`chapterVIDCriticalParameterModulus`. -/
def chapterVIDCriticalToGlobalParameterRaw (k : ℝ) : ℝ :=
  (1 - (chapterVIDCriticalParameterInverseAtD (k : ℂ)).re) /
    (1 - chapterVIDCriticalParameterModulus)

/-- The canonical synchronization with the compiled radial certificate. Clamping makes this a
total function; near the collision it agrees with the affine inverse whenever the local critical
parameter lies on Poincaré's real radial segment. -/
def chapterVIDCriticalToGlobalParameter (k : ℝ) : unitInterval :=
  Set.projIcc 0 1 zero_le_one (chapterVIDCriticalToGlobalParameterRaw k)

@[simp]
theorem chapterVIDCriticalToGlobalParameterRaw_zero :
    chapterVIDCriticalToGlobalParameterRaw 0 = 1 := by
  unfold chapterVIDCriticalToGlobalParameterRaw
  change (1 - (chapterVIDCriticalParameterInverseAtD 0).re) /
    (1 - chapterVIDCriticalParameterModulus) = 1
  rw [chapterVIDCriticalParameterInverseAtD_zero,
    chapterVIDZBase_eq_criticalParameter]
  simp only [Complex.ofReal_re]
  field_simp [ne_of_gt (sub_pos.mpr chapterVIDCriticalParameterModulus_lt_one)]

@[simp]
theorem chapterVIDCriticalToGlobalParameter_zero :
    chapterVIDCriticalToGlobalParameter 0 = 1 := by
  rw [chapterVIDCriticalToGlobalParameter]
  simp

theorem continuousAt_chapterVIDCriticalToGlobalParameter :
    ContinuousAt chapterVIDCriticalToGlobalParameter 0 := by
  have hinverse : ContinuousAt
      (fun k : ℝ ↦ chapterVIDCriticalParameterInverseAtD (k : ℂ)) 0 :=
    analyticAt_chapterVIDCriticalParameterInverseAtD.continuousAt.comp_of_eq
      Complex.ofRealCLM.continuous.continuousAt rfl
  have hreal : ContinuousAt
      (fun k : ℝ ↦ (chapterVIDCriticalParameterInverseAtD (k : ℂ)).re) 0 :=
    Complex.continuous_re.continuousAt.comp_of_eq hinverse rfl
  have hraw : ContinuousAt chapterVIDCriticalToGlobalParameterRaw 0 := by
    unfold chapterVIDCriticalToGlobalParameterRaw
    exact (continuousAt_const.sub hreal).div_const _
  exact (continuous_projIcc (h := zero_le_one)).continuousAt.comp_of_eq hraw rfl

/-- Synchronization with the compiled radial parameter approaches its collision endpoint. -/
theorem tendsto_chapterVIDCriticalToGlobalParameter :
    Tendsto chapterVIDCriticalToGlobalParameter (𝓝[>] (0 : ℝ))
      (𝓝 (1 : unitInterval)) := by
  rw [← chapterVIDCriticalToGlobalParameter_zero]
  exact continuousAt_chapterVIDCriticalToGlobalParameter.tendsto.mono_left
    nhdsWithin_le_nhds

/-- If the local inverse critical parameter lies on the real radial segment, the canonical
synchronization recovers it exactly as the cube of the certified global root path. -/
theorem chapterVIDCommonParameterRootPath_criticalToGlobal_pow
    {k : ℝ}
    (hreal : (chapterVIDCriticalParameterInverseAtD (k : ℂ)).im = 0)
    (hsegment : (chapterVIDCriticalParameterInverseAtD (k : ℂ)).re ∈
      Set.Icc chapterVIDCriticalParameterModulus 1) :
    chapterVIDCommonParameterRootPath
        (chapterVIDCriticalToGlobalParameter k) ^ 3 =
      chapterVIDCriticalParameterInverseAtD (k : ℂ) := by
  have hden : 0 < 1 - chapterVIDCriticalParameterModulus :=
    sub_pos.mpr chapterVIDCriticalParameterModulus_lt_one
  have hraw : chapterVIDCriticalToGlobalParameterRaw k ∈ Set.Icc (0 : ℝ) 1 := by
    unfold chapterVIDCriticalToGlobalParameterRaw
    constructor
    · exact div_nonneg (sub_nonneg.mpr hsegment.2) hden.le
    · apply (div_le_one hden).mpr
      linarith [hsegment.1]
  rw [chapterVIDCommonParameterRootPath_pow,
    chapterVIDInsideXPath_parameter]
  unfold chapterVIDCriticalToGlobalParameter
  rw [Set.projIcc_of_mem zero_le_one hraw]
  apply Complex.ext
  · simp only [Complex.ofReal_re]
    unfold chapterVIDCriticalToGlobalParameterRaw
    simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add,
      smul_eq_mul]
    field_simp [hden.ne']
    ring
  · simpa only [Complex.ofReal_im] using hreal.symm

/-- The real part of the inverse critical parameter has the positive reciprocal derivative at
zero. -/
theorem hasDerivAt_chapterVIDCriticalParameterInverseAtD_re :
    HasDerivAt
      (fun k : ℝ ↦ (chapterVIDCriticalParameterInverseAtD (k : ℂ)).re)
      ((deriv chapterVIDCriticalValue chapterVIDZBase)⁻¹).re 0 := by
  simpa only [chapterVIDCriticalParameterInverseAtD] using
    (hasDerivAt_chapterVIDCriticalParameterInverse
      deriv_chapterVIDCriticalValue_ne_zero).real_of_complex

/-- Positive critical values move the inverse source parameter to the right of `z_D`. -/
theorem eventually_chapterVIDCriticalParameterInverseAtD_re_gt_base :
    ∀ᶠ k : ℝ in nhdsWithin 0 (Set.Ioi 0),
      chapterVIDCriticalParameterModulus <
        (chapterVIDCriticalParameterInverseAtD (k : ℂ)).re := by
  let g : ℝ → ℝ := fun k ↦
    (chapterVIDCriticalParameterInverseAtD (k : ℂ)).re -
      chapterVIDCriticalParameterModulus
  have hg := hasDerivAt_chapterVIDCriticalParameterInverseAtD_re.sub_const
    chapterVIDCriticalParameterModulus
  have hgZero : g 0 = 0 := by
    unfold g
    change (chapterVIDCriticalParameterInverseAtD (0 : ℂ)).re -
      chapterVIDCriticalParameterModulus = 0
    rw [chapterVIDCriticalParameterInverseAtD_zero,
      chapterVIDZBase_eq_criticalParameter]
    simp
  have hgDeriv : 0 < deriv g 0 := by
    rw [hg.deriv]
    exact chapterVIDCriticalParameterInverse_derivative_re_pos
  have hsign := eventually_nhdsWithin_sign_eq_of_deriv_pos hgDeriv hgZero
  filter_upwards [hsign.filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with k hkSign hkPos
  have hk : 0 < k := hkPos
  have hsignK : SignType.sign k = 1 := sign_pos hk
  have hgPos : 0 < g k := by
    rw [sub_zero, hsignK] at hkSign
    exact sign_eq_one_iff.mp hkSign
  exact sub_pos.mp hgPos

/-- Continuity keeps the same inverse branch below the regular endpoint `z=1`. -/
theorem eventually_chapterVIDCriticalParameterInverseAtD_re_lt_one :
    ∀ᶠ k : ℝ in nhdsWithin 0 (Set.Ioi 0),
      (chapterVIDCriticalParameterInverseAtD (k : ℂ)).re < 1 := by
  have hcontinuous :=
    hasDerivAt_chapterVIDCriticalParameterInverseAtD_re.continuousAt
  have hbase :
      (chapterVIDCriticalParameterInverseAtD (0 : ℂ)).re =
        chapterVIDCriticalParameterModulus := by
    rw [chapterVIDCriticalParameterInverseAtD_zero,
      chapterVIDZBase_eq_criticalParameter]
    simp
  have hlt : ∀ᶠ x : ℝ in nhds chapterVIDCriticalParameterModulus, x < 1 :=
    eventually_lt_nhds chapterVIDCriticalParameterModulus_lt_one
  have htendsto := hcontinuous.tendsto
  have hbase' :
      (chapterVIDCriticalParameterInverseAtD ((0 : ℝ) : ℂ)).re =
        chapterVIDCriticalParameterModulus := by
    simpa using hbase
  rw [hbase'] at htendsto
  have hpull := htendsto.eventually hlt
  exact hpull.filter_mono nhdsWithin_le_nhds

/-- The entire radial-segment premise needed by synchronization is now unconditional. -/
theorem eventually_chapterVIDCriticalParameterInverseAtD_mem_segment :
    ∀ᶠ k : ℝ in nhdsWithin 0 (Set.Ioi 0),
      (chapterVIDCriticalParameterInverseAtD (k : ℂ)).re ∈
        Set.Icc chapterVIDCriticalParameterModulus 1 := by
  filter_upwards [eventually_chapterVIDCriticalParameterInverseAtD_re_gt_base,
    eventually_chapterVIDCriticalParameterInverseAtD_re_lt_one] with k hlower hupper
  exact ⟨hlower.le, hupper.le⟩

theorem eventually_chapterVIDCriticalToGlobalParameter_on_ray
    (hreal : ∀ᶠ k : ℝ in 𝓝[>] 0,
      (chapterVIDCriticalParameterInverseAtD (k : ℂ)).im = 0)
    (hsegment : ∀ᶠ k : ℝ in 𝓝[>] 0,
      (chapterVIDCriticalParameterInverseAtD (k : ℂ)).re ∈
        Set.Icc chapterVIDCriticalParameterModulus 1) :
    ∀ᶠ k : ℝ in 𝓝[>] 0,
      chapterVIDCommonParameterRootPath
          (chapterVIDCriticalToGlobalParameter k) ^ 3 =
        chapterVIDCriticalParameterInverseAtD (k : ℂ) := by
  filter_upwards [hreal, hsegment] with k hkreal hksegment
  exact chapterVIDCommonParameterRootPath_criticalToGlobal_pow hkreal hksegment

/-- Exact synchronization of the local critical-value parameter with the compiled global radial
parameter, with both former real-ray hypotheses discharged. -/
theorem eventually_chapterVIDCriticalToGlobalParameter_on_ray_unconditional :
    ∀ᶠ k : ℝ in nhdsWithin 0 (Set.Ioi 0),
      chapterVIDCommonParameterRootPath
          (chapterVIDCriticalToGlobalParameter k) ^ 3 =
        chapterVIDCriticalParameterInverseAtD (k : ℂ) :=
  eventually_chapterVIDCriticalToGlobalParameter_on_ray
    (eventually_chapterVIDCriticalParameterInverseAtD_im_eq_zero.filter_mono
      nhdsWithin_le_nhds)
    eventually_chapterVIDCriticalParameterInverseAtD_mem_segment

/-- The exact remaining placement data after the compiled outer quarters, the literal local
middle path, and global/local parameter synchronization have been proved.
`connectorContribution` is the normalized sum of the two regular arcs from the quarter endpoints
to the local path endpoints; unlike the pinched middle path it must have an ordinary finite
limit. `decomposition` is the source-sheet contour identity containing all five pieces. -/
structure ChapterVIDCompiledPrincipalThreeArcPlacement
    (run : ChapterVIDOuterArcPolarCompiledGrid.CompiledRunVerdict)
    (massProduct : ℂ) (b d : ℤ)
    (model : ChapterVIDPrincipalLocalSourceModel massProduct b d) where
  fullContribution : ℝ → ℂ
  connectorContribution : ℝ → ℂ
  connectorLimit : ℂ
  connector_tendsto :
    Tendsto connectorContribution (𝓝[>] (0 : ℝ)) (𝓝 connectorLimit)
  decomposition : ∀ᶠ k in 𝓝[>] (0 : ℝ),
    fullContribution k =
      (ChapterVIDOuterArcRegularity.principalRegularContribution
          run massProduct b d (chapterVIDCriticalToGlobalParameter k) +
        connectorContribution k) +
      chapterVIDPrincipalLocalPhiContribution massProduct b d model.L k

namespace ChapterVIDCompiledPrincipalThreeArcPlacement

/-- The certified regular contribution, pulled back from the global radial parameter to the
positive local critical-value parameter. -/
def regularContribution
    {run : ChapterVIDOuterArcPolarCompiledGrid.CompiledRunVerdict}
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalLocalSourceModel massProduct b d}
    (placement : ChapterVIDCompiledPrincipalThreeArcPlacement
      run massProduct b d model) : ℝ → ℂ :=
  fun k ↦ ChapterVIDOuterArcRegularity.principalRegularContribution
      run massProduct b d (chapterVIDCriticalToGlobalParameter k) +
    placement.connectorContribution k

/-- The compiled outer contribution has a finite limit after synchronization with the local
critical-value parameter. -/
theorem tendsto_regularContribution
    {run : ChapterVIDOuterArcPolarCompiledGrid.CompiledRunVerdict}
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalLocalSourceModel massProduct b d}
    (placement : ChapterVIDCompiledPrincipalThreeArcPlacement
      run massProduct b d model) :
    Tendsto placement.regularContribution (𝓝[>] (0 : ℝ))
      (𝓝 (ChapterVIDOuterArcRegularity.principalRegularContribution
        run massProduct b d 1 + placement.connectorLimit)) :=
  (Filter.Tendsto.comp
      (ChapterVIDOuterArcRegularity.tendsto_principalRegularContribution_collision
        run massProduct b d)
      tendsto_chapterVIDCriticalToGlobalParameter).add placement.connector_tendsto

/-- Convert the geometric placement data into the generic three-arc asymptotic package.  In
particular, the formerly abstract `regular_sublog` field is discharged by the compiled finite
outer limit together with the named finite connector limit. -/
def toThreeArcContinuation
    {run : ChapterVIDOuterArcPolarCompiledGrid.CompiledRunVerdict}
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalLocalSourceModel massProduct b d}
    (placement : ChapterVIDCompiledPrincipalThreeArcPlacement
      run massProduct b d model) :
    ChapterVIDPrincipalThreeArcContinuation massProduct b d model :=
  ChapterVIDPrincipalThreeArcContinuation.of_tendsto_regular
    placement.fullContribution placement.regularContribution
    placement.decomposition placement.tendsto_regularContribution

/-- The fully placed compiled continuation inherits Poincaré's exact logarithmic coefficient. -/
theorem tendsto_full_inv_neg_log_smul
    {run : ChapterVIDOuterArcPolarCompiledGrid.CompiledRunVerdict}
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalLocalSourceModel massProduct b d}
    (placement : ChapterVIDCompiledPrincipalThreeArcPlacement
      run massProduct b d model) :
    Tendsto
      (fun k : ℝ ↦ (-Real.log k)⁻¹ • placement.fullContribution k)
      (𝓝[>] 0)
      (𝓝 ((2 * Real.pi * Complex.I : ℂ)⁻¹ *
        chapterVIDPrincipalMorseAmplitude massProduct b d (0, 0))) :=
  placement.toThreeArcContinuation.tendsto_full_inv_neg_log_smul

/-- For nonzero physical masses, the coefficient produced by the compiled three-arc
continuation cannot vanish. -/
theorem full_logCoefficient_ne_zero
    {run : ChapterVIDOuterArcPolarCompiledGrid.CompiledRunVerdict}
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalLocalSourceModel massProduct b d}
    (placement : ChapterVIDCompiledPrincipalThreeArcPlacement
      run massProduct b d model) (hmass : massProduct ≠ 0) :
    (2 * Real.pi * Complex.I : ℂ)⁻¹ *
      chapterVIDPrincipalMorseAmplitude massProduct b d (0, 0) ≠ 0 :=
  placement.toThreeArcContinuation.full_logCoefficient_ne_zero hmass

end ChapterVIDCompiledPrincipalThreeArcPlacement

end PoincareChapterVI
