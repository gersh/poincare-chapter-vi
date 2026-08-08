/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.ChapterVIPrincipalIntegrand
import PoincareChapterVI.ChapterVIPinchModel

/-!
# Poincare's local vanishing cycle at D

The source radicand has already been changed analytically to the exact normal form `k + v²`, and
the complete numerator together with the inverse-coordinate Jacobian is the analytic function
`chapterVIDPrincipalMorseAmplitude`.  This file restricts that holomorphic germ to the real
positive-`k` slice and proves Poincare's decisive local calculation: the integral over a fixed
symmetric middle segment has a logarithmic leading term whose coefficient is the value of the
actual source amplitude at D.

The proof is local.  It does not extend the inverse-function-theorem germ arbitrarily to a global
continuous function, and it uses no numerical or compiled certificate.
-/

noncomputable section

open Filter Set Topology
open scoped Interval ComplexOrder

namespace PoincareChapterVI

/-- The canonical collision root on the local source chart.  On the positive real Morse slice
this is the same principal square root used in the explicit quadratic-pinch integral. -/
def chapterVIDPrincipalCollisionRoot (point : ℂ × ℂ) : ℂ :=
  Complex.sqrt (chapterVIDRadicand point)

/-- The actual principal Morse amplitude restricted to Poincare's real vanishing-cycle slice. -/
def chapterVIDPrincipalRealMorseAmplitude
    (massProduct : ℂ) (b d : ℤ) (point : ℝ × ℝ) : ℂ :=
  chapterVIDPrincipalMorseAmplitude massProduct b d
    ((point.1 : ℂ), (point.2 : ℂ))

@[simp]
theorem chapterVIDPrincipalRealMorseAmplitude_base
    (massProduct : ℂ) (b d : ℤ) :
    chapterVIDPrincipalRealMorseAmplitude massProduct b d (0, 0) =
      chapterVIDPrincipalMorseAmplitude massProduct b d (0, 0) :=
  rfl

/-- Holomorphic regularity of the prepared source amplitude supplies real `C¹` regularity on
the positive-parameter slice. -/
theorem contDiffAt_chapterVIDPrincipalRealMorseAmplitude
    (massProduct : ℂ) (b d : ℤ) :
    ContDiffAt ℝ 1 (chapterVIDPrincipalRealMorseAmplitude massProduct b d) (0, 0) := by
  have hcomplex : ContDiffAt ℂ 1
      (chapterVIDPrincipalMorseAmplitude massProduct b d) (0, 0) :=
    (analyticAt_chapterVIDPrincipalMorseAmplitude massProduct b d).contDiffAt
  have hreal : ContDiffAt ℝ 1
      (chapterVIDPrincipalMorseAmplitude massProduct b d) (0, 0) :=
    hcomplex.restrict_scalars ℝ
  have hfst : ContDiffAt ℝ 1
      (fun point : ℝ × ℝ ↦ (point.1 : ℂ)) (0, 0) :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp (0, 0) contDiffAt_fst
  have hsnd : ContDiffAt ℝ 1
      (fun point : ℝ × ℝ ↦ (point.2 : ℂ)) (0, 0) :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp (0, 0) contDiffAt_snd
  exact hreal.comp (0, 0) (hfst.prodMk hsnd)

/-- There is a genuine compact positive-parameter rectangle on which the actual local amplitude
is `C¹`.  This extracts explicit real integration data from the holomorphic germ. -/
theorem exists_chapterVIDPrincipalRealMorseAmplitude_contDiffOn
    (massProduct : ℂ) (b d : ℤ) :
    ∃ δ L : ℝ, 0 < δ ∧ 0 < L ∧
      ContDiffOn ℝ 1 (chapterVIDPrincipalRealMorseAmplitude massProduct b d)
        (Set.Icc 0 δ ×ˢ Set.uIcc (-L) L) := by
  obtain ⟨u, hu, hcont⟩ :=
    (contDiffAt_chapterVIDPrincipalRealMorseAmplitude massProduct b d).contDiffOn
      (m := 1) le_rfl (by simp)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hu
  refine ⟨ε / 2, ε / 2, by positivity, by positivity, hcont.mono ?_⟩
  rintro ⟨k, t⟩ ⟨hk, ht⟩
  apply hball
  rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
  simp only [Real.dist_eq, sub_zero]
  rw [uIcc_of_le (by linarith)] at ht
  constructor
  · rw [abs_of_nonneg hk.1]
    linarith [hk.2]
  · rw [abs_lt]
    constructor <;> linarith [ht.1, ht.2]

/-- The center value of the actual prepared amplitude converges to its value at D along positive
real critical values. -/
theorem tendsto_chapterVIDPrincipalRealMorseAmplitude_center
    (massProduct : ℂ) (b d : ℤ) :
    Tendsto
      (fun k : ℝ ↦ chapterVIDPrincipalRealMorseAmplitude massProduct b d (k, 0))
      (𝓝[>] 0)
      (𝓝 (chapterVIDPrincipalRealMorseAmplitude massProduct b d (0, 0))) := by
  have hline : ContinuousAt (fun k : ℝ ↦ (k, (0 : ℝ))) 0 :=
    continuousAt_id.prodMk continuousAt_const
  have hcomp : ContinuousAt
      (chapterVIDPrincipalRealMorseAmplitude massProduct b d ∘
        fun k : ℝ ↦ (k, (0 : ℝ))) 0 :=
    (contDiffAt_chapterVIDPrincipalRealMorseAmplitude massProduct b d).continuousAt.comp_of_eq
      hline rfl
  change Tendsto
    (chapterVIDPrincipalRealMorseAmplitude massProduct b d ∘
      fun k : ℝ ↦ (k, (0 : ℝ)))
    (𝓝[>] 0)
    (𝓝 (chapterVIDPrincipalRealMorseAmplitude massProduct b d (0, 0)))
  exact hcomp.tendsto.mono_left nhdsWithin_le_nhds

/-- The literal source point corresponding to real normal-form coordinates `(k,v)`. -/
def chapterVIDRealCriticalMorseSourcePoint (point : ℝ × ℝ) : ℂ × ℂ :=
  chapterVIDCriticalMorseSourcePointAtD
    ((point.1 : ℂ), (point.2 : ℂ))

@[simp]
theorem chapterVIDRealCriticalMorseSourcePoint_base :
    chapterVIDRealCriticalMorseSourcePoint (0, 0) =
      (chapterVIDZBase, chapterVIDTBase) :=
  chapterVIDCriticalMorseSourcePointAtD_base

/-- The exact complex normal-form identity pulls back to the real positive-parameter slice. -/
theorem eventually_chapterVIDRadicand_realCriticalMorseSourcePoint_eq :
    ∀ᶠ point : ℝ × ℝ in 𝓝 (0, 0),
      chapterVIDRadicand (chapterVIDRealCriticalMorseSourcePoint point) =
        (point.1 : ℂ) + (point.2 : ℂ) ^ 2 := by
  have hfst : Continuous
      (fun point : ℝ × ℝ ↦ (point.1 : ℂ)) :=
    Complex.ofRealCLM.continuous.comp continuous_fst
  have hsnd : Continuous
      (fun point : ℝ × ℝ ↦ (point.2 : ℂ)) :=
    Complex.ofRealCLM.continuous.comp continuous_snd
  have htendsto : Tendsto
      (fun point : ℝ × ℝ ↦ ((point.1 : ℂ), (point.2 : ℂ)))
      (𝓝 (0, 0)) (𝓝 ((0 : ℂ), (0 : ℂ))) :=
    (hfst.prodMk hsnd).continuousAt
  exact htendsto.eventually
    eventually_chapterVIDRadicand_criticalMorseSourcePointAtD_eq

/-- On a neighborhood of the real Morse slice, differentiation in the `v` coordinate of the
inverse Morse fiber is exactly the named inverse Morse Jacobian. -/
theorem eventually_hasDerivAt_chapterVIDRealCriticalMorseFiberInverse :
    ∀ᶠ point : ℝ × ℝ in 𝓝 (0, 0),
      HasDerivAt
        (chapterVIDMorseFiberInverse ∘ fun w : ℂ ↦
          (chapterVIDCriticalParameterInverseAtD (point.1 : ℂ), w))
        (chapterVIDMorseJacobian
          (chapterVIDCriticalMorseParameterMap
            deriv_chapterVIDCriticalValue_ne_zero
            ((point.1 : ℂ), (point.2 : ℂ))))
        (point.2 : ℂ) := by
  have hfst : Continuous
      (fun point : ℝ × ℝ ↦ (point.1 : ℂ)) :=
    Complex.ofRealCLM.continuous.comp continuous_fst
  have hsnd : Continuous
      (fun point : ℝ × ℝ ↦ (point.2 : ℂ)) :=
    Complex.ofRealCLM.continuous.comp continuous_snd
  have hcritical : Tendsto
      (fun point : ℝ × ℝ ↦
        chapterVIDCriticalMorseParameterMap
          deriv_chapterVIDCriticalValue_ne_zero
          ((point.1 : ℂ), (point.2 : ℂ)))
      (𝓝 (0, 0)) (𝓝 (chapterVIDZBase, 0)) := by
    have hpair : Tendsto
        (fun point : ℝ × ℝ ↦ ((point.1 : ℂ), (point.2 : ℂ)))
        (𝓝 (0, 0)) (𝓝 ((0 : ℂ), (0 : ℂ))) :=
      (hfst.prodMk hsnd).continuousAt
    change Tendsto
      (chapterVIDCriticalMorseParameterMap
        deriv_chapterVIDCriticalValue_ne_zero ∘
          fun point : ℝ × ℝ ↦ ((point.1 : ℂ), (point.2 : ℂ)))
      (𝓝 (0, 0)) (𝓝 (chapterVIDZBase, 0))
    simpa only [chapterVIDCriticalMorseParameterMap_base] using
      Filter.Tendsto.comp
        (analyticAt_chapterVIDCriticalMorseParameterMap
          deriv_chapterVIDCriticalValue_ne_zero).continuousAt hpair
  have hfiber := hcritical.eventually
    eventually_hasDerivAt_chapterVIDMorseFiberInverse
  filter_upwards [hfiber] with point hpoint
  simpa only [chapterVIDCriticalMorseParameterMap,
    chapterVIDCriticalParameterInverseAtD] using hpoint

/-- Complete local data for Poincare's actual principal middle cycle.  On one and the same
positive rectangle, the pulled-back source amplitude is `C¹` and the literal source radicand is
exactly `k+v²`. -/
structure ChapterVIDPrincipalLocalSourceModel
    (massProduct : ℂ) (b d : ℤ) where
  δ : ℝ
  L : ℝ
  δ_pos : 0 < δ
  L_pos : 0 < L
  amplitude_contDiffOn :
    ContDiffOn ℝ 1 (chapterVIDPrincipalRealMorseAmplitude massProduct b d)
      (Set.Icc 0 δ ×ˢ Set.uIcc (-L) L)
  radicand_eq : ∀ k ∈ Set.Icc 0 δ, ∀ v ∈ Set.uIcc (-L) L,
    chapterVIDRadicand (chapterVIDRealCriticalMorseSourcePoint (k, v)) =
      (k : ℂ) + (v : ℂ) ^ 2
  sourceFiber_hasDerivAt : ∀ k ∈ Set.Icc 0 δ, ∀ v ∈ Set.uIcc (-L) L,
    HasDerivAt
      (chapterVIDMorseFiberInverse ∘ fun w : ℂ ↦
        (chapterVIDCriticalParameterInverseAtD (k : ℂ), w))
      (chapterVIDMorseJacobian
        (chapterVIDCriticalMorseParameterMap
          deriv_chapterVIDCriticalValue_ne_zero ((k : ℂ), (v : ℂ))))
      (v : ℂ)

/-- On the certified local rectangle, the canonical source root is literally the principal root
of Poincaré's exact normal form `k+v²`. -/
theorem ChapterVIDPrincipalLocalSourceModel.principalCollisionRoot_eq
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalLocalSourceModel massProduct b d)
    {k v : ℝ} (hk : k ∈ Set.Icc 0 model.δ)
    (hv : v ∈ Set.uIcc (-model.L) model.L) :
    chapterVIDPrincipalCollisionRoot
        (chapterVIDRealCriticalMorseSourcePoint (k, v)) =
      Complex.sqrt ((k : ℂ) + (v : ℂ) ^ 2) := by
  rw [chapterVIDPrincipalCollisionRoot, model.radicand_eq k hk v hv]

/-- Pointwise source-to-Morse pullback for the actual principal integrand.  The only hypothesis
is the already proved local normal-form identity; the square-root compatibility is discharged
by choosing `Complex.sqrt` on both sides. -/
theorem chapterVIDPrincipalCriticalMorse_pullback_oneForm
    (massProduct : ℂ) (b d : ℤ) (point : ℂ × ℂ) (direction : ℂ)
    (hradicand :
      chapterVIDRadicand (chapterVIDCriticalMorseSourcePointAtD point) =
        point.1 + point.2 ^ 2) :
    chapterVIComplexScalarOneForm
        (chapterVIDPrincipalPhiIntegrand massProduct b d
          chapterVIDPrincipalCollisionRoot
          (chapterVIDCriticalMorseSourcePointAtD point).1)
        (chapterVIDCriticalMorseSourcePointAtD point).2
        (direction * chapterVIDMorseJacobian
          (chapterVIDCriticalMorseParameterMap
            deriv_chapterVIDCriticalValue_ne_zero point)) =
      chapterVIComplexScalarOneForm
        (fun v ↦ chapterVIDPrincipalMorseAmplitude massProduct b d (point.1, v) /
          Complex.sqrt (point.1 + v ^ 2))
        point.2 direction := by
  have hpull := chapterVIDMorse_pullback_inverseRoot_oneForm
    (chapterVIDPrincipalSourceNumerator massProduct b d)
    chapterVIDPrincipalCollisionRoot
    (fun _ ↦ Complex.sqrt (point.1 + point.2 ^ 2))
    (chapterVIDCriticalMorseParameterMap
      deriv_chapterVIDCriticalValue_ne_zero point) direction
    (by
      change Complex.sqrt
          (chapterVIDRadicand (chapterVIDCriticalMorseSourcePointAtD point)) =
        Complex.sqrt (point.1 + point.2 ^ 2)
      rw [hradicand])
  simpa only [chapterVIComplexScalarOneForm_apply,
    chapterVIDPrincipalPhiIntegrand,
    chapterVIDCriticalMorseSourcePointAtD,
    chapterVIDCriticalMorseSourcePoint,
    chapterVIDMorseSourcePoint,
    chapterVIDCriticalMorseParameterMap,
    chapterVIDPrincipalMorseAmplitude,
    chapterVIDCriticalMorseAmplitudeAtD,
    chapterVIDCriticalMorseAmplitude] using hpull

/-- The analytic constructions made earlier really supply the complete local source model on a
single compact rectangle. -/
theorem exists_chapterVIDPrincipalLocalSourceModel
    (massProduct : ℂ) (b d : ℤ) :
    Nonempty (ChapterVIDPrincipalLocalSourceModel massProduct b d) := by
  obtain ⟨δ₀, L₀, hδ₀, hL₀, hcont⟩ :=
    exists_chapterVIDPrincipalRealMorseAmplitude_contDiffOn massProduct b d
  have hnormalSet :
      {point : ℝ × ℝ |
        chapterVIDRadicand (chapterVIDRealCriticalMorseSourcePoint point) =
          (point.1 : ℂ) + (point.2 : ℂ) ^ 2} ∈ 𝓝 (0, 0) :=
    eventually_chapterVIDRadicand_realCriticalMorseSourcePoint_eq
  have hderivSet :
      {point : ℝ × ℝ |
        HasDerivAt
          (chapterVIDMorseFiberInverse ∘ fun w : ℂ ↦
            (chapterVIDCriticalParameterInverseAtD (point.1 : ℂ), w))
          (chapterVIDMorseJacobian
            (chapterVIDCriticalMorseParameterMap
              deriv_chapterVIDCriticalValue_ne_zero
              ((point.1 : ℂ), (point.2 : ℂ))))
          (point.2 : ℂ)} ∈ 𝓝 (0, 0) :=
    eventually_hasDerivAt_chapterVIDRealCriticalMorseFiberInverse
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp
    (inter_mem hnormalSet hderivSet)
  let r : ℝ := min (min δ₀ L₀) (ε / 2)
  have hr : 0 < r := by
    dsimp [r]
    exact lt_min (lt_min hδ₀ hL₀) (by positivity)
  have hrmin : r ≤ min δ₀ L₀ := by
    dsimp [r]
    exact min_le_left _ _
  have hrδ : r ≤ δ₀ := hrmin.trans (min_le_left δ₀ L₀)
  have hrL : r ≤ L₀ := hrmin.trans (min_le_right δ₀ L₀)
  have hrε : r ≤ ε / 2 := by
    dsimp [r]
    exact min_le_right _ _
  refine ⟨{
    δ := r
    L := r
    δ_pos := hr
    L_pos := hr
    amplitude_contDiffOn := hcont.mono ?_
    radicand_eq := ?_
    sourceFiber_hasDerivAt := ?_ }⟩
  · rintro ⟨k, v⟩ ⟨hk, hv⟩
    rw [uIcc_of_le (by linarith [hr])] at hv ⊢
    exact ⟨⟨hk.1, hk.2.trans hrδ⟩,
      ⟨by linarith [hrL, hv.1], by linarith [hrL, hv.2]⟩⟩
  · intro k hk v hv
    have hkv : (k, v) ∈ Metric.ball (0, 0) ε := by
      rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
      simp only [Real.dist_eq, sub_zero]
      rw [uIcc_of_le (by linarith [hr])] at hv
      constructor
      · rw [abs_of_nonneg hk.1]
        linarith [hk.2, hrε]
      · rw [abs_lt]
        constructor <;> linarith [hv.1, hv.2, hrε]
    exact (hball hkv).1
  · intro k hk v hv
    have hkv : (k, v) ∈ Metric.ball (0, 0) ε := by
      rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
      simp only [Real.dist_eq, sub_zero]
      rw [uIcc_of_le (by linarith [hr])] at hv
      constructor
      · rw [abs_of_nonneg hk.1]
        linarith [hk.2, hrε]
      · rw [abs_lt]
        constructor <;> linarith [hv.1, hv.2, hrε]
    exact (hball hkv).2

/-- The integral over the symmetric real middle cycle in the exact `k+v²` Morse chart.  For
`k>0`, the denominator is the positive square-root sheet of the normal-form radicand. -/
def chapterVIDPrincipalLocalVanishingCycleIntegral
    (massProduct : ℂ) (b d : ℤ) (L k : ℝ) : ℂ :=
  ∫ t in -L..L,
    chapterVIParametricQuadraticPinchIntegrand
      (fun parameter coordinate ↦
        chapterVIDPrincipalRealMorseAmplitude massProduct b d (parameter, coordinate)) k t

/-- The holomorphic normal-form integrand whose restriction to the positive real slice is the
integrand above.  The principal complex square root is the positive sheet along that slice. -/
def chapterVIDPrincipalNormalIntegrand
    (massProduct : ℂ) (b d : ℤ) (k : ℝ) (v : ℂ) : ℂ :=
  chapterVIDPrincipalMorseAmplitude massProduct b d ((k : ℂ), v) /
    Complex.sqrt ((k : ℂ) + v ^ 2)

/-- On `k>0` and the real middle cycle, the complex positive square-root sheet is exactly the
real quadratic-pinch kernel used in the asymptotic theorem. -/
theorem chapterVIDPrincipalNormalIntegrand_ofReal
    (massProduct : ℂ) (b d : ℤ) {k : ℝ} (hk : 0 < k) (t : ℝ) :
    chapterVIDPrincipalNormalIntegrand massProduct b d k (t : ℂ) =
      chapterVIParametricQuadraticPinchIntegrand
        (fun parameter coordinate ↦
          chapterVIDPrincipalRealMorseAmplitude massProduct b d (parameter, coordinate)) k t := by
  have hpositive : 0 < t ^ 2 + k := by nlinarith [sq_nonneg t]
  have hnonnegative : (0 : ℂ) ≤ ((t ^ 2 + k : ℝ) : ℂ) := by
    exact_mod_cast hpositive.le
  have hsqrt : Complex.sqrt ((k : ℂ) + (t : ℂ) ^ 2) =
      (Real.sqrt (t ^ 2 + k) : ℂ) := by
    rw [show (k : ℂ) + (t : ℂ) ^ 2 = ((t ^ 2 + k : ℝ) : ℂ) by
      push_cast
      ring]
    rw [Complex.sqrt_of_nonneg hnonnegative]
    congr 1
  rw [chapterVIDPrincipalNormalIntegrand, hsqrt]
  simp only [chapterVIParametricQuadraticPinchIntegrand,
    chapterVIQuadraticPinchIntegrand, chapterVIDPrincipalRealMorseAmplitude]
  rw [Complex.real_smul]
  push_cast
  rw [inv_mul_eq_div]

/-- On the local model rectangle, the one-form in Poincaré's literal source coordinate pulls
back exactly to the principal normal-form one-form used in the logarithmic calculation. -/
theorem ChapterVIDPrincipalLocalSourceModel.principalSource_pullback_oneForm
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalLocalSourceModel massProduct b d)
    {k v : ℝ} (hk : k ∈ Set.Icc 0 model.δ)
    (hv : v ∈ Set.uIcc (-model.L) model.L) (direction : ℂ) :
    chapterVIComplexScalarOneForm
        (chapterVIDPrincipalPhiIntegrand massProduct b d
          chapterVIDPrincipalCollisionRoot
          (chapterVIDRealCriticalMorseSourcePoint (k, v)).1)
        (chapterVIDRealCriticalMorseSourcePoint (k, v)).2
        (direction * chapterVIDMorseJacobian
          (chapterVIDCriticalMorseParameterMap
            deriv_chapterVIDCriticalValue_ne_zero ((k : ℂ), (v : ℂ)))) =
      chapterVIComplexScalarOneForm
        (chapterVIDPrincipalNormalIntegrand massProduct b d k)
        (v : ℂ) direction := by
  simpa [chapterVIDRealCriticalMorseSourcePoint,
    chapterVIDPrincipalNormalIntegrand] using
    chapterVIDPrincipalCriticalMorse_pullback_oneForm massProduct b d
      ((k : ℂ), (v : ℂ)) direction (model.radicand_eq k hk v hv)

/-- The interval integral evaluated below is literally the complex curve integral of the
normal-form one-form along the straight middle path from `-L` to `L`. -/
theorem chapterVIDPrincipalNormal_curveIntegral_segment_eq
    (massProduct : ℂ) (b d : ℤ) {L k : ℝ} (hk : 0 < k) :
    (∫ᶜ v in Path.segment (-L : ℂ) (L : ℂ),
      chapterVIComplexScalarOneForm
        (chapterVIDPrincipalNormalIntegrand massProduct b d k) v) =
      chapterVIDPrincipalLocalVanishingCycleIntegral massProduct b d L k := by
  rw [curveIntegral_segment]
  let integrand : ℝ → ℂ := fun t ↦
    chapterVIParametricQuadraticPinchIntegrand
      (fun parameter coordinate ↦
        chapterVIDPrincipalRealMorseAmplitude massProduct b d (parameter, coordinate)) k t
  calc
    (∫ s in 0..1,
      chapterVIComplexScalarOneForm
        (chapterVIDPrincipalNormalIntegrand massProduct b d k)
        (AffineMap.lineMap (-L : ℂ) (L : ℂ) s) ((L : ℂ) - (-L : ℂ))) =
        (2 * L) • ∫ s in 0..1, integrand (2 * L * s + -L) := by
      rw [← intervalIntegral.integral_smul]
      apply intervalIntegral.integral_congr
      intro s _
      change chapterVIComplexScalarOneForm
          (chapterVIDPrincipalNormalIntegrand massProduct b d k)
          (AffineMap.lineMap (-L : ℂ) (L : ℂ) s) ((L : ℂ) - (-L : ℂ)) =
        (2 * L) • integrand (2 * L * s + -L)
      rw [chapterVIComplexScalarOneForm_apply]
      have hline : AffineMap.lineMap (-L : ℂ) (L : ℂ) s =
          ((2 * L * s + -L : ℝ) : ℂ) := by
        simp [AffineMap.lineMap_apply]
        ring
      rw [hline, chapterVIDPrincipalNormalIntegrand_ofReal massProduct b d hk]
      dsimp only [integrand]
      rw [Complex.real_smul]
      push_cast
      ring
    _ = ∫ t in -L..L, integrand t := by
      have hsubstitution := intervalIntegral.smul_integral_comp_mul_add
        (f := integrand) (a := 0) (b := 1) (c := 2 * L) (-L)
      convert hsubstitution using 1
      · ring_nf
    _ = chapterVIDPrincipalLocalVanishingCycleIntegral massProduct b d L k := by
      rfl

/-- Poincare's local logarithmic calculation for the literal principal source term at D.  There
is a fixed symmetric middle cycle on which the coefficient of `-log k` is exactly the complete
Morse amplitude (source numerator times coordinate Jacobian) at the collision. -/
theorem exists_tendsto_chapterVIDPrincipalLocalVanishingCycleIntegral
    (massProduct : ℂ) (b d : ℤ) :
    ∃ δ L : ℝ, 0 < δ ∧ 0 < L ∧
      Tendsto
        (fun k : ℝ ↦ (-Real.log k)⁻¹ •
          chapterVIDPrincipalLocalVanishingCycleIntegral massProduct b d L k)
        (𝓝[>] 0)
        (𝓝 (chapterVIDPrincipalMorseAmplitude massProduct b d (0, 0))) := by
  obtain ⟨δ, L, hδ, hL, hcont⟩ :=
    exists_chapterVIDPrincipalRealMorseAmplitude_contDiffOn massProduct b d
  refine ⟨δ, L, hδ, hL, ?_⟩
  simpa only [chapterVIDPrincipalLocalVanishingCycleIntegral,
    chapterVIDPrincipalRealMorseAmplitude_base] using
    tendsto_chapterVI_parametricQuadraticPinch_inv_neg_log_smul_of_contDiffOn_local
      (tendsto_chapterVIDPrincipalRealMorseAmplitude_center massProduct b d)
      hδ hL hcont

/-- With a nonzero physical mass product, the logarithmic coefficient on Poincare's local
vanishing cycle is nonzero. -/
theorem chapterVIDPrincipalLocalVanishingCycle_logCoefficient_ne_zero
    {massProduct : ℂ} (b d : ℤ) (hmass : massProduct ≠ 0) :
    chapterVIDPrincipalMorseAmplitude massProduct b d (0, 0) ≠ 0 :=
  chapterVIDPrincipalMorseAmplitude_base_ne_zero b d hmass

/-- Source-facing package of the local conclusion: a fixed middle cycle exists, its normalized
integral converges to the exact source coefficient, and that coefficient cannot vanish for
nonzero masses. -/
theorem exists_chapterVIDPrincipalLocalVanishingCycle_nonzeroLog
    {massProduct : ℂ} (b d : ℤ) (hmass : massProduct ≠ 0) :
    ∃ δ L : ℝ, 0 < δ ∧ 0 < L ∧
      Tendsto
        (fun k : ℝ ↦ (-Real.log k)⁻¹ •
          chapterVIDPrincipalLocalVanishingCycleIntegral massProduct b d L k)
        (𝓝[>] 0)
        (𝓝 (chapterVIDPrincipalMorseAmplitude massProduct b d (0, 0))) ∧
      chapterVIDPrincipalMorseAmplitude massProduct b d (0, 0) ≠ 0 := by
  obtain ⟨δ, L, hδ, hL, hlimit⟩ :=
    exists_tendsto_chapterVIDPrincipalLocalVanishingCycleIntegral massProduct b d
  exact ⟨δ, L, hδ, hL, hlimit,
    chapterVIDPrincipalLocalVanishingCycle_logCoefficient_ne_zero b d hmass⟩

/-- Strongest local package: the logarithmic middle-cycle asymptotic is proved on a rectangle
where the integrand is the pullback of Poincare's literal source radicand, not merely an abstract
quadratic model. -/
theorem exists_chapterVIDPrincipalLocalSourceModel_nonzeroLog
    {massProduct : ℂ} (b d : ℤ) (hmass : massProduct ≠ 0) :
    ∃ model : ChapterVIDPrincipalLocalSourceModel massProduct b d,
      Tendsto
        (fun k : ℝ ↦ (-Real.log k)⁻¹ •
          chapterVIDPrincipalLocalVanishingCycleIntegral massProduct b d model.L k)
        (𝓝[>] 0)
        (𝓝 (chapterVIDPrincipalMorseAmplitude massProduct b d (0, 0))) ∧
      chapterVIDPrincipalMorseAmplitude massProduct b d (0, 0) ≠ 0 := by
  let model := Classical.choice
    (exists_chapterVIDPrincipalLocalSourceModel massProduct b d)
  refine ⟨model, ?_,
    chapterVIDPrincipalLocalVanishingCycle_logCoefficient_ne_zero b d hmass⟩
  simpa only [chapterVIDPrincipalLocalVanishingCycleIntegral,
    chapterVIDPrincipalRealMorseAmplitude_base] using
    tendsto_chapterVI_parametricQuadraticPinch_inv_neg_log_smul_of_contDiffOn_local
      (tendsto_chapterVIDPrincipalRealMorseAmplitude_center massProduct b d)
      model.δ_pos model.L_pos model.amplitude_contDiffOn

end PoincareChapterVI
