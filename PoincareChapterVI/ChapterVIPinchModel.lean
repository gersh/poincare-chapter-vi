/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# A rigorous quadratic-pinch model for Poincaré's Chapter VI, §99

The local normal form in §99 reduces the singular part of the contour integrand to a unit times
`((t - h)² + k)⁻¹ᐟ²`. This file treats the real symmetric model exactly. It shows that integrating
the quadratic factor gives an inverse hyperbolic sine and hence an explicit logarithmic term as
`k → 0⁺`.

This is not yet the complex contour-pinch theorem needed for Poincaré's actual perturbing
function: that step also requires compatible square-root branches, transport of the integration
cycle, and control of the analytic unit and remainder.
-/

noncomputable section

open Filter Set
open scoped Interval Topology

namespace PoincareChapterVI

/-- The real quadratic-pinch integrand. -/
def chapterVIQuadraticPinchIntegrand (k t : ℝ) : ℝ :=
  (Real.sqrt (t ^ 2 + k))⁻¹

/-- A scalar analytic unit multiplying the quadratic-pinch kernel.  The source application has
an analytic amplitude depending on both the contour coordinate and the external parameter; this
one-parameter model isolates the effect of variation in the contour coordinate. -/
def chapterVIWeightedQuadraticPinchIntegrand
    (amplitude : ℝ → ℝ) (k t : ℝ) : ℝ :=
  amplitude t * chapterVIQuadraticPinchIntegrand k t

/-- After extracting the value of the amplitude at the pinch, this is the remaining integrand. -/
def chapterVIQuadraticPinchAmplitudeRemainder
    (amplitude : ℝ → ℝ) (k t : ℝ) : ℝ :=
  (amplitude t - amplitude 0) * chapterVIQuadraticPinchIntegrand k t

/-- The elementary primitive behind the logarithmic local model. -/
theorem hasDerivAt_chapterVIQuadraticPinchPrimitive
    {k : ℝ} (hk : 0 < k) (t : ℝ) :
    HasDerivAt (fun x ↦ Real.arsinh (x / Real.sqrt k))
      (chapterVIQuadraticPinchIntegrand k t) t := by
  have hsqrt : 0 < Real.sqrt k := Real.sqrt_pos.2 hk
  have hquotient :
      Real.sqrt (1 + (t / Real.sqrt k) ^ 2) =
        Real.sqrt (t ^ 2 + k) / Real.sqrt k := by
    rw [← Real.sqrt_div (by positivity) k]
    congr 1
    field_simp [hsqrt.ne']
    nlinarith [Real.sq_sqrt hk.le]
  refine ((Real.hasDerivAt_arsinh (t / Real.sqrt k)).comp t
    ((hasDerivAt_id t).div_const (Real.sqrt k))).congr_deriv ?_
  change (Real.sqrt (1 + (t / Real.sqrt k) ^ 2))⁻¹ * (1 / Real.sqrt k) =
    (Real.sqrt (t ^ 2 + k))⁻¹
  rw [hquotient]
  field_simp [hsqrt.ne']

/-- The quadratic-pinch integrand is continuous when `k > 0`. -/
theorem continuous_chapterVIQuadraticPinchIntegrand
    {k : ℝ} (hk : 0 < k) : Continuous (chapterVIQuadraticPinchIntegrand k) := by
  unfold chapterVIQuadraticPinchIntegrand
  apply Continuous.inv₀ ((continuous_id.pow 2).add continuous_const).sqrt
  intro t
  change Real.sqrt (t ^ 2 + k) ≠ 0
  exact Real.sqrt_ne_zero'.mpr (by nlinarith [sq_nonneg t])

/-- A continuous amplitude gives continuous weighted and remainder integrands away from the
singular parameter. -/
theorem continuous_chapterVIWeightedQuadraticPinchIntegrand
    {amplitude : ℝ → ℝ} (hamplitude : Continuous amplitude)
    {k : ℝ} (hk : 0 < k) :
    Continuous (chapterVIWeightedQuadraticPinchIntegrand amplitude k) := by
  exact hamplitude.mul (continuous_chapterVIQuadraticPinchIntegrand hk)

theorem continuous_chapterVIQuadraticPinchAmplitudeRemainder
    {amplitude : ℝ → ℝ} (hamplitude : Continuous amplitude)
    {k : ℝ} (hk : 0 < k) :
    Continuous (chapterVIQuadraticPinchAmplitudeRemainder amplitude k) := by
  exact (hamplitude.sub continuous_const).mul
    (continuous_chapterVIQuadraticPinchIntegrand hk)

/-- Exact extraction of the amplitude's value at the pinch.  This is the elementary real-model
counterpart of extracting Poincaré's nonzero analytic unit from the prepared local integral. -/
theorem integral_chapterVIWeightedQuadraticPinchIntegrand_eq
    {amplitude : ℝ → ℝ} (hamplitude : Continuous amplitude)
    {k : ℝ} (hk : 0 < k) (a b : ℝ) :
    (∫ t in a..b, chapterVIWeightedQuadraticPinchIntegrand amplitude k t) =
      amplitude 0 * (∫ t in a..b, chapterVIQuadraticPinchIntegrand k t) +
        ∫ t in a..b, chapterVIQuadraticPinchAmplitudeRemainder amplitude k t := by
  have hconstant : Continuous
      (fun t ↦ amplitude 0 * chapterVIQuadraticPinchIntegrand k t) :=
    continuous_const.mul (continuous_chapterVIQuadraticPinchIntegrand hk)
  have hremainder :=
    continuous_chapterVIQuadraticPinchAmplitudeRemainder hamplitude hk
  calc
    (∫ t in a..b, chapterVIWeightedQuadraticPinchIntegrand amplitude k t) =
        ∫ t in a..b,
          amplitude 0 * chapterVIQuadraticPinchIntegrand k t +
            chapterVIQuadraticPinchAmplitudeRemainder amplitude k t := by
      apply intervalIntegral.integral_congr
      intro t _
      simp only [chapterVIWeightedQuadraticPinchIntegrand,
        chapterVIQuadraticPinchAmplitudeRemainder]
      ring
    _ = (∫ t in a..b, amplitude 0 * chapterVIQuadraticPinchIntegrand k t) +
        ∫ t in a..b, chapterVIQuadraticPinchAmplitudeRemainder amplitude k t := by
      rw [intervalIntegral.integral_add
        (hconstant.intervalIntegrable a b) (hremainder.intervalIntegrable a b)]
    _ = amplitude 0 * (∫ t in a..b, chapterVIQuadraticPinchIntegrand k t) +
        ∫ t in a..b, chapterVIQuadraticPinchAmplitudeRemainder amplitude k t := by
      rw [intervalIntegral.integral_const_mul]

/-- A Lipschitz amplitude contributes only a uniformly bounded remainder to the real prepared
pinch integral.  The crucial estimate is `|t| / sqrt(t²+k) ≤ 1`. -/
theorem abs_integral_chapterVIQuadraticPinchAmplitudeRemainder_le
    {amplitude : ℝ → ℝ} {C k L : ℝ}
    (hC : 0 ≤ C) (hk : 0 < k) (hL : 0 ≤ L)
    (hLipschitz : ∀ t, |amplitude t - amplitude 0| ≤ C * |t|) :
    |∫ t in -L..L, chapterVIQuadraticPinchAmplitudeRemainder amplitude k t| ≤
      2 * C * L := by
  have hbound : ∀ t ∈ Ι (-L) L,
      ‖chapterVIQuadraticPinchAmplitudeRemainder amplitude k t‖ ≤ C := by
    intro t _
    have hpositive : 0 < t ^ 2 + k := by nlinarith [sq_nonneg t]
    have hsqrt : 0 < Real.sqrt (t ^ 2 + k) := Real.sqrt_pos.2 hpositive
    have ht_le : |t| ≤ Real.sqrt (t ^ 2 + k) := by
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt (by linarith)
    rw [Real.norm_eq_abs]
    simp only [chapterVIQuadraticPinchAmplitudeRemainder,
      chapterVIQuadraticPinchIntegrand, abs_mul, abs_inv,
      abs_of_nonneg (Real.sqrt_nonneg _)]
    rw [inv_eq_one_div, mul_div]
    simp only [mul_one]
    apply (div_le_div_of_nonneg_right (hLipschitz t) hsqrt.le).trans
    rw [div_le_iff₀ hsqrt]
    nlinarith
  have hintegral := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  rw [Real.norm_eq_abs] at hintegral
  calc
    |∫ t in -L..L, chapterVIQuadraticPinchAmplitudeRemainder amplitude k t| ≤
        C * |L - -L| := hintegral
    _ = 2 * C * L := by rw [abs_of_nonneg (by linarith)]; ring

/-- Exact evaluation of the real quadratic-pinch integral. -/
theorem integral_chapterVIQuadraticPinchIntegrand
    {k : ℝ} (hk : 0 < k) (a b : ℝ) :
    ∫ t in a..b, chapterVIQuadraticPinchIntegrand k t =
      Real.arsinh (b / Real.sqrt k) - Real.arsinh (a / Real.sqrt k) := by
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ ↦ hasDerivAt_chapterVIQuadraticPinchPrimitive hk t)
    ((continuous_chapterVIQuadraticPinchIntegrand hk).intervalIntegrable a b)

/-- On a symmetric interval, the local integral is twice an inverse hyperbolic sine. -/
theorem integral_chapterVIQuadraticPinchIntegrand_symmetric
    {k L : ℝ} (hk : 0 < k) :
    ∫ t in -L..L, chapterVIQuadraticPinchIntegrand k t =
      2 * Real.arsinh (L / Real.sqrt k) := by
  rw [integral_chapterVIQuadraticPinchIntegrand hk]
  rw [show -L / Real.sqrt k = -(L / Real.sqrt k) by ring, Real.arsinh_neg]
  ring

/-- The symmetric local integral contains an exact `-log k` term. The remaining term is
continuous and finite at `k = 0` when `L > 0`. -/
theorem chapterVI_quadraticPinch_logarithmic_decomposition
    {k L : ℝ} (hk : 0 < k) (hL : 0 < L) :
    2 * Real.arsinh (L / Real.sqrt k) =
      -Real.log k + 2 * Real.log (L + Real.sqrt (L ^ 2 + k)) := by
  have hsqrt : 0 < Real.sqrt k := Real.sqrt_pos.2 hk
  have hsum : 0 < L + Real.sqrt (L ^ 2 + k) :=
    add_pos_of_pos_of_nonneg hL (Real.sqrt_nonneg _)
  have hquotient :
      Real.sqrt (1 + (L / Real.sqrt k) ^ 2) =
        Real.sqrt (L ^ 2 + k) / Real.sqrt k := by
    rw [← Real.sqrt_div (by positivity) k]
    congr 1
    field_simp [hsqrt.ne']
    nlinarith [Real.sq_sqrt hk.le]
  rw [Real.arsinh, hquotient]
  have hcombine : L / Real.sqrt k + Real.sqrt (L ^ 2 + k) / Real.sqrt k =
      (L + Real.sqrt (L ^ 2 + k)) / Real.sqrt k := by ring
  rw [hcombine, Real.log_div hsum.ne' hsqrt.ne', Real.log_sqrt hk.le]
  ring

/-- The nonsingular part of the quadratic-pinch integral converges to its finite boundary value.
Together with `chapterVI_quadraticPinch_logarithmic_decomposition`, this identifies the exact
leading logarithm of the real model. -/
theorem tendsto_chapterVI_quadraticPinch_regularPart
    {L : ℝ} (hL : 0 < L) :
    Tendsto (fun k : ℝ ↦ 2 * Real.log (L + Real.sqrt (L ^ 2 + k)))
      (𝓝[>] 0) (𝓝 (2 * Real.log (2 * L))) := by
  have hinner : ContinuousAt (fun k : ℝ ↦ L + Real.sqrt (L ^ 2 + k)) 0 := by
    fun_prop
  have hvalue : L + Real.sqrt (L ^ 2 + 0) = 2 * L := by
    rw [add_zero, Real.sqrt_sq hL.le]
    ring
  have hnonzero : L + Real.sqrt (L ^ 2 + 0) ≠ 0 := by
    rw [hvalue]
    positivity
  have hcontinuous :
      ContinuousAt (fun k : ℝ ↦ 2 * Real.log (L + Real.sqrt (L ^ 2 + k))) 0 :=
    continuousAt_const.mul (hinner.log hnonzero)
  have htendsto := hcontinuous.continuousWithinAt (s := Set.Ioi 0)
  change Tendsto (fun k : ℝ ↦ 2 * Real.log (L + Real.sqrt (L ^ 2 + k)))
    (𝓝[>] 0) (𝓝 (2 * Real.log (L + Real.sqrt (L ^ 2 + 0)))) at htendsto
  rw [hvalue] at htendsto
  exact htendsto

/-- The exact logarithmic asymptotic of the integrated real quadratic-pinch model. -/
theorem tendsto_chapterVI_quadraticPinch_sub_log
    {L : ℝ} (hL : 0 < L) :
    Tendsto
      (fun k : ℝ ↦
        (∫ t in -L..L, chapterVIQuadraticPinchIntegrand k t) + Real.log k)
      (𝓝[>] 0) (𝓝 (2 * Real.log (2 * L))) := by
  apply (tendsto_chapterVI_quadraticPinch_regularPart hL).congr'
  filter_upwards [self_mem_nhdsWithin] with k hk
  have hkpos : 0 < k := hk
  rw [integral_chapterVIQuadraticPinchIntegrand_symmetric hkpos,
    chapterVI_quadraticPinch_logarithmic_decomposition hkpos hL]
  ring

/-- The bare quadratic-pinch integral has leading coefficient one relative to `-log k`. -/
theorem tendsto_chapterVI_quadraticPinch_div_neg_log
    {L : ℝ} (hL : 0 < L) :
    Tendsto
      (fun k : ℝ ↦
        (∫ t in -L..L, chapterVIQuadraticPinchIntegrand k t) / (-Real.log k))
      (𝓝[>] 0) (𝓝 1) := by
  have hdenominator : Tendsto (fun k : ℝ ↦ -Real.log k) (𝓝[>] 0) atTop := by
    apply tendsto_neg_atTop_iff.mpr
    exact Real.tendsto_log_nhdsGT_zero
  have hregularRatio :=
    (tendsto_chapterVI_quadraticPinch_sub_log hL).div_atTop hdenominator
  have hsum : Tendsto
      (fun k : ℝ ↦ 1 +
        ((∫ t in -L..L, chapterVIQuadraticPinchIntegrand k t) + Real.log k) /
          (-Real.log k))
      (𝓝[>] 0) (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).add hregularRatio
  apply hsum.congr'
  filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with k hk
  have hlog : Real.log k ≠ 0 := (Real.log_neg hk.1 hk.2).ne
  field_simp [hlog]
  ring

/-- Multiplication by a continuous Lipschitz unit changes the leading logarithmic coefficient by
exactly its value at the pinch.  In particular, a nonzero analytic unit cannot turn the genuine
real quadratic pinch into an apparent singularity.

This proves the analytic-unit part of Poincaré's local calculation for a fixed real symmetric
cycle.  The source theorem still needs parameter dependence, complex square-root branches, and
cycle transport. -/
theorem tendsto_chapterVI_weightedQuadraticPinch_div_neg_log
    {amplitude : ℝ → ℝ} {C L : ℝ}
    (hamplitude : Continuous amplitude) (hC : 0 ≤ C) (hL : 0 < L)
    (hLipschitz : ∀ t, |amplitude t - amplitude 0| ≤ C * |t|) :
    Tendsto
      (fun k : ℝ ↦
        (∫ t in -L..L, chapterVIWeightedQuadraticPinchIntegrand amplitude k t) /
          (-Real.log k))
      (𝓝[>] 0) (𝓝 (amplitude 0)) := by
  let remainder : ℝ → ℝ := fun k ↦
    ∫ t in -L..L, chapterVIQuadraticPinchAmplitudeRemainder amplitude k t
  have hdenominator : Tendsto (fun k : ℝ ↦ -Real.log k) (𝓝[>] 0) atTop := by
    apply tendsto_neg_atTop_iff.mpr
    exact Real.tendsto_log_nhdsGT_zero
  have hremainderBound : ∀ᶠ k in 𝓝[>] (0 : ℝ), |remainder k| ≤ 2 * C * L := by
    filter_upwards [self_mem_nhdsWithin] with k hk
    exact abs_integral_chapterVIQuadraticPinchAmplitudeRemainder_le
      hC hk hL.le hLipschitz
  have hremainderLower : ∀ᶠ k in 𝓝[>] (0 : ℝ), -(2 * C * L) ≤ remainder k :=
    hremainderBound.mono fun _ hk ↦ (abs_le.mp hk).1
  have hremainderUpper : ∀ᶠ k in 𝓝[>] (0 : ℝ), remainder k ≤ 2 * C * L :=
    hremainderBound.mono fun _ hk ↦ (abs_le.mp hk).2
  have hremainderRatio :
      Tendsto (fun k ↦ remainder k / (-Real.log k)) (𝓝[>] 0) (𝓝 0) :=
    tendsto_bdd_div_atTop_nhds_zero
      hremainderLower hremainderUpper hdenominator
  have hbaseRatio := tendsto_chapterVI_quadraticPinch_div_neg_log hL
  have hcombined :
      Tendsto
        (fun k ↦ amplitude 0 *
            ((∫ t in -L..L, chapterVIQuadraticPinchIntegrand k t) / (-Real.log k)) +
          remainder k / (-Real.log k))
        (𝓝[>] 0) (𝓝 (amplitude 0)) := by
    simpa using (hbaseRatio.const_mul (amplitude 0)).add hremainderRatio
  apply hcombined.congr'
  filter_upwards [self_mem_nhdsWithin] with k hk
  rw [integral_chapterVIWeightedQuadraticPinchIntegrand_eq hamplitude hk]
  change amplitude 0 *
        ((∫ t in -L..L, chapterVIQuadraticPinchIntegrand k t) / (-Real.log k)) +
      remainder k / (-Real.log k) =
    (amplitude 0 * (∫ t in -L..L, chapterVIQuadraticPinchIntegrand k t) +
      remainder k) / (-Real.log k)
  ring

end PoincareChapterVI
