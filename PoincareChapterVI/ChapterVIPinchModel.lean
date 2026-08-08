/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.Calculus.ContDiff.RCLike
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

/-- The prepared pinch with an amplitude taking values in a complete real normed space.  Taking
`E = ℂ` gives the complex-valued amplitude in Poincaré's contour integral.  The first argument of
`amplitude` is the external singular parameter and the second is the local contour coordinate. -/
def chapterVIParametricQuadraticPinchIntegrand
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (amplitude : ℝ → ℝ → E) (k t : ℝ) : E :=
  chapterVIQuadraticPinchIntegrand k t • amplitude k t

/-- The part left after extracting the parameter-dependent center value `amplitude k 0`. -/
def chapterVIParametricQuadraticPinchRemainder
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (amplitude : ℝ → ℝ → E) (k t : ℝ) : E :=
  chapterVIQuadraticPinchIntegrand k t • (amplitude k t - amplitude k 0)

/-- The prepared local pinch before translating Poincaré's moving center `h(k)` to zero. -/
def chapterVIMovingCenteredQuadraticPinchIntegrand
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (amplitude : ℝ → ℝ → E) (center : ℝ → ℝ) (k t : ℝ) : E :=
  chapterVIQuadraticPinchIntegrand k (t - center k) • amplitude k t

/-- Translation by the moving center identifies the moving local interval exactly with the fixed
symmetric prepared pinch.  This is the affine cycle-transport step implicit in §99. -/
theorem integral_chapterVIMovingCenteredQuadraticPinchIntegrand_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (amplitude : ℝ → ℝ → E) (center : ℝ → ℝ) (k L : ℝ) :
    (∫ t in center k - L..center k + L,
      chapterVIMovingCenteredQuadraticPinchIntegrand amplitude center k t) =
    ∫ u in -L..L,
      chapterVIParametricQuadraticPinchIntegrand
        (fun parameter coordinate ↦ amplitude parameter (coordinate + center parameter)) k u := by
  calc
    (∫ t in center k - L..center k + L,
        chapterVIMovingCenteredQuadraticPinchIntegrand amplitude center k t) =
      ∫ t in -L + center k..L + center k,
        chapterVIMovingCenteredQuadraticPinchIntegrand amplitude center k t := by
      congr 1 <;> ring
    _ = ∫ u in -L..L,
        chapterVIMovingCenteredQuadraticPinchIntegrand amplitude center k (u + center k) := by
      exact (intervalIntegral.integral_comp_add_right
        (chapterVIMovingCenteredQuadraticPinchIntegrand amplitude center k) (center k)).symm
    _ = ∫ u in -L..L,
        chapterVIParametricQuadraticPinchIntegrand
          (fun parameter coordinate ↦ amplitude parameter (coordinate + center parameter)) k u := by
      apply intervalIntegral.integral_congr
      intro u _
      simp only [chapterVIMovingCenteredQuadraticPinchIntegrand,
        chapterVIParametricQuadraticPinchIntegrand, add_sub_cancel_right]

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

/-- Continuity of the vector-valued prepared integrand for each positive parameter. -/
theorem continuous_chapterVIParametricQuadraticPinchIntegrand
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {amplitude : ℝ → ℝ → E} {k : ℝ}
    (hamplitude : Continuous (amplitude k)) (hk : 0 < k) :
    Continuous (chapterVIParametricQuadraticPinchIntegrand amplitude k) := by
  exact (continuous_chapterVIQuadraticPinchIntegrand hk).smul hamplitude

/-- Continuity of the vector-valued varying-amplitude remainder. -/
theorem continuous_chapterVIParametricQuadraticPinchRemainder
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {amplitude : ℝ → ℝ → E} {k : ℝ}
    (hamplitude : Continuous (amplitude k)) (hk : 0 < k) :
    Continuous (chapterVIParametricQuadraticPinchRemainder amplitude k) := by
  exact (continuous_chapterVIQuadraticPinchIntegrand hk).smul
    (hamplitude.sub continuous_const)

/-- Exact extraction of the center value from a vector-valued, parameter-dependent prepared
pinch. -/
theorem integral_chapterVIParametricQuadraticPinchIntegrand_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {amplitude : ℝ → ℝ → E} {k : ℝ}
    (hamplitude : Continuous (amplitude k)) (hk : 0 < k) (a b : ℝ) :
    (∫ t in a..b, chapterVIParametricQuadraticPinchIntegrand amplitude k t) =
      (∫ t in a..b, chapterVIQuadraticPinchIntegrand k t) • amplitude k 0 +
        ∫ t in a..b, chapterVIParametricQuadraticPinchRemainder amplitude k t := by
  have hconstant : Continuous
      (fun t ↦ chapterVIQuadraticPinchIntegrand k t • amplitude k 0) :=
    (continuous_chapterVIQuadraticPinchIntegrand hk).smul continuous_const
  have hremainder :=
    continuous_chapterVIParametricQuadraticPinchRemainder hamplitude hk
  calc
    (∫ t in a..b, chapterVIParametricQuadraticPinchIntegrand amplitude k t) =
        ∫ t in a..b,
          chapterVIQuadraticPinchIntegrand k t • amplitude k 0 +
            chapterVIParametricQuadraticPinchRemainder amplitude k t := by
      apply intervalIntegral.integral_congr
      intro t _
      simp only [chapterVIParametricQuadraticPinchIntegrand,
        chapterVIParametricQuadraticPinchRemainder, smul_sub]
      abel
    _ = (∫ t in a..b, chapterVIQuadraticPinchIntegrand k t • amplitude k 0) +
        ∫ t in a..b, chapterVIParametricQuadraticPinchRemainder amplitude k t := by
      rw [intervalIntegral.integral_add
        (hconstant.intervalIntegrable a b) (hremainder.intervalIntegrable a b)]
    _ = (∫ t in a..b, chapterVIQuadraticPinchIntegrand k t) • amplitude k 0 +
        ∫ t in a..b, chapterVIParametricQuadraticPinchRemainder amplitude k t := by
      rw [intervalIntegral.integral_smul_const]

/-- Local form of `integral_chapterVIParametricQuadraticPinchIntegrand_eq`.  Only continuity on
the interval of integration is mathematically needed.  This form is what applies to an analytic
germ produced by the local Morse coordinate: no arbitrary extension of that germ to the whole
real line is required. -/
theorem integral_chapterVIParametricQuadraticPinchIntegrand_eq_of_continuousOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {amplitude : ℝ → ℝ → E} {k a b : ℝ}
    (hamplitude : ContinuousOn (amplitude k) (Set.uIcc a b)) (hk : 0 < k) :
    (∫ t in a..b, chapterVIParametricQuadraticPinchIntegrand amplitude k t) =
      (∫ t in a..b, chapterVIQuadraticPinchIntegrand k t) • amplitude k 0 +
        ∫ t in a..b, chapterVIParametricQuadraticPinchRemainder amplitude k t := by
  have hkernel : Continuous
      (fun t ↦ chapterVIQuadraticPinchIntegrand k t) :=
    continuous_chapterVIQuadraticPinchIntegrand hk
  have hconstant : Continuous
      (fun t ↦ chapterVIQuadraticPinchIntegrand k t • amplitude k 0) :=
    hkernel.smul continuous_const
  have hremainder : ContinuousOn
      (chapterVIParametricQuadraticPinchRemainder amplitude k) (Set.uIcc a b) :=
    hkernel.continuousOn.smul (hamplitude.sub continuousOn_const)
  calc
    (∫ t in a..b, chapterVIParametricQuadraticPinchIntegrand amplitude k t) =
        ∫ t in a..b,
          chapterVIQuadraticPinchIntegrand k t • amplitude k 0 +
            chapterVIParametricQuadraticPinchRemainder amplitude k t := by
      apply intervalIntegral.integral_congr
      intro t _
      simp only [chapterVIParametricQuadraticPinchIntegrand,
        chapterVIParametricQuadraticPinchRemainder, smul_sub]
      abel
    _ = (∫ t in a..b, chapterVIQuadraticPinchIntegrand k t • amplitude k 0) +
        ∫ t in a..b, chapterVIParametricQuadraticPinchRemainder amplitude k t := by
      rw [intervalIntegral.integral_add
        (hconstant.intervalIntegrable a b) hremainder.intervalIntegrable]
    _ = (∫ t in a..b, chapterVIQuadraticPinchIntegrand k t) • amplitude k 0 +
        ∫ t in a..b, chapterVIParametricQuadraticPinchRemainder amplitude k t := by
      rw [intervalIntegral.integral_smul_const]

/-- A uniform Lipschitz estimate in the contour coordinate makes the vector-valued remainder
uniformly bounded as the pinch parameter tends to zero. -/
theorem norm_integral_chapterVIParametricQuadraticPinchRemainder_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {amplitude : ℝ → ℝ → E} {C k L : ℝ}
    (hC : 0 ≤ C) (hk : 0 < k) (hL : 0 ≤ L)
    (hLipschitz : ∀ t ∈ Ι (-L) L,
      ‖amplitude k t - amplitude k 0‖ ≤ C * |t|) :
    ‖∫ t in -L..L, chapterVIParametricQuadraticPinchRemainder amplitude k t‖ ≤
      2 * C * L := by
  have hbound : ∀ t ∈ Ι (-L) L,
      ‖chapterVIParametricQuadraticPinchRemainder amplitude k t‖ ≤ C := by
    intro t _
    have hpositive : 0 < t ^ 2 + k := by nlinarith [sq_nonneg t]
    have hsqrt : 0 < Real.sqrt (t ^ 2 + k) := Real.sqrt_pos.2 hpositive
    have ht_le : |t| ≤ Real.sqrt (t ^ 2 + k) := by
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt (by linarith)
    simp only [chapterVIParametricQuadraticPinchRemainder,
      chapterVIQuadraticPinchIntegrand, norm_smul, Real.norm_eq_abs, abs_inv,
      abs_of_nonneg (Real.sqrt_nonneg _)]
    rw [mul_comm]
    rw [inv_eq_one_div, mul_div]
    simp only [mul_one]
    apply (div_le_div_of_nonneg_right (hLipschitz t ‹t ∈ Ι (-L) L›) hsqrt.le).trans
    rw [div_le_iff₀ hsqrt]
    nlinarith
  have hintegral := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  calc
    ‖∫ t in -L..L, chapterVIParametricQuadraticPinchRemainder amplitude k t‖ ≤
        C * |L - -L| := hintegral
    _ = 2 * C * L := by rw [abs_of_nonneg (by linarith)]; ring

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

/-- A `C¹` amplitude on a compact parameter-contour rectangle has one Lipschitz constant in the
contour coordinate, uniformly in the parameter.  This supplies rather than assumes the estimate
used to bound the nonsingular remainder in Poincare's prepared integral. -/
theorem exists_uniform_chapterVI_contour_lipschitz_of_contDiffOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {amplitude : ℝ × ℝ → E} {δ L : ℝ}
    (hL : 0 ≤ L)
    (hamplitude : ContDiffOn ℝ 1 amplitude (Set.Icc 0 δ ×ˢ Set.uIcc (-L) L)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k ∈ Set.Icc 0 δ, ∀ t ∈ Ι (-L) L,
      ‖amplitude (k, t) - amplitude (k, 0)‖ ≤ C * |t| := by
  have hconvex : Convex ℝ (Set.Icc (0 : ℝ) δ ×ˢ Set.uIcc (-L) L) :=
    (convex_Icc 0 δ).prod (convex_uIcc (𝕜 := ℝ) (-L) L)
  have hcompact : IsCompact (Set.Icc (0 : ℝ) δ ×ˢ Set.uIcc (-L) L) :=
    isCompact_Icc.prod isCompact_uIcc
  rcases hamplitude.exists_lipschitzOnWith one_ne_zero hconvex hcompact with
    ⟨K, hK⟩
  refine ⟨(K : ℝ), K.coe_nonneg, ?_⟩
  intro k hk t ht
  have hzero : (0 : ℝ) ∈ Set.uIcc (-L) L := by
    rw [uIcc_of_le (by linarith)]
    exact ⟨by linarith, hL⟩
  have hdist := hK.dist_le_mul (k, t) ⟨hk, uIoc_subset_uIcc ht⟩
    (k, 0) ⟨hk, hzero⟩
  simpa [dist_eq_norm, Prod.norm_def, Real.norm_eq_abs] using hdist

/-- Core source-facing local limit in which the uniform contour-coordinate estimate is needed
only eventually as the positive pinch parameter tends to zero, and only on the interval actually
integrated. -/
theorem tendsto_chapterVI_parametricQuadraticPinch_inv_neg_log_smul_of_eventually_lipschitz
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {amplitude : ℝ → ℝ → E} {center : E} {C L : ℝ}
    (hamplitude : ∀ k, 0 < k → Continuous (amplitude k))
    (hcenter : Tendsto (fun k ↦ amplitude k 0) (𝓝[>] 0) (𝓝 center))
    (hC : 0 ≤ C) (hL : 0 < L)
    (hLipschitz : ∀ᶠ k in 𝓝[>] (0 : ℝ), ∀ t ∈ Ι (-L) L,
      ‖amplitude k t - amplitude k 0‖ ≤ C * |t|) :
    Tendsto
      (fun k : ℝ ↦ (-Real.log k)⁻¹ •
        (∫ t in -L..L, chapterVIParametricQuadraticPinchIntegrand amplitude k t))
      (𝓝[>] 0) (𝓝 center) := by
  let remainder : ℝ → E := fun k ↦
    ∫ t in -L..L, chapterVIParametricQuadraticPinchRemainder amplitude k t
  have hdenominator : Tendsto (fun k : ℝ ↦ -Real.log k) (𝓝[>] 0) atTop := by
    apply tendsto_neg_atTop_iff.mpr
    exact Real.tendsto_log_nhdsGT_zero
  have hremainderBound : ∀ᶠ k in 𝓝[>] (0 : ℝ), ‖remainder k‖ ≤ 2 * C * L := by
    filter_upwards [self_mem_nhdsWithin, hLipschitz] with k hk hkLipschitz
    exact norm_integral_chapterVIParametricQuadraticPinchRemainder_le
      hC hk hL.le hkLipschitz
  have hremainderBounded :
      IsBoundedUnder (· ≤ ·) (𝓝[>] (0 : ℝ)) (norm ∘ remainder) := by
    apply isBoundedUnder_of_eventually_le (a := 2 * C * L)
    simpa [Function.comp_def] using hremainderBound
  have hinverse :
      Tendsto (fun k : ℝ ↦ (-Real.log k)⁻¹) (𝓝[>] 0) (𝓝 0) :=
    hdenominator.inv_tendsto_atTop
  have hremainderRatio :
      Tendsto (fun k ↦ (-Real.log k)⁻¹ • remainder k) (𝓝[>] 0) (𝓝 0) :=
    hinverse.zero_smul_isBoundedUnder_le hremainderBounded
  have hbaseRatio := tendsto_chapterVI_quadraticPinch_div_neg_log hL
  have hmain : Tendsto
      (fun k ↦
        ((∫ t in -L..L, chapterVIQuadraticPinchIntegrand k t) / (-Real.log k)) •
          amplitude k 0)
      (𝓝[>] 0) (𝓝 center) := by
    simpa using hbaseRatio.smul hcenter
  have hcombined : Tendsto
      (fun k ↦
        ((∫ t in -L..L, chapterVIQuadraticPinchIntegrand k t) / (-Real.log k)) •
            amplitude k 0 +
          (-Real.log k)⁻¹ • remainder k)
      (𝓝[>] 0) (𝓝 center) := by
    simpa using hmain.add hremainderRatio
  apply hcombined.congr'
  filter_upwards [self_mem_nhdsWithin] with k hk
  rw [integral_chapterVIParametricQuadraticPinchIntegrand_eq
    (hamplitude k hk) hk]
  change ((∫ t in -L..L, chapterVIQuadraticPinchIntegrand k t) / (-Real.log k)) •
        amplitude k 0 + (-Real.log k)⁻¹ • remainder k =
    (-Real.log k)⁻¹ •
      ((∫ t in -L..L, chapterVIQuadraticPinchIntegrand k t) • amplitude k 0 +
        remainder k)
  rw [smul_add, smul_smul]
  congr 1
  rw [div_eq_mul_inv, mul_comm]

/-- Local-continuity version of the parametric pinch theorem.  The amplitude is required to be
continuous only on the fixed middle interval.  This is the form appropriate for Poincare's
locally prepared analytic germ. -/
theorem tendsto_chapterVI_parametricQuadraticPinch_inv_neg_log_smul_of_eventually_lipschitzOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {amplitude : ℝ → ℝ → E} {center : E} {C L : ℝ}
    (hamplitude : ∀ᶠ k in 𝓝[>] (0 : ℝ),
      ContinuousOn (amplitude k) (Set.uIcc (-L) L))
    (hcenter : Tendsto (fun k ↦ amplitude k 0) (𝓝[>] 0) (𝓝 center))
    (hC : 0 ≤ C) (hL : 0 < L)
    (hLipschitz : ∀ᶠ k in 𝓝[>] (0 : ℝ), ∀ t ∈ Ι (-L) L,
      ‖amplitude k t - amplitude k 0‖ ≤ C * |t|) :
    Tendsto
      (fun k : ℝ ↦ (-Real.log k)⁻¹ •
        (∫ t in -L..L, chapterVIParametricQuadraticPinchIntegrand amplitude k t))
      (𝓝[>] 0) (𝓝 center) := by
  let remainder : ℝ → E := fun k ↦
    ∫ t in -L..L, chapterVIParametricQuadraticPinchRemainder amplitude k t
  have hdenominator : Tendsto (fun k : ℝ ↦ -Real.log k) (𝓝[>] 0) atTop := by
    apply tendsto_neg_atTop_iff.mpr
    exact Real.tendsto_log_nhdsGT_zero
  have hremainderBound : ∀ᶠ k in 𝓝[>] (0 : ℝ), ‖remainder k‖ ≤ 2 * C * L := by
    filter_upwards [self_mem_nhdsWithin, hLipschitz] with k hk hkLipschitz
    exact norm_integral_chapterVIParametricQuadraticPinchRemainder_le
      hC hk hL.le hkLipschitz
  have hremainderBounded :
      IsBoundedUnder (· ≤ ·) (𝓝[>] (0 : ℝ)) (norm ∘ remainder) := by
    apply isBoundedUnder_of_eventually_le (a := 2 * C * L)
    simpa [Function.comp_def] using hremainderBound
  have hinverse :
      Tendsto (fun k : ℝ ↦ (-Real.log k)⁻¹) (𝓝[>] 0) (𝓝 0) :=
    hdenominator.inv_tendsto_atTop
  have hremainderRatio :
      Tendsto (fun k ↦ (-Real.log k)⁻¹ • remainder k) (𝓝[>] 0) (𝓝 0) :=
    hinverse.zero_smul_isBoundedUnder_le hremainderBounded
  have hbaseRatio := tendsto_chapterVI_quadraticPinch_div_neg_log hL
  have hmain : Tendsto
      (fun k ↦
        ((∫ t in -L..L, chapterVIQuadraticPinchIntegrand k t) / (-Real.log k)) •
          amplitude k 0)
      (𝓝[>] 0) (𝓝 center) := by
    simpa using hbaseRatio.smul hcenter
  have hcombined : Tendsto
      (fun k ↦
        ((∫ t in -L..L, chapterVIQuadraticPinchIntegrand k t) / (-Real.log k)) •
            amplitude k 0 +
          (-Real.log k)⁻¹ • remainder k)
      (𝓝[>] 0) (𝓝 center) := by
    simpa using hmain.add hremainderRatio
  apply hcombined.congr'
  filter_upwards [self_mem_nhdsWithin, hamplitude] with k hk hkcontinuous
  rw [integral_chapterVIParametricQuadraticPinchIntegrand_eq_of_continuousOn
    hkcontinuous hk]
  change ((∫ t in -L..L, chapterVIQuadraticPinchIntegrand k t) / (-Real.log k)) •
        amplitude k 0 + (-Real.log k)⁻¹ • remainder k =
    (-Real.log k)⁻¹ •
      ((∫ t in -L..L, chapterVIQuadraticPinchIntegrand k t) • amplitude k 0 +
        remainder k)
  rw [smul_add, smul_smul]
  congr 1
  rw [div_eq_mul_inv, mul_comm]

/-- A `C¹` realization of the prepared amplitude on one compact parameter-contour rectangle
automatically satisfies the uniform remainder estimate and therefore has Poincare's logarithmic
pinch limit.  This removes the hand-supplied Lipschitz constant from the source-facing analytic
application. -/
theorem tendsto_chapterVI_parametricQuadraticPinch_inv_neg_log_smul_of_contDiffOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {amplitude : ℝ × ℝ → E} {center : E} {δ L : ℝ}
    (hamplitude : ∀ k, 0 < k → Continuous (fun t ↦ amplitude (k, t)))
    (hcenter : Tendsto (fun k ↦ amplitude (k, 0)) (𝓝[>] 0) (𝓝 center))
    (hδ : 0 < δ) (hL : 0 < L)
    (hcontDiff : ContDiffOn ℝ 1 amplitude
      (Set.Icc 0 δ ×ˢ Set.uIcc (-L) L)) :
    Tendsto
      (fun k : ℝ ↦ (-Real.log k)⁻¹ •
        (∫ t in -L..L,
          chapterVIParametricQuadraticPinchIntegrand
            (fun parameter coordinate ↦ amplitude (parameter, coordinate)) k t))
      (𝓝[>] 0) (𝓝 center) := by
  rcases exists_uniform_chapterVI_contour_lipschitz_of_contDiffOn hL.le hcontDiff with
    ⟨C, hC, hCuniform⟩
  apply
    tendsto_chapterVI_parametricQuadraticPinch_inv_neg_log_smul_of_eventually_lipschitz
      hamplitude hcenter hC hL
  filter_upwards [Ioc_mem_nhdsGT hδ] with k hk
  intro t ht
  exact hCuniform k ⟨hk.1.le, hk.2⟩ t ht

/-- A `C¹` amplitude on the compact local rectangle has Poincare's logarithmic limit without any
global-continuity premise. -/
theorem tendsto_chapterVI_parametricQuadraticPinch_inv_neg_log_smul_of_contDiffOn_local
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {amplitude : ℝ × ℝ → E} {center : E} {δ L : ℝ}
    (hcenter : Tendsto (fun k ↦ amplitude (k, 0)) (𝓝[>] 0) (𝓝 center))
    (hδ : 0 < δ) (hL : 0 < L)
    (hcontDiff : ContDiffOn ℝ 1 amplitude
      (Set.Icc 0 δ ×ˢ Set.uIcc (-L) L)) :
    Tendsto
      (fun k : ℝ ↦ (-Real.log k)⁻¹ •
        (∫ t in -L..L,
          chapterVIParametricQuadraticPinchIntegrand
            (fun parameter coordinate ↦ amplitude (parameter, coordinate)) k t))
      (𝓝[>] 0) (𝓝 center) := by
  rcases exists_uniform_chapterVI_contour_lipschitz_of_contDiffOn hL.le hcontDiff with
    ⟨C, hC, hCuniform⟩
  apply
    tendsto_chapterVI_parametricQuadraticPinch_inv_neg_log_smul_of_eventually_lipschitzOn
      (amplitude := fun parameter coordinate ↦ amplitude (parameter, coordinate))
      (center := center) (C := C) ?_ hcenter hC hL
  · filter_upwards [Ioc_mem_nhdsGT hδ] with k hk
    intro t ht
    exact hCuniform k ⟨hk.1.le, hk.2⟩ t ht
  · filter_upwards [Ioc_mem_nhdsGT hδ] with k hk
    exact hcontDiff.continuousOn.comp
      (continuous_const.prodMk continuous_id).continuousOn (fun t ht ↦ by
        exact ⟨⟨hk.1.le, hk.2⟩, ht⟩)

/-- Source-facing vector-valued local limit.  The amplitude may depend on the external pinch
parameter, its center value need only converge, and its variation in the contour coordinate is
controlled by one uniform Lipschitz constant.  The theorem applies in particular to `E = ℂ`.

Thus, on the fixed real symmetric local cycle, the coefficient of `-log k` is the limiting value
of the analytic unit at the pinch.  No finite-dimensional approximation of the amplitude is used.
-/
theorem tendsto_chapterVI_parametricQuadraticPinch_inv_neg_log_smul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {amplitude : ℝ → ℝ → E} {center : E} {C L : ℝ}
    (hamplitude : ∀ k, 0 < k → Continuous (amplitude k))
    (hcenter : Tendsto (fun k ↦ amplitude k 0) (𝓝[>] 0) (𝓝 center))
    (hC : 0 ≤ C) (hL : 0 < L)
    (hLipschitz : ∀ k, 0 < k → ∀ t,
      ‖amplitude k t - amplitude k 0‖ ≤ C * |t|) :
    Tendsto
      (fun k : ℝ ↦ (-Real.log k)⁻¹ •
        (∫ t in -L..L, chapterVIParametricQuadraticPinchIntegrand amplitude k t))
      (𝓝[>] 0) (𝓝 center) := by
  apply tendsto_chapterVI_parametricQuadraticPinch_inv_neg_log_smul_of_eventually_lipschitz
    hamplitude hcenter hC hL
  filter_upwards [self_mem_nhdsWithin] with k hk
  intro t _
  exact hLipschitz k hk t

/-- The logarithmic limit on Poincaré's moving centered interval.  The amplitude is allowed to be
complex-valued (or vector-valued), the center may move arbitrarily with the parameter, and only a
uniform Lipschitz estimate relative to that center is required. -/
theorem tendsto_chapterVI_movingCenteredQuadraticPinch_inv_neg_log_smul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {amplitude : ℝ → ℝ → E} {center : ℝ → ℝ} {centerValue : E} {C L : ℝ}
    (hamplitude : ∀ k, 0 < k → Continuous (amplitude k))
    (hcenterValue : Tendsto (fun k ↦ amplitude k (center k)) (𝓝[>] 0) (𝓝 centerValue))
    (hC : 0 ≤ C) (hL : 0 < L)
    (hLipschitz : ∀ k, 0 < k → ∀ t,
      ‖amplitude k t - amplitude k (center k)‖ ≤ C * |t - center k|) :
    Tendsto
      (fun k : ℝ ↦ (-Real.log k)⁻¹ •
        (∫ t in center k - L..center k + L,
          chapterVIMovingCenteredQuadraticPinchIntegrand amplitude center k t))
      (𝓝[>] 0) (𝓝 centerValue) := by
  let shiftedAmplitude : ℝ → ℝ → E := fun k u ↦ amplitude k (u + center k)
  have hshiftedContinuous : ∀ k, 0 < k → Continuous (shiftedAmplitude k) := by
    intro k hk
    exact (hamplitude k hk).comp (continuous_id.add continuous_const)
  have hshiftedCenter :
      Tendsto (fun k ↦ shiftedAmplitude k 0) (𝓝[>] 0) (𝓝 centerValue) := by
    simpa [shiftedAmplitude] using hcenterValue
  have hshiftedLipschitz : ∀ k, 0 < k → ∀ u,
      ‖shiftedAmplitude k u - shiftedAmplitude k 0‖ ≤ C * |u| := by
    intro k hk u
    simpa [shiftedAmplitude] using hLipschitz k hk (u + center k)
  have hfixed :=
    tendsto_chapterVI_parametricQuadraticPinch_inv_neg_log_smul
      hshiftedContinuous hshiftedCenter hC hL hshiftedLipschitz
  apply hfixed.congr'
  filter_upwards with k
  rw [integral_chapterVIMovingCenteredQuadraticPinchIntegrand_eq]

end PoincareChapterVI
