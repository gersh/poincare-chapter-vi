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

end PoincareChapterVI
