/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import PoincareChapterVI.ChapterVIDarboux
import PoincareChapterVI.ChapterVIDarbouxSpectrum

/-!
# From boundary logarithms to a finite Darboux spectrum

This file supplies the coefficient-transfer step between the local logarithms in Chapter VI,
§100 and the finite-spectrum uniqueness argument used in §102.  If all retained logarithmic
singularities lie on a circle of radius `R`, multiplication of the coefficient of `z^(n+1)` by
`(n+1) R^(n+1)` turns their contributions into a finite exponential sum on the unit circle.

An analytic remainder on a strictly larger disk is exponentially smaller after this
normalization.  Thus a decomposition into finitely many boundary logarithms and such an analytic
remainder gives exactly the `o(1)` finite-spectrum asymptotic required downstream.
-/

noncomputable section

open Filter
open scoped BigOperators NNReal Topology

namespace PoincareChapterVI

/-- Darboux normalization of the coefficient of `z^(index + 1)` at a positive real radius. -/
def chapterVINormalizedCoefficient (radius : ℝ≥0) (coefficient : ℕ → ℂ)
    (index : ℕ) : ℂ :=
  (index + 1 : ℂ) * (radius : ℂ) ^ (index + 1) * coefficient index

/-- The unit-circle base obtained from an inverse singularity on the radius-`R` circle. -/
def chapterVIUnitBase (radius : ℝ≥0) (singularityInverse : ℂ) : ℂ :=
  (radius : ℂ) * singularityInverse

/-- The leading weight produced by `amplitude * log (1 - z / singularity)`. -/
def chapterVILogSpectrumWeight (radius : ℝ≥0) (singularityInverse amplitude : ℂ) : ℂ :=
  -amplitude * chapterVIUnitBase radius singularityInverse

/-- Full Taylor coefficient sequence of `log (1 - z * singularityInverse)`.  Its constant term is
zero because division by zero is zero in Lean. -/
def chapterVILogTaylorCoefficient (singularityInverse : ℂ) (degree : ℕ) : ℂ :=
  -(singularityInverse ^ degree / degree)

@[simp] theorem chapterVILogTaylorCoefficient_succ
    (singularityInverse : ℂ) (index : ℕ) :
    chapterVILogTaylorCoefficient singularityInverse (index + 1) =
      chapterVILogSingularityCoefficient singularityInverse index := by
  unfold chapterVILogTaylorCoefficient chapterVILogSingularityCoefficient
  push_cast
  rfl

/-- The complete analytic germ of a boundary logarithm has the expected Taylor coefficients. -/
theorem hasFPowerSeriesAt_chapterVILogTaylorCoefficient (singularityInverse : ℂ) :
    HasFPowerSeriesAt (fun z : ℂ ↦ Complex.log (1 - z * singularityInverse))
      (FormalMultilinearSeries.ofScalars ℂ
        (chapterVILogTaylorCoefficient singularityInverse)) 0 := by
  let scale : ℂ →L[ℂ] ℂ :=
    (ContinuousLinearMap.lsmul ℂ ℂ) (-singularityInverse)
  have hbase : HasFPowerSeriesAt (fun z : ℂ ↦ Complex.log (1 + z))
      (FormalMultilinearSeries.ofScalars ℂ (fun n ↦ -(-1 : ℂ) ^ n / n))
      (scale 0) := by
    simpa [scale] using hasFPowerSeriesAt_clog_one_add
  have h := hbase.compContinuousLinearMap
    (u := scale) (x := (0 : ℂ))
  convert h using 1
  · funext z
    simp [scale]
    congr 1
    ring
  · ext degree
    rw [FormalMultilinearSeries.compContinuousLinearMap_apply]
    simp only [FormalMultilinearSeries.apply_eq_prod_smul_coeff,
      FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul]
    simp [scale]
    cases degree with
    | zero => simp [chapterVILogTaylorCoefficient]
    | succ degree =>
        unfold chapterVILogTaylorCoefficient
        rw [neg_pow]
        have hsign : ((-1 : ℂ) ^ (degree + 1)) * ((-1 : ℂ) ^ (degree + 1)) = 1 := by
          rw [← pow_add, ← two_mul]
          simp
        symm
        calc
          ((-1 : ℂ) ^ (degree + 1) * singularityInverse ^ (degree + 1)) *
              (-(-1 : ℂ) ^ (degree + 1) / ((degree + 1 : ℕ) : ℂ)) =
              -((((-1 : ℂ) ^ (degree + 1)) * ((-1 : ℂ) ^ (degree + 1))) *
                (singularityInverse ^ (degree + 1) / ((degree + 1 : ℕ) : ℂ))) := by ring
          _ = -(singularityInverse ^ (degree + 1) / ((degree + 1 : ℕ) : ℂ)) := by
            rw [hsign]
            ring

/-- A finite weighted sum of logarithmic germs has the coefficientwise sum of their Taylor
series. -/
theorem hasFPowerSeriesAt_finiteLogarithmicSum {r : ℕ}
    (singularityInverse amplitude : Fin r → ℂ) :
    HasFPowerSeriesAt
      (fun z : ℂ ↦ ∑ j, amplitude j * Complex.log (1 - z * singularityInverse j))
      (FormalMultilinearSeries.ofScalars ℂ
        (fun degree ↦ ∑ j, amplitude j *
          chapterVILogTaylorCoefficient (singularityInverse j) degree)) 0 := by
  classical
  let terms : Fin r → ℂ → ℂ :=
    fun j z ↦ amplitude j * Complex.log (1 - z * singularityInverse j)
  let termSeries : Fin r → FormalMultilinearSeries ℂ ℂ ℂ :=
    fun j ↦ FormalMultilinearSeries.ofScalars ℂ
      (fun degree ↦ amplitude j * chapterVILogTaylorCoefficient
        (singularityInverse j) degree)
  have hterm (j : Fin r) : HasFPowerSeriesAt (terms j) (termSeries j) 0 := by
    have h := (hasFPowerSeriesAt_chapterVILogTaylorCoefficient
      (singularityInverse j)).const_smul (c := amplitude j)
    convert h using 1
    · funext z
      simp [terms]
    · rw [← FormalMultilinearSeries.ofScalars_smul]
      congr 1
  have hsum : HasFPowerSeriesAt
      (fun z : ℂ ↦ ∑ j, terms j z) (∑ j, termSeries j) 0 := by
    induction (Finset.univ : Finset (Fin r)) using Finset.induction_on with
    | empty =>
        simpa using (hasFPowerSeriesAt_const (𝕜 := ℂ) (E := ℂ)
          (c := (0 : ℂ)) (e := (0 : ℂ)))
    | @insert j indices hj ih =>
        rw [Finset.sum_insert hj]
        apply ((hterm j).add ih).congr
        apply Eventually.of_forall
        intro z
        change terms j z + ∑ x ∈ indices, terms x z = ∑ x ∈ insert j indices, terms x z
        rw [Finset.sum_insert hj]
  convert hsum using 1
  · let coefficientTerm : Fin r → ℕ → ℂ :=
      fun j degree ↦ amplitude j *
        chapterVILogTaylorCoefficient (singularityInverse j) degree
    have hcoefficientSum :
        (fun degree ↦ ∑ j, coefficientTerm j degree) = ∑ j, coefficientTerm j := by
      funext degree
      simp
    rw [hcoefficientSum]
    change FormalMultilinearSeries.ofScalars ℂ (∑ j, coefficientTerm j) =
      ∑ j, FormalMultilinearSeries.ofScalars ℂ (coefficientTerm j)
    induction (Finset.univ : Finset (Fin r)) using Finset.induction_on with
    | empty => simp
    | @insert j indices hj ih =>
        rw [Finset.sum_insert hj, Finset.sum_insert hj,
          FormalMultilinearSeries.ofScalars_add, ih]

/-- Equality of analytic germs turns Poincaré's function-level finite-logarithm decomposition
into the exact coefficient decomposition used by the Darboux transfer theorem. -/
theorem coefficient_eq_finiteLogs_add_analyticRemainder
    {r : ℕ} {coefficientFunction remainder : ℂ → ℂ}
    {coefficient remainderCoefficient : ℕ → ℂ}
    (singularityInverse amplitude : Fin r → ℂ)
    (hcoefficient : HasFPowerSeriesAt coefficientFunction
      (FormalMultilinearSeries.ofScalars ℂ coefficient) 0)
    (hremainder : HasFPowerSeriesAt remainder
      (FormalMultilinearSeries.ofScalars ℂ remainderCoefficient) 0)
    (hdecomposition : coefficientFunction =ᶠ[nhds 0]
      fun z ↦ (∑ j, amplitude j * Complex.log (1 - z * singularityInverse j)) +
        remainder z) (degree : ℕ) :
    coefficient degree =
      (∑ j, amplitude j * chapterVILogTaylorCoefficient
        (singularityInverse j) degree) + remainderCoefficient degree := by
  let logarithmicCoefficient : ℕ → ℂ :=
    fun n ↦ ∑ j, amplitude j * chapterVILogTaylorCoefficient
      (singularityInverse j) n
  have hlogarithms := hasFPowerSeriesAt_finiteLogarithmicSum
    singularityInverse amplitude
  have hrhs : HasFPowerSeriesAt
      (fun z ↦ (∑ j, amplitude j * Complex.log (1 - z * singularityInverse j)) +
        remainder z)
      (FormalMultilinearSeries.ofScalars ℂ
        (fun n ↦ logarithmicCoefficient n + remainderCoefficient n)) 0 := by
    convert hlogarithms.add hremainder using 1
    · rfl
    · change FormalMultilinearSeries.ofScalars ℂ
          (logarithmicCoefficient + remainderCoefficient) = _
      rw [FormalMultilinearSeries.ofScalars_add]
  have hseries := hcoefficient.eq_formalMultilinearSeries_of_eventually hrhs hdecomposition
  have hdegree := congrArg (fun series : FormalMultilinearSeries ℂ ℂ ℂ ↦ series.coeff degree)
    hseries
  simpa [logarithmicCoefficient] using hdegree

/-- A finite sum of logarithmic singularities becomes an exact finite exponential moment after
Darboux normalization. -/
theorem chapterVINormalizedCoefficient_sum_logarithmicSingularities
    {r : ℕ} (radius : ℝ≥0) (hradius : radius ≠ 0)
    (singularityInverse amplitude : Fin r → ℂ) (index : ℕ) :
    chapterVINormalizedCoefficient radius
        (fun n ↦ ∑ j, amplitude j * chapterVILogSingularityCoefficient
          (singularityInverse j) n) index =
      chapterVIFiniteExponentialMoment
        (fun j ↦ chapterVIUnitBase radius (singularityInverse j))
        (fun j ↦ chapterVILogSpectrumWeight radius (singularityInverse j) (amplitude j))
        index := by
  classical
  unfold chapterVINormalizedCoefficient chapterVIFiniteExponentialMoment
    chapterVILogSpectrumWeight chapterVIUnitBase chapterVILogSingularityCoefficient
  simp only
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hradiusComplex : (radius : ℂ) ≠ 0 := by exact_mod_cast hradius
  rw [mul_pow]
  field_simp
  ring

/-- If inverse singularities have common norm `R⁻¹`, their normalized bases lie on the unit
circle. -/
theorem norm_chapterVIUnitBase_eq_one
    {radius : ℝ≥0} (hradius : radius ≠ 0) {singularityInverse : ℂ}
    (hnorm : ‖singularityInverse‖ = (radius : ℝ)⁻¹) :
    ‖chapterVIUnitBase radius singularityInverse‖ = 1 := by
  rw [chapterVIUnitBase, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg radius.coe_nonneg, hnorm]
  exact mul_inv_cancel₀ (NNReal.coe_ne_zero.mpr hradius)

/-- Coefficients of a function analytic on a disk strictly larger than the boundary-singularity
circle vanish after Darboux normalization.  The shift selects the coefficient of `z^(n+1)`,
matching `chapterVILogSingularityCoefficient`. -/
theorem tendsto_chapterVINormalizedCoefficient_analyticRemainder
    {radius analyticRadius : ℝ≥0} {remainderCoefficient : ℕ → ℂ}
    {remainder : ℂ → ℂ}
    (hradius : radius < analyticRadius)
    (hremainder : HasFPowerSeriesOnBall remainder
      (FormalMultilinearSeries.ofScalars ℂ remainderCoefficient) 0 analyticRadius) :
    Tendsto
      (chapterVINormalizedCoefficient radius (fun n ↦ remainderCoefficient (n + 1)))
      atTop (nhds 0) := by
  let powerSeries := FormalMultilinearSeries.ofScalars ℂ remainderCoefficient
  have hradiiENNReal : (radius : ENNReal) < (analyticRadius : ENNReal) :=
    ENNReal.coe_lt_coe.mpr hradius
  have hradiusSeries : (radius : ENNReal) < powerSeries.radius :=
    hradiiENNReal.trans_le hremainder.r_le
  obtain ⟨ratio, hratio, constant, hconstant, hbound⟩ :=
    powerSeries.norm_mul_pow_le_mul_pow_of_lt_radius hradiusSeries
  have hmodel : Tendsto
      (fun n : ℕ ↦ constant * ((n + 1 : ℕ) : ℝ) * ratio ^ (n + 1))
      atTop (nhds 0) := by
    have hgeometric := tendsto_pow_const_mul_const_pow_of_lt_one 1 hratio.1.le hratio.2
    have hshift := hgeometric.comp (tendsto_add_atTop_nat 1)
    simpa [pow_one, mul_assoc] using hshift.const_mul constant
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero (fun _ ↦ norm_nonneg _)
    (fun index ↦ ?_) hmodel
  unfold chapterVINormalizedCoefficient
  rw [show (index : ℂ) + 1 = ((index + 1 : ℕ) : ℂ) by push_cast; ring,
    norm_mul, norm_mul, norm_natCast, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg radius.coe_nonneg]
  simp only
  have hcoefficientNorm :
      ‖remainderCoefficient (index + 1)‖ = ‖powerSeries (index + 1)‖ := by
    simp [powerSeries]
  rw [hcoefficientNorm]
  have h := hbound (index + 1)
  simpa [mul_assoc, mul_comm, mul_left_comm] using
    mul_le_mul_of_nonneg_left h (Nat.cast_nonneg' (index + 1))

/-- The coefficient-level Darboux transfer theorem for finitely many equally dominant logarithmic
singularities.  The full normalized coefficient sequence differs from its unit-circle exponential
spectrum by a term tending to zero. -/
theorem tendsto_chapterVINormalizedCoefficient_sub_finiteLogSpectrum
    {r : ℕ} {radius analyticRadius : ℝ≥0}
    (hradius : radius ≠ 0) (hradii : radius < analyticRadius)
    (singularityInverse amplitude : Fin r → ℂ)
    (remainderCoefficient : ℕ → ℂ) (remainder : ℂ → ℂ)
    (hremainder : HasFPowerSeriesOnBall remainder
      (FormalMultilinearSeries.ofScalars ℂ remainderCoefficient) 0 analyticRadius) :
    Tendsto
      (chapterVINormalizedCoefficient radius
          (fun n ↦
            (∑ j, amplitude j * chapterVILogSingularityCoefficient
              (singularityInverse j) n) + remainderCoefficient (n + 1)) -
        chapterVIFiniteExponentialMoment
          (fun j ↦ chapterVIUnitBase radius (singularityInverse j))
          (fun j ↦ chapterVILogSpectrumWeight radius
            (singularityInverse j) (amplitude j)))
      atTop (nhds 0) := by
  have hremainderTendsto :=
    tendsto_chapterVINormalizedCoefficient_analyticRemainder hradii hremainder
  convert hremainderTendsto using 1
  funext index
  have hlog := chapterVINormalizedCoefficient_sum_logarithmicSingularities
    radius hradius singularityInverse amplitude index
  rw [Pi.sub_apply]
  unfold chapterVINormalizedCoefficient at hlog ⊢
  rw [mul_add, hlog]
  ring

end PoincareChapterVI
