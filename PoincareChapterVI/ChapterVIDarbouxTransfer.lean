/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Normed.Group.Tannery
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

/-- In one complex variable every formal multilinear series is determined by its scalar
coefficients. -/
theorem formalMultilinearSeries_eq_ofScalars_coeff
    (series : FormalMultilinearSeries ℂ ℂ ℂ) :
    series = FormalMultilinearSeries.ofScalars ℂ series.coeff := by
  ext degree
  simp [FormalMultilinearSeries.apply_eq_prod_smul_coeff]

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

/-- Coefficient of `z^(n+1)` in
`(1 - z * singularityInverse) * log (1 - z * singularityInverse)`. -/
def chapterVIFirstVanishingLogCoefficient (singularityInverse : ℂ) (index : ℕ) : ℂ :=
  chapterVILogTaylorCoefficient singularityInverse (index + 1) -
    singularityInverse * chapterVILogTaylorCoefficient singularityInverse index

/-- Full Taylor coefficient sequence of
`(1 - z * singularityInverse) * log (1 - z * singularityInverse)`, including degree zero. -/
def chapterVIFirstVanishingLogTaylorCoefficient
    (singularityInverse : ℂ) (degree : ℕ) : ℂ :=
  chapterVILogTaylorCoefficient singularityInverse degree -
    singularityInverse * if degree = 0 then 0
      else chapterVILogTaylorCoefficient singularityInverse (degree - 1)

@[simp] theorem chapterVIFirstVanishingLogTaylorCoefficient_succ
    (singularityInverse : ℂ) (index : ℕ) :
    chapterVIFirstVanishingLogTaylorCoefficient singularityInverse (index + 1) =
      chapterVIFirstVanishingLogCoefficient singularityInverse index := by
  simp [chapterVIFirstVanishingLogTaylorCoefficient,
    chapterVIFirstVanishingLogCoefficient]

/-- Away from its degree-one exceptional coefficient, the first-vanishing logarithmic kernel has
the exact `1 / (d(d-1))` decay used in the convolution proof for a varying analytic amplitude. -/
theorem chapterVIFirstVanishingLogTaylorCoefficient_eq
    (singularityInverse : ℂ) {degree : ℕ} (hdegree : 2 ≤ degree) :
    chapterVIFirstVanishingLogTaylorCoefficient singularityInverse degree =
      singularityInverse ^ degree / (degree * (degree - 1) : ℕ) := by
  have hdegree0 : degree ≠ 0 := by omega
  have hdegreePred0 : degree - 1 ≠ 0 := by omega
  have hdegreePred : degree - 1 + 1 = degree := by omega
  unfold chapterVIFirstVanishingLogTaylorCoefficient chapterVILogTaylorCoefficient
  simp only [if_neg hdegree0]
  rw [show singularityInverse ^ degree =
      singularityInverse * singularityInverse ^ (degree - 1) by
    nth_rewrite 1 [← hdegreePred]
    rw [pow_succ']]
  push_cast
  field_simp
  rw [show (degree : ℂ) = (degree - 1 : ℕ) + 1 by exact_mod_cast hdegreePred.symm]
  ring

/-- Radius-scaled full coefficients of the first-vanishing logarithmic kernel.  This scaling
turns a boundary singularity into a unit-modulus sequence. -/
def chapterVIScaledFirstVanishingLogTaylorCoefficient
    (radius : ℝ≥0) (singularityInverse : ℂ) (degree : ℕ) : ℂ :=
  (radius : ℂ) ^ degree *
    chapterVIFirstVanishingLogTaylorCoefficient singularityInverse degree

theorem norm_chapterVIScaledFirstVanishingLogTaylorCoefficient
    {radius : ℝ≥0} {singularityInverse : ℂ}
    (hunit : ‖chapterVIUnitBase radius singularityInverse‖ = 1)
    {degree : ℕ} (hdegree : 2 ≤ degree) :
    ‖chapterVIScaledFirstVanishingLogTaylorCoefficient
      radius singularityInverse degree‖ =
      1 / (degree * (degree - 1) : ℕ) := by
  rw [chapterVIScaledFirstVanishingLogTaylorCoefficient,
    chapterVIFirstVanishingLogTaylorCoefficient_eq singularityInverse hdegree]
  rw [norm_mul, norm_div, norm_pow]
  have hscaled : ‖(radius : ℂ)‖ * ‖singularityInverse‖ = 1 := by
    simpa [chapterVIUnitBase, norm_mul] using hunit
  rw [norm_pow]
  rw [← mul_div_assoc]
  rw [← mul_pow, hscaled, one_pow, one_div]
  simp

theorem norm_natCast_mul_chapterVIScaledFirstVanishingLogTaylorCoefficient
    {radius : ℝ≥0} {singularityInverse : ℂ}
    (hunit : ‖chapterVIUnitBase radius singularityInverse‖ = 1)
    {degree : ℕ} (hdegree : 2 ≤ degree) :
    ‖(degree : ℂ) * chapterVIScaledFirstVanishingLogTaylorCoefficient
      radius singularityInverse degree‖ = 1 / (degree - 1 : ℕ) := by
  rw [norm_mul, norm_natCast,
    norm_chapterVIScaledFirstVanishingLogTaylorCoefficient hunit hdegree]
  have hdegree0 : (degree : ℝ) ≠ 0 := by positivity
  have hdegreePred0 : ((degree - 1 : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (show degree - 1 ≠ 0 by omega)
  push_cast
  field_simp

/-- The radius-scaled first-vanishing logarithmic kernel is `o(1/d)`. -/
theorem tendsto_natCast_mul_chapterVIScaledFirstVanishingLogTaylorCoefficient
    {radius : ℝ≥0} {singularityInverse : ℂ}
    (hunit : ‖chapterVIUnitBase radius singularityInverse‖ = 1) :
    Tendsto (fun degree : ℕ ↦ (degree : ℂ) *
      chapterVIScaledFirstVanishingLogTaylorCoefficient
        radius singularityInverse degree) atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hmodel : Tendsto (fun degree : ℕ ↦ (1 : ℝ) / (degree - 1 : ℕ))
      atTop (nhds 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).comp
      (tendsto_sub_atTop_nat 1)
  apply hmodel.congr'
  filter_upwards [eventually_ge_atTop 2] with degree hdegree
  exact (norm_natCast_mul_chapterVIScaledFirstVanishingLogTaylorCoefficient
    hunit hdegree).symm

/-- In particular, the scaled first-vanishing logarithmic kernel itself tends to zero. -/
theorem tendsto_chapterVIScaledFirstVanishingLogTaylorCoefficient
    {radius : ℝ≥0} {singularityInverse : ℂ}
    (hunit : ‖chapterVIUnitBase radius singularityInverse‖ = 1) :
    Tendsto (chapterVIScaledFirstVanishingLogTaylorCoefficient
      radius singularityInverse) atTop (nhds 0) := by
  have hweighted :=
    tendsto_natCast_mul_chapterVIScaledFirstVanishingLogTaylorCoefficient hunit
  rw [tendsto_zero_iff_norm_tendsto_zero] at hweighted ⊢
  apply squeeze_zero (fun _ ↦ norm_nonneg _) (fun degree ↦ ?_) hweighted
  cases degree with
  | zero => simp [chapterVIScaledFirstVanishingLogTaylorCoefficient,
      chapterVIFirstVanishingLogTaylorCoefficient, chapterVILogTaylorCoefficient]
  | succ degree =>
      rw [norm_mul, norm_natCast]
      exact le_mul_of_one_le_left (norm_nonneg _) (by norm_num)

/-- Cauchy product truncated at a fixed Taylor degree. -/
def chapterVITruncatedConvolution (left right : ℕ → ℂ) (degree : ℕ) : ℂ :=
  ∑ index ∈ Finset.range (degree + 1), left index * right (degree - index)

/-- A weighted `ℓ¹ * c₀` convolution lemma tailored to Darboux transfer.  If both a kernel and
its degree-weighted sequence tend to zero, convolution with coefficients having a summable first
moment is still `o(1 / degree)`. -/
theorem tendsto_natCast_mul_chapterVITruncatedConvolution
    (left kernel : ℕ → ℂ)
    (hleft : Summable fun index ↦ ‖left index‖)
    (hleftMoment : Summable fun index : ℕ ↦ (index : ℝ) * ‖left index‖)
    (hkernel : Tendsto kernel atTop (nhds 0))
    (hweightedKernel : Tendsto (fun degree : ℕ ↦ (degree : ℂ) * kernel degree)
      atTop (nhds 0)) :
    Tendsto (fun degree : ℕ ↦ (degree : ℂ) *
      chapterVITruncatedConvolution left kernel degree) atTop (nhds 0) := by
  obtain ⟨weightedBound, hweightedBoundPos, hweightedBound⟩ :=
    (Metric.isBounded_range_of_tendsto _ hweightedKernel).exists_pos_norm_le
  obtain ⟨kernelBound, hkernelBoundPos, hkernelBound⟩ :=
    (Metric.isBounded_range_of_tendsto _ hkernel).exists_pos_norm_le
  let term : ℕ → ℕ → ℂ := fun degree index ↦
    if index ≤ degree then
      (degree : ℂ) * left index * kernel (degree - index)
    else 0
  let bound : ℕ → ℝ := fun index ↦
    weightedBound * ‖left index‖ +
      kernelBound * ((index : ℝ) * ‖left index‖)
  have hsummableBound : Summable bound :=
    (hleft.mul_left weightedBound).add (hleftMoment.mul_left kernelBound)
  have hterm (index : ℕ) : Tendsto (fun degree ↦ term degree index)
      atTop (nhds 0) := by
    have hweightedShift := hweightedKernel.comp (tendsto_sub_atTop_nat index)
    have hkernelShift := hkernel.comp (tendsto_sub_atTop_nat index)
    have hsum : Tendsto (fun degree : ℕ ↦
        ((degree - index : ℕ) : ℂ) * kernel (degree - index) +
          (index : ℂ) * kernel (degree - index)) atTop (nhds 0) := by
      simpa using hweightedShift.add (hkernelShift.const_mul (index : ℂ))
    have hproduct : Tendsto (fun degree : ℕ ↦ left index *
        (((degree - index : ℕ) : ℂ) * kernel (degree - index) +
          (index : ℂ) * kernel (degree - index))) atTop (nhds 0) := by
      simpa using hsum.const_mul (left index)
    apply hproduct.congr'
    filter_upwards [eventually_ge_atTop index] with degree hdegree
    simp only [term, if_pos hdegree]
    have hdegreeSplit : degree - index + index = degree := Nat.sub_add_cancel hdegree
    rw [show (degree : ℂ) = (degree - index : ℕ) + index by
      exact_mod_cast hdegreeSplit.symm]
    ring
  have hdominated : ∀ degree index, ‖term degree index‖ ≤ bound index := by
    intro degree index
    by_cases hindex : index ≤ degree
    · simp only [term, if_pos hindex]
      have hdegreeSplit : degree - index + index = degree := Nat.sub_add_cancel hindex
      have heq : (degree : ℂ) * left index * kernel (degree - index) =
          left index * (((degree - index : ℕ) : ℂ) * kernel (degree - index) +
            (index : ℂ) * kernel (degree - index)) := by
        rw [show (degree : ℂ) = (degree - index : ℕ) + index by
          exact_mod_cast hdegreeSplit.symm]
        ring
      rw [heq, norm_mul]
      calc
        ‖left index‖ * ‖((degree - index : ℕ) : ℂ) * kernel (degree - index) +
            (index : ℂ) * kernel (degree - index)‖ ≤
            ‖left index‖ *
              (‖((degree - index : ℕ) : ℂ) * kernel (degree - index)‖ +
                ‖(index : ℂ) * kernel (degree - index)‖) := by
              gcongr
              exact norm_add_le _ _
        _ ≤ ‖left index‖ *
            (weightedBound + (index : ℝ) * kernelBound) := by
              gcongr
              · exact hweightedBound _ ⟨degree - index, rfl⟩
              · rw [norm_mul, norm_natCast]
                exact mul_le_mul_of_nonneg_left
                  (hkernelBound _ ⟨degree - index, rfl⟩) (Nat.cast_nonneg index)
        _ = bound index := by simp [bound]; ring
    · simp only [term, if_neg hindex, norm_zero]
      dsimp [bound]
      positivity
  have htsum : Tendsto (fun degree ↦ ∑' index, term degree index)
      atTop (nhds (∑' _index : ℕ, (0 : ℂ))) :=
    tendsto_tsum_of_dominated_convergence hsummableBound hterm
      (Eventually.of_forall hdominated)
  have heq (degree : ℕ) : (∑' index, term degree index) =
      (degree : ℂ) * chapterVITruncatedConvolution left kernel degree := by
    rw [tsum_eq_sum (s := Finset.range (degree + 1))]
    · unfold chapterVITruncatedConvolution
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro index hindex
      simp only [term, if_pos (Nat.le_of_lt_succ (Finset.mem_range.mp hindex))]
      ring
    · intro index hindex
      have hnotle : ¬index ≤ degree := by
        simpa [Finset.mem_range, Nat.lt_succ_iff] using hindex
      simp [term, hnotle]
  simpa [heq] using htsum

/-- Scaling a Cauchy product coefficient by `R^degree` scales each factor coefficient by its own
degree. -/
theorem chapterVITruncatedConvolution_scaled (radius : ℝ≥0)
    (left right : ℕ → ℂ) (degree : ℕ) :
    (radius : ℂ) ^ degree * chapterVITruncatedConvolution left right degree =
      chapterVITruncatedConvolution
        (fun index ↦ (radius : ℂ) ^ index * left index)
        (fun index ↦ (radius : ℂ) ^ index * right index) degree := by
  unfold chapterVITruncatedConvolution
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro index hindex
  have hle : index ≤ degree := Nat.le_of_lt_succ (Finset.mem_range.mp hindex)
  have hpow : (radius : ℂ) ^ degree =
      (radius : ℂ) ^ index * (radius : ℂ) ^ (degree - index) := by
    rw [← pow_add, Nat.add_sub_of_le hle]
  rw [hpow]
  ring

/-- Coefficients of an analytic function multiplied by the first-vanishing logarithmic kernel,
indexed at Taylor degree `index + 1`. -/
def chapterVIRegularAmplitudeLogRemainderCoefficient
    (singularityInverse : ℂ) (amplitudeCoefficient : ℕ → ℂ) (index : ℕ) : ℂ :=
  chapterVITruncatedConvolution amplitudeCoefficient
    (chapterVIFirstVanishingLogTaylorCoefficient singularityInverse) (index + 1)

/-- Coefficients of a function analytic on a disk strictly larger than radius `R` are absolutely
summable after `R^n` scaling, even after multiplication by one power of `n`. -/
theorem summable_radiusScaledCoefficient_and_moment
    {radius analyticRadius : ℝ≥0} {amplitudeCoefficient : ℕ → ℂ}
    {amplitude : ℂ → ℂ} (hradii : radius < analyticRadius)
    (hamplitude : HasFPowerSeriesOnBall amplitude
      (FormalMultilinearSeries.ofScalars ℂ amplitudeCoefficient) 0 analyticRadius) :
    Summable (fun index ↦
        ‖(radius : ℂ) ^ index * amplitudeCoefficient index‖) ∧
      Summable (fun index : ℕ ↦
        (index : ℝ) * ‖(radius : ℂ) ^ index * amplitudeCoefficient index‖) := by
  let powerSeries := FormalMultilinearSeries.ofScalars ℂ amplitudeCoefficient
  have hradiiENNReal : (radius : ENNReal) < (analyticRadius : ENNReal) :=
    ENNReal.coe_lt_coe.mpr hradii
  have hradiusSeries : (radius : ENNReal) < powerSeries.radius :=
    hradiiENNReal.trans_le hamplitude.r_le
  obtain ⟨ratio, hratio, constant, hconstant, hbound⟩ :=
    powerSeries.norm_mul_pow_le_mul_pow_of_lt_radius hradiusSeries
  have hratioNorm : ‖ratio‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos hratio.1]
    exact hratio.2
  have hgeometric : Summable (fun index : ℕ ↦ constant * ratio ^ index) := by
    exact (summable_geometric_of_norm_lt_one hratioNorm).mul_left constant
  have hmomentGeometric : Summable
      (fun index : ℕ ↦ constant * ((index : ℝ) * ratio ^ index)) := by
    have h := summable_norm_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hratioNorm
    have h' : Summable (fun index : ℕ ↦ (index : ℝ) * ratio ^ index) := by
      simpa [Real.norm_eq_abs, abs_of_nonneg hratio.1.le] using h
    exact h'.mul_left constant
  constructor
  · apply hgeometric.of_nonneg_of_le (fun _ ↦ norm_nonneg _)
    intro index
    have hcoefficientNorm :
        ‖amplitudeCoefficient index‖ = ‖powerSeries index‖ := by
      simp [powerSeries]
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg radius.coe_nonneg, hcoefficientNorm]
    simpa [mul_comm] using hbound index
  · apply hmomentGeometric.of_nonneg_of_le (fun _ ↦ mul_nonneg
      (Nat.cast_nonneg _) (norm_nonneg _))
    intro index
    have hcoefficientNorm :
        ‖amplitudeCoefficient index‖ = ‖powerSeries index‖ := by
      simp [powerSeries]
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg radius.coe_nonneg, hcoefficientNorm]
    calc
      (index : ℝ) * ((radius : ℝ) ^ index * ‖powerSeries index‖) =
          (index : ℝ) * (‖powerSeries index‖ * (radius : ℝ) ^ index) := by ring
      _ ≤ (index : ℝ) * (constant * ratio ^ index) :=
        mul_le_mul_of_nonneg_left (hbound index) (Nat.cast_nonneg index)
      _ = constant * ((index : ℝ) * ratio ^ index) := by ring

/-- A genuinely analytic amplitude automatically has Poincaré's regular-factor decomposition.
The divided difference `dslope` fills in the removable value at the boundary point, and an
intermediate disk preserves a radius strictly larger than the singularity circle. -/
theorem exists_regularAmplitudeFactorization_of_analytic
    {radius analyticRadius : ℝ≥0} {singularity : ℂ}
    (hsingularity : singularity ≠ 0) (hnorm : ‖singularity‖ = radius)
    (hradii : radius < analyticRadius) (amplitude : ℂ → ℂ)
    (amplitudeSeries : FormalMultilinearSeries ℂ ℂ ℂ)
    (hamplitude : HasFPowerSeriesOnBall amplitude amplitudeSeries 0 analyticRadius) :
    ∃ (regularRadius : ℝ≥0) (regularCoefficient : ℕ → ℂ) (regular : ℂ → ℂ),
      radius < regularRadius ∧
      HasFPowerSeriesOnBall regular
        (FormalMultilinearSeries.ofScalars ℂ regularCoefficient) 0 regularRadius ∧
      ∀ z, amplitude z = amplitude singularity +
        (1 - z * singularity⁻¹) * regular z := by
  obtain ⟨regularRadius, hradiusRegular, hregularAnalytic⟩ := exists_between hradii
  let regular : ℂ → ℂ := fun z ↦ -singularity * dslope amplitude singularity z
  have hsingularityMem : singularity ∈ Metric.ball (0 : ℂ) analyticRadius := by
    rw [Metric.mem_ball, dist_zero_right, hnorm]
    exact hradii
  have hballNhd : Metric.ball (0 : ℂ) analyticRadius ∈ nhds singularity :=
    Metric.isOpen_ball.mem_nhds hsingularityMem
  have hamplitudeDifferentiable : DifferentiableOn ℂ amplitude
      (Metric.ball (0 : ℂ) analyticRadius) :=
    by simpa only [Metric.eball_coe] using hamplitude.analyticOnNhd.differentiableOn
  have hregularDifferentiable : DifferentiableOn ℂ regular
      (Metric.ball (0 : ℂ) analyticRadius) := by
    exact ((Complex.differentiableOn_dslope hballNhd).mpr hamplitudeDifferentiable).const_mul
      (-singularity)
  have hregularRadiusPos : 0 < regularRadius :=
    radius.coe_nonneg.trans_lt hradiusRegular
  have hregularPowerSeries :=
    (hregularDifferentiable.mono
      (Metric.closedBall_subset_ball hregularAnalytic)).hasFPowerSeriesOnBall
        hregularRadiusPos
  let regularSeries : FormalMultilinearSeries ℂ ℂ ℂ :=
    cauchyPowerSeries regular 0 regularRadius
  let regularCoefficient : ℕ → ℂ := regularSeries.coeff
  refine ⟨regularRadius, regularCoefficient, regular, hradiusRegular, ?_, ?_⟩
  · change HasFPowerSeriesOnBall regular
      (FormalMultilinearSeries.ofScalars ℂ regularSeries.coeff) 0 regularRadius
    rw [← formalMultilinearSeries_eq_ofScalars_coeff regularSeries]
    exact hregularPowerSeries
  · intro z
    have hslope := sub_smul_dslope amplitude singularity z
    simp only [smul_eq_mul] at hslope
    have hinverse : singularity⁻¹ * singularity = 1 :=
      inv_mul_cancel₀ hsingularity
    have halgebra : (1 - z * singularity⁻¹) * (-singularity) =
        z - singularity := by
      calc
        (1 - z * singularity⁻¹) * (-singularity) =
            -singularity + z * (singularity⁻¹ * singularity) := by ring
        _ = z - singularity := by rw [hinverse]; ring
    calc
      amplitude z = amplitude singularity + (z - singularity) *
          dslope amplitude singularity z := by rw [hslope]; ring
      _ = amplitude singularity + (1 - z * singularity⁻¹) * regular z := by
        unfold regular
        rw [← mul_assoc, halgebra]

/-- A regular analytic amplitude multiplying `(1-zλ) log(1-zλ)` is Darboux-subleading whenever
its radius-scaled Taylor coefficients have a summable first moment.  This is the coefficient
form of writing a varying amplitude as its singular value plus a vanishing factor. -/
theorem tendsto_chapterVINormalizedCoefficient_regularAmplitudeLogRemainder
    {radius : ℝ≥0} {singularityInverse : ℂ}
    (hunit : ‖chapterVIUnitBase radius singularityInverse‖ = 1)
    (amplitudeCoefficient : ℕ → ℂ)
    (hsummable : Summable fun index ↦
      ‖(radius : ℂ) ^ index * amplitudeCoefficient index‖)
    (hsummableMoment : Summable fun index : ℕ ↦
      (index : ℝ) * ‖(radius : ℂ) ^ index * amplitudeCoefficient index‖) :
    Tendsto
      (chapterVINormalizedCoefficient radius
        (chapterVIRegularAmplitudeLogRemainderCoefficient
          singularityInverse amplitudeCoefficient)) atTop (nhds 0) := by
  let scaledAmplitude : ℕ → ℂ := fun index ↦
    (radius : ℂ) ^ index * amplitudeCoefficient index
  let scaledKernel : ℕ → ℂ :=
    chapterVIScaledFirstVanishingLogTaylorCoefficient radius singularityInverse
  have hconvolution := tendsto_natCast_mul_chapterVITruncatedConvolution
    scaledAmplitude scaledKernel hsummable hsummableMoment
      (tendsto_chapterVIScaledFirstVanishingLogTaylorCoefficient hunit)
      (tendsto_natCast_mul_chapterVIScaledFirstVanishingLogTaylorCoefficient hunit)
  have hshift := hconvolution.comp (tendsto_add_atTop_nat 1)
  apply hshift.congr'
  apply Eventually.of_forall
  intro index
  unfold chapterVINormalizedCoefficient chapterVIRegularAmplitudeLogRemainderCoefficient
    scaledAmplitude scaledKernel chapterVIScaledFirstVanishingLogTaylorCoefficient
  simp only [Function.comp_apply]
  rw [← chapterVITruncatedConvolution_scaled radius amplitudeCoefficient
    (chapterVIFirstVanishingLogTaylorCoefficient singularityInverse) (index + 1)]
  push_cast
  ring

/-- Analyticity of the regular amplitude on a disk strictly larger than the boundary circle
automatically supplies the summable first moment required by the convolution theorem. -/
theorem tendsto_chapterVINormalizedCoefficient_regularAmplitudeLogRemainder_of_analytic
    {radius analyticRadius : ℝ≥0} {singularityInverse : ℂ}
    (hunit : ‖chapterVIUnitBase radius singularityInverse‖ = 1)
    (hradii : radius < analyticRadius)
    (amplitudeCoefficient : ℕ → ℂ) (amplitude : ℂ → ℂ)
    (hamplitude : HasFPowerSeriesOnBall amplitude
      (FormalMultilinearSeries.ofScalars ℂ amplitudeCoefficient) 0 analyticRadius) :
    Tendsto
      (chapterVINormalizedCoefficient radius
        (chapterVIRegularAmplitudeLogRemainderCoefficient
          singularityInverse amplitudeCoefficient)) atTop (nhds 0) := by
  obtain ⟨hsummable, hsummableMoment⟩ :=
    summable_radiusScaledCoefficient_and_moment hradii hamplitude
  exact tendsto_chapterVINormalizedCoefficient_regularAmplitudeLogRemainder
    hunit amplitudeCoefficient hsummable hsummableMoment

/-- After Darboux normalization, the first vanishing logarithmic amplitude has the exact
subleading form `unitBase^(n+1) / n`. -/
theorem chapterVINormalizedCoefficient_firstVanishingLog
    (radius : ℝ≥0) (singularityInverse : ℂ) {index : ℕ} (hindex : index ≠ 0) :
    chapterVINormalizedCoefficient radius
        (chapterVIFirstVanishingLogCoefficient singularityInverse) index =
      chapterVIUnitBase radius singularityInverse ^ (index + 1) / index := by
  unfold chapterVINormalizedCoefficient chapterVIFirstVanishingLogCoefficient
    chapterVILogTaylorCoefficient chapterVIUnitBase
  push_cast
  rw [mul_pow]
  field_simp
  ring

/-- A logarithmic term whose amplitude contains one factor vanishing at the singular point is
`o(1)` after the leading Darboux normalization. -/
theorem tendsto_chapterVINormalizedCoefficient_firstVanishingLog
    {radius : ℝ≥0} {singularityInverse : ℂ}
    (hunit : ‖chapterVIUnitBase radius singularityInverse‖ = 1) :
    Tendsto
      (chapterVINormalizedCoefficient radius
        (chapterVIFirstVanishingLogCoefficient singularityInverse))
      atTop (nhds 0) := by
  have hmodel : Tendsto
      (fun index : ℕ ↦ chapterVIUnitBase radius singularityInverse ^ (index + 1) / index)
      atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa [norm_div, norm_pow, hunit] using
      (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ))
  apply hmodel.congr'
  filter_upwards [eventually_ne_atTop 0] with index hindex
  exact (chapterVINormalizedCoefficient_firstVanishingLog
    radius singularityInverse hindex).symm

/-- Coefficient transform induced, for a zero-constant-term series, by multiplication with
`1 - z * singularityInverse`.  Only the large-index behavior matters below, so the degree-one
coefficient is handled separately at index zero. -/
def chapterVIVanishingFactorTransform (singularityInverse : ℂ)
    (coefficient : ℕ → ℂ) (index : ℕ) : ℂ :=
  if index = 0 then coefficient 0
  else coefficient index - singularityInverse * coefficient (index - 1)

/-- Darboux normalization intertwines multiplication by the vanishing factor with a shifted
normalized sequence and a scalar tending to the unit base. -/
theorem chapterVINormalizedCoefficient_vanishingFactorTransform
    (radius : ℝ≥0) (singularityInverse : ℂ) (coefficient : ℕ → ℂ)
    {index : ℕ} (hindex : index ≠ 0) :
    chapterVINormalizedCoefficient radius
        (chapterVIVanishingFactorTransform singularityInverse coefficient) index =
      chapterVINormalizedCoefficient radius coefficient index -
        ((index + 1 : ℕ) : ℂ) / index * chapterVIUnitBase radius singularityInverse *
          chapterVINormalizedCoefficient radius coefficient (index - 1) := by
  have hpred : index - 1 + 1 = index := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hindex)
  have hpredCast : ((index - 1 : ℕ) : ℂ) + 1 = (index : ℂ) := by
    exact_mod_cast hpred
  unfold chapterVINormalizedCoefficient chapterVIVanishingFactorTransform chapterVIUnitBase
  simp only [if_neg hindex]
  rw [hpred, hpredCast, pow_succ]
  field_simp
  push_cast
  ring

/-- Multiplication by one more factor vanishing at a unit-modulus boundary singularity preserves
normalized decay. -/
theorem tendsto_chapterVINormalizedCoefficient_vanishingFactorTransform
    {radius : ℝ≥0} {singularityInverse : ℂ} {coefficient : ℕ → ℂ}
    (hcoefficient : Tendsto (chapterVINormalizedCoefficient radius coefficient)
      atTop (nhds 0)) :
    Tendsto
      (chapterVINormalizedCoefficient radius
        (chapterVIVanishingFactorTransform singularityInverse coefficient))
      atTop (nhds 0) := by
  have hprevious := hcoefficient.comp (tendsto_sub_atTop_nat 1)
  have hratio : Tendsto (fun index : ℕ ↦ ((index + 1 : ℕ) : ℂ) / index)
      atTop (nhds 1) := by
    have hinverse : Tendsto (fun index : ℕ ↦ (index : ℂ)⁻¹) atTop (nhds 0) :=
      tendsto_inv_atTop_nhds_zero_nat
    have hone : Tendsto (fun _ : ℕ ↦ (1 : ℂ)) atTop (nhds 1) :=
      tendsto_const_nhds
    have hbase : Tendsto (fun index : ℕ ↦ 1 + (index : ℂ)⁻¹)
        atTop (nhds 1) := by simpa using hone.add hinverse
    apply hbase.congr'
    filter_upwards [eventually_ne_atTop 0] with index hindex
    push_cast
    have hindexComplex : (index : ℂ) ≠ 0 := by exact_mod_cast hindex
    field_simp
  have hsubleading : Tendsto
      (fun index : ℕ ↦ ((index + 1 : ℕ) : ℂ) / index *
        chapterVIUnitBase radius singularityInverse *
          chapterVINormalizedCoefficient radius coefficient (index - 1))
      atTop (nhds 0) := by
    simpa using (hratio.mul_const (chapterVIUnitBase radius singularityInverse)).mul hprevious
  have hmain := hcoefficient.sub hsubleading
  have heq : (fun index ↦ chapterVINormalizedCoefficient radius coefficient index -
      ((index + 1 : ℕ) : ℂ) / index * chapterVIUnitBase radius singularityInverse *
        chapterVINormalizedCoefficient radius coefficient (index - 1)) =ᶠ[atTop]
      chapterVINormalizedCoefficient radius
        (chapterVIVanishingFactorTransform singularityInverse coefficient) := by
    filter_upwards [eventually_ne_atTop 0] with index hindex
    exact (chapterVINormalizedCoefficient_vanishingFactorTransform
      radius singularityInverse coefficient hindex).symm
  simpa using hmain.congr' heq

/-- Coefficients of `(1-zλ)^k log(1-zλ)`, indexed by the coefficient of `z^(n+1)`. -/
def chapterVIHigherVanishingLogCoefficient (singularityInverse : ℂ) (order : ℕ) : ℕ → ℂ :=
  (chapterVIVanishingFactorTransform singularityInverse)^[order]
    (fun index ↦ chapterVILogTaylorCoefficient singularityInverse (index + 1))

theorem chapterVIVanishingFactorTransform_log_eq_firstVanishingLog
    (singularityInverse : ℂ) :
    chapterVIVanishingFactorTransform singularityInverse
        (fun index ↦ chapterVILogTaylorCoefficient singularityInverse (index + 1)) =
      chapterVIFirstVanishingLogCoefficient singularityInverse := by
  funext index
  by_cases hindex : index = 0
  · subst index
    simp [chapterVIVanishingFactorTransform, chapterVIFirstVanishingLogCoefficient,
      chapterVILogTaylorCoefficient]
  · have hpred : index - 1 + 1 = index :=
      Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hindex)
    simp only [chapterVIVanishingFactorTransform, if_neg hindex,
      chapterVIFirstVanishingLogCoefficient]
    rw [hpred]

theorem chapterVIHigherVanishingLogCoefficient_succ
    (singularityInverse : ℂ) (order : ℕ) :
    chapterVIHigherVanishingLogCoefficient singularityInverse (order + 1) =
      chapterVIVanishingFactorTransform singularityInverse
        (chapterVIHigherVanishingLogCoefficient singularityInverse order) := by
  unfold chapterVIHigherVanishingLogCoefficient
  rw [show order + 1 = order.succ by omega, Function.iterate_succ_apply']

/-- Every positive-order amplitude jet `(1-zλ)^k log(1-zλ)` is subleading after Darboux
normalization. -/
theorem tendsto_chapterVINormalizedCoefficient_higherVanishingLog
    {radius : ℝ≥0} {singularityInverse : ℂ}
    (hunit : ‖chapterVIUnitBase radius singularityInverse‖ = 1) (order : ℕ) :
    Tendsto
      (chapterVINormalizedCoefficient radius
        (chapterVIHigherVanishingLogCoefficient singularityInverse (order + 1)))
      atTop (nhds 0) := by
  induction order with
  | zero =>
      rw [chapterVIHigherVanishingLogCoefficient_succ]
      change Tendsto
        (chapterVINormalizedCoefficient radius
          (chapterVIVanishingFactorTransform singularityInverse
            (fun index ↦ chapterVILogTaylorCoefficient singularityInverse (index + 1))))
        atTop (nhds 0)
      rw [chapterVIVanishingFactorTransform_log_eq_firstVanishingLog]
      exact tendsto_chapterVINormalizedCoefficient_firstVanishingLog hunit
  | succ order inductionHypothesis =>
      rw [chapterVIHigherVanishingLogCoefficient_succ]
      exact tendsto_chapterVINormalizedCoefficient_vanishingFactorTransform inductionHypothesis

/-- Darboux normalization commutes with a finite coefficient sum. -/
theorem chapterVINormalizedCoefficient_finset_sum
    {ι : Type*} (radius : ℝ≥0) (indices : Finset ι)
    (coefficient : ι → ℕ → ℂ) (index : ℕ) :
    chapterVINormalizedCoefficient radius
        (fun n ↦ ∑ i ∈ indices, coefficient i n) index =
      ∑ i ∈ indices, chapterVINormalizedCoefficient radius (coefficient i) index := by
  unfold chapterVINormalizedCoefficient
  simp only [Finset.mul_sum]

/-- Darboux normalization commutes with a constant coefficient multiplier. -/
theorem chapterVINormalizedCoefficient_const_mul
    (radius : ℝ≥0) (constant : ℂ) (coefficient : ℕ → ℂ) (index : ℕ) :
    chapterVINormalizedCoefficient radius (fun n ↦ constant * coefficient n) index =
      constant * chapterVINormalizedCoefficient radius coefficient index := by
  unfold chapterVINormalizedCoefficient
  ring

/-- The Taylor coefficients contributed by a finite jet in powers of `1-zλ`, multiplying the
logarithm at the same boundary singularity. -/
def chapterVILogAmplitudeJetCoefficient {jetOrder : ℕ} (singularityInverse : ℂ)
    (jet : Fin (jetOrder + 1) → ℂ) (index : ℕ) : ℂ :=
  ∑ order, jet order *
    chapterVIHigherVanishingLogCoefficient singularityInverse order index

/-- The positive-order portion of a logarithmic amplitude jet. -/
def chapterVILogAmplitudeJetRemainderCoefficient {jetOrder : ℕ}
    (singularityInverse : ℂ) (jet : Fin (jetOrder + 1) → ℂ) (index : ℕ) : ℂ :=
  ∑ order : Fin jetOrder, jet order.succ *
    chapterVIHigherVanishingLogCoefficient singularityInverse (order + 1) index

/-- Split a finite logarithmic amplitude jet into its value at the singularity and terms carrying
a positive power of the vanishing factor. -/
theorem chapterVILogAmplitudeJetCoefficient_eq_leading_add_remainder
    {jetOrder : ℕ} (singularityInverse : ℂ) (jet : Fin (jetOrder + 1) → ℂ)
    (index : ℕ) :
    chapterVILogAmplitudeJetCoefficient singularityInverse jet index =
      jet 0 * chapterVILogTaylorCoefficient singularityInverse (index + 1) +
        chapterVILogAmplitudeJetRemainderCoefficient singularityInverse jet index := by
  unfold chapterVILogAmplitudeJetCoefficient chapterVILogAmplitudeJetRemainderCoefficient
  rw [Fin.sum_univ_succ]
  rfl

/-- Every positive-order part of a finite logarithmic amplitude jet disappears after leading
Darboux normalization. -/
theorem tendsto_chapterVINormalizedCoefficient_logAmplitudeJetRemainder
    {jetOrder : ℕ} {radius : ℝ≥0} {singularityInverse : ℂ}
    (hunit : ‖chapterVIUnitBase radius singularityInverse‖ = 1)
    (jet : Fin (jetOrder + 1) → ℂ) :
    Tendsto
      (chapterVINormalizedCoefficient radius
        (chapterVILogAmplitudeJetRemainderCoefficient singularityInverse jet))
      atTop (nhds 0) := by
  have hterm (order : Fin jetOrder) : Tendsto
      (chapterVINormalizedCoefficient radius
        (fun index ↦ jet order.succ *
          chapterVIHigherVanishingLogCoefficient singularityInverse (order + 1) index))
      atTop (nhds 0) := by
    have h := (tendsto_chapterVINormalizedCoefficient_higherVanishingLog hunit order).const_mul
      (jet order.succ)
    convert h using 1
    · funext index
      exact chapterVINormalizedCoefficient_const_mul radius (jet order.succ)
        (chapterVIHigherVanishingLogCoefficient singularityInverse (order + 1)) index
    · simp
  have hsum := tendsto_finsetSum (Finset.univ : Finset (Fin jetOrder))
    (fun order _ ↦ hterm order)
  convert hsum using 1
  · funext index
    exact chapterVINormalizedCoefficient_finset_sum radius Finset.univ
      (fun (order : Fin jetOrder) index ↦ jet order.succ *
        chapterVIHigherVanishingLogCoefficient singularityInverse (order + 1) index) index
  · simp

/-- The positive-order part of a possibly infinite analytic amplitude expansion, written in
powers of the local vanishing factor `1 - z * singularityInverse`. -/
def chapterVILogAnalyticAmplitudeRemainderCoefficient
    (singularityInverse : ℂ) (jet : ℕ → ℂ) (index : ℕ) : ℂ :=
  ∑' order : ℕ, jet (order + 1) *
    chapterVIHigherVanishingLogCoefficient singularityInverse (order + 1) index

/-- Darboux normalization commutes with a summable coefficient series. -/
theorem chapterVINormalizedCoefficient_tsum {ι : Type*}
    (radius : ℝ≥0) (coefficient : ι → ℕ → ℂ) (index : ℕ)
    (hsummable : Summable fun i ↦ coefficient i index) :
    chapterVINormalizedCoefficient radius (fun n ↦ ∑' i, coefficient i n) index =
      ∑' i, chapterVINormalizedCoefficient radius (coefficient i) index := by
  unfold chapterVINormalizedCoefficient
  change ((index : ℂ) + 1) * (radius : ℂ) ^ (index + 1) *
      (∑' i, coefficient i index) =
    ∑' i, ((index : ℂ) + 1) * (radius : ℂ) ^ (index + 1) *
      coefficient i index
  simpa only [mul_assoc] using
    (hsummable.tsum_mul_left
      (((index : ℂ) + 1) * (radius : ℂ) ^ (index + 1))).symm

/-- Tannery's theorem supplies the infinite-tail step missing from the finite amplitude-jet
argument.  A summable majorant, uniform for all sufficiently large coefficient indices, permits
the individually subleading positive-order logarithmic terms to be summed without changing the
leading Darboux spectrum. -/
theorem tendsto_chapterVINormalizedCoefficient_logAnalyticAmplitudeRemainder
    {radius : ℝ≥0} {singularityInverse : ℂ}
    (hunit : ‖chapterVIUnitBase radius singularityInverse‖ = 1)
    (jet : ℕ → ℂ) (bound : ℕ → ℝ)
    (hsummableCoefficient : ∀ index, Summable fun order : ℕ ↦
      jet (order + 1) *
        chapterVIHigherVanishingLogCoefficient singularityInverse (order + 1) index)
    (hsummableBound : Summable bound)
    (hbound : ∀ᶠ index : ℕ in atTop, ∀ order : ℕ,
      ‖chapterVINormalizedCoefficient radius
        (fun n ↦ jet (order + 1) *
          chapterVIHigherVanishingLogCoefficient singularityInverse (order + 1) n)
        index‖ ≤ bound order) :
    Tendsto
      (chapterVINormalizedCoefficient radius
        (chapterVILogAnalyticAmplitudeRemainderCoefficient singularityInverse jet))
      atTop (nhds 0) := by
  let term : ℕ → ℕ → ℂ := fun index order ↦
    chapterVINormalizedCoefficient radius
      (fun n ↦ jet (order + 1) *
        chapterVIHigherVanishingLogCoefficient singularityInverse (order + 1) n)
      index
  have hterm (order : ℕ) : Tendsto (fun index ↦ term index order) atTop (nhds 0) := by
    have h :=
      (tendsto_chapterVINormalizedCoefficient_higherVanishingLog hunit order).const_mul
        (jet (order + 1))
    convert h using 1
    funext index
    exact chapterVINormalizedCoefficient_const_mul radius (jet (order + 1))
      (chapterVIHigherVanishingLogCoefficient singularityInverse (order + 1)) index
    simp
  have htsum : Tendsto (fun index ↦ ∑' order, term index order)
      atTop (nhds (∑' _order : ℕ, (0 : ℂ))) :=
    tendsto_tsum_of_dominated_convergence hsummableBound hterm hbound
  have heq : (fun index ↦ ∑' order, term index order) =
      chapterVINormalizedCoefficient radius
        (chapterVILogAnalyticAmplitudeRemainderCoefficient singularityInverse jet) := by
    funext index
    symm
    exact chapterVINormalizedCoefficient_tsum radius
      (fun order n ↦ jet (order + 1) *
        chapterVIHigherVanishingLogCoefficient singularityInverse (order + 1) n)
      index (hsummableCoefficient index)
  rw [← heq]
  simpa using htsum

/-- Sum the coefficient contributions of finite logarithmic amplitude jets at several boundary
singularities. -/
def chapterVIFiniteLogAmplitudeJetCoefficient {r jetOrder : ℕ}
    (singularityInverse : Fin r → ℂ) (jet : Fin r → Fin (jetOrder + 1) → ℂ)
    (index : ℕ) : ℂ :=
  ∑ j, chapterVILogAmplitudeJetCoefficient (singularityInverse j) (jet j) index

/-- Finite amplitude jets have the same leading spectrum as their constant values at the
singularities; every positive-order jet coefficient is rigorously subleading. -/
theorem tendsto_chapterVINormalizedCoefficient_sub_finiteLogAmplitudeJetSpectrum
    {r jetOrder : ℕ} {radius : ℝ≥0} (hradius : radius ≠ 0)
    (singularityInverse : Fin r → ℂ) (jet : Fin r → Fin (jetOrder + 1) → ℂ)
    (hunit : ∀ j, ‖chapterVIUnitBase radius (singularityInverse j)‖ = 1) :
    Tendsto
      (chapterVINormalizedCoefficient radius
          (chapterVIFiniteLogAmplitudeJetCoefficient singularityInverse jet) -
        chapterVIFiniteExponentialMoment
          (fun j ↦ chapterVIUnitBase radius (singularityInverse j))
          (fun j ↦ chapterVILogSpectrumWeight radius (singularityInverse j) (jet j 0)))
      atTop (nhds 0) := by
  let remainder : ℕ → ℂ := fun index ↦
    ∑ j, chapterVILogAmplitudeJetRemainderCoefficient
      (singularityInverse j) (jet j) index
  have hremainderTerm (j : Fin r) : Tendsto
      (chapterVINormalizedCoefficient radius
        (chapterVILogAmplitudeJetRemainderCoefficient (singularityInverse j) (jet j)))
      atTop (nhds 0) :=
    tendsto_chapterVINormalizedCoefficient_logAmplitudeJetRemainder (hunit j) (jet j)
  have hremainder : Tendsto (chapterVINormalizedCoefficient radius remainder)
      atTop (nhds 0) := by
    have hsum := tendsto_finsetSum (Finset.univ : Finset (Fin r))
      (fun j _ ↦ hremainderTerm j)
    convert hsum using 1
    · funext index
      exact chapterVINormalizedCoefficient_finset_sum radius Finset.univ
        (fun j ↦ chapterVILogAmplitudeJetRemainderCoefficient
          (singularityInverse j) (jet j)) index
    · simp
  convert hremainder using 1
  funext index
  have hleading :
      chapterVINormalizedCoefficient radius
          (fun n ↦ ∑ j, jet j 0 *
            chapterVILogTaylorCoefficient (singularityInverse j) (n + 1)) index =
        chapterVIFiniteExponentialMoment
          (fun j ↦ chapterVIUnitBase radius (singularityInverse j))
          (fun j ↦ chapterVILogSpectrumWeight radius
            (singularityInverse j) (jet j 0)) index := by
    classical
    simp_rw [chapterVILogTaylorCoefficient_succ]
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
  unfold chapterVIFiniteLogAmplitudeJetCoefficient
  simp_rw [chapterVILogAmplitudeJetCoefficient_eq_leading_add_remainder]
  simp only [Finset.sum_add_distrib]
  unfold remainder
  rw [Pi.sub_apply]
  unfold chapterVINormalizedCoefficient at hleading ⊢
  rw [mul_add, hleading]
  ring

/-- A finite collection of logarithmic singularities with genuinely analytic varying
amplitudes. Each amplitude is represented as its value at the singularity plus the vanishing
factor times a regular analytic function. -/
def chapterVIFiniteRegularAnalyticLogAmplitudeCoefficient {r : ℕ}
    (singularityInverse leadingAmplitude : Fin r → ℂ)
    (regularAmplitudeCoefficient : Fin r → ℕ → ℂ) (index : ℕ) : ℂ :=
  ∑ j, (leadingAmplitude j *
      chapterVILogTaylorCoefficient (singularityInverse j) (index + 1) +
    chapterVIRegularAmplitudeLogRemainderCoefficient
      (singularityInverse j) (regularAmplitudeCoefficient j) index)

/-- Darboux transfer for the source-faithful factorization
`G(z) = G(z₀) + (1-z/z₀)H(z)`: if each regular factor `H` is analytic beyond the common boundary
circle, only `G(z₀)` contributes to the leading finite spectrum. -/
theorem tendsto_chapterVINormalizedCoefficient_sub_finiteRegularAnalyticLogAmplitudeSpectrum
    {r : ℕ} {radius : ℝ≥0} (hradius : radius ≠ 0)
    (singularityInverse leadingAmplitude : Fin r → ℂ)
    (regularAmplitudeCoefficient : Fin r → ℕ → ℂ)
    (regularAmplitude : Fin r → ℂ → ℂ) (analyticRadius : Fin r → ℝ≥0)
    (hunit : ∀ j, ‖chapterVIUnitBase radius (singularityInverse j)‖ = 1)
    (hradii : ∀ j, radius < analyticRadius j)
    (hanalytic : ∀ j, HasFPowerSeriesOnBall (regularAmplitude j)
      (FormalMultilinearSeries.ofScalars ℂ (regularAmplitudeCoefficient j)) 0
      (analyticRadius j)) :
    Tendsto
      (chapterVINormalizedCoefficient radius
          (chapterVIFiniteRegularAnalyticLogAmplitudeCoefficient
            singularityInverse leadingAmplitude regularAmplitudeCoefficient) -
        chapterVIFiniteExponentialMoment
          (fun j ↦ chapterVIUnitBase radius (singularityInverse j))
          (fun j ↦ chapterVILogSpectrumWeight radius
            (singularityInverse j) (leadingAmplitude j)))
      atTop (nhds 0) := by
  let remainder : ℕ → ℂ := fun index ↦ ∑ j,
    chapterVIRegularAmplitudeLogRemainderCoefficient
      (singularityInverse j) (regularAmplitudeCoefficient j) index
  have hremainderTerm (j : Fin r) : Tendsto
      (chapterVINormalizedCoefficient radius
        (chapterVIRegularAmplitudeLogRemainderCoefficient
          (singularityInverse j) (regularAmplitudeCoefficient j))) atTop (nhds 0) :=
    tendsto_chapterVINormalizedCoefficient_regularAmplitudeLogRemainder_of_analytic
      (hunit j) (hradii j) (regularAmplitudeCoefficient j) (regularAmplitude j) (hanalytic j)
  have hremainder : Tendsto (chapterVINormalizedCoefficient radius remainder)
      atTop (nhds 0) := by
    have hsum := tendsto_finsetSum (Finset.univ : Finset (Fin r))
      (fun j _ ↦ hremainderTerm j)
    convert hsum using 1
    · funext index
      exact chapterVINormalizedCoefficient_finset_sum radius Finset.univ
        (fun j ↦ chapterVIRegularAmplitudeLogRemainderCoefficient
          (singularityInverse j) (regularAmplitudeCoefficient j)) index
    · simp
  convert hremainder using 1
  funext index
  have hleading :
      chapterVINormalizedCoefficient radius
          (fun n ↦ ∑ j, leadingAmplitude j *
            chapterVILogTaylorCoefficient (singularityInverse j) (n + 1)) index =
        chapterVIFiniteExponentialMoment
          (fun j ↦ chapterVIUnitBase radius (singularityInverse j))
          (fun j ↦ chapterVILogSpectrumWeight radius
            (singularityInverse j) (leadingAmplitude j)) index := by
    classical
    simp_rw [chapterVILogTaylorCoefficient_succ]
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
  unfold chapterVIFiniteRegularAnalyticLogAmplitudeCoefficient remainder
  simp only [Finset.sum_add_distrib, Pi.sub_apply]
  unfold chapterVINormalizedCoefficient at hleading ⊢
  rw [mul_add, hleading]
  ring

/-- Coefficients contributed by finitely many logarithmic singularities whose analytic
amplitudes are represented by infinite local power series.  Order zero is separated from the
positive-order `tsum` so that the leading Darboux spectrum remains explicit. -/
def chapterVIFiniteLogAnalyticAmplitudeCoefficient {r : ℕ}
    (singularityInverse : Fin r → ℂ) (jet : Fin r → ℕ → ℂ) (index : ℕ) : ℂ :=
  ∑ j, (jet j 0 * chapterVILogTaylorCoefficient (singularityInverse j) (index + 1) +
    chapterVILogAnalyticAmplitudeRemainderCoefficient (singularityInverse j) (jet j) index)

/-- Infinite analytic logarithmic amplitudes have the same leading finite spectrum as their
values at the singularities, provided Tannery's summable uniform bound holds for every positive
amplitude order. -/
theorem tendsto_chapterVINormalizedCoefficient_sub_finiteLogAnalyticAmplitudeSpectrum
    {r : ℕ} {radius : ℝ≥0} (hradius : radius ≠ 0)
    (singularityInverse : Fin r → ℂ) (jet : Fin r → ℕ → ℂ)
    (bound : Fin r → ℕ → ℝ)
    (hunit : ∀ j, ‖chapterVIUnitBase radius (singularityInverse j)‖ = 1)
    (hsummableCoefficient : ∀ j index, Summable fun order : ℕ ↦
      jet j (order + 1) * chapterVIHigherVanishingLogCoefficient
        (singularityInverse j) (order + 1) index)
    (hsummableBound : ∀ j, Summable (bound j))
    (hbound : ∀ j, ∀ᶠ index : ℕ in atTop, ∀ order : ℕ,
      ‖chapterVINormalizedCoefficient radius
        (fun n ↦ jet j (order + 1) * chapterVIHigherVanishingLogCoefficient
          (singularityInverse j) (order + 1) n) index‖ ≤ bound j order) :
    Tendsto
      (chapterVINormalizedCoefficient radius
          (chapterVIFiniteLogAnalyticAmplitudeCoefficient singularityInverse jet) -
        chapterVIFiniteExponentialMoment
          (fun j ↦ chapterVIUnitBase radius (singularityInverse j))
          (fun j ↦ chapterVILogSpectrumWeight radius (singularityInverse j) (jet j 0)))
      atTop (nhds 0) := by
  let remainder : ℕ → ℂ := fun index ↦ ∑ j,
    chapterVILogAnalyticAmplitudeRemainderCoefficient
      (singularityInverse j) (jet j) index
  have hremainderTerm (j : Fin r) : Tendsto
      (chapterVINormalizedCoefficient radius
        (chapterVILogAnalyticAmplitudeRemainderCoefficient
          (singularityInverse j) (jet j))) atTop (nhds 0) :=
    tendsto_chapterVINormalizedCoefficient_logAnalyticAmplitudeRemainder
      (hunit j) (jet j) (bound j) (hsummableCoefficient j)
        (hsummableBound j) (hbound j)
  have hremainder : Tendsto (chapterVINormalizedCoefficient radius remainder)
      atTop (nhds 0) := by
    have hsum := tendsto_finsetSum (Finset.univ : Finset (Fin r))
      (fun j _ ↦ hremainderTerm j)
    convert hsum using 1
    · funext index
      exact chapterVINormalizedCoefficient_finset_sum radius Finset.univ
        (fun j ↦ chapterVILogAnalyticAmplitudeRemainderCoefficient
          (singularityInverse j) (jet j)) index
    · simp
  convert hremainder using 1
  funext index
  have hleading :
      chapterVINormalizedCoefficient radius
          (fun n ↦ ∑ j, jet j 0 *
            chapterVILogTaylorCoefficient (singularityInverse j) (n + 1)) index =
        chapterVIFiniteExponentialMoment
          (fun j ↦ chapterVIUnitBase radius (singularityInverse j))
          (fun j ↦ chapterVILogSpectrumWeight radius
            (singularityInverse j) (jet j 0)) index := by
    classical
    simp_rw [chapterVILogTaylorCoefficient_succ]
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
  unfold chapterVIFiniteLogAnalyticAmplitudeCoefficient remainder
  simp only [Finset.sum_add_distrib, Pi.sub_apply]
  unfold chapterVINormalizedCoefficient at hleading ⊢
  rw [mul_add, hleading]
  ring

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
