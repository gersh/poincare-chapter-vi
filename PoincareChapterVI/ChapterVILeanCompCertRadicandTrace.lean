/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.ChapterVILeanCompCertPolarTrace
import PoincareChapterVI.ChapterVIDOuterArcInterval

/-!
# Compiled sparse-radicand traces

This trace evaluates the rational part of Poincaré's D radicand while retaining the polar
dependencies proved in `ChapterVILeanCompCertPolarTrace`.  The two exponential values enter as
rectangles widened by the analytic first-order remainder theorem; every subsequent product is a
signed-dyadic operation checked by LeanCompCert.
-/

namespace PoincareChapterVI

open ChapterVILeanCompCertBatch

namespace ChapterVILeanCompCertRadicandTrace

abbrev Interval (precision : ℕ) := ChapterVISignedDyadicInterval precision
abbrev Rectangle (precision : ℕ) := ChapterVISignedDyadicComplexRectangle precision

/-- All rounded intermediates for one polar cell. -/
structure Trace {precision : ℕ}
    (zeta radius : Interval precision) (unit : Rectangle precision) where
  exponentialCoefficient : Interval precision
  inverse10001 : Interval precision
  polar : ChapterVILeanCompCertPolarTrace.Trace radius unit
  zetaInv : Interval precision
  argument : ChapterVISignedDyadicComplexRectangle.RealMulTrace
    exponentialCoefficient (polar.uCubeInv.output.sub polar.uCube.output)
  uLinear : ChapterVISignedDyadicComplexRectangle.MulTrace polar.u.output
    ((ChapterVISignedDyadicComplexRectangle.pointInt precision 1).add argument.output)
  yApprox : ChapterVISignedDyadicComplexRectangle.RealMulTrace zeta uLinear.output
  uInvLinear : ChapterVISignedDyadicComplexRectangle.MulTrace polar.uInv.output
    ((ChapterVISignedDyadicComplexRectangle.pointInt precision 1).sub argument.output)
  yInvApprox : ChapterVISignedDyadicComplexRectangle.RealMulTrace zetaInv uInvLinear.output
  argumentNorm : Interval precision
  argumentNormSq : Interval precision
  yScale : Interval precision
  yError : Interval precision
  yInvScale : Interval precision
  yInvError : Interval precision
  laurentPlus : ChapterVISignedDyadicComplexRectangle.RealMulTrace inverse10001
    (((polar.uCube.output.nsmul 10000).add polar.uCubeInv.output).add
      (ChapterVISignedDyadicComplexRectangle.pointInt precision (-200)))
  laurentMinus : ChapterVISignedDyadicComplexRectangle.RealMulTrace inverse10001
    ((polar.uCube.output.add (polar.uCubeInv.output.nsmul 10000)).add
      (ChapterVISignedDyadicComplexRectangle.pointInt precision (-200)))
  product : ChapterVISignedDyadicComplexRectangle.MulTrace
    (laurentPlus.output.sub ((yApprox.output.widenUpper yError).nsmul 2))
    (laurentMinus.output.sub ((yInvApprox.output.widenUpper yInvError).nsmul 2))

def Trace.operations {precision : ℕ}
    {zeta radius : Interval precision} {unit : Rectangle precision}
    (trace : Trace zeta radius unit) : List (DyadicOperation precision) :=
  trace.polar.operations ++
    [ .positiveReciprocal zeta trace.zetaInv ] ++
    trace.argument.operations ++ trace.uLinear.operations ++ trace.yApprox.operations ++
      trace.uInvLinear.operations ++ trace.yInvApprox.operations ++
      [ .mul trace.exponentialCoefficient
          (trace.polar.radiusCubeInv.add trace.polar.radiusCube) trace.argumentNorm
      , .mul trace.argumentNorm trace.argumentNorm trace.argumentNormSq
      , .mul zeta radius trace.yScale
      , .mul trace.yScale trace.argumentNormSq trace.yError
      , .mul trace.zetaInv trace.polar.radiusInv trace.yInvScale
      , .mul trace.yInvScale trace.argumentNormSq trace.yInvError ] ++
      trace.laurentPlus.operations ++ trace.laurentMinus.operations ++ trace.product.operations

def Trace.output {precision : ℕ}
    {zeta radius : Interval precision} {unit : Rectangle precision}
    (trace : Trace zeta radius unit) : Rectangle precision :=
  trace.product.output

def Trace.y {precision : ℕ}
    {zeta radius : Interval precision} {unit : Rectangle precision}
    (trace : Trace zeta radius unit) : Rectangle precision :=
  trace.yApprox.output.widenUpper trace.yError

def Trace.yInv {precision : ℕ}
    {zeta radius : Interval precision} {unit : Rectangle precision}
    (trace : Trace zeta radius unit) : Rectangle precision :=
  trace.yInvApprox.output.widenUpper trace.yInvError

theorem Trace.approximations_contain_of_allSound {precision : ℕ}
    {zeta radius : Interval precision} {unit : Rectangle precision}
    (trace : Trace zeta radius unit)
    (hall : ∀ operation ∈ trace.operations, operation.Sound)
    {ζ r : ℝ} {v : ℂ} (hζ : zeta.Contains ζ) (hr : radius.Contains r)
    (hv : unit.Contains v) (hvNorm : ‖v‖ = 1)
    (hcoefficient : trace.exponentialCoefficient.Contains (100 / 30003 : ℝ)) :
    trace.argument.output.Contains
        (chapterVIDRootExponentialArgument ((r : ℂ) * v)) ∧
      trace.yApprox.output.Contains
        ((ζ : ℂ) * chapterVIDRootToOriginalContourLinearApprox ((r : ℂ) * v)) ∧
      trace.yInvApprox.output.Contains
        (((ζ : ℂ)⁻¹) * (((r : ℂ) * v)⁻¹) *
          (1 - chapterVIDRootExponentialArgument ((r : ℂ) * v))) := by
  have hpolarSound : ∀ operation ∈ trace.polar.operations, operation.Sound := by
    intro operation hoperation
    exact hall operation (by simp [Trace.operations, hoperation])
  have hargumentSound : ∀ operation ∈ trace.argument.operations, operation.Sound := by
    intro operation hoperation
    exact hall operation (by simp [Trace.operations, hoperation])
  have huLinearSound : ∀ operation ∈ trace.uLinear.operations, operation.Sound := by
    intro operation hoperation
    exact hall operation (by simp [Trace.operations, hoperation])
  have hySound : ∀ operation ∈ trace.yApprox.operations, operation.Sound := by
    intro operation hoperation
    exact hall operation (by simp [Trace.operations, hoperation])
  have huInvLinearSound : ∀ operation ∈ trace.uInvLinear.operations, operation.Sound := by
    intro operation hoperation
    exact hall operation (by simp [Trace.operations, hoperation])
  have hyInvSound : ∀ operation ∈ trace.yInvApprox.operations, operation.Sound := by
    intro operation hoperation
    exact hall operation (by simp [Trace.operations, hoperation])
  have hzetaInvCert : ChapterVISignedDyadicInterval.PositiveReciprocalCertificate
      zeta trace.zetaInv :=
    hall (.positiveReciprocal zeta trace.zetaInv) (by simp [Trace.operations])
  rcases trace.polar.outputs_contain_of_allSound hpolarSound hr hv hvNorm with
    ⟨hu, huInv, huCube, huCubeInv⟩
  have hdifference := ChapterVISignedDyadicComplexRectangle.sub_contains huCubeInv huCube
  have hargument := trace.argument.output_contains_of_allSound
    hargumentSound hcoefficient hdifference
  have hone := ChapterVISignedDyadicComplexRectangle.pointInt_contains precision 1
  have honePlus := ChapterVISignedDyadicComplexRectangle.add_contains hone hargument
  have huLinear := trace.uLinear.output_contains_mul_of_allSound huLinearSound hu honePlus
  have hy := trace.yApprox.output_contains_of_allSound hySound hζ huLinear
  have hζInv := hzetaInvCert.contains_inv hζ
  have honeMinus := ChapterVISignedDyadicComplexRectangle.sub_contains hone hargument
  have huInvLinear := trace.uInvLinear.output_contains_mul_of_allSound
    huInvLinearSound huInv honeMinus
  have hyInv := trace.yInvApprox.output_contains_of_allSound hyInvSound hζInv huInvLinear
  refine ⟨?_, ?_, ?_⟩
  · simpa [chapterVIDRootExponentialArgument] using hargument
  · simpa [chapterVIDRootToOriginalContourLinearApprox,
      chapterVIDRootExponentialArgument, mul_assoc] using hy
  · simpa [chapterVIDRootExponentialArgument, mul_assoc] using hyInv

theorem Trace.remainder_bounds_of_allSound {precision : ℕ}
    {zeta radius : Interval precision} {unit : Rectangle precision}
    (trace : Trace zeta radius unit)
    (hall : ∀ operation ∈ trace.operations, operation.Sound)
    {ζ r : ℝ} {v : ℂ} (hζ : zeta.Contains ζ) (hr : radius.Contains r)
    (hvNorm : ‖v‖ = 1)
    (hcoefficient : trace.exponentialCoefficient.Contains (100 / 30003 : ℝ))
    (hζPos : 0 < ζ) (hrPos : 0 < r) :
    ‖((ζ : ℂ))‖ *
        (‖(r : ℂ) * v‖ * ‖chapterVIDRootExponentialArgument ((r : ℂ) * v)‖ ^ 2) ≤
        (trace.yError.upper : ℝ) / ChapterVISignedDyadicInterval.scale precision ∧
      ‖((ζ : ℂ)⁻¹)‖ *
        (‖((r : ℂ) * v)⁻¹‖ * ‖chapterVIDRootExponentialArgument ((r : ℂ) * v)‖ ^ 2) ≤
        (trace.yInvError.upper : ℝ) / ChapterVISignedDyadicInterval.scale precision := by
  have hpolarSound : ∀ operation ∈ trace.polar.operations, operation.Sound := by
    intro operation hoperation
    exact hall operation (by simp [Trace.operations, hoperation])
  rcases trace.polar.radial_outputs_contain_of_allSound hpolarSound hr with
    ⟨hrInv, hrCube, hrCubeInv⟩
  have hzetaInvCert : ChapterVISignedDyadicInterval.PositiveReciprocalCertificate
      zeta trace.zetaInv :=
    hall (.positiveReciprocal zeta trace.zetaInv) (by simp [Trace.operations])
  have hargCert : ChapterVISignedDyadicInterval.MulCertificate
      trace.exponentialCoefficient
      (trace.polar.radiusCubeInv.add trace.polar.radiusCube) trace.argumentNorm :=
    hall (.mul trace.exponentialCoefficient
      (trace.polar.radiusCubeInv.add trace.polar.radiusCube) trace.argumentNorm)
      (by simp [Trace.operations])
  have hargSqCert : ChapterVISignedDyadicInterval.MulCertificate
      trace.argumentNorm trace.argumentNorm trace.argumentNormSq :=
    hall (.mul trace.argumentNorm trace.argumentNorm trace.argumentNormSq)
      (by simp [Trace.operations])
  have hyScaleCert : ChapterVISignedDyadicInterval.MulCertificate
      zeta radius trace.yScale :=
    hall (.mul zeta radius trace.yScale) (by simp [Trace.operations])
  have hyErrorCert : ChapterVISignedDyadicInterval.MulCertificate
      trace.yScale trace.argumentNormSq trace.yError :=
    hall (.mul trace.yScale trace.argumentNormSq trace.yError)
      (by simp [Trace.operations])
  have hyInvScaleCert : ChapterVISignedDyadicInterval.MulCertificate
      trace.zetaInv trace.polar.radiusInv trace.yInvScale :=
    hall (.mul trace.zetaInv trace.polar.radiusInv trace.yInvScale)
      (by simp [Trace.operations])
  have hyInvErrorCert : ChapterVISignedDyadicInterval.MulCertificate
      trace.yInvScale trace.argumentNormSq trace.yInvError :=
    hall (.mul trace.yInvScale trace.argumentNormSq trace.yInvError)
      (by simp [Trace.operations])
  let bound : ℝ := (100 / 30003 : ℝ) * ((r ^ 3)⁻¹ + r ^ 3)
  have hsum := ChapterVISignedDyadicInterval.add_contains hrCubeInv hrCube
  have hbound : trace.argumentNorm.Contains bound := by
    exact hargCert.contains_mul hcoefficient hsum
  have hboundSq : trace.argumentNormSq.Contains (bound ^ 2) := by
    simpa [pow_two] using hargSqCert.contains_mul hbound hbound
  have hyScale := hyScaleCert.contains_mul hζ hr
  have hyBound : trace.yError.Contains (ζ * r * bound ^ 2) :=
    hyErrorCert.contains_mul hyScale hboundSq
  have hζInv := hzetaInvCert.contains_inv hζ
  have hyInvScale := hyInvScaleCert.contains_mul hζInv hrInv
  have hyInvBound : trace.yInvError.Contains (ζ⁻¹ * r⁻¹ * bound ^ 2) :=
    hyInvErrorCert.contains_mul hyInvScale hboundSq
  have hargument := norm_chapterVIDRootExponentialArgument_le ((r : ℂ) * v)
  have hnormu : ‖(r : ℂ) * v‖ = r := by
    rw [norm_mul, hvNorm, mul_one]
    simp [abs_of_pos hrPos]
  have hboundNonneg : 0 ≤ bound := by
    dsimp [bound]
    positivity
  rw [hnormu] at hargument
  have hargumentSq :
      ‖chapterVIDRootExponentialArgument ((r : ℂ) * v)‖ ^ 2 ≤ bound ^ 2 := by
    dsimp [bound]
    nlinarith [norm_nonneg (chapterVIDRootExponentialArgument ((r : ℂ) * v))]
  have hnormζ : ‖((ζ : ℂ))‖ = ζ := by
    simp [abs_of_pos hζPos]
  have hnormζInv : ‖((ζ : ℂ)⁻¹)‖ = ζ⁻¹ := by
    rw [norm_inv, hnormζ]
  have hnormuInv : ‖((r : ℂ) * v)⁻¹‖ = r⁻¹ := by
    rw [norm_inv, hnormu]
  have hyUpper : ζ * (r * bound ^ 2) ≤
      (trace.yError.upper : ℝ) / ChapterVISignedDyadicInterval.scale precision := by
    simpa [ChapterVISignedDyadicInterval.Contains,
      ChapterVISignedDyadicInterval.toRealInterval, mul_assoc] using hyBound.2
  have hyInvUpper : ζ⁻¹ * (r⁻¹ * bound ^ 2) ≤
      (trace.yInvError.upper : ℝ) / ChapterVISignedDyadicInterval.scale precision := by
    simpa [ChapterVISignedDyadicInterval.Contains,
      ChapterVISignedDyadicInterval.toRealInterval, mul_assoc] using hyInvBound.2
  constructor
  · rw [hnormζ, hnormu]
    exact (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hargumentSq hrPos.le) hζPos.le).trans hyUpper
  · rw [hnormζInv, hnormuInv]
    exact (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hargumentSq (inv_nonneg.mpr hrPos.le))
      (inv_nonneg.mpr hζPos.le)).trans hyInvUpper

theorem Trace.anomalies_contain_of_allSound {precision : ℕ}
    {zeta radius : Interval precision} {unit : Rectangle precision}
    (trace : Trace zeta radius unit)
    (hall : ∀ operation ∈ trace.operations, operation.Sound)
    {ζ r : ℝ} {v : ℂ} (hζ : zeta.Contains ζ) (hr : radius.Contains r)
    (hv : unit.Contains v) (hvNorm : ‖v‖ = 1)
    (hcoefficient : trace.exponentialCoefficient.Contains (100 / 30003 : ℝ))
    (hζPos : 0 < ζ) (hrPos : 0 < r)
    (hargument : ‖chapterVIDRootExponentialArgument ((r : ℂ) * v)‖ ≤ 1) :
    trace.y.Contains (chapterVIDRootSecondAnomaly (ζ : ℂ) ((r : ℂ) * v)) ∧
      trace.yInv.Contains (chapterVIDRootSecondAnomaly (ζ : ℂ) ((r : ℂ) * v))⁻¹ := by
  rcases trace.approximations_contain_of_allSound hall hζ hr hv hvNorm hcoefficient with
    ⟨_, hyApprox, hyInvApprox⟩
  rcases trace.remainder_bounds_of_allSound hall hζ hr hvNorm hcoefficient hζPos hrPos with
    ⟨hyError, hyInvError⟩
  have hvNe : v ≠ 0 := by
    intro hvZero
    rw [hvZero, norm_zero] at hvNorm
    norm_num at hvNorm
  have huNe : (r : ℂ) * v ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr hrPos.ne') hvNe
  constructor
  · apply ChapterVISignedDyadicComplexRectangle.widenUpper_contains_of_norm_sub_le
      (by simpa [Trace.y, chapterVIDRootSecondAnomalyLinearApprox] using hyApprox)
    exact (norm_chapterVIDRootSecondAnomaly_sub_linearApprox_le hargument).trans hyError
  · have hyInvApproxExact : trace.yInvApprox.output.Contains
        (chapterVIDRootSecondAnomalyInvLinearApprox (ζ : ℂ) ((r : ℂ) * v)) := by
      simpa [chapterVIDRootSecondAnomalyInvLinearApprox, mul_assoc] using hyInvApprox
    exact ChapterVISignedDyadicComplexRectangle.widenUpper_contains_of_norm_sub_le
      (x := trace.yInvApprox.output) (error := trace.yInvError)
      (approximation := chapterVIDRootSecondAnomalyInvLinearApprox
        (ζ : ℂ) ((r : ℂ) * v)) hyInvApproxExact
      ((norm_chapterVIDRootSecondAnomaly_inv_sub_invLinearApprox_le
        (Complex.ofReal_ne_zero.mpr hζPos.ne') huNe hargument).trans hyInvError)

/-- Once the analytic remainder enclosures for `y` and `y⁻¹` are supplied, the compiled trace
encloses the exact sparse radicand. -/
theorem Trace.output_contains_sparse_of_allSound {precision : ℕ}
    {zeta radius : Interval precision} {unit : Rectangle precision}
    (trace : Trace zeta radius unit)
    (hall : ∀ operation ∈ trace.operations, operation.Sound)
    {r : ℝ} {v y yInv : ℂ} (hr : radius.Contains r)
    (hv : unit.Contains v) (hvNorm : ‖v‖ = 1)
    (hinverse10001 : trace.inverse10001.Contains (1 / 10001 : ℝ))
    (hy : trace.y.Contains y) (hyInv : trace.yInv.Contains yInv) :
    trace.output.Contains
      (((((1 / 10001 : ℝ) : ℂ) *
            ((10000 : ℂ) * (((r : ℂ) * v) ^ 3) + ((((r : ℂ) * v) ^ 3)⁻¹) - 200)) -
          2 * y) *
        ((((1 / 10001 : ℝ) : ℂ) *
            ((((r : ℂ) * v) ^ 3) + 10000 * ((((r : ℂ) * v) ^ 3)⁻¹) - 200)) -
          2 * yInv)) := by
  have hpolarSound : ∀ operation ∈ trace.polar.operations, operation.Sound := by
    intro operation hoperation
    exact hall operation (by simp [Trace.operations, hoperation])
  have hplusSound : ∀ operation ∈ trace.laurentPlus.operations, operation.Sound := by
    intro operation hoperation
    exact hall operation (by simp [Trace.operations, hoperation])
  have hminusSound : ∀ operation ∈ trace.laurentMinus.operations, operation.Sound := by
    intro operation hoperation
    exact hall operation (by simp [Trace.operations, hoperation])
  have hproductSound : ∀ operation ∈ trace.product.operations, operation.Sound := by
    intro operation hoperation
    exact hall operation (by simp [Trace.operations, hoperation])
  rcases trace.polar.outputs_contain_of_allSound hpolarSound hr hv hvNorm with
    ⟨_, _, huCube, huCubeInv⟩
  have hminus200 := ChapterVISignedDyadicComplexRectangle.pointInt_contains precision (-200)
  have hplusInput := ChapterVISignedDyadicComplexRectangle.add_contains
    (ChapterVISignedDyadicComplexRectangle.add_contains
      (ChapterVISignedDyadicComplexRectangle.nsmul_contains 10000 huCube) huCubeInv)
    hminus200
  have hminusInput := ChapterVISignedDyadicComplexRectangle.add_contains
    (ChapterVISignedDyadicComplexRectangle.add_contains huCube
      (ChapterVISignedDyadicComplexRectangle.nsmul_contains 10000 huCubeInv))
    hminus200
  have hplus := trace.laurentPlus.output_contains_of_allSound
    hplusSound hinverse10001 hplusInput
  have hminus := trace.laurentMinus.output_contains_of_allSound
    hminusSound hinverse10001 hminusInput
  have hfactorPlus := ChapterVISignedDyadicComplexRectangle.sub_contains hplus
    (ChapterVISignedDyadicComplexRectangle.nsmul_contains 2 hy)
  have hfactorMinus := ChapterVISignedDyadicComplexRectangle.sub_contains hminus
    (ChapterVISignedDyadicComplexRectangle.nsmul_contains 2 hyInv)
  have hproduct := trace.product.output_contains_mul_of_allSound
    hproductSound hfactorPlus hfactorMinus
  change trace.product.output.Contains _
  convert hproduct using 1 <;> ring

/-- End-to-end semantic form for one checked polar cell. -/
theorem Trace.output_contains_rootCoordinateRadicand_of_allSound {precision : ℕ}
    {zeta radius : Interval precision} {unit : Rectangle precision}
    (trace : Trace zeta radius unit)
    (hall : ∀ operation ∈ trace.operations, operation.Sound)
    {ζ r : ℝ} {v : ℂ} (hζ : zeta.Contains ζ) (hr : radius.Contains r)
    (hv : unit.Contains v) (hvNorm : ‖v‖ = 1)
    (hcoefficient : trace.exponentialCoefficient.Contains (100 / 30003 : ℝ))
    (hinverse10001 : trace.inverse10001.Contains (1 / 10001 : ℝ))
    (hζPos : 0 < ζ) (hrPos : 0 < r)
    (hargument : ‖chapterVIDRootExponentialArgument ((r : ℂ) * v)‖ ≤ 1) :
    trace.output.Contains
      (chapterVIDRootCoordinateRadicand (ζ : ℂ) ((r : ℂ) * v)) := by
  have hvNe : v ≠ 0 := by
    intro hvZero
    rw [hvZero, norm_zero] at hvNorm
    norm_num at hvNorm
  have huNe : (r : ℂ) * v ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr hrPos.ne') hvNe
  rw [chapterVIDRootCoordinateRadicand_eq_polarCertificateFormula
    (Complex.ofReal_ne_zero.mpr hζPos.ne') huNe]
  rcases trace.anomalies_contain_of_allSound hall hζ hr hv hvNorm hcoefficient
    hζPos hrPos hargument with ⟨hy, hyInv⟩
  exact trace.output_contains_sparse_of_allSound hall hr hv hvNorm
    hinverse10001 hy hyInv

end ChapterVILeanCompCertRadicandTrace

end PoincareChapterVI
