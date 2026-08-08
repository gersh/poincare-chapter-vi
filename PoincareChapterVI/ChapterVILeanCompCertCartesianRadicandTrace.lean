/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.ChapterVILeanCompCertRadicandTrace

/-!
# Cartesian compiled traces for Poincare's D radicand

The outer-arc checker exploits a polar representation `u = r v`. Connector points are affine
segments and have no such exact representation. This file evaluates the same sparse literal
radicand directly from complex rectangles for `ζ` and `u`.

All rational complex arithmetic, including both reciprocals, is represented by LeanCompCert
operations. Static integer budgets derive norm bounds from the input and intermediate rectangles;
compiled scalar products then propagate the analytic exponential remainder bounds. The only
nontrivial semantic inputs left to a connector cell are rectangles enclosing `ζ` and `u`. Thus a
noncomputable inverse-Morse endpoint is never evaluated by the compiled program, but it also no
longer hides inside a monolithic radicand-containment premise.
-/

namespace PoincareChapterVI

open ChapterVILeanCompCertBatch

namespace ChapterVILeanCompCertCartesianRadicandTrace

abbrev Interval (precision : ℕ) := ChapterVISignedDyadicInterval precision
abbrev Rectangle (precision : ℕ) := ChapterVISignedDyadicComplexRectangle precision

/-- Rounded intermediates for one arbitrary complex-coordinate cell. -/
structure Trace {precision : ℕ}
    (zeta coordinate : Rectangle precision) where
  exponentialCoefficient : Interval precision
  inverse10001 : Interval precision
  zetaInv : ChapterVISignedDyadicComplexRectangle.InvTrace zeta
  coordinateInv : ChapterVISignedDyadicComplexRectangle.InvTrace coordinate
  coordinateCube : ChapterVISignedDyadicComplexRectangle.CubeTrace coordinate
  coordinateInvCube : ChapterVISignedDyadicComplexRectangle.CubeTrace coordinateInv.output
  argument : ChapterVISignedDyadicComplexRectangle.RealMulTrace
    exponentialCoefficient (coordinateInvCube.output.sub coordinateCube.output)
  coordinateLinear : ChapterVISignedDyadicComplexRectangle.MulTrace coordinate
    ((ChapterVISignedDyadicComplexRectangle.pointInt precision 1).add argument.output)
  yApprox : ChapterVISignedDyadicComplexRectangle.MulTrace zeta coordinateLinear.output
  coordinateInvLinear : ChapterVISignedDyadicComplexRectangle.MulTrace coordinateInv.output
    ((ChapterVISignedDyadicComplexRectangle.pointInt precision 1).sub argument.output)
  yInvApprox : ChapterVISignedDyadicComplexRectangle.MulTrace
    zetaInv.output coordinateInvLinear.output
  zetaNorm : Interval precision
  coordinateNorm : Interval precision
  zetaInvNorm : Interval precision
  coordinateInvNorm : Interval precision
  argumentNorm : Interval precision
  zetaNormBound : zeta.L1NormBound zetaNorm
  coordinateNormBound : coordinate.L1NormBound coordinateNorm
  zetaInvNormBound : zetaInv.output.L1NormBound zetaInvNorm
  coordinateInvNormBound : coordinateInv.output.L1NormBound coordinateInvNorm
  argumentNormBound : argument.output.L1NormBound argumentNorm
  argumentNorm_upper_le_one : argumentNorm.upper ≤ (2 : ℤ) ^ precision
  argumentNormSq : Interval precision
  yScale : Interval precision
  yError : Interval precision
  yInvScale : Interval precision
  yInvError : Interval precision
  laurentPlus : ChapterVISignedDyadicComplexRectangle.RealMulTrace inverse10001
    (((coordinateCube.output.nsmul 10000).add coordinateInvCube.output).add
      (ChapterVISignedDyadicComplexRectangle.pointInt precision (-200)))
  laurentMinus : ChapterVISignedDyadicComplexRectangle.RealMulTrace inverse10001
    ((coordinateCube.output.add (coordinateInvCube.output.nsmul 10000)).add
      (ChapterVISignedDyadicComplexRectangle.pointInt precision (-200)))
  product : ChapterVISignedDyadicComplexRectangle.MulTrace
    (laurentPlus.output.sub ((yApprox.output.widenUpper yError).nsmul 2))
    (laurentMinus.output.sub ((yInvApprox.output.widenUpper yInvError).nsmul 2))

def Trace.operations {precision : ℕ}
    {zeta coordinate : Rectangle precision}
    (trace : Trace zeta coordinate) : List (DyadicOperation precision) :=
  trace.zetaInv.operations ++ trace.coordinateInv.operations ++
    trace.coordinateCube.operations ++ trace.coordinateInvCube.operations ++
    trace.argument.operations ++ trace.coordinateLinear.operations ++
    trace.yApprox.operations ++ trace.coordinateInvLinear.operations ++
    trace.yInvApprox.operations ++
    [ .mul trace.argumentNorm trace.argumentNorm trace.argumentNormSq
    , .mul trace.zetaNorm trace.coordinateNorm trace.yScale
    , .mul trace.yScale trace.argumentNormSq trace.yError
    , .mul trace.zetaInvNorm trace.coordinateInvNorm trace.yInvScale
    , .mul trace.yInvScale trace.argumentNormSq trace.yInvError ] ++
    trace.laurentPlus.operations ++
    trace.laurentMinus.operations ++ trace.product.operations

def Trace.output {precision : ℕ}
    {zeta coordinate : Rectangle precision}
    (trace : Trace zeta coordinate) : Rectangle precision :=
  trace.product.output

def Trace.y {precision : ℕ}
    {zeta coordinate : Rectangle precision}
    (trace : Trace zeta coordinate) : Rectangle precision :=
  trace.yApprox.output.widenUpper trace.yError

def Trace.yInv {precision : ℕ}
    {zeta coordinate : Rectangle precision}
    (trace : Trace zeta coordinate) : Rectangle precision :=
  trace.yInvApprox.output.widenUpper trace.yInvError

/-- The compiled arithmetic encloses the exponential argument and the two first-order anomaly
approximations for an arbitrary complex connector coordinate. -/
theorem Trace.approximations_contain_of_allSound {precision : ℕ}
    {zeta coordinate : Rectangle precision}
    (trace : Trace zeta coordinate)
    (hall : ∀ operation ∈ trace.operations, operation.Sound)
    {ζ u : ℂ} (hζ : zeta.Contains ζ) (hu : coordinate.Contains u)
    (hcoefficient : trace.exponentialCoefficient.Contains (100 / 30003 : ℝ)) :
    trace.argument.output.Contains (chapterVIDRootExponentialArgument u) ∧
      trace.yApprox.output.Contains (chapterVIDRootSecondAnomalyLinearApprox ζ u) ∧
      trace.yInvApprox.output.Contains
        (chapterVIDRootSecondAnomalyInvLinearApprox ζ u) := by
  have soundOf {operations : List (DyadicOperation precision)}
      (hsub : ∀ operation ∈ operations, operation ∈ trace.operations) :
      ∀ operation ∈ operations, operation.Sound := by
    intro operation hoperation
    exact hall operation (hsub operation hoperation)
  have hζInv := trace.zetaInv.output_contains_inv_of_allSound
    (soundOf (by intro operation hoperation; simp [Trace.operations, hoperation])) hζ
  have huInv := trace.coordinateInv.output_contains_inv_of_allSound
    (soundOf (by intro operation hoperation; simp [Trace.operations, hoperation])) hu
  have huCube := trace.coordinateCube.output_contains_cube_of_allSound
    (soundOf (by intro operation hoperation; simp [Trace.operations, hoperation])) hu
  have huInvCube := trace.coordinateInvCube.output_contains_cube_of_allSound
    (soundOf (by intro operation hoperation; simp [Trace.operations, hoperation])) huInv
  have huCubeInv : trace.coordinateInvCube.output.Contains (u ^ 3)⁻¹ := by
    simpa only [inv_pow] using huInvCube
  have hdifference := ChapterVISignedDyadicComplexRectangle.sub_contains huCubeInv huCube
  have hargument := trace.argument.output_contains_of_allSound
    (soundOf (by intro operation hoperation; simp [Trace.operations, hoperation]))
    hcoefficient hdifference
  have hone := ChapterVISignedDyadicComplexRectangle.pointInt_contains precision 1
  have huLinear := trace.coordinateLinear.output_contains_mul_of_allSound
    (soundOf (by intro operation hoperation; simp [Trace.operations, hoperation])) hu
    (ChapterVISignedDyadicComplexRectangle.add_contains hone hargument)
  have hy := trace.yApprox.output_contains_mul_of_allSound
    (soundOf (by intro operation hoperation; simp [Trace.operations, hoperation])) hζ huLinear
  have huInvLinear := trace.coordinateInvLinear.output_contains_mul_of_allSound
    (soundOf (by intro operation hoperation; simp [Trace.operations, hoperation])) huInv
    (ChapterVISignedDyadicComplexRectangle.sub_contains hone hargument)
  have hyInv := trace.yInvApprox.output_contains_mul_of_allSound
    (soundOf (by intro operation hoperation; simp [Trace.operations, hoperation]))
    hζInv huInvLinear
  refine ⟨?_, ?_, ?_⟩
  · simpa [chapterVIDRootExponentialArgument] using hargument
  · simpa [chapterVIDRootSecondAnomalyLinearApprox,
      chapterVIDRootToOriginalContourLinearApprox,
      chapterVIDRootExponentialArgument, mul_assoc] using hy
  · simpa [chapterVIDRootSecondAnomalyInvLinearApprox,
      chapterVIDRootExponentialArgument, mul_assoc] using hyInv

/-- Compiled scalar products turn simple norm enclosures into the two analytic remainder bounds. -/
theorem Trace.remainder_bounds_of_allSound {precision : ℕ}
    {zeta coordinate : Rectangle precision}
    (trace : Trace zeta coordinate)
    (hall : ∀ operation ∈ trace.operations, operation.Sound)
    {ζ u : ℂ} (hζ : zeta.Contains ζ) (hu : coordinate.Contains u)
    (hcoefficient : trace.exponentialCoefficient.Contains (100 / 30003 : ℝ)) :
    ‖ζ‖ * (‖u‖ * ‖chapterVIDRootExponentialArgument u‖ ^ 2) ≤
        (trace.yError.upper : ℝ) / ChapterVISignedDyadicInterval.scale precision ∧
      ‖ζ⁻¹‖ * (‖u⁻¹‖ * ‖chapterVIDRootExponentialArgument u‖ ^ 2) ≤
        (trace.yInvError.upper : ℝ) / ChapterVISignedDyadicInterval.scale precision := by
  have certificate (operation : DyadicOperation precision)
      (hoperation : operation ∈ trace.operations) : operation.Sound :=
    hall operation hoperation
  have hζInv := trace.zetaInv.output_contains_inv_of_allSound
    (fun operation hoperation ↦ certificate operation
      (by simp [Trace.operations, hoperation])) hζ
  have huInv := trace.coordinateInv.output_contains_inv_of_allSound
    (fun operation hoperation ↦ certificate operation
      (by simp [Trace.operations, hoperation])) hu
  have hargument := (trace.approximations_contain_of_allSound hall hζ hu
    hcoefficient).1
  have hζNorm := trace.zetaNormBound.contains_norm hζ
  have huNorm := trace.coordinateNormBound.contains_norm hu
  have hζInvNorm := trace.zetaInvNormBound.contains_norm hζInv
  have huInvNorm := trace.coordinateInvNormBound.contains_norm huInv
  have hargumentNorm := trace.argumentNormBound.contains_norm hargument
  have hargSq : trace.argumentNormSq.Contains
      (‖chapterVIDRootExponentialArgument u‖ ^ 2) := by
    have hcert : ChapterVISignedDyadicInterval.MulCertificate
        trace.argumentNorm trace.argumentNorm trace.argumentNormSq :=
      certificate (.mul trace.argumentNorm trace.argumentNorm trace.argumentNormSq)
        (by simp [Trace.operations])
    simpa only [pow_two] using hcert.contains_mul hargumentNorm hargumentNorm
  have hyScale : trace.yScale.Contains (‖ζ‖ * ‖u‖) := by
    have hcert : ChapterVISignedDyadicInterval.MulCertificate
        trace.zetaNorm trace.coordinateNorm trace.yScale :=
      certificate (.mul trace.zetaNorm trace.coordinateNorm trace.yScale)
        (by simp [Trace.operations])
    exact hcert.contains_mul hζNorm huNorm
  have hy : trace.yError.Contains
      ((‖ζ‖ * ‖u‖) * ‖chapterVIDRootExponentialArgument u‖ ^ 2) := by
    have hcert : ChapterVISignedDyadicInterval.MulCertificate
        trace.yScale trace.argumentNormSq trace.yError :=
      certificate (.mul trace.yScale trace.argumentNormSq trace.yError)
        (by simp [Trace.operations])
    exact hcert.contains_mul hyScale hargSq
  have hyInvScale : trace.yInvScale.Contains (‖ζ⁻¹‖ * ‖u⁻¹‖) := by
    have hcert : ChapterVISignedDyadicInterval.MulCertificate
        trace.zetaInvNorm trace.coordinateInvNorm trace.yInvScale :=
      certificate (.mul trace.zetaInvNorm trace.coordinateInvNorm trace.yInvScale)
        (by simp [Trace.operations])
    exact hcert.contains_mul hζInvNorm huInvNorm
  have hyInv : trace.yInvError.Contains
      ((‖ζ⁻¹‖ * ‖u⁻¹‖) * ‖chapterVIDRootExponentialArgument u‖ ^ 2) := by
    have hcert : ChapterVISignedDyadicInterval.MulCertificate
        trace.yInvScale trace.argumentNormSq trace.yInvError :=
      certificate (.mul trace.yInvScale trace.argumentNormSq trace.yInvError)
        (by simp [Trace.operations])
    exact hcert.contains_mul hyInvScale hargSq
  constructor
  · simpa [ChapterVISignedDyadicInterval.Contains,
      ChapterVISignedDyadicInterval.toRealInterval, mul_assoc] using hy.2
  · simpa [ChapterVISignedDyadicInterval.Contains,
      ChapterVISignedDyadicInterval.toRealInterval, mul_assoc] using hyInv.2

/-- The static norm budget attached to the argument rectangle discharges the analytic
first-order exponential hypothesis. -/
theorem Trace.argument_norm_le_one_of_allSound {precision : ℕ}
    {zeta coordinate : Rectangle precision}
    (trace : Trace zeta coordinate)
    (hall : ∀ operation ∈ trace.operations, operation.Sound)
    {ζ u : ℂ} (hζ : zeta.Contains ζ) (hu : coordinate.Contains u)
    (hcoefficient : trace.exponentialCoefficient.Contains (100 / 30003 : ℝ)) :
    ‖chapterVIDRootExponentialArgument u‖ ≤ 1 := by
  have hargument := (trace.approximations_contain_of_allSound hall hζ hu
    hcoefficient).1
  have hnorm := trace.argumentNormBound.contains_norm hargument
  apply hnorm.2.trans
  change (trace.argumentNorm.upper : ℝ) /
      ChapterVISignedDyadicInterval.scale precision ≤ 1
  rw [div_le_iff₀ (ChapterVISignedDyadicInterval.scale_pos precision)]
  have hcast : (trace.argumentNorm.upper : ℝ) ≤ (2 : ℝ) ^ precision := by
    exact_mod_cast trace.argumentNorm_upper_le_one
  simpa [ChapterVISignedDyadicInterval.scale] using hcast

/-- Scalar analytic error bounds widen the compiled first-order approximations to rectangles
containing the exact anomaly and its reciprocal. -/
theorem Trace.anomalies_contain_of_allSound {precision : ℕ}
    {zeta coordinate : Rectangle precision}
    (trace : Trace zeta coordinate)
    (hall : ∀ operation ∈ trace.operations, operation.Sound)
    {ζ u : ℂ} (hζ : zeta.Contains ζ) (hu : coordinate.Contains u)
    (hcoefficient : trace.exponentialCoefficient.Contains (100 / 30003 : ℝ))
    (hζne : ζ ≠ 0) (hune : u ≠ 0) :
    trace.y.Contains (chapterVIDRootSecondAnomaly ζ u) ∧
      trace.yInv.Contains (chapterVIDRootSecondAnomaly ζ u)⁻¹ := by
  rcases trace.approximations_contain_of_allSound hall hζ hu hcoefficient with
    ⟨_, hyApprox, hyInvApprox⟩
  have hargument := trace.argument_norm_le_one_of_allSound hall hζ hu hcoefficient
  rcases trace.remainder_bounds_of_allSound hall hζ hu hcoefficient with
    ⟨hyError, hyInvError⟩
  constructor
  · apply ChapterVISignedDyadicComplexRectangle.widenUpper_contains_of_norm_sub_le
      (x := trace.yApprox.output) (error := trace.yError)
      (approximation := chapterVIDRootSecondAnomalyLinearApprox ζ u) hyApprox
    exact (norm_chapterVIDRootSecondAnomaly_sub_linearApprox_le hargument).trans hyError
  · apply ChapterVISignedDyadicComplexRectangle.widenUpper_contains_of_norm_sub_le
      (x := trace.yInvApprox.output) (error := trace.yInvError)
      (approximation := chapterVIDRootSecondAnomalyInvLinearApprox ζ u) hyInvApprox
    exact (norm_chapterVIDRootSecondAnomaly_inv_sub_invLinearApprox_le
      hζne hune hargument).trans hyInvError

/-- Once the two anomalies are enclosed, the remaining checked arithmetic encloses the exact
sparse radicand expression. -/
theorem Trace.output_contains_sparse_of_allSound {precision : ℕ}
    {zeta coordinate : Rectangle precision}
    (trace : Trace zeta coordinate)
    (hall : ∀ operation ∈ trace.operations, operation.Sound)
    {u y yInv : ℂ} (hu : coordinate.Contains u)
    (hinverse10001 : trace.inverse10001.Contains (1 / 10001 : ℝ))
    (hy : trace.y.Contains y) (hyInv : trace.yInv.Contains yInv) :
    trace.output.Contains
      (((((1 / 10001 : ℝ) : ℂ) *
            ((10000 : ℂ) * u ^ 3 + (u ^ 3)⁻¹ - 200)) - 2 * y) *
        ((((1 / 10001 : ℝ) : ℂ) *
            (u ^ 3 + 10000 * (u ^ 3)⁻¹ - 200)) - 2 * yInv)) := by
  have soundOf {operations : List (DyadicOperation precision)}
      (hsub : ∀ operation ∈ operations, operation ∈ trace.operations) :
      ∀ operation ∈ operations, operation.Sound := by
    intro operation hoperation
    exact hall operation (hsub operation hoperation)
  have huInv := trace.coordinateInv.output_contains_inv_of_allSound
    (soundOf (by intro operation hoperation; simp [Trace.operations, hoperation])) hu
  have huCube := trace.coordinateCube.output_contains_cube_of_allSound
    (soundOf (by intro operation hoperation; simp [Trace.operations, hoperation])) hu
  have huInvCube := trace.coordinateInvCube.output_contains_cube_of_allSound
    (soundOf (by intro operation hoperation; simp [Trace.operations, hoperation])) huInv
  have huCubeInv : trace.coordinateInvCube.output.Contains (u ^ 3)⁻¹ := by
    simpa only [inv_pow] using huInvCube
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
    (soundOf (by intro operation hoperation; simp [Trace.operations, hoperation]))
    hinverse10001 hplusInput
  have hminus := trace.laurentMinus.output_contains_of_allSound
    (soundOf (by intro operation hoperation; simp [Trace.operations, hoperation]))
    hinverse10001 hminusInput
  have hfactorPlus := ChapterVISignedDyadicComplexRectangle.sub_contains hplus
    (ChapterVISignedDyadicComplexRectangle.nsmul_contains 2 hy)
  have hfactorMinus := ChapterVISignedDyadicComplexRectangle.sub_contains hminus
    (ChapterVISignedDyadicComplexRectangle.nsmul_contains 2 hyInv)
  have hproduct := trace.product.output_contains_mul_of_allSound
    (soundOf (by intro operation hoperation; simp [Trace.operations, hoperation]))
    hfactorPlus hfactorMinus
  change trace.product.output.Contains _
  convert hproduct using 1 <;> ring

/-- End-to-end semantic theorem for one checked Cartesian cell. -/
theorem Trace.output_contains_rootCoordinateRadicand_of_allSound {precision : ℕ}
    {zeta coordinate : Rectangle precision}
    (trace : Trace zeta coordinate)
    (hall : ∀ operation ∈ trace.operations, operation.Sound)
    {ζ u : ℂ} (hζ : zeta.Contains ζ) (hu : coordinate.Contains u)
    (hcoefficient : trace.exponentialCoefficient.Contains (100 / 30003 : ℝ))
    (hinverse10001 : trace.inverse10001.Contains (1 / 10001 : ℝ))
    (hζne : ζ ≠ 0) (hune : u ≠ 0) :
    trace.output.Contains (chapterVIDRootCoordinateRadicand ζ u) := by
  rw [chapterVIDRootCoordinateRadicand_eq_polarCertificateFormula hζne hune]
  rcases trace.anomalies_contain_of_allSound hall hζ hu hcoefficient hζne hune
    with ⟨hy, hyInv⟩
  exact trace.output_contains_sparse_of_allSound hall hu hinverse10001 hy hyInv

end ChapterVILeanCompCertCartesianRadicandTrace

end PoincareChapterVI
