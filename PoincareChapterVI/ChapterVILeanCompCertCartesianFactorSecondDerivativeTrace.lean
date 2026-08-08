/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.ChapterVILeanCompCertCartesianFactorDerivativeTrace

/-!
# Cartesian interval trace for second-order connector curvature

The first derivative of the vanishing collision factor is zero at the collapsed point `D`.
Consequently the scale-relevant affine quantity is not `f'(u) * Δ` at the endpoint but
`f''(u) * Δ²`, the derivative of that path derivative.  This file expands the literal second
derivative into LeanCompCert operations.  The trace retains both copies of the connector
direction and therefore does not erase the quadratic scale.
-/

noncomputable section

namespace PoincareChapterVI

/-- Imaginary part of the first path derivative along an affine root-coordinate connector. -/
def chapterVIDRootCoordinateCollisionFactorPlusLineDerivativeImag
    (ζ source target : ℂ) (t : ℝ) : ℝ :=
  (chapterVIDRootCoordinateCollisionFactorPlusDerivative ζ
    (AffineMap.lineMap source target t) * (target - source)).im

set_option backward.isDefEq.respectTransparency.types false in
/-- The affine curvature `f''(u) Δ²` is the real derivative of the path derivative. -/
theorem hasDerivAt_chapterVIDRootCoordinateCollisionFactorPlusLineDerivativeImag
    {ζ source target : ℂ} {t : ℝ}
    (hu : AffineMap.lineMap source target t ≠ 0) :
    HasDerivAt
      (chapterVIDRootCoordinateCollisionFactorPlusLineDerivativeImag ζ source target)
      (chapterVIDRootCoordinateCollisionFactorPlusSecondDerivative ζ
        (AffineMap.lineMap source target t) * (target - source) ^ 2).im t := by
  let line : ℂ → ℂ := fun w ↦ (target - source) * w + source
  have hline := ((hasDerivAt_id (t : ℂ)).const_mul (target - source)).add_const source
  have hu' : line (t : ℂ) ≠ 0 := by
    simpa [line, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add,
      smul_eq_mul, mul_comm] using hu
  have hfactor :=
    hasDerivAt_chapterVIDRootCoordinateCollisionFactorPlusDerivative (ζ := ζ) hu'
  have hcomp := hfactor.comp (t : ℂ) hline
  have hproduct := hcomp.mul_const (target - source)
  have hproduct' : HasDerivAt
      (fun w ↦ (chapterVIDRootCoordinateCollisionFactorPlusDerivative ζ ∘ line) w *
        (target - source))
      (chapterVIDRootCoordinateCollisionFactorPlusSecondDerivative ζ (line (t : ℂ)) *
        (target - source) ^ 2) (t : ℂ) :=
    hproduct.congr_deriv (by ring)
  have him := (hproduct'.mul_const (-Complex.I)).real_of_complex
  change HasDerivAt
    (fun x : ℝ ↦ (chapterVIDRootCoordinateCollisionFactorPlusDerivative ζ
      (AffineMap.lineMap source target x) * (target - source)).im) _ t
  simpa [line, Function.comp_apply, AffineMap.lineMap_apply, vsub_eq_sub,
    vadd_eq_add, smul_eq_mul, Complex.mul_re, Complex.mul_im, mul_comm] using him

namespace ChapterVILeanCompCertCartesianFactorSecondDerivativeTrace

open ChapterVILeanCompCertBatch
open ChapterVILeanCompCertCartesianRadicandTrace
open ChapterVILeanCompCertProposals

abbrev Interval (precision : ℕ) := ChapterVISignedDyadicInterval precision
abbrev Rectangle (precision : ℕ) := ChapterVISignedDyadicComplexRectangle precision

/-- Rounded intermediates for `f''(u) * Δ²`. -/
structure Trace {precision : ℕ} {zeta coordinate : Rectangle precision}
    (base : ChapterVILeanCompCertCartesianRadicandTrace.Trace zeta coordinate)
    (logCoefficient secondCoefficient : Interval precision)
    (delta : Rectangle precision) where
  coordinateInvFourth : ChapterVISignedDyadicComplexRectangle.MulTrace
    base.coordinateInvCube.output base.coordinateInv.output
  coordinateInvFifth : ChapterVISignedDyadicComplexRectangle.MulTrace
    coordinateInvFourth.output base.coordinateInv.output
  coordinateInvSquare : ChapterVISignedDyadicComplexRectangle.MulTrace
    base.coordinateInv.output base.coordinateInv.output
  logCorrection : ChapterVISignedDyadicComplexRectangle.RealMulTrace logCoefficient
    (coordinateInvFourth.output.add base.coordinateCube.square.output)
  anomalyTimesLog : ChapterVISignedDyadicComplexRectangle.MulTrace base.y
    (base.coordinateInv.output.sub logCorrection.output)
  anomalyLogOverCoordinate : ChapterVISignedDyadicComplexRectangle.MulTrace
    anomalyTimesLog.output base.coordinateInv.output
  anomalyOverCoordinateSquare : ChapterVISignedDyadicComplexRectangle.MulTrace
    base.y coordinateInvSquare.output
  laurentSecondDerivative : ChapterVISignedDyadicComplexRectangle.RealMulTrace
    base.inverse10001
    ((coordinate.nsmul 60000).add (coordinateInvFifth.output.nsmul 12))
  anomalyLogTimesPowerSum : ChapterVISignedDyadicComplexRectangle.MulTrace
    anomalyTimesLog.output
    (coordinateInvFourth.output.add base.coordinateCube.square.output)
  anomalyTimesLastSlope : ChapterVISignedDyadicComplexRectangle.MulTrace base.y
    ((coordinate.nsmul 2).sub (coordinateInvFifth.output.nsmul 4))
  lastTerm : ChapterVISignedDyadicComplexRectangle.RealMulTrace secondCoefficient
    (anomalyLogTimesPowerSum.output.add anomalyTimesLastSlope.output)
  deltaSquare : ChapterVISignedDyadicComplexRectangle.MulTrace delta delta
  pathSecondDerivative : ChapterVISignedDyadicComplexRectangle.MulTrace
    ((laurentSecondDerivative.output.sub
      ((anomalyLogOverCoordinate.output.sub
        anomalyOverCoordinateSquare.output).nsmul 2)).add lastTerm.output)
    deltaSquare.output

def Trace.operations {precision : ℕ} {zeta coordinate : Rectangle precision}
    {base : ChapterVILeanCompCertCartesianRadicandTrace.Trace zeta coordinate}
    {logCoefficient secondCoefficient : Interval precision} {delta : Rectangle precision}
    (trace : Trace base logCoefficient secondCoefficient delta) :
    List (DyadicOperation precision) :=
  base.operations ++ trace.coordinateInvFourth.operations ++
    trace.coordinateInvFifth.operations ++ trace.coordinateInvSquare.operations ++
    trace.logCorrection.operations ++ trace.anomalyTimesLog.operations ++
    trace.anomalyLogOverCoordinate.operations ++
    trace.anomalyOverCoordinateSquare.operations ++
    trace.laurentSecondDerivative.operations ++
    trace.anomalyLogTimesPowerSum.operations ++
    trace.anomalyTimesLastSlope.operations ++ trace.lastTerm.operations ++
    trace.deltaSquare.operations ++ trace.pathSecondDerivative.operations

def Trace.output {precision : ℕ} {zeta coordinate : Rectangle precision}
    {base : ChapterVILeanCompCertCartesianRadicandTrace.Trace zeta coordinate}
    {logCoefficient secondCoefficient : Interval precision} {delta : Rectangle precision}
    (trace : Trace base logCoefficient secondCoefficient delta) : Rectangle precision :=
  trace.pathSecondDerivative.output

/-- Deterministic rounded proposal for the second-order terminal certificate. -/
def secondDerivativeTrace {precision : ℕ} {zeta coordinate : Rectangle precision}
    (base : ChapterVILeanCompCertCartesianRadicandTrace.Trace zeta coordinate)
    (logCoefficient secondCoefficient : Interval precision) (delta : Rectangle precision) :
    Trace base logCoefficient secondCoefficient delta := by
  let coordinateInvFourth := mulTrace base.coordinateInvCube.output base.coordinateInv.output
  let coordinateInvFifth := mulTrace coordinateInvFourth.output base.coordinateInv.output
  let coordinateInvSquare := mulTrace base.coordinateInv.output base.coordinateInv.output
  let powerSum := coordinateInvFourth.output.add base.coordinateCube.square.output
  let logCorrection := realMulTrace logCoefficient powerSum
  let logDerivative := base.coordinateInv.output.sub logCorrection.output
  let anomalyTimesLog := mulTrace base.y logDerivative
  let anomalyLogOverCoordinate := mulTrace anomalyTimesLog.output base.coordinateInv.output
  let anomalyOverCoordinateSquare := mulTrace base.y coordinateInvSquare.output
  let laurentInput := (coordinate.nsmul 60000).add (coordinateInvFifth.output.nsmul 12)
  let laurentSecondDerivative := realMulTrace base.inverse10001 laurentInput
  let anomalyLogTimesPowerSum := mulTrace anomalyTimesLog.output powerSum
  let lastSlope := (coordinate.nsmul 2).sub (coordinateInvFifth.output.nsmul 4)
  let anomalyTimesLastSlope := mulTrace base.y lastSlope
  let lastTerm := realMulTrace secondCoefficient
    (anomalyLogTimesPowerSum.output.add anomalyTimesLastSlope.output)
  let secondDerivative :=
    (laurentSecondDerivative.output.sub
      ((anomalyLogOverCoordinate.output.sub
        anomalyOverCoordinateSquare.output).nsmul 2)).add lastTerm.output
  let deltaSquare := mulTrace delta delta
  let pathSecondDerivative := mulTrace secondDerivative deltaSquare.output
  exact {
    coordinateInvFourth := coordinateInvFourth
    coordinateInvFifth := coordinateInvFifth
    coordinateInvSquare := coordinateInvSquare
    logCorrection := logCorrection
    anomalyTimesLog := anomalyTimesLog
    anomalyLogOverCoordinate := anomalyLogOverCoordinate
    anomalyOverCoordinateSquare := anomalyOverCoordinateSquare
    laurentSecondDerivative := laurentSecondDerivative
    anomalyLogTimesPowerSum := anomalyLogTimesPowerSum
    anomalyTimesLastSlope := anomalyTimesLastSlope
    lastTerm := lastTerm
    deltaSquare := deltaSquare
    pathSecondDerivative := pathSecondDerivative }

/-- Kernel reconstruction of the literal affine second derivative from a passing trace. -/
theorem Trace.output_contains_of_allSound
    {precision : ℕ} {zeta coordinate : Rectangle precision}
    {base : ChapterVILeanCompCertCartesianRadicandTrace.Trace zeta coordinate}
    {logCoefficient secondCoefficient : Interval precision} {delta : Rectangle precision}
    (trace : Trace base logCoefficient secondCoefficient delta)
    (hall : ∀ operation ∈ trace.operations, operation.Sound)
    {ζ u direction : ℂ}
    (hu : coordinate.Contains u)
    (hy : base.y.Contains (chapterVIDRootSecondAnomaly ζ u))
    (hinverse10001 : base.inverse10001.Contains (1 / 10001 : ℝ))
    (hlogCoefficient : logCoefficient.Contains (100 / 10001 : ℝ))
    (hsecondCoefficient : secondCoefficient.Contains (200 / 10001 : ℝ))
    (hdirection : delta.Contains direction) :
    trace.output.Contains
      (chapterVIDRootCoordinateCollisionFactorPlusSecondDerivative ζ u * direction ^ 2) := by
  have soundOf {operations : List (DyadicOperation precision)}
      (hsub : ∀ operation ∈ operations, operation ∈ trace.operations) :
      ∀ operation ∈ operations, operation.Sound := by
    intro operation hoperation
    exact hall operation (hsub operation hoperation)
  have hbase : ∀ operation ∈ base.operations, operation.Sound :=
    soundOf (by intro operation hoperation; simp [Trace.operations, hoperation])
  have huInv := base.coordinateInv.output_contains_inv_of_allSound
    (by intro operation hoperation
        exact hbase operation (by
          simp [ChapterVILeanCompCertCartesianRadicandTrace.Trace.operations, hoperation])) hu
  have huInvCube := base.coordinateInvCube.output_contains_cube_of_allSound
    (by intro operation hoperation
        exact hbase operation (by
          simp [ChapterVILeanCompCertCartesianRadicandTrace.Trace.operations, hoperation])) huInv
  have huInvFourth := trace.coordinateInvFourth.output_contains_mul_of_allSound
    (soundOf (by intro operation hoperation; simp [Trace.operations, hoperation]))
    huInvCube huInv
  have huInvFifth := trace.coordinateInvFifth.output_contains_mul_of_allSound
    (soundOf (by intro operation hoperation; simp [Trace.operations, hoperation]))
    huInvFourth huInv
  have huInvSquare := trace.coordinateInvSquare.output_contains_mul_of_allSound
    (soundOf (by intro operation hoperation; simp [Trace.operations, hoperation]))
    huInv huInv
  have huSquare := base.coordinateCube.square.output_contains_mul_of_allSound
    (by intro operation hoperation
        exact hbase operation (by
          simp [ChapterVILeanCompCertCartesianRadicandTrace.Trace.operations,
            ChapterVISignedDyadicComplexRectangle.CubeTrace.operations, hoperation])) hu hu
  have hpowerSum := ChapterVISignedDyadicComplexRectangle.add_contains huInvFourth huSquare
  have hlogCorrection := trace.logCorrection.output_contains_of_allSound
    (soundOf (by intro operation hoperation; simp [Trace.operations, hoperation]))
    hlogCoefficient hpowerSum
  have hlogDerivative := ChapterVISignedDyadicComplexRectangle.sub_contains
    huInv hlogCorrection
  have hanomalyTimesLog := trace.anomalyTimesLog.output_contains_mul_of_allSound
    (soundOf (by intro operation hoperation; simp [Trace.operations, hoperation]))
    hy hlogDerivative
  have hanomalyLogOverCoordinate :=
    trace.anomalyLogOverCoordinate.output_contains_mul_of_allSound
      (soundOf (by intro operation hoperation; simp [Trace.operations, hoperation]))
      hanomalyTimesLog huInv
  have hanomalyOverCoordinateSquare :=
    trace.anomalyOverCoordinateSquare.output_contains_mul_of_allSound
      (soundOf (by intro operation hoperation; simp [Trace.operations, hoperation]))
      hy huInvSquare
  have hlaurentInput := ChapterVISignedDyadicComplexRectangle.add_contains
    (ChapterVISignedDyadicComplexRectangle.nsmul_contains 60000 hu)
    (ChapterVISignedDyadicComplexRectangle.nsmul_contains 12 huInvFifth)
  have hlaurent := trace.laurentSecondDerivative.output_contains_of_allSound
    (soundOf (by intro operation hoperation; simp [Trace.operations, hoperation]))
    hinverse10001 hlaurentInput
  have hanomalyLogTimesPowerSum :=
    trace.anomalyLogTimesPowerSum.output_contains_mul_of_allSound
      (soundOf (by intro operation hoperation; simp [Trace.operations, hoperation]))
      hanomalyTimesLog hpowerSum
  have hlastSlope := ChapterVISignedDyadicComplexRectangle.sub_contains
    (ChapterVISignedDyadicComplexRectangle.nsmul_contains 2 hu)
    (ChapterVISignedDyadicComplexRectangle.nsmul_contains 4 huInvFifth)
  have hanomalyTimesLastSlope :=
    trace.anomalyTimesLastSlope.output_contains_mul_of_allSound
      (soundOf (by intro operation hoperation; simp [Trace.operations, hoperation]))
      hy hlastSlope
  have hlastInput := ChapterVISignedDyadicComplexRectangle.add_contains
    hanomalyLogTimesPowerSum hanomalyTimesLastSlope
  have hlast := trace.lastTerm.output_contains_of_allSound
    (soundOf (by intro operation hoperation; simp [Trace.operations, hoperation]))
    hsecondCoefficient hlastInput
  have hmiddle := ChapterVISignedDyadicComplexRectangle.nsmul_contains 2
    (ChapterVISignedDyadicComplexRectangle.sub_contains
      hanomalyLogOverCoordinate hanomalyOverCoordinateSquare)
  have hsecond := ChapterVISignedDyadicComplexRectangle.add_contains
    (ChapterVISignedDyadicComplexRectangle.sub_contains hlaurent hmiddle) hlast
  have hdeltaSquare := trace.deltaSquare.output_contains_mul_of_allSound
    (soundOf (by intro operation hoperation; simp [Trace.operations, hoperation]))
    hdirection hdirection
  have hpath := trace.pathSecondDerivative.output_contains_mul_of_allSound
    (soundOf (by intro operation hoperation; simp [Trace.operations, hoperation]))
    hsecond hdeltaSquare
  change trace.pathSecondDerivative.output.Contains _
  have heq :
      chapterVIDRootCoordinateCollisionFactorPlusSecondDerivative ζ u * direction ^ 2 =
        ((↑(1 / 10001 : ℝ) * (↑(60000 : ℕ) * u + ↑(12 : ℕ) *
              (u⁻¹ ^ 3 * u⁻¹ * u⁻¹)) -
            ↑(2 : ℕ) *
              ((chapterVIDRootSecondAnomaly ζ u *
                    (u⁻¹ - ↑(100 / 10001 : ℝ) *
                      (u⁻¹ ^ 3 * u⁻¹ + u * u))) * u⁻¹ -
                chapterVIDRootSecondAnomaly ζ u * (u⁻¹ * u⁻¹)) +
            ↑(200 / 10001 : ℝ) *
              ((chapterVIDRootSecondAnomaly ζ u *
                    (u⁻¹ - ↑(100 / 10001 : ℝ) *
                      (u⁻¹ ^ 3 * u⁻¹ + u * u))) *
                  (u⁻¹ ^ 3 * u⁻¹ + u * u) +
                chapterVIDRootSecondAnomaly ζ u *
                  (↑(2 : ℕ) * u - ↑(4 : ℕ) * (u⁻¹ ^ 3 * u⁻¹ * u⁻¹)))) *
          (direction * direction)) := by
    unfold chapterVIDRootCoordinateCollisionFactorPlusSecondDerivative
      chapterVIDRootSecondAnomalyLogDerivative
    push_cast
    ring
  rw [heq]
  exact hpath

end ChapterVILeanCompCertCartesianFactorSecondDerivativeTrace
end PoincareChapterVI
