/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.ChapterVILeanCompCertCartesianRadicandTrace
import PoincareChapterVI.ChapterVILeanCompCertProposals

/-!
# Cartesian interval trace for the connector collision-factor derivative

The first collision factor is the one that vanishes at Poincare's point D.  Near the two local
connector endpoints, direct interval evaluation loses the dependency between the endpoint and
the Morse length.  A signed enclosure of the derivative along the affine connector can instead
prove one-sided monotonicity from the exact positive endpoint value.

This file differentiates the literal cubic root-coordinate formula and provides the corresponding
LeanCompCert operation trace.  In particular, the exponential derivative is derived from the
actual cubic exponent `(100/30003)(u⁻³-u³)`; no exploratory surrogate is used.
-/

noncomputable section

open Filter

namespace PoincareChapterVI

/-- Exact complex derivative of the vanishing collision factor with respect to `u`. -/
def chapterVIDRootCoordinateCollisionFactorPlusDerivative (ζ u : ℂ) : ℂ :=
  (1 / 10001) * (30000 * u ^ 2 - 3 * u⁻¹ ^ 4) -
    2 * chapterVIDRootSecondAnomaly ζ u * u⁻¹ +
    (200 / 10001) * chapterVIDRootSecondAnomaly ζ u * (u⁻¹ ^ 4 + u ^ 2)

private def chapterVIDRootCoordinateCollisionFactorPlusFormula (ζ u : ℂ) : ℂ :=
  (1 / 10001) * (10000 * u ^ 3 + u⁻¹ ^ 3 - 200) -
    2 * chapterVIDRootSecondAnomaly ζ u

private theorem hasDerivAt_chapterVIDRootCoordinateCollisionFactorPlusFormula
    (ζ : ℂ) {u : ℂ} (hu : u ≠ 0) :
    HasDerivAt (chapterVIDRootCoordinateCollisionFactorPlusFormula ζ)
      (chapterVIDRootCoordinateCollisionFactorPlusDerivative ζ u) u := by
  have hinv := (hasDerivAt_id u).inv hu
  have hinv3 := hinv.pow 3
  have hu3 := (hasDerivAt_id u).pow 3
  have hargument := (hinv3.sub hu3).const_mul (100 / 30003 : ℂ)
  have hexponential := hargument.cexp
  have hcoordinate := (hasDerivAt_id u).mul hexponential
  have hy := (hasDerivAt_const u ζ).mul hcoordinate
  have hlaurent := ((hasDerivAt_const u (1 / 10001 : ℂ)).mul
    (((hasDerivAt_const u (10000 : ℂ)).mul hu3).add hinv3 |>.sub_const 200))
  have hformula := hlaurent.sub ((hasDerivAt_const u (2 : ℂ)).mul hy)
  simp only [id_eq, Pi.inv_apply, Pi.pow_apply, Pi.sub_apply, Pi.add_apply,
    Pi.mul_apply, one_mul, zero_mul, zero_add, Nat.cast_ofNat] at hformula
  have hderivative : HasDerivAt _
      (chapterVIDRootCoordinateCollisionFactorPlusDerivative ζ u) u :=
    hformula.congr_deriv (by
      unfold chapterVIDRootCoordinateCollisionFactorPlusDerivative
        chapterVIDRootSecondAnomaly chapterVIDRootToOriginalContour
        chapterVIDRootExponentialArgument
      simp only [Pi.pow_apply, Pi.sub_apply, Pi.add_apply, Pi.mul_apply,
        Nat.reduceSub]
      field_simp [hu]
      ring)
  apply hderivative.congr_of_eventuallyEq
  filter_upwards [] with w
  simp [chapterVIDRootCoordinateCollisionFactorPlusFormula,
    chapterVIDRootSecondAnomaly, chapterVIDRootToOriginalContour,
    chapterVIDRootExponentialArgument]

/-- The displayed derivative is the derivative of Poincare's literal first collision factor. -/
theorem hasDerivAt_chapterVIDRootCoordinateCollisionFactorPlus
    {ζ u : ℂ} (hζ : ζ ≠ 0) (hu : u ≠ 0) :
    HasDerivAt (chapterVIDRootCoordinateCollisionFactorPlus ζ)
      (chapterVIDRootCoordinateCollisionFactorPlusDerivative ζ u) u := by
  apply (hasDerivAt_chapterVIDRootCoordinateCollisionFactorPlusFormula ζ hu).congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds hu] with w hw
  rw [chapterVIDRootCoordinateCollisionFactorPlus_eq_polarCertificateFormula hζ hw]
  simp [chapterVIDRootCoordinateCollisionFactorPlusFormula, inv_pow]

namespace ChapterVILeanCompCertCartesianFactorDerivativeTrace

open ChapterVILeanCompCertBatch
open ChapterVILeanCompCertCartesianRadicandTrace
open ChapterVILeanCompCertProposals

abbrev Interval (precision : ℕ) := ChapterVISignedDyadicInterval precision
abbrev Rectangle (precision : ℕ) := ChapterVISignedDyadicComplexRectangle precision

/-- Rounded intermediates for the first factor's derivative along one affine connector. -/
structure Trace {precision : ℕ} {zeta coordinate : Rectangle precision}
    (base : ChapterVILeanCompCertCartesianRadicandTrace.Trace zeta coordinate)
    (derivativeCoefficient : Interval precision) (delta : Rectangle precision) where
  coordinateInvFourth : ChapterVISignedDyadicComplexRectangle.MulTrace
    base.coordinateInvCube.output base.coordinateInv.output
  anomalyTimesPowerSum : ChapterVISignedDyadicComplexRectangle.MulTrace base.y
    (coordinateInvFourth.output.add base.coordinateCube.square.output)
  anomalyDerivative : ChapterVISignedDyadicComplexRectangle.RealMulTrace
    derivativeCoefficient anomalyTimesPowerSum.output
  twoAnomalyOverCoordinate : ChapterVISignedDyadicComplexRectangle.MulTrace
    (base.y.nsmul 2) base.coordinateInv.output
  laurentDerivative : ChapterVISignedDyadicComplexRectangle.RealMulTrace base.inverse10001
    ((base.coordinateCube.square.output.nsmul 30000).sub
      (coordinateInvFourth.output.nsmul 3))
  pathDerivative : ChapterVISignedDyadicComplexRectangle.MulTrace
    ((laurentDerivative.output.sub twoAnomalyOverCoordinate.output).add
      anomalyDerivative.output) delta

def Trace.operations {precision : ℕ} {zeta coordinate : Rectangle precision}
    {base : ChapterVILeanCompCertCartesianRadicandTrace.Trace zeta coordinate}
    {derivativeCoefficient : Interval precision} {delta : Rectangle precision}
    (trace : Trace base derivativeCoefficient delta) : List (DyadicOperation precision) :=
  base.operations ++ trace.coordinateInvFourth.operations ++
    trace.anomalyTimesPowerSum.operations ++ trace.anomalyDerivative.operations ++
    trace.twoAnomalyOverCoordinate.operations ++ trace.laurentDerivative.operations ++
    trace.pathDerivative.operations

def Trace.output {precision : ℕ} {zeta coordinate : Rectangle precision}
    {base : ChapterVILeanCompCertCartesianRadicandTrace.Trace zeta coordinate}
    {derivativeCoefficient : Interval precision} {delta : Rectangle precision}
    (trace : Trace base derivativeCoefficient delta) : Rectangle precision :=
  trace.pathDerivative.output

/-- Deterministic rounded proposal used by the certificate generator. -/
def derivativeTrace {precision : ℕ} {zeta coordinate : Rectangle precision}
    (base : ChapterVILeanCompCertCartesianRadicandTrace.Trace zeta coordinate)
    (derivativeCoefficient : Interval precision) (delta : Rectangle precision) :
    Trace base derivativeCoefficient delta := by
  let coordinateInvFourth := mulTrace base.coordinateInvCube.output base.coordinateInv.output
  let powerSum := coordinateInvFourth.output.add base.coordinateCube.square.output
  let anomalyTimesPowerSum := mulTrace base.y powerSum
  let anomalyDerivative := realMulTrace derivativeCoefficient anomalyTimesPowerSum.output
  let twoAnomalyOverCoordinate := mulTrace (base.y.nsmul 2) base.coordinateInv.output
  let laurentInput := (base.coordinateCube.square.output.nsmul 30000).sub
    (coordinateInvFourth.output.nsmul 3)
  let laurentDerivative := realMulTrace base.inverse10001 laurentInput
  let derivative := (laurentDerivative.output.sub twoAnomalyOverCoordinate.output).add
    anomalyDerivative.output
  let pathDerivative := mulTrace derivative delta
  exact {
    coordinateInvFourth := coordinateInvFourth
    anomalyTimesPowerSum := anomalyTimesPowerSum
    anomalyDerivative := anomalyDerivative
    twoAnomalyOverCoordinate := twoAnomalyOverCoordinate
    laurentDerivative := laurentDerivative
    pathDerivative := pathDerivative }

/-- Semantic reconstruction of the compiled derivative trace. -/
theorem Trace.output_contains_of_allSound
    {precision : ℕ} {zeta coordinate : Rectangle precision}
    {base : ChapterVILeanCompCertCartesianRadicandTrace.Trace zeta coordinate}
    {derivativeCoefficient : Interval precision} {delta : Rectangle precision}
    (trace : Trace base derivativeCoefficient delta)
    (hall : ∀ operation ∈ trace.operations, operation.Sound)
    {ζ u direction : ℂ}
    (hu : coordinate.Contains u)
    (hy : base.y.Contains (chapterVIDRootSecondAnomaly ζ u))
    (hinverse10001 : base.inverse10001.Contains (1 / 10001 : ℝ))
    (hderivativeCoefficient : derivativeCoefficient.Contains (200 / 10001 : ℝ))
    (hdirection : delta.Contains direction) :
    trace.output.Contains
      (chapterVIDRootCoordinateCollisionFactorPlusDerivative ζ u * direction) := by
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
  have huSquare := base.coordinateCube.square.output_contains_mul_of_allSound
    (by intro operation hoperation
        exact hbase operation (by
          simp [ChapterVILeanCompCertCartesianRadicandTrace.Trace.operations,
            ChapterVISignedDyadicComplexRectangle.CubeTrace.operations, hoperation])) hu hu
  have hpowerSum := ChapterVISignedDyadicComplexRectangle.add_contains
    huInvFourth huSquare
  have hanomalyTimesPowerSum :=
    trace.anomalyTimesPowerSum.output_contains_mul_of_allSound
      (soundOf (by intro operation hoperation; simp [Trace.operations, hoperation]))
      hy hpowerSum
  have hanomalyDerivative := trace.anomalyDerivative.output_contains_of_allSound
    (soundOf (by intro operation hoperation; simp [Trace.operations, hoperation]))
    hderivativeCoefficient hanomalyTimesPowerSum
  have htwoAnomaly := ChapterVISignedDyadicComplexRectangle.nsmul_contains 2 hy
  have htwoAnomalyOverCoordinate :=
    trace.twoAnomalyOverCoordinate.output_contains_mul_of_allSound
      (soundOf (by intro operation hoperation; simp [Trace.operations, hoperation]))
      htwoAnomaly huInv
  have hlaurentInput := ChapterVISignedDyadicComplexRectangle.sub_contains
    (ChapterVISignedDyadicComplexRectangle.nsmul_contains 30000 huSquare)
    (ChapterVISignedDyadicComplexRectangle.nsmul_contains 3 huInvFourth)
  have hlaurentDerivative := trace.laurentDerivative.output_contains_of_allSound
    (soundOf (by intro operation hoperation; simp [Trace.operations, hoperation]))
    hinverse10001 hlaurentInput
  have hfactorDerivative := ChapterVISignedDyadicComplexRectangle.add_contains
    (ChapterVISignedDyadicComplexRectangle.sub_contains hlaurentDerivative
      htwoAnomalyOverCoordinate) hanomalyDerivative
  have hpathDerivative := trace.pathDerivative.output_contains_mul_of_allSound
    (soundOf (by intro operation hoperation; simp [Trace.operations, hoperation]))
    hfactorDerivative hdirection
  change trace.pathDerivative.output.Contains _
  have heq :
      chapterVIDRootCoordinateCollisionFactorPlusDerivative ζ u * direction =
        ((↑(1 / 10001 : ℝ) *
            (↑(30000 : ℕ) * (u * u) - ↑(3 : ℕ) * (u⁻¹ ^ 3 * u⁻¹)) -
          ↑(2 : ℕ) * chapterVIDRootSecondAnomaly ζ u * u⁻¹ +
          ↑(200 / 10001 : ℝ) *
            (chapterVIDRootSecondAnomaly ζ u * (u⁻¹ ^ 3 * u⁻¹ + u * u))) * direction) := by
    unfold chapterVIDRootCoordinateCollisionFactorPlusDerivative
    push_cast
    ring
  rw [heq]
  exact hpathDerivative

end ChapterVILeanCompCertCartesianFactorDerivativeTrace
end PoincareChapterVI
