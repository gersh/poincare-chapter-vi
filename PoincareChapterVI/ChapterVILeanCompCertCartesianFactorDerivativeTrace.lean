/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.ChapterVILeanCompCertCartesianRadicandTrace
import PoincareChapterVI.ChapterVILeanCompCertProposals
import PoincareChapterVI.ChapterVIDMovingRootBridge
import Mathlib.Analysis.Complex.RealDeriv

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

/-- Logarithmic derivative of the transformed second anomaly with respect to the root
coordinate. -/
def chapterVIDRootSecondAnomalyLogDerivative (u : ℂ) : ℂ :=
  u⁻¹ - (100 / 10001) * (u⁻¹ ^ 4 + u ^ 2)

/-- Exact second derivative of the vanishing collision factor with respect to `u`.  The
factorization through the anomaly's logarithmic derivative is also the arithmetic layout used by
the forthcoming second-order terminal trace. -/
def chapterVIDRootCoordinateCollisionFactorPlusSecondDerivative (ζ u : ℂ) : ℂ :=
  (1 / 10001) * (60000 * u + 12 * u⁻¹ ^ 5) -
    2 * (chapterVIDRootSecondAnomaly ζ u *
        chapterVIDRootSecondAnomalyLogDerivative u * u⁻¹ -
      chapterVIDRootSecondAnomaly ζ u * u⁻¹ ^ 2) +
    (200 / 10001) *
      (chapterVIDRootSecondAnomaly ζ u *
          chapterVIDRootSecondAnomalyLogDerivative u * (u⁻¹ ^ 4 + u ^ 2) +
        chapterVIDRootSecondAnomaly ζ u * (-4 * u⁻¹ ^ 5 + 2 * u))

/-- The named logarithmic derivative differentiates the literal transformed second anomaly. -/
theorem hasDerivAt_chapterVIDRootSecondAnomaly
    {ζ u : ℂ} (hu : u ≠ 0) :
    HasDerivAt (chapterVIDRootSecondAnomaly ζ)
      (chapterVIDRootSecondAnomaly ζ u *
        chapterVIDRootSecondAnomalyLogDerivative u) u := by
  have hinv := (hasDerivAt_id u).inv hu
  have hinv3 := hinv.pow 3
  have hu3 := (hasDerivAt_id u).pow 3
  have hargument := (hinv3.sub hu3).const_mul (100 / 30003 : ℂ)
  have hexponential := hargument.cexp
  have hcoordinate := (hasDerivAt_id u).mul hexponential
  have hy := (hasDerivAt_const u ζ).mul hcoordinate
  have hderivative : HasDerivAt _
      (chapterVIDRootSecondAnomaly ζ u *
        chapterVIDRootSecondAnomalyLogDerivative u) u :=
    hy.congr_deriv (by
      unfold chapterVIDRootSecondAnomaly chapterVIDRootToOriginalContour
        chapterVIDRootExponentialArgument chapterVIDRootSecondAnomalyLogDerivative
      simp only [id_eq, Pi.inv_apply, Pi.pow_apply, Pi.sub_apply, Pi.add_apply,
        Pi.mul_apply, one_mul, zero_mul, zero_add, Nat.cast_ofNat]
      simp only [inv_pow]
      field_simp [hu]
      ring)
  apply hderivative.congr_of_eventuallyEq
  filter_upwards [] with w
  simp [chapterVIDRootSecondAnomaly, chapterVIDRootToOriginalContour,
    chapterVIDRootExponentialArgument]

/-- The displayed second derivative differentiates the first-derivative formula. -/
theorem hasDerivAt_chapterVIDRootCoordinateCollisionFactorPlusDerivative
    {ζ u : ℂ} (hu : u ≠ 0) :
    HasDerivAt (chapterVIDRootCoordinateCollisionFactorPlusDerivative ζ)
      (chapterVIDRootCoordinateCollisionFactorPlusSecondDerivative ζ u) u := by
  have hid := hasDerivAt_id u
  have hinv := hid.inv hu
  have hy := hasDerivAt_chapterVIDRootSecondAnomaly (ζ := ζ) hu
  have hlaurent := (hasDerivAt_const u (1 / 10001 : ℂ)).mul
    ((((hasDerivAt_const u (30000 : ℂ)).mul (hid.pow 2)).sub
      ((hasDerivAt_const u (3 : ℂ)).mul (hinv.pow 4))))
  have hmiddle := (hasDerivAt_const u (2 : ℂ)).mul (hy.mul hinv)
  have hlast := (hasDerivAt_const u (200 / 10001 : ℂ)).mul
    (hy.mul ((hinv.pow 4).add (hid.pow 2)))
  have h := hlaurent.sub hmiddle |>.add hlast
  have hderivative : HasDerivAt _
      (chapterVIDRootCoordinateCollisionFactorPlusSecondDerivative ζ u) u :=
    h.congr_deriv (by
      unfold chapterVIDRootCoordinateCollisionFactorPlusSecondDerivative
        chapterVIDRootSecondAnomalyLogDerivative
      simp only [id_eq, Pi.inv_apply, Pi.pow_apply, Pi.sub_apply, Pi.add_apply,
        Pi.mul_apply, one_mul, zero_mul, zero_add, Nat.cast_ofNat]
      simp only [inv_pow]
      field_simp [hu]
      ring)
  apply hderivative.congr_of_eventuallyEq
  filter_upwards [] with w
  simp [chapterVIDRootCoordinateCollisionFactorPlusDerivative]
  ring

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

/-- At the collapsed connector endpoint the first collision factor has zero first derivative.
This is the exact algebraic reason that no fixed positive-margin derivative certificate can cover
the endpoint merely by increasing interval precision: a terminal certificate must retain the
second-order Morse scale instead. -/
theorem chapterVIDRootCoordinateCollisionFactorPlusDerivative_base :
    chapterVIDRootCoordinateCollisionFactorPlusDerivative
      chapterVIDZRootBase chapterVIDCollisionLift = 0 := by
  unfold chapterVIDRootCoordinateCollisionFactorPlusDerivative
  rw [chapterVIDRootSecondAnomaly_base]
  have hu : chapterVIDCollisionLift ≠ 0 := chapterVIDCollisionLift_ne_zero
  have hx : (chapterVIDRoot : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_lt chapterVIDRoot_lt_zero)
  have hu3 : chapterVIDCollisionLift ^ 3 = (chapterVIDRoot : ℂ) := by
    simpa only [chapterVIDX] using chapterVIDCollisionLift_pow
  have hu6 : chapterVIDCollisionLift ^ 6 = (chapterVIDRoot : ℂ) ^ 2 := by
    calc
      chapterVIDCollisionLift ^ 6 = (chapterVIDCollisionLift ^ 3) ^ 2 := by ring
      _ = (chapterVIDRoot : ℂ) ^ 2 := by rw [hu3]
  have hroot : (chapterVIDPolynomial chapterVIDRoot : ℂ) = 0 := by
    exact_mod_cast chapterVIDRoot_isRoot
  unfold chapterVIDY chapterVIDX
  field_simp [hu, hx]
  ring_nf
  rw [hu3, hu6]
  field_simp [hx]
  unfold chapterVIDPolynomial at hroot
  push_cast at hroot
  linear_combination ((800 : ℂ) * chapterVIDRoot - 8) * hroot

/-- Exact algebraic reduction of the second derivative at `D`.  All transcendental terms have
disappeared: Poincaré's equation (7) reduces the result to a rational function of its isolated
algebraic root. -/
theorem chapterVIDRootCoordinateCollisionFactorPlusSecondDerivative_base_formula :
    chapterVIDRootCoordinateCollisionFactorPlusSecondDerivative
      chapterVIDZRootBase chapterVIDCollisionLift =
      chapterVIDCollisionLift *
        (-18 * (33327498249925 * (chapterVIDRoot : ℂ) ^ 2 +
          833324982499 * (chapterVIDRoot : ℂ) - 1666499975) /
          (2500500025 * (chapterVIDRoot : ℂ) ^ 4)) := by
  unfold chapterVIDRootCoordinateCollisionFactorPlusSecondDerivative
    chapterVIDRootSecondAnomalyLogDerivative
  rw [chapterVIDRootSecondAnomaly_base]
  have hu : chapterVIDCollisionLift ≠ 0 := chapterVIDCollisionLift_ne_zero
  have hx : (chapterVIDRoot : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_lt chapterVIDRoot_lt_zero)
  have hu3 : chapterVIDCollisionLift ^ 3 = (chapterVIDRoot : ℂ) := by
    simpa only [chapterVIDX] using chapterVIDCollisionLift_pow
  have hu6 : chapterVIDCollisionLift ^ 6 = (chapterVIDRoot : ℂ) ^ 2 := by
    calc
      chapterVIDCollisionLift ^ 6 = (chapterVIDCollisionLift ^ 3) ^ 2 := by ring
      _ = (chapterVIDRoot : ℂ) ^ 2 := by rw [hu3]
  have hu9 : chapterVIDCollisionLift ^ 9 = (chapterVIDRoot : ℂ) ^ 3 := by
    calc
      chapterVIDCollisionLift ^ 9 = (chapterVIDCollisionLift ^ 3) ^ 3 := by ring
      _ = (chapterVIDRoot : ℂ) ^ 3 := by rw [hu3]
  have hu12 : chapterVIDCollisionLift ^ 12 = (chapterVIDRoot : ℂ) ^ 4 := by
    calc
      chapterVIDCollisionLift ^ 12 = (chapterVIDCollisionLift ^ 3) ^ 4 := by ring
      _ = (chapterVIDRoot : ℂ) ^ 4 := by rw [hu3]
  have hroot : (chapterVIDPolynomial chapterVIDRoot : ℂ) = 0 := by
    exact_mod_cast chapterVIDRoot_isRoot
  unfold chapterVIDY chapterVIDX
  field_simp [hu, hx]
  ring_nf
  rw [hu3, hu6, hu9, hu12]
  field_simp [hx]
  unfold chapterVIDPolynomial at hroot
  push_cast at hroot
  linear_combination
    (-200040002000000 * (chapterVIDRoot : ℂ) ^ 3 +
      120038004000140000 * (chapterVIDRoot : ℂ) ^ 2 -
      12005000760050001200 * (chapterVIDRoot : ℂ) +
      2400479965984798699964) * hroot

/-- The small quadratic numerator controlling the second derivative is negative.  The only
finite input is the compiled `10⁻¹²` isolation certificate for the root of equation (7). -/
theorem chapterVIDRoot_secondDerivativeQuadratic_neg :
    33327498249925 * chapterVIDRoot ^ 2 +
      833324982499 * chapterVIDRoot - 1666499975 < 0 := by
  have hleft := chapterVIDRoot_ultrafine_mem.1
  have hright := chapterVIDRoot_ultrafine_mem.2
  have hsquare : chapterVIDRoot ^ 2 ≤
      (-26865395705 / 1000000000000 : ℝ) ^ 2 := by
    have hproduct : 0 ≤
        (chapterVIDRoot - (-26865395705 / 1000000000000 : ℝ)) *
          (-chapterVIDRoot - (-26865395705 / 1000000000000 : ℝ)) :=
      mul_nonneg (by linarith) (by linarith [chapterVIDRoot_lt_zero])
    nlinarith
  nlinarith

/-- The double zero has the orientation required by Poincaré's terminal local argument. -/
theorem chapterVIDRootCoordinateCollisionFactorPlusSecondDerivative_base_re_neg :
    (chapterVIDRootCoordinateCollisionFactorPlusSecondDerivative
      chapterVIDZRootBase chapterVIDCollisionLift).re < 0 := by
  rw [chapterVIDRootCoordinateCollisionFactorPlusSecondDerivative_base_formula,
    chapterVIDCollisionLift_eq_neg_norm]
  have hq := chapterVIDRoot_secondDerivativeQuadratic_neg
  have hx2 : 0 < chapterVIDRoot ^ 2 := sq_pos_of_ne_zero chapterVIDRoot_lt_zero.ne
  have hx4 : 0 < chapterVIDRoot ^ 4 := by
    nlinarith [mul_pos hx2 hx2]
  have hnorm : 0 < ‖chapterVIDCollisionLift‖ :=
    norm_pos_iff.mpr chapterVIDCollisionLift_ne_zero
  have hscalar :
      (-18 * (33327498249925 * (chapterVIDRoot : ℂ) ^ 2 +
          833324982499 * (chapterVIDRoot : ℂ) - 1666499975) /
          (2500500025 * (chapterVIDRoot : ℂ) ^ 4)) =
        ((-18 * (33327498249925 * chapterVIDRoot ^ 2 +
          833324982499 * chapterVIDRoot - 1666499975) /
          (2500500025 * chapterVIDRoot ^ 4) : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hscalar]
  simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im]
  have hpositive : 0 <
      -18 * (33327498249925 * chapterVIDRoot ^ 2 +
        833324982499 * chapterVIDRoot - 1666499975) /
        (2500500025 * chapterVIDRoot ^ 4) :=
    div_pos (mul_pos_of_neg_of_neg (by norm_num) hq)
      (mul_pos (by norm_num) hx4)
  nlinarith [mul_pos hnorm hpositive]

theorem chapterVIDRootCoordinateCollisionFactorPlusSecondDerivative_base_ne_zero :
    chapterVIDRootCoordinateCollisionFactorPlusSecondDerivative
      chapterVIDZRootBase chapterVIDCollisionLift ≠ 0 := by
  intro hzero
  have hre := congrArg Complex.re hzero
  simp only [Complex.zero_re] at hre
  linarith [chapterVIDRootCoordinateCollisionFactorPlusSecondDerivative_base_re_neg]

/-- Imaginary part of the first collision factor along an affine line in root coordinates. -/
def chapterVIDRootCoordinateCollisionFactorPlusLineImag
    (ζ source target : ℂ) (t : ℝ) : ℝ :=
  (chapterVIDRootCoordinateCollisionFactorPlus ζ
    (AffineMap.lineMap source target t)).im

set_option backward.isDefEq.respectTransparency.types false in
/-- The displayed complex derivative is exactly the real derivative used by the connector
monotonicity argument.  Multiplication by `-I` turns imaginary part into real part, allowing the
standard complex-to-real derivative theorem to discharge the final projection. -/
theorem hasDerivAt_chapterVIDRootCoordinateCollisionFactorPlusLineImag
    {ζ source target : ℂ} {t : ℝ}
    (hζ : ζ ≠ 0) (hu : AffineMap.lineMap source target t ≠ 0) :
    HasDerivAt (chapterVIDRootCoordinateCollisionFactorPlusLineImag ζ source target)
      (chapterVIDRootCoordinateCollisionFactorPlusDerivative ζ
        (AffineMap.lineMap source target t) * (target - source)).im t := by
  let line : ℂ → ℂ := fun w ↦ (target - source) * w + source
  have hline := ((hasDerivAt_id (t : ℂ)).const_mul (target - source)).add_const source
  have hu' : line (t : ℂ) ≠ 0 := by
    simpa [line, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add,
      smul_eq_mul, mul_comm] using hu
  have hfactor := hasDerivAt_chapterVIDRootCoordinateCollisionFactorPlus hζ hu'
  have hcomp := hfactor.comp (t : ℂ) hline
  have him := (hcomp.mul_const (-Complex.I)).real_of_complex
  change HasDerivAt
    (fun x : ℝ ↦ (chapterVIDRootCoordinateCollisionFactorPlus ζ
      (AffineMap.lineMap source target x)).im) _ t
  simpa [line, Function.comp_apply,
    AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, smul_eq_mul,
    Complex.mul_re, Complex.mul_im, mul_comm] using him

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
