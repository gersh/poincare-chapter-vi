/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.ChapterVIDMorseSlopeCompiled
import PoincareChapterVI.ChapterVILeanCompCertRelativeExponentialTrace
import PoincareChapterVI.ChapterVIDConnectorFactorCrossing
import PoincareChapterVI.ChapterVIDConnectorFactorNormalizedDerivativeCompiled

/-!
# Homogeneous expansion of the D-connector derivative

This module performs the cancellation needed before fixed-point evaluation.  The literal first
factor derivative is written as a base second derivative times `u-D`, plus a quadratic coordinate
remainder and a term proportional to the relative parameter displacement.  In particular, no
interval operation subtracts two values which agree at Poincare's collision point.
-/

noncomputable section

namespace PoincareChapterVI

/-- The coefficient left after exposing `u-D` in the relative exponential argument. -/
def chapterVIDRootExponentialArgumentDifferenceCoefficient (u : ℂ) : ℂ :=
  -(100 / 30003) *
    (u ^ 2 + u * chapterVIDCollisionLift + chapterVIDCollisionLift ^ 2) *
    (1 + u⁻¹ ^ 3 * chapterVIDCollisionLift⁻¹ ^ 3)

theorem chapterVIDRootExponentialArgumentDifference_eq_mul_coefficient (u : ℂ) :
    chapterVIDRootExponentialArgumentDifference u =
      (u - chapterVIDCollisionLift) *
        chapterVIDRootExponentialArgumentDifferenceCoefficient u := by
  unfold chapterVIDRootExponentialArgumentDifference
    chapterVIDRootExponentialArgumentDifferenceCoefficient
  ring

/-- Coefficient of the exposed coordinate difference in the Laurent contribution. -/
def chapterVIDRootFactorDerivativeLaurentCoefficient (u : ℂ) : ℂ :=
  (1 / 10001) * (u + chapterVIDCollisionLift) *
    (30000 + 3 * (u ^ 2 + chapterVIDCollisionLift ^ 2) /
      (u ^ 4 * chapterVIDCollisionLift ^ 4))

/-- Coefficient of `u-D` in the power-shape difference. -/
def chapterVIDRootFactorDerivativePowerShapeDifferenceCoefficient (u : ℂ) : ℂ :=
  (u ^ 2 + u * chapterVIDCollisionLift + chapterVIDCollisionLift ^ 2) *
    chapterVIDCollisionLift⁻¹ *
    (1 - u⁻¹ ^ 3 * chapterVIDCollisionLift⁻¹ ^ 3)

/-- Coordinate coefficient before the exponential's own linear term is collected. -/
def chapterVIDRootFactorDerivativeCoordinateCoefficient (u : ℂ) : ℂ :=
  chapterVIDRootFactorDerivativeLaurentCoefficient u +
    (200 / 10001) * chapterVIDY *
      chapterVIDRootFactorDerivativePowerShapeDifferenceCoefficient u

/-- Coefficient multiplying the relative anomaly multiplier. -/
def chapterVIDRootFactorDerivativeMultiplierCoefficient (u : ℂ) : ℂ :=
  -2 * (chapterVIDY / chapterVIDCollisionLift) +
    (200 / 10001) * chapterVIDY * chapterVIDRootFactorDerivativePowerShape u

/-- Complete coefficient of the first-order coordinate displacement. -/
def chapterVIDRootFactorDerivativeLinearCoefficient (u : ℂ) : ℂ :=
  chapterVIDRootFactorDerivativeCoordinateCoefficient u +
    chapterVIDRootExponentialArgumentDifferenceCoefficient u *
      chapterVIDRootFactorDerivativeMultiplierCoefficient u

/-- Difference quotient of the Laurent coefficient, with inverse-power differences already
cancelled algebraically. -/
def chapterVIDRootFactorDerivativeLaurentCoefficientDifference (u : ℂ) : ℂ :=
  let D : ℂ := chapterVIDCollisionLift
  let inverseTwoDifference : ℂ := -(u + D) / (u ^ 2 * D ^ 2)
  let inverseFourDifference : ℂ :=
    -(u ^ 3 + u ^ 2 * D + u * D ^ 2 + D ^ 3) / (u ^ 4 * D ^ 4)
  let powerTerm : ℂ := D⁻¹ ^ 4 * (u⁻¹ ^ 2 + D ^ 2 * u⁻¹ ^ 4)
  let powerTermDifference : ℂ := D⁻¹ ^ 4 *
    (inverseTwoDifference + D ^ 2 * inverseFourDifference)
  (1 / 10001) *
    ((30000 + 3 * powerTerm) + 2 * D * (3 * powerTermDifference))

/-- Difference quotient of the power-shape-difference coefficient. -/
def chapterVIDRootFactorDerivativePowerShapeCoefficientDifference (u : ℂ) : ℂ :=
  let D : ℂ := chapterVIDCollisionLift
  let quadratic : ℂ := u ^ 2 + u * D + D ^ 2
  let quadraticDifference : ℂ := u + 2 * D
  let inverseCubeDifference : ℂ := -quadratic / (u ^ 3 * D ^ 3)
  let inverseFactor : ℂ := 1 - u⁻¹ ^ 3 * D⁻¹ ^ 3
  let inverseFactorDifference : ℂ := -(D⁻¹ ^ 3) * inverseCubeDifference
  D⁻¹ * (quadraticDifference * inverseFactor + 3 * D ^ 2 * inverseFactorDifference)

/-- Difference quotient of the coordinate coefficient. -/
def chapterVIDRootFactorDerivativeCoordinateCoefficientDifference (u : ℂ) : ℂ :=
  chapterVIDRootFactorDerivativeLaurentCoefficientDifference u +
    (200 / 10001) * chapterVIDY *
      chapterVIDRootFactorDerivativePowerShapeCoefficientDifference u

/-- Difference quotient of the exponential-argument coefficient. -/
def chapterVIDRootExponentialArgumentCoefficientDifference (u : ℂ) : ℂ :=
  let D : ℂ := chapterVIDCollisionLift
  let quadratic : ℂ := u ^ 2 + u * D + D ^ 2
  let quadraticDifference : ℂ := u + 2 * D
  let inverseCubeDifference : ℂ := -quadratic / (u ^ 3 * D ^ 3)
  let inverseFactor : ℂ := 1 + u⁻¹ ^ 3 * D⁻¹ ^ 3
  let inverseFactorDifference : ℂ := D⁻¹ ^ 3 * inverseCubeDifference
  (-(100 / 30003 : ℂ)) *
    (quadraticDifference * inverseFactor + 3 * D ^ 2 * inverseFactorDifference)

/-- Difference quotient of the multiplier coefficient. -/
def chapterVIDRootFactorDerivativeMultiplierCoefficientDifference (u : ℂ) : ℂ :=
  let D : ℂ := chapterVIDCollisionLift
  let quadratic : ℂ := u ^ 2 + u * D + D ^ 2
  let inverseCubeDifference : ℂ := -quadratic / (u ^ 3 * D ^ 3)
  (200 / 10001) * chapterVIDY * D⁻¹ *
    (inverseCubeDifference + quadratic)

/-- Explicit removable difference quotient of the full linear coefficient. -/
def chapterVIDRootFactorDerivativeLinearCoefficientDifference (u : ℂ) : ℂ :=
  chapterVIDRootFactorDerivativeCoordinateCoefficientDifference u +
    chapterVIDRootExponentialArgumentCoefficientDifference u *
      chapterVIDRootFactorDerivativeMultiplierCoefficient u +
    chapterVIDRootExponentialArgumentDifferenceCoefficient chapterVIDCollisionLift *
      chapterVIDRootFactorDerivativeMultiplierCoefficientDifference u

theorem chapterVIDRootFactorDerivativeLinearCoefficient_sub_base
    {u : ℂ} (hu : u ≠ 0) :
    chapterVIDRootFactorDerivativeLinearCoefficient u -
        chapterVIDRootFactorDerivativeLinearCoefficient chapterVIDCollisionLift =
      (u - chapterVIDCollisionLift) *
        chapterVIDRootFactorDerivativeLinearCoefficientDifference u := by
  have hD := chapterVIDCollisionLift_ne_zero
  unfold chapterVIDRootFactorDerivativeLinearCoefficient
    chapterVIDRootFactorDerivativeCoordinateCoefficient
    chapterVIDRootFactorDerivativeLaurentCoefficient
    chapterVIDRootFactorDerivativePowerShapeDifferenceCoefficient
    chapterVIDRootFactorDerivativeMultiplierCoefficient
    chapterVIDRootFactorDerivativePowerShape
    chapterVIDRootExponentialArgumentDifferenceCoefficient
    chapterVIDRootFactorDerivativeLinearCoefficientDifference
    chapterVIDRootFactorDerivativeCoordinateCoefficientDifference
    chapterVIDRootFactorDerivativeLaurentCoefficientDifference
    chapterVIDRootFactorDerivativePowerShapeCoefficientDifference
    chapterVIDRootExponentialArgumentCoefficientDifference
    chapterVIDRootFactorDerivativeMultiplierCoefficientDifference
  dsimp only
  simp only [chapterVIDRootExponentialArgumentDifferenceCoefficient,
    chapterVIDRootFactorDerivativeMultiplierCoefficient,
    chapterVIDRootFactorDerivativePowerShape]
  field_simp [hu, hD]
  ring

/-- Exact second-order exponential remainder factor, with its removable value fixed to zero. -/
def chapterVIDExponentialSecondRemainderFactor (a : ℂ) : ℂ :=
  if a = 0 then 0 else (Complex.exp a - 1 - a) / a ^ 2

theorem chapterVID_exp_sub_one_eq_linear_add_square_mul_remainder (a : ℂ) :
    Complex.exp a - 1 =
      a + a ^ 2 * chapterVIDExponentialSecondRemainderFactor a := by
  by_cases ha : a = 0
  · simp [ha, chapterVIDExponentialSecondRemainderFactor]
  · rw [chapterVIDExponentialSecondRemainderFactor, if_neg ha]
    field_simp [ha]
    ring

theorem chapterVID_exp_eq_one_add_linear_add_square_mul_remainder (a : ℂ) :
    Complex.exp a =
      1 + a + a ^ 2 * chapterVIDExponentialSecondRemainderFactor a := by
  have h := chapterVID_exp_sub_one_eq_linear_add_square_mul_remainder a
  linear_combination h

theorem norm_chapterVIDExponentialSecondRemainderFactor_le_one
    {a : ℂ} (ha : ‖a‖ ≤ 1) :
    ‖chapterVIDExponentialSecondRemainderFactor a‖ ≤ 1 := by
  by_cases hazero : a = 0
  · simp [hazero, chapterVIDExponentialSecondRemainderFactor]
  · rw [chapterVIDExponentialSecondRemainderFactor, if_neg hazero, norm_div, norm_pow]
    rw [div_le_one (pow_pos (norm_pos_iff.mpr hazero) 2)]
    exact Complex.norm_exp_sub_one_sub_id_le ha

/-- Coefficient of the parameter displacement in the homogeneous derivative expansion. -/
def chapterVIDRootFactorDerivativeParameterCoefficient (u : ℂ) : ℂ :=
  let argument := chapterVIDRootExponentialArgumentDifference u
  (1 + argument + argument ^ 2 * chapterVIDExponentialSecondRemainderFactor argument) *
    chapterVIDRootFactorDerivativeMultiplierCoefficient u

/-- Quadratic coordinate coefficient in the homogeneous derivative expansion. -/
def chapterVIDRootFactorDerivativeQuadraticCoefficient (u : ℂ) : ℂ :=
  let H := chapterVIDRootExponentialArgumentDifferenceCoefficient u
  let argument := chapterVIDRootExponentialArgumentDifference u
  chapterVIDRootFactorDerivativeLinearCoefficientDifference u +
    H ^ 2 * chapterVIDExponentialSecondRemainderFactor argument *
      chapterVIDRootFactorDerivativeMultiplierCoefficient u

/-- Exact homogeneous identity used by the endpoint compiler.  The three displayed terms have
coordinate orders one, two, and parameter order one, respectively. -/
theorem chapterVIDRootCoordinateCollisionFactorPlusDerivative_eq_homogeneous
    (ζ : ℂ) {u : ℂ} (hu : u ≠ 0) :
    chapterVIDRootCoordinateCollisionFactorPlusDerivative ζ u =
      chapterVIDRootFactorDerivativeLinearCoefficient chapterVIDCollisionLift *
          (u - chapterVIDCollisionLift) +
        (u - chapterVIDCollisionLift) ^ 2 *
          chapterVIDRootFactorDerivativeQuadraticCoefficient u +
        (ζ / chapterVIDZRootBase - 1) *
          chapterVIDRootFactorDerivativeParameterCoefficient u := by
  rw [chapterVIDRootCoordinateCollisionFactorPlusDerivative_eq_dependencyPreserving ζ hu]
  unfold chapterVIDRootFactorDerivativeDependencyPreserving
    chapterVIDRootRelativeMultiplierDelta
  rw [chapterVIDRootExponentialArgument_sub_base hu]
  rw [chapterVIDRootExponentialArgumentDifference_eq_mul_coefficient]
  rw [chapterVID_exp_eq_one_add_linear_add_square_mul_remainder]
  simp only [chapterVIDRootFactorDerivativeLaurentDifference,
    chapterVIDRootFactorDerivativePowerShapeDifference,
    chapterVIDRootFactorDerivativeCoordinateCoefficient,
    chapterVIDRootFactorDerivativeLaurentCoefficient,
    chapterVIDRootFactorDerivativePowerShapeDifferenceCoefficient,
    chapterVIDRootFactorDerivativeMultiplierCoefficient,
    chapterVIDRootFactorDerivativeLinearCoefficient,
    chapterVIDRootFactorDerivativeQuadraticCoefficient,
    chapterVIDRootFactorDerivativeParameterCoefficient,
    chapterVIDRootFactorDerivativeLinearCoefficientDifference,
    chapterVIDRootFactorDerivativeCoordinateCoefficientDifference,
    chapterVIDRootFactorDerivativeLaurentCoefficientDifference,
    chapterVIDRootFactorDerivativePowerShapeCoefficientDifference,
    chapterVIDRootExponentialArgumentCoefficientDifference,
    chapterVIDRootFactorDerivativeMultiplierCoefficientDifference,
    chapterVIDRootExponentialArgumentDifferenceCoefficient,
    chapterVIDRootExponentialArgumentDifference,
    chapterVIDRootFactorDerivativePowerShape]
  have hD := chapterVIDCollisionLift_ne_zero
  field_simp [hu, hD, chapterVIDZRootBase_ne_zero]
  ring

/-- The linear coefficient is the literal second derivative at the double collision zero. -/
theorem chapterVIDRootFactorDerivativeLinearCoefficient_base_eq_secondDerivative :
    chapterVIDRootFactorDerivativeLinearCoefficient chapterVIDCollisionLift =
      chapterVIDRootCoordinateCollisionFactorPlusSecondDerivative
        chapterVIDZRootBase chapterVIDCollisionLift := by
  unfold chapterVIDRootFactorDerivativeLinearCoefficient
    chapterVIDRootFactorDerivativeCoordinateCoefficient
    chapterVIDRootFactorDerivativeLaurentCoefficient
    chapterVIDRootFactorDerivativePowerShapeDifferenceCoefficient
    chapterVIDRootExponentialArgumentDifferenceCoefficient
    chapterVIDRootFactorDerivativeMultiplierCoefficient
    chapterVIDRootFactorDerivativePowerShape
    chapterVIDRootCoordinateCollisionFactorPlusSecondDerivative
    chapterVIDRootSecondAnomalyLogDerivative
  rw [chapterVIDRootSecondAnomaly_base]
  field_simp [chapterVIDCollisionLift_ne_zero]
  ring

theorem chapterVIDRootFactorDerivativeLinearCoefficient_base_re_neg :
    (chapterVIDRootFactorDerivativeLinearCoefficient chapterVIDCollisionLift).re < 0 := by
  rw [chapterVIDRootFactorDerivativeLinearCoefficient_base_eq_secondDerivative]
  exact chapterVIDRootCoordinateCollisionFactorPlusSecondDerivative_base_re_neg

theorem chapterVIDRootFactorDerivativeLinearCoefficient_base_im_zero :
    (chapterVIDRootFactorDerivativeLinearCoefficient chapterVIDCollisionLift).im = 0 := by
  rw [chapterVIDRootFactorDerivativeLinearCoefficient_base_eq_secondDerivative]
  exact chapterVIDRootCoordinateCollisionFactorPlusSecondDerivative_base_im

/-- Connector direction at the collapsed parameter and local length zero. -/
def chapterVIDCollapsedConnectorDirection (side : ChapterVIDOuterArcSide) : ℂ :=
  match side with
  | .initial => (‖chapterVIDCollisionLift‖ : ℂ) * (1 + Complex.I)
  | .final => (‖chapterVIDCollisionLift‖ : ℂ) * (1 - Complex.I)

theorem ChapterVIDPrincipalGlobalRootModel.outerConnectorEndpoint_zero_sub_collision
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalGlobalRootModel massProduct b d)
    (side : ChapterVIDOuterArcSide) :
    model.outerConnectorEndpoint side 0 - chapterVIDCollisionLift =
      chapterVIDCollapsedConnectorDirection side := by
  rw [chapterVIDCollisionLift_eq_neg_norm]
  cases side <;>
    simp [ChapterVIDPrincipalGlobalRootModel.outerConnectorEndpoint,
      chapterVIDOuterArcPoint, chapterVIDCriticalToGlobalParameter_zero,
      chapterVIDCollapsedConnectorDirection] <;> ring

/-- The potentially dangerous distance-linear contribution is exactly imaginary, not merely
small. -/
theorem chapterVIDCollapsedConnectorDirection_sq_re_zero
    (side : ChapterVIDOuterArcSide) :
    (chapterVIDCollapsedConnectorDirection side ^ 2).re = 0 := by
  cases side <;>
    simp [chapterVIDCollapsedConnectorDirection, Complex.mul_re, Complex.add_re,
      Complex.add_im, Complex.sub_re, Complex.sub_im, pow_two]

theorem chapterVID_linear_base_mul_collapsedDirection_sq_re_zero
    (side : ChapterVIDOuterArcSide) :
    (chapterVIDRootFactorDerivativeLinearCoefficient chapterVIDCollisionLift *
      chapterVIDCollapsedConnectorDirection side ^ 2).re = 0 := by
  rw [Complex.mul_re, chapterVIDRootFactorDerivativeLinearCoefficient_base_im_zero,
    chapterVIDCollapsedConnectorDirection_sq_re_zero]
  ring

/-! ## `L + distance²` decomposition -/

/-- Sign of the real Morse endpoint coordinate. -/
def chapterVIDMorseSideSign : ChapterVIDOuterArcSide → ℝ
  | .initial => -1
  | .final => 1

theorem signedMorseLength_eq_sign_mul
    (side : ChapterVIDOuterArcSide) (L : ℝ) :
    ChapterVIDMorseSlopeCompiled.signedMorseLength side L =
      chapterVIDMorseSideSign side * L := by
  cases side <;> simp [ChapterVIDMorseSlopeCompiled.signedMorseLength,
    chapterVIDMorseSideSign]

/-- Connector vector reconstructed entirely from scale-free moving inputs. -/
def chapterVIDHomogeneousConnectorDirection
    (side : ChapterVIDOuterArcSide) (L : ℝ) (q r : ℂ) : ℂ :=
  chapterVIDCollapsedConnectorDirection side + (L ^ 2 : ℝ) * r -
    (chapterVIDMorseSideSign side * L : ℝ) * q

/-- Coefficient of `L` in the oriented real derivative. -/
def chapterVIDHomogeneousEndpointCoefficient
    (side : ChapterVIDOuterArcSide) (L distance : ℝ)
    (q r parameterDelta quadraticCoefficient parameterCoefficient : ℂ) : ℂ :=
  let sign := chapterVIDMorseSideSign side
  let base := chapterVIDCollapsedConnectorDirection side
  let direction := chapterVIDHomogeneousConnectorDirection side L q r
  let linear := chapterVIDRootFactorDerivativeLinearCoefficient chapterVIDCollisionLift
  linear * (sign : ℂ) * q * direction +
    (distance : ℂ) * linear * ((L : ℂ) * r - (sign : ℂ) * q) *
      (direction + base) +
    ((L : ℂ) * q ^ 2 + 2 * (sign : ℂ) * (distance : ℂ) * q * direction) *
      quadraticCoefficient * direction +
    (L : ℂ) * parameterDelta * parameterCoefficient * direction

/-- Coefficient of `distance²` in the oriented real derivative. -/
def chapterVIDHomogeneousDistanceCoefficient
    (side : ChapterVIDOuterArcSide) (L : ℝ) (q r quadraticCoefficient : ℂ) : ℂ :=
  chapterVIDHomogeneousConnectorDirection side L q r ^ 3 * quadraticCoefficient

/-- Pure algebraic heart of the homogeneous certificate.  The only discarded complex term is
`distance * linear * base²`, whose real part was proved exactly zero above. -/
theorem chapterVID_homogeneous_oriented_real_decomposition
    (side : ChapterVIDOuterArcSide) (L distance : ℝ)
    (q r parameterDelta quadraticCoefficient parameterCoefficient : ℂ) :
    let sign := chapterVIDMorseSideSign side
    let direction := chapterVIDHomogeneousConnectorDirection side L q r
    let coordinateDelta := (sign * L : ℝ) * q + (distance : ℂ) * direction
    let derivative :=
      chapterVIDRootFactorDerivativeLinearCoefficient chapterVIDCollisionLift * coordinateDelta +
        coordinateDelta ^ 2 * quadraticCoefficient +
        ((L ^ 2 : ℝ) : ℂ) * parameterDelta * parameterCoefficient
    (derivative * direction).re =
      L * (chapterVIDHomogeneousEndpointCoefficient side L distance q r parameterDelta
        quadraticCoefficient parameterCoefficient).re +
      distance ^ 2 *
        (chapterVIDHomogeneousDistanceCoefficient side L q r quadraticCoefficient).re := by
  dsimp only
  push_cast
  let sign : ℂ := (chapterVIDMorseSideSign side : ℂ)
  let base := chapterVIDCollapsedConnectorDirection side
  let direction := chapterVIDHomogeneousConnectorDirection side L q r
  let linear := chapterVIDRootFactorDerivativeLinearCoefficient chapterVIDCollisionLift
  have hsign : sign ^ 2 = 1 := by
    cases side <;> norm_num [sign, chapterVIDMorseSideSign]
  have hdirection : direction =
      base + (L : ℂ) * ((L : ℂ) * r - sign * q) := by
    dsimp only [direction, base, sign, chapterVIDHomogeneousConnectorDirection]
    push_cast
    ring
  have hcomplex :
      (L : ℂ) * chapterVIDHomogeneousEndpointCoefficient side L distance q r parameterDelta
          quadraticCoefficient parameterCoefficient +
        (distance : ℂ) ^ 2 *
          chapterVIDHomogeneousDistanceCoefficient side L q r quadraticCoefficient =
      (linear * ((sign * (L : ℂ)) * q + (distance : ℂ) * direction) +
          ((sign * (L : ℂ)) * q + (distance : ℂ) * direction) ^ 2 *
            quadraticCoefficient +
          ((L ^ 2 : ℝ) : ℂ) * parameterDelta * parameterCoefficient) * direction -
        (distance : ℂ) * linear * base ^ 2 := by
    simp only [chapterVIDHomogeneousEndpointCoefficient,
      chapterVIDHomogeneousDistanceCoefficient]
    change
      (L : ℂ) *
          (linear * sign * q * direction +
            (distance : ℂ) * linear * ((L : ℂ) * r - sign * q) *
              (direction + base) +
            ((L : ℂ) * q ^ 2 + 2 * sign * (distance : ℂ) * q * direction) *
              quadraticCoefficient * direction +
            (L : ℂ) * parameterDelta * parameterCoefficient * direction) +
        (distance : ℂ) ^ 2 * (direction ^ 3 * quadraticCoefficient) = _
    rw [hdirection]
    push_cast
    cases side <;> norm_num [sign, chapterVIDMorseSideSign] at * <;> ring
  push_cast at hcomplex
  have hbaseZero : (linear * base ^ 2).re = 0 := by
    change (chapterVIDRootFactorDerivativeLinearCoefficient chapterVIDCollisionLift *
      chapterVIDCollapsedConnectorDirection side ^ 2).re = 0
    exact chapterVID_linear_base_mul_collapsedDirection_sq_re_zero side
  have hcorrectionZero : ((distance : ℂ) * linear * base ^ 2).re = 0 := by
    rw [mul_assoc, Complex.mul_re, hbaseZero]
    simp
  have hleft :
      ((L : ℂ) * chapterVIDHomogeneousEndpointCoefficient side L distance q r parameterDelta
          quadraticCoefficient parameterCoefficient +
        (distance : ℂ) ^ 2 *
          chapterVIDHomogeneousDistanceCoefficient side L q r quadraticCoefficient).re =
      L * (chapterVIDHomogeneousEndpointCoefficient side L distance q r parameterDelta
        quadraticCoefficient parameterCoefficient).re +
      distance ^ 2 *
        (chapterVIDHomogeneousDistanceCoefficient side L q r quadraticCoefficient).re := by
    norm_num [Complex.add_re, Complex.mul_re, Complex.mul_im, pow_two]
  calc
    ((linear * ((sign * (L : ℂ)) * q + (distance : ℂ) * direction) +
          ((sign * (L : ℂ)) * q + (distance : ℂ) * direction) ^ 2 *
            quadraticCoefficient +
          (L : ℂ) ^ 2 * parameterDelta * parameterCoefficient) * direction).re =
      (((linear * ((sign * (L : ℂ)) * q + (distance : ℂ) * direction) +
          ((sign * (L : ℂ)) * q + (distance : ℂ) * direction) ^ 2 *
            quadraticCoefficient +
          (L : ℂ) ^ 2 * parameterDelta * parameterCoefficient) * direction) -
        (distance : ℂ) * linear * base ^ 2).re := by
          rw [Complex.sub_re, hcorrectionZero, sub_zero]
    _ = ((L : ℂ) * chapterVIDHomogeneousEndpointCoefficient side L distance q r parameterDelta
          quadraticCoefficient parameterCoefficient +
        (distance : ℂ) ^ 2 *
          chapterVIDHomogeneousDistanceCoefficient side L q r quadraticCoefficient).re :=
      congrArg Complex.re hcomplex.symm
    _ = _ := hleft

/-! ## Handoff to the literal connector -/

def ChapterVIDAnchoredConnectorModel.normalizedParameterDelta
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDAnchoredConnectorModel massProduct b d) : ℂ :=
  (model.connectorParameterRoot 0 / chapterVIDZRootBase - 1) /
    ((model.rootModel.L ^ 2 : ℝ) : ℂ)

def ChapterVIDAnchoredConnectorModel.normalizedOuterEndpointDelta
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDAnchoredConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) : ℂ :=
  (model.rootModel.outerConnectorEndpoint side model.κ -
      model.rootModel.outerConnectorEndpoint side 0) /
    ((model.rootModel.L ^ 2 : ℝ) : ℂ)

theorem ChapterVIDAnchoredConnectorModel.parameterDelta_eq_length_sq_mul_normalized
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDAnchoredConnectorModel massProduct b d) :
    model.connectorParameterRoot 0 / chapterVIDZRootBase - 1 =
      ((model.rootModel.L ^ 2 : ℝ) : ℂ) * model.normalizedParameterDelta := by
  have hLsq : ((model.rootModel.L ^ 2 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (pow_ne_zero 2 model.rootModel.L_pos.ne')
  unfold ChapterVIDAnchoredConnectorModel.normalizedParameterDelta
  exact (mul_div_cancel₀ _ hLsq).symm

theorem ChapterVIDAnchoredConnectorModel.localToOuter_eq_homogeneousDirection
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDAnchoredConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) :
    model.rootModel.outerConnectorEndpoint side model.κ -
        model.rootModel.localConnectorEndpoint side (model.criticalValue 0) =
      chapterVIDHomogeneousConnectorDirection side model.rootModel.L
        (chapterVIDNormalizedLocalEndpointDelta side model.κ model.rootModel.L)
        (model.normalizedOuterEndpointDelta side) := by
  rw [ChapterVIDMorseSlopeCompiled.localToOuter_eq_collapsed_add_scaled_deltas model side]
  rw [model.rootModel.outerConnectorEndpoint_zero_sub_collision side]
  rw [signedMorseLength_eq_sign_mul]
  unfold chapterVIDHomogeneousConnectorDirection
    ChapterVIDAnchoredConnectorModel.normalizedOuterEndpointDelta
  push_cast
  ring

/-- Literal affine connector coordinate used by the first-factor derivative. -/
def ChapterVIDAnchoredConnectorModel.homogeneousConnectorCoordinate
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDAnchoredConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) (t : ℝ) : ℂ :=
  AffineMap.lineMap
    (model.rootModel.connectorSource side (model.criticalValue 0))
    (model.rootModel.connectorTarget side (model.criticalValue 0)) (t : ℂ)

theorem ChapterVIDAnchoredConnectorModel.homogeneousConnectorCoordinate_sub_collision
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDAnchoredConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) (t : ℝ) :
    model.homogeneousConnectorCoordinate side t - chapterVIDCollisionLift =
      ((chapterVIDMorseSideSign side * model.rootModel.L : ℝ) : ℂ) *
          chapterVIDNormalizedLocalEndpointDelta side model.κ model.rootModel.L +
        (ChapterVIDConnectorFactorCrossing.localEndpointDistance side t : ℂ) *
          chapterVIDHomogeneousConnectorDirection side model.rootModel.L
            (chapterVIDNormalizedLocalEndpointDelta side model.κ model.rootModel.L)
            (model.normalizedOuterEndpointDelta side) := by
  let localPoint := model.rootModel.localConnectorEndpoint side (model.criticalValue 0)
  let outer := model.rootModel.outerConnectorEndpoint side (model.criticalValue 0)
  have hline :=
    ChapterVIDConnectorFactorNormalizedDerivativeCompiled.lineMap_sub_collision_eq_localDelta_add_distance_mul
      side localPoint outer chapterVIDCollisionLift t
  rw [ChapterVIDConnectorFactorNormalizedDerivativeCompiled.connectorSourceFromLocalOuter_eq
      model side,
    ChapterVIDConnectorFactorNormalizedDerivativeCompiled.connectorTargetFromLocalOuter_eq
      model side] at hline
  change model.homogeneousConnectorCoordinate side t - chapterVIDCollisionLift = _ at hline
  rw [hline]
  dsimp only [localPoint, outer]
  rw [ChapterVIDMorseSlopeCompiled.localEndpointDelta_eq_signedMorseLength_mul_normalized
    model side]
  have hout :
      model.rootModel.outerConnectorEndpoint side (model.criticalValue 0) =
        model.rootModel.outerConnectorEndpoint side model.κ := by
    rw [ChapterVIDPrincipalConnectorModel.criticalValue_zero]
  rw [hout]
  rw [model.localToOuter_eq_homogeneousDirection side]
  rw [signedMorseLength_eq_sign_mul]

theorem ChapterVIDAnchoredConnectorModel.homogeneousConnectorCoordinate_ne_zero
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDAnchoredConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    model.homogeneousConnectorCoordinate side t ≠ 0 := by
  let tUnit : Set.Icc (0 : ℝ) 1 := ⟨t, ht⟩
  simpa [ChapterVIDAnchoredConnectorModel.homogeneousConnectorCoordinate,
    ChapterVIDPrincipalConnectorModel.rectanglePoint,
    ChapterVIDPrincipalGlobalRootModel.connectorPoint, tUnit,
    AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, smul_eq_mul,
    mul_comm] using
    model.toChapterVIDPrincipalConnectorModel.rectanglePoint_ne_zero side (0, tUnit)

/-- After orienting the initial connector toward its local endpoint, both sides use the same
local-to-outer direction in the homogeneous formula. -/
theorem ChapterVIDAnchoredConnectorModel.orientedLineDerivative_eq_homogeneousDirection
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDAnchoredConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) (t : ℝ) :
    ChapterVIDConnectorFactorCrossing.orientedLineDerivative
        model.toChapterVIDPrincipalConnectorModel side t =
      (chapterVIDRootCoordinateCollisionFactorPlusDerivative
          (model.connectorParameterRoot 0)
          (model.homogeneousConnectorCoordinate side t) *
        chapterVIDHomogeneousConnectorDirection side model.rootModel.L
          (chapterVIDNormalizedLocalEndpointDelta side model.κ model.rootModel.L)
          (model.normalizedOuterEndpointDelta side)).re := by
  rw [← model.localToOuter_eq_homogeneousDirection side]
  cases side with
  | initial =>
    simp only [ChapterVIDConnectorFactorCrossing.orientedLineDerivative,
      ChapterVIDConnectorFactorCrossing.lineDerivativeReal,
      ChapterVIDAnchoredConnectorModel.homogeneousConnectorCoordinate,
      ChapterVIDPrincipalGlobalRootModel.connectorSource,
      ChapterVIDPrincipalGlobalRootModel.connectorTarget]
    rw [ChapterVIDPrincipalConnectorModel.criticalValue_zero]
    rw [← Complex.neg_re]
    congr 1
    ring
  | final =>
    simp only [ChapterVIDConnectorFactorCrossing.orientedLineDerivative,
      ChapterVIDConnectorFactorCrossing.lineDerivativeReal,
      ChapterVIDAnchoredConnectorModel.homogeneousConnectorCoordinate,
      ChapterVIDPrincipalGlobalRootModel.connectorSource,
      ChapterVIDPrincipalGlobalRootModel.connectorTarget]
    rw [ChapterVIDPrincipalConnectorModel.criticalValue_zero]

/-- Concrete scale-free endpoint coefficient along the anchored connector. -/
def ChapterVIDAnchoredConnectorModel.homogeneousEndpointCoefficient
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDAnchoredConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) (t : ℝ) : ℂ :=
  chapterVIDHomogeneousEndpointCoefficient side model.rootModel.L
    (ChapterVIDConnectorFactorCrossing.localEndpointDistance side t)
    (chapterVIDNormalizedLocalEndpointDelta side model.κ model.rootModel.L)
    (model.normalizedOuterEndpointDelta side)
    model.normalizedParameterDelta
    (chapterVIDRootFactorDerivativeQuadraticCoefficient
      (model.homogeneousConnectorCoordinate side t))
    (chapterVIDRootFactorDerivativeParameterCoefficient
      (model.homogeneousConnectorCoordinate side t))

/-- Concrete scale-free distance coefficient along the anchored connector. -/
def ChapterVIDAnchoredConnectorModel.homogeneousDistanceCoefficient
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDAnchoredConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) (t : ℝ) : ℂ :=
  chapterVIDHomogeneousDistanceCoefficient side model.rootModel.L
    (chapterVIDNormalizedLocalEndpointDelta side model.κ model.rootModel.L)
    (model.normalizedOuterEndpointDelta side)
    (chapterVIDRootFactorDerivativeQuadraticCoefficient
      (model.homogeneousConnectorCoordinate side t))

/-- Exact compiler handoff.  The literal oriented path derivative is a nonnegative linear
combination of two scale-free real coefficients.  The remaining finite campaign may therefore
certify those coefficients directly, without dividing an interval by a vanishing scale. -/
theorem ChapterVIDAnchoredConnectorModel.orientedLineDerivative_eq_homogeneousCoefficients
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDAnchoredConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ChapterVIDConnectorFactorCrossing.orientedLineDerivative
        model.toChapterVIDPrincipalConnectorModel side t =
      model.rootModel.L * (model.homogeneousEndpointCoefficient side t).re +
        ChapterVIDConnectorFactorCrossing.localEndpointDistance side t ^ 2 *
          (model.homogeneousDistanceCoefficient side t).re := by
  rw [model.orientedLineDerivative_eq_homogeneousDirection side t]
  have hu := model.homogeneousConnectorCoordinate_ne_zero side ht
  rw [chapterVIDRootCoordinateCollisionFactorPlusDerivative_eq_homogeneous _ hu]
  rw [model.homogeneousConnectorCoordinate_sub_collision side t]
  rw [model.parameterDelta_eq_length_sq_mul_normalized]
  exact chapterVID_homogeneous_oriented_real_decomposition side model.rootModel.L
    (ChapterVIDConnectorFactorCrossing.localEndpointDistance side t)
    (chapterVIDNormalizedLocalEndpointDelta side model.κ model.rootModel.L)
    (model.normalizedOuterEndpointDelta side)
    model.normalizedParameterDelta
    (chapterVIDRootFactorDerivativeQuadraticCoefficient
      (model.homogeneousConnectorCoordinate side t))
    (chapterVIDRootFactorDerivativeParameterCoefficient
      (model.homogeneousConnectorCoordinate side t))

/-! ## Semantic target for the finite homogeneous table -/

/-- The two scale-free coefficient signs certified by the finite collar table.  This is the
smallest numerical interface needed after the exact homogeneous cancellation: neither the
literal derivative nor its vanishing scale appears in the certificate. -/
structure ChapterVIDAnchoredConnectorModel.HomogeneousCoefficientCertificate
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDAnchoredConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) : Prop where
  endpoint_nonnegative : ∀ t : Set.Icc (0 : ℝ) 1,
    (t : ℝ) ∈ ChapterVIDConnectorFactorMonotonicity.collarInterval side →
      0 ≤ (model.homogeneousEndpointCoefficient side (t : ℝ)).re
  distance_nonnegative : ∀ t : Set.Icc (0 : ℝ) 1,
    (t : ℝ) ∈ ChapterVIDConnectorFactorMonotonicity.collarInterval side →
      0 ≤ (model.homogeneousDistanceCoefficient side (t : ℝ)).re

/-- The homogeneous coefficient table proves the oriented derivative directly.  The weights
are `L > 0` and a square, so no division by the collapsing Morse scale is required. -/
theorem ChapterVIDAnchoredConnectorModel.HomogeneousCoefficientCertificate.toOrientedRealDerivativeCertificate
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDAnchoredConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide)
    (certificate : model.HomogeneousCoefficientCertificate side) :
    ChapterVIDConnectorFactorCrossing.OrientedRealDerivativeCertificate
      model.toChapterVIDPrincipalConnectorModel side := by
  refine ⟨?_⟩
  intro t ht
  have htUnit : (t : ℝ) ∈ Set.Icc (0 : ℝ) 1 := t.property
  have hdecomposition :=
    model.orientedLineDerivative_eq_homogeneousCoefficients side htUnit
  have hendpoint := certificate.endpoint_nonnegative t ht
  have hdistance := certificate.distance_nonnegative t ht
  have horiented :
      0 ≤ ChapterVIDConnectorFactorCrossing.orientedLineDerivative
        model.toChapterVIDPrincipalConnectorModel side (t : ℝ) := by
    rw [hdecomposition]
    exact add_nonneg
      (mul_nonneg model.rootModel.L_pos.le hendpoint)
      (mul_nonneg (sq_nonneg _) hdistance)
  cases side with
  | initial =>
      simpa [ChapterVIDConnectorFactorCrossing.orientedLineDerivative] using horiented
  | final =>
      simpa [ChapterVIDConnectorFactorCrossing.orientedLineDerivative] using horiented

/-- Compatibility with the pre-existing normalized compiled-campaign interface. -/
theorem ChapterVIDAnchoredConnectorModel.HomogeneousCoefficientCertificate.toNormalizedRealDerivativeCertificate
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDAnchoredConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide)
    (certificate : model.HomogeneousCoefficientCertificate side) :
    ChapterVIDConnectorFactorCrossing.NormalizedRealDerivativeCertificate model side := by
  refine ⟨?_⟩
  intro t ht
  have horiented := (certificate.toOrientedRealDerivativeCertificate model side).oriented t ht
  have hscale := ChapterVIDConnectorFactorCrossing.realDerivativeScale_pos
    model side (t : ℝ)
  unfold ChapterVIDConnectorFactorCrossing.normalizedOrientedLineDerivative
  apply div_nonneg
  · cases side with
    | initial =>
        simpa [ChapterVIDConnectorFactorCrossing.orientedLineDerivative] using horiented
    | final =>
        simpa [ChapterVIDConnectorFactorCrossing.orientedLineDerivative] using horiented
  · exact hscale.le

end PoincareChapterVI
