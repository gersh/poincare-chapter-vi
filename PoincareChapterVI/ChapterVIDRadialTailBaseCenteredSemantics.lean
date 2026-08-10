/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.ChapterVIDRadialTailTaylorSemantics
import PoincareChapterVI.ChapterVIDEndpointOrientation

/-! # Exact semantics of the collision-base-centred straight-line program -/

noncomputable section

namespace PoincareChapterVI
namespace ChapterVIDRadialTailBaseCenteredSemantics

set_option maxRecDepth 100000
set_option maxHeartbeats 0

open scoped unitInterval
open ChapterVIFieldExpression Expr
open ChapterVIDRadialTailBaseCenteredProgram
open ChapterVIDRadialTailTaylorSemantics

def exactInputs (t : I) (s : ℝ) (remainder : ℂ) : Fin 56 → ℂ
  | 0 => pValue s
  | 1 => (t : ℝ)
  | 2 => remainder
  | 3 => chapterVIDCriticalParameterModulus - 1
  | 4 => chapterVIDCertificateContourCorrection - 1
  | 5 => Complex.I
  | 6 => chapterVIDCollisionLift
  | 7 => chapterVIDCollisionLift⁻¹
  | 8 => chapterVIDCollisionLift ^ 2
  | 9 => chapterVIDCollisionLift⁻¹ ^ 3
  | 10 => chapterVIDCollisionLift⁻¹ ^ 4
  | 11 => chapterVIDY
  | 12 => chapterVIDZRootBase
  | _ => 0

def exactQuarter (t : I) : ℂ :=
  ((1 - (t : ℂ) ^ 2) + (2 * (t : ℂ)) * Complex.I) / (1 + (t : ℂ) ^ 2)

def exactUnit (side : ChapterVIDPinchingArcSide) (t : I) : ℂ :=
  match side with
  | .upper => Complex.I * exactQuarter t
  | .lower => -exactQuarter t

def exactCorrection (s : ℝ) : ℂ :=
  1 + (chapterVIDCertificateContourCorrection - 1 : ℂ) *
    ((pValue s : ℂ) ^ 6 - 1) / (chapterVIDCriticalParameterModulus - 1 : ℂ)

def exactU (side : ChapterVIDPinchingArcSide) (t : I) (s : ℝ) : ℂ :=
  (pValue s : ℂ) * exactCorrection s * exactUnit side t

def exactArgument (side : ChapterVIDPinchingArcSide) (t : I) (s : ℝ) : ℂ :=
  (100 / 30003 : ℂ) *
    (((exactU side t s)⁻¹ ^ 3 - exactU side t s ^ 3) -
      (chapterVIDCollisionLift⁻¹ ^ 3 -
        chapterVIDCollisionLift * chapterVIDCollisionLift ^ 2))

def exactRemainder (side : ChapterVIDPinchingArcSide) (t : I) (s : ℝ) : ℂ :=
  Complex.exp (exactArgument side t s) -
    ChapterVILeanCompCertHighOrderAnomalyTrace.expPolynomial (exactArgument side t s)

def exactExpRelative (side : ChapterVIDPinchingArcSide) (t : I) (s : ℝ) : ℂ :=
  Complex.exp (exactArgument side t s)

def exactZeta (s : ℝ) : ℂ := (pValue s : ℂ) ^ 2

def exactMultiplierDelta (side : ChapterVIDPinchingArcSide) (t : I) (s : ℝ) : ℂ :=
  (exactZeta s / chapterVIDZRootBase - 1) * exactExpRelative side t s +
    (exactExpRelative side t s - 1)

def exactAnomaly (side : ChapterVIDPinchingArcSide) (t : I) (s : ℝ) : ℂ :=
  chapterVIDY * (1 + exactMultiplierDelta side t s) *
    (exactU side t s * chapterVIDCollisionLift⁻¹)

def exactPDot (s : ℝ) : ℂ :=
  (chapterVIDCriticalParameterModulus - 1 : ℂ) / (6 * (pValue s : ℂ) ^ 5)

def exactRadiusDot (s : ℝ) : ℂ :=
  exactPDot s * exactCorrection s +
    (pValue s : ℂ) * (chapterVIDCertificateContourCorrection - 1 : ℂ)

def exactUDot (side : ChapterVIDPinchingArcSide) (t : I) (s : ℝ) : ℂ :=
  exactRadiusDot s * exactUnit side t

def exactZetaLogDot (s : ℝ) : ℂ :=
  (chapterVIDCriticalParameterModulus - 1 : ℂ) / (3 * (pValue s : ℂ) ^ 6)

def exactFactorMinus (side : ChapterVIDPinchingArcSide) (t : I) (s : ℝ) : ℂ :=
  (1 / 10001 : ℂ) *
      (exactU side t s ^ 3 + 10000 * (exactU side t s ^ 3)⁻¹ - 200) -
    2 * (exactAnomaly side t s)⁻¹

def exactFactorMinusDot (side : ChapterVIDPinchingArcSide) (t : I) (s : ℝ) : ℂ :=
  (1 / 10001 : ℂ) *
      (3 * exactU side t s ^ 2 * exactUDot side t s -
        30000 * (exactU side t s ^ 3)⁻¹ * (exactU side t s)⁻¹ *
          exactUDot side t s) +
    2 * (exactAnomaly side t s)⁻¹ *
      ((exactU side t s)⁻¹ - (100 / 10001 : ℂ) *
          ((exactU side t s)⁻¹ ^ 4 + exactU side t s ^ 2)) *
      exactUDot side t s +
    2 * (exactAnomaly side t s)⁻¹ * exactZetaLogDot s

def exactFactorPlusCoordinateDerivative
    (side : ChapterVIDPinchingArcSide) (t : I) (s : ℝ) : ℂ :=
  let u := exactU side t s
  let delta := u - chapterVIDCollisionLift
  let multiplierDelta := exactMultiplierDelta side t s
  let powerShape := chapterVIDCollisionLift⁻¹ * u⁻¹ ^ 3 +
    u ^ 3 * chapterVIDCollisionLift⁻¹
  let powerShapeDifference := delta *
    (u ^ 2 + u * chapterVIDCollisionLift + chapterVIDCollisionLift ^ 2) *
    chapterVIDCollisionLift⁻¹ *
    (1 - u⁻¹ ^ 3 * chapterVIDCollisionLift⁻¹ ^ 3)
  (1 / 10001 : ℂ) * delta * (u + chapterVIDCollisionLift) *
      (30000 + 3 * (u⁻¹ ^ 4 * chapterVIDCollisionLift⁻¹ ^ 4) *
        (u ^ 2 + chapterVIDCollisionLift ^ 2)) -
    2 * (chapterVIDY * chapterVIDCollisionLift⁻¹) * multiplierDelta +
    (200 / 10001 : ℂ) * chapterVIDY *
      (multiplierDelta * powerShape + powerShapeDifference)

def exactFactorPlus (side : ChapterVIDPinchingArcSide) (t : I) (s : ℝ) : ℂ :=
  let u := exactU side t s
  let delta := u - chapterVIDCollisionLift
  let laurentDifference := (1 / 10001 : ℂ) * delta *
    (u ^ 2 + u * chapterVIDCollisionLift + chapterVIDCollisionLift ^ 2) *
    (10000 - u⁻¹ ^ 3 * chapterVIDCollisionLift⁻¹ ^ 3)
  let anomalyDifference := chapterVIDY *
    (delta * chapterVIDCollisionLift⁻¹ +
      (u * chapterVIDCollisionLift⁻¹) * exactMultiplierDelta side t s)
  laurentDifference - 2 * anomalyDifference

def exactProgramDerivative
    (side : ChapterVIDPinchingArcSide) (t : I) (s : ℝ) : ℂ :=
  (exactFactorPlusCoordinateDerivative side t s * exactUDot side t s -
      2 * exactAnomaly side t s * exactZetaLogDot s) *
      exactFactorMinus side t s +
    exactFactorPlus side t s * exactFactorMinusDot side t s

theorem collisionLift_inv_pow_three :
    chapterVIDCollisionLift⁻¹ ^ 3 = chapterVIDX⁻¹ := by
  rw [inv_pow, chapterVIDCollisionLift_pow]

/-- Exact mathematical value assigned to every register.  Keeping this map named prevents
symbolic execution from duplicating the straight-line program exponentially. -/
def exactState (side : ChapterVIDPinchingArcSide) (t : I) (s : ℝ) : Fin 56 → ℂ
  | 0 => pValue s
  | 1 => (t : ℝ)
  | 2 => exactRemainder side t s
  | 3 => chapterVIDCriticalParameterModulus - 1
  | 4 => chapterVIDCertificateContourCorrection - 1
  | 5 => Complex.I
  | 6 => chapterVIDCollisionLift
  | 7 => chapterVIDCollisionLift⁻¹
  | 8 => chapterVIDCollisionLift ^ 2
  | 9 => chapterVIDCollisionLift⁻¹ ^ 3
  | 10 => chapterVIDCollisionLift⁻¹ ^ 4
  | 11 => chapterVIDY
  | 12 => chapterVIDZRootBase
  | 13 => exactCorrection s
  | 14 => exactUnit side t
  | 15 => exactU side t s
  | 16 => (exactU side t s)⁻¹
  | 17 => exactU side t s ^ 2
  | 18 => exactU side t s ^ 3
  | 19 => (exactU side t s ^ 3)⁻¹
  | 20 => exactU side t s - chapterVIDCollisionLift
  | 21 => exactArgument side t s
  | 22 => exactArgument side t s ^ 2
  | 23 => exactArgument side t s ^ 3
  | 24 => exactArgument side t s ^ 4
  | 25 => exactArgument side t s ^ 5
  | 26 => 1 + exactArgument side t s + exactArgument side t s ^ 2 / 2 +
      exactArgument side t s ^ 3 / 6 + exactArgument side t s ^ 4 / 24
  | 27 => exactExpRelative side t s
  | 28 => exactZeta s
  | 29 => exactZeta s / chapterVIDZRootBase - 1
  | 30 => exactMultiplierDelta side t s
  | 31 => exactU side t s * chapterVIDCollisionLift⁻¹
  | 32 => exactAnomaly side t s
  | 33 => (exactAnomaly side t s)⁻¹
  | 34 => exactPDot s
  | 35 => exactRadiusDot s
  | 36 => exactUDot side t s
  | 37 => exactZetaLogDot s
  | 38 => (1 / 10001 : ℂ) *
      (exactU side t s ^ 3 + 10000 * (exactU side t s ^ 3)⁻¹ - 200)
  | 39 => exactFactorMinus side t s
  | 40 => (1 / 10001 : ℂ) *
      (3 * exactU side t s ^ 2 * exactUDot side t s -
        30000 * (exactU side t s ^ 3)⁻¹ * (exactU side t s)⁻¹ *
          exactUDot side t s)
  | 41 => (exactU side t s)⁻¹ - (100 / 10001 : ℂ) *
      ((exactU side t s)⁻¹ ^ 4 + exactU side t s ^ 2)
  | 42 => ((exactU side t s)⁻¹ - (100 / 10001 : ℂ) *
      ((exactU side t s)⁻¹ ^ 4 + exactU side t s ^ 2)) *
      exactUDot side t s + exactZetaLogDot s
  | 43 => exactFactorMinusDot side t s
  | 44 => (1 / 10001 : ℂ) *
      (exactU side t s - chapterVIDCollisionLift) *
      (exactU side t s + chapterVIDCollisionLift) *
      (30000 + 3 * ((exactU side t s)⁻¹ ^ 4 * chapterVIDCollisionLift⁻¹ ^ 4) *
        (exactU side t s ^ 2 + chapterVIDCollisionLift ^ 2))
  | 45 => chapterVIDCollisionLift⁻¹ * (exactU side t s)⁻¹ ^ 3 +
      exactU side t s ^ 3 * chapterVIDCollisionLift⁻¹
  | 46 => (exactU side t s - chapterVIDCollisionLift) *
      (exactU side t s ^ 2 + exactU side t s * chapterVIDCollisionLift +
        chapterVIDCollisionLift ^ 2) * chapterVIDCollisionLift⁻¹ *
      (1 - (exactU side t s)⁻¹ ^ 3 * chapterVIDCollisionLift⁻¹ ^ 3)
  | 47 => exactFactorPlusCoordinateDerivative side t s
  | 48 => exactFactorPlusCoordinateDerivative side t s * exactUDot side t s -
      2 * exactAnomaly side t s * exactZetaLogDot s
  | 49 => (1 / 10001 : ℂ) * (exactU side t s - chapterVIDCollisionLift) *
      (exactU side t s ^ 2 + exactU side t s * chapterVIDCollisionLift +
        chapterVIDCollisionLift ^ 2) *
      (10000 - (exactU side t s)⁻¹ ^ 3 * chapterVIDCollisionLift⁻¹ ^ 3)
  | 50 => chapterVIDY * ((exactU side t s - chapterVIDCollisionLift) *
      chapterVIDCollisionLift⁻¹ +
      (exactU side t s * chapterVIDCollisionLift⁻¹) *
        exactMultiplierDelta side t s)
  | 51 => exactFactorPlus side t s
  | 52 => exactProgramDerivative side t s
  | _ => 0

theorem exactArgument_independent (side : ChapterVIDPinchingArcSide) (t : I) (s : ℝ)
    (remainder : ℂ) :
    evalProgram (program side) (exactInputs t s remainder) 21 = exactArgument side t s := by
  rw [show program side = (program side).take 9 ++ (program side).drop 9 by
    exact (List.take_append_drop 9 (program side)).symm,
    evalProgram_append]
  rw [evalProgram_preserves]
  · cases side <;>
      simp [program, assignment, evalProgram, Assignment.updateValues,
        Function.update, exactInputs, quarter, unitFormula, r, p,
        exactArgument, exactU, exactCorrection, exactUnit, exactQuarter,
        Expr.eval, Expr.npow,
        ChapterVIDRadialTailBaseCenteredProgram.t, expRemainder, qdot, cdot,
        imaginaryUnit, collision, collisionInv, collisionSq, collisionInvCube,
        collisionInvFourth, yBase, zetaBase, correction, unit, u, uInv, uSq, uCube,
        uCubeInv, coordinateDelta, argumentDelta] <;> ring
  · intro next hnext
    cases side <;> simp [program, assignment] at hnext <;> aesop

theorem exactState_assignment (side : ChapterVIDPinchingArcSide) (t : I) (s : ℝ) :
    ∀ next ∈ program side,
      next.expression.eval (exactState side t s) = exactState side t s next.target := by
  intro next hnext
  cases side <;> simp [program, assignment] at hnext
  all_goals
    rcases hnext with
      (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
       rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
       rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
       rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  all_goals
    simp [exactState, Expr.eval, exactExpRelative,
      ChapterVILeanCompCertHighOrderAnomalyTrace.expPolynomial,
      quarter, unitFormula, r, p,
      ChapterVIDRadialTailBaseCenteredProgram.t, expRemainder, qdot, cdot,
      imaginaryUnit, collision, collisionInv, collisionSq, collisionInvCube,
      collisionInvFourth, yBase, zetaBase, correction, unit, u, uInv, uSq, uCube,
      uCubeInv, coordinateDelta, argumentDelta, argumentSq, argumentCube,
      argumentFourth, argumentFifth, expDerivativePolynomial, expRelative, zeta,
      zetaDelta, multiplierDelta, uRatio, anomaly, anomalyInv, pDot, radiusDot,
      uDot, zetaLogDot, factorMinusLaurent, factorMinus, minusLaurentDot,
      anomalyLogDerivative, anomalyLogDot, factorMinusDot, laurentDifference,
      powerShape, powerShapeDifference, factorPlusCoordinateDerivative,
      factorPlusDot, laurentValueDifference, anomalyDifference, factorPlus,
      derivative, chapterVIDCollisionLift_pow, collisionLift_inv_pow_three,
      inv_pow, pow_two, pow_succ]
  all_goals first
    | rfl
    | (change _ = exactCorrection _; unfold exactCorrection; ring)
    | (change _ = exactUnit _ _; unfold exactUnit exactQuarter; ring)
    | (change _ = exactU _ _ _; unfold exactU; ring)
    | (change _ = exactArgument _ _ _
       unfold exactArgument
       rw [show chapterVIDCollisionLift * chapterVIDCollisionLift ^ 2 =
          chapterVIDCollisionLift ^ 3 by ring, chapterVIDCollisionLift_pow,
          collisionLift_inv_pow_three]
       ring)
    | (unfold exactRemainder ChapterVILeanCompCertHighOrderAnomalyTrace.expPolynomial; ring)
    | (change _ = exactZeta _; unfold exactZeta; ring)
    | (change _ = exactMultiplierDelta _ _ _; unfold exactMultiplierDelta; ring)
    | (change _ = exactPDot _; unfold exactPDot; ring)
    | (change _ = exactRadiusDot _; unfold exactRadiusDot; ring)
    | (change _ = exactUDot _ _ _; unfold exactUDot; ring)
    | (change _ = exactZetaLogDot _; unfold exactZetaLogDot; ring)
    | (change _ = exactFactorMinusDot _ _ _
       unfold exactFactorMinusDot
       simp only [inv_pow]
       ring)
    | (change _ = exactProgramDerivative _ _ _; unfold exactProgramDerivative; ring)
    | (simp only [← inv_pow, chapterVIDCollisionLift_pow]; ring)
    | (left; ring)
    | (try simp [exactAnomaly, exactFactorMinus, exactFactorMinusDot,
        exactFactorPlusCoordinateDerivative, exactFactorPlus,
        chapterVIDY_eq_ofReal, chapterVIDCollisionLift_pow,
        inv_pow, pow_two, pow_succ] <;> ring)
  all_goals rw [chapterVIDCollisionLift_pow, collisionLift_inv_pow_three] <;> ring

theorem program_wellFormed (side : ChapterVIDPinchingArcSide) :
    ProgramWellFormedFrom 13 (program side) = true := by
  cases side <;> decide +kernel

theorem evalProgram_exactState (side : ChapterVIDPinchingArcSide) (t : I) (s : ℝ)
    (i : Fin 56) (hi : i.val < 13 + (program side).length) :
    evalProgram (program side) (exactInputs t s (exactRemainder side t s)) i =
      exactState side t s i := by
  apply evalProgram_eq_exact_below (program_wellFormed side) _
      (exactState_assignment side t s) i hi
  intro j hj
  fin_cases j <;> simp [exactInputs, exactState] at hj ⊢

theorem evalProgram_exact (side : ChapterVIDPinchingArcSide) (t : I) (s : ℝ) :
    evalProgram (program side) (exactInputs t s (exactRemainder side t s)) 52 =
      exactProgramDerivative side t s := by
  refine evalProgram_eq_exact_below (program_wellFormed side) ?_
      (exactState_assignment side t s) 52 ?_
  · intro i hi
    fin_cases i <;> simp [exactInputs, exactState] at hi ⊢
  · norm_num [program]

theorem exactQuarter_eq (t : I) :
    exactQuarter t = chapterVIDRationalUnitQuarter t := by
  unfold exactQuarter chapterVIDRationalUnitQuarter
  have hden := (chapterVIDRationalUnitQuarter_denominator_pos t).ne'
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr hden]

theorem exactUnit_eq (side : ChapterVIDPinchingArcSide) (t : I) :
    exactUnit side t = chapterVIDRadialTailFixedUnit side t := by
  rw [chapterVIDRadialTailFixedUnit]
  cases side <;>
    simp [exactUnit, chapterVIDRationalPinchingArcUnit, exactQuarter_eq]

theorem exactCorrection_eq (s : I) :
    exactCorrection s =
      (chapterVIDCertificateContourCorrectionFactorReal s : ℂ) := by
  rw [show exactCorrection s =
      ((1 + (chapterVIDCertificateContourCorrection - 1) *
        (pValue s ^ 6 - 1) /
          (chapterVIDCriticalParameterModulus - 1) : ℝ) : ℂ) by
    norm_num [exactCorrection]]
  norm_cast
  have hq : 0 ≤ chapterVIDCertificateParameterReal s := by
    rw [chapterVIDCertificateParameterReal_eq]
    exact (chapterVIDCertificateParameter_pos s).le
  rw [pValue_pow_six hq]
  unfold chapterVIDCertificateContourCorrectionFactorReal
    chapterVIDCertificateParameterReal
  field_simp [sub_ne_zero.mpr
    (ne_of_lt chapterVIDCriticalParameterModulus_lt_one)]
  ring

theorem exactU_eq (side : ChapterVIDPinchingArcSide) (t s : I) :
    exactU side t s =
      (chapterVIDCertificateContourRadiusReal s : ℂ) *
        chapterVIDRadialTailFixedUnit side t := by
  rw [exactU, exactCorrection_eq, exactUnit_eq]
  unfold pValue chapterVIDCertificateContourRadiusReal
  push_cast
  ring

theorem exactArgument_eq (side : ChapterVIDPinchingArcSide) (t : I) (s : ℝ) :
    exactArgument side t s =
      chapterVIDRootExponentialArgument (exactU side t s) -
        chapterVIDRootExponentialArgument chapterVIDCollisionLift := by
  unfold exactArgument chapterVIDRootExponentialArgument
  rw [show chapterVIDCollisionLift * chapterVIDCollisionLift ^ 2 =
    chapterVIDCollisionLift ^ 3 by ring]
  ring

theorem exactExpRelative_eq (side : ChapterVIDPinchingArcSide) (t : I) (s : ℝ) :
    exactExpRelative side t s =
      Complex.exp (chapterVIDRootExponentialArgument (exactU side t s) -
        chapterVIDRootExponentialArgument chapterVIDCollisionLift) := by
  rw [exactExpRelative, exactArgument_eq]

theorem exactMultiplierDelta_eq
    (side : ChapterVIDPinchingArcSide) (t : I) (s : ℝ) :
    exactMultiplierDelta side t s =
      chapterVIDRootRelativeMultiplierDelta (exactZeta s) (exactU side t s) := by
  unfold exactMultiplierDelta chapterVIDRootRelativeMultiplierDelta
  rw [exactExpRelative_eq]

theorem exactAnomaly_eq (side : ChapterVIDPinchingArcSide) (t : I) (s : ℝ) :
    exactAnomaly side t s =
      chapterVIDRootSecondAnomaly (exactZeta s) (exactU side t s) := by
  rw [chapterVIDRootSecondAnomaly_eq_relativeToBase]
  unfold chapterVIDRootSecondAnomalyRelativeToBase exactAnomaly
  rw [exactMultiplierDelta_eq]
  unfold chapterVIDRootRelativeMultiplierDelta
  field_simp [chapterVIDZRootBase_ne_zero, chapterVIDCollisionLift_ne_zero]
  ring

theorem exactFactorMinus_eq
    (side : ChapterVIDPinchingArcSide) (t : I) (s : ℝ) :
    exactFactorMinus side t s =
      chapterVIDRadialTailFactorMinus (exactZeta s) (exactU side t s) := by
  unfold exactFactorMinus chapterVIDRadialTailFactorMinus
  rw [exactAnomaly_eq]

theorem exactFactorPlusCoordinateDerivative_eq
    (side : ChapterVIDPinchingArcSide) (t : I) (s : ℝ)
    (hu : exactU side t s ≠ 0) :
    exactFactorPlusCoordinateDerivative side t s =
      chapterVIDRootCoordinateCollisionFactorPlusDerivative
        (exactZeta s) (exactU side t s) := by
  rw [chapterVIDRootCoordinateCollisionFactorPlusDerivative_eq_dependencyPreserving
    (exactZeta s) hu]
  unfold exactFactorPlusCoordinateDerivative
    chapterVIDRootFactorDerivativeDependencyPreserving
    chapterVIDRootFactorDerivativeLaurentDifference
    chapterVIDRootFactorDerivativePowerShape
    chapterVIDRootFactorDerivativePowerShapeDifference
  rw [exactMultiplierDelta_eq]
  field_simp [hu, chapterVIDCollisionLift_ne_zero]

theorem exactFactorPlus_eq
    (side : ChapterVIDPinchingArcSide) (t : I) (s : ℝ)
    (hζ : exactZeta s ≠ 0) (hu : exactU side t s ≠ 0) :
    exactFactorPlus side t s =
      chapterVIDRadialTailFactorPlus (exactZeta s) (exactU side t s) := by
  have hbase : chapterVIDRadialTailFactorPlus
      chapterVIDZRootBase chapterVIDCollisionLift = 0 := by
    rw [chapterVIDRadialTailFactorPlus_eq chapterVIDZRootBase_ne_zero
      chapterVIDCollisionLift_ne_zero]
    exact chapterVIDRootCoordinateCollisionFactorPlus_base
  unfold exactFactorPlus chapterVIDRadialTailFactorPlus at hbase ⊢
  rw [chapterVIDRootSecondAnomaly_base] at hbase
  rw [← exactAnomaly_eq]
  unfold exactAnomaly
  field_simp [hu, chapterVIDCollisionLift_ne_zero] at hbase ⊢
  linear_combination -(exactU side t s ^ 3) * hbase

theorem exactZeta_eq {s : ℝ} (hq : 0 < chapterVIDCertificateParameterReal s) :
    exactZeta s = (chapterVIDCertificateZetaReal s : ℂ) := by
  rw [show exactZeta s = ((pValue s ^ 2 : ℝ) : ℂ) by simp [exactZeta]]
  norm_cast
  unfold pValue chapterVIDCertificateZetaReal
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul hq.le]
  congr 1 <;> norm_num

theorem exactPDot_eq (s : ℝ) : exactPDot s = (pVelocity s : ℂ) := by
  unfold exactPDot pVelocity
  push_cast
  ring

theorem exactZetaVelocity_eq (s : I) :
    exactZetaLogDot s * exactZeta s =
      (chapterVIDCertificateZetaVelocityReal s : ℂ) := by
  rw [exactZeta_eq (by
    rw [chapterVIDCertificateParameterReal_eq]
    exact chapterVIDCertificateParameter_pos s)]
  rw [chapterVIDCertificateZetaVelocityReal_eq_log_mul]
  unfold exactZetaLogDot
  push_cast
  have hp6Real := pValue_pow_six (by
      rw [chapterVIDCertificateParameterReal_eq]
      exact (chapterVIDCertificateParameter_pos s).le)
  rw [chapterVIDCertificateParameterReal_eq] at hp6Real
  have hp6 : (pValue s : ℂ) ^ 6 =
      (chapterVIDCertificateParameter s : ℂ) := by
    simpa using congrArg Complex.ofReal hp6Real
  rw [hp6]
  ring

theorem exactRadiusVelocity_eq (s : I) :
    exactRadiusDot s =
      (chapterVIDCertificateContourRadiusVelocityReal s : ℂ) := by
  rw [exactRadiusDot, exactPDot_eq, exactCorrection_eq]
  rw [chapterVIDCertificateContourCorrectionFactorReal_eq]
  rw [chapterVIDCertificateContourRadiusVelocityReal_eq_log]
  rw [show chapterVIDCertificateParameter s ^ ((6 : ℝ)⁻¹) = pValue s by
    rw [pValue, chapterVIDCertificateParameterReal_eq]]
  push_cast
  have hp : pValue s ≠ 0 := (pValue_pos (by
    rw [chapterVIDCertificateParameterReal_eq]
    exact chapterVIDCertificateParameter_pos s)).ne'
  have hp6 := pValue_pow_six (by
    rw [chapterVIDCertificateParameterReal_eq]
    exact (chapterVIDCertificateParameter_pos s).le)
  rw [chapterVIDCertificateParameterReal_eq] at hp6
  unfold pVelocity
  rw [← hp6]
  push_cast
  field_simp [hp]

theorem exactUDot_eq (side : ChapterVIDPinchingArcSide) (t s : I) :
    exactUDot side t s =
      (chapterVIDCertificateContourRadiusVelocityReal s : ℂ) *
        chapterVIDRadialTailFixedUnit side t := by
  unfold exactUDot
  rw [exactRadiusVelocity_eq, exactUnit_eq]

theorem exactFactorPlusDot_eq
    (side : ChapterVIDPinchingArcSide) (t : I) (s : ℝ)
    (hu : exactU side t s ≠ 0) :
    exactFactorPlusCoordinateDerivative side t s * exactUDot side t s -
        2 * exactAnomaly side t s * exactZetaLogDot s =
      chapterVIDRadialTailFactorPlusDerivative
        (exactZeta s) (exactU side t s)
        (exactZetaLogDot s * exactZeta s) (exactUDot side t s) := by
  rw [exactFactorPlusCoordinateDerivative_eq side t s hu, exactAnomaly_eq]
  unfold chapterVIDRadialTailFactorPlusDerivative
    chapterVIDRadialTailAnomalyDerivative
    chapterVIDRootCoordinateCollisionFactorPlusDerivative
    chapterVIDRootSecondAnomalyLogDerivative
    chapterVIDRootSecondAnomaly chapterVIDRootToOriginalContour
  field_simp [hu]
  ring

theorem exactFactorMinusDot_eq
    (side : ChapterVIDPinchingArcSide) (t : I) (s : ℝ)
    (hζ : exactZeta s ≠ 0) (hu : exactU side t s ≠ 0) :
    exactFactorMinusDot side t s =
      chapterVIDRadialTailFactorMinusDerivative
        (exactZeta s) (exactU side t s)
        (exactZetaLogDot s * exactZeta s) (exactUDot side t s) := by
  have hy : chapterVIDRootSecondAnomaly (exactZeta s) (exactU side t s) ≠ 0 :=
    mul_ne_zero hζ (chapterVIDRootToOriginalContour_ne_zero hu)
  unfold exactFactorMinusDot chapterVIDRadialTailFactorMinusDerivative
    chapterVIDRadialTailAnomalyDerivative
    chapterVIDRootSecondAnomalyLogDerivative
  rw [exactAnomaly_eq]
  unfold chapterVIDRootSecondAnomaly chapterVIDRootToOriginalContour at hy ⊢
  field_simp [hu, hy]
  ring

theorem exactProgramDerivative_eq
    (side : ChapterVIDPinchingArcSide) (t : I) (s : ℝ)
    (hζ : exactZeta s ≠ 0) (hu : exactU side t s ≠ 0) :
    exactProgramDerivative side t s =
      chapterVIDRadialTailRadicandDerivative
        (exactZeta s) (exactU side t s)
        (exactZetaLogDot s * exactZeta s) (exactUDot side t s) := by
  unfold exactProgramDerivative chapterVIDRadialTailRadicandDerivative
  rw [exactFactorPlusDot_eq side t s hu, exactFactorMinus_eq,
    exactFactorPlus_eq side t s hζ hu, exactFactorMinusDot_eq side t s hζ hu]

theorem evalProgram_eq_actualDerivative
    (side : ChapterVIDPinchingArcSide) (t s : I) :
    evalProgram (program side) (exactInputs t s (exactRemainder side t s)) 52 =
      chapterVIDRadialTailActualDerivative side t s := by
  have hq : 0 < chapterVIDCertificateParameterReal s := by
    rw [chapterVIDCertificateParameterReal_eq]
    exact chapterVIDCertificateParameter_pos s
  have hζ : exactZeta s ≠ 0 := by
    rw [exactZeta_eq hq]
    exact Complex.ofReal_ne_zero.mpr
      (Real.rpow_pos_of_pos hq ((3 : ℝ)⁻¹)).ne'
  have hu : exactU side t s ≠ 0 := by
    rw [exactU_eq]
    apply mul_ne_zero
    · apply Complex.ofReal_ne_zero.mpr
      rw [chapterVIDCertificateContourRadiusReal_eq]
      exact (chapterVIDCertificateContourRadius_pos s).ne'
    · intro hzero
      have hnorm : ‖chapterVIDRadialTailFixedUnit side t‖ = 1 := by
        exact chapterVIDRationalPinchingArcUnit_norm side t
      rw [hzero, norm_zero] at hnorm
      norm_num at hnorm
  rw [evalProgram_exact, exactProgramDerivative_eq side t s hζ hu]
  rw [exactZetaVelocity_eq, exactUDot_eq]
  rw [exactZeta_eq hq, exactU_eq]
  rfl

end ChapterVIDRadialTailBaseCenteredSemantics
end PoincareChapterVI
