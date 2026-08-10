/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.ChapterVIDRadialTailTaylorTrace
import PoincareChapterVI.ChapterVILeanCompCertDependencyPreservingFactorDerivativeTrace

/-!
# Collision-base-centred radial-tail derivative program

Both the vanishing collision factor and its coordinate derivative are evaluated in exact forms
where every cancellation at `D` is exposed by a factor `u-D`, `ζ/ζ_D-1`, or
`exp(A(u)-A(D))-1`.
-/

noncomputable section

namespace PoincareChapterVI

open ChapterVIFieldExpression

namespace ChapterVIDRadialTailBaseCenteredProgram

open Expr

abbrev E := Expr 56

def r (n : Fin 56) : E := .var n

-- Inputs 0--12.
def p := r 0
def t := r 1
def expRemainder := r 2
def qdot := r 3
def cdot := r 4
def imaginaryUnit := r 5
def collision := r 6
def collisionInv := r 7
def collisionSq := r 8
def collisionInvCube := r 9
def collisionInvFourth := r 10
def yBase := r 11
def zetaBase := r 12

-- Assigned registers 13--55.
def correction := r 13
def unit := r 14
def u := r 15
def uInv := r 16
def uSq := r 17
def uCube := r 18
def uCubeInv := r 19
def coordinateDelta := r 20
def argumentDelta := r 21
def argumentSq := r 22
def argumentCube := r 23
def argumentFourth := r 24
def argumentFifth := r 25
def expDerivativePolynomial := r 26
def expRelative := r 27
def zeta := r 28
def zetaDelta := r 29
def multiplierDelta := r 30
def uRatio := r 31
def anomaly := r 32
def anomalyInv := r 33
def pDot := r 34
def radiusDot := r 35
def uDot := r 36
def zetaLogDot := r 37
def factorMinusLaurent := r 38
def factorMinus := r 39
def minusLaurentDot := r 40
def anomalyLogDerivative := r 41
def anomalyLogDot := r 42
def factorMinusDot := r 43
def laurentDifference := r 44
def powerShape := r 45
def powerShapeDifference := r 46
def factorPlusCoordinateDerivative := r 47
def factorPlusDot := r 48
def laurentValueDifference := r 49
def anomalyDifference := r 50
def factorPlus := r 51
def derivative := r 52
-- 53--55 are reserved for subsequent certificate refinements.

def assignment (target : Fin 56) (expression : E) : Assignment 56 :=
  ⟨target, expression⟩

def quarter : E :=
  ((1 - t ^ 2) + (2 * t) * imaginaryUnit) / (1 + t ^ 2)

def unitFormula (side : ChapterVIDPinchingArcSide) : E :=
  match side with
  | .upper => imaginaryUnit * quarter
  | .lower => -quarter

def program (side : ChapterVIDPinchingArcSide) : List (Assignment 56) :=
  [ assignment 13 (1 + cdot * (p ^ 6 - 1) / qdot)
  , assignment 14 (unitFormula side)
  , assignment 15 (p * correction * unit)
  , assignment 16 u⁻¹
  , assignment 17 (u * u)
  , assignment 18 (uSq * u)
  , assignment 19 uCube⁻¹
  , assignment 20 (u - collision)
  , assignment 21 ((100 / 30003) *
      ((uInv ^ 3 - uCube) -
        (collisionInvCube - collision * collisionSq)))
  , assignment 22 (argumentDelta * argumentDelta)
  , assignment 23 (argumentSq * argumentDelta)
  , assignment 24 (argumentCube * argumentDelta)
  , assignment 25 (argumentFourth * argumentDelta)
  , assignment 26 (1 + argumentDelta + argumentSq / 2 + argumentCube / 6 +
      argumentFourth / 24)
  , assignment 27 (expDerivativePolynomial + argumentFifth / 120 + expRemainder)
  , assignment 28 (p * p)
  , assignment 29 (zeta / zetaBase - 1)
  , assignment 30 (zetaDelta * expRelative + (expRelative - 1))
  , assignment 31 (u * collisionInv)
  , assignment 32 (yBase * (1 + multiplierDelta) * uRatio)
  , assignment 33 anomaly⁻¹
  , assignment 34 (qdot / (6 * p ^ 5))
  , assignment 35 (pDot * correction + p * cdot)
  , assignment 36 (radiusDot * unit)
  , assignment 37 (qdot / (3 * p ^ 6))
  , assignment 38 ((10001 : E)⁻¹ * (uCube + 10000 * uCubeInv - 200))
  , assignment 39 (factorMinusLaurent - 2 * anomalyInv)
  , assignment 40 ((10001 : E)⁻¹ *
      (3 * uSq * uDot - 30000 * uCubeInv * uInv * uDot))
  , assignment 41 (uInv - (100 * (10001 : E)⁻¹) * (uInv ^ 4 + uSq))
  , assignment 42 (anomalyLogDerivative * uDot + zetaLogDot)
  , assignment 43 (minusLaurentDot + 2 * anomalyInv * anomalyLogDot)
  , assignment 44 ((10001 : E)⁻¹ * coordinateDelta * (u + collision) *
      (30000 + 3 * (uInv ^ 4 * collisionInvFourth) *
        (uSq + collisionSq)))
  , assignment 45 (collisionInv * uInv ^ 3 + uCube * collisionInv)
  , assignment 46 (coordinateDelta * (uSq + u * collision + collisionSq) *
      collisionInv * (1 - uInv ^ 3 * collisionInvCube))
  , assignment 47 (laurentDifference -
      2 * (yBase * collisionInv) * multiplierDelta +
      (200 / 10001) * yBase *
        (multiplierDelta * powerShape + powerShapeDifference))
  , assignment 48 (factorPlusCoordinateDerivative * uDot -
      2 * anomaly * zetaLogDot)
  , assignment 49 ((10001 : E)⁻¹ * coordinateDelta *
      (uSq + u * collision + collisionSq) *
      (10000 - uInv ^ 3 * collisionInvCube))
  , assignment 50 (yBase *
      (coordinateDelta * collisionInv + uRatio * multiplierDelta))
  , assignment 51 (laurentValueDifference - 2 * anomalyDifference)
  , assignment 52 (factorPlusDot * factorMinus + factorPlus * factorMinusDot)
  ]

def finalValue (side : ChapterVIDPinchingArcSide) (values : Fin 56 → ℂ) : ℂ :=
  evalProgram (program side) values 52

def finalVelocity (side : ChapterVIDPinchingArcSide)
    (values velocities : Fin 56 → ℂ) : ℂ :=
  evalProgramVelocity (program side) values velocities 52

end ChapterVIDRadialTailBaseCenteredProgram

end PoincareChapterVI
