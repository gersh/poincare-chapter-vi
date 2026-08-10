/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.ChapterVIDRadialTailCenteredTrace

/-!
# Taylor-dependency-preserving radial-tail program

The analytic exponential is represented as `P₅(a) + ρ`, where the sole independent input `ρ`
has the proved norm bound `|a|⁶ / 512`.  Thus the argument, polynomial, anomaly, inverse anomaly,
and all Laurent terms remain in one shared straight-line graph.
-/

noncomputable section

namespace PoincareChapterVI

open ChapterVIFieldExpression

namespace ChapterVIDRadialTailTaylorProgram

open Expr

abbrev E := Expr 33

def p : E := .var 0
def t : E := .var 1
def exponentialRemainder : E := .var 2
def qdot : E := .var 3
def cdot : E := .var 4
def imaginaryUnit : E := .var 5
def correction : E := .var 6
def unit : E := .var 7
def u : E := .var 8
def uInv : E := .var 9
def uSq : E := .var 10
def uCube : E := .var 11
def uCubeInv : E := .var 12
def argument : E := .var 13
def argumentSq : E := .var 14
def argumentCube : E := .var 15
def argumentFourth : E := .var 16
def argumentFifth : E := .var 17
def expDerivativePolynomial : E := .var 18
def exponential : E := .var 19
def anomaly : E := .var 20
def anomalyInv : E := .var 21
def pDot : E := .var 22
def radiusDot : E := .var 23
def uDot : E := .var 24
def zetaLogDot : E := .var 25
def laurentPlus : E := .var 26
def laurentMinus : E := .var 27
def laurentPlusDot : E := .var 28
def laurentMinusDot : E := .var 29
def anomalyLogDerivative : E := .var 30
def anomalyLogDot : E := .var 31
def derivative : E := .var 32

def assignment (target : Fin 33) (expression : E) : Assignment 33 :=
  ⟨target, expression.normalize⟩

def quarter : E :=
  ((1 - t ^ 2) + (2 * t) * imaginaryUnit) / (1 + t ^ 2)

def unitFormula (side : ChapterVIDPinchingArcSide) : E :=
  match side with
  | .upper => imaginaryUnit * quarter
  | .lower => -quarter

def derivativeFormula : E :=
  (laurentPlusDot - 2 * anomaly * anomalyLogDot) *
      (laurentMinus - 2 * anomalyInv) +
    (laurentPlus - 2 * anomaly) *
      (laurentMinusDot + 2 * anomalyInv * anomalyLogDot)

def program (side : ChapterVIDPinchingArcSide) : List (Assignment 33) :=
  [ assignment 6 (1 + cdot * (p ^ 6 - 1) / qdot)
  , assignment 7 (unitFormula side)
  , assignment 8 (p * correction * unit)
  , assignment 9 u⁻¹
  , assignment 10 (u * u)
  , assignment 11 (uSq * u)
  , assignment 12 uCube⁻¹
  , assignment 13 ((100 / 30003) * (uInv ^ 3 - uCube))
  , assignment 14 (argument * argument)
  , assignment 15 (argumentSq * argument)
  , assignment 16 (argumentCube * argument)
  , assignment 17 (argumentFourth * argument)
  , assignment 18 (1 + argument + argumentSq / 2 + argumentCube / 6 +
      argumentFourth / 24)
  , assignment 19 (expDerivativePolynomial + argumentFifth / 120 +
      exponentialRemainder)
  , assignment 20 (p * p * u * exponential)
  , assignment 21 anomaly⁻¹
  , assignment 22 (qdot / (6 * p ^ 5))
  , assignment 23 (pDot * correction + p * cdot)
  , assignment 24 (radiusDot * unit)
  , assignment 25 (qdot / (3 * p ^ 6))
  , assignment 26 ((10001 : E)⁻¹ * (10000 * uCube + uCubeInv - 200))
  , assignment 27 ((10001 : E)⁻¹ * (uCube + 10000 * uCubeInv - 200))
  , assignment 28 ((10001 : E)⁻¹ *
      (30000 * uSq * uDot - 3 * uCubeInv * uInv * uDot))
  , assignment 29 ((10001 : E)⁻¹ *
      (3 * uSq * uDot - 30000 * uCubeInv * uInv * uDot))
  , assignment 30 (uInv - (100 * (10001 : E)⁻¹) * (uInv ^ 4 + uSq))
  , assignment 31 (anomalyLogDerivative * uDot + zetaLogDot)
  , assignment 32 derivativeFormula
  ]

def finalValue (side : ChapterVIDPinchingArcSide) (values : Fin 33 → ℂ) : ℂ :=
  evalProgram (program side) values 32

def finalVelocity (side : ChapterVIDPinchingArcSide)
    (values velocities : Fin 33 → ℂ) : ℂ :=
  evalProgramVelocity (program side) values velocities 32

end ChapterVIDRadialTailTaylorProgram

end PoincareChapterVI
