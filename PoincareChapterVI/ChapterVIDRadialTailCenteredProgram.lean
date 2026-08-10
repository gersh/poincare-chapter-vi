/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.ChapterVIDRadialTailCenteredExpression

/-!
# Shared straight-line program for the radial-tail derivative

This program is the common-subexpression-eliminated form of the exact reduced derivative.  Its
register layout is part of the certificate format; both ordinary interval evaluation and the
forward directional-jet evaluator execute this same list.
-/

noncomputable section

namespace PoincareChapterVI

open ChapterVIFieldExpression

namespace ChapterVIDRadialTailCenteredProgram

open Expr

abbrev E := Expr 26

def p : E := .var 0
def t : E := .var 1
def exponential : E := .var 2
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
def anomaly : E := .var 13
def anomalyInv : E := .var 14
def pDot : E := .var 15
def radiusDot : E := .var 16
def uDot : E := .var 17
def zetaLogDot : E := .var 18
def laurentPlus : E := .var 19
def laurentMinus : E := .var 20
def laurentPlusDot : E := .var 21
def laurentMinusDot : E := .var 22
def anomalyLogDerivative : E := .var 23
def anomalyLogDot : E := .var 24
def derivative : E := .var 25

def assignment (target : Fin 26) (expression : E) : Assignment 26 :=
  ⟨target, expression.normalize⟩

def quarter : E :=
  ((1 - t ^ 2) + (2 * t) * imaginaryUnit) / (1 + t ^ 2)

def unitFormula (side : ChapterVIDPinchingArcSide) : E :=
  match side with
  | .upper => imaginaryUnit * quarter
  | .lower => -quarter

def derivativeFormula : E :=
  laurentPlusDot * laurentMinus + laurentPlus * laurentMinusDot -
    2 * (laurentPlusDot * anomalyInv + anomaly * laurentMinusDot) +
    2 * anomalyLogDot *
      (laurentPlus * anomalyInv - anomaly * laurentMinus)

/-- The shared SSA program.  Registers `0`--`5` are inputs and `6`--`25` are assigned in order. -/
def program (side : ChapterVIDPinchingArcSide) : List (Assignment 26) :=
  [ assignment 6 (1 + cdot * (p ^ 6 - 1) / qdot)
  , assignment 7 (unitFormula side)
  , assignment 8 (p * correction * unit)
  , assignment 9 u⁻¹
  , assignment 10 (u * u)
  , assignment 11 (uSq * u)
  , assignment 12 uCube⁻¹
  , assignment 13 (p * p * u * exponential)
  , assignment 14 anomaly⁻¹
  , assignment 15 (qdot / (6 * p ^ 5))
  , assignment 16 (pDot * correction + p * cdot)
  , assignment 17 (radiusDot * unit)
  , assignment 18 (qdot / (3 * p ^ 6))
  , assignment 19 ((10001 : E)⁻¹ * (10000 * uCube + uCubeInv - 200))
  , assignment 20 ((10001 : E)⁻¹ * (uCube + 10000 * uCubeInv - 200))
  , assignment 21 ((10001 : E)⁻¹ *
      (30000 * uSq * uDot - 3 * uCubeInv * uInv * uDot))
  , assignment 22 ((10001 : E)⁻¹ *
      (3 * uSq * uDot - 30000 * uCubeInv * uInv * uDot))
  , assignment 23 (uInv - (100 * (10001 : E)⁻¹) * (uInv ^ 4 + uSq))
  , assignment 24 (anomalyLogDerivative * uDot + zetaLogDot)
  , assignment 25 derivativeFormula
  ]

def finalValue (side : ChapterVIDPinchingArcSide) (values : Fin 26 → ℂ) : ℂ :=
  evalProgram (program side) values 25

def finalVelocity (side : ChapterVIDPinchingArcSide)
    (values velocities : Fin 26 → ℂ) : ℂ :=
  evalProgramVelocity (program side) values velocities 25

#eval (program .upper).map (fun a ↦ a.expression.nodeCount)

end ChapterVIDRadialTailCenteredProgram

end PoincareChapterVI
