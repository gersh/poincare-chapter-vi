/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.ChapterVIFieldExpressionTrace
import PoincareChapterVI.ChapterVILeanCompCertHighOrderAnomalyTrace
import PoincareChapterVI.ChapterVIDRadialTailPathDerivative

/-!
# Dependency-preserving radial-tail expressions

The old interval trace enclosed repeated Laurent quantities independently.  Here a single field
expression retains the common variables

`p = q^(1/6)`, `c = correction`, `v = angular unit`, and
`y = root second anomaly`.

The first radial derivative is Poincare's cancellation-reduced expression.  Its radial and
angular derivatives are produced by formal differentiation of that same expression, so they can
be used as certified variation bounds in a cell-centred table.
-/

noncomputable section

namespace PoincareChapterVI

open ChapterVIFieldExpression

namespace ChapterVIDRadialTailCenteredExpression

open Expr

abbrev E := Expr 7

def p : E := .var 0
def c : E := .var 1
def v : E := .var 2
def y : E := .var 3
def qdot : E := .var 4
def cdot : E := .var 5
def vt : E := .var 6

def u : E := p * c * v
def zeta : E := p ^ 2
def pdot : E := qdot / (6 * p ^ 5)
def rdot : E := pdot * c + p * cdot
def udot : E := rdot * v
def zetaLogDot : E := qdot / (3 * p ^ 6)

def inverse10001 : E := (10001 : E)⁻¹

def laurentPlus : E :=
  inverse10001 * (10000 * u ^ 3 + (u ^ 3)⁻¹ - 200)

def laurentMinus : E :=
  inverse10001 * (u ^ 3 + 10000 * (u ^ 3)⁻¹ - 200)

def laurentPlusDot : E :=
  inverse10001 * (30000 * u ^ 2 * udot - 3 * (u ^ 3)⁻¹ * u⁻¹ * udot)

def laurentMinusDot : E :=
  inverse10001 * (3 * u ^ 2 * udot - 30000 * (u ^ 3)⁻¹ * u⁻¹ * udot)

def anomalyLogDerivative : E :=
  u⁻¹ - (100 * inverse10001) * (u⁻¹ ^ 4 + u ^ 2)

def anomalyLogDot : E := anomalyLogDerivative * udot + zetaLogDot

/-- Cancellation-preserving first derivative of the literal radicand along the radial path. -/
def radialDerivativeRaw : E :=
  laurentPlusDot * laurentMinus + laurentPlus * laurentMinusDot -
    2 * (laurentPlusDot * y⁻¹ + y * laurentMinusDot) +
    2 * anomalyLogDot * (laurentPlus * y⁻¹ - y * laurentMinus)

def radialVelocity : Fin 7 → E
  | 0 => pdot
  | 1 => cdot
  | 2 => 0
  | 3 => y * anomalyLogDot
  | 4 => 0
  | 5 => 0
  | 6 => 0

def angularUdot : E := p * c * vt

def angularVelocity : Fin 7 → E
  | 0 => 0
  | 1 => 0
  | 2 => vt
  | 3 => y * (anomalyLogDerivative * angularUdot)
  | 4 => 0
  | 5 => 0
  | 6 => 0

def radialDerivative : E := radialDerivativeRaw.normalize

/-- Second radial derivative, used only as a uniform variation bound. -/
def radialSecondDerivative : E :=
  (radialDerivative.directional radialVelocity).normalize

/-- Angular derivative of the radial derivative, used only as a uniform variation bound. -/
def radialAngularDerivative : E :=
  (radialDerivative.directional angularVelocity).normalize

theorem radialDerivative_eval (values : Fin 7 → ℂ) :
    radialDerivative.eval values = radialDerivativeRaw.eval values :=
  Expr.eval_normalize values radialDerivativeRaw

theorem radialSecondDerivative_eval (values : Fin 7 → ℂ) :
    radialSecondDerivative.eval values =
      (radialDerivative.directional radialVelocity).eval values :=
  Expr.eval_normalize values _

theorem radialAngularDerivative_eval (values : Fin 7 → ℂ) :
    radialAngularDerivative.eval values =
      (radialDerivative.directional angularVelocity).eval values :=
  Expr.eval_normalize values _

#eval radialDerivative.nodeCount
#eval radialSecondDerivative.nodeCount
#eval radialAngularDerivative.nodeCount

/-! ## Fully parameter-dependent form

For the production table we eliminate two more independent interval inputs.  Since
`p^6 = 1 + qdot * s`, the affine correction is exactly
`1 + cdot * (p^6 - 1) / qdot`.  The unit-circle point is reconstructed from the single rational
quarter parameter `t`.  The only analytic input left is `e = exp(argument)`; its interval and
its two velocities come from the proved degree-five exponential remainder.
-/

namespace ParameterExpression

abbrev PE := Expr 6

def p : PE := .var 0
def t : PE := .var 1
def e : PE := .var 2
def qdot : PE := .var 3
def cdot : PE := .var 4
def imaginaryUnit : PE := .var 5

def correction : PE := 1 + cdot * (p ^ 6 - 1) / qdot

def quarter : PE :=
  ((1 - t ^ 2) + (2 * t) * imaginaryUnit) / (1 + t ^ 2)

def unit (side : ChapterVIDPinchingArcSide) : PE :=
  match side with
  | .upper => imaginaryUnit * quarter
  | .lower => -quarter

def u (side : ChapterVIDPinchingArcSide) : PE :=
  p * correction * unit side

def zeta : PE := p ^ 2
def pdot : PE := qdot / (6 * p ^ 5)
def rdot : PE := pdot * correction + p * cdot
def udot (side : ChapterVIDPinchingArcSide) : PE := rdot * unit side
def zetaLogDot : PE := qdot / (3 * p ^ 6)

def inverse10001 : PE := (10001 : PE)⁻¹

def laurentPlus (side : ChapterVIDPinchingArcSide) : PE :=
  inverse10001 * (10000 * u side ^ 3 + (u side ^ 3)⁻¹ - 200)

def laurentMinus (side : ChapterVIDPinchingArcSide) : PE :=
  inverse10001 * (u side ^ 3 + 10000 * (u side ^ 3)⁻¹ - 200)

def laurentPlusDot (side : ChapterVIDPinchingArcSide) : PE :=
  inverse10001 * (30000 * u side ^ 2 * udot side -
    3 * (u side ^ 3)⁻¹ * (u side)⁻¹ * udot side)

def laurentMinusDot (side : ChapterVIDPinchingArcSide) : PE :=
  inverse10001 * (3 * u side ^ 2 * udot side -
    30000 * (u side ^ 3)⁻¹ * (u side)⁻¹ * udot side)

def anomaly (side : ChapterVIDPinchingArcSide) : PE :=
  zeta * u side * e

def anomalyLogDerivative (side : ChapterVIDPinchingArcSide) : PE :=
  (u side)⁻¹ - (100 * inverse10001) * ((u side)⁻¹ ^ 4 + u side ^ 2)

def anomalyLogDot (side : ChapterVIDPinchingArcSide) : PE :=
  anomalyLogDerivative side * udot side + zetaLogDot

def radialDerivativeRaw (side : ChapterVIDPinchingArcSide) : PE :=
  let A := laurentPlus side
  let B := laurentMinus side
  let a := laurentPlusDot side
  let b := laurentMinusDot side
  let y := anomaly side
  let L := anomalyLogDot side
  a * B + A * b - 2 * (a * y⁻¹ + y * b) + 2 * L * (A * y⁻¹ - y * B)

def exponentialArgument (side : ChapterVIDPinchingArcSide) : PE :=
  (100 / 30003) * ((u side)⁻¹ ^ 3 - u side ^ 3)

def radialBaseVelocity : Fin 6 → PE
  | 0 => pdot
  | 1 => 0
  | 2 => 0
  | 3 => 0
  | 4 => 0
  | 5 => 0

def radialVelocity (side : ChapterVIDPinchingArcSide) : Fin 6 → PE
  | 0 => pdot
  | 1 => 0
  | 2 => e * (exponentialArgument side).directional radialBaseVelocity
  | 3 => 0
  | 4 => 0
  | 5 => 0

def angularBaseVelocity : Fin 6 → PE
  | 0 => 0
  | 1 => 1
  | 2 => 0
  | 3 => 0
  | 4 => 0
  | 5 => 0

def angularVelocity (side : ChapterVIDPinchingArcSide) : Fin 6 → PE
  | 0 => 0
  | 1 => 1
  | 2 => e * (exponentialArgument side).directional angularBaseVelocity
  | 3 => 0
  | 4 => 0
  | 5 => 0

def radialDerivative (side : ChapterVIDPinchingArcSide) : PE :=
  (radialDerivativeRaw side).normalize

#eval (radialDerivative .upper).nodeCount

end ParameterExpression

end ChapterVIDRadialTailCenteredExpression

end PoincareChapterVI
