/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.ChapterVIDRadialTailTaylorSemantics

namespace PoincareChapterVI.ChapterVIDRadialTailEndpointTrace

open ChapterVIFieldExpression
open ChapterVILeanCompCertAffineTrace
open ChapterVIDRadialTailBaseCenteredAffineTrace
open ChapterVIDRadialTailCellInputTrace
open Expr

set_option maxRecDepth 100000
set_option maxHeartbeats 0

abbrev E := Expr 5
def r (i : Fin 5) : E := .var i
def t := r 0
def collision := r 1
def yBase := r 2
def exponential := r 3
def imaginaryUnit := r 4

def quarter : E := ((1 - t ^ 2) + (2 * t) * imaginaryUnit) / (1 + t ^ 2)
def unit : ChapterVIDPinchingArcSide → E
  | .upper => imaginaryUnit * quarter
  | .lower => -quarter
def u (side : ChapterVIDPinchingArcSide) : E := -collision * unit side
def argument (side : ChapterVIDPinchingArcSide) : E :=
  (100 / 30003) * ((u side) ⁻¹ ^ 3 - u side ^ 3 - (collision⁻¹ ^ 3 - collision ^ 3))
def anomaly (side : ChapterVIDPinchingArcSide) : E :=
  yBase * exponential * (u side * collision⁻¹)
def factorPlus (side : ChapterVIDPinchingArcSide) : E :=
  (10000 * u side ^ 3 + (u side ^ 3)⁻¹ - 200) / 10001 - 2 * anomaly side
def factorMinus (side : ChapterVIDPinchingArcSide) : E :=
  (u side ^ 3 + 10000 * (u side ^ 3)⁻¹ - 200) / 10001 -
    2 * (anomaly side)⁻¹
def radicand (side : ChapterVIDPinchingArcSide) : E :=
  factorPlus side * factorMinus side

def basicVelocity : Fin 5 → E
  | 0 => 1
  | _ => 0

def velocity (side : ChapterVIDPinchingArcSide) : Fin 5 → E
  | 0 => 1
  | 3 => exponential * (argument side).directional basicVelocity
  | _ => 0

def firstDerivative (side : ChapterVIDPinchingArcSide) : E :=
  (radicand side).directional (velocity side)

def endpointInputs (side : ChapterVIDPinchingArcSide) (row : Fin 6)
    (angular : Fin (angularCells side row)) : Fin 56 → Model 40 :=
  inputModels ChapterVIDRadialTailBaseConstantTrace.pBase
    (tModel side row angular) remainderModel
    ChapterVIDRadialTailBaseConstantTrace.qdot
    ChapterVIDRadialTailBaseConstantTrace.cdot
    ChapterVIDRadialTailBaseConstantTrace.collisionModel
    ChapterVIDRadialTailBaseConstantTrace.collisionInv
    ChapterVIDRadialTailBaseConstantTrace.collisionSq
    ChapterVIDRadialTailBaseConstantTrace.collisionInvCube
    ChapterVIDRadialTailBaseConstantTrace.collisionInvFourth
    ChapterVIDRadialTailBaseConstantTrace.yBase
    ChapterVIDRadialTailBaseConstantTrace.zetaBase

def boxes (side : ChapterVIDPinchingArcSide) (row : Fin 6)
    (angular : Fin (angularCells side row)) : Fin 5 →
      ChapterVISignedDyadicComplexRectangle 40
  | 0 => (tModel side row angular).range
  | 1 => ChapterVIDRadialTailBaseConstantTrace.collisionModel.range
  | 2 => ChapterVIDRadialTailBaseConstantTrace.yBase.range
  | 3 => ((trace side (endpointInputs side row angular)).outputs 27).range
  | 4 => ChapterVIDRadialTailBaseCenteredAffineTrace.imaginaryUnit.range


def rationalTModel (a b : ℚ) : Model 40 :=
  { center := realRectangle (enclose ((a + b) / 2))
    radial := ChapterVIDRadialTailCellInputTrace.zeroRectangle
    angular := realRectangle (enclose ((b - a) / 2))
    error := ChapterVIDRadialTailCellInputTrace.zeroRectangle }

def endpointInputsFromT (side : ChapterVIDPinchingArcSide) (tm : Model 40) :
    Fin 56 → Model 40 :=
  inputModels ChapterVIDRadialTailBaseConstantTrace.pBase tm remainderModel
    ChapterVIDRadialTailBaseConstantTrace.qdot
    ChapterVIDRadialTailBaseConstantTrace.cdot
    ChapterVIDRadialTailBaseConstantTrace.collisionModel
    ChapterVIDRadialTailBaseConstantTrace.collisionInv
    ChapterVIDRadialTailBaseConstantTrace.collisionSq
    ChapterVIDRadialTailBaseConstantTrace.collisionInvCube
    ChapterVIDRadialTailBaseConstantTrace.collisionInvFourth
    ChapterVIDRadialTailBaseConstantTrace.yBase
    ChapterVIDRadialTailBaseConstantTrace.zetaBase

def boxesFromT (side : ChapterVIDPinchingArcSide) (tm : Model 40) : Fin 5 →
    ChapterVISignedDyadicComplexRectangle 40
  | 0 => tm.range
  | 1 => ChapterVIDRadialTailBaseConstantTrace.collisionModel.range
  | 2 => ChapterVIDRadialTailBaseConstantTrace.yBase.range
  | 3 => ((trace side (endpointInputsFromT side tm)).outputs 27).range
  | 4 => ChapterVIDRadialTailBaseCenteredAffineTrace.imaginaryUnit.range

def velocityBoxesFromT (side : ChapterVIDPinchingArcSide) (tm : Model 40) :
    Fin 5 → ChapterVISignedDyadicComplexRectangle 40 := fun i ↦
  (proposeTrace (boxesFromT side tm) (velocity side i)).output

def secondJetFromT (side : ChapterVIDPinchingArcSide) (a b : ℚ) :=
  let tm := rationalTModel a b
  proposeJetTrace (boxesFromT side tm) (velocityBoxesFromT side tm)
    (firstDerivative side)

def jetLowerFromT (side : ChapterVIDPinchingArcSide) (a b : ℚ) : Int :=
  (secondJetFromT side a b).derivative.real.lower

def upperLocalStart (i : Fin 63) : ℚ := (961 + i.val) / 1024
def upperLocalEnd (i : Fin 63) : ℚ := (962 + i.val) / 1024
def upperLocalLower (i : Fin 63) : Int :=
  jetLowerFromT .upper (upperLocalStart i) (upperLocalEnd i)

end PoincareChapterVI.ChapterVIDRadialTailEndpointTrace
