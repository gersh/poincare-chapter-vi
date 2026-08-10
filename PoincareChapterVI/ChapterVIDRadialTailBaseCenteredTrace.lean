/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.ChapterVIDRadialTailBaseCenteredProgram

/-! # Centre and directional traces for the collision-base-centred program -/

namespace PoincareChapterVI

open ChapterVIFieldExpression ChapterVILeanCompCertBatch

namespace ChapterVIDRadialTailBaseCenteredTrace

open Expr ChapterVIDRadialTailBaseCenteredProgram

abbrev Rectangle := ChapterVISignedDyadicComplexRectangle 40

def zero : Rectangle := ChapterVISignedDyadicComplexRectangle.pointInt 40 0
def one : Rectangle := ChapterVISignedDyadicComplexRectangle.pointInt 40 1
def imaginaryUnit : Rectangle :=
  ⟨⟨0, 0⟩, ⟨1099511627776, 1099511627776⟩⟩

def inputBoxes (p t remainder qdot cdot collision collisionInv collisionSq
    collisionInvCube collisionInvFourth yBase zetaBase : Rectangle) : Fin 56 → Rectangle
  | 0 => p
  | 1 => t
  | 2 => remainder
  | 3 => qdot
  | 4 => cdot
  | 5 => imaginaryUnit
  | 6 => collision
  | 7 => collisionInv
  | 8 => collisionSq
  | 9 => collisionInvCube
  | 10 => collisionInvFourth
  | 11 => yBase
  | 12 => zetaBase
  | _ => zero

def valueTrace (side : ChapterVIDPinchingArcSide) (boxes : Fin 56 → Rectangle) :=
  Expr.proposeProgramTrace boxes (program side)

def preliminaryVelocities (side : ChapterVIDPinchingArcSide)
    (boxes : Fin 56 → Rectangle) (angular : Bool) : Fin 56 → Rectangle
  | 0 => if angular then zero else (valueTrace side boxes).outputBoxes 34
  | 1 => if angular then one else zero
  | _ => zero

def preliminaryJet (side : ChapterVIDPinchingArcSide)
    (boxes : Fin 56 → Rectangle) (angular : Bool) :=
  Expr.proposeJetProgramTrace boxes (preliminaryVelocities side boxes angular) (program side)

def remainderVelocityBoxes (side : ChapterVIDPinchingArcSide)
    (boxes : Fin 56 → Rectangle) (angular : Bool) : Fin 56 → Rectangle :=
  Function.update (valueTrace side boxes).outputBoxes 21
    ((preliminaryJet side boxes angular).outputVelocityBoxes 21)

def remainderVelocityExpression : Expr 56 :=
  (expRelative - expDerivativePolynomial) * argumentDelta

def remainderVelocity (side : ChapterVIDPinchingArcSide)
    (boxes : Fin 56 → Rectangle) (angular : Bool) :=
  Expr.proposeTrace (remainderVelocityBoxes side boxes angular)
    remainderVelocityExpression

def finalVelocities (side : ChapterVIDPinchingArcSide)
    (boxes : Fin 56 → Rectangle) (angular : Bool) : Fin 56 → Rectangle
  | 0 => if angular then zero else (valueTrace side boxes).outputBoxes 34
  | 1 => if angular then one else zero
  | 2 => (remainderVelocity side boxes angular).output
  | _ => zero

def finalJet (side : ChapterVIDPinchingArcSide)
    (boxes : Fin 56 → Rectangle) (angular : Bool) :=
  Expr.proposeJetProgramTrace boxes (finalVelocities side boxes angular) (program side)

def centerOutput (side : ChapterVIDPinchingArcSide) (boxes : Fin 56 → Rectangle) : Rectangle :=
  (valueTrace side boxes).outputBoxes 52

def radialOutput (side : ChapterVIDPinchingArcSide) (boxes : Fin 56 → Rectangle) : Rectangle :=
  (finalJet side boxes false).outputVelocityBoxes 52

def angularOutput (side : ChapterVIDPinchingArcSide) (boxes : Fin 56 → Rectangle) : Rectangle :=
  (finalJet side boxes true).outputVelocityBoxes 52

def centerOperations (side : ChapterVIDPinchingArcSide) (boxes : Fin 56 → Rectangle) :
    List (DyadicOperation 40) := (valueTrace side boxes).operations

def variationOperations (side : ChapterVIDPinchingArcSide)
    (boxes : Fin 56 → Rectangle) (angular : Bool) : List (DyadicOperation 40) :=
  (valueTrace side boxes).operations ++ (preliminaryJet side boxes angular).operations ++
    (remainderVelocity side boxes angular).operations ++
    (finalJet side boxes angular).operations

end ChapterVIDRadialTailBaseCenteredTrace

end PoincareChapterVI
