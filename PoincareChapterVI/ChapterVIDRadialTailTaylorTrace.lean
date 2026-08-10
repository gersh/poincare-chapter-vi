/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.ChapterVIDRadialTailTaylorProgram

/-! # Centre and directional traces for the Taylor-preserving program -/

namespace PoincareChapterVI

open ChapterVIFieldExpression ChapterVILeanCompCertBatch

namespace ChapterVIDRadialTailTaylorTrace

open Expr ChapterVIDRadialTailTaylorProgram

abbrev Rectangle := ChapterVISignedDyadicComplexRectangle 40

def zero : Rectangle := ChapterVISignedDyadicComplexRectangle.pointInt 40 0
def one : Rectangle := ChapterVISignedDyadicComplexRectangle.pointInt 40 1
def imaginaryUnit : Rectangle :=
  ⟨⟨0, 0⟩, ⟨1099511627776, 1099511627776⟩⟩

def inputBoxes (p t remainder qdot cdot : Rectangle) : Fin 33 → Rectangle
  | 0 => p
  | 1 => t
  | 2 => remainder
  | 3 => qdot
  | 4 => cdot
  | 5 => imaginaryUnit
  | _ => zero

def valueTrace (side : ChapterVIDPinchingArcSide) (boxes : Fin 33 → Rectangle) :=
  Expr.proposeProgramTrace boxes (program side)

/-- With zero remainder velocity, the preliminary jet computes the exact argument velocity. -/
def preliminaryVelocities (side : ChapterVIDPinchingArcSide)
    (boxes : Fin 33 → Rectangle) (angular : Bool) : Fin 33 → Rectangle
  | 0 => if angular then zero else (valueTrace side boxes).outputBoxes 22
  | 1 => if angular then one else zero
  | _ => zero

def preliminaryJet (side : ChapterVIDPinchingArcSide)
    (boxes : Fin 33 → Rectangle) (angular : Bool) :=
  Expr.proposeJetProgramTrace boxes (preliminaryVelocities side boxes angular) (program side)

def remainderVelocityBoxes (side : ChapterVIDPinchingArcSide)
    (boxes : Fin 33 → Rectangle) (angular : Bool) : Fin 33 → Rectangle :=
  Function.update (valueTrace side boxes).outputBoxes 13
    ((preliminaryJet side boxes angular).outputVelocityBoxes 13)

def remainderVelocityExpression : Expr 33 :=
  (exponential - expDerivativePolynomial) * argument

def remainderVelocity (side : ChapterVIDPinchingArcSide)
    (boxes : Fin 33 → Rectangle) (angular : Bool) :=
  Expr.proposeTrace (remainderVelocityBoxes side boxes angular)
    remainderVelocityExpression

def finalVelocities (side : ChapterVIDPinchingArcSide)
    (boxes : Fin 33 → Rectangle) (angular : Bool) : Fin 33 → Rectangle
  | 0 => if angular then zero else (valueTrace side boxes).outputBoxes 22
  | 1 => if angular then one else zero
  | 2 => (remainderVelocity side boxes angular).output
  | _ => zero

def finalJet (side : ChapterVIDPinchingArcSide)
    (boxes : Fin 33 → Rectangle) (angular : Bool) :=
  Expr.proposeJetProgramTrace boxes (finalVelocities side boxes angular) (program side)

def centerOutput (side : ChapterVIDPinchingArcSide) (boxes : Fin 33 → Rectangle) : Rectangle :=
  (valueTrace side boxes).outputBoxes 32

def radialOutput (side : ChapterVIDPinchingArcSide) (boxes : Fin 33 → Rectangle) : Rectangle :=
  (finalJet side boxes false).outputVelocityBoxes 32

def angularOutput (side : ChapterVIDPinchingArcSide) (boxes : Fin 33 → Rectangle) : Rectangle :=
  (finalJet side boxes true).outputVelocityBoxes 32

def centerOperations (side : ChapterVIDPinchingArcSide) (boxes : Fin 33 → Rectangle) :
    List (DyadicOperation 40) := (valueTrace side boxes).operations

def variationOperations (side : ChapterVIDPinchingArcSide)
    (boxes : Fin 33 → Rectangle) (angular : Bool) : List (DyadicOperation 40) :=
  (valueTrace side boxes).operations ++ (preliminaryJet side boxes angular).operations ++
    (remainderVelocity side boxes angular).operations ++
    (finalJet side boxes angular).operations

end ChapterVIDRadialTailTaylorTrace

end PoincareChapterVI
