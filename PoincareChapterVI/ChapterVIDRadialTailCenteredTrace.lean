/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.ChapterVIDRadialTailCenteredProgram

/-!
# Cell-centred radial-tail trace

The centre trace evaluates the exact reduced derivative.  The two jet traces enclose its radial
and rational-angular derivatives on a complete cell.  Each straight-line program retains all
shared Laurent powers, velocities, and anomaly inverses.
-/

namespace PoincareChapterVI

open ChapterVIFieldExpression
open ChapterVILeanCompCertBatch

namespace ChapterVIDRadialTailCenteredTrace

open Expr ChapterVIDRadialTailCenteredProgram

abbrev Rectangle := ChapterVISignedDyadicComplexRectangle 40

def zero : Rectangle := ChapterVISignedDyadicComplexRectangle.pointInt 40 0
def one : Rectangle := ChapterVISignedDyadicComplexRectangle.pointInt 40 1
def imaginaryUnit : Rectangle :=
  ⟨⟨0, 0⟩, ⟨1099511627776, 1099511627776⟩⟩

/-- Fill the unused SSA registers with zero. -/
def inputBoxes (p t exponential qdot cdot : Rectangle) : Fin 26 → Rectangle
  | 0 => p
  | 1 => t
  | 2 => exponential
  | 3 => qdot
  | 4 => cdot
  | 5 => imaginaryUnit
  | _ => zero

def valueTrace (side : ChapterVIDPinchingArcSide) (boxes : Fin 26 → Rectangle) :=
  Expr.proposeProgramTrace boxes (program side)

def radialExpVelocityExpression : Expr 26 :=
  exponential * (anomalyLogDerivative - uInv) * uDot

def radialExpVelocity (side : ChapterVIDPinchingArcSide)
    (boxes : Fin 26 → Rectangle) :=
  Expr.proposeTrace (valueTrace side boxes).outputBoxes radialExpVelocityExpression

def radialInitialVelocities (side : ChapterVIDPinchingArcSide)
    (boxes : Fin 26 → Rectangle) : Fin 26 → Rectangle
  | 0 => (valueTrace side boxes).outputBoxes 15
  | 2 => (radialExpVelocity side boxes).output
  | _ => zero

def radialJet (side : ChapterVIDPinchingArcSide) (boxes : Fin 26 → Rectangle) :=
  Expr.proposeJetProgramTrace boxes (radialInitialVelocities side boxes) (program side)

def angularZeroEVelocities : Fin 26 → Rectangle
  | 1 => one
  | _ => zero

def angularPreJet (side : ChapterVIDPinchingArcSide) (boxes : Fin 26 → Rectangle) :=
  Expr.proposeJetProgramTrace boxes angularZeroEVelocities (program side)

def angularExpBoxes (side : ChapterVIDPinchingArcSide)
    (boxes : Fin 26 → Rectangle) : Fin 26 → Rectangle :=
  Function.update (valueTrace side boxes).outputBoxes 8
    ((angularPreJet side boxes).outputVelocityBoxes 8)

def angularExpVelocityExpression : Expr 26 :=
  exponential * (anomalyLogDerivative - uInv) * u

def angularExpVelocity (side : ChapterVIDPinchingArcSide)
    (boxes : Fin 26 → Rectangle) :=
  Expr.proposeTrace (angularExpBoxes side boxes) angularExpVelocityExpression

def angularInitialVelocities (side : ChapterVIDPinchingArcSide)
    (boxes : Fin 26 → Rectangle) : Fin 26 → Rectangle
  | 1 => one
  | 2 => (angularExpVelocity side boxes).output
  | _ => zero

def angularJet (side : ChapterVIDPinchingArcSide) (boxes : Fin 26 → Rectangle) :=
  Expr.proposeJetProgramTrace boxes (angularInitialVelocities side boxes) (program side)

def centerOutput (side : ChapterVIDPinchingArcSide) (boxes : Fin 26 → Rectangle) : Rectangle :=
  (valueTrace side boxes).outputBoxes 25

def radialOutput (side : ChapterVIDPinchingArcSide) (boxes : Fin 26 → Rectangle) : Rectangle :=
  (radialJet side boxes).outputVelocityBoxes 25

def angularOutput (side : ChapterVIDPinchingArcSide) (boxes : Fin 26 → Rectangle) : Rectangle :=
  (angularJet side boxes).outputVelocityBoxes 25

def centerOperations (side : ChapterVIDPinchingArcSide) (boxes : Fin 26 → Rectangle) :
    List (DyadicOperation 40) :=
  (valueTrace side boxes).operations

def radialOperations (side : ChapterVIDPinchingArcSide) (boxes : Fin 26 → Rectangle) :
    List (DyadicOperation 40) :=
  (valueTrace side boxes).operations ++ (radialExpVelocity side boxes).operations ++
    (radialJet side boxes).operations

def angularOperations (side : ChapterVIDPinchingArcSide) (boxes : Fin 26 → Rectangle) :
    List (DyadicOperation 40) :=
  (valueTrace side boxes).operations ++ (angularPreJet side boxes).operations ++
    (angularExpVelocity side boxes).operations ++ (angularJet side boxes).operations

end ChapterVIDRadialTailCenteredTrace

end PoincareChapterVI
