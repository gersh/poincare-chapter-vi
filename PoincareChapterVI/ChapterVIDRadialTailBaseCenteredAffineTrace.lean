/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.ChapterVIDRadialTailBaseCenteredProgram
import PoincareChapterVI.ChapterVILeanCompCertAffineTrace

/-! # Affine traces for the collision-base-centred radial-tail program -/

namespace PoincareChapterVI

open ChapterVILeanCompCertBatch

namespace ChapterVIDRadialTailBaseCenteredAffineTrace

open ChapterVIDRadialTailBaseCenteredProgram
open ChapterVILeanCompCertAffineTrace

abbrev Rectangle := ChapterVISignedDyadicComplexRectangle 40
abbrev Model := ChapterVILeanCompCertAffineTrace.Model 40

def zeroRectangle : Rectangle :=
  ChapterVISignedDyadicComplexRectangle.pointInt 40 0

def zero : Model := ChapterVILeanCompCertAffineTrace.zero 40

def imaginaryUnit : Model :=
  { center := ⟨⟨0, 0⟩, ⟨1099511627776, 1099511627776⟩⟩
    radial := zeroRectangle
    angular := zeroRectangle
    error := zeroRectangle }

def constant (x : Rectangle) : Model :=
  { center := x, radial := zeroRectangle, angular := zeroRectangle, error := zeroRectangle }

def inputModels (p t remainder qdot cdot collision collisionInv collisionSq
    collisionInvCube collisionInvFourth yBase zetaBase : Model) : Fin 56 → Model
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

def trace (side : ChapterVIDPinchingArcSide) (inputs : Fin 56 → Model) :=
  ChapterVILeanCompCertAffineTrace.proposeProgram inputs (program side)

def output (side : ChapterVIDPinchingArcSide) (inputs : Fin 56 → Model) : Model :=
  (trace side inputs).outputs 52

def outputRange (side : ChapterVIDPinchingArcSide) (inputs : Fin 56 → Model) : Rectangle :=
  (output side inputs).range

def operations (side : ChapterVIDPinchingArcSide) (inputs : Fin 56 → Model) :
    List (DyadicOperation 40) :=
  (trace side inputs).operations

end ChapterVIDRadialTailBaseCenteredAffineTrace

end PoincareChapterVI
