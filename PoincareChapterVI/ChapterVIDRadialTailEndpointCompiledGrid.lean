/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.ChapterVIDRadialTailEndpointTrace

/-! # Compiled endpoint and curvature tables for the radial-tail repair -/

namespace PoincareChapterVI
namespace ChapterVIDRadialTailEndpointCompiledGrid

open ChapterVIFieldExpression Expr
open ChapterVILeanCompCertAffineTrace
open ChapterVIDRadialTailBaseCenteredAffineTrace
open ChapterVIDRadialTailCellInputTrace
open ChapterVIDRadialTailEndpointTrace

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def directInputs (side : ChapterVIDPinchingArcSide)
    (angular : Fin (angularCells side 0)) : Fin 56 → Model 40 :=
  inputModels ChapterVIDRadialTailBaseConstantTrace.pBase
    (tModel side 0 angular) remainderModel
    ChapterVIDRadialTailBaseConstantTrace.qdot
    ChapterVIDRadialTailBaseConstantTrace.cdot
    ChapterVIDRadialTailBaseConstantTrace.collisionModel
    ChapterVIDRadialTailBaseConstantTrace.collisionInv
    ChapterVIDRadialTailBaseConstantTrace.collisionSq
    ChapterVIDRadialTailBaseConstantTrace.collisionInvCube
    ChapterVIDRadialTailBaseConstantTrace.collisionInvFourth
    ChapterVIDRadialTailBaseConstantTrace.yBase
    ChapterVIDRadialTailBaseConstantTrace.zetaBase

def directProductTrace (side : ChapterVIDPinchingArcSide)
    (angular : Fin (angularCells side 0)) :=
  let outputs := (ChapterVIDRadialTailBaseCenteredAffineTrace.trace side
    (directInputs side angular)).outputs
  proposeMul (outputs 51) (outputs 39)

def directOutput (side : ChapterVIDPinchingArcSide)
    (angular : Fin (angularCells side 0)) :
    ChapterVISignedDyadicComplexRectangle 40 :=
  (directProductTrace side angular).output.range

end ChapterVIDRadialTailEndpointCompiledGrid
end PoincareChapterVI
