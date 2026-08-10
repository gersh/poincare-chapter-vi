/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.ChapterVIDRadialTailTaylorSemantics

/-! # Kernel-checked centered affine table for the final radial tail -/

namespace PoincareChapterVI

open ChapterVILeanCompCertBatch
open ChapterVILeanCompCertAffineTrace

namespace ChapterVIDRadialTailCenteredCompiledGrid

open ChapterVIDRadialTailBaseCenteredAffineTrace
open ChapterVIDRadialTailCellInputTrace

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def inputs (side : ChapterVIDPinchingArcSide) (row : Fin 6) (radial : Fin 16)
    (angular : Fin (angularCells side row)) : Fin 56 →
      ChapterVILeanCompCertAffineTrace.Model 40 :=
  inputModels (pModel row radial) (tModel side row angular) remainderModel
    ChapterVIDRadialTailBaseConstantTrace.qdot
    ChapterVIDRadialTailBaseConstantTrace.cdot
    ChapterVIDRadialTailBaseConstantTrace.collisionModel
    ChapterVIDRadialTailBaseConstantTrace.collisionInv
    ChapterVIDRadialTailBaseConstantTrace.collisionSq
    ChapterVIDRadialTailBaseConstantTrace.collisionInvCube
    ChapterVIDRadialTailBaseConstantTrace.collisionInvFourth
    ChapterVIDRadialTailBaseConstantTrace.yBase
    ChapterVIDRadialTailBaseConstantTrace.zetaBase

def cellOperations (side : ChapterVIDPinchingArcSide) (row : Fin 6) (radial : Fin 16)
    (angular : Fin (angularCells side row)) : List (DyadicOperation 40) :=
  operations side (inputs side row radial angular)

def cellOutput (side : ChapterVIDPinchingArcSide) (row : Fin 6) (radial : Fin 16)
    (angular : Fin (angularCells side row)) :
      ChapterVISignedDyadicComplexRectangle 40 :=
  outputRange side (inputs side row radial angular)

def cellArgument (side : ChapterVIDPinchingArcSide) (row : Fin 6) (radial : Fin 16)
    (angular : Fin (angularCells side row)) :
      ChapterVISignedDyadicComplexRectangle 40 :=
  ((trace side (inputs side row radial angular)).outputs 21).range

end ChapterVIDRadialTailCenteredCompiledGrid
end PoincareChapterVI
