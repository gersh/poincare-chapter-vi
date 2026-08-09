/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.ChapterVIDConnectorFactorCrossing
import PoincareChapterVI.ChapterVILeanCompCertRelativeExponentialTrace

/-!
# Compiled dependency-preserving endpoint tables

This module turns a finite table of dependency-preserving derivative traces into the normalized
endpoint certificate consumed by the Chapter VI seam theorem.  Table generation is deliberately
untrusted.  Each cell must supply analytic enclosures for its primitive inputs, while every
rounded arithmetic operation and the terminal oriented sign are checked by one LeanCompCert
batch (or by hash-bound receipts for shards of that batch).

The important trust boundary is explicit: a receipt certifies only integer arithmetic.  The
fields named `*_contains` are the analytic bridges which still have to be proved in Lean for a
concrete Poincare campaign.
-/

noncomputable section

open Set
open scoped unitInterval

namespace PoincareChapterVI
namespace ChapterVIDConnectorFactorNormalizedDerivativeCompiled

open ChapterVILeanCompCertBatch
open ChapterVILeanCompCertAttestation
open ChapterVILeanCompCertDependencyPreservingFactorDerivativeTrace
open ChapterVILeanCompCertRelativeExponentialTrace
open ChapterVIDConnectorFactorCrossing
open ChapterVIDConnectorFactorMonotonicity
open LeanCompCert.Ports.SignedProductClaims

abbrev Interval (precision : ℕ) := ChapterVISignedDyadicInterval precision
abbrev Rectangle (precision : ℕ) := ChapterVISignedDyadicComplexRectangle precision

/-- Negate the trace output on the initial connector and leave it unchanged on the final
connector, so that one positive-real claim represents both required orientations. -/
def orientedOutput (side : ChapterVIDOuterArcSide) {precision : ℕ}
    (rectangle : Rectangle precision) : Rectangle precision :=
  match side with
  | .initial => rectangle.neg
  | .final => rectangle

def orientedValue (side : ChapterVIDOuterArcSide) (z : ℂ) : ℂ :=
  match side with
  | .initial => -z
  | .final => z

theorem orientedOutput_contains
    (side : ChapterVIDOuterArcSide) {precision : ℕ}
    {rectangle : Rectangle precision} {z : ℂ}
    (hz : rectangle.Contains z) :
    (orientedOutput side rectangle).Contains (orientedValue side z) := by
  cases side with
  | initial => exact ChapterVISignedDyadicComplexRectangle.neg_contains hz
  | final => exact hz

/-- One compiler cell.  Its trace is executable data.  Only the primitive transcendental and
algebraic enclosures are mathematical proof fields; all arithmetic after those inputs is checked
by the compiled batch. -/
structure Cell
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDAnchoredConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) (precision : ℕ) where
  parameter : Interval precision
  coordinate : Rectangle precision
  coordinateDelta : Rectangle precision
  zetaDelta : Rectangle precision
  direction : Rectangle precision
  collision : Rectangle precision
  collisionInv : Rectangle precision
  collisionSquare : Rectangle precision
  collisionInvCube : Rectangle precision
  collisionInvFourth : Rectangle precision
  yBase : Rectangle precision
  inverse10001 : Interval precision
  coefficient100 : Interval precision
  coefficient200 : Interval precision
  relativeExpTrace : ChapterVILeanCompCertRelativeExponentialTrace.Trace
    coordinate coordinateDelta collision collisionInvCube coefficient100
  trace : ChapterVILeanCompCertDependencyPreservingFactorDerivativeTrace.Trace
    coordinate coordinateDelta zetaDelta relativeExpTrace.output direction collision collisionInv
      collisionSquare collisionInvCube collisionInvFourth yBase inverse10001 coefficient200
  coordinate_contains : ∀ {t : ℝ}, parameter.Contains t → coordinate.Contains
    (AffineMap.lineMap
      (model.rootModel.connectorSource side (model.criticalValue 0))
      (model.rootModel.connectorTarget side (model.criticalValue 0)) (t : ℂ))
  coordinateDelta_contains : ∀ {t : ℝ}, parameter.Contains t → coordinateDelta.Contains
    (AffineMap.lineMap
      (model.rootModel.connectorSource side (model.criticalValue 0))
      (model.rootModel.connectorTarget side (model.criticalValue 0)) (t : ℂ) -
        chapterVIDCollisionLift)
  zetaDelta_contains : zetaDelta.Contains
    (model.connectorParameterRoot 0 / chapterVIDZRootBase - 1)
  direction_contains : direction.Contains
    (model.rootModel.connectorTarget side (model.criticalValue 0) -
      model.rootModel.connectorSource side (model.criticalValue 0))
  collision_contains : collision.Contains chapterVIDCollisionLift
  collisionInv_contains : collisionInv.Contains chapterVIDCollisionLift⁻¹
  collisionSquare_contains : collisionSquare.Contains (chapterVIDCollisionLift ^ 2)
  collisionInvCube_contains : collisionInvCube.Contains (chapterVIDCollisionLift⁻¹ ^ 3)
  collisionInvFourth_contains : collisionInvFourth.Contains (chapterVIDCollisionLift⁻¹ ^ 4)
  yBase_contains : yBase.Contains chapterVIDY
  inverse10001_contains : inverse10001.Contains (1 / 10001 : ℝ)
  coefficient100_contains : coefficient100.Contains (100 / 30003 : ℝ)
  coefficient200_contains : coefficient200.Contains (200 / 10001 : ℝ)

def Cell.operations
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDAnchoredConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide} {precision : ℕ}
    (cell : Cell model side precision) : List (DyadicOperation precision) :=
  cell.relativeExpTrace.operations ++ cell.trace.operations ++
    [.positiveLower (orientedOutput side cell.trace.output).real]

/-- A successful cell batch proves the sign of the exact dependency-preserving path derivative
at every real parameter enclosed by the cell. -/
theorem Cell.normalized_nonnegative_of_allSound
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDAnchoredConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide} {precision : ℕ}
    (cell : Cell model side precision)
    (hall : ∀ operation ∈ cell.operations, operation.Sound)
    {t : ℝ} (ht : cell.parameter.Contains t) (htUnit : t ∈ Icc (0 : ℝ) 1) :
    0 ≤ normalizedOrientedLineDerivative model side t := by
  let coordinateValue := AffineMap.lineMap
    (model.rootModel.connectorSource side (model.criticalValue 0))
    (model.rootModel.connectorTarget side (model.criticalValue 0)) (t : ℂ)
  have hExpTraceSound : ∀ operation ∈ cell.relativeExpTrace.operations, operation.Sound := by
    intro operation hoperation
    exact hall operation (by simp [Cell.operations, hoperation])
  have htraceSound : ∀ operation ∈ cell.trace.operations, operation.Sound := by
    intro operation hoperation
    exact hall operation (by simp [Cell.operations, hoperation])
  let tUnit : I := ⟨t, htUnit⟩
  have hcoordinateNe : coordinateValue ≠ 0 := by
    simpa [coordinateValue, ChapterVIDPrincipalConnectorModel.rectanglePoint,
      ChapterVIDPrincipalGlobalRootModel.connectorPoint, tUnit,
      AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, smul_eq_mul,
      mul_comm] using
      model.toChapterVIDPrincipalConnectorModel.rectanglePoint_ne_zero side (0, tUnit)
  have hExpDelta : cell.relativeExpTrace.output.Contains
      (Complex.exp
        (chapterVIDRootExponentialArgument coordinateValue -
          chapterVIDRootExponentialArgument chapterVIDCollisionLift) - 1) :=
    cell.relativeExpTrace.output_contains_of_allSound hExpTraceSound hcoordinateNe
      (cell.coordinate_contains ht) (cell.coordinateDelta_contains ht)
      cell.collision_contains cell.collisionInvCube_contains cell.coefficient100_contains
  have htrace : cell.trace.output.Contains
      (chapterVIDRootFactorDerivativeDependencyPreserving
        (model.connectorParameterRoot 0) coordinateValue *
          (model.rootModel.connectorTarget side (model.criticalValue 0) -
            model.rootModel.connectorSource side (model.criticalValue 0))) := by
    apply cell.trace.output_contains_of_allSound htraceSound
      (cell.coordinate_contains ht) (cell.coordinateDelta_contains ht)
      cell.zetaDelta_contains hExpDelta rfl
      cell.direction_contains cell.collision_contains cell.collisionInv_contains
      cell.collisionSquare_contains cell.collisionInvCube_contains
      cell.collisionInvFourth_contains cell.yBase_contains
      cell.inverse10001_contains cell.coefficient200_contains
  have horiented := orientedOutput_contains side htrace
  have hlower : 0 < (orientedOutput side cell.trace.output).real.lower := by
    have := hall (.positiveLower (orientedOutput side cell.trace.output).real)
      (by simp [Cell.operations])
    simpa [DyadicOperation.Sound] using this
  have hscaleDyadic : 0 < ChapterVISignedDyadicInterval.scale precision :=
    ChapterVISignedDyadicInterval.scale_pos precision
  have hlowerReal : 0 <
      ((orientedOutput side cell.trace.output).real.lower : ℝ) /
        ChapterVISignedDyadicInterval.scale precision :=
    div_pos (by exact_mod_cast hlower) hscaleDyadic
  have horientedReal : 0 <
      (orientedValue side
        (chapterVIDRootFactorDerivativeDependencyPreserving
          (model.connectorParameterRoot 0) coordinateValue *
            (model.rootModel.connectorTarget side (model.criticalValue 0) -
              model.rootModel.connectorSource side (model.criticalValue 0)))).re := by
    have horientedLower := horiented.1.1
    change ((orientedOutput side cell.trace.output).real.lower : ℝ) /
        ChapterVISignedDyadicInterval.scale precision ≤ _ at horientedLower
    exact hlowerReal.trans_le horientedLower
  rw [normalizedOrientedLineDerivative_eq_dependencyPreserving model side htUnit]
  unfold normalizedDependencyPreservingLineDerivative
  have hdenom := (realDerivativeScale_pos model side t).le
  cases side with
  | initial =>
      exact div_nonneg (by simpa [lineDependencyPreservingDerivativeReal,
        orientedValue, coordinateValue] using horientedReal.le) hdenom
  | final =>
      exact div_nonneg (by simpa [lineDependencyPreservingDerivativeReal,
        orientedValue, coordinateValue] using horientedReal.le) hdenom

/-- A finite cover of the endpoint collar by compiler cells. -/
structure Table
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDAnchoredConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) (precision : ℕ) where
  cells : List (Cell model side precision)
  covers : ∀ t : I, (t : ℝ) ∈ collarInterval side →
    ∃ cell ∈ cells, cell.parameter.Contains (t : ℝ)

def Table.operations
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDAnchoredConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide} {precision : ℕ}
    (table : Table model side precision) : List (DyadicOperation precision) :=
  table.cells.flatMap Cell.operations

theorem Table.toNormalizedRealDerivativeCertificate_of_allSound
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDAnchoredConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide} {precision : ℕ}
    (table : Table model side precision)
    (hall : ∀ operation ∈ table.operations, operation.Sound) :
    NormalizedRealDerivativeCertificate model side := by
  refine ⟨?_⟩
  intro t ht
  obtain ⟨cell, hcell, hparameter⟩ := table.covers t ht
  apply cell.normalized_nonnegative_of_allSound _ hparameter t.property
  intro operation hoperation
  apply hall operation
  rw [Table.operations, List.mem_flatMap]
  exact ⟨cell, hcell, hoperation⟩

/-- Package a concrete table as the generic compiled-data interface already consumed by the seam
assembly.  Admissibility is kept separate because it is normally emitted as small generated Lean
proofs after the table is sharded. -/
def Table.toCompiledData
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDAnchoredConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide} {precision : ℕ}
    (table : Table model side precision)
    (admissible : Admissible (batchClaims table.operations)) :
    CompiledNormalizedRealDerivativeData model side precision where
  operations := table.operations
  admissible := admissible
  sound := table.toNormalizedRealDerivativeCertificate_of_allSound

end ChapterVIDConnectorFactorNormalizedDerivativeCompiled
end PoincareChapterVI
