/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.ChapterVIDConnectorFactorCrossing
import PoincareChapterVI.ChapterVIDConnectorInputBounds
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

/-- The static one-raw-unit box used for `localEndpoint - D`.  Its mathematical radius shrinks
with the fixed-point precision, but its compiled representation is always four tiny integers. -/
def rawUnitDeltaRectangle (precision : ℕ) : Rectangle precision :=
  ⟨⟨-1, 1⟩, ⟨-1, 1⟩⟩

theorem rawUnitDeltaRectangle_contains_of_norm_le
    {precision : ℕ} {z : ℂ}
    (hz : ‖z‖ ≤ 1 / ChapterVISignedDyadicInterval.scale precision) :
    (rawUnitDeltaRectangle precision).Contains z := by
  have hre := (Complex.abs_re_le_norm z).trans hz
  have him := (Complex.abs_im_le_norm z).trans hz
  rw [abs_le] at hre him
  simp only [one_div] at hre him
  simpa only [rawUnitDeltaRectangle,
    ChapterVISignedDyadicComplexRectangle.Contains,
    ChapterVISignedDyadicInterval.Contains,
    ChapterVISignedDyadicInterval.toRealInterval,
    ChapterVIRealInterval.Contains, Int.cast_neg, Int.cast_one, neg_div, one_div] using
      ⟨hre, him⟩

/-- At every fixed-point precision, the analytic selector can choose a connector whose two local
endpoint displacements fit the same static raw-unit box.  This is the direct handoff from the
inverse-function theorem to LeanCompCert input data. -/
theorem exists_model_with_rawUnitDeltaRectangle
    (massProduct : ℂ) (b d : ℤ) (precision : ℕ)
    (Lmax κmax : ℝ) (hLmaxPos : 0 < Lmax) (hκmaxPos : 0 < κmax) :
    ∃ model : ChapterVIDAnchoredConnectorModel massProduct b d,
      model.toChapterVIDPrincipalConnectorModel.rootModel.L ≤ Lmax ∧
      model.toChapterVIDPrincipalConnectorModel.κ ≤ κmax ∧
      (∀ side : ChapterVIDOuterArcSide,
        (rawUnitDeltaRectangle precision).Contains
          (model.toChapterVIDPrincipalConnectorModel.rootModel.localConnectorEndpoint side
              (model.toChapterVIDPrincipalConnectorModel.criticalValue 0) -
            chapterVIDCollisionLift)) ∧
      (rawUnitDeltaRectangle precision).Contains
        (model.toChapterVIDPrincipalConnectorModel.connectorParameterRoot 0 /
          chapterVIDZRootBase - 1) := by
  have hscalePos := ChapterVISignedDyadicInterval.scale_pos precision
  have hscaleOne : 1 ≤ ChapterVISignedDyadicInterval.scale precision := by
    change 1 ≤ (2 : ℝ) ^ precision
    exact one_le_pow₀ (by norm_num)
  let selectedLmax := min Lmax (1 / ChapterVISignedDyadicInterval.scale precision)
  have hselectedLmax : 0 < selectedLmax :=
    lt_min hLmaxPos (one_div_pos.mpr hscalePos)
  obtain ⟨model, hL, hκ, hlocal⟩ :=
    exists_chapterVIDAnchoredConnectorModel_with_local_endpoint_bound
      massProduct b d selectedLmax κmax
        (1 / ChapterVISignedDyadicInterval.scale precision)
      hselectedLmax hκmaxPos (one_div_pos.mpr hscalePos)
  have hLRequested : model.toChapterVIDPrincipalConnectorModel.rootModel.L ≤ Lmax :=
    hL.trans (min_le_left _ _)
  have hLRaw : model.toChapterVIDPrincipalConnectorModel.rootModel.L ≤
      1 / ChapterVISignedDyadicInterval.scale precision :=
    hL.trans (min_le_right _ _)
  have hRawNonneg : 0 ≤ 1 / ChapterVISignedDyadicInterval.scale precision :=
    (one_div_pos.mpr hscalePos).le
  have hRawLeOne : 1 / ChapterVISignedDyadicInterval.scale precision ≤ 1 := by
    exact (div_le_one hscalePos).mpr hscaleOne
  have hLSquare : model.toChapterVIDPrincipalConnectorModel.rootModel.L ^ 2 ≤
      1 / ChapterVISignedDyadicInterval.scale precision := by
    calc
      model.toChapterVIDPrincipalConnectorModel.rootModel.L ^ 2 ≤
          (1 / ChapterVISignedDyadicInterval.scale precision) ^ 2 :=
        (sq_le_sq₀ model.toChapterVIDPrincipalConnectorModel.rootModel.L_pos.le
          hRawNonneg).mpr hLRaw
      _ ≤ 1 / ChapterVISignedDyadicInterval.scale precision := by
        nlinarith
  exact ⟨model, hLRequested, hκ,
    fun side => rawUnitDeltaRectangle_contains_of_norm_le (hlocal side),
    rawUnitDeltaRectangle_contains_of_norm_le
      (model.parameterRootRelativeDelta_norm_le_length_sq.trans hLSquare)⟩

/-- Precision-20 enclosure of the vector from the local inverse-Morse endpoint to the certified
outer endpoint.  Both source rectangles were already proved against the terminal radial grid. -/
def referenceLocalToOuterRectangle (side : ChapterVIDOuterArcSide) : Rectangle 20 :=
  (ChapterVIDConnectorInputBounds.terminalOuterRectangle side).sub
    ChapterVIDConnectorInputBounds.localEndpointRectangle

theorem referenceLocalToOuterRectangle_contains
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDAnchoredConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) :
    (referenceLocalToOuterRectangle side).Contains
      (model.rootModel.outerConnectorEndpoint side (model.criticalValue 0) -
        model.rootModel.localConnectorEndpoint side (model.criticalValue 0)) := by
  apply ChapterVISignedDyadicComplexRectangle.sub_contains
  · exact ChapterVIDConnectorInputBounds.terminalOuterRectangle_contains
      model.toChapterVIDPrincipalConnectorModel side 0
  · exact ChapterVIDConnectorInputBounds.localEndpointRectangle_contains
      model.toChapterVIDPrincipalConnectorModel.rootModel side
      (model.toChapterVIDPrincipalConnectorModel.criticalValue 0)
      (model.toChapterVIDPrincipalConnectorModel.criticalValue_mem_rootModel 0)

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

/-- Exact fixed-point interval for distance from the local endpoint. -/
def endpointDistanceInterval (side : ChapterVIDOuterArcSide) {precision : ℕ}
    (parameter : Interval precision) : Interval precision :=
  match side with
  | .initial => (ChapterVISignedDyadicInterval.pointInt precision 1).sub parameter
  | .final => parameter

theorem endpointDistanceInterval_contains
    (side : ChapterVIDOuterArcSide) {precision : ℕ}
    {parameter : Interval precision} {t : ℝ}
    (ht : parameter.Contains t) :
    (endpointDistanceInterval side parameter).Contains (localEndpointDistance side t) := by
  cases side with
  | initial =>
      apply ChapterVISignedDyadicInterval.sub_contains _ ht
      simpa using ChapterVISignedDyadicInterval.pointInt_contains precision 1
  | final => exact ht

/-- Source of the oriented affine connector when its two geometric endpoints are supplied
directly.  Naming this operation keeps later dependent trace statements definitionally stable. -/
def connectorSourceFromLocalOuter
    (side : ChapterVIDOuterArcSide) (localPoint outer : ℂ) : ℂ :=
  match side with
  | .initial => outer
  | .final => localPoint

/-- Target of the oriented affine connector when its two geometric endpoints are supplied
directly. -/
def connectorTargetFromLocalOuter
    (side : ChapterVIDOuterArcSide) (localPoint outer : ℂ) : ℂ :=
  match side with
  | .initial => localPoint
  | .final => outer

/-- Algebraic identity which retains both endpoint-small quantities before interval evaluation. -/
theorem lineMap_sub_collision_eq_localDelta_add_distance_mul
    (side : ChapterVIDOuterArcSide) (localPoint outer collision : ℂ) (t : ℝ) :
    AffineMap.lineMap
        (connectorSourceFromLocalOuter side localPoint outer)
        (connectorTargetFromLocalOuter side localPoint outer) (t : ℂ) - collision =
      (localPoint - collision) +
        (localEndpointDistance side t : ℂ) * (outer - localPoint) := by
  cases side <;>
    simp only [connectorSourceFromLocalOuter, connectorTargetFromLocalOuter,
      localEndpointDistance, AffineMap.lineMap_apply, vsub_eq_sub,
      vadd_eq_add, smul_eq_mul] <;> push_cast <;> ring

/-- One rounded multiplication constructs `u-D` from the local endpoint displacement and the
distance-scaled local-to-outer direction. -/
structure CoordinateDeltaTrace (side : ChapterVIDOuterArcSide) {precision : ℕ}
    (parameter : Interval precision) (localDelta localToOuter : Rectangle precision) where
  scaled : ChapterVISignedDyadicComplexRectangle.RealMulTrace
    (endpointDistanceInterval side parameter) localToOuter

def CoordinateDeltaTrace.operations
    {side : ChapterVIDOuterArcSide} {precision : ℕ}
    {parameter : Interval precision} {localDelta localToOuter : Rectangle precision}
    (trace : CoordinateDeltaTrace side parameter localDelta localToOuter) :
    List (DyadicOperation precision) :=
  trace.scaled.operations

def CoordinateDeltaTrace.output
    {side : ChapterVIDOuterArcSide} {precision : ℕ}
    {parameter : Interval precision} {localDelta localToOuter : Rectangle precision}
    (trace : CoordinateDeltaTrace side parameter localDelta localToOuter) : Rectangle precision :=
  localDelta.add trace.scaled.output

def coordinateDeltaTrace
    (side : ChapterVIDOuterArcSide) {precision : ℕ}
    (parameter : Interval precision) (localDelta localToOuter : Rectangle precision) :
    CoordinateDeltaTrace side parameter localDelta localToOuter :=
  ⟨ChapterVILeanCompCertProposals.realMulTrace
    (endpointDistanceInterval side parameter) localToOuter⟩

theorem CoordinateDeltaTrace.output_contains_of_allSound
    {side : ChapterVIDOuterArcSide} {precision : ℕ}
    {parameter : Interval precision} {localDelta localToOuter : Rectangle precision}
    (trace : CoordinateDeltaTrace side parameter localDelta localToOuter)
    (hall : ∀ operation ∈ trace.operations, operation.Sound)
    {localPoint outer collision : ℂ} {t : ℝ}
    (ht : parameter.Contains t)
    (hLocalDelta : localDelta.Contains (localPoint - collision))
    (hLocalToOuter : localToOuter.Contains (outer - localPoint)) :
    trace.output.Contains
      (AffineMap.lineMap
          (connectorSourceFromLocalOuter side localPoint outer)
          (connectorTargetFromLocalOuter side localPoint outer) (t : ℂ) - collision) := by
  have hscaled := trace.scaled.output_contains_of_allSound hall
    (endpointDistanceInterval_contains side ht) hLocalToOuter
  have hsum := ChapterVISignedDyadicComplexRectangle.add_contains hLocalDelta hscaled
  rw [← lineMap_sub_collision_eq_localDelta_add_distance_mul] at hsum
  exact hsum

/-- The affine path direction is the local-to-outer vector, with the initial side reversed. -/
def pathDirectionRectangle (side : ChapterVIDOuterArcSide) {precision : ℕ}
    (localToOuter : Rectangle precision) : Rectangle precision :=
  match side with
  | .initial => localToOuter.neg
  | .final => localToOuter

theorem pathDirectionRectangle_contains
    (side : ChapterVIDOuterArcSide) {precision : ℕ}
    {localToOuter : Rectangle precision} {localPoint outer : ℂ}
    (hLocalToOuter : localToOuter.Contains (outer - localPoint)) :
    (pathDirectionRectangle side localToOuter).Contains
      (connectorTargetFromLocalOuter side localPoint outer -
        connectorSourceFromLocalOuter side localPoint outer) := by
  cases side with
  | initial =>
      simpa only [pathDirectionRectangle, connectorSourceFromLocalOuter,
        connectorTargetFromLocalOuter, neg_sub] using
        ChapterVISignedDyadicComplexRectangle.neg_contains hLocalToOuter
  | final => exact hLocalToOuter

theorem connectorSourceFromLocalOuter_eq
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDAnchoredConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) :
    connectorSourceFromLocalOuter side
        (model.rootModel.localConnectorEndpoint side (model.criticalValue 0))
        (model.rootModel.outerConnectorEndpoint side (model.criticalValue 0)) =
      model.rootModel.connectorSource side (model.criticalValue 0) := by
  cases side <;> rfl

theorem connectorTargetFromLocalOuter_eq
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDAnchoredConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) :
    connectorTargetFromLocalOuter side
        (model.rootModel.localConnectorEndpoint side (model.criticalValue 0))
        (model.rootModel.outerConnectorEndpoint side (model.criticalValue 0)) =
      model.rootModel.connectorTarget side (model.criticalValue 0) := by
  cases side <;> rfl

/-- One compiler cell.  Its trace is executable data.  Only the primitive transcendental and
algebraic enclosures are mathematical proof fields; all arithmetic after those inputs is checked
by the compiled batch. -/
structure Cell
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDAnchoredConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) (precision : ℕ) where
  parameter : Interval precision
  /-- Primitive scale-aware enclosure of the inverse-Morse endpoint minus `D`. -/
  localDelta : Rectangle precision
  /-- Primitive enclosure of the vector from the local endpoint to the outer endpoint. -/
  localToOuter : Rectangle precision
  coordinateDeltaTrace : CoordinateDeltaTrace side parameter localDelta localToOuter
  zetaDelta : Rectangle precision
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
    (collision.add coordinateDeltaTrace.output) coordinateDeltaTrace.output collision
      collisionInvCube coefficient100
  trace : ChapterVILeanCompCertDependencyPreservingFactorDerivativeTrace.Trace
    (collision.add coordinateDeltaTrace.output) coordinateDeltaTrace.output zetaDelta
      relativeExpTrace.output (pathDirectionRectangle side localToOuter) collision collisionInv
      collisionSquare collisionInvCube collisionInvFourth yBase inverse10001 coefficient200
  localDelta_contains : localDelta.Contains
    (model.rootModel.localConnectorEndpoint side (model.criticalValue 0) -
      chapterVIDCollisionLift)
  localToOuter_contains : localToOuter.Contains
    (model.rootModel.outerConnectorEndpoint side (model.criticalValue 0) -
      model.rootModel.localConnectorEndpoint side (model.criticalValue 0))
  zetaDelta_contains : zetaDelta.Contains
    (model.connectorParameterRoot 0 / chapterVIDZRootBase - 1)
  collision_contains : collision.Contains chapterVIDCollisionLift
  collisionInv_contains : collisionInv.Contains chapterVIDCollisionLift⁻¹
  collisionSquare_contains : collisionSquare.Contains (chapterVIDCollisionLift ^ 2)
  collisionInvCube_contains : collisionInvCube.Contains (chapterVIDCollisionLift⁻¹ ^ 3)
  collisionInvFourth_contains : collisionInvFourth.Contains (chapterVIDCollisionLift⁻¹ ^ 4)
  yBase_contains : yBase.Contains chapterVIDY
  inverse10001_contains : inverse10001.Contains (1 / 10001 : ℝ)
  coefficient100_contains : coefficient100.Contains (100 / 30003 : ℝ)
  coefficient200_contains : coefficient200.Contains (200 / 10001 : ℝ)

/-- Deterministic untrusted compiler for a cell from primitive analytic rectangles.  Callers do
not construct any rounded intermediate: the two dependency-preserving traces are proposed here,
and `Cell.operations` exposes every multiplication, reciprocal, and terminal sign for checking. -/
def Cell.propose
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDAnchoredConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) (precision : ℕ)
    (parameter : Interval precision)
    (localDelta localToOuter zetaDelta collision collisionInv collisionSquare
      collisionInvCube collisionInvFourth yBase : Rectangle precision)
    (inverse10001 coefficient100 coefficient200 : Interval precision)
    (localDelta_contains : localDelta.Contains
      (model.rootModel.localConnectorEndpoint side (model.criticalValue 0) -
        chapterVIDCollisionLift))
    (localToOuter_contains : localToOuter.Contains
      (model.rootModel.outerConnectorEndpoint side (model.criticalValue 0) -
        model.rootModel.localConnectorEndpoint side (model.criticalValue 0)))
    (zetaDelta_contains : zetaDelta.Contains
      (model.connectorParameterRoot 0 / chapterVIDZRootBase - 1))
    (collision_contains : collision.Contains chapterVIDCollisionLift)
    (collisionInv_contains : collisionInv.Contains chapterVIDCollisionLift⁻¹)
    (collisionSquare_contains : collisionSquare.Contains (chapterVIDCollisionLift ^ 2))
    (collisionInvCube_contains : collisionInvCube.Contains (chapterVIDCollisionLift⁻¹ ^ 3))
    (collisionInvFourth_contains : collisionInvFourth.Contains (chapterVIDCollisionLift⁻¹ ^ 4))
    (yBase_contains : yBase.Contains chapterVIDY)
    (inverse10001_contains : inverse10001.Contains (1 / 10001 : ℝ))
    (coefficient100_contains : coefficient100.Contains (100 / 30003 : ℝ))
    (coefficient200_contains : coefficient200.Contains (200 / 10001 : ℝ)) :
    Cell model side precision :=
  let coordinateDeltaTrace :=
    ChapterVIDConnectorFactorNormalizedDerivativeCompiled.coordinateDeltaTrace
      side parameter localDelta localToOuter
  let coordinate := collision.add coordinateDeltaTrace.output
  let direction := pathDirectionRectangle side localToOuter
  let relativeExpTrace :=
    ChapterVILeanCompCertRelativeExponentialTrace.relativeExpTrace
      coordinate coordinateDeltaTrace.output collision collisionInvCube coefficient100
  let trace :=
    ChapterVILeanCompCertDependencyPreservingFactorDerivativeTrace.dependencyPreservingTrace
      coordinate coordinateDeltaTrace.output zetaDelta relativeExpTrace.output direction
      collision collisionInv collisionSquare collisionInvCube collisionInvFourth yBase
      inverse10001 coefficient200
  { parameter := parameter
    localDelta := localDelta
    localToOuter := localToOuter
    coordinateDeltaTrace := coordinateDeltaTrace
    zetaDelta := zetaDelta
    collision := collision
    collisionInv := collisionInv
    collisionSquare := collisionSquare
    collisionInvCube := collisionInvCube
    collisionInvFourth := collisionInvFourth
    yBase := yBase
    inverse10001 := inverse10001
    coefficient100 := coefficient100
    coefficient200 := coefficient200
    relativeExpTrace := relativeExpTrace
    trace := trace
    localDelta_contains := localDelta_contains
    localToOuter_contains := localToOuter_contains
    zetaDelta_contains := zetaDelta_contains
    collision_contains := collision_contains
    collisionInv_contains := collisionInv_contains
    collisionSquare_contains := collisionSquare_contains
    collisionInvCube_contains := collisionInvCube_contains
    collisionInvFourth_contains := collisionInvFourth_contains
    yBase_contains := yBase_contains
    inverse10001_contains := inverse10001_contains
    coefficient100_contains := coefficient100_contains
    coefficient200_contains := coefficient200_contains }

def Cell.operations
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDAnchoredConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide} {precision : ℕ}
    (cell : Cell model side precision) : List (DyadicOperation precision) :=
  cell.coordinateDeltaTrace.operations ++ cell.relativeExpTrace.operations ++
    cell.trace.operations ++
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
  have hcoordinateDeltaTraceSound :
      ∀ operation ∈ cell.coordinateDeltaTrace.operations, operation.Sound := by
    intro operation hoperation
    exact hall operation (by simp [Cell.operations, hoperation])
  have hExpTraceSound : ∀ operation ∈ cell.relativeExpTrace.operations, operation.Sound := by
    intro operation hoperation
    exact hall operation (by simp [Cell.operations, hoperation])
  have htraceSound : ∀ operation ∈ cell.trace.operations, operation.Sound := by
    intro operation hoperation
    exact hall operation (by simp [Cell.operations, hoperation])
  have hcoordinateDelta : cell.coordinateDeltaTrace.output.Contains
      (coordinateValue - chapterVIDCollisionLift) := by
    have h := cell.coordinateDeltaTrace.output_contains_of_allSound
      hcoordinateDeltaTraceSound ht cell.localDelta_contains cell.localToOuter_contains
    rw [connectorSourceFromLocalOuter_eq model side,
      connectorTargetFromLocalOuter_eq model side] at h
    exact h
  have hcoordinate :
      (cell.collision.add cell.coordinateDeltaTrace.output).Contains coordinateValue := by
    have h := ChapterVISignedDyadicComplexRectangle.add_contains
      cell.collision_contains hcoordinateDelta
    convert h using 1
    ring
  have hdirection : (pathDirectionRectangle side cell.localToOuter).Contains
      (model.rootModel.connectorTarget side (model.criticalValue 0) -
        model.rootModel.connectorSource side (model.criticalValue 0)) := by
    have h := pathDirectionRectangle_contains side cell.localToOuter_contains
    rw [connectorSourceFromLocalOuter_eq model side,
      connectorTargetFromLocalOuter_eq model side] at h
    exact h
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
      hcoordinate hcoordinateDelta
      cell.collision_contains cell.collisionInvCube_contains cell.coefficient100_contains
  have htrace : cell.trace.output.Contains
      (chapterVIDRootFactorDerivativeDependencyPreserving
        (model.connectorParameterRoot 0) coordinateValue *
          (model.rootModel.connectorTarget side (model.criticalValue 0) -
            model.rootModel.connectorSource side (model.criticalValue 0))) := by
    apply cell.trace.output_contains_of_allSound htraceSound
      hcoordinate hcoordinateDelta
      cell.zetaDelta_contains hExpDelta rfl
      hdirection cell.collision_contains cell.collisionInv_contains
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
