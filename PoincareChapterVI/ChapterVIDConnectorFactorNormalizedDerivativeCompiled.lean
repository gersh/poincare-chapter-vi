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

/-- A deliberately modest fixed box for the real algebraic constant `Y(D)`.  The sharp root
isolation is unnecessary here; Poincare's original `[-.027,-.026]` isolating interval suffices. -/
def referenceYBaseRectangle : Rectangle 20 :=
  ⟨⟨-28312, -25000⟩, ⟨0, 0⟩⟩

theorem referenceYBaseRectangle_contains :
    referenceYBaseRectangle.Contains chapterVIDY := by
  let x := chapterVIDRoot
  have hxLower : (-27 / 1000 : ℝ) ≤ x := chapterVIDRoot_mem.1
  have hxUpper : x ≤ (-26 / 1000 : ℝ) := chapterVIDRoot_mem.2
  have hden : 2 * (1 + (1 / 100 : ℝ) ^ 2) * x < 0 := by
    norm_num
    linarith
  have hYLower : (-27 / 1000 : ℝ) ≤
      (x - 1 / 100) ^ 2 / (2 * (1 + (1 / 100 : ℝ) ^ 2) * x) := by
    rw [le_div_iff_of_neg hden]
    nlinarith [sq_nonneg (x - 1 / 100)]
  have hYUpper :
      (x - 1 / 100) ^ 2 / (2 * (1 + (1 / 100 : ℝ) ^ 2) * x) ≤
        (-24 / 1000 : ℝ) := by
    rw [div_le_iff_of_neg hden]
    nlinarith [sq_nonneg (x - 1 / 100)]
  have hYOfReal : chapterVIDY =
      ((x - 1 / 100) ^ 2 / (2 * (1 + (1 / 100 : ℝ) ^ 2) * x) : ℝ) := by
    dsimp only [chapterVIDY, chapterVIDX, x]
    push_cast
    norm_num
  have hYReal : chapterVIDY.re =
      (x - 1 / 100) ^ 2 / (2 * (1 + (1 / 100 : ℝ) ^ 2) * x) := by
    have h := congrArg Complex.re hYOfReal
    simpa only [Complex.ofReal_re] using h
  have hYImag : chapterVIDY.im = 0 := by
    have h := congrArg Complex.im hYOfReal
    simpa only [Complex.ofReal_im] using h
  simp only [referenceYBaseRectangle,
    ChapterVISignedDyadicComplexRectangle.Contains,
    ChapterVISignedDyadicInterval.Contains,
    ChapterVISignedDyadicInterval.toRealInterval, ChapterVIRealInterval.Contains,
    ChapterVISignedDyadicInterval.scale]
  rw [hYReal, hYImag]
  constructor
  · constructor
    · norm_num at ⊢ hYLower
      linarith
    · norm_num at ⊢ hYUpper
      linarith
  · norm_num

def referenceCoefficient200 : Interval 20 := ⟨20969, 20970⟩

theorem referenceCoefficient200_contains :
    referenceCoefficient200.Contains (200 / 10001 : ℝ) := by
  norm_num [referenceCoefficient200, ChapterVISignedDyadicInterval.Contains,
    ChapterVISignedDyadicInterval.toRealInterval, ChapterVIRealInterval.Contains,
    ChapterVISignedDyadicInterval.scale]

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

/-- Checked reusable powers of the collision lift.  A campaign supplies only one rectangle for
`D`; reciprocal and power rectangles are generated and independently checked. -/
structure CollisionConstantsTrace {precision : ℕ} (collision : Rectangle precision) where
  collisionInv : ChapterVISignedDyadicComplexRectangle.InvTrace collision
  collisionSquare : ChapterVISignedDyadicComplexRectangle.MulTrace collision collision
  collisionInvCube : ChapterVISignedDyadicComplexRectangle.CubeTrace collisionInv.output
  collisionInvFourth : ChapterVISignedDyadicComplexRectangle.MulTrace
    collisionInvCube.output collisionInv.output

def CollisionConstantsTrace.operations
    {precision : ℕ} {collision : Rectangle precision}
    (trace : CollisionConstantsTrace collision) : List (DyadicOperation precision) :=
  trace.collisionInv.operations ++ trace.collisionSquare.operations ++
    trace.collisionInvCube.operations ++ trace.collisionInvFourth.operations

def collisionConstantsTrace {precision : ℕ} (collision : Rectangle precision) :
    CollisionConstantsTrace collision :=
  let collisionInv := ChapterVILeanCompCertProposals.invTrace collision
  let collisionSquare := ChapterVILeanCompCertProposals.mulTrace collision collision
  let collisionInvCube := ChapterVILeanCompCertProposals.cubeTrace collisionInv.output
  let collisionInvFourth := ChapterVILeanCompCertProposals.mulTrace
    collisionInvCube.output collisionInv.output
  ⟨collisionInv, collisionSquare, collisionInvCube, collisionInvFourth⟩

theorem CollisionConstantsTrace.outputs_contain_of_allSound
    {precision : ℕ} {collision : Rectangle precision}
    (trace : CollisionConstantsTrace collision)
    (hall : ∀ operation ∈ trace.operations, operation.Sound)
    (hcollision : collision.Contains chapterVIDCollisionLift) :
    trace.collisionInv.output.Contains chapterVIDCollisionLift⁻¹ ∧
      trace.collisionSquare.output.Contains (chapterVIDCollisionLift ^ 2) ∧
      trace.collisionInvCube.output.Contains (chapterVIDCollisionLift⁻¹ ^ 3) ∧
      trace.collisionInvFourth.output.Contains (chapterVIDCollisionLift⁻¹ ^ 4) := by
  have hinvSound : ∀ operation ∈ trace.collisionInv.operations, operation.Sound := by
    intro operation hoperation
    exact hall operation (by simp [CollisionConstantsTrace.operations, hoperation])
  have hsquareSound : ∀ operation ∈ trace.collisionSquare.operations, operation.Sound := by
    intro operation hoperation
    exact hall operation (by simp [CollisionConstantsTrace.operations, hoperation])
  have hinvCubeSound : ∀ operation ∈ trace.collisionInvCube.operations, operation.Sound := by
    intro operation hoperation
    exact hall operation (by simp [CollisionConstantsTrace.operations, hoperation])
  have hinvFourthSound : ∀ operation ∈ trace.collisionInvFourth.operations, operation.Sound := by
    intro operation hoperation
    exact hall operation (by simp [CollisionConstantsTrace.operations, hoperation])
  have hinv := trace.collisionInv.output_contains_inv_of_allSound hinvSound hcollision
  have hsquare := trace.collisionSquare.output_contains_mul_of_allSound
    hsquareSound hcollision hcollision
  have hsquare' : trace.collisionSquare.output.Contains (chapterVIDCollisionLift ^ 2) := by
    simpa [pow_two] using hsquare
  have hinvCube := trace.collisionInvCube.output_contains_cube_of_allSound hinvCubeSound hinv
  have hinvFourth := trace.collisionInvFourth.output_contains_mul_of_allSound
    hinvFourthSound hinvCube hinv
  exact ⟨hinv, hsquare', hinvCube, by simpa [pow_succ] using hinvFourth⟩

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
  collisionConstantsTrace : CollisionConstantsTrace collision
  yBase : Rectangle precision
  inverse10001 : Interval precision
  coefficient100 : Interval precision
  coefficient200 : Interval precision
  relativeExpTrace : ChapterVILeanCompCertRelativeExponentialTrace.Trace
    (collision.add coordinateDeltaTrace.output) coordinateDeltaTrace.output collision
      collisionConstantsTrace.collisionInvCube.output coefficient100
  trace : ChapterVILeanCompCertDependencyPreservingFactorDerivativeTrace.Trace
    (collision.add coordinateDeltaTrace.output) coordinateDeltaTrace.output zetaDelta
      relativeExpTrace.output (pathDirectionRectangle side localToOuter) collision
      collisionConstantsTrace.collisionInv.output
      collisionConstantsTrace.collisionSquare.output
      collisionConstantsTrace.collisionInvCube.output
      collisionConstantsTrace.collisionInvFourth.output yBase inverse10001 coefficient200
  localDelta_contains : localDelta.Contains
    (model.rootModel.localConnectorEndpoint side (model.criticalValue 0) -
      chapterVIDCollisionLift)
  localToOuter_contains : localToOuter.Contains
    (model.rootModel.outerConnectorEndpoint side (model.criticalValue 0) -
      model.rootModel.localConnectorEndpoint side (model.criticalValue 0))
  zetaDelta_contains : zetaDelta.Contains
    (model.connectorParameterRoot 0 / chapterVIDZRootBase - 1)
  collision_contains : collision.Contains chapterVIDCollisionLift
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
    (localDelta localToOuter zetaDelta collision yBase : Rectangle precision)
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
  let collisionConstantsTrace :=
    ChapterVIDConnectorFactorNormalizedDerivativeCompiled.collisionConstantsTrace collision
  let relativeExpTrace :=
    ChapterVILeanCompCertRelativeExponentialTrace.relativeExpTrace
      coordinate coordinateDeltaTrace.output collision
        collisionConstantsTrace.collisionInvCube.output coefficient100
  let trace :=
    ChapterVILeanCompCertDependencyPreservingFactorDerivativeTrace.dependencyPreservingTrace
      coordinate coordinateDeltaTrace.output zetaDelta relativeExpTrace.output direction
      collision collisionConstantsTrace.collisionInv.output
      collisionConstantsTrace.collisionSquare.output
      collisionConstantsTrace.collisionInvCube.output
      collisionConstantsTrace.collisionInvFourth.output yBase inverse10001 coefficient200
  { parameter := parameter
    localDelta := localDelta
    localToOuter := localToOuter
    coordinateDeltaTrace := coordinateDeltaTrace
    zetaDelta := zetaDelta
    collision := collision
    collisionConstantsTrace := collisionConstantsTrace
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
    yBase_contains := yBase_contains
    inverse10001_contains := inverse10001_contains
    coefficient100_contains := coefficient100_contains
    coefficient200_contains := coefficient200_contains }

/-- Fully populated precision-20 cell proposal.  After the model selector supplies the two
raw-unit facts, the only varying untrusted datum is the real parameter interval. -/
def referenceCellProposal
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDAnchoredConnectorModel massProduct b d)
    (localDelta_contains : ∀ side : ChapterVIDOuterArcSide,
      (rawUnitDeltaRectangle 20).Contains
        (model.rootModel.localConnectorEndpoint side (model.criticalValue 0) -
          chapterVIDCollisionLift))
    (zetaDelta_contains : (rawUnitDeltaRectangle 20).Contains
      (model.connectorParameterRoot 0 / chapterVIDZRootBase - 1))
    (side : ChapterVIDOuterArcSide) (parameter : Interval 20) :
    Cell model side 20 :=
  Cell.propose model side 20 parameter
    (rawUnitDeltaRectangle 20) (referenceLocalToOuterRectangle side)
    (rawUnitDeltaRectangle 20) ChapterVIDConnectorInputBounds.localEndpointRectangle
    referenceYBaseRectangle
    ChapterVIDOuterArcPolarCompiledGrid.inverse10001
    ChapterVIDOuterArcPolarCompiledGrid.exponentialCoefficient referenceCoefficient200
    (localDelta_contains side) (referenceLocalToOuterRectangle_contains model side)
    zetaDelta_contains ChapterVIDConnectorInputBounds.localEndpointRectangle_contains_collisionLift
    referenceYBaseRectangle_contains
    ChapterVIDOuterArcPolarCompiledGrid.inverse10001_contains
    ChapterVIDOuterArcPolarCompiledGrid.exponentialCoefficient_contains
    referenceCoefficient200_contains

/-- Analytic model bundled with exactly the two noncomputable facts needed by the otherwise
executable reference-cell generator. -/
structure ReferenceCampaignModel (massProduct : ℂ) (b d : ℤ) where
  model : ChapterVIDAnchoredConnectorModel massProduct b d
  localDelta_contains : ∀ side : ChapterVIDOuterArcSide,
    (rawUnitDeltaRectangle 20).Contains
      (model.rootModel.localConnectorEndpoint side (model.criticalValue 0) -
        chapterVIDCollisionLift)
  zetaDelta_contains : (rawUnitDeltaRectangle 20).Contains
    (model.connectorParameterRoot 0 / chapterVIDZRootBase - 1)

theorem exists_referenceCampaignModel (massProduct : ℂ) (b d : ℤ) :
    Nonempty (ReferenceCampaignModel massProduct b d) := by
  obtain ⟨model, _, _, hlocal, hzeta⟩ :=
    exists_model_with_rawUnitDeltaRectangle massProduct b d 20 1 1
      (by norm_num) (by norm_num)
  exact ⟨⟨model, hlocal, hzeta⟩⟩

def ReferenceCampaignModel.cellProposal
    {massProduct : ℂ} {b d : ℤ}
    (campaign : ReferenceCampaignModel massProduct b d)
    (side : ChapterVIDOuterArcSide) (parameter : Interval 20) :
    Cell campaign.model side 20 :=
  referenceCellProposal campaign.model campaign.localDelta_contains
    campaign.zetaDelta_contains side parameter

def Cell.operations
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDAnchoredConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide} {precision : ℕ}
    (cell : Cell model side precision) : List (DyadicOperation precision) :=
  cell.coordinateDeltaTrace.operations ++ cell.collisionConstantsTrace.operations ++
    cell.relativeExpTrace.operations ++ cell.trace.operations ++
    [.positiveLower (orientedOutput side cell.trace.output).real]

/-- Pure executable form of the reference proposal, independent of the noncomputable analytic
model and its erased proof fields. -/
def referenceOperations (side : ChapterVIDOuterArcSide) (parameter : Interval 20) :
    List (DyadicOperation 20) :=
  let localDelta := rawUnitDeltaRectangle 20
  let localToOuter := referenceLocalToOuterRectangle side
  let zetaDelta := rawUnitDeltaRectangle 20
  let collision := ChapterVIDConnectorInputBounds.localEndpointRectangle
  let coordinateDeltaTrace :=
    ChapterVIDConnectorFactorNormalizedDerivativeCompiled.coordinateDeltaTrace
      side parameter localDelta localToOuter
  let collisionConstantsTrace :=
    ChapterVIDConnectorFactorNormalizedDerivativeCompiled.collisionConstantsTrace collision
  let coordinate := collision.add coordinateDeltaTrace.output
  let relativeExpTrace :=
    ChapterVILeanCompCertRelativeExponentialTrace.relativeExpTrace coordinate
      coordinateDeltaTrace.output collision collisionConstantsTrace.collisionInvCube.output
      ChapterVIDOuterArcPolarCompiledGrid.exponentialCoefficient
  let trace :=
    ChapterVILeanCompCertDependencyPreservingFactorDerivativeTrace.dependencyPreservingTrace
      coordinate coordinateDeltaTrace.output zetaDelta relativeExpTrace.output
      (pathDirectionRectangle side localToOuter) collision
      collisionConstantsTrace.collisionInv.output collisionConstantsTrace.collisionSquare.output
      collisionConstantsTrace.collisionInvCube.output
      collisionConstantsTrace.collisionInvFourth.output referenceYBaseRectangle
      ChapterVIDOuterArcPolarCompiledGrid.inverse10001 referenceCoefficient200
  coordinateDeltaTrace.operations ++ collisionConstantsTrace.operations ++
    relativeExpTrace.operations ++ trace.operations ++
    [.positiveLower (orientedOutput side trace.output).real]

theorem ReferenceCampaignModel.cellProposal_operations
    {massProduct : ℂ} {b d : ℤ}
    (campaign : ReferenceCampaignModel massProduct b d)
    (side : ChapterVIDOuterArcSide) (parameter : Interval 20) :
    (campaign.cellProposal side parameter).operations = referenceOperations side parameter := by
  rfl

def referenceCellCount : ℕ := 261

/-- The old omitted collar consists of exactly 261 precision-20 cells of width `2^-10`. -/
def referenceParameterInterval (side : ChapterVIDOuterArcSide)
    (index : Fin referenceCellCount) : Interval 20 :=
  let offset := Int.ofNat (index.val * 1024)
  match side with
  | .initial => ⟨781312 + offset, 781312 + offset + 1024⟩
  | .final => ⟨offset, offset + 1024⟩

def referenceSideOperations (side : ChapterVIDOuterArcSide) : List (DyadicOperation 20) :=
  (List.finRange referenceCellCount).flatMap fun index =>
    referenceOperations side (referenceParameterInterval side index)

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
  have hcollisionConstantsSound :
      ∀ operation ∈ cell.collisionConstantsTrace.operations, operation.Sound := by
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
  obtain ⟨hcollisionInv, hcollisionSquare, hcollisionInvCube,
      hcollisionInvFourth⟩ :=
    cell.collisionConstantsTrace.outputs_contain_of_allSound
      hcollisionConstantsSound cell.collision_contains
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
      cell.collision_contains hcollisionInvCube cell.coefficient100_contains
  have htrace : cell.trace.output.Contains
      (chapterVIDRootFactorDerivativeDependencyPreserving
        (model.connectorParameterRoot 0) coordinateValue *
          (model.rootModel.connectorTarget side (model.criticalValue 0) -
            model.rootModel.connectorSource side (model.criticalValue 0))) := by
    apply cell.trace.output_contains_of_allSound htraceSound
      hcoordinate hcoordinateDelta
      cell.zetaDelta_contains hExpDelta rfl
      hdirection cell.collision_contains hcollisionInv
      hcollisionSquare hcollisionInvCube hcollisionInvFourth cell.yBase_contains
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
