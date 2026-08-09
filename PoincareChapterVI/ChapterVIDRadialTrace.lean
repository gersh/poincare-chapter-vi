/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.ChapterVIDCriticalParameterInterval
import PoincareChapterVI.ChapterVILeanCompCertRoots

/-!
# Compiled interval trace for the radial coordinate

This is the reusable semantic layer for the radial dimension of the D outer-arc grid.  A small
endpoint trace certifies `q_D^(1/6)`, the collision radius, and their quotient.  Each radial cell
then uses only multiplication, exact fixed-scale addition/subtraction, and the compiled cubic- and
sixth-root traces.
-/

namespace PoincareChapterVI

open ChapterVILeanCompCertBatch
open ChapterVILeanCompCertRoots
open scoped unitInterval

namespace ChapterVIDRadialTrace

abbrev Interval (precision : ℕ) := ChapterVISignedDyadicInterval precision

/-- Operations shared by every radial cell. -/
structure EndpointTrace {precision : ℕ} where
  qD : Interval precision
  qDSixthRoot : Interval precision
  qDSixthTrace : SixthRootTrace qD qDSixthRoot
  xAbs : Interval precision
  collisionRadius : Interval precision
  collisionTrace : CubicRootTrace xAbs collisionRadius
  qDSixthInv : Interval precision
  correction : Interval precision

def EndpointTrace.operations {precision : ℕ}
    (trace : EndpointTrace (precision := precision)) :
    List (DyadicOperation precision) :=
  trace.qDSixthTrace.operations ++ trace.collisionTrace.operations ++
    [ .positiveReciprocal trace.qDSixthRoot trace.qDSixthInv
    , .mul trace.collisionRadius trace.qDSixthInv trace.correction ]

def EndpointTrace.Valid {precision : ℕ}
    (trace : EndpointTrace (precision := precision)) : Prop :=
  trace.qDSixthTrace.Valid ∧ trace.collisionTrace.Valid

theorem EndpointTrace.correction_contains_of_allSound {precision : ℕ}
    (trace : EndpointTrace (precision := precision)) (hvalid : trace.Valid)
    (hall : ∀ operation ∈ trace.operations, operation.Sound)
    (hqD : trace.qD.Contains chapterVIDCriticalParameterModulus)
    (hxAbs : trace.xAbs.Contains (-chapterVIDRoot)) :
    trace.correction.Contains chapterVIDCertificateContourCorrection := by
  have hqSound : ∀ operation ∈ trace.qDSixthTrace.operations, operation.Sound := by
    intro operation hoperation
    exact hall operation (by simp [EndpointTrace.operations, hoperation])
  have hcollisionSound : ∀ operation ∈ trace.collisionTrace.operations, operation.Sound := by
    intro operation hoperation
    exact hall operation (by simp [EndpointTrace.operations, hoperation])
  have hqRoot := trace.qDSixthTrace.output_contains_of_valid hvalid.1 hqSound
    chapterVIDCriticalParameterModulus_pos.le hqD
  have hcollisionRoot := trace.collisionTrace.output_contains_of_valid hvalid.2
    hcollisionSound (by linarith [chapterVIDRoot_lt_zero]) hxAbs
  have hinv : ChapterVISignedDyadicInterval.PositiveReciprocalCertificate
      trace.qDSixthRoot trace.qDSixthInv :=
    hall (.positiveReciprocal trace.qDSixthRoot trace.qDSixthInv)
      (by simp [EndpointTrace.operations])
  have hmul : ChapterVISignedDyadicInterval.MulCertificate
      trace.collisionRadius trace.qDSixthInv trace.correction :=
    hall (.mul trace.collisionRadius trace.qDSixthInv trace.correction)
      (by simp [EndpointTrace.operations])
  have hinvValue := hinv.contains_inv hqRoot
  have hcorrection := hmul.contains_mul hcollisionRoot hinvValue
  rw [← chapterVIDCollisionRadius_eq_rpow] at hcorrection
  simpa [chapterVIDCertificateContourCorrection,
    chapterVIDCriticalParameterSixthRoot, div_eq_mul_inv] using hcorrection

/-- Rounded intermediates depending on one radial input interval. -/
structure Trace {precision : ℕ} (endpoint : EndpointTrace (precision := precision))
    (input : Interval precision) where
  qDeltaProduct : Interval precision
  qCubeRoot : Interval precision
  qCubeTrace : CubicRootTrace
    ((ChapterVISignedDyadicInterval.pointInt precision 1).add qDeltaProduct) qCubeRoot
  qSixthRoot : Interval precision
  qSixthTrace : SixthRootTrace
    ((ChapterVISignedDyadicInterval.pointInt precision 1).add qDeltaProduct) qSixthRoot
  correctionDeltaProduct : Interval precision
  radius : Interval precision

def Trace.one {precision : ℕ}
    {endpoint : EndpointTrace (precision := precision)} {input : Interval precision}
    (_trace : Trace endpoint input) : Interval precision :=
  ChapterVISignedDyadicInterval.pointInt precision 1

def Trace.qDelta {precision : ℕ}
    {endpoint : EndpointTrace (precision := precision)} {input : Interval precision}
    (trace : Trace endpoint input) : Interval precision :=
  endpoint.qD.sub trace.one

def Trace.q {precision : ℕ}
    {endpoint : EndpointTrace (precision := precision)} {input : Interval precision}
    (trace : Trace endpoint input) : Interval precision :=
  trace.one.add trace.qDeltaProduct

def Trace.correctionDelta {precision : ℕ}
    {endpoint : EndpointTrace (precision := precision)} {input : Interval precision}
    (trace : Trace endpoint input) : Interval precision :=
  endpoint.correction.sub trace.one

def Trace.correctionFactor {precision : ℕ}
    {endpoint : EndpointTrace (precision := precision)} {input : Interval precision}
    (trace : Trace endpoint input) : Interval precision :=
  trace.one.add trace.correctionDeltaProduct

def Trace.operations {precision : ℕ}
    {endpoint : EndpointTrace (precision := precision)}
    {input : Interval precision} (trace : Trace endpoint input) :
    List (DyadicOperation precision) :=
  [ .mul input trace.qDelta trace.qDeltaProduct ] ++
    trace.qCubeTrace.operations ++ trace.qSixthTrace.operations ++
    [ .mul input trace.correctionDelta trace.correctionDeltaProduct
    , .mul trace.qSixthRoot trace.correctionFactor trace.radius ]

def Trace.Valid {precision : ℕ}
    {endpoint : EndpointTrace (precision := precision)}
    {input : Interval precision} (trace : Trace endpoint input) : Prop :=
  trace.qCubeTrace.Valid ∧ trace.qSixthTrace.Valid

theorem Trace.outputs_contain_of_allSound {precision : ℕ}
    {endpoint : EndpointTrace (precision := precision)} {input : Interval precision}
    (trace : Trace endpoint input) (hvalid : trace.Valid)
    (hall : ∀ operation ∈ trace.operations, operation.Sound)
    {s : I} (hs : input.Contains (s : ℝ))
    (hqD : endpoint.qD.Contains chapterVIDCriticalParameterModulus)
    (hcorrection : endpoint.correction.Contains chapterVIDCertificateContourCorrection) :
    trace.qCubeRoot.Contains
        (chapterVIDCertificateParameter s ^ ((3 : ℝ)⁻¹)) ∧
      trace.radius.Contains (chapterVIDCertificateContourRadius s) := by
  have hone := ChapterVISignedDyadicInterval.pointInt_contains precision 1
  have hqDelta := ChapterVISignedDyadicInterval.sub_contains hqD hone
  have hqMul : ChapterVISignedDyadicInterval.MulCertificate
      input trace.qDelta trace.qDeltaProduct :=
    hall (.mul input trace.qDelta trace.qDeltaProduct)
      (by simp [Trace.operations])
  have hqProduct := hqMul.contains_mul hs hqDelta
  have hq : trace.q.Contains (chapterVIDCertificateParameter s) := by
    simpa [Trace.q, Trace.one, Trace.qDelta, chapterVIDCertificateParameter,
      AffineMap.lineMap_apply, mul_assoc, add_comm] using
      ChapterVISignedDyadicInterval.add_contains hone hqProduct
  have hcubeSound : ∀ operation ∈ trace.qCubeTrace.operations, operation.Sound := by
    intro operation hoperation
    exact hall operation (by simp [Trace.operations, hoperation])
  have hsixthSound : ∀ operation ∈ trace.qSixthTrace.operations, operation.Sound := by
    intro operation hoperation
    exact hall operation (by simp [Trace.operations, hoperation])
  have hcube := trace.qCubeTrace.output_contains_of_valid hvalid.1 hcubeSound
    (chapterVIDCertificateParameter_pos s).le hq
  have hsixth := trace.qSixthTrace.output_contains_of_valid hvalid.2 hsixthSound
    (chapterVIDCertificateParameter_pos s).le hq
  have hcorrectionDelta := ChapterVISignedDyadicInterval.sub_contains hcorrection hone
  have hcorrectionMul : ChapterVISignedDyadicInterval.MulCertificate
      input trace.correctionDelta trace.correctionDeltaProduct :=
    hall (.mul input trace.correctionDelta trace.correctionDeltaProduct)
      (by simp [Trace.operations])
  have hcorrectionProduct := hcorrectionMul.contains_mul hs hcorrectionDelta
  have hfactor : trace.correctionFactor.Contains
      (chapterVIDCertificateContourCorrectionFactor s) := by
    simpa [Trace.correctionFactor, Trace.correctionDelta, Trace.one,
      chapterVIDCertificateContourCorrectionFactor, AffineMap.lineMap_apply,
      mul_assoc, add_comm] using
      ChapterVISignedDyadicInterval.add_contains hone hcorrectionProduct
  have hradiusMul : ChapterVISignedDyadicInterval.MulCertificate
      trace.qSixthRoot trace.correctionFactor trace.radius :=
    hall (.mul trace.qSixthRoot trace.correctionFactor trace.radius)
      (by simp [Trace.operations])
  exact ⟨hcube, by
    simpa [chapterVIDCertificateContourRadius] using
      hradiusMul.contains_mul hsixth hfactor⟩

/-- Internal scalar enclosures needed when differentiating the certificate radius. -/
theorem Trace.velocity_inputs_contain_of_allSound {precision : ℕ}
    {endpoint : EndpointTrace (precision := precision)} {input : Interval precision}
    (trace : Trace endpoint input) (hvalid : trace.Valid)
    (hall : ∀ operation ∈ trace.operations, operation.Sound)
    {s : I} (hs : input.Contains (s : ℝ))
    (hqD : endpoint.qD.Contains chapterVIDCriticalParameterModulus)
    (hcorrection : endpoint.correction.Contains chapterVIDCertificateContourCorrection) :
    trace.q.Contains (chapterVIDCertificateParameter s) ∧
      trace.qSixthRoot.Contains
        (chapterVIDCertificateParameter s ^ ((6 : ℝ)⁻¹)) ∧
      trace.correctionFactor.Contains
        (chapterVIDCertificateContourCorrectionFactor s) := by
  have hone := ChapterVISignedDyadicInterval.pointInt_contains precision 1
  have hqDelta := ChapterVISignedDyadicInterval.sub_contains hqD hone
  have hqMul : ChapterVISignedDyadicInterval.MulCertificate
      input trace.qDelta trace.qDeltaProduct :=
    hall (.mul input trace.qDelta trace.qDeltaProduct)
      (by simp [Trace.operations])
  have hqProduct := hqMul.contains_mul hs hqDelta
  have hq : trace.q.Contains (chapterVIDCertificateParameter s) := by
    simpa [Trace.q, Trace.one, Trace.qDelta, chapterVIDCertificateParameter,
      AffineMap.lineMap_apply, mul_assoc, add_comm] using
      ChapterVISignedDyadicInterval.add_contains hone hqProduct
  have hsixthSound : ∀ operation ∈ trace.qSixthTrace.operations, operation.Sound := by
    intro operation hoperation
    exact hall operation (by simp [Trace.operations, hoperation])
  have hsixth := trace.qSixthTrace.output_contains_of_valid hvalid.2
    hsixthSound (chapterVIDCertificateParameter_pos s).le hq
  have hcorrectionDelta := ChapterVISignedDyadicInterval.sub_contains hcorrection hone
  have hcorrectionMul : ChapterVISignedDyadicInterval.MulCertificate
      input trace.correctionDelta trace.correctionDeltaProduct :=
    hall (.mul input trace.correctionDelta trace.correctionDeltaProduct)
      (by simp [Trace.operations])
  have hcorrectionProduct := hcorrectionMul.contains_mul hs hcorrectionDelta
  have hfactor : trace.correctionFactor.Contains
      (chapterVIDCertificateContourCorrectionFactor s) := by
    simpa [Trace.correctionFactor, Trace.correctionDelta, Trace.one,
      chapterVIDCertificateContourCorrectionFactor, AffineMap.lineMap_apply,
      mul_assoc, add_comm] using
      ChapterVISignedDyadicInterval.add_contains hone hcorrectionProduct
  exact ⟨hq, hsixth, hfactor⟩

end ChapterVIDRadialTrace

end PoincareChapterVI
