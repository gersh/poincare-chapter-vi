/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.ChapterVIDRadialTailPathDerivative
import PoincareChapterVI.ChapterVILeanCompCertHighOrderAnomalyTrace

/-!
# Signed-dyadic trace for the radial-tail total derivative

The trace reuses the certified polar radicand, including its analytic exponential remainder.
It then evaluates both collision-factor derivatives, their parameter-root contributions, and the
final product rule using only signed fixed-point multiplications.
-/

noncomputable section

set_option maxHeartbeats 5000000

namespace PoincareChapterVI

open ChapterVILeanCompCertBatch

namespace ChapterVILeanCompCertRadialTailDerivativeTrace

abbrev Interval (precision : ℕ) := ChapterVISignedDyadicInterval precision
abbrev Rectangle (precision : ℕ) := ChapterVISignedDyadicComplexRectangle precision

/-- Scalar trace for `ζ'/ζ` and the radius velocity. -/
structure VelocityTrace {precision : ℕ}
    (q qSixthRoot correctionFactor qDelta correctionDelta : Interval precision) where
  qInv : Interval precision
  third : Interval precision
  sixth : Interval precision
  qDotThird : Interval precision
  qDotSixth : Interval precision
  zetaLogVelocity : Interval precision
  sixthLogVelocity : Interval precision
  sixthVelocity : Interval precision
  firstRadiusVelocity : Interval precision
  secondRadiusVelocity : Interval precision

def VelocityTrace.radiusVelocity {precision : ℕ}
    {q qSixthRoot correctionFactor qDelta correctionDelta : Interval precision}
    (trace : VelocityTrace q qSixthRoot correctionFactor qDelta correctionDelta) :
    Interval precision :=
  trace.firstRadiusVelocity.add trace.secondRadiusVelocity

def VelocityTrace.operations {precision : ℕ}
    {q qSixthRoot correctionFactor qDelta correctionDelta : Interval precision}
    (trace : VelocityTrace q qSixthRoot correctionFactor qDelta correctionDelta) :
    List (DyadicOperation precision) :=
  [ .positiveReciprocal q trace.qInv
  , .positiveReciprocal (ChapterVISignedDyadicInterval.pointInt precision 3) trace.third
  , .positiveReciprocal (ChapterVISignedDyadicInterval.pointInt precision 6) trace.sixth
  , .mul qDelta trace.third trace.qDotThird
  , .mul qDelta trace.sixth trace.qDotSixth
  , .mul trace.qDotThird trace.qInv trace.zetaLogVelocity
  , .mul trace.qDotSixth trace.qInv trace.sixthLogVelocity
  , .mul trace.sixthLogVelocity qSixthRoot trace.sixthVelocity
  , .mul trace.sixthVelocity correctionFactor trace.firstRadiusVelocity
  , .mul qSixthRoot correctionDelta trace.secondRadiusVelocity ]

def velocityTrace {precision : ℕ}
    (q qSixthRoot correctionFactor qDelta correctionDelta : Interval precision) :
    VelocityTrace q qSixthRoot correctionFactor qDelta correctionDelta := by
  let qInv := ChapterVILeanCompCertProposals.positiveReciprocal precision q
  let third := ChapterVILeanCompCertProposals.positiveReciprocal precision
    (ChapterVISignedDyadicInterval.pointInt precision 3)
  let sixth := ChapterVILeanCompCertProposals.positiveReciprocal precision
    (ChapterVISignedDyadicInterval.pointInt precision 6)
  let qDotThird := ChapterVILeanCompCertProposals.mul precision qDelta third
  let qDotSixth := ChapterVILeanCompCertProposals.mul precision qDelta sixth
  let zetaLogVelocity := ChapterVILeanCompCertProposals.mul precision qDotThird qInv
  let sixthLogVelocity := ChapterVILeanCompCertProposals.mul precision qDotSixth qInv
  let sixthVelocity := ChapterVILeanCompCertProposals.mul precision sixthLogVelocity qSixthRoot
  let firstRadiusVelocity := ChapterVILeanCompCertProposals.mul precision
    sixthVelocity correctionFactor
  let secondRadiusVelocity := ChapterVILeanCompCertProposals.mul precision
    qSixthRoot correctionDelta
  exact ⟨qInv, third, sixth, qDotThird, qDotSixth, zetaLogVelocity,
    sixthLogVelocity, sixthVelocity, firstRadiusVelocity, secondRadiusVelocity⟩

theorem VelocityTrace.outputs_contain_of_allSound
    {precision : ℕ}
    {q qSixthRoot correctionFactor qDelta correctionDelta : Interval precision}
    (trace : VelocityTrace q qSixthRoot correctionFactor qDelta correctionDelta)
    (hall : ∀ operation ∈ trace.operations, operation.Sound)
    {qValue qSixthValue correctionValue qDot correctionDot : ℝ}
    (hq : q.Contains qValue)
    (hsixth : qSixthRoot.Contains qSixthValue)
    (hfactor : correctionFactor.Contains correctionValue)
    (hqDot : qDelta.Contains qDot)
    (hcorrectionDot : correctionDelta.Contains correctionDot) :
    trace.zetaLogVelocity.Contains (qDot * (3 : ℝ)⁻¹ * qValue⁻¹) ∧
      trace.radiusVelocity.Contains
        ((qDot * (6 : ℝ)⁻¹ * qValue⁻¹ * qSixthValue) * correctionValue +
          qSixthValue * correctionDot) := by
  have hqInv := (show ChapterVISignedDyadicInterval.PositiveReciprocalCertificate
      q trace.qInv from hall (.positiveReciprocal q trace.qInv)
        (by simp [VelocityTrace.operations])).contains_inv hq
  have hthree := ChapterVISignedDyadicInterval.pointInt_contains precision 3
  have hsix := ChapterVISignedDyadicInterval.pointInt_contains precision 6
  have hthird := (show ChapterVISignedDyadicInterval.PositiveReciprocalCertificate
      (ChapterVISignedDyadicInterval.pointInt precision 3) trace.third from
        hall (.positiveReciprocal (ChapterVISignedDyadicInterval.pointInt precision 3)
          trace.third) (by simp [VelocityTrace.operations])).contains_inv hthree
  have hsixthInv := (show ChapterVISignedDyadicInterval.PositiveReciprocalCertificate
      (ChapterVISignedDyadicInterval.pointInt precision 6) trace.sixth from
        hall (.positiveReciprocal (ChapterVISignedDyadicInterval.pointInt precision 6)
          trace.sixth) (by simp [VelocityTrace.operations])).contains_inv hsix
  have hqThird := (show ChapterVISignedDyadicInterval.MulCertificate
      qDelta trace.third trace.qDotThird from
        hall (.mul qDelta trace.third trace.qDotThird)
          (by simp [VelocityTrace.operations])).contains_mul hqDot hthird
  have hqSixth := (show ChapterVISignedDyadicInterval.MulCertificate
      qDelta trace.sixth trace.qDotSixth from
        hall (.mul qDelta trace.sixth trace.qDotSixth)
          (by simp [VelocityTrace.operations])).contains_mul hqDot hsixthInv
  have hζLog := (show ChapterVISignedDyadicInterval.MulCertificate
      trace.qDotThird trace.qInv trace.zetaLogVelocity from
        hall (.mul trace.qDotThird trace.qInv trace.zetaLogVelocity)
          (by simp [VelocityTrace.operations])).contains_mul hqThird hqInv
  have hsixthLog := (show ChapterVISignedDyadicInterval.MulCertificate
      trace.qDotSixth trace.qInv trace.sixthLogVelocity from
        hall (.mul trace.qDotSixth trace.qInv trace.sixthLogVelocity)
          (by simp [VelocityTrace.operations])).contains_mul hqSixth hqInv
  have hsixthVelocity := (show ChapterVISignedDyadicInterval.MulCertificate
      trace.sixthLogVelocity qSixthRoot trace.sixthVelocity from
        hall (.mul trace.sixthLogVelocity qSixthRoot trace.sixthVelocity)
          (by simp [VelocityTrace.operations])).contains_mul hsixthLog hsixth
  have hfirst := (show ChapterVISignedDyadicInterval.MulCertificate
      trace.sixthVelocity correctionFactor trace.firstRadiusVelocity from
        hall (.mul trace.sixthVelocity correctionFactor trace.firstRadiusVelocity)
          (by simp [VelocityTrace.operations])).contains_mul hsixthVelocity hfactor
  have hsecond := (show ChapterVISignedDyadicInterval.MulCertificate
      qSixthRoot correctionDelta trace.secondRadiusVelocity from
        hall (.mul qSixthRoot correctionDelta trace.secondRadiusVelocity)
          (by simp [VelocityTrace.operations])).contains_mul hsixth hcorrectionDot
  constructor
  · simpa [mul_assoc] using hζLog
  · simpa [VelocityTrace.radiusVelocity, mul_assoc] using
      ChapterVISignedDyadicInterval.add_contains hfirst hsecond

structure Trace {precision : ℕ} {zeta radius : Interval precision}
    {unit : Rectangle precision}
    (base : ChapterVILeanCompCertRadicandTrace.Trace zeta radius unit)
    (anomaly : ChapterVILeanCompCertHighOrderAnomalyTrace.Trace base)
    (zetaLogVelocity radiusVelocity : Interval precision) where
  uVelocity : ChapterVISignedDyadicComplexRectangle.RealMulTrace radiusVelocity unit
  coordinateSquare : ChapterVISignedDyadicComplexRectangle.MulTrace
    base.polar.u.output base.polar.u.output
  coordinateInvFourth : ChapterVISignedDyadicComplexRectangle.MulTrace
    base.polar.uCubeInv.output base.polar.uInv.output
  logCorrection : ChapterVISignedDyadicComplexRectangle.RealMulTrace base.inverse10001
    (coordinateInvFourth.output.add coordinateSquare.output)
  plusLaurent : ChapterVISignedDyadicComplexRectangle.RealMulTrace base.inverse10001
    ((coordinateSquare.output.nsmul 30000).sub (coordinateInvFourth.output.nsmul 3))
  minusLaurent : ChapterVISignedDyadicComplexRectangle.RealMulTrace base.inverse10001
    ((coordinateSquare.output.nsmul 3).sub (coordinateInvFourth.output.nsmul 30000))
  plusLaurentPath : ChapterVISignedDyadicComplexRectangle.MulTrace
    plusLaurent.output uVelocity.output
  minusLaurentPath : ChapterVISignedDyadicComplexRectangle.MulTrace
    minusLaurent.output uVelocity.output
  laurentCrossOne : ChapterVISignedDyadicComplexRectangle.MulTrace
    plusLaurentPath.output base.laurentMinus.output
  laurentCrossTwo : ChapterVISignedDyadicComplexRectangle.MulTrace
    base.laurentPlus.output minusLaurentPath.output
  mixedOne : ChapterVISignedDyadicComplexRectangle.MulTrace
    plusLaurentPath.output anomaly.yInv
  mixedTwo : ChapterVISignedDyadicComplexRectangle.MulTrace anomaly.y minusLaurentPath.output
  shapeOne : ChapterVISignedDyadicComplexRectangle.MulTrace
    base.laurentPlus.output anomaly.yInv
  shapeTwo : ChapterVISignedDyadicComplexRectangle.MulTrace anomaly.y base.laurentMinus.output
  logPath : ChapterVISignedDyadicComplexRectangle.MulTrace
    (base.polar.uInv.output.sub (logCorrection.output.nsmul 100)) uVelocity.output
  logShape : ChapterVISignedDyadicComplexRectangle.MulTrace
    (logPath.output.add ⟨zetaLogVelocity,
      ChapterVISignedDyadicInterval.pointInt precision 0⟩)
    (shapeOne.output.sub shapeTwo.output)

def Trace.operations {precision : ℕ} {zeta radius : Interval precision}
    {unit : Rectangle precision}
    {base : ChapterVILeanCompCertRadicandTrace.Trace zeta radius unit}
    {anomaly : ChapterVILeanCompCertHighOrderAnomalyTrace.Trace base}
    {zetaLogVelocity radiusVelocity : Interval precision}
    (trace : Trace base anomaly zetaLogVelocity radiusVelocity) : List (DyadicOperation precision) :=
  base.operations ++ anomaly.operations ++ trace.uVelocity.operations ++ trace.coordinateSquare.operations ++
    trace.coordinateInvFourth.operations ++ trace.logCorrection.operations ++
    trace.plusLaurent.operations ++ trace.minusLaurent.operations ++
    trace.plusLaurentPath.operations ++ trace.minusLaurentPath.operations ++
    trace.laurentCrossOne.operations ++ trace.laurentCrossTwo.operations ++
    trace.mixedOne.operations ++ trace.mixedTwo.operations ++
    trace.shapeOne.operations ++ trace.shapeTwo.operations ++ trace.logPath.operations ++
    trace.logShape.operations

def Trace.output {precision : ℕ} {zeta radius : Interval precision}
    {unit : Rectangle precision}
    {base : ChapterVILeanCompCertRadicandTrace.Trace zeta radius unit}
    {anomaly : ChapterVILeanCompCertHighOrderAnomalyTrace.Trace base}
    {zetaLogVelocity radiusVelocity : Interval precision}
    (trace : Trace base anomaly zetaLogVelocity radiusVelocity) : Rectangle precision :=
  (trace.laurentCrossOne.output.add trace.laurentCrossTwo.output).sub
      ((trace.mixedOne.output.add trace.mixedTwo.output).nsmul 2) |>.add
    (trace.logShape.output.nsmul 2)

def derivativeTrace {precision : ℕ} {zeta radius : Interval precision}
    {unit : Rectangle precision}
    (base : ChapterVILeanCompCertRadicandTrace.Trace zeta radius unit)
    (zetaLogVelocity radiusVelocity : Interval precision) :
    Trace base (ChapterVILeanCompCertHighOrderAnomalyTrace.highOrderTrace base)
      zetaLogVelocity radiusVelocity := by
  let anomaly := ChapterVILeanCompCertHighOrderAnomalyTrace.highOrderTrace base
  let uVelocity := ChapterVILeanCompCertProposals.realMulTrace radiusVelocity unit
  let coordinateSquare := ChapterVILeanCompCertProposals.mulTrace
    base.polar.u.output base.polar.u.output
  let coordinateInvFourth := ChapterVILeanCompCertProposals.mulTrace
    base.polar.uCubeInv.output base.polar.uInv.output
  let powerSum := coordinateInvFourth.output.add coordinateSquare.output
  let logCorrection := ChapterVILeanCompCertProposals.realMulTrace base.inverse10001 powerSum
  let logDerivative := base.polar.uInv.output.sub (logCorrection.output.nsmul 100)
  let plusLaurent := ChapterVILeanCompCertProposals.realMulTrace base.inverse10001
    ((coordinateSquare.output.nsmul 30000).sub (coordinateInvFourth.output.nsmul 3))
  let minusLaurent := ChapterVILeanCompCertProposals.realMulTrace base.inverse10001
    ((coordinateSquare.output.nsmul 3).sub (coordinateInvFourth.output.nsmul 30000))
  let plusLaurentPath := ChapterVILeanCompCertProposals.mulTrace
    plusLaurent.output uVelocity.output
  let minusLaurentPath := ChapterVILeanCompCertProposals.mulTrace
    minusLaurent.output uVelocity.output
  let laurentCrossOne := ChapterVILeanCompCertProposals.mulTrace
    plusLaurentPath.output base.laurentMinus.output
  let laurentCrossTwo := ChapterVILeanCompCertProposals.mulTrace
    base.laurentPlus.output minusLaurentPath.output
  let mixedOne := ChapterVILeanCompCertProposals.mulTrace plusLaurentPath.output anomaly.yInv
  let mixedTwo := ChapterVILeanCompCertProposals.mulTrace anomaly.y minusLaurentPath.output
  let shapeOne := ChapterVILeanCompCertProposals.mulTrace base.laurentPlus.output anomaly.yInv
  let shapeTwo := ChapterVILeanCompCertProposals.mulTrace anomaly.y base.laurentMinus.output
  let logPath := ChapterVILeanCompCertProposals.mulTrace logDerivative uVelocity.output
  let logShape := ChapterVILeanCompCertProposals.mulTrace
    (logPath.output.add ⟨zetaLogVelocity,
      ChapterVISignedDyadicInterval.pointInt precision 0⟩)
    (shapeOne.output.sub shapeTwo.output)
  exact ⟨uVelocity, coordinateSquare, coordinateInvFourth, logCorrection,
    plusLaurent, minusLaurent, plusLaurentPath,
    minusLaurentPath, laurentCrossOne, laurentCrossTwo, mixedOne, mixedTwo, shapeOne,
    shapeTwo, logPath, logShape⟩

theorem Trace.output_contains_of_allSound
    {precision : ℕ} {zeta radius : Interval precision} {unit : Rectangle precision}
    {base : ChapterVILeanCompCertRadicandTrace.Trace zeta radius unit}
    {anomaly : ChapterVILeanCompCertHighOrderAnomalyTrace.Trace base}
    {zetaLogVelocity radiusVelocity : Interval precision}
    (trace : Trace base anomaly zetaLogVelocity radiusVelocity)
    (hall : ∀ operation ∈ trace.operations, operation.Sound)
    {ζ r ζlog rdot : ℝ} {v : ℂ}
    (hζ : zeta.Contains ζ) (hr : radius.Contains r) (hv : unit.Contains v)
    (hvNorm : ‖v‖ = 1)
    (hcoefficient : base.exponentialCoefficient.Contains (100 / 30003 : ℝ))
    (hinverse10001 : base.inverse10001.Contains (1 / 10001 : ℝ))
    (hζPos : 0 < ζ) (hrPos : 0 < r)
    (hargument : ‖chapterVIDRootExponentialArgument ((r : ℂ) * v)‖ ≤ 1)
    (hζlog : zetaLogVelocity.Contains ζlog)
    (hrdot : radiusVelocity.Contains rdot) :
    trace.output.Contains
      (chapterVIDRadialTailRadicandDerivative (ζ : ℂ) ((r : ℂ) * v)
        ((ζlog * ζ : ℝ) : ℂ) ((rdot : ℂ) * v)) := by
  have soundOf {operations : List (DyadicOperation precision)}
      (hsub : ∀ operation ∈ operations, operation ∈ trace.operations) :
      ∀ operation ∈ operations, operation.Sound := by
    intro operation hoperation
    exact hall operation (hsub operation hoperation)
  have hbase : ∀ operation ∈ base.operations, operation.Sound :=
    soundOf (by intro operation hoperation; simp [Trace.operations, hoperation])
  have hanomaly : ∀ operation ∈ anomaly.operations, operation.Sound :=
    soundOf (by intro operation hoperation; simp [Trace.operations, hoperation])
  have hpolar : ∀ operation ∈ base.polar.operations, operation.Sound := by
    intro operation hoperation
    exact hbase operation (by
      simp [ChapterVILeanCompCertRadicandTrace.Trace.operations, hoperation])
  rcases base.polar.outputs_contain_of_allSound hpolar hr hv hvNorm with
    ⟨hu, huInv, huCube, huCubeInv⟩
  rcases anomaly.anomalies_contain_of_allSound hbase hanomaly hζ hr hv hvNorm hcoefficient
    hζPos hrPos hargument with ⟨hy, hyInv⟩
  have huVelocity := trace.uVelocity.output_contains_of_allSound
    (soundOf (by intro operation hoperation; simp [Trace.operations, hoperation]))
    hrdot hv
  have huSquare := trace.coordinateSquare.output_contains_mul_of_allSound
    (soundOf (by intro operation hoperation; simp [Trace.operations, hoperation])) hu hu
  have huInvFourth := trace.coordinateInvFourth.output_contains_mul_of_allSound
    (soundOf (by intro operation hoperation; simp [Trace.operations, hoperation]))
    huCubeInv huInv
  have hpowerSum := ChapterVISignedDyadicComplexRectangle.add_contains huInvFourth huSquare
  have hlogCorrection := trace.logCorrection.output_contains_of_allSound
    (soundOf (by intro operation hoperation; simp [Trace.operations, hoperation]))
    hinverse10001 hpowerSum
  have hvNe : v ≠ 0 := by
    intro hv0
    rw [hv0, norm_zero] at hvNorm
    norm_num at hvNorm
  have huNe : (r : ℂ) * v ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr hrPos.ne') hvNe
  have hlogScaled : (trace.logCorrection.output.nsmul 100).Contains
      ((100 / 10001 : ℂ) * (((r : ℂ) * v)⁻¹ ^ 4 + ((r : ℂ) * v) ^ 2)) := by
    convert ChapterVISignedDyadicComplexRectangle.nsmul_contains 100 hlogCorrection using 1
    push_cast
    field_simp [huNe]
  have hlogDerivative :
      (base.polar.uInv.output.sub (trace.logCorrection.output.nsmul 100)).Contains
        (chapterVIDRootSecondAnomalyLogDerivative ((r : ℂ) * v)) := by
    unfold chapterVIDRootSecondAnomalyLogDerivative
    exact ChapterVISignedDyadicComplexRectangle.sub_contains huInv hlogScaled
  have hplusLaurentInput := ChapterVISignedDyadicComplexRectangle.sub_contains
    (ChapterVISignedDyadicComplexRectangle.nsmul_contains 30000 huSquare)
    (ChapterVISignedDyadicComplexRectangle.nsmul_contains 3 huInvFourth)
  have hminusLaurentInput := ChapterVISignedDyadicComplexRectangle.sub_contains
    (ChapterVISignedDyadicComplexRectangle.nsmul_contains 3 huSquare)
    (ChapterVISignedDyadicComplexRectangle.nsmul_contains 30000 huInvFourth)
  have hplusLaurent := trace.plusLaurent.output_contains_of_allSound
    (soundOf (by intro operation hoperation; simp [Trace.operations, hoperation]))
    hinverse10001 hplusLaurentInput
  have hminusLaurent := trace.minusLaurent.output_contains_of_allSound
    (soundOf (by intro operation hoperation; simp [Trace.operations, hoperation]))
    hinverse10001 hminusLaurentInput
  have hA := base.laurentPlus.output_contains_of_allSound
    (by intro operation hoperation
        exact hbase operation (by
          simp [ChapterVILeanCompCertRadicandTrace.Trace.operations, hoperation]))
    hinverse10001
    (ChapterVISignedDyadicComplexRectangle.add_contains
      (ChapterVISignedDyadicComplexRectangle.add_contains
        (ChapterVISignedDyadicComplexRectangle.nsmul_contains 10000 huCube) huCubeInv)
      (ChapterVISignedDyadicComplexRectangle.pointInt_contains precision (-200)))
  have hB := base.laurentMinus.output_contains_of_allSound
    (by intro operation hoperation
        exact hbase operation (by
          simp [ChapterVILeanCompCertRadicandTrace.Trace.operations, hoperation]))
    hinverse10001
    (ChapterVISignedDyadicComplexRectangle.add_contains
      (ChapterVISignedDyadicComplexRectangle.add_contains huCube
        (ChapterVISignedDyadicComplexRectangle.nsmul_contains 10000 huCubeInv))
      (ChapterVISignedDyadicComplexRectangle.pointInt_contains precision (-200)))
  have ha := trace.plusLaurentPath.output_contains_mul_of_allSound
    (soundOf (by intro operation hoperation; simp [Trace.operations, hoperation]))
    hplusLaurent huVelocity
  have hb := trace.minusLaurentPath.output_contains_mul_of_allSound
    (soundOf (by intro operation hoperation; simp [Trace.operations, hoperation]))
    hminusLaurent huVelocity
  have haB := trace.laurentCrossOne.output_contains_mul_of_allSound
    (soundOf (by intro operation hoperation; simp [Trace.operations, hoperation])) ha hB
  have hAb := trace.laurentCrossTwo.output_contains_mul_of_allSound
    (soundOf (by intro operation hoperation; simp [Trace.operations, hoperation])) hA hb
  have hayInv := trace.mixedOne.output_contains_mul_of_allSound
    (soundOf (by intro operation hoperation; simp [Trace.operations, hoperation])) ha hyInv
  have hyb := trace.mixedTwo.output_contains_mul_of_allSound
    (soundOf (by intro operation hoperation; simp [Trace.operations, hoperation])) hy hb
  have hAyInv := trace.shapeOne.output_contains_mul_of_allSound
    (soundOf (by intro operation hoperation; simp [Trace.operations, hoperation])) hA hyInv
  have hyB := trace.shapeTwo.output_contains_mul_of_allSound
    (soundOf (by intro operation hoperation; simp [Trace.operations, hoperation])) hy hB
  have hlogPath := trace.logPath.output_contains_mul_of_allSound
    (soundOf (by intro operation hoperation; simp [Trace.operations, hoperation]))
    hlogDerivative huVelocity
  have hζLogComplex :
      (⟨zetaLogVelocity, ChapterVISignedDyadicInterval.pointInt precision 0⟩ :
        Rectangle precision).Contains (ζlog : ℂ) := by
    exact ⟨by simpa using hζlog,
      by simpa using ChapterVISignedDyadicInterval.pointInt_contains precision 0⟩
  have htotalLog := ChapterVISignedDyadicComplexRectangle.add_contains
    hlogPath hζLogComplex
  have hshape := ChapterVISignedDyadicComplexRectangle.sub_contains hAyInv hyB
  have hlogShape := trace.logShape.output_contains_mul_of_allSound
    (soundOf (by intro operation hoperation; simp [Trace.operations, hoperation]))
    htotalLog hshape
  have hcross := ChapterVISignedDyadicComplexRectangle.add_contains haB hAb
  have hmixed := ChapterVISignedDyadicComplexRectangle.add_contains hayInv hyb
  have hresult := ChapterVISignedDyadicComplexRectangle.add_contains
    (ChapterVISignedDyadicComplexRectangle.sub_contains hcross
      (ChapterVISignedDyadicComplexRectangle.nsmul_contains 2 hmixed))
    (ChapterVISignedDyadicComplexRectangle.nsmul_contains 2 hlogShape)
  change (((trace.laurentCrossOne.output.add trace.laurentCrossTwo.output).sub
      ((trace.mixedOne.output.add trace.mixedTwo.output).nsmul 2)).add
        (trace.logShape.output.nsmul 2)).Contains _
  convert hresult using 1
  push_cast
  rw [chapterVIDRadialTailRadicandDerivative_eq_reduced
    (Complex.ofReal_ne_zero.mpr hζPos.ne') huNe]
  unfold chapterVIDRadialTailRadicandDerivativeReduced
  ring

end ChapterVILeanCompCertRadialTailDerivativeTrace

end PoincareChapterVI
