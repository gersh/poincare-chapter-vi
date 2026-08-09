/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.ChapterVILeanCompCertProposals

/-!
# A degree-five compiled enclosure for the D anomaly

The older polar trace uses `exp a = 1 + a + O (|a|^2)`.  That estimate is adequate for
nonvanishing, but it is too wide for the cancellation in the final radial derivative.  This
trace retains the first six Taylor terms and uses `Complex.exp_bound` to enclose the remainder
by `|a|^6 / 512`.  All polynomial arithmetic and the final error radii remain signed-dyadic
LeanCompCert operations.
-/

namespace PoincareChapterVI

open ChapterVILeanCompCertBatch

noncomputable section

namespace ChapterVILeanCompCertHighOrderAnomalyTrace

abbrev Interval (precision : ℕ) := ChapterVISignedDyadicInterval precision
abbrev Rectangle (precision : ℕ) := ChapterVISignedDyadicComplexRectangle precision

def expPolynomial (a : ℂ) : ℂ :=
  1 + a + a ^ 2 / 2 + a ^ 3 / 6 + a ^ 4 / 24 + a ^ 5 / 120

def expInvPolynomial (a : ℂ) : ℂ :=
  1 - a + a ^ 2 / 2 - a ^ 3 / 6 + a ^ 4 / 24 - a ^ 5 / 120

structure Trace {precision : ℕ} {zeta radius : Interval precision}
    {unit : Rectangle precision}
    (base : ChapterVILeanCompCertRadicandTrace.Trace zeta radius unit) where
  half : Interval precision
  sixth : Interval precision
  twentyFourth : Interval precision
  oneTwenty : Interval precision
  oneFiveTwelve : Interval precision
  argumentSquare : ChapterVISignedDyadicComplexRectangle.MulTrace
    base.argument.output base.argument.output
  argumentCube : ChapterVISignedDyadicComplexRectangle.MulTrace
    argumentSquare.output base.argument.output
  argumentFourth : ChapterVISignedDyadicComplexRectangle.MulTrace
    argumentCube.output base.argument.output
  argumentFifth : ChapterVISignedDyadicComplexRectangle.MulTrace
    argumentFourth.output base.argument.output
  squareHalf : ChapterVISignedDyadicComplexRectangle.RealMulTrace half argumentSquare.output
  cubeSixth : ChapterVISignedDyadicComplexRectangle.RealMulTrace sixth argumentCube.output
  fourthTwentyFourth : ChapterVISignedDyadicComplexRectangle.RealMulTrace
    twentyFourth argumentFourth.output
  fifthOneTwenty : ChapterVISignedDyadicComplexRectangle.RealMulTrace oneTwenty argumentFifth.output
  uPolynomial : ChapterVISignedDyadicComplexRectangle.MulTrace base.polar.u.output
    ((((ChapterVISignedDyadicComplexRectangle.pointInt precision 1).add base.argument.output).add
      squareHalf.output).add cubeSixth.output |>.add fourthTwentyFourth.output |>.add
        fifthOneTwenty.output)
  yApprox : ChapterVISignedDyadicComplexRectangle.RealMulTrace zeta uPolynomial.output
  uInvPolynomial : ChapterVISignedDyadicComplexRectangle.MulTrace base.polar.uInv.output
    ((((ChapterVISignedDyadicComplexRectangle.pointInt precision 1).sub base.argument.output).add
      squareHalf.output).sub cubeSixth.output |>.add fourthTwentyFourth.output |>.sub
        fifthOneTwenty.output)
  yInvApprox : ChapterVISignedDyadicComplexRectangle.RealMulTrace base.zetaInv
    uInvPolynomial.output
  argumentNormFourth : Interval precision
  argumentNormSixth : Interval precision
  yRemainderBase : Interval precision
  yError : Interval precision
  yInvRemainderBase : Interval precision
  yInvError : Interval precision

def Trace.operations {precision : ℕ} {zeta radius : Interval precision}
    {unit : Rectangle precision}
    {base : ChapterVILeanCompCertRadicandTrace.Trace zeta radius unit}
    (trace : Trace base) : List (DyadicOperation precision) :=
  [ .positiveReciprocal (ChapterVISignedDyadicInterval.pointInt precision 2) trace.half
  , .positiveReciprocal (ChapterVISignedDyadicInterval.pointInt precision 6) trace.sixth
  , .positiveReciprocal (ChapterVISignedDyadicInterval.pointInt precision 24) trace.twentyFourth
  , .positiveReciprocal (ChapterVISignedDyadicInterval.pointInt precision 120) trace.oneTwenty
  , .positiveReciprocal (ChapterVISignedDyadicInterval.pointInt precision 512) trace.oneFiveTwelve
  ] ++ trace.argumentSquare.operations ++ trace.argumentCube.operations ++
    trace.argumentFourth.operations ++ trace.argumentFifth.operations ++
    trace.squareHalf.operations ++ trace.cubeSixth.operations ++
    trace.fourthTwentyFourth.operations ++ trace.fifthOneTwenty.operations ++
    trace.uPolynomial.operations ++ trace.yApprox.operations ++
    trace.uInvPolynomial.operations ++ trace.yInvApprox.operations ++
    [ .mul base.argumentNormSq base.argumentNormSq trace.argumentNormFourth
    , .mul trace.argumentNormFourth base.argumentNormSq trace.argumentNormSixth
    , .mul base.yScale trace.argumentNormSixth trace.yRemainderBase
    , .mul trace.yRemainderBase trace.oneFiveTwelve trace.yError
    , .mul base.yInvScale trace.argumentNormSixth trace.yInvRemainderBase
    , .mul trace.yInvRemainderBase trace.oneFiveTwelve trace.yInvError ]

def Trace.y {precision : ℕ} {zeta radius : Interval precision}
    {unit : Rectangle precision}
    {base : ChapterVILeanCompCertRadicandTrace.Trace zeta radius unit}
    (trace : Trace base) : Rectangle precision :=
  trace.yApprox.output.widenUpper trace.yError

def Trace.yInv {precision : ℕ} {zeta radius : Interval precision}
    {unit : Rectangle precision}
    {base : ChapterVILeanCompCertRadicandTrace.Trace zeta radius unit}
    (trace : Trace base) : Rectangle precision :=
  trace.yInvApprox.output.widenUpper trace.yInvError

def highOrderTrace {precision : ℕ} {zeta radius : Interval precision}
    {unit : Rectangle precision}
    (base : ChapterVILeanCompCertRadicandTrace.Trace zeta radius unit) : Trace base := by
  let reciprocal (n : ℤ) := ChapterVILeanCompCertProposals.positiveReciprocal precision
    (ChapterVISignedDyadicInterval.pointInt precision n)
  let half := reciprocal 2
  let sixth := reciprocal 6
  let twentyFourth := reciprocal 24
  let oneTwenty := reciprocal 120
  let oneFiveTwelve := reciprocal 512
  let a2 := ChapterVILeanCompCertProposals.mulTrace base.argument.output base.argument.output
  let a3 := ChapterVILeanCompCertProposals.mulTrace a2.output base.argument.output
  let a4 := ChapterVILeanCompCertProposals.mulTrace a3.output base.argument.output
  let a5 := ChapterVILeanCompCertProposals.mulTrace a4.output base.argument.output
  let a2h := ChapterVILeanCompCertProposals.realMulTrace half a2.output
  let a3s := ChapterVILeanCompCertProposals.realMulTrace sixth a3.output
  let a4t := ChapterVILeanCompCertProposals.realMulTrace twentyFourth a4.output
  let a5t := ChapterVILeanCompCertProposals.realMulTrace oneTwenty a5.output
  let one := ChapterVISignedDyadicComplexRectangle.pointInt precision 1
  let positive := ((((one.add base.argument.output).add a2h.output).add a3s.output).add
    a4t.output).add a5t.output
  let negative := ((((one.sub base.argument.output).add a2h.output).sub a3s.output).add
    a4t.output).sub a5t.output
  let uPolynomial := ChapterVILeanCompCertProposals.mulTrace base.polar.u.output positive
  let yApprox := ChapterVILeanCompCertProposals.realMulTrace zeta uPolynomial.output
  let uInvPolynomial := ChapterVILeanCompCertProposals.mulTrace base.polar.uInv.output negative
  let yInvApprox := ChapterVILeanCompCertProposals.realMulTrace base.zetaInv uInvPolynomial.output
  let argumentNormFourth := ChapterVILeanCompCertProposals.mul precision
    base.argumentNormSq base.argumentNormSq
  let argumentNormSixth := ChapterVILeanCompCertProposals.mul precision
    argumentNormFourth base.argumentNormSq
  let yRemainderBase := ChapterVILeanCompCertProposals.mul precision
    base.yScale argumentNormSixth
  let yError := ChapterVILeanCompCertProposals.mul precision yRemainderBase oneFiveTwelve
  let yInvRemainderBase := ChapterVILeanCompCertProposals.mul precision
    base.yInvScale argumentNormSixth
  let yInvError := ChapterVILeanCompCertProposals.mul precision
    yInvRemainderBase oneFiveTwelve
  exact ⟨half, sixth, twentyFourth, oneTwenty, oneFiveTwelve, a2, a3, a4, a5,
    a2h, a3s, a4t, a5t, uPolynomial, yApprox, uInvPolynomial, yInvApprox,
    argumentNormFourth, argumentNormSixth, yRemainderBase, yError,
    yInvRemainderBase, yInvError⟩

theorem Trace.approximations_contain_of_allSound
    {precision : ℕ} {zeta radius : Interval precision} {unit : Rectangle precision}
    {base : ChapterVILeanCompCertRadicandTrace.Trace zeta radius unit}
    (trace : Trace base)
    (hbase : ∀ operation ∈ base.operations, operation.Sound)
    (hall : ∀ operation ∈ trace.operations, operation.Sound)
    {ζ r : ℝ} {v : ℂ} (hζ : zeta.Contains ζ) (hr : radius.Contains r)
    (hv : unit.Contains v) (hvNorm : ‖v‖ = 1)
    (hcoefficient : base.exponentialCoefficient.Contains (100 / 30003 : ℝ)) :
    trace.yApprox.output.Contains
        ((ζ : ℂ) * ((r : ℂ) * v) *
          expPolynomial (chapterVIDRootExponentialArgument ((r : ℂ) * v))) ∧
      trace.yInvApprox.output.Contains
        (((ζ : ℂ)⁻¹) * (((r : ℂ) * v)⁻¹) *
          expInvPolynomial (chapterVIDRootExponentialArgument ((r : ℂ) * v))) := by
  have hsound {operations : List (DyadicOperation precision)}
      (hsub : ∀ operation ∈ operations, operation ∈ trace.operations) :
      ∀ operation ∈ operations, operation.Sound := by
    intro operation hoperation
    exact hall operation (hsub operation hoperation)
  have hpolar : ∀ operation ∈ base.polar.operations, operation.Sound := by
    intro operation hoperation
    exact hbase operation (by
      simp [ChapterVILeanCompCertRadicandTrace.Trace.operations, hoperation])
  rcases base.polar.outputs_contain_of_allSound hpolar hr hv hvNorm with
    ⟨hu, huInv, _, _⟩
  have ha := (base.approximations_contain_of_allSound hbase hζ hr hv hvNorm hcoefficient).1
  have reciprocalContains (n : ℤ) (hn : 0 < n) (output : Interval precision)
      (hop : DyadicOperation.positiveReciprocal
        (ChapterVISignedDyadicInterval.pointInt precision n) output ∈ trace.operations) :
      output.Contains (n : ℝ)⁻¹ := by
    have cert : ChapterVISignedDyadicInterval.PositiveReciprocalCertificate
        (ChapterVISignedDyadicInterval.pointInt precision n) output := hall _ hop
    exact cert.contains_inv (ChapterVISignedDyadicInterval.pointInt_contains precision n)
  have hhalf := reciprocalContains 2 (by norm_num) trace.half (by simp [Trace.operations])
  have hsixth := reciprocalContains 6 (by norm_num) trace.sixth (by simp [Trace.operations])
  have h24 := reciprocalContains 24 (by norm_num) trace.twentyFourth
    (by simp [Trace.operations])
  have h120 := reciprocalContains 120 (by norm_num) trace.oneTwenty
    (by simp [Trace.operations])
  have ha2 := trace.argumentSquare.output_contains_mul_of_allSound
    (hsound (by intro operation hoperation; simp [Trace.operations, hoperation])) ha ha
  have ha3 := trace.argumentCube.output_contains_mul_of_allSound
    (hsound (by intro operation hoperation; simp [Trace.operations, hoperation])) ha2 ha
  have ha4 := trace.argumentFourth.output_contains_mul_of_allSound
    (hsound (by intro operation hoperation; simp [Trace.operations, hoperation])) ha3 ha
  have ha5 := trace.argumentFifth.output_contains_mul_of_allSound
    (hsound (by intro operation hoperation; simp [Trace.operations, hoperation])) ha4 ha
  have ha2h := trace.squareHalf.output_contains_of_allSound
    (hsound (by intro operation hoperation; simp [Trace.operations, hoperation])) hhalf ha2
  have ha3s := trace.cubeSixth.output_contains_of_allSound
    (hsound (by intro operation hoperation; simp [Trace.operations, hoperation])) hsixth ha3
  have ha4t := trace.fourthTwentyFourth.output_contains_of_allSound
    (hsound (by intro operation hoperation; simp [Trace.operations, hoperation])) h24 ha4
  have ha5t := trace.fifthOneTwenty.output_contains_of_allSound
    (hsound (by intro operation hoperation; simp [Trace.operations, hoperation])) h120 ha5
  have hone := ChapterVISignedDyadicComplexRectangle.pointInt_contains precision 1
  let a := chapterVIDRootExponentialArgument ((r : ℂ) * v)
  let positiveBox := ((((ChapterVISignedDyadicComplexRectangle.pointInt precision 1).add
      base.argument.output).add trace.squareHalf.output).add trace.cubeSixth.output |>.add
        trace.fourthTwentyFourth.output).add trace.fifthOneTwenty.output
  let negativeBox := ((((ChapterVISignedDyadicComplexRectangle.pointInt precision 1).sub
      base.argument.output).add trace.squareHalf.output).sub trace.cubeSixth.output |>.add
        trace.fourthTwentyFourth.output).sub trace.fifthOneTwenty.output
  have hpositive : positiveBox.Contains (expPolynomial a) := by
    dsimp [positiveBox, expPolynomial, a]
    convert ChapterVISignedDyadicComplexRectangle.add_contains
      (ChapterVISignedDyadicComplexRectangle.add_contains
        (ChapterVISignedDyadicComplexRectangle.add_contains
          (ChapterVISignedDyadicComplexRectangle.add_contains
            (ChapterVISignedDyadicComplexRectangle.add_contains hone ha) ha2h) ha3s) ha4t) ha5t
      using 1 <;> push_cast <;> ring
  have hnegative : negativeBox.Contains (expInvPolynomial a) := by
    dsimp [negativeBox, expInvPolynomial, a]
    convert ChapterVISignedDyadicComplexRectangle.sub_contains
      (ChapterVISignedDyadicComplexRectangle.add_contains
        (ChapterVISignedDyadicComplexRectangle.sub_contains
          (ChapterVISignedDyadicComplexRectangle.add_contains
            (ChapterVISignedDyadicComplexRectangle.sub_contains hone ha) ha2h) ha3s) ha4t) ha5t
      using 1 <;> push_cast <;> ring
  have huPoly := trace.uPolynomial.output_contains_mul_of_allSound
    (hsound (by intro operation hoperation; simp [Trace.operations, hoperation])) hu hpositive
  have hy := trace.yApprox.output_contains_of_allSound
    (hsound (by intro operation hoperation; simp [Trace.operations, hoperation])) hζ huPoly
  have huInvPoly := trace.uInvPolynomial.output_contains_mul_of_allSound
    (hsound (by intro operation hoperation; simp [Trace.operations, hoperation])) huInv hnegative
  have hζInv := (show ChapterVISignedDyadicInterval.PositiveReciprocalCertificate
      zeta base.zetaInv from hbase (.positiveReciprocal zeta base.zetaInv)
        (by simp [ChapterVILeanCompCertRadicandTrace.Trace.operations])).contains_inv hζ
  have hyInv := trace.yInvApprox.output_contains_of_allSound
    (hsound (by intro operation hoperation; simp [Trace.operations, hoperation])) hζInv huInvPoly
  constructor
  · simpa [a, mul_assoc] using hy
  · simpa [a, mul_assoc] using hyInv

theorem norm_exp_sub_expPolynomial_le {a : ℂ} (ha : ‖a‖ ≤ 1) :
    ‖Complex.exp a - expPolynomial a‖ ≤ ‖a‖ ^ 6 / 512 := by
  have h := Complex.exp_bound ha (n := 6) (by norm_num)
  have hsum : (∑ m ∈ Finset.range 6, a ^ m / m.factorial) = expPolynomial a := by
    simp [expPolynomial, Finset.sum_range_succ, Nat.factorial]
  rw [hsum] at h
  calc
    ‖Complex.exp a - expPolynomial a‖ ≤
        ‖a‖ ^ 6 * ((Nat.succ 6 : ℝ) *
          (((Nat.factorial 6 : ℕ) : ℝ) * (6 : ℝ))⁻¹) := h
    _ ≤ ‖a‖ ^ 6 * (1 / 512 : ℝ) := by
      gcongr
      norm_num [Nat.factorial]
    _ = ‖a‖ ^ 6 / 512 := by ring

theorem norm_exp_neg_sub_expInvPolynomial_le {a : ℂ} (ha : ‖a‖ ≤ 1) :
    ‖Complex.exp (-a) - expInvPolynomial a‖ ≤ ‖a‖ ^ 6 / 512 := by
  have h := norm_exp_sub_expPolynomial_le (a := -a) (by simpa using ha)
  convert h using 1 <;> simp [expPolynomial, expInvPolynomial] <;> ring

theorem Trace.remainder_bounds_of_allSound
    {precision : ℕ} {zeta radius : Interval precision} {unit : Rectangle precision}
    {base : ChapterVILeanCompCertRadicandTrace.Trace zeta radius unit}
    (trace : Trace base)
    (hbase : ∀ operation ∈ base.operations, operation.Sound)
    (hall : ∀ operation ∈ trace.operations, operation.Sound)
    {ζ r : ℝ} {v : ℂ} (hζ : zeta.Contains ζ) (hr : radius.Contains r)
    (hvNorm : ‖v‖ = 1)
    (hcoefficient : base.exponentialCoefficient.Contains (100 / 30003 : ℝ))
    (hζPos : 0 < ζ) (hrPos : 0 < r) :
    ‖(ζ : ℂ)‖ * ‖(r : ℂ) * v‖ *
        (‖chapterVIDRootExponentialArgument ((r : ℂ) * v)‖ ^ 6 / 512) ≤
        (trace.yError.upper : ℝ) / ChapterVISignedDyadicInterval.scale precision ∧
      ‖(ζ : ℂ)⁻¹‖ * ‖((r : ℂ) * v)⁻¹‖ *
        (‖chapterVIDRootExponentialArgument ((r : ℂ) * v)‖ ^ 6 / 512) ≤
        (trace.yInvError.upper : ℝ) / ChapterVISignedDyadicInterval.scale precision := by
  have hnew (operation : DyadicOperation precision) (hop : operation ∈ trace.operations) :=
    hall operation hop
  have hpolar : ∀ operation ∈ base.polar.operations, operation.Sound := by
    intro operation hoperation
    exact hbase operation (by
      simp [ChapterVILeanCompCertRadicandTrace.Trace.operations, hoperation])
  rcases base.polar.radial_outputs_contain_of_allSound hpolar hr with
    ⟨hrInv, hrCube, hrCubeInv⟩
  have hζInv := (show ChapterVISignedDyadicInterval.PositiveReciprocalCertificate
      zeta base.zetaInv from hbase (.positiveReciprocal zeta base.zetaInv)
        (by simp [ChapterVILeanCompCertRadicandTrace.Trace.operations])).contains_inv hζ
  have harg := (show ChapterVISignedDyadicInterval.MulCertificate
      base.exponentialCoefficient (base.polar.radiusCubeInv.add base.polar.radiusCube)
        base.argumentNorm from hbase (.mul base.exponentialCoefficient
          (base.polar.radiusCubeInv.add base.polar.radiusCube) base.argumentNorm)
          (by simp [ChapterVILeanCompCertRadicandTrace.Trace.operations])).contains_mul
      hcoefficient (ChapterVISignedDyadicInterval.add_contains hrCubeInv hrCube)
  have hargSq := (show ChapterVISignedDyadicInterval.MulCertificate
      base.argumentNorm base.argumentNorm base.argumentNormSq from hbase
        (.mul base.argumentNorm base.argumentNorm base.argumentNormSq)
        (by simp [ChapterVILeanCompCertRadicandTrace.Trace.operations])).contains_mul harg harg
  have hargFourth := (show ChapterVISignedDyadicInterval.MulCertificate
      base.argumentNormSq base.argumentNormSq trace.argumentNormFourth from hnew
        (.mul base.argumentNormSq base.argumentNormSq trace.argumentNormFourth)
        (by simp [Trace.operations])).contains_mul hargSq hargSq
  have hargSixth := (show ChapterVISignedDyadicInterval.MulCertificate
      trace.argumentNormFourth base.argumentNormSq trace.argumentNormSixth from hnew
        (.mul trace.argumentNormFourth base.argumentNormSq trace.argumentNormSixth)
        (by simp [Trace.operations])).contains_mul hargFourth hargSq
  have hscale := (show ChapterVISignedDyadicInterval.MulCertificate
      base.yScale trace.argumentNormSixth trace.yRemainderBase from hnew
        (.mul base.yScale trace.argumentNormSixth trace.yRemainderBase)
        (by simp [Trace.operations])).contains_mul
      ((show ChapterVISignedDyadicInterval.MulCertificate zeta radius base.yScale from
        hbase (.mul zeta radius base.yScale)
          (by simp [ChapterVILeanCompCertRadicandTrace.Trace.operations])).contains_mul hζ hr)
      hargSixth
  have hInvScale := (show ChapterVISignedDyadicInterval.MulCertificate
      base.yInvScale trace.argumentNormSixth trace.yInvRemainderBase from hnew
        (.mul base.yInvScale trace.argumentNormSixth trace.yInvRemainderBase)
        (by simp [Trace.operations])).contains_mul
      ((show ChapterVISignedDyadicInterval.MulCertificate
          base.zetaInv base.polar.radiusInv base.yInvScale from
        hbase (.mul base.zetaInv base.polar.radiusInv base.yInvScale)
          (by simp [ChapterVILeanCompCertRadicandTrace.Trace.operations])).contains_mul
          hζInv hrInv) hargSixth
  have h512 : trace.oneFiveTwelve.Contains (512 : ℝ)⁻¹ :=
    (show ChapterVISignedDyadicInterval.PositiveReciprocalCertificate
      (ChapterVISignedDyadicInterval.pointInt precision 512) trace.oneFiveTwelve from
        hnew (.positiveReciprocal
          (ChapterVISignedDyadicInterval.pointInt precision 512) trace.oneFiveTwelve)
          (by simp [Trace.operations])).contains_inv
      (ChapterVISignedDyadicInterval.pointInt_contains precision 512)
  have hyError := (show ChapterVISignedDyadicInterval.MulCertificate
      trace.yRemainderBase trace.oneFiveTwelve trace.yError from hnew
        (.mul trace.yRemainderBase trace.oneFiveTwelve trace.yError)
        (by simp [Trace.operations])).contains_mul hscale h512
  have hyInvError := (show ChapterVISignedDyadicInterval.MulCertificate
      trace.yInvRemainderBase trace.oneFiveTwelve trace.yInvError from hnew
        (.mul trace.yInvRemainderBase trace.oneFiveTwelve trace.yInvError)
        (by simp [Trace.operations])).contains_mul hInvScale h512
  let bound : ℝ := (100 / 30003 : ℝ) * ((r ^ 3)⁻¹ + r ^ 3)
  have hbound : base.argumentNorm.Contains bound := by
    simpa [bound] using harg
  have hboundSq : base.argumentNormSq.Contains (bound ^ 2) := by
    simpa [pow_two] using (show ChapterVISignedDyadicInterval.MulCertificate
      base.argumentNorm base.argumentNorm base.argumentNormSq from hbase
        (.mul base.argumentNorm base.argumentNorm base.argumentNormSq)
        (by simp [ChapterVILeanCompCertRadicandTrace.Trace.operations])).contains_mul hbound hbound
  have hboundFourth : trace.argumentNormFourth.Contains (bound ^ 4) := by
    convert (show ChapterVISignedDyadicInterval.MulCertificate
      base.argumentNormSq base.argumentNormSq trace.argumentNormFourth from hnew
        (.mul base.argumentNormSq base.argumentNormSq trace.argumentNormFourth)
        (by simp [Trace.operations])).contains_mul hboundSq hboundSq using 1 <;> ring
  have hboundSixth : trace.argumentNormSixth.Contains (bound ^ 6) := by
    convert (show ChapterVISignedDyadicInterval.MulCertificate
      trace.argumentNormFourth base.argumentNormSq trace.argumentNormSixth from hnew
        (.mul trace.argumentNormFourth base.argumentNormSq trace.argumentNormSixth)
        (by simp [Trace.operations])).contains_mul hboundFourth hboundSq using 1 <;> ring
  have hnormu : ‖(r : ℂ) * v‖ = r := by
    rw [norm_mul, hvNorm, mul_one]
    simp [abs_of_pos hrPos]
  have haLe := norm_chapterVIDRootExponentialArgument_le ((r : ℂ) * v)
  rw [hnormu] at haLe
  have haSixth :
      ‖chapterVIDRootExponentialArgument ((r : ℂ) * v)‖ ^ 6 ≤ bound ^ 6 := by
    dsimp [bound]
    exact pow_le_pow_left₀ (norm_nonneg _) haLe 6
  have hyUpper : ζ * r * bound ^ 6 * (512 : ℝ)⁻¹ ≤
      (trace.yError.upper : ℝ) / ChapterVISignedDyadicInterval.scale precision := by
    dsimp [bound]
    convert hyError.2 using 1 <;>
      simp [ChapterVISignedDyadicInterval.Contains,
        ChapterVISignedDyadicInterval.toRealInterval] <;> ring <;> simp
  have hyInvUpper : ζ⁻¹ * r⁻¹ * bound ^ 6 * (512 : ℝ)⁻¹ ≤
      (trace.yInvError.upper : ℝ) / ChapterVISignedDyadicInterval.scale precision := by
    dsimp [bound]
    convert hyInvError.2 using 1 <;>
      simp [ChapterVISignedDyadicInterval.Contains,
        ChapterVISignedDyadicInterval.toRealInterval] <;> ring <;> simp
  have hnormζ : ‖(ζ : ℂ)‖ = ζ := by simp [abs_of_pos hζPos]
  have hnormζInv : ‖(ζ : ℂ)⁻¹‖ = ζ⁻¹ := by rw [norm_inv, hnormζ]
  have hnormuInv : ‖((r : ℂ) * v)⁻¹‖ = r⁻¹ := by rw [norm_inv, hnormu]
  constructor
  · rw [hnormζ, hnormu]
    calc
      ζ * r * (‖chapterVIDRootExponentialArgument ((r : ℂ) * v)‖ ^ 6 / 512) ≤
          ζ * r * (bound ^ 6 / 512) := by gcongr
      _ = ζ * r * bound ^ 6 * (512 : ℝ)⁻¹ := by ring
      _ ≤ _ := hyUpper
  · rw [hnormζInv, hnormuInv]
    calc
      ζ⁻¹ * r⁻¹ * (‖chapterVIDRootExponentialArgument ((r : ℂ) * v)‖ ^ 6 / 512) ≤
          ζ⁻¹ * r⁻¹ * (bound ^ 6 / 512) := by gcongr
      _ = ζ⁻¹ * r⁻¹ * bound ^ 6 * (512 : ℝ)⁻¹ := by ring
      _ ≤ _ := hyInvUpper

theorem Trace.anomalies_contain_of_allSound
    {precision : ℕ} {zeta radius : Interval precision} {unit : Rectangle precision}
    {base : ChapterVILeanCompCertRadicandTrace.Trace zeta radius unit}
    (trace : Trace base)
    (hbase : ∀ operation ∈ base.operations, operation.Sound)
    (hall : ∀ operation ∈ trace.operations, operation.Sound)
    {ζ r : ℝ} {v : ℂ} (hζ : zeta.Contains ζ) (hr : radius.Contains r)
    (hv : unit.Contains v) (hvNorm : ‖v‖ = 1)
    (hcoefficient : base.exponentialCoefficient.Contains (100 / 30003 : ℝ))
    (hζPos : 0 < ζ) (hrPos : 0 < r)
    (hargument : ‖chapterVIDRootExponentialArgument ((r : ℂ) * v)‖ ≤ 1) :
    trace.y.Contains (chapterVIDRootSecondAnomaly (ζ : ℂ) ((r : ℂ) * v)) ∧
      trace.yInv.Contains (chapterVIDRootSecondAnomaly (ζ : ℂ) ((r : ℂ) * v))⁻¹ := by
  let u : ℂ := (r : ℂ) * v
  let a : ℂ := chapterVIDRootExponentialArgument u
  rcases trace.approximations_contain_of_allSound hbase hall hζ hr hv hvNorm hcoefficient with
    ⟨hyApprox, hyInvApprox⟩
  rcases trace.remainder_bounds_of_allSound hbase hall hζ hr hvNorm hcoefficient hζPos hrPos with
    ⟨hyError, hyInvError⟩
  constructor
  · apply ChapterVISignedDyadicComplexRectangle.widenUpper_contains_of_norm_sub_le hyApprox
    unfold chapterVIDRootSecondAnomaly chapterVIDRootToOriginalContour
    have heq : (ζ : ℂ) * ((r : ℂ) * v * Complex.exp
          (chapterVIDRootExponentialArgument ((r : ℂ) * v))) -
        (ζ : ℂ) * ((r : ℂ) * v) * expPolynomial
          (chapterVIDRootExponentialArgument ((r : ℂ) * v)) =
        (ζ : ℂ) * ((r : ℂ) * v) *
          (Complex.exp (chapterVIDRootExponentialArgument ((r : ℂ) * v)) -
            expPolynomial (chapterVIDRootExponentialArgument ((r : ℂ) * v))) := by ring
    rw [heq, norm_mul, norm_mul]
    exact (mul_le_mul_of_nonneg_left (norm_exp_sub_expPolynomial_le hargument)
      (mul_nonneg (norm_nonneg (ζ : ℂ)) (norm_nonneg ((r : ℂ) * v)))).trans hyError
  · apply ChapterVISignedDyadicComplexRectangle.widenUpper_contains_of_norm_sub_le hyInvApprox
    have hexact : (chapterVIDRootSecondAnomaly (ζ : ℂ) u)⁻¹ =
        ((ζ : ℂ)⁻¹) * u⁻¹ * Complex.exp (-a) := by
      simp [chapterVIDRootSecondAnomaly, chapterVIDRootToOriginalContour, a,
        mul_inv_rev, Complex.exp_neg, mul_assoc]
      ring
    rw [hexact]
    have heq : (ζ : ℂ)⁻¹ * u⁻¹ * Complex.exp (-a) -
        (ζ : ℂ)⁻¹ * u⁻¹ * expInvPolynomial a =
        (ζ : ℂ)⁻¹ * u⁻¹ * (Complex.exp (-a) - expInvPolynomial a) := by ring
    rw [heq, norm_mul, norm_mul]
    have hmain := mul_le_mul_of_nonneg_left
      (norm_exp_neg_sub_expInvPolynomial_le hargument)
      (mul_nonneg (norm_nonneg (ζ : ℂ)⁻¹) (norm_nonneg u⁻¹))
    exact hmain.trans (by simpa [u, a] using hyInvError)

end ChapterVILeanCompCertHighOrderAnomalyTrace

end

end PoincareChapterVI
