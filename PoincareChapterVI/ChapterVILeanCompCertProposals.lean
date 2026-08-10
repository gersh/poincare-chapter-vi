/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.ChapterVILeanCompCertCartesianRadicandTrace
import PoincareChapterVI.ChapterVIDOuterArcUnitTrace
import PoincareChapterVI.ChapterVIDRadialTrace

/-!
# Untrusted fixed-point trace proposals

These executable definitions keep generated certificate sources small.  They propose outward
rounded endpoints; they do not prove anything.  Every proposed endpoint is subsequently checked
by the signed-product LeanCompCert program, so an error here can only make the verdict nonzero.
-/

namespace PoincareChapterVI

namespace ChapterVILeanCompCertProposals

abbrev Interval (precision : ℕ) := ChapterVISignedDyadicInterval precision
abbrev Rectangle (precision : ℕ) := ChapterVISignedDyadicComplexRectangle precision

def scaleInt (precision : ℕ) : ℤ := 2 ^ precision

def floorDiv (numerator denominator : ℤ) : ℤ := numerator.ediv denominator

def ceilDiv (numerator denominator : ℤ) : ℤ := -((-numerator).ediv denominator)

def mul (precision : ℕ) (x y : Interval precision) : Interval precision :=
  let ll := x.lower * y.lower
  let lu := x.lower * y.upper
  let ul := x.upper * y.lower
  let uu := x.upper * y.upper
  let lower := min (min ll lu) (min ul uu)
  let upper := max (max ll lu) (max ul uu)
  ⟨floorDiv lower (scaleInt precision), ceilDiv upper (scaleInt precision)⟩

def positiveReciprocal (precision : ℕ) (x : Interval precision) : Interval precision :=
  let numerator := scaleInt precision * scaleInt precision
  ⟨floorDiv numerator x.upper, ceilDiv numerator x.lower⟩

/-! ## Soundness of arbitrary-precision outward rounding

These facts deliberately use Lean's mathematical integers.  They are useful when a fixed-point
campaign exceeds the `u64 × u64` range of the optional compiled signed-product checker. -/

private theorem scaleInt_pos (precision : ℕ) : 0 < scaleInt precision := by
  simp [scaleInt]

private theorem floorDiv_mul_le (numerator : ℤ) (precision : ℕ) :
    floorDiv numerator (scaleInt precision) * scaleInt precision ≤ numerator := by
  exact Int.ediv_mul_le numerator (ne_of_gt (scaleInt_pos precision))

private theorem le_ceilDiv_mul (numerator : ℤ) (precision : ℕ) :
    numerator ≤ ceilDiv numerator (scaleInt precision) * scaleInt precision := by
  have h := Int.ediv_mul_le (-numerator) (ne_of_gt (scaleInt_pos precision))
  rw [ceilDiv]
  calc
    numerator = -(-numerator) := by ring
    _ ≤ -((-numerator).ediv (scaleInt precision) * scaleInt precision) := neg_le_neg h
    _ = -((-numerator).ediv (scaleInt precision)) * scaleInt precision := by ring

theorem mul_sound (precision : ℕ) (x y : Interval precision) :
    ChapterVISignedDyadicInterval.MulCertificate x y (mul precision x y) := by
  let ll := x.lower * y.lower
  let lu := x.lower * y.upper
  let ul := x.upper * y.lower
  let uu := x.upper * y.upper
  let lower := min (min ll lu) (min ul uu)
  let upper := max (max ll lu) (max ul uu)
  have hlower : floorDiv lower (scaleInt precision) * scaleInt precision ≤ lower :=
    floorDiv_mul_le lower precision
  have hupper : upper ≤ ceilDiv upper (scaleInt precision) * scaleInt precision :=
    le_ceilDiv_mul upper precision
  have hs : scaleInt precision = (2 ^ precision : ℤ) := rfl
  have hllLower : lower ≤ ll := by simp [lower]
  have hluLower : lower ≤ lu := by simp [lower]
  have hulLower : lower ≤ ul := by simp [lower]
  have huuLower : lower ≤ uu := by simp [lower]
  have hllUpper : ll ≤ upper := by simp [upper]
  have hluUpper : lu ≤ upper := by simp [upper]
  have hulUpper : ul ≤ upper := by simp [upper]
  have huuUpper : uu ≤ upper := by simp [upper]
  change ChapterVISignedDyadicInterval.MulCertificate x y
    ⟨floorDiv lower (scaleInt precision), ceilDiv upper (scaleInt precision)⟩
  refine
    { output_wf := ?_
      lower_ll := ?_, lower_lu := ?_, lower_ul := ?_, lower_uu := ?_
      upper_ll := ?_, upper_lu := ?_, upper_ul := ?_, upper_uu := ?_ }
  · exact le_of_mul_le_mul_right
      (hlower.trans (hllLower.trans (hllUpper.trans hupper)))
      (scaleInt_pos precision)
  · rw [← hs]; exact hlower.trans hllLower
  · rw [← hs]; exact hlower.trans hluLower
  · rw [← hs]; exact hlower.trans hulLower
  · rw [← hs]; exact hlower.trans huuLower
  · rw [← hs]; exact hllUpper.trans hupper
  · rw [← hs]; exact hluUpper.trans hupper
  · rw [← hs]; exact hulUpper.trans hupper
  · rw [← hs]; exact huuUpper.trans hupper

theorem positiveReciprocal_sound (precision : ℕ) (x : Interval precision)
    (hlower : 0 < x.lower) (hwf : x.lower ≤ x.upper) :
    ChapterVISignedDyadicInterval.PositiveReciprocalCertificate x
      (positiveReciprocal precision x) := by
  let scale := scaleInt precision
  let numerator := scale * scale
  have hscale : 0 < scale := scaleInt_pos precision
  have hupper : 0 < x.upper := hlower.trans_le hwf
  have hnumerator : 0 ≤ numerator := mul_nonneg hscale.le hscale.le
  have houtLower : 0 ≤ floorDiv numerator x.upper := by
    exact Int.ediv_nonneg hnumerator hupper.le
  have hlowerCross : floorDiv numerator x.upper * x.upper ≤ numerator :=
    Int.ediv_mul_le numerator hupper.ne'
  have hupperCross : numerator ≤ ceilDiv numerator x.lower * x.lower := by
    have h := Int.ediv_mul_le (-numerator) hlower.ne'
    rw [ceilDiv]
    calc
      numerator = -(-numerator) := by ring
      _ ≤ -((-numerator).ediv x.lower * x.lower) := neg_le_neg h
      _ = -((-numerator).ediv x.lower) * x.lower := by ring
  have houtputWf : floorDiv numerator x.upper ≤ ceilDiv numerator x.lower := by
    apply le_of_mul_le_mul_right _ hlower
    exact calc
      floorDiv numerator x.upper * x.lower ≤
          floorDiv numerator x.upper * x.upper :=
        mul_le_mul_of_nonneg_left hwf houtLower
      _ ≤ numerator := hlowerCross
      _ ≤ ceilDiv numerator x.lower * x.lower := hupperCross
  change ChapterVISignedDyadicInterval.PositiveReciprocalCertificate x
    ⟨floorDiv numerator x.upper, ceilDiv numerator x.lower⟩
  refine
    { input_lower_pos := hlower
      output_wf := houtputWf
      output_lower_nonneg := houtLower
      lower_cross := ?_
      upper_cross := ?_ }
  · simpa [numerator, scale, scaleInt, pow_two] using hlowerCross
  · simpa [numerator, scale, scaleInt, pow_two] using hupperCross

def realMulTrace {precision : ℕ} (scalar : Interval precision)
    (input : Rectangle precision) :
    ChapterVISignedDyadicComplexRectangle.RealMulTrace scalar input where
  realOut := mul precision scalar input.real
  imagOut := mul precision scalar input.imag

def lineMapTrace {precision : ℕ} (source target : Rectangle precision)
    (parameter : Interval precision) :
    ChapterVISignedDyadicComplexRectangle.LineMapTrace source target parameter :=
  ⟨realMulTrace parameter (target.sub source)⟩

def mulTrace {precision : ℕ} (x y : Rectangle precision) :
    ChapterVISignedDyadicComplexRectangle.MulTrace x y where
  realReal := mul precision x.real y.real
  imagImag := mul precision x.imag y.imag
  realImag := mul precision x.real y.imag
  imagReal := mul precision x.imag y.real

def invTrace {precision : ℕ} (input : Rectangle precision) :
    ChapterVISignedDyadicComplexRectangle.InvTrace input :=
  let realSq := mul precision input.real input.real
  let imagSq := mul precision input.imag input.imag
  let normInv := positiveReciprocal precision (realSq.add imagSq)
  ⟨realSq, imagSq, normInv,
    mul precision input.real normInv,
    mul precision input.imag.neg normInv⟩

theorem mulTrace_operations_sound {precision : ℕ} (x y : Rectangle precision) :
    ∀ operation ∈ (mulTrace x y).operations, operation.Sound := by
  intro operation hoperation
  simp [mulTrace, ChapterVISignedDyadicComplexRectangle.MulTrace.operations] at hoperation
  rcases hoperation with rfl | rfl | rfl | rfl
  all_goals exact mul_sound precision _ _

theorem invTrace_operations_sound {precision : ℕ} (input : Rectangle precision)
    (hnorm : 0 < (invTrace input).normSq.lower) :
    ∀ operation ∈ (invTrace input).operations, operation.Sound := by
  have hre := mul_sound precision input.real input.real
  have him := mul_sound precision input.imag input.imag
  have hnormWf : (invTrace input).normSq.lower ≤ (invTrace input).normSq.upper := by
    change (mul precision input.real input.real).lower +
        (mul precision input.imag input.imag).lower ≤
      (mul precision input.real input.real).upper +
        (mul precision input.imag input.imag).upper
    exact add_le_add hre.output_wf him.output_wf
  intro operation hoperation
  simp [invTrace, ChapterVISignedDyadicComplexRectangle.InvTrace.operations] at hoperation
  rcases hoperation with rfl | rfl | rfl | rfl | rfl
  · exact hre
  · exact him
  · exact positiveReciprocal_sound precision _ hnorm hnormWf
  all_goals exact mul_sound precision _ _

/-- An exact integer budget for the absolute value of every number in a dyadic interval. -/
def componentBudget {precision : ℕ} (input : Interval precision) : ℤ :=
  max (max 0 (-input.lower)) input.upper

/-- The automatically proposed L1 norm interval for a complex rectangle. -/
def l1NormInterval {precision : ℕ} (input : Rectangle precision) : Interval precision :=
  ⟨0, componentBudget input.real + componentBudget input.imag⟩

/-- The proposed L1 norm interval is sound by construction; unlike rounded arithmetic, this
small fact is proved directly by exact integer order reasoning. -/
def l1NormBound {precision : ℕ} (input : Rectangle precision) :
    input.L1NormBound (l1NormInterval input) := by
  refine {
    realBudget := componentBudget input.real
    imagBudget := componentBudget input.imag
    realBudget_nonneg := ?_
    imagBudget_nonneg := ?_
    real_lower := ?_
    real_upper := ?_
    imag_lower := ?_
    imag_upper := ?_
    output_lower_nonpos := ?_
    budget_le_output := ?_ }
  all_goals simp [componentBudget, l1NormInterval] <;> omega

def cubeTrace {precision : ℕ} (input : Rectangle precision) :
    ChapterVISignedDyadicComplexRectangle.CubeTrace input :=
  let square := mulTrace input input
  ⟨square, mulTrace square.output input⟩

def outerUnitTrace {precision : ℕ} (t : Interval precision) :
    ChapterVIDOuterArcUnitTrace.Trace t :=
  let one := ChapterVISignedDyadicInterval.pointInt precision 1
  let two := ChapterVISignedDyadicInterval.pointInt precision 2
  let tSq := mul precision t t
  let denominatorInv := positiveReciprocal precision (one.add tSq)
  let twoT := mul precision two t
  let realOut := mul precision (one.sub tSq) denominatorInv
  let imagOut := mul precision twoT denominatorInv
  ⟨tSq, denominatorInv, twoT, realOut, imagOut⟩

def powThreeTrace {precision : ℕ} (input : Interval precision) :
    ChapterVILeanCompCertRoots.PowThreeTrace input :=
  let square := mul precision input input
  ⟨square, mul precision square input⟩

def powSixTrace {precision : ℕ} (input : Interval precision) :
    ChapterVILeanCompCertRoots.PowSixTrace input :=
  let square := mul precision input input
  let cube := mul precision square input
  ⟨square, cube, mul precision cube cube⟩

def cubicRootTrace {precision : ℕ} (input output : Interval precision) :
    ChapterVILeanCompCertRoots.CubicRootTrace input output :=
  ⟨powThreeTrace (ChapterVILeanCompCertRoots.endpoint output.lower),
    powThreeTrace (ChapterVILeanCompCertRoots.endpoint output.upper)⟩

def sixthRootTrace {precision : ℕ} (input output : Interval precision) :
    ChapterVILeanCompCertRoots.SixthRootTrace input output :=
  ⟨powSixTrace (ChapterVILeanCompCertRoots.endpoint output.lower),
    powSixTrace (ChapterVILeanCompCertRoots.endpoint output.upper)⟩

theorem powThreeTrace_operations_sound {precision : ℕ} (input : Interval precision) :
    ∀ operation ∈ (powThreeTrace input).operations, operation.Sound := by
  intro operation hoperation
  simp [powThreeTrace, ChapterVILeanCompCertRoots.PowThreeTrace.operations] at hoperation
  rcases hoperation with rfl | rfl
  all_goals exact mul_sound precision _ _

theorem powSixTrace_operations_sound {precision : ℕ} (input : Interval precision) :
    ∀ operation ∈ (powSixTrace input).operations, operation.Sound := by
  intro operation hoperation
  simp [powSixTrace, ChapterVILeanCompCertRoots.PowSixTrace.operations] at hoperation
  rcases hoperation with rfl | rfl | rfl
  all_goals exact mul_sound precision _ _

theorem cubicRootTrace_operations_sound {precision : ℕ} (input output : Interval precision) :
    ∀ operation ∈ (cubicRootTrace input output).operations, operation.Sound := by
  intro operation hoperation
  change operation ∈
    (powThreeTrace (ChapterVILeanCompCertRoots.endpoint output.lower)).operations ++
      (powThreeTrace (ChapterVILeanCompCertRoots.endpoint output.upper)).operations at hoperation
  rcases List.mem_append.mp hoperation with h | h
  all_goals exact powThreeTrace_operations_sound _ operation h

theorem sixthRootTrace_operations_sound {precision : ℕ} (input output : Interval precision) :
    ∀ operation ∈ (sixthRootTrace input output).operations, operation.Sound := by
  intro operation hoperation
  change operation ∈
    (powSixTrace (ChapterVILeanCompCertRoots.endpoint output.lower)).operations ++
      (powSixTrace (ChapterVILeanCompCertRoots.endpoint output.upper)).operations at hoperation
  rcases List.mem_append.mp hoperation with h | h
  all_goals exact powSixTrace_operations_sound _ operation h

def radialEndpointTrace {precision : ℕ} (qD qDSixthRoot xAbs collisionRadius : Interval precision) :
    ChapterVIDRadialTrace.EndpointTrace (precision := precision) :=
  let qDSixthTrace := sixthRootTrace qD qDSixthRoot
  let collisionTrace := cubicRootTrace xAbs collisionRadius
  let qDSixthInv := positiveReciprocal precision qDSixthRoot
  let correction := mul precision collisionRadius qDSixthInv
  ⟨qD, qDSixthRoot, qDSixthTrace, xAbs, collisionRadius, collisionTrace,
    qDSixthInv, correction⟩

def radialTrace {precision : ℕ} (endpoint : ChapterVIDRadialTrace.EndpointTrace)
    (input qCubeRoot qSixthRoot : Interval precision) :
    ChapterVIDRadialTrace.Trace endpoint input :=
  let one := ChapterVISignedDyadicInterval.pointInt precision 1
  let qDeltaProduct := mul precision input (endpoint.qD.sub one)
  let q := one.add qDeltaProduct
  let qCubeTrace := cubicRootTrace q qCubeRoot
  let qSixthTrace := sixthRootTrace q qSixthRoot
  let correctionDeltaProduct := mul precision input (endpoint.correction.sub one)
  let correctionFactor := one.add correctionDeltaProduct
  let radius := mul precision qSixthRoot correctionFactor
  ⟨qDeltaProduct, qCubeRoot, qCubeTrace, qSixthRoot, qSixthTrace,
    correctionDeltaProduct, radius⟩

def polarTrace {precision : ℕ} (radius : Interval precision) (unit : Rectangle precision) :
    ChapterVILeanCompCertPolarTrace.Trace radius unit :=
  let radiusInv := positiveReciprocal precision radius
  let radiusSq := mul precision radius radius
  let radiusCube := mul precision radiusSq radius
  let radiusCubeInv := positiveReciprocal precision radiusCube
  let unitCube := cubeTrace unit
  let u := realMulTrace radius unit
  let uInv := realMulTrace radiusInv unit.conjugate
  let uCube := realMulTrace radiusCube unitCube.output
  let uCubeInv := realMulTrace radiusCubeInv unitCube.output.conjugate
  ⟨radiusInv, radiusSq, radiusCube, radiusCubeInv, unitCube, u, uInv, uCube, uCubeInv⟩

def radicandTrace {precision : ℕ} (zeta radius : Interval precision)
    (unit : Rectangle precision) (exponentialCoefficient inverse10001 : Interval precision) :
    ChapterVILeanCompCertRadicandTrace.Trace zeta radius unit :=
  let polar := polarTrace radius unit
  let zetaInv := positiveReciprocal precision zeta
  let argument := realMulTrace exponentialCoefficient
    (polar.uCubeInv.output.sub polar.uCube.output)
  let one := ChapterVISignedDyadicComplexRectangle.pointInt precision 1
  let uLinear := mulTrace polar.u.output (one.add argument.output)
  let yApprox := realMulTrace zeta uLinear.output
  let uInvLinear := mulTrace polar.uInv.output (one.sub argument.output)
  let yInvApprox := realMulTrace zetaInv uInvLinear.output
  let argumentNorm := mul precision exponentialCoefficient
    (polar.radiusCubeInv.add polar.radiusCube)
  let argumentNormSq := mul precision argumentNorm argumentNorm
  let yScale := mul precision zeta radius
  let yError := mul precision yScale argumentNormSq
  let yInvScale := mul precision zetaInv polar.radiusInv
  let yInvError := mul precision yInvScale argumentNormSq
  let plusInput := ((polar.uCube.output.nsmul 10000).add polar.uCubeInv.output).add
    (ChapterVISignedDyadicComplexRectangle.pointInt precision (-200))
  let minusInput := (polar.uCube.output.add (polar.uCubeInv.output.nsmul 10000)).add
    (ChapterVISignedDyadicComplexRectangle.pointInt precision (-200))
  let laurentPlus := realMulTrace inverse10001 plusInput
  let laurentMinus := realMulTrace inverse10001 minusInput
  let y := yApprox.output.widenUpper yError
  let yInv := yInvApprox.output.widenUpper yInvError
  let product := mulTrace (laurentPlus.output.sub (y.nsmul 2))
    (laurentMinus.output.sub (yInv.nsmul 2))
  ⟨exponentialCoefficient, inverse10001, polar, zetaInv, argument, uLinear,
    yApprox, uInvLinear, yInvApprox, argumentNorm, argumentNormSq, yScale, yError,
    yInvScale, yInvError, laurentPlus, laurentMinus, product⟩

/-- Propose the complete Cartesian connector trace as pure data. The exponential-argument
budget is an ordinary raw claim in `Trace.operations`; an over-wide rectangle therefore produces
a nonzero compiled verdict instead of preventing construction of the trace. -/
def cartesianRadicandTrace {precision : ℕ} (zeta coordinate : Rectangle precision)
    (exponentialCoefficient inverse10001 : Interval precision) :
    ChapterVILeanCompCertCartesianRadicandTrace.Trace zeta coordinate :=
  let zetaInv := invTrace zeta
  let coordinateInv := invTrace coordinate
  let coordinateCube := cubeTrace coordinate
  let coordinateInvCube := cubeTrace coordinateInv.output
  let argument := realMulTrace exponentialCoefficient
    (coordinateInvCube.output.sub coordinateCube.output)
  let one := ChapterVISignedDyadicComplexRectangle.pointInt precision 1
  let coordinateLinear := mulTrace coordinate (one.add argument.output)
  let yApprox := mulTrace zeta coordinateLinear.output
  let coordinateInvLinear := mulTrace coordinateInv.output (one.sub argument.output)
  let yInvApprox := mulTrace zetaInv.output coordinateInvLinear.output
  let zetaNorm := l1NormInterval zeta
  let coordinateNorm := l1NormInterval coordinate
  let zetaInvNorm := l1NormInterval zetaInv.output
  let coordinateInvNorm := l1NormInterval coordinateInv.output
  let argumentNorm := l1NormInterval argument.output
  let argumentNormSq := mul precision argumentNorm argumentNorm
  let yScale := mul precision zetaNorm coordinateNorm
  let yError := mul precision yScale argumentNormSq
  let yInvScale := mul precision zetaInvNorm coordinateInvNorm
  let yInvError := mul precision yInvScale argumentNormSq
  let plusInput :=
    ((coordinateCube.output.nsmul 10000).add coordinateInvCube.output).add
      (ChapterVISignedDyadicComplexRectangle.pointInt precision (-200))
  let minusInput :=
    (coordinateCube.output.add (coordinateInvCube.output.nsmul 10000)).add
      (ChapterVISignedDyadicComplexRectangle.pointInt precision (-200))
  let laurentPlus := realMulTrace inverse10001 plusInput
  let laurentMinus := realMulTrace inverse10001 minusInput
  let y := yApprox.output.widenUpper yError
  let yInv := yInvApprox.output.widenUpper yInvError
  let product := mulTrace (laurentPlus.output.sub (y.nsmul 2))
    (laurentMinus.output.sub (yInv.nsmul 2))
  {
    exponentialCoefficient := exponentialCoefficient
    inverse10001 := inverse10001
    zetaInv := zetaInv
    coordinateInv := coordinateInv
    coordinateCube := coordinateCube
    coordinateInvCube := coordinateInvCube
    argument := argument
    coordinateLinear := coordinateLinear
    yApprox := yApprox
    coordinateInvLinear := coordinateInvLinear
    yInvApprox := yInvApprox
    zetaNorm := zetaNorm
    coordinateNorm := coordinateNorm
    zetaInvNorm := zetaInvNorm
    coordinateInvNorm := coordinateInvNorm
    argumentNorm := argumentNorm
    zetaNormBound := l1NormBound zeta
    coordinateNormBound := l1NormBound coordinate
    zetaInvNormBound := l1NormBound zetaInv.output
    coordinateInvNormBound := l1NormBound coordinateInv.output
    argumentNormBound := l1NormBound argument.output
    argumentNormSq := argumentNormSq
    yScale := yScale
    yError := yError
    yInvScale := yInvScale
    yInvError := yInvError
    laurentPlus := laurentPlus
    laurentMinus := laurentMinus
    product := product }

/-- Compatibility wrapper for existing callers. Trace construction is total; all rejection
conditions now appear in the compiled claim batch. -/
def cartesianRadicandTrace? {precision : ℕ} (zeta coordinate : Rectangle precision)
    (exponentialCoefficient inverse10001 : Interval precision) :
    Option (ChapterVILeanCompCertCartesianRadicandTrace.Trace zeta coordinate) :=
  some (cartesianRadicandTrace zeta coordinate exponentialCoefficient inverse10001)

end ChapterVILeanCompCertProposals

end PoincareChapterVI
