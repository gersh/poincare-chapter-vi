/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.ChapterVILeanCompCertCartesianFactorDerivativeTrace

/-!
# Dependency-preserving compiled trace for the D-connector derivative

The earlier Cartesian derivative trace evaluates three large absolute terms and loses their
common zero at Poincare's collision point.  This trace evaluates the exact base-centered formula
instead.  Its primitive inputs include `u-D`, `ζ/ζ_D-1`, and `exp(A(u)-A(D))-1`; every terminal
quantity that must become small therefore remains visibly multiplied by its common scale.
-/

namespace PoincareChapterVI
namespace ChapterVILeanCompCertDependencyPreservingFactorDerivativeTrace

open ChapterVILeanCompCertBatch

abbrev Rectangle (precision : ℕ) := ChapterVISignedDyadicComplexRectangle precision

namespace Rectangle

abbrev MulTrace {precision : ℕ} (x y : Rectangle precision) :=
  ChapterVISignedDyadicComplexRectangle.MulTrace x y
abbrev InvTrace {precision : ℕ} (x : Rectangle precision) :=
  ChapterVISignedDyadicComplexRectangle.InvTrace x
abbrev CubeTrace {precision : ℕ} (x : Rectangle precision) :=
  ChapterVISignedDyadicComplexRectangle.CubeTrace x
abbrev RealMulTrace {precision : ℕ}
    (r : ChapterVISignedDyadicInterval precision) (x : Rectangle precision) :=
  ChapterVISignedDyadicComplexRectangle.RealMulTrace r x

abbrev pointInt := ChapterVISignedDyadicComplexRectangle.pointInt

end Rectangle

/-- Rounded intermediates for the exact dependency-preserving path derivative.  The rectangles
for the constants at `D` are inputs so that a concrete campaign can reuse one ultrafine algebraic
root certificate across every cell. -/
structure Trace {precision : ℕ}
    (coordinate coordinateDelta zetaDelta expDelta direction : Rectangle precision)
    (collision collisionInv collisionSquare collisionInvCube collisionInvFourth
      yBase : Rectangle precision)
    (inverse10001 coefficient200 : ChapterVISignedDyadicInterval precision) where
  zetaDeltaTimesExp : Rectangle.MulTrace zetaDelta
    ((Rectangle.pointInt precision 1).add expDelta)
  coordinateSquare : Rectangle.MulTrace coordinate coordinate
  coordinateCube : Rectangle.MulTrace coordinateSquare.output coordinate
  coordinateInv : Rectangle.InvTrace coordinate
  coordinateInvCube : Rectangle.CubeTrace coordinateInv.output
  coordinateInvFourth : Rectangle.MulTrace coordinateInvCube.output coordinateInv.output
  deltaTimesSum : Rectangle.MulTrace coordinateDelta (coordinate.add collision)
  inverseFourthProduct : Rectangle.MulTrace coordinateInvFourth.output collisionInvFourth
  inverseCorrection : Rectangle.MulTrace inverseFourthProduct.output
    (coordinateSquare.output.add collisionSquare)
  laurentCore : Rectangle.MulTrace deltaTimesSum.output
    ((Rectangle.pointInt precision 30000).add (inverseCorrection.output.nsmul 3))
  laurent : Rectangle.RealMulTrace inverse10001 laurentCore.output
  shapeInv : Rectangle.MulTrace collisionInv coordinateInvCube.output
  shapeCube : Rectangle.MulTrace coordinateCube.output collisionInv
  coordinateTimesCollision : Rectangle.MulTrace coordinate collision
  deltaTimesQuadratic : Rectangle.MulTrace coordinateDelta
    ((coordinateSquare.output.add coordinateTimesCollision.output).add collisionSquare)
  deltaQuadraticOverCollision : Rectangle.MulTrace deltaTimesQuadratic.output collisionInv
  inverseCubeProduct : Rectangle.MulTrace coordinateInvCube.output collisionInvCube
  shapeDifference : Rectangle.MulTrace deltaQuadraticOverCollision.output
    ((Rectangle.pointInt precision 1).sub inverseCubeProduct.output)
  multiplierTimesShape : Rectangle.MulTrace
    (zetaDeltaTimesExp.output.add expDelta) (shapeInv.output.add shapeCube.output)
  yTimesPowerDifference : Rectangle.MulTrace yBase
    (multiplierTimesShape.output.add shapeDifference.output)
  powerDifference : Rectangle.RealMulTrace coefficient200 yTimesPowerDifference.output
  yOverCollision : Rectangle.MulTrace yBase collisionInv
  quotientDifference : Rectangle.MulTrace yOverCollision.output
    (zetaDeltaTimesExp.output.add expDelta)
  pathDerivative : Rectangle.MulTrace
    ((laurent.output.sub (quotientDifference.output.nsmul 2)).add powerDifference.output)
    direction

def Trace.parts {precision : ℕ}
    {coordinate coordinateDelta zetaDelta expDelta direction : Rectangle precision}
    {collision collisionInv collisionSquare collisionInvCube collisionInvFourth
      yBase : Rectangle precision}
    {inverse10001 coefficient200 : ChapterVISignedDyadicInterval precision}
    (trace : Trace coordinate coordinateDelta zetaDelta expDelta direction collision
      collisionInv collisionSquare collisionInvCube collisionInvFourth yBase
      inverse10001 coefficient200) : List (List (DyadicOperation precision)) :=
  [ trace.zetaDeltaTimesExp.operations
  , trace.coordinateSquare.operations
  , trace.coordinateCube.operations
  , trace.coordinateInv.operations
  , trace.coordinateInvCube.operations
  , trace.coordinateInvFourth.operations
  , trace.deltaTimesSum.operations
  , trace.inverseFourthProduct.operations
  , trace.inverseCorrection.operations
  , trace.laurentCore.operations
  , trace.laurent.operations
  , trace.shapeInv.operations
  , trace.shapeCube.operations
  , trace.coordinateTimesCollision.operations
  , trace.deltaTimesQuadratic.operations
  , trace.deltaQuadraticOverCollision.operations
  , trace.inverseCubeProduct.operations
  , trace.shapeDifference.operations
  , trace.multiplierTimesShape.operations
  , trace.yTimesPowerDifference.operations
  , trace.powerDifference.operations
  , trace.yOverCollision.operations
  , trace.quotientDifference.operations
  , trace.pathDerivative.operations ]

def Trace.operations {precision : ℕ}
    {coordinate coordinateDelta zetaDelta expDelta direction : Rectangle precision}
    {collision collisionInv collisionSquare collisionInvCube collisionInvFourth
      yBase : Rectangle precision}
    {inverse10001 coefficient200 : ChapterVISignedDyadicInterval precision}
    (trace : Trace coordinate coordinateDelta zetaDelta expDelta direction collision
      collisionInv collisionSquare collisionInvCube collisionInvFourth yBase
      inverse10001 coefficient200) : List (DyadicOperation precision) :=
  trace.parts.flatten

def Trace.output {precision : ℕ}
    {coordinate coordinateDelta zetaDelta expDelta direction : Rectangle precision}
    {collision collisionInv collisionSquare collisionInvCube collisionInvFourth
      yBase : Rectangle precision}
    {inverse10001 coefficient200 : ChapterVISignedDyadicInterval precision}
    (trace : Trace coordinate coordinateDelta zetaDelta expDelta direction collision
      collisionInv collisionSquare collisionInvCube collisionInvFourth yBase
      inverse10001 coefficient200) : Rectangle precision :=
  trace.pathDerivative.output

/-- Deterministic outward-rounded proposal for the dependency-preserving trace.  This definition
is untrusted numerical data generation: every rounded product and reciprocal it proposes is
rechecked by the compiled LeanCompCert batch before `Trace.output_contains_of_allSound` may use
it. -/
def dependencyPreservingTrace {precision : ℕ}
    (coordinate coordinateDelta zetaDelta expDelta direction : Rectangle precision)
    (collision collisionInv collisionSquare collisionInvCube collisionInvFourth
      yBase : Rectangle precision)
    (inverse10001 coefficient200 : ChapterVISignedDyadicInterval precision) :
    Trace coordinate coordinateDelta zetaDelta expDelta direction collision
      collisionInv collisionSquare collisionInvCube collisionInvFourth yBase
      inverse10001 coefficient200 :=
  let one := Rectangle.pointInt precision 1
  let zetaDeltaTimesExp := ChapterVILeanCompCertProposals.mulTrace zetaDelta (one.add expDelta)
  let coordinateSquare := ChapterVILeanCompCertProposals.mulTrace coordinate coordinate
  let coordinateCube := ChapterVILeanCompCertProposals.mulTrace coordinateSquare.output coordinate
  let coordinateInv := ChapterVILeanCompCertProposals.invTrace coordinate
  let coordinateInvCube := ChapterVILeanCompCertProposals.cubeTrace coordinateInv.output
  let coordinateInvFourth := ChapterVILeanCompCertProposals.mulTrace
    coordinateInvCube.output coordinateInv.output
  let deltaTimesSum := ChapterVILeanCompCertProposals.mulTrace
    coordinateDelta (coordinate.add collision)
  let inverseFourthProduct := ChapterVILeanCompCertProposals.mulTrace
    coordinateInvFourth.output collisionInvFourth
  let inverseCorrection := ChapterVILeanCompCertProposals.mulTrace
    inverseFourthProduct.output (coordinateSquare.output.add collisionSquare)
  let laurentCore := ChapterVILeanCompCertProposals.mulTrace deltaTimesSum.output
    ((Rectangle.pointInt precision 30000).add (inverseCorrection.output.nsmul 3))
  let laurent := ChapterVILeanCompCertProposals.realMulTrace inverse10001 laurentCore.output
  let shapeInv := ChapterVILeanCompCertProposals.mulTrace collisionInv coordinateInvCube.output
  let shapeCube := ChapterVILeanCompCertProposals.mulTrace coordinateCube.output collisionInv
  let coordinateTimesCollision := ChapterVILeanCompCertProposals.mulTrace coordinate collision
  let deltaTimesQuadratic := ChapterVILeanCompCertProposals.mulTrace coordinateDelta
    ((coordinateSquare.output.add coordinateTimesCollision.output).add collisionSquare)
  let deltaQuadraticOverCollision := ChapterVILeanCompCertProposals.mulTrace
    deltaTimesQuadratic.output collisionInv
  let inverseCubeProduct := ChapterVILeanCompCertProposals.mulTrace
    coordinateInvCube.output collisionInvCube
  let shapeDifference := ChapterVILeanCompCertProposals.mulTrace
    deltaQuadraticOverCollision.output (one.sub inverseCubeProduct.output)
  let multiplierTimesShape := ChapterVILeanCompCertProposals.mulTrace
    (zetaDeltaTimesExp.output.add expDelta) (shapeInv.output.add shapeCube.output)
  let yTimesPowerDifference := ChapterVILeanCompCertProposals.mulTrace yBase
    (multiplierTimesShape.output.add shapeDifference.output)
  let powerDifference := ChapterVILeanCompCertProposals.realMulTrace
    coefficient200 yTimesPowerDifference.output
  let yOverCollision := ChapterVILeanCompCertProposals.mulTrace yBase collisionInv
  let quotientDifference := ChapterVILeanCompCertProposals.mulTrace
    yOverCollision.output (zetaDeltaTimesExp.output.add expDelta)
  let pathDerivative := ChapterVILeanCompCertProposals.mulTrace
    ((laurent.output.sub (quotientDifference.output.nsmul 2)).add powerDifference.output)
    direction
  { zetaDeltaTimesExp := zetaDeltaTimesExp
    coordinateSquare := coordinateSquare
    coordinateCube := coordinateCube
    coordinateInv := coordinateInv
    coordinateInvCube := coordinateInvCube
    coordinateInvFourth := coordinateInvFourth
    deltaTimesSum := deltaTimesSum
    inverseFourthProduct := inverseFourthProduct
    inverseCorrection := inverseCorrection
    laurentCore := laurentCore
    laurent := laurent
    shapeInv := shapeInv
    shapeCube := shapeCube
    coordinateTimesCollision := coordinateTimesCollision
    deltaTimesQuadratic := deltaTimesQuadratic
    deltaQuadraticOverCollision := deltaQuadraticOverCollision
    inverseCubeProduct := inverseCubeProduct
    shapeDifference := shapeDifference
    multiplierTimesShape := multiplierTimesShape
    yTimesPowerDifference := yTimesPowerDifference
    powerDifference := powerDifference
    yOverCollision := yOverCollision
    quotientDifference := quotientDifference
    pathDerivative := pathDerivative }

/-- Semantic reconstruction of the exact dependency-preserving path derivative from a successful
integer batch.  Bounds for the small exponential delta and algebraic base constants are supplied
by their dedicated analytic/algebraic bridges; all subsequent arithmetic is reconstructed here. -/
theorem Trace.output_contains_of_allSound
    {precision : ℕ}
    {coordinate coordinateDelta zetaDelta expDelta direction : Rectangle precision}
    {collision collisionInv collisionSquare collisionInvCube collisionInvFourth
      yBase : Rectangle precision}
    {inverse10001 coefficient200 : ChapterVISignedDyadicInterval precision}
    (trace : Trace coordinate coordinateDelta zetaDelta expDelta direction collision
      collisionInv collisionSquare collisionInvCube collisionInvFourth yBase
      inverse10001 coefficient200)
    (hall : ∀ operation ∈ trace.operations, operation.Sound)
    {ζ u Δexp pathDirection : ℂ}
    (hu : coordinate.Contains u)
    (huDelta : coordinateDelta.Contains (u - chapterVIDCollisionLift))
    (hζDelta : zetaDelta.Contains (ζ / chapterVIDZRootBase - 1))
    (hExpDelta : expDelta.Contains Δexp)
    (hΔexp : Δexp = Complex.exp
      (chapterVIDRootExponentialArgument u -
        chapterVIDRootExponentialArgument chapterVIDCollisionLift) - 1)
    (hDirection : direction.Contains pathDirection)
    (hCollision : collision.Contains chapterVIDCollisionLift)
    (hCollisionInv : collisionInv.Contains chapterVIDCollisionLift⁻¹)
    (hCollisionSquare : collisionSquare.Contains (chapterVIDCollisionLift ^ 2))
    (hCollisionInvCube : collisionInvCube.Contains (chapterVIDCollisionLift⁻¹ ^ 3))
    (hCollisionInvFourth : collisionInvFourth.Contains (chapterVIDCollisionLift⁻¹ ^ 4))
    (hYBase : yBase.Contains chapterVIDY)
    (hInverse10001 : inverse10001.Contains (1 / 10001 : ℝ))
    (hCoefficient200 : coefficient200.Contains (200 / 10001 : ℝ)) :
    trace.output.Contains
      (chapterVIDRootFactorDerivativeDependencyPreserving ζ u * pathDirection) := by
  have soundPart (operations : List (DyadicOperation precision))
      (hpart : operations ∈ trace.parts) :
      ∀ operation ∈ operations, operation.Sound := by
    intro operation hoperation
    apply hall operation
    rw [Trace.operations, List.mem_flatten]
    exact ⟨operations, hpart, hoperation⟩
  have hone := ChapterVISignedDyadicComplexRectangle.pointInt_contains precision 1
  have hExpValue : ((Rectangle.pointInt precision 1).add expDelta).Contains
      (Complex.exp (chapterVIDRootExponentialArgument u -
        chapterVIDRootExponentialArgument chapterVIDCollisionLift)) := by
    have := ChapterVISignedDyadicComplexRectangle.add_contains hone hExpDelta
    rw [hΔexp] at this
    convert this using 1 <;> ring
  have hZetaExp := trace.zetaDeltaTimesExp.output_contains_mul_of_allSound
    (soundPart trace.zetaDeltaTimesExp.operations (by simp [Trace.parts])) hζDelta hExpValue
  have hMultiplierDelta : (trace.zetaDeltaTimesExp.output.add expDelta).Contains
      (chapterVIDRootRelativeMultiplierDelta ζ u) := by
    have := ChapterVISignedDyadicComplexRectangle.add_contains hZetaExp hExpDelta
    rw [hΔexp] at this
    simpa [chapterVIDRootRelativeMultiplierDelta] using this
  have hUSquare := trace.coordinateSquare.output_contains_mul_of_allSound
    (soundPart trace.coordinateSquare.operations (by simp [Trace.parts])) hu hu
  have hUCube := trace.coordinateCube.output_contains_mul_of_allSound
    (soundPart trace.coordinateCube.operations (by simp [Trace.parts])) hUSquare hu
  have hUInv := trace.coordinateInv.output_contains_inv_of_allSound
    (soundPart trace.coordinateInv.operations (by simp [Trace.parts])) hu
  have hUInvCube := trace.coordinateInvCube.output_contains_cube_of_allSound
    (soundPart trace.coordinateInvCube.operations (by simp [Trace.parts])) hUInv
  have hUInvFourth := trace.coordinateInvFourth.output_contains_mul_of_allSound
    (soundPart trace.coordinateInvFourth.operations (by simp [Trace.parts])) hUInvCube hUInv
  have hDeltaSum := trace.deltaTimesSum.output_contains_mul_of_allSound
    (soundPart trace.deltaTimesSum.operations (by simp [Trace.parts])) huDelta
    (ChapterVISignedDyadicComplexRectangle.add_contains hu hCollision)
  have hInvFourthProduct := trace.inverseFourthProduct.output_contains_mul_of_allSound
    (soundPart trace.inverseFourthProduct.operations (by simp [Trace.parts]))
    hUInvFourth hCollisionInvFourth
  have hInverseCorrection := trace.inverseCorrection.output_contains_mul_of_allSound
    (soundPart trace.inverseCorrection.operations (by simp [Trace.parts]))
    hInvFourthProduct
      (ChapterVISignedDyadicComplexRectangle.add_contains hUSquare hCollisionSquare)
  have hLaurentCore := trace.laurentCore.output_contains_mul_of_allSound
    (soundPart trace.laurentCore.operations (by simp [Trace.parts])) hDeltaSum
    (ChapterVISignedDyadicComplexRectangle.add_contains
      (ChapterVISignedDyadicComplexRectangle.pointInt_contains precision 30000)
      (ChapterVISignedDyadicComplexRectangle.nsmul_contains 3 hInverseCorrection))
  have hLaurent := trace.laurent.output_contains_of_allSound
    (soundPart trace.laurent.operations (by simp [Trace.parts]))
    hInverse10001 hLaurentCore
  have hLaurent' : trace.laurent.output.Contains
      (chapterVIDRootFactorDerivativeLaurentDifference u) := by
    convert hLaurent using 1
    unfold chapterVIDRootFactorDerivativeLaurentDifference
    push_cast
    ring
  have hShapeInv := trace.shapeInv.output_contains_mul_of_allSound
    (soundPart trace.shapeInv.operations (by simp [Trace.parts])) hCollisionInv hUInvCube
  have hShapeCube := trace.shapeCube.output_contains_mul_of_allSound
    (soundPart trace.shapeCube.operations (by simp [Trace.parts])) hUCube hCollisionInv
  have hShape : (trace.shapeInv.output.add trace.shapeCube.output).Contains
      (chapterVIDRootFactorDerivativePowerShape u) := by
    convert ChapterVISignedDyadicComplexRectangle.add_contains hShapeInv hShapeCube using 1
    unfold chapterVIDRootFactorDerivativePowerShape
    ring
  have hUTimesD := trace.coordinateTimesCollision.output_contains_mul_of_allSound
    (soundPart trace.coordinateTimesCollision.operations (by simp [Trace.parts])) hu hCollision
  have hSymmetricQuadratic := ChapterVISignedDyadicComplexRectangle.add_contains
    (ChapterVISignedDyadicComplexRectangle.add_contains hUSquare hUTimesD) hCollisionSquare
  have hDeltaQuadratic := trace.deltaTimesQuadratic.output_contains_mul_of_allSound
    (soundPart trace.deltaTimesQuadratic.operations (by simp [Trace.parts])) huDelta hSymmetricQuadratic
  have hDeltaQuadraticOverD :=
    trace.deltaQuadraticOverCollision.output_contains_mul_of_allSound
      (soundPart trace.deltaQuadraticOverCollision.operations (by simp [Trace.parts]))
      hDeltaQuadratic hCollisionInv
  have hInvCubeProduct := trace.inverseCubeProduct.output_contains_mul_of_allSound
    (soundPart trace.inverseCubeProduct.operations (by simp [Trace.parts]))
    hUInvCube hCollisionInvCube
  have hOneSubInvCube := ChapterVISignedDyadicComplexRectangle.sub_contains hone hInvCubeProduct
  have hShapeDifference := trace.shapeDifference.output_contains_mul_of_allSound
    (soundPart trace.shapeDifference.operations (by simp [Trace.parts]))
    hDeltaQuadraticOverD hOneSubInvCube
  have hShapeDifference' : trace.shapeDifference.output.Contains
      (chapterVIDRootFactorDerivativePowerShapeDifference u) := by
    convert hShapeDifference using 1
    unfold chapterVIDRootFactorDerivativePowerShapeDifference
    ring
  have hMultiplierShape := trace.multiplierTimesShape.output_contains_mul_of_allSound
    (soundPart trace.multiplierTimesShape.operations (by simp [Trace.parts])) hMultiplierDelta hShape
  have hPowerInput := ChapterVISignedDyadicComplexRectangle.add_contains
    hMultiplierShape hShapeDifference'
  have hYPower := trace.yTimesPowerDifference.output_contains_mul_of_allSound
    (soundPart trace.yTimesPowerDifference.operations (by simp [Trace.parts])) hYBase hPowerInput
  have hPower := trace.powerDifference.output_contains_of_allSound
    (soundPart trace.powerDifference.operations (by simp [Trace.parts])) hCoefficient200 hYPower
  have hCoefficient200Cast : ((200 / 10001 : ℝ) : ℂ) = (200 / 10001 : ℂ) := by
    rw [Complex.ofReal_div]
    norm_num
  rw [hCoefficient200Cast] at hPower
  have hYOverD := trace.yOverCollision.output_contains_mul_of_allSound
    (soundPart trace.yOverCollision.operations (by simp [Trace.parts])) hYBase hCollisionInv
  have hQuotient := trace.quotientDifference.output_contains_mul_of_allSound
    (soundPart trace.quotientDifference.operations (by simp [Trace.parts])) hYOverD hMultiplierDelta
  have hDerivative := ChapterVISignedDyadicComplexRectangle.add_contains
    (ChapterVISignedDyadicComplexRectangle.sub_contains hLaurent'
      (ChapterVISignedDyadicComplexRectangle.nsmul_contains 2 hQuotient)) hPower
  have hPath := trace.pathDerivative.output_contains_mul_of_allSound
    (soundPart trace.pathDerivative.operations (by simp [Trace.parts])) hDerivative hDirection
  change trace.pathDerivative.output.Contains _
  convert hPath using 1
  unfold chapterVIDRootFactorDerivativeDependencyPreserving
  ring

end ChapterVILeanCompCertDependencyPreservingFactorDerivativeTrace
end PoincareChapterVI
