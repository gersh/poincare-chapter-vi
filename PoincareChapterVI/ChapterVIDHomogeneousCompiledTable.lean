/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.ChapterVIDHomogeneousDerivative
import PoincareChapterVI.ChapterVILeanCompCertAttestation

/-!
# LeanCompCert table for the homogeneous D-connector coefficients

This module is the trusted counterpart of `research/check_chapter_vi_connector_seam.py`.
It keeps the two vanishing scales out of interval arithmetic and checks the scale-free
coefficients `X` and `Z` from `ChapterVIDHomogeneousDerivative`.  Additions, subtraction,
integer scaling, and conjugation are exact at a common dyadic scale; every rounded product and
reciprocal is emitted as a `DyadicOperation` and is reconstructed from one LeanCompCert verdict.
-/

noncomputable section

namespace PoincareChapterVI
namespace ChapterVIDHomogeneousCompiledTable

open ChapterVILeanCompCertBatch
open ChapterVILeanCompCertAttestation
open ChapterVILeanCompCertProposals
open ChapterVILeanCompCertIntervalBridge
open LeanCompCert.Ports.SignedProductClaims

abbrev Interval := ChapterVISignedDyadicInterval 20
abbrev Rectangle := ChapterVISignedDyadicComplexRectangle 20

namespace Rectangle

abbrev MulTrace (x y : Rectangle) :=
  ChapterVISignedDyadicComplexRectangle.MulTrace x y
abbrev InvTrace (x : Rectangle) :=
  ChapterVISignedDyadicComplexRectangle.InvTrace x
abbrev CubeTrace (x : Rectangle) :=
  ChapterVISignedDyadicComplexRectangle.CubeTrace x
abbrev RealMulTrace (r : Interval) (x : Rectangle) :=
  ChapterVISignedDyadicComplexRectangle.RealMulTrace r x

abbrev pointInt (value : ℤ) :=
  ChapterVISignedDyadicComplexRectangle.pointInt 20 value

end Rectangle

def collision : Rectangle := ⟨⟨-314053, -314047⟩, ⟨0, 0⟩⟩
def yBase : Rectangle := ⟨⟨-28312, -25000⟩, ⟨0, 0⟩⟩
def coefficient100 : Interval := ⟨3494, 3495⟩
def coefficient200 : Interval := ⟨20969, 20970⟩
def inverse10001 : Interval := ⟨104, 105⟩
def length : Interval := ⟨0, 1⟩
def normalizedEndpoint : Rectangle :=
  ⟨⟨-1024, 1024⟩, ⟨-158311, -130048⟩⟩
def unitSquare : Rectangle :=
  ⟨⟨-(2 ^ 20), 2 ^ 20⟩, ⟨-(2 ^ 20), 2 ^ 20⟩⟩

theorem collision_contains : collision.Contains chapterVIDCollisionLift := by
  have hradius := ChapterVIDRadialClusteredCompiledGrid.collisionRadius_contains
  have hcollision := chapterVIDCollisionLift_eq_neg_norm
  change (314047 : ℝ) / (2 : ℝ) ^ 20 ≤ ‖chapterVIDCollisionLift‖ ∧
    ‖chapterVIDCollisionLift‖ ≤ (314053 : ℝ) / (2 : ℝ) ^ 20 at hradius
  simp only [collision, ChapterVISignedDyadicComplexRectangle.Contains,
    ChapterVISignedDyadicInterval.Contains,
    ChapterVISignedDyadicInterval.toRealInterval,
    ChapterVISignedDyadicInterval.scale]
  rw [hcollision]
  simp only [Complex.neg_re, Complex.ofReal_re, Complex.neg_im, Complex.ofReal_im,
    neg_zero]
  constructor
  · constructor <;> norm_num at ⊢ hradius <;> linarith
  · unfold ChapterVIRealInterval.Contains
    norm_num [ChapterVISignedDyadicInterval.toRealInterval]

theorem yBase_contains : yBase.Contains chapterVIDY := by
  simpa [yBase, ChapterVIDConnectorFactorNormalizedDerivativeCompiled.referenceYBaseRectangle]
    using ChapterVIDConnectorFactorNormalizedDerivativeCompiled.referenceYBaseRectangle_contains

theorem coefficient100_contains : coefficient100.Contains (100 / 30003 : ℝ) := by
  norm_num [coefficient100, ChapterVISignedDyadicInterval.Contains,
    ChapterVISignedDyadicInterval.toRealInterval, ChapterVIRealInterval.Contains,
    ChapterVISignedDyadicInterval.scale]

theorem coefficient200_contains : coefficient200.Contains (200 / 10001 : ℝ) := by
  simpa [coefficient200,
    ChapterVIDConnectorFactorNormalizedDerivativeCompiled.referenceCoefficient200]
    using ChapterVIDConnectorFactorNormalizedDerivativeCompiled.referenceCoefficient200_contains

theorem inverse10001_contains : inverse10001.Contains (1 / 10001 : ℝ) := by
  norm_num [inverse10001, ChapterVISignedDyadicInterval.Contains,
    ChapterVISignedDyadicInterval.toRealInterval, ChapterVIRealInterval.Contains,
    ChapterVISignedDyadicInterval.scale]

theorem length_contains {L : ℝ} (hLnonneg : 0 ≤ L) (hL : L ≤ 1 / (2 : ℝ) ^ 20) :
    length.Contains L := by
  unfold ChapterVISignedDyadicInterval.Contains ChapterVIRealInterval.Contains
  norm_num [length, ChapterVISignedDyadicInterval.toRealInterval,
    ChapterVISignedDyadicInterval.scale]
  norm_num at hL
  exact ⟨hLnonneg, hL⟩

theorem unitSquare_contains_of_norm_le_one {z : ℂ} (hz : ‖z‖ ≤ 1) :
    unitSquare.Contains z := by
  have hre := (Complex.abs_re_le_norm z).trans hz
  have him := (Complex.abs_im_le_norm z).trans hz
  rw [abs_le] at hre him
  unfold ChapterVISignedDyadicComplexRectangle.Contains
    ChapterVISignedDyadicInterval.Contains ChapterVIRealInterval.Contains
  norm_num [unitSquare, ChapterVISignedDyadicInterval.toRealInterval,
    ChapterVISignedDyadicInterval.scale]
  exact ⟨hre, him⟩

/-- A sharper endpoint-direction box obtained by selecting the inverse-Morse fiber within
`2⁻¹⁰` of its limiting tangent. -/
theorem normalizedEndpoint_contains_of_direction_close {q : ℂ}
    (hq : ‖q - deriv chapterVIDGlobalContourFromMorse 0‖ < 1 / (2 : ℝ) ^ 10) :
    normalizedEndpoint.Contains q := by
  let slope := deriv chapterVIDGlobalContourFromMorse 0
  have hreNorm := (Complex.abs_re_le_norm (q - slope)).trans_lt hq
  have himNorm := (Complex.abs_im_le_norm (q - slope)).trans_lt hq
  have hre := abs_lt.mp hreNorm
  have him := abs_lt.mp himNorm
  have hslopeRe : slope.re = 0 := deriv_chapterVIDGlobalContourFromMorse_re_zero
  have hslopeIm := ChapterVIDMorseSlopeCompiled.deriv_chapterVIDGlobalContourFromMorse_im_mem
  rw [Complex.sub_re, hslopeRe, sub_zero] at hre
  rw [Complex.sub_im] at him
  unfold ChapterVISignedDyadicComplexRectangle.Contains
    ChapterVISignedDyadicInterval.Contains ChapterVIRealInterval.Contains
  norm_num [normalizedEndpoint, ChapterVISignedDyadicInterval.toRealInterval,
    ChapterVISignedDyadicInterval.scale] at ⊢ hq hre him hslopeIm
  constructor
  · constructor <;> linarith
  · constructor <;> linarith

/-- Certified rectangle for the real base coefficient `A=Fᵤᵤ(D)`.  Its real enclosure is
reused from the already kernel-checked inverse-Morse slope batch; its imaginary coordinate is
replaced by the exact zero theorem. -/
def baseLinear : Rectangle :=
  ⟨ChapterVIDMorseSlopeCompiled.plusSecondTrace.output.real, ⟨0, 0⟩⟩

theorem baseLinear_contains :
    baseLinear.Contains
      (chapterVIDRootFactorDerivativeLinearCoefficient chapterVIDCollisionLift) := by
  have hall := ChapterVIDMorseSlopeCompiled.reference_allSound
  have hbase : ∀ operation ∈ ChapterVIDMorseSlopeCompiled.baseTrace.operations,
      operation.Sound := by
    intro operation hoperation
    exact hall operation (by simp [ChapterVIDMorseSlopeCompiled.operations, hoperation])
  have hsecond : ∀ operation ∈ ChapterVIDMorseSlopeCompiled.plusSecondTrace.operations,
      operation.Sound := by
    intro operation hoperation
    exact hall operation (by simp [ChapterVIDMorseSlopeCompiled.operations, hoperation])
  have hζ := ChapterVIDMorseSlopeCompiled.terminalZetaRectangle_contains_base
  have hu := ChapterVIDConnectorInputBounds.localEndpointRectangle_contains_collisionLift
  have hanomalies := ChapterVIDMorseSlopeCompiled.baseTrace.anomalies_contain_of_allSound
    hbase hζ hu ChapterVIDOuterArcPolarCompiledGrid.exponentialCoefficient_contains
    chapterVIDZRootBase_ne_zero chapterVIDCollisionLift_ne_zero
  have hplus := ChapterVIDMorseSlopeCompiled.plusSecondTrace.output_contains_of_allSound
    hsecond hu hanomalies.1
    ChapterVIDOuterArcPolarCompiledGrid.inverse10001_contains
    ChapterVIDConnectorFactorSecondDerivativeReference.logCoefficient_contains
    ChapterVIDConnectorFactorSecondDerivativeReference.secondCoefficient_contains
    (ChapterVISignedDyadicComplexRectangle.pointInt_contains 20 1)
  rw [chapterVIDRootFactorDerivativeLinearCoefficient_base_eq_secondDerivative]
  constructor
  · simpa [baseLinear] using hplus.1
  · rw [chapterVIDRootCoordinateCollisionFactorPlusSecondDerivative_base_im]
    unfold ChapterVISignedDyadicInterval.Contains ChapterVIRealInterval.Contains
    norm_num [baseLinear, ChapterVISignedDyadicInterval.toRealInterval]

/-- Collision powers and inverses, checked once and shared by all 320 side/cell evaluations. -/
structure CollisionTrace where
  inverse : Rectangle.InvTrace collision
  square : Rectangle.MulTrace collision collision
  cube : Rectangle.MulTrace square.output collision
  fourth : Rectangle.MulTrace square.output square.output
  inverseSquare : Rectangle.MulTrace inverse.output inverse.output
  inverseCube : Rectangle.MulTrace inverseSquare.output inverse.output
  inverseFourth : Rectangle.MulTrace inverseSquare.output inverseSquare.output

def CollisionTrace.parts (trace : CollisionTrace) : List (List (DyadicOperation 20)) :=
  [ trace.inverse.operations, trace.square.operations, trace.cube.operations,
    trace.fourth.operations, trace.inverseSquare.operations,
    trace.inverseCube.operations, trace.inverseFourth.operations ]

def CollisionTrace.operations (trace : CollisionTrace) : List (DyadicOperation 20) :=
  trace.parts.flatten

def collisionTrace : CollisionTrace :=
  let inverse := invTrace collision
  let square := mulTrace collision collision
  let cube := mulTrace square.output collision
  let fourth := mulTrace square.output square.output
  let inverseSquare := mulTrace inverse.output inverse.output
  let inverseCube := mulTrace inverseSquare.output inverse.output
  let inverseFourth := mulTrace inverseSquare.output inverseSquare.output
  ⟨inverse, square, cube, fourth, inverseSquare, inverseCube, inverseFourth⟩

theorem CollisionTrace.contains_of_allSound (trace : CollisionTrace)
    (hall : ∀ operation ∈ trace.operations, operation.Sound) :
    trace.inverse.output.Contains chapterVIDCollisionLift⁻¹ ∧
    trace.square.output.Contains (chapterVIDCollisionLift ^ 2) ∧
    trace.cube.output.Contains (chapterVIDCollisionLift ^ 3) ∧
    trace.fourth.output.Contains (chapterVIDCollisionLift ^ 4) ∧
    trace.inverseSquare.output.Contains (chapterVIDCollisionLift⁻¹ ^ 2) ∧
    trace.inverseCube.output.Contains (chapterVIDCollisionLift⁻¹ ^ 3) ∧
    trace.inverseFourth.output.Contains (chapterVIDCollisionLift⁻¹ ^ 4) := by
  have soundPart (operations : List (DyadicOperation 20)) (hpart : operations ∈ trace.parts) :
      ∀ operation ∈ operations, operation.Sound := by
    intro operation hoperation
    apply hall operation
    rw [CollisionTrace.operations, List.mem_flatten]
    exact ⟨operations, hpart, hoperation⟩
  have hinv := trace.inverse.output_contains_inv_of_allSound
    (soundPart trace.inverse.operations (by simp [CollisionTrace.parts])) collision_contains
  have hsq := trace.square.output_contains_mul_of_allSound
    (soundPart trace.square.operations (by simp [CollisionTrace.parts]))
    collision_contains collision_contains
  have hcube := trace.cube.output_contains_mul_of_allSound
    (soundPart trace.cube.operations (by simp [CollisionTrace.parts])) hsq collision_contains
  have hfourth := trace.fourth.output_contains_mul_of_allSound
    (soundPart trace.fourth.operations (by simp [CollisionTrace.parts])) hsq hsq
  have hinvSq := trace.inverseSquare.output_contains_mul_of_allSound
    (soundPart trace.inverseSquare.operations (by simp [CollisionTrace.parts])) hinv hinv
  have hinvCube := trace.inverseCube.output_contains_mul_of_allSound
    (soundPart trace.inverseCube.operations (by simp [CollisionTrace.parts])) hinvSq hinv
  have hinvFourth := trace.inverseFourth.output_contains_mul_of_allSound
    (soundPart trace.inverseFourth.operations (by simp [CollisionTrace.parts])) hinvSq hinvSq
  refine ⟨hinv, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [pow_two] using hsq
  · convert hcube using 1 <;> ring
  · convert hfourth using 1 <;> ring
  · simpa [pow_two] using hinvSq
  · convert hinvCube using 1 <;> ring
  · convert hinvFourth using 1 <;> ring

/-- Cell-independent collision data, including the exponential-argument coefficient at `D`. -/
structure FixedTrace where
  powers : CollisionTrace
  inverseCubeProduct : Rectangle.MulTrace powers.inverseCube.output powers.inverseCube.output
  argumentBaseCore : Rectangle.MulTrace (powers.square.output.nsmul 3)
    ((Rectangle.pointInt 1).add inverseCubeProduct.output)
  argumentBaseScaled : Rectangle.RealMulTrace coefficient100 argumentBaseCore.output

def FixedTrace.argumentBase (trace : FixedTrace) : Rectangle :=
  trace.argumentBaseScaled.output.neg

def FixedTrace.parts (trace : FixedTrace) : List (List (DyadicOperation 20)) :=
  [ trace.powers.operations, trace.inverseCubeProduct.operations,
    trace.argumentBaseCore.operations, trace.argumentBaseScaled.operations ]

def FixedTrace.operations (trace : FixedTrace) : List (DyadicOperation 20) :=
  trace.parts.flatten

def fixedTrace : FixedTrace :=
  let powers := collisionTrace
  let inverseCubeProduct := mulTrace powers.inverseCube.output powers.inverseCube.output
  let argumentBaseCore := mulTrace (powers.square.output.nsmul 3)
    ((Rectangle.pointInt 1).add inverseCubeProduct.output)
  let argumentBaseScaled := realMulTrace coefficient100 argumentBaseCore.output
  ⟨powers, inverseCubeProduct, argumentBaseCore, argumentBaseScaled⟩

theorem FixedTrace.contains_of_allSound (trace : FixedTrace)
    (hall : ∀ operation ∈ trace.operations, operation.Sound) :
    trace.powers.inverse.output.Contains chapterVIDCollisionLift⁻¹ ∧
    trace.powers.square.output.Contains (chapterVIDCollisionLift ^ 2) ∧
    trace.powers.cube.output.Contains (chapterVIDCollisionLift ^ 3) ∧
    trace.powers.fourth.output.Contains (chapterVIDCollisionLift ^ 4) ∧
    trace.powers.inverseSquare.output.Contains (chapterVIDCollisionLift⁻¹ ^ 2) ∧
    trace.powers.inverseCube.output.Contains (chapterVIDCollisionLift⁻¹ ^ 3) ∧
    trace.powers.inverseFourth.output.Contains (chapterVIDCollisionLift⁻¹ ^ 4) ∧
    trace.argumentBase.Contains
      (chapterVIDRootExponentialArgumentDifferenceCoefficient chapterVIDCollisionLift) := by
  have soundPart (operations : List (DyadicOperation 20)) (hpart : operations ∈ trace.parts) :
      ∀ operation ∈ operations, operation.Sound := by
    intro operation hoperation
    apply hall operation
    rw [FixedTrace.operations, List.mem_flatten]
    exact ⟨operations, hpart, hoperation⟩
  have hpowers := trace.powers.contains_of_allSound
    (soundPart trace.powers.operations (by simp [FixedTrace.parts]))
  rcases hpowers with ⟨hDInv, hDSq, hDCube, hDFourth, hDInvSq, hDInvCube, hDInvFourth⟩
  have hinverseCubeProduct := trace.inverseCubeProduct.output_contains_mul_of_allSound
    (soundPart trace.inverseCubeProduct.operations (by simp [FixedTrace.parts]))
    hDInvCube hDInvCube
  have hthreeDSq := ChapterVISignedDyadicComplexRectangle.nsmul_contains 3 hDSq
  have hone := ChapterVISignedDyadicComplexRectangle.pointInt_contains 20 1
  have hcore := trace.argumentBaseCore.output_contains_mul_of_allSound
    (soundPart trace.argumentBaseCore.operations (by simp [FixedTrace.parts])) hthreeDSq
    (ChapterVISignedDyadicComplexRectangle.add_contains hone hinverseCubeProduct)
  have hscaled := trace.argumentBaseScaled.output_contains_of_allSound
    (soundPart trace.argumentBaseScaled.operations (by simp [FixedTrace.parts]))
    coefficient100_contains hcore
  have hneg := ChapterVISignedDyadicComplexRectangle.neg_contains hscaled
  refine ⟨hDInv, hDSq, hDCube, hDFourth, hDInvSq, hDInvCube, hDInvFourth, ?_⟩
  change trace.argumentBaseScaled.output.neg.Contains _
  convert hneg using 1
  unfold chapterVIDRootExponentialArgumentDifferenceCoefficient
  push_cast
  ring

/-! ## Per-coordinate coefficient trace -/

/-- Shared powers and the two elementary coefficients `H(u)` and `M(u)`. -/
structure CoordinateTrace (fixed : FixedTrace) (coordinate coordinateDelta : Rectangle) where
  square : Rectangle.MulTrace coordinate coordinate
  cube : Rectangle.MulTrace square.output coordinate
  inverse : Rectangle.InvTrace coordinate
  inverseSquare : Rectangle.MulTrace inverse.output inverse.output
  inverseCube : Rectangle.MulTrace inverseSquare.output inverse.output
  inverseFourth : Rectangle.MulTrace inverseSquare.output inverseSquare.output
  coordinateTimesCollision : Rectangle.MulTrace coordinate collision
  inverseCubeProduct : Rectangle.MulTrace inverseCube.output fixed.powers.inverseCube.output
  inverseCubeDifferenceProduct : Rectangle.MulTrace
    ((square.output.add coordinateTimesCollision.output).add fixed.powers.square.output)
    inverseCubeProduct.output
  argumentCoefficientCore : Rectangle.MulTrace
    ((square.output.add coordinateTimesCollision.output).add fixed.powers.square.output)
    ((Rectangle.pointInt 1).add inverseCubeProduct.output)
  argumentCoefficientScaled : Rectangle.RealMulTrace coefficient100 argumentCoefficientCore.output
  powerShape : Rectangle.MulTrace fixed.powers.inverse.output
    (inverseCube.output.add cube.output)
  yTimesPowerShape : Rectangle.MulTrace yBase powerShape.output
  powerShapeScaled : Rectangle.RealMulTrace coefficient200 yTimesPowerShape.output
  yOverCollision : Rectangle.MulTrace yBase fixed.powers.inverse.output
  argument : Rectangle.MulTrace coordinateDelta argumentCoefficientScaled.output.neg

def CoordinateTrace.quadratic {fixed : FixedTrace} {coordinate coordinateDelta : Rectangle}
    (trace : CoordinateTrace fixed coordinate coordinateDelta) : Rectangle :=
  (trace.square.output.add trace.coordinateTimesCollision.output).add fixed.powers.square.output

def CoordinateTrace.inverseCubeDifference {fixed : FixedTrace}
    {coordinate coordinateDelta : Rectangle}
    (trace : CoordinateTrace fixed coordinate coordinateDelta) : Rectangle :=
  trace.inverseCubeDifferenceProduct.output.neg

def CoordinateTrace.argumentCoefficient {fixed : FixedTrace}
    {coordinate coordinateDelta : Rectangle}
    (trace : CoordinateTrace fixed coordinate coordinateDelta) : Rectangle :=
  trace.argumentCoefficientScaled.output.neg

def CoordinateTrace.multiplierCoefficient {fixed : FixedTrace}
    {coordinate coordinateDelta : Rectangle}
    (trace : CoordinateTrace fixed coordinate coordinateDelta) : Rectangle :=
  (trace.yOverCollision.output.nsmul 2).neg.add trace.powerShapeScaled.output

def CoordinateTrace.parts {fixed : FixedTrace} {coordinate coordinateDelta : Rectangle}
    (trace : CoordinateTrace fixed coordinate coordinateDelta) :
    List (List (DyadicOperation 20)) :=
  [ trace.square.operations, trace.cube.operations, trace.inverse.operations,
    trace.inverseSquare.operations, trace.inverseCube.operations, trace.inverseFourth.operations,
    trace.coordinateTimesCollision.operations, trace.inverseCubeProduct.operations,
    trace.inverseCubeDifferenceProduct.operations, trace.argumentCoefficientCore.operations,
    trace.argumentCoefficientScaled.operations, trace.powerShape.operations,
    trace.yTimesPowerShape.operations, trace.powerShapeScaled.operations,
    trace.yOverCollision.operations, trace.argument.operations ]

def CoordinateTrace.operations {fixed : FixedTrace} {coordinate coordinateDelta : Rectangle}
    (trace : CoordinateTrace fixed coordinate coordinateDelta) : List (DyadicOperation 20) :=
  trace.parts.flatten

def coordinateTrace (fixed : FixedTrace) (coordinate coordinateDelta : Rectangle) :
    CoordinateTrace fixed coordinate coordinateDelta :=
  let square := mulTrace coordinate coordinate
  let cube := mulTrace square.output coordinate
  let inverse := invTrace coordinate
  let inverseSquare := mulTrace inverse.output inverse.output
  let inverseCube := mulTrace inverseSquare.output inverse.output
  let inverseFourth := mulTrace inverseSquare.output inverseSquare.output
  let coordinateTimesCollision := mulTrace coordinate collision
  let quadratic := (square.output.add coordinateTimesCollision.output).add fixed.powers.square.output
  let inverseCubeProduct := mulTrace inverseCube.output fixed.powers.inverseCube.output
  let inverseCubeDifferenceProduct := mulTrace quadratic inverseCubeProduct.output
  let argumentCoefficientCore := mulTrace quadratic
    ((Rectangle.pointInt 1).add inverseCubeProduct.output)
  let argumentCoefficientScaled := realMulTrace coefficient100 argumentCoefficientCore.output
  let powerShape := mulTrace fixed.powers.inverse.output (inverseCube.output.add cube.output)
  let yTimesPowerShape := mulTrace yBase powerShape.output
  let powerShapeScaled := realMulTrace coefficient200 yTimesPowerShape.output
  let yOverCollision := mulTrace yBase fixed.powers.inverse.output
  let argument := mulTrace coordinateDelta argumentCoefficientScaled.output.neg
  { square := square, cube := cube, inverse := inverse, inverseSquare := inverseSquare,
    inverseCube := inverseCube, inverseFourth := inverseFourth,
    coordinateTimesCollision := coordinateTimesCollision,
    inverseCubeProduct := inverseCubeProduct,
    inverseCubeDifferenceProduct := inverseCubeDifferenceProduct,
    argumentCoefficientCore := argumentCoefficientCore,
    argumentCoefficientScaled := argumentCoefficientScaled,
    powerShape := powerShape, yTimesPowerShape := yTimesPowerShape,
    powerShapeScaled := powerShapeScaled, yOverCollision := yOverCollision,
    argument := argument }

theorem CoordinateTrace.contains_of_allSound
    {fixed : FixedTrace} {coordinate coordinateDelta : Rectangle}
    (trace : CoordinateTrace fixed coordinate coordinateDelta)
    (hall : ∀ operation ∈ trace.operations, operation.Sound)
    {u : ℂ} (hu : coordinate.Contains u)
    (huDelta : coordinateDelta.Contains (u - chapterVIDCollisionLift))
    (hfixed :
      fixed.powers.inverse.output.Contains chapterVIDCollisionLift⁻¹ ∧
      fixed.powers.square.output.Contains (chapterVIDCollisionLift ^ 2) ∧
      fixed.powers.cube.output.Contains (chapterVIDCollisionLift ^ 3) ∧
      fixed.powers.fourth.output.Contains (chapterVIDCollisionLift ^ 4) ∧
      fixed.powers.inverseSquare.output.Contains (chapterVIDCollisionLift⁻¹ ^ 2) ∧
      fixed.powers.inverseCube.output.Contains (chapterVIDCollisionLift⁻¹ ^ 3) ∧
      fixed.powers.inverseFourth.output.Contains (chapterVIDCollisionLift⁻¹ ^ 4) ∧
      fixed.argumentBase.Contains
        (chapterVIDRootExponentialArgumentDifferenceCoefficient chapterVIDCollisionLift)) :
    trace.square.output.Contains (u ^ 2) ∧
    trace.cube.output.Contains (u ^ 3) ∧
    trace.inverse.output.Contains u⁻¹ ∧
    trace.inverseSquare.output.Contains (u⁻¹ ^ 2) ∧
    trace.inverseCube.output.Contains (u⁻¹ ^ 3) ∧
    trace.inverseFourth.output.Contains (u⁻¹ ^ 4) ∧
    trace.quadratic.Contains (u ^ 2 + u * chapterVIDCollisionLift + chapterVIDCollisionLift ^ 2) ∧
    trace.inverseCubeProduct.output.Contains
      (u⁻¹ ^ 3 * chapterVIDCollisionLift⁻¹ ^ 3) ∧
    trace.inverseCubeDifference.Contains
      (-(u ^ 2 + u * chapterVIDCollisionLift + chapterVIDCollisionLift ^ 2) /
        (u ^ 3 * chapterVIDCollisionLift ^ 3)) ∧
    trace.argumentCoefficient.Contains
      (chapterVIDRootExponentialArgumentDifferenceCoefficient u) ∧
    trace.multiplierCoefficient.Contains
      (chapterVIDRootFactorDerivativeMultiplierCoefficient u) ∧
    trace.argument.output.Contains (chapterVIDRootExponentialArgumentDifference u) := by
  have soundPart (operations : List (DyadicOperation 20)) (hpart : operations ∈ trace.parts) :
      ∀ operation ∈ operations, operation.Sound := by
    intro operation hoperation
    apply hall operation
    rw [CoordinateTrace.operations, List.mem_flatten]
    exact ⟨operations, hpart, hoperation⟩
  rcases hfixed with ⟨hDInv, hDSq, hDCube, hDFourth, hDInvSq, hDInvCube,
    hDInvFourth, hArgumentBase⟩
  have hsq := trace.square.output_contains_mul_of_allSound
    (soundPart trace.square.operations (by simp [CoordinateTrace.parts])) hu hu
  have hcube := trace.cube.output_contains_mul_of_allSound
    (soundPart trace.cube.operations (by simp [CoordinateTrace.parts])) hsq hu
  have hinv := trace.inverse.output_contains_inv_of_allSound
    (soundPart trace.inverse.operations (by simp [CoordinateTrace.parts])) hu
  have hinvSq := trace.inverseSquare.output_contains_mul_of_allSound
    (soundPart trace.inverseSquare.operations (by simp [CoordinateTrace.parts])) hinv hinv
  have hinvCube := trace.inverseCube.output_contains_mul_of_allSound
    (soundPart trace.inverseCube.operations (by simp [CoordinateTrace.parts])) hinvSq hinv
  have hinvFourth := trace.inverseFourth.output_contains_mul_of_allSound
    (soundPart trace.inverseFourth.operations (by simp [CoordinateTrace.parts])) hinvSq hinvSq
  have huD := trace.coordinateTimesCollision.output_contains_mul_of_allSound
    (soundPart trace.coordinateTimesCollision.operations (by simp [CoordinateTrace.parts]))
    hu collision_contains
  have hquadratic := ChapterVISignedDyadicComplexRectangle.add_contains
    (ChapterVISignedDyadicComplexRectangle.add_contains hsq huD) hDSq
  have hinvCubeProduct := trace.inverseCubeProduct.output_contains_mul_of_allSound
    (soundPart trace.inverseCubeProduct.operations (by simp [CoordinateTrace.parts]))
    hinvCube hDInvCube
  have hinvCubeDifferenceProduct :=
    trace.inverseCubeDifferenceProduct.output_contains_mul_of_allSound
      (soundPart trace.inverseCubeDifferenceProduct.operations
        (by simp [CoordinateTrace.parts])) hquadratic hinvCubeProduct
  have hinvCubeDifference :=
    ChapterVISignedDyadicComplexRectangle.neg_contains hinvCubeDifferenceProduct
  have hone := ChapterVISignedDyadicComplexRectangle.pointInt_contains 20 1
  have hargumentCore := trace.argumentCoefficientCore.output_contains_mul_of_allSound
    (soundPart trace.argumentCoefficientCore.operations (by simp [CoordinateTrace.parts]))
    hquadratic (ChapterVISignedDyadicComplexRectangle.add_contains hone hinvCubeProduct)
  have hargumentScaled := trace.argumentCoefficientScaled.output_contains_of_allSound
    (soundPart trace.argumentCoefficientScaled.operations (by simp [CoordinateTrace.parts]))
    coefficient100_contains hargumentCore
  have hargumentCoefficient :=
    ChapterVISignedDyadicComplexRectangle.neg_contains hargumentScaled
  have hpowerShape := trace.powerShape.output_contains_mul_of_allSound
    (soundPart trace.powerShape.operations (by simp [CoordinateTrace.parts])) hDInv
    (ChapterVISignedDyadicComplexRectangle.add_contains hinvCube hcube)
  have hyPowerShape := trace.yTimesPowerShape.output_contains_mul_of_allSound
    (soundPart trace.yTimesPowerShape.operations (by simp [CoordinateTrace.parts]))
    yBase_contains hpowerShape
  have hpowerScaled := trace.powerShapeScaled.output_contains_of_allSound
    (soundPart trace.powerShapeScaled.operations (by simp [CoordinateTrace.parts]))
    coefficient200_contains hyPowerShape
  have hyDInv := trace.yOverCollision.output_contains_mul_of_allSound
    (soundPart trace.yOverCollision.operations (by simp [CoordinateTrace.parts]))
    yBase_contains hDInv
  have hmultiplier := ChapterVISignedDyadicComplexRectangle.add_contains
    (ChapterVISignedDyadicComplexRectangle.neg_contains
      (ChapterVISignedDyadicComplexRectangle.nsmul_contains 2 hyDInv)) hpowerScaled
  have hargument := trace.argument.output_contains_mul_of_allSound
    (soundPart trace.argument.operations (by simp [CoordinateTrace.parts]))
    huDelta hargumentCoefficient
  refine ⟨?_, ?_, hinv, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [pow_two] using hsq
  · convert hcube using 1 <;> ring
  · simpa [pow_two] using hinvSq
  · convert hinvCube using 1 <;> ring
  · convert hinvFourth using 1 <;> ring
  · change (((trace.square.output.add trace.coordinateTimesCollision.output).add
        fixed.powers.square.output).Contains _)
    convert hquadratic using 1 <;> ring
  · convert hinvCubeProduct using 1 <;> ring
  · change trace.inverseCubeDifferenceProduct.output.neg.Contains _
    convert hinvCubeDifference using 1
    field_simp [chapterVIDCollisionLift_ne_zero]
  · change trace.argumentCoefficientScaled.output.neg.Contains _
    convert hargumentCoefficient using 1
    unfold chapterVIDRootExponentialArgumentDifferenceCoefficient
    push_cast
    ring
  · change ((trace.yOverCollision.output.nsmul 2).neg.add
      trace.powerShapeScaled.output).Contains _
    convert hmultiplier using 1
    unfold chapterVIDRootFactorDerivativeMultiplierCoefficient
      chapterVIDRootFactorDerivativePowerShape
    push_cast
    ring
  · convert hargument using 1
    rw [chapterVIDRootExponentialArgumentDifference_eq_mul_coefficient]
    unfold chapterVIDRootExponentialArgumentDifferenceCoefficient
    push_cast
    ring

/-- The removable difference quotients and the final `K(u)` and `P(u)` coefficients. -/
structure CoefficientTrace (fixed : FixedTrace) (coordinate coordinateDelta : Rectangle)
    (remainder : Rectangle) where
  coordinateData : CoordinateTrace fixed coordinate coordinateDelta
  squareTimesCollision : Rectangle.MulTrace coordinateData.square.output collision
  coordinateTimesCollisionSquare : Rectangle.MulTrace coordinate fixed.powers.square.output
  inverseTwoFirst : Rectangle.MulTrace (coordinate.add collision)
    coordinateData.inverseSquare.output
  inverseTwoSecond : Rectangle.MulTrace inverseTwoFirst.output fixed.powers.inverseSquare.output
  inverseFourthProduct : Rectangle.MulTrace coordinateData.inverseFourth.output
    fixed.powers.inverseFourth.output
  inverseFourDifferenceProduct : Rectangle.MulTrace
    (((coordinateData.cube.output.add squareTimesCollision.output).add
      coordinateTimesCollisionSquare.output).add fixed.powers.cube.output)
    inverseFourthProduct.output
  collisionSquareTimesInverseFourth : Rectangle.MulTrace fixed.powers.square.output
    coordinateData.inverseFourth.output
  powerTerm : Rectangle.MulTrace fixed.powers.inverseFourth.output
    (coordinateData.inverseSquare.output.add collisionSquareTimesInverseFourth.output)
  collisionSquareTimesInverseFourDifference : Rectangle.MulTrace fixed.powers.square.output
    inverseFourDifferenceProduct.output.neg
  powerTermDifference : Rectangle.MulTrace fixed.powers.inverseFourth.output
    (inverseTwoSecond.output.neg.add collisionSquareTimesInverseFourDifference.output)
  collisionTimesPowerTermDifference : Rectangle.MulTrace collision powerTermDifference.output
  laurentDifference : Rectangle.RealMulTrace inverse10001
    ((Rectangle.pointInt 30000).add (powerTerm.output.nsmul 3) |>.add
      (collisionTimesPowerTermDifference.output.nsmul 6))
  inverseFactorDifferenceMinus : Rectangle.MulTrace fixed.powers.inverseCube.output
    coordinateData.inverseCubeDifference
  quadraticDifferenceTimesMinus : Rectangle.MulTrace
    (coordinate.add (collision.nsmul 2))
    ((Rectangle.pointInt 1).sub coordinateData.inverseCubeProduct.output)
  collisionSquareTimesInverseFactorDifferenceMinus : Rectangle.MulTrace
    fixed.powers.square.output inverseFactorDifferenceMinus.output.neg
  powerShapeDifference : Rectangle.MulTrace fixed.powers.inverse.output
    (quadraticDifferenceTimesMinus.output.add
      (collisionSquareTimesInverseFactorDifferenceMinus.output.nsmul 3))
  yTimesPowerShapeDifference : Rectangle.MulTrace yBase powerShapeDifference.output
  powerShapeDifferenceScaled : Rectangle.RealMulTrace coefficient200
    yTimesPowerShapeDifference.output
  inverseFactorDifferencePlus : Rectangle.MulTrace fixed.powers.inverseCube.output
    coordinateData.inverseCubeDifference
  quadraticDifferenceTimesPlus : Rectangle.MulTrace
    (coordinate.add (collision.nsmul 2))
    ((Rectangle.pointInt 1).add coordinateData.inverseCubeProduct.output)
  collisionSquareTimesInverseFactorDifferencePlus : Rectangle.MulTrace
    fixed.powers.square.output inverseFactorDifferencePlus.output
  argumentCoefficientDifference : Rectangle.RealMulTrace coefficient100
    (quadraticDifferenceTimesPlus.output.add
      (collisionSquareTimesInverseFactorDifferencePlus.output.nsmul 3))
  multiplierDifferenceCollision : Rectangle.MulTrace fixed.powers.inverse.output
    (coordinateData.inverseCubeDifference.add coordinateData.quadratic)
  multiplierDifferenceY : Rectangle.MulTrace yBase multiplierDifferenceCollision.output
  multiplierDifference : Rectangle.RealMulTrace coefficient200 multiplierDifferenceY.output
  argumentDifferenceTimesMultiplier : Rectangle.MulTrace
    argumentCoefficientDifference.output.neg coordinateData.multiplierCoefficient
  baseArgumentTimesMultiplierDifference : Rectangle.MulTrace fixed.argumentBase
    multiplierDifference.output
  argumentCoefficientSquare : Rectangle.MulTrace coordinateData.argumentCoefficient
    coordinateData.argumentCoefficient
  argumentSquareTimesRemainder : Rectangle.MulTrace argumentCoefficientSquare.output remainder
  argumentRemainderTimesMultiplier : Rectangle.MulTrace argumentSquareTimesRemainder.output
    coordinateData.multiplierCoefficient
  parameterArgumentSquare : Rectangle.MulTrace coordinateData.argument.output
    coordinateData.argument.output
  parameterRemainder : Rectangle.MulTrace parameterArgumentSquare.output remainder
  parameterCoefficient : Rectangle.MulTrace
    ((Rectangle.pointInt 1).add coordinateData.argument.output |>.add parameterRemainder.output)
    coordinateData.multiplierCoefficient

def CoefficientTrace.coordinateCoefficientDifference {fixed : FixedTrace}
    {coordinate coordinateDelta remainder : Rectangle}
    (trace : CoefficientTrace fixed coordinate coordinateDelta remainder) : Rectangle :=
  trace.laurentDifference.output.add trace.powerShapeDifferenceScaled.output

def CoefficientTrace.linearCoefficientDifference {fixed : FixedTrace}
    {coordinate coordinateDelta remainder : Rectangle}
    (trace : CoefficientTrace fixed coordinate coordinateDelta remainder) : Rectangle :=
  (trace.coordinateCoefficientDifference.add
    trace.argumentDifferenceTimesMultiplier.output).add
    trace.baseArgumentTimesMultiplierDifference.output

def CoefficientTrace.quadraticCoefficient {fixed : FixedTrace}
    {coordinate coordinateDelta remainder : Rectangle}
    (trace : CoefficientTrace fixed coordinate coordinateDelta remainder) : Rectangle :=
  trace.linearCoefficientDifference.add trace.argumentRemainderTimesMultiplier.output

def CoefficientTrace.parts {fixed : FixedTrace}
    {coordinate coordinateDelta remainder : Rectangle}
    (trace : CoefficientTrace fixed coordinate coordinateDelta remainder) :
    List (List (DyadicOperation 20)) :=
  [ trace.coordinateData.operations,
    trace.squareTimesCollision.operations, trace.coordinateTimesCollisionSquare.operations,
    trace.inverseTwoFirst.operations, trace.inverseTwoSecond.operations,
    trace.inverseFourthProduct.operations, trace.inverseFourDifferenceProduct.operations,
    trace.collisionSquareTimesInverseFourth.operations, trace.powerTerm.operations,
    trace.collisionSquareTimesInverseFourDifference.operations,
    trace.powerTermDifference.operations, trace.collisionTimesPowerTermDifference.operations,
    trace.laurentDifference.operations, trace.inverseFactorDifferenceMinus.operations,
    trace.quadraticDifferenceTimesMinus.operations,
    trace.collisionSquareTimesInverseFactorDifferenceMinus.operations,
    trace.powerShapeDifference.operations, trace.yTimesPowerShapeDifference.operations,
    trace.powerShapeDifferenceScaled.operations, trace.inverseFactorDifferencePlus.operations,
    trace.quadraticDifferenceTimesPlus.operations,
    trace.collisionSquareTimesInverseFactorDifferencePlus.operations,
    trace.argumentCoefficientDifference.operations,
    trace.multiplierDifferenceCollision.operations, trace.multiplierDifferenceY.operations,
    trace.multiplierDifference.operations, trace.argumentDifferenceTimesMultiplier.operations,
    trace.baseArgumentTimesMultiplierDifference.operations,
    trace.argumentCoefficientSquare.operations, trace.argumentSquareTimesRemainder.operations,
    trace.argumentRemainderTimesMultiplier.operations, trace.parameterArgumentSquare.operations,
    trace.parameterRemainder.operations, trace.parameterCoefficient.operations ]

def CoefficientTrace.operations {fixed : FixedTrace}
    {coordinate coordinateDelta remainder : Rectangle}
    (trace : CoefficientTrace fixed coordinate coordinateDelta remainder) :
    List (DyadicOperation 20) := trace.parts.flatten

def coefficientTrace (fixed : FixedTrace) (coordinate coordinateDelta remainder : Rectangle) :
    CoefficientTrace fixed coordinate coordinateDelta remainder :=
  let c := coordinateTrace fixed coordinate coordinateDelta
  let squareTimesCollision := mulTrace c.square.output collision
  let coordinateTimesCollisionSquare := mulTrace coordinate fixed.powers.square.output
  let inverseTwoFirst := mulTrace (coordinate.add collision) c.inverseSquare.output
  let inverseTwoSecond := mulTrace inverseTwoFirst.output fixed.powers.inverseSquare.output
  let inverseFourthProduct := mulTrace c.inverseFourth.output fixed.powers.inverseFourth.output
  let inverseFourPolynomial := (((c.cube.output.add squareTimesCollision.output).add
    coordinateTimesCollisionSquare.output).add fixed.powers.cube.output)
  let inverseFourDifferenceProduct := mulTrace inverseFourPolynomial inverseFourthProduct.output
  let collisionSquareTimesInverseFourth := mulTrace fixed.powers.square.output c.inverseFourth.output
  let powerTerm := mulTrace fixed.powers.inverseFourth.output
    (c.inverseSquare.output.add collisionSquareTimesInverseFourth.output)
  let collisionSquareTimesInverseFourDifference := mulTrace fixed.powers.square.output
    inverseFourDifferenceProduct.output.neg
  let powerTermDifference := mulTrace fixed.powers.inverseFourth.output
    (inverseTwoSecond.output.neg.add collisionSquareTimesInverseFourDifference.output)
  let collisionTimesPowerTermDifference := mulTrace collision powerTermDifference.output
  let laurentCore := ((Rectangle.pointInt 30000).add (powerTerm.output.nsmul 3)).add
    (collisionTimesPowerTermDifference.output.nsmul 6)
  let laurentDifference := realMulTrace inverse10001 laurentCore
  let inverseFactorDifferenceMinus := mulTrace fixed.powers.inverseCube.output
    c.inverseCubeDifference
  let quadraticDifference := coordinate.add (collision.nsmul 2)
  let inverseFactorMinus := (Rectangle.pointInt 1).sub c.inverseCubeProduct.output
  let quadraticDifferenceTimesMinus := mulTrace quadraticDifference inverseFactorMinus
  let collisionSquareTimesInverseFactorDifferenceMinus := mulTrace fixed.powers.square.output
    inverseFactorDifferenceMinus.output.neg
  let powerShapeDifference := mulTrace fixed.powers.inverse.output
    (quadraticDifferenceTimesMinus.output.add
      (collisionSquareTimesInverseFactorDifferenceMinus.output.nsmul 3))
  let yTimesPowerShapeDifference := mulTrace yBase powerShapeDifference.output
  let powerShapeDifferenceScaled := realMulTrace coefficient200 yTimesPowerShapeDifference.output
  let inverseFactorDifferencePlus := mulTrace fixed.powers.inverseCube.output
    c.inverseCubeDifference
  let inverseFactorPlus := (Rectangle.pointInt 1).add c.inverseCubeProduct.output
  let quadraticDifferenceTimesPlus := mulTrace quadraticDifference inverseFactorPlus
  let collisionSquareTimesInverseFactorDifferencePlus := mulTrace fixed.powers.square.output
    inverseFactorDifferencePlus.output
  let argumentCoefficientDifference := realMulTrace coefficient100
    (quadraticDifferenceTimesPlus.output.add
      (collisionSquareTimesInverseFactorDifferencePlus.output.nsmul 3))
  let multiplierDifferenceCollision := mulTrace fixed.powers.inverse.output
    (c.inverseCubeDifference.add c.quadratic)
  let multiplierDifferenceY := mulTrace yBase multiplierDifferenceCollision.output
  let multiplierDifference := realMulTrace coefficient200 multiplierDifferenceY.output
  let argumentDifferenceTimesMultiplier := mulTrace argumentCoefficientDifference.output.neg
    c.multiplierCoefficient
  let baseArgumentTimesMultiplierDifference := mulTrace fixed.argumentBase multiplierDifference.output
  let argumentCoefficientSquare := mulTrace c.argumentCoefficient c.argumentCoefficient
  let argumentSquareTimesRemainder := mulTrace argumentCoefficientSquare.output remainder
  let argumentRemainderTimesMultiplier := mulTrace argumentSquareTimesRemainder.output
    c.multiplierCoefficient
  let parameterArgumentSquare := mulTrace c.argument.output c.argument.output
  let parameterRemainder := mulTrace parameterArgumentSquare.output remainder
  let parameterCoefficient := mulTrace
    (((Rectangle.pointInt 1).add c.argument.output).add parameterRemainder.output)
    c.multiplierCoefficient
  { coordinateData := c, squareTimesCollision := squareTimesCollision,
    coordinateTimesCollisionSquare := coordinateTimesCollisionSquare,
    inverseTwoFirst := inverseTwoFirst, inverseTwoSecond := inverseTwoSecond,
    inverseFourthProduct := inverseFourthProduct,
    inverseFourDifferenceProduct := inverseFourDifferenceProduct,
    collisionSquareTimesInverseFourth := collisionSquareTimesInverseFourth,
    powerTerm := powerTerm,
    collisionSquareTimesInverseFourDifference := collisionSquareTimesInverseFourDifference,
    powerTermDifference := powerTermDifference,
    collisionTimesPowerTermDifference := collisionTimesPowerTermDifference,
    laurentDifference := laurentDifference,
    inverseFactorDifferenceMinus := inverseFactorDifferenceMinus,
    quadraticDifferenceTimesMinus := quadraticDifferenceTimesMinus,
    collisionSquareTimesInverseFactorDifferenceMinus :=
      collisionSquareTimesInverseFactorDifferenceMinus,
    powerShapeDifference := powerShapeDifference,
    yTimesPowerShapeDifference := yTimesPowerShapeDifference,
    powerShapeDifferenceScaled := powerShapeDifferenceScaled,
    inverseFactorDifferencePlus := inverseFactorDifferencePlus,
    quadraticDifferenceTimesPlus := quadraticDifferenceTimesPlus,
    collisionSquareTimesInverseFactorDifferencePlus :=
      collisionSquareTimesInverseFactorDifferencePlus,
    argumentCoefficientDifference := argumentCoefficientDifference,
    multiplierDifferenceCollision := multiplierDifferenceCollision,
    multiplierDifferenceY := multiplierDifferenceY,
    multiplierDifference := multiplierDifference,
    argumentDifferenceTimesMultiplier := argumentDifferenceTimesMultiplier,
    baseArgumentTimesMultiplierDifference := baseArgumentTimesMultiplierDifference,
    argumentCoefficientSquare := argumentCoefficientSquare,
    argumentSquareTimesRemainder := argumentSquareTimesRemainder,
    argumentRemainderTimesMultiplier := argumentRemainderTimesMultiplier,
    parameterArgumentSquare := parameterArgumentSquare,
    parameterRemainder := parameterRemainder, parameterCoefficient := parameterCoefficient }

theorem CoefficientTrace.outputs_contain_of_allSound
    {fixed : FixedTrace} {coordinate coordinateDelta remainder : Rectangle}
    (trace : CoefficientTrace fixed coordinate coordinateDelta remainder)
    (hall : ∀ operation ∈ trace.operations, operation.Sound)
    {u : ℂ} (hu0 : u ≠ 0) (hu : coordinate.Contains u)
    (huDelta : coordinateDelta.Contains (u - chapterVIDCollisionLift))
    (hfixed :
      fixed.powers.inverse.output.Contains chapterVIDCollisionLift⁻¹ ∧
      fixed.powers.square.output.Contains (chapterVIDCollisionLift ^ 2) ∧
      fixed.powers.cube.output.Contains (chapterVIDCollisionLift ^ 3) ∧
      fixed.powers.fourth.output.Contains (chapterVIDCollisionLift ^ 4) ∧
      fixed.powers.inverseSquare.output.Contains (chapterVIDCollisionLift⁻¹ ^ 2) ∧
      fixed.powers.inverseCube.output.Contains (chapterVIDCollisionLift⁻¹ ^ 3) ∧
      fixed.powers.inverseFourth.output.Contains (chapterVIDCollisionLift⁻¹ ^ 4) ∧
      fixed.argumentBase.Contains
        (chapterVIDRootExponentialArgumentDifferenceCoefficient chapterVIDCollisionLift))
    (hremainder : remainder.Contains (chapterVIDExponentialSecondRemainderFactor
      (chapterVIDRootExponentialArgumentDifference u))) :
    trace.quadraticCoefficient.Contains (chapterVIDRootFactorDerivativeQuadraticCoefficient u) ∧
    trace.parameterCoefficient.output.Contains
      (chapterVIDRootFactorDerivativeParameterCoefficient u) ∧
    trace.coordinateData.argument.output.Contains
      (chapterVIDRootExponentialArgumentDifference u) := by
  have soundPart (operations : List (DyadicOperation 20)) (hpart : operations ∈ trace.parts) :
      ∀ operation ∈ operations, operation.Sound := by
    intro operation hoperation
    apply hall operation
    rw [CoefficientTrace.operations, List.mem_flatten]
    exact ⟨operations, hpart, hoperation⟩
  have hc := trace.coordinateData.contains_of_allSound
    (soundPart trace.coordinateData.operations (by simp [CoefficientTrace.parts]))
    hu huDelta hfixed
  rcases hc with ⟨hUSq, hUCube, hUInv, hUInvSq, hUInvCube, hUInvFourth,
    hQuadratic, hInvCubeProduct, hInvCubeDifference, hH, hM, hArgument⟩
  rcases hfixed with ⟨hDInv, hDSq, hDCube, hDFourth, hDInvSq, hDInvCube,
    hDInvFourth, hHBase⟩
  have hUSqD := trace.squareTimesCollision.output_contains_mul_of_allSound
    (soundPart trace.squareTimesCollision.operations (by simp [CoefficientTrace.parts]))
    hUSq collision_contains
  have hUDSq := trace.coordinateTimesCollisionSquare.output_contains_mul_of_allSound
    (soundPart trace.coordinateTimesCollisionSquare.operations
      (by simp [CoefficientTrace.parts])) hu hDSq
  have hInvTwoFirst := trace.inverseTwoFirst.output_contains_mul_of_allSound
    (soundPart trace.inverseTwoFirst.operations (by simp [CoefficientTrace.parts]))
    (ChapterVISignedDyadicComplexRectangle.add_contains hu collision_contains) hUInvSq
  have hInvTwoSecond := trace.inverseTwoSecond.output_contains_mul_of_allSound
    (soundPart trace.inverseTwoSecond.operations (by simp [CoefficientTrace.parts]))
    hInvTwoFirst hDInvSq
  have hInvTwoDifferenceRaw :=
    ChapterVISignedDyadicComplexRectangle.neg_contains hInvTwoSecond
  have hInvTwoDifference : trace.inverseTwoSecond.output.neg.Contains
      (-(u + chapterVIDCollisionLift) /
        (u ^ 2 * chapterVIDCollisionLift ^ 2)) := by
    convert hInvTwoDifferenceRaw using 1
    field_simp [hu0, chapterVIDCollisionLift_ne_zero]
  have hInvFourthProduct := trace.inverseFourthProduct.output_contains_mul_of_allSound
    (soundPart trace.inverseFourthProduct.operations (by simp [CoefficientTrace.parts]))
    hUInvFourth hDInvFourth
  have hFourthPolynomial := ChapterVISignedDyadicComplexRectangle.add_contains
    (ChapterVISignedDyadicComplexRectangle.add_contains
      (ChapterVISignedDyadicComplexRectangle.add_contains hUCube hUSqD) hUDSq) hDCube
  have hInvFourRaw := trace.inverseFourDifferenceProduct.output_contains_mul_of_allSound
    (soundPart trace.inverseFourDifferenceProduct.operations
      (by simp [CoefficientTrace.parts])) hFourthPolynomial hInvFourthProduct
  have hInvFourNeg := ChapterVISignedDyadicComplexRectangle.neg_contains hInvFourRaw
  have hInvFourDifference : trace.inverseFourDifferenceProduct.output.neg.Contains
      (-(u ^ 3 + u ^ 2 * chapterVIDCollisionLift +
        u * chapterVIDCollisionLift ^ 2 + chapterVIDCollisionLift ^ 3) /
        (u ^ 4 * chapterVIDCollisionLift ^ 4)) := by
    convert hInvFourNeg using 1
    field_simp [hu0, chapterVIDCollisionLift_ne_zero]
  have hDSqUInvFourth :=
    trace.collisionSquareTimesInverseFourth.output_contains_mul_of_allSound
      (soundPart trace.collisionSquareTimesInverseFourth.operations
        (by simp [CoefficientTrace.parts])) hDSq hUInvFourth
  have hPowerTerm := trace.powerTerm.output_contains_mul_of_allSound
    (soundPart trace.powerTerm.operations (by simp [CoefficientTrace.parts])) hDInvFourth
    (ChapterVISignedDyadicComplexRectangle.add_contains hUInvSq hDSqUInvFourth)
  have hDSqInvFourDifference :=
    trace.collisionSquareTimesInverseFourDifference.output_contains_mul_of_allSound
      (soundPart trace.collisionSquareTimesInverseFourDifference.operations
        (by simp [CoefficientTrace.parts])) hDSq hInvFourDifference
  have hPowerTermDifference := trace.powerTermDifference.output_contains_mul_of_allSound
    (soundPart trace.powerTermDifference.operations (by simp [CoefficientTrace.parts]))
    hDInvFourth
    (ChapterVISignedDyadicComplexRectangle.add_contains hInvTwoDifference
      hDSqInvFourDifference)
  have hDPowerTermDifference :=
    trace.collisionTimesPowerTermDifference.output_contains_mul_of_allSound
      (soundPart trace.collisionTimesPowerTermDifference.operations
        (by simp [CoefficientTrace.parts])) collision_contains hPowerTermDifference
  have hLaurentCore := ChapterVISignedDyadicComplexRectangle.add_contains
    (ChapterVISignedDyadicComplexRectangle.add_contains
      (ChapterVISignedDyadicComplexRectangle.pointInt_contains 20 30000)
      (ChapterVISignedDyadicComplexRectangle.nsmul_contains 3 hPowerTerm))
    (ChapterVISignedDyadicComplexRectangle.nsmul_contains 6 hDPowerTermDifference)
  have hLaurentRaw := trace.laurentDifference.output_contains_of_allSound
    (soundPart trace.laurentDifference.operations (by simp [CoefficientTrace.parts]))
    inverse10001_contains hLaurentCore
  have hLaurent : trace.laurentDifference.output.Contains
      (chapterVIDRootFactorDerivativeLaurentCoefficientDifference u) := by
    convert hLaurentRaw using 1
    unfold chapterVIDRootFactorDerivativeLaurentCoefficientDifference
    dsimp only
    push_cast
    ring
  have hInvFactorMinusRaw :=
    trace.inverseFactorDifferenceMinus.output_contains_mul_of_allSound
      (soundPart trace.inverseFactorDifferenceMinus.operations
        (by simp [CoefficientTrace.parts])) hDInvCube hInvCubeDifference
  have hInvFactorMinus :=
    ChapterVISignedDyadicComplexRectangle.neg_contains hInvFactorMinusRaw
  have hQuadraticDifference := ChapterVISignedDyadicComplexRectangle.add_contains hu
    (ChapterVISignedDyadicComplexRectangle.nsmul_contains 2 collision_contains)
  have hOne := ChapterVISignedDyadicComplexRectangle.pointInt_contains 20 1
  have hQuadraticMinus := trace.quadraticDifferenceTimesMinus.output_contains_mul_of_allSound
    (soundPart trace.quadraticDifferenceTimesMinus.operations
      (by simp [CoefficientTrace.parts])) hQuadraticDifference
    (ChapterVISignedDyadicComplexRectangle.sub_contains hOne hInvCubeProduct)
  have hDSqInvFactorMinus :=
    trace.collisionSquareTimesInverseFactorDifferenceMinus.output_contains_mul_of_allSound
      (soundPart trace.collisionSquareTimesInverseFactorDifferenceMinus.operations
        (by simp [CoefficientTrace.parts])) hDSq hInvFactorMinus
  have hPowerShapeDifferenceRaw := trace.powerShapeDifference.output_contains_mul_of_allSound
    (soundPart trace.powerShapeDifference.operations (by simp [CoefficientTrace.parts]))
    hDInv (ChapterVISignedDyadicComplexRectangle.add_contains hQuadraticMinus
      (ChapterVISignedDyadicComplexRectangle.nsmul_contains 3 hDSqInvFactorMinus))
  have hPowerShapeDifference : trace.powerShapeDifference.output.Contains
      (chapterVIDRootFactorDerivativePowerShapeCoefficientDifference u) := by
    convert hPowerShapeDifferenceRaw using 1
    unfold chapterVIDRootFactorDerivativePowerShapeCoefficientDifference
    dsimp only
    field_simp [hu0, chapterVIDCollisionLift_ne_zero]
    ring
  have hYPowerShapeDifference :=
    trace.yTimesPowerShapeDifference.output_contains_mul_of_allSound
      (soundPart trace.yTimesPowerShapeDifference.operations
        (by simp [CoefficientTrace.parts])) yBase_contains hPowerShapeDifference
  have hPowerShapeDifferenceScaled :=
    trace.powerShapeDifferenceScaled.output_contains_of_allSound
      (soundPart trace.powerShapeDifferenceScaled.operations
        (by simp [CoefficientTrace.parts])) coefficient200_contains hYPowerShapeDifference
  have hCoordinateDifferenceRaw := ChapterVISignedDyadicComplexRectangle.add_contains
    hLaurent hPowerShapeDifferenceScaled
  have hCoordinateDifference : trace.coordinateCoefficientDifference.Contains
      (chapterVIDRootFactorDerivativeCoordinateCoefficientDifference u) := by
    change (trace.laurentDifference.output.add
      trace.powerShapeDifferenceScaled.output).Contains _
    convert hCoordinateDifferenceRaw using 1
    unfold chapterVIDRootFactorDerivativeCoordinateCoefficientDifference
    push_cast
    ring
  have hInvFactorPlus := trace.inverseFactorDifferencePlus.output_contains_mul_of_allSound
    (soundPart trace.inverseFactorDifferencePlus.operations
      (by simp [CoefficientTrace.parts])) hDInvCube hInvCubeDifference
  have hQuadraticPlus := trace.quadraticDifferenceTimesPlus.output_contains_mul_of_allSound
    (soundPart trace.quadraticDifferenceTimesPlus.operations
      (by simp [CoefficientTrace.parts])) hQuadraticDifference
    (ChapterVISignedDyadicComplexRectangle.add_contains hOne hInvCubeProduct)
  have hDSqInvFactorPlus :=
    trace.collisionSquareTimesInverseFactorDifferencePlus.output_contains_mul_of_allSound
      (soundPart trace.collisionSquareTimesInverseFactorDifferencePlus.operations
        (by simp [CoefficientTrace.parts])) hDSq hInvFactorPlus
  have hArgumentDifferenceScaled :=
    trace.argumentCoefficientDifference.output_contains_of_allSound
      (soundPart trace.argumentCoefficientDifference.operations
        (by simp [CoefficientTrace.parts])) coefficient100_contains
      (ChapterVISignedDyadicComplexRectangle.add_contains hQuadraticPlus
        (ChapterVISignedDyadicComplexRectangle.nsmul_contains 3 hDSqInvFactorPlus))
  have hArgumentDifferenceNeg :=
    ChapterVISignedDyadicComplexRectangle.neg_contains hArgumentDifferenceScaled
  have hArgumentDifference : trace.argumentCoefficientDifference.output.neg.Contains
      (chapterVIDRootExponentialArgumentCoefficientDifference u) := by
    convert hArgumentDifferenceNeg using 1
    unfold chapterVIDRootExponentialArgumentCoefficientDifference
    dsimp only
    push_cast
    field_simp [hu0, chapterVIDCollisionLift_ne_zero]
  have hMultiplierCollision :=
    trace.multiplierDifferenceCollision.output_contains_mul_of_allSound
      (soundPart trace.multiplierDifferenceCollision.operations
        (by simp [CoefficientTrace.parts])) hDInv
      (ChapterVISignedDyadicComplexRectangle.add_contains hInvCubeDifference hQuadratic)
  have hMultiplierY := trace.multiplierDifferenceY.output_contains_mul_of_allSound
    (soundPart trace.multiplierDifferenceY.operations (by simp [CoefficientTrace.parts]))
    yBase_contains hMultiplierCollision
  have hMultiplierDifferenceRaw := trace.multiplierDifference.output_contains_of_allSound
    (soundPart trace.multiplierDifference.operations (by simp [CoefficientTrace.parts]))
    coefficient200_contains hMultiplierY
  have hMultiplierDifference : trace.multiplierDifference.output.Contains
      (chapterVIDRootFactorDerivativeMultiplierCoefficientDifference u) := by
    convert hMultiplierDifferenceRaw using 1
    unfold chapterVIDRootFactorDerivativeMultiplierCoefficientDifference
    dsimp only
    push_cast
    ring
  have hArgumentTimesM := trace.argumentDifferenceTimesMultiplier.output_contains_mul_of_allSound
    (soundPart trace.argumentDifferenceTimesMultiplier.operations
      (by simp [CoefficientTrace.parts])) hArgumentDifference hM
  have hBaseArgumentTimesMultiplierDifference :=
    trace.baseArgumentTimesMultiplierDifference.output_contains_mul_of_allSound
      (soundPart trace.baseArgumentTimesMultiplierDifference.operations
        (by simp [CoefficientTrace.parts])) hHBase hMultiplierDifference
  have hLinearDifferenceRaw := ChapterVISignedDyadicComplexRectangle.add_contains
    (ChapterVISignedDyadicComplexRectangle.add_contains hCoordinateDifference hArgumentTimesM)
    hBaseArgumentTimesMultiplierDifference
  have hLinearDifference : trace.linearCoefficientDifference.Contains
      (chapterVIDRootFactorDerivativeLinearCoefficientDifference u) := by
    change ((trace.coordinateCoefficientDifference.add
      trace.argumentDifferenceTimesMultiplier.output).add
        trace.baseArgumentTimesMultiplierDifference.output).Contains _
    convert hLinearDifferenceRaw using 1
    unfold chapterVIDRootFactorDerivativeLinearCoefficientDifference
    ring
  have hHSquare := trace.argumentCoefficientSquare.output_contains_mul_of_allSound
    (soundPart trace.argumentCoefficientSquare.operations (by simp [CoefficientTrace.parts])) hH hH
  have hHSquareRemainder := trace.argumentSquareTimesRemainder.output_contains_mul_of_allSound
    (soundPart trace.argumentSquareTimesRemainder.operations
      (by simp [CoefficientTrace.parts])) hHSquare hremainder
  have hHRemainderM := trace.argumentRemainderTimesMultiplier.output_contains_mul_of_allSound
    (soundPart trace.argumentRemainderTimesMultiplier.operations
      (by simp [CoefficientTrace.parts])) hHSquareRemainder hM
  have hQuadraticCoefficientRaw := ChapterVISignedDyadicComplexRectangle.add_contains
    hLinearDifference hHRemainderM
  have hQuadraticCoefficient : trace.quadraticCoefficient.Contains
      (chapterVIDRootFactorDerivativeQuadraticCoefficient u) := by
    change (trace.linearCoefficientDifference.add
      trace.argumentRemainderTimesMultiplier.output).Contains _
    convert hQuadraticCoefficientRaw using 1
    unfold chapterVIDRootFactorDerivativeQuadraticCoefficient
    dsimp only
    ring
  have hParameterArgumentSquare := trace.parameterArgumentSquare.output_contains_mul_of_allSound
    (soundPart trace.parameterArgumentSquare.operations (by simp [CoefficientTrace.parts]))
    hArgument hArgument
  have hParameterRemainder := trace.parameterRemainder.output_contains_mul_of_allSound
    (soundPart trace.parameterRemainder.operations (by simp [CoefficientTrace.parts]))
    hParameterArgumentSquare hremainder
  have hParameterInput := ChapterVISignedDyadicComplexRectangle.add_contains
    (ChapterVISignedDyadicComplexRectangle.add_contains hOne hArgument) hParameterRemainder
  have hParameterCoefficientRaw := trace.parameterCoefficient.output_contains_mul_of_allSound
    (soundPart trace.parameterCoefficient.operations (by simp [CoefficientTrace.parts]))
    hParameterInput hM
  have hParameterCoefficient : trace.parameterCoefficient.output.Contains
      (chapterVIDRootFactorDerivativeParameterCoefficient u) := by
    convert hParameterCoefficientRaw using 1
    unfold chapterVIDRootFactorDerivativeParameterCoefficient
    dsimp only
    ring
  exact ⟨hQuadraticCoefficient, hParameterCoefficient, hArgument⟩

/-! ## Homogeneous collar cells -/

def baseDirection : ChapterVIDOuterArcSide → Rectangle
  | .initial => ⟨collision.real.neg, collision.real.neg⟩
  | .final => ⟨collision.real.neg, collision.real⟩

theorem baseDirection_contains (side : ChapterVIDOuterArcSide) :
    (baseDirection side).Contains (chapterVIDCollapsedConnectorDirection side) := by
  have hD := collision_contains
  have hDre := hD.1
  rw [chapterVIDCollisionLift_eq_neg_norm] at hDre
  cases side with
  | initial =>
      unfold baseDirection chapterVIDCollapsedConnectorDirection
      constructor
      · simpa [Complex.mul_re] using ChapterVISignedDyadicInterval.neg_contains hDre
      · simpa [Complex.mul_im] using ChapterVISignedDyadicInterval.neg_contains hDre
  | final =>
      unfold baseDirection chapterVIDCollapsedConnectorDirection
      constructor
      · simpa [Complex.mul_re] using ChapterVISignedDyadicInterval.neg_contains hDre
      · simpa [Complex.mul_im] using hDre

def distanceCell (index : Fin 160) : Interval :=
  ⟨(Int.ofNat index * 1671 : ℤ), (Int.ofNat (index + 1) * 1671 : ℤ)⟩

def signedRectangle (side : ChapterVIDOuterArcSide) (x : Rectangle) : Rectangle :=
  match side with
  | .initial => x.neg
  | .final => x

theorem signedRectangle_contains (side : ChapterVIDOuterArcSide)
    {x : Rectangle} {z : ℂ} (hz : x.Contains z) :
    (signedRectangle side x).Contains ((chapterVIDMorseSideSign side : ℝ) * z) := by
  cases side with
  | initial =>
      simpa [signedRectangle, chapterVIDMorseSideSign] using
        ChapterVISignedDyadicComplexRectangle.neg_contains hz
  | final => simpa [signedRectangle, chapterVIDMorseSideSign] using hz

def traceDirection (side : ChapterVIDOuterArcSide)
    (lengthSquareTimesOuter lengthTimesEndpoint : Rectangle) : Rectangle :=
  ((baseDirection side).add lengthSquareTimesOuter).sub
    (signedRectangle side lengthTimesEndpoint)

def traceCoordinateDelta (side : ChapterVIDOuterArcSide)
    (lengthTimesEndpoint distanceTimesDirection : Rectangle) : Rectangle :=
  (signedRectangle side lengthTimesEndpoint).add distanceTimesDirection

structure CellTrace (fixed : FixedTrace) (side : ChapterVIDOuterArcSide)
    (distance : Interval) where
  lengthSquareTimesOuter : Rectangle.RealMulTrace
    (ChapterVILeanCompCertProposals.mul 20 length length) unitSquare
  lengthTimesEndpoint : Rectangle.RealMulTrace length normalizedEndpoint
  distanceTimesDirection : Rectangle.RealMulTrace distance
    (traceDirection side lengthSquareTimesOuter.output lengthTimesEndpoint.output)
  coefficients : CoefficientTrace fixed
    (collision.add (traceCoordinateDelta side lengthTimesEndpoint.output
      distanceTimesDirection.output))
    (traceCoordinateDelta side lengthTimesEndpoint.output distanceTimesDirection.output)
    unitSquare
  linearTimesSignedEndpoint : Rectangle.MulTrace baseLinear
    (signedRectangle side normalizedEndpoint)
  endpointLinearTerm : Rectangle.MulTrace linearTimesSignedEndpoint.output
    (traceDirection side lengthSquareTimesOuter.output lengthTimesEndpoint.output)
  lengthTimesOuter : Rectangle.RealMulTrace length unitSquare
  linearTimesDirectionCorrection : Rectangle.MulTrace baseLinear
    (lengthTimesOuter.output.sub (signedRectangle side normalizedEndpoint))
  correctionTimesDirections : Rectangle.MulTrace linearTimesDirectionCorrection.output
    ((traceDirection side lengthSquareTimesOuter.output lengthTimesEndpoint.output).add
      (baseDirection side))
  distanceTimesCorrection : Rectangle.RealMulTrace distance correctionTimesDirections.output
  endpointSquare : Rectangle.MulTrace normalizedEndpoint normalizedEndpoint
  lengthTimesEndpointSquare : Rectangle.RealMulTrace length endpointSquare.output
  endpointTimesDirection : Rectangle.MulTrace normalizedEndpoint
    (traceDirection side lengthSquareTimesOuter.output lengthTimesEndpoint.output)
  distanceTimesEndpointDirection : Rectangle.RealMulTrace distance endpointTimesDirection.output
  quadraticInputTimesCoefficient : Rectangle.MulTrace
    (lengthTimesEndpointSquare.output.add
      ((signedRectangle side distanceTimesEndpointDirection.output).nsmul 2))
    coefficients.quadraticCoefficient
  quadraticEndpointTerm : Rectangle.MulTrace quadraticInputTimesCoefficient.output
    (traceDirection side lengthSquareTimesOuter.output lengthTimesEndpoint.output)
  lengthTimesParameter : Rectangle.RealMulTrace length unitSquare
  parameterTimesCoefficient : Rectangle.MulTrace lengthTimesParameter.output
    coefficients.parameterCoefficient.output
  parameterEndpointTerm : Rectangle.MulTrace parameterTimesCoefficient.output
    (traceDirection side lengthSquareTimesOuter.output lengthTimesEndpoint.output)
  directionCube : Rectangle.CubeTrace
    (traceDirection side lengthSquareTimesOuter.output lengthTimesEndpoint.output)
  distanceCoefficient : Rectangle.MulTrace directionCube.output
    coefficients.quadraticCoefficient

def CellTrace.direction {fixed : FixedTrace} {side : ChapterVIDOuterArcSide}
    {distance : Interval} (trace : CellTrace fixed side distance) : Rectangle :=
  traceDirection side trace.lengthSquareTimesOuter.output trace.lengthTimesEndpoint.output

def CellTrace.coordinateDelta {fixed : FixedTrace} {side : ChapterVIDOuterArcSide}
    {distance : Interval} (trace : CellTrace fixed side distance) : Rectangle :=
  traceCoordinateDelta side trace.lengthTimesEndpoint.output trace.distanceTimesDirection.output

def CellTrace.endpointCoefficient {fixed : FixedTrace} {side : ChapterVIDOuterArcSide}
    {distance : Interval} (trace : CellTrace fixed side distance) : Rectangle :=
  ((trace.endpointLinearTerm.output.add trace.distanceTimesCorrection.output).add
    trace.quadraticEndpointTerm.output).add trace.parameterEndpointTerm.output

def CellTrace.argumentNorm (trace : CellTrace fixed side distance) : Interval :=
  l1NormInterval trace.coefficients.coordinateData.argument.output

def CellTrace.argumentNormBound (trace : CellTrace fixed side distance) :
    trace.coefficients.coordinateData.argument.output.L1NormBound trace.argumentNorm :=
  l1NormBound _

def CellTrace.argumentNormClaim (trace : CellTrace fixed side distance) : Claim :=
  productClaim trace.argumentNorm.upper 1 (2 ^ 20) 1

def CellTrace.parts (trace : CellTrace fixed side distance) :
    List (List (DyadicOperation 20)) :=
  [ trace.lengthSquareTimesOuter.operations, trace.lengthTimesEndpoint.operations,
    trace.distanceTimesDirection.operations, trace.coefficients.operations,
    trace.linearTimesSignedEndpoint.operations, trace.endpointLinearTerm.operations,
    trace.lengthTimesOuter.operations, trace.linearTimesDirectionCorrection.operations,
    trace.correctionTimesDirections.operations, trace.distanceTimesCorrection.operations,
    trace.endpointSquare.operations, trace.lengthTimesEndpointSquare.operations,
    trace.endpointTimesDirection.operations, trace.distanceTimesEndpointDirection.operations,
    trace.quadraticInputTimesCoefficient.operations, trace.quadraticEndpointTerm.operations,
    trace.lengthTimesParameter.operations, trace.parameterTimesCoefficient.operations,
    trace.parameterEndpointTerm.operations, trace.directionCube.operations,
    trace.distanceCoefficient.operations,
    [.mul length length (ChapterVILeanCompCertProposals.mul 20 length length),
      .rawClaim trace.argumentNormClaim,
      .positiveLower trace.endpointCoefficient.real,
      .positiveLower trace.distanceCoefficient.output.real] ]

def CellTrace.operations (trace : CellTrace fixed side distance) : List (DyadicOperation 20) :=
  trace.parts.flatten

def cellTrace (fixed : FixedTrace) (side : ChapterVIDOuterArcSide) (distance : Interval) :
    CellTrace fixed side distance :=
  let lengthSquareRaw := mul 20 length length
  let lengthSquareTimesOuter := realMulTrace lengthSquareRaw unitSquare
  let lengthTimesEndpoint := realMulTrace length normalizedEndpoint
  let direction := ((baseDirection side).add lengthSquareTimesOuter.output).sub
    (signedRectangle side lengthTimesEndpoint.output)
  let distanceTimesDirection := realMulTrace distance direction
  let coordinateDelta := (signedRectangle side lengthTimesEndpoint.output).add
    distanceTimesDirection.output
  let coefficients := coefficientTrace fixed (collision.add coordinateDelta)
    coordinateDelta unitSquare
  let linearTimesSignedEndpoint := mulTrace baseLinear
    (signedRectangle side normalizedEndpoint)
  let endpointLinearTerm := mulTrace linearTimesSignedEndpoint.output direction
  let lengthTimesOuter := realMulTrace length unitSquare
  let linearTimesDirectionCorrection := mulTrace baseLinear
    (lengthTimesOuter.output.sub (signedRectangle side normalizedEndpoint))
  let correctionTimesDirections := mulTrace linearTimesDirectionCorrection.output
    (direction.add (baseDirection side))
  let distanceTimesCorrection := realMulTrace distance correctionTimesDirections.output
  let endpointSquare := mulTrace normalizedEndpoint normalizedEndpoint
  let lengthTimesEndpointSquare := realMulTrace length endpointSquare.output
  let endpointTimesDirection := mulTrace normalizedEndpoint direction
  let distanceTimesEndpointDirection := realMulTrace distance endpointTimesDirection.output
  let quadraticInput := lengthTimesEndpointSquare.output.add
    ((signedRectangle side distanceTimesEndpointDirection.output).nsmul 2)
  let quadraticInputTimesCoefficient := mulTrace quadraticInput coefficients.quadraticCoefficient
  let quadraticEndpointTerm := mulTrace quadraticInputTimesCoefficient.output direction
  let lengthTimesParameter := realMulTrace length unitSquare
  let parameterTimesCoefficient := mulTrace lengthTimesParameter.output
    coefficients.parameterCoefficient.output
  let parameterEndpointTerm := mulTrace parameterTimesCoefficient.output direction
  let directionCube := cubeTrace direction
  let distanceCoefficient := mulTrace directionCube.output coefficients.quadraticCoefficient
  { lengthSquareTimesOuter := lengthSquareTimesOuter,
    lengthTimesEndpoint := lengthTimesEndpoint,
    distanceTimesDirection := distanceTimesDirection, coefficients := coefficients,
    linearTimesSignedEndpoint := linearTimesSignedEndpoint,
    endpointLinearTerm := endpointLinearTerm, lengthTimesOuter := lengthTimesOuter,
    linearTimesDirectionCorrection := linearTimesDirectionCorrection,
    correctionTimesDirections := correctionTimesDirections,
    distanceTimesCorrection := distanceTimesCorrection, endpointSquare := endpointSquare,
    lengthTimesEndpointSquare := lengthTimesEndpointSquare,
    endpointTimesDirection := endpointTimesDirection,
    distanceTimesEndpointDirection := distanceTimesEndpointDirection,
    quadraticInputTimesCoefficient := quadraticInputTimesCoefficient,
    quadraticEndpointTerm := quadraticEndpointTerm,
    lengthTimesParameter := lengthTimesParameter,
    parameterTimesCoefficient := parameterTimesCoefficient,
    parameterEndpointTerm := parameterEndpointTerm, directionCube := directionCube,
    distanceCoefficient := distanceCoefficient }

theorem CellTrace.outputs_contain_of_allSound
    {fixed : FixedTrace} {side : ChapterVIDOuterArcSide} {distance : Interval}
    (trace : CellTrace fixed side distance)
    (hall : ∀ operation ∈ trace.operations, operation.Sound)
    {L δ : ℝ} {q r p : ℂ}
    (hL : length.Contains L) (hδ : distance.Contains δ)
    (hq : normalizedEndpoint.Contains q) (hr : unitSquare.Contains r)
    (hp : unitSquare.Contains p)
    (hfixed :
      fixed.powers.inverse.output.Contains chapterVIDCollisionLift⁻¹ ∧
      fixed.powers.square.output.Contains (chapterVIDCollisionLift ^ 2) ∧
      fixed.powers.cube.output.Contains (chapterVIDCollisionLift ^ 3) ∧
      fixed.powers.fourth.output.Contains (chapterVIDCollisionLift ^ 4) ∧
      fixed.powers.inverseSquare.output.Contains (chapterVIDCollisionLift⁻¹ ^ 2) ∧
      fixed.powers.inverseCube.output.Contains (chapterVIDCollisionLift⁻¹ ^ 3) ∧
      fixed.powers.inverseFourth.output.Contains (chapterVIDCollisionLift⁻¹ ^ 4) ∧
      fixed.argumentBase.Contains
        (chapterVIDRootExponentialArgumentDifferenceCoefficient chapterVIDCollisionLift))
    (hu0 : chapterVIDCollisionLift +
      (chapterVIDMorseSideSign side * L : ℝ) * q + δ *
        chapterVIDHomogeneousConnectorDirection side L q r ≠ 0) :
    trace.endpointCoefficient.Contains
      (chapterVIDHomogeneousEndpointCoefficient side L δ q r p
        (chapterVIDRootFactorDerivativeQuadraticCoefficient
          (chapterVIDCollisionLift +
            (chapterVIDMorseSideSign side * L : ℝ) * q + δ *
              chapterVIDHomogeneousConnectorDirection side L q r))
        (chapterVIDRootFactorDerivativeParameterCoefficient
          (chapterVIDCollisionLift +
            (chapterVIDMorseSideSign side * L : ℝ) * q + δ *
              chapterVIDHomogeneousConnectorDirection side L q r))) ∧
    trace.distanceCoefficient.output.Contains
      (chapterVIDHomogeneousDistanceCoefficient side L q r
        (chapterVIDRootFactorDerivativeQuadraticCoefficient
          (chapterVIDCollisionLift +
            (chapterVIDMorseSideSign side * L : ℝ) * q + δ *
              chapterVIDHomogeneousConnectorDirection side L q r))) := by
  have soundPart (operations : List (DyadicOperation 20)) (hpart : operations ∈ trace.parts) :
      ∀ operation ∈ operations, operation.Sound := by
    intro operation hoperation
    apply hall operation
    rw [CellTrace.operations, List.mem_flatten]
    exact ⟨operations, hpart, hoperation⟩
  let lengthSquareRaw := ChapterVILeanCompCertProposals.mul 20 length length
  have hLengthSquareCertificate : ChapterVISignedDyadicInterval.MulCertificate
      length length lengthSquareRaw := by
    exact hall (.mul length length lengthSquareRaw) (by
      simp [CellTrace.operations, CellTrace.parts, lengthSquareRaw])
  have hLengthSquare := hLengthSquareCertificate.contains_mul hL hL
  have hLengthSquareOuter := trace.lengthSquareTimesOuter.output_contains_of_allSound
    (soundPart trace.lengthSquareTimesOuter.operations (by simp [CellTrace.parts]))
    hLengthSquare hr
  have hLengthEndpoint := trace.lengthTimesEndpoint.output_contains_of_allSound
    (soundPart trace.lengthTimesEndpoint.operations (by simp [CellTrace.parts])) hL hq
  have hSignedLengthEndpoint := signedRectangle_contains side hLengthEndpoint
  have hDirectionRaw := ChapterVISignedDyadicComplexRectangle.sub_contains
    (ChapterVISignedDyadicComplexRectangle.add_contains (baseDirection_contains side)
      hLengthSquareOuter) hSignedLengthEndpoint
  have hDirection : trace.direction.Contains
      (chapterVIDHomogeneousConnectorDirection side L q r) := by
    have hvalue : chapterVIDCollapsedConnectorDirection side + (L * L : ℝ) * r -
        (chapterVIDMorseSideSign side : ℂ) * ((L : ℂ) * q) =
        chapterVIDHomogeneousConnectorDirection side L q r := by
      unfold chapterVIDHomogeneousConnectorDirection
      push_cast
      ring
    rw [← hvalue]
    simpa [CellTrace.direction, traceDirection] using hDirectionRaw
  have hDistanceDirection := trace.distanceTimesDirection.output_contains_of_allSound
    (soundPart trace.distanceTimesDirection.operations (by simp [CellTrace.parts])) hδ hDirection
  have hCoordinateDeltaRaw := ChapterVISignedDyadicComplexRectangle.add_contains
    hSignedLengthEndpoint hDistanceDirection
  have hCoordinateDelta :
      (traceCoordinateDelta side trace.lengthTimesEndpoint.output
        trace.distanceTimesDirection.output).Contains
      ((chapterVIDMorseSideSign side * L : ℝ) * q + δ *
        chapterVIDHomogeneousConnectorDirection side L q r) := by
    have hvalue : (chapterVIDMorseSideSign side : ℂ) * ((L : ℂ) * q) +
        (δ : ℂ) * chapterVIDHomogeneousConnectorDirection side L q r =
        ((chapterVIDMorseSideSign side * L : ℝ) : ℂ) * q +
          (δ : ℂ) * chapterVIDHomogeneousConnectorDirection side L q r := by
      push_cast
      ring
    rw [← hvalue]
    simpa [traceCoordinateDelta] using hCoordinateDeltaRaw
  let u := chapterVIDCollisionLift +
    (chapterVIDMorseSideSign side * L : ℝ) * q + δ *
      chapterVIDHomogeneousConnectorDirection side L q r
  have hCoordinate : (collision.add trace.coordinateDelta).Contains u := by
    have hdelta : trace.coordinateDelta.Contains
        ((chapterVIDMorseSideSign side * L : ℝ) * q + δ *
          chapterVIDHomogeneousConnectorDirection side L q r) := by
      simpa [CellTrace.coordinateDelta] using hCoordinateDelta
    have := ChapterVISignedDyadicComplexRectangle.add_contains collision_contains hdelta
    simpa [u, add_assoc] using this
  have hCoordinateData := trace.coefficients.coordinateData.contains_of_allSound
    (by
      intro operation hoperation
      exact soundPart trace.coefficients.operations (by simp [CellTrace.parts]) operation
        (by
          rw [CoefficientTrace.operations, List.mem_flatten]
          exact ⟨trace.coefficients.coordinateData.operations,
            by simp [CoefficientTrace.parts], hoperation⟩))
    hCoordinate (by simpa [u, add_assoc] using hCoordinateDelta) hfixed
  rcases hCoordinateData with
    ⟨_, _, _, _, _, _, _, _, _, _, _, hArgument⟩
  have hArgumentNorm := trace.argumentNormBound.contains_norm hArgument
  have hNormClaim : trace.argumentNormClaim.Holds := by
    exact hall (.rawClaim trace.argumentNormClaim) (by
      simp [CellTrace.operations, CellTrace.parts])
  have hNormUpper : trace.argumentNorm.upper ≤ (2 ^ 20 : ℤ) := by
    simpa [CellTrace.argumentNormClaim, productClaim_holds_iff] using hNormClaim
  have hArgumentNormLeOne :
      ‖chapterVIDRootExponentialArgumentDifference u‖ ≤ 1 := by
    apply hArgumentNorm.2.trans
    change (trace.argumentNorm.upper : ℝ) / (2 : ℝ) ^ 20 ≤ 1
    rw [div_le_one (by positivity)]
    exact_mod_cast hNormUpper
  have hRemainder : unitSquare.Contains
      (chapterVIDExponentialSecondRemainderFactor
        (chapterVIDRootExponentialArgumentDifference u)) :=
    unitSquare_contains_of_norm_le_one
      (norm_chapterVIDExponentialSecondRemainderFactor_le_one hArgumentNormLeOne)
  have hCoefficientOutputs := trace.coefficients.outputs_contain_of_allSound
    (soundPart trace.coefficients.operations (by simp [CellTrace.parts]))
    (by simpa [u] using hu0) hCoordinate
    (by simpa [u, add_assoc] using hCoordinateDelta) hfixed hRemainder
  rcases hCoefficientOutputs with ⟨hK, hP, _⟩
  have hSignedQ := signedRectangle_contains side hq
  have hLinearSignedQ := trace.linearTimesSignedEndpoint.output_contains_mul_of_allSound
    (soundPart trace.linearTimesSignedEndpoint.operations (by simp [CellTrace.parts]))
    baseLinear_contains hSignedQ
  have hEndpointLinear := trace.endpointLinearTerm.output_contains_mul_of_allSound
    (soundPart trace.endpointLinearTerm.operations (by simp [CellTrace.parts]))
    hLinearSignedQ hDirection
  have hLengthOuter := trace.lengthTimesOuter.output_contains_of_allSound
    (soundPart trace.lengthTimesOuter.operations (by simp [CellTrace.parts])) hL hr
  have hDirectionCorrection := ChapterVISignedDyadicComplexRectangle.sub_contains
    hLengthOuter (signedRectangle_contains side hq)
  have hLinearCorrection := trace.linearTimesDirectionCorrection.output_contains_mul_of_allSound
    (soundPart trace.linearTimesDirectionCorrection.operations
      (by simp [CellTrace.parts])) baseLinear_contains hDirectionCorrection
  have hDirections := ChapterVISignedDyadicComplexRectangle.add_contains hDirection
    (baseDirection_contains side)
  have hCorrectionDirections := trace.correctionTimesDirections.output_contains_mul_of_allSound
    (soundPart trace.correctionTimesDirections.operations (by simp [CellTrace.parts]))
    hLinearCorrection hDirections
  have hDistanceCorrection := trace.distanceTimesCorrection.output_contains_of_allSound
    (soundPart trace.distanceTimesCorrection.operations (by simp [CellTrace.parts]))
    hδ hCorrectionDirections
  have hQSquare := trace.endpointSquare.output_contains_mul_of_allSound
    (soundPart trace.endpointSquare.operations (by simp [CellTrace.parts])) hq hq
  have hLQSquare := trace.lengthTimesEndpointSquare.output_contains_of_allSound
    (soundPart trace.lengthTimesEndpointSquare.operations (by simp [CellTrace.parts])) hL hQSquare
  have hQDirection := trace.endpointTimesDirection.output_contains_mul_of_allSound
    (soundPart trace.endpointTimesDirection.operations (by simp [CellTrace.parts])) hq hDirection
  have hDistanceQDirection := trace.distanceTimesEndpointDirection.output_contains_of_allSound
    (soundPart trace.distanceTimesEndpointDirection.operations (by simp [CellTrace.parts]))
    hδ hQDirection
  have hSignedDistanceQDirection := signedRectangle_contains side hDistanceQDirection
  have hQuadraticInput := ChapterVISignedDyadicComplexRectangle.add_contains hLQSquare
    (ChapterVISignedDyadicComplexRectangle.nsmul_contains 2 hSignedDistanceQDirection)
  have hQuadraticTimesCoefficient :=
    trace.quadraticInputTimesCoefficient.output_contains_mul_of_allSound
      (soundPart trace.quadraticInputTimesCoefficient.operations
        (by simp [CellTrace.parts])) hQuadraticInput hK
  have hQuadraticEndpoint := trace.quadraticEndpointTerm.output_contains_mul_of_allSound
    (soundPart trace.quadraticEndpointTerm.operations (by simp [CellTrace.parts]))
    hQuadraticTimesCoefficient hDirection
  have hLengthParameter := trace.lengthTimesParameter.output_contains_of_allSound
    (soundPart trace.lengthTimesParameter.operations (by simp [CellTrace.parts])) hL hp
  have hParameterCoefficient := trace.parameterTimesCoefficient.output_contains_mul_of_allSound
    (soundPart trace.parameterTimesCoefficient.operations (by simp [CellTrace.parts]))
    hLengthParameter hP
  have hParameterEndpoint := trace.parameterEndpointTerm.output_contains_mul_of_allSound
    (soundPart trace.parameterEndpointTerm.operations (by simp [CellTrace.parts]))
    hParameterCoefficient hDirection
  have hEndpointRaw := ChapterVISignedDyadicComplexRectangle.add_contains
    (ChapterVISignedDyadicComplexRectangle.add_contains
      (ChapterVISignedDyadicComplexRectangle.add_contains hEndpointLinear hDistanceCorrection)
      hQuadraticEndpoint) hParameterEndpoint
  have hEndpoint : trace.endpointCoefficient.Contains
      (chapterVIDHomogeneousEndpointCoefficient side L δ q r p
        (chapterVIDRootFactorDerivativeQuadraticCoefficient u)
        (chapterVIDRootFactorDerivativeParameterCoefficient u)) := by
    change (((trace.endpointLinearTerm.output.add trace.distanceTimesCorrection.output).add
      trace.quadraticEndpointTerm.output).add trace.parameterEndpointTerm.output).Contains _
    convert hEndpointRaw using 1
    unfold chapterVIDHomogeneousEndpointCoefficient
    dsimp only
    push_cast
    ring
  have hDirectionCube := trace.directionCube.output_contains_cube_of_allSound
    (soundPart trace.directionCube.operations (by simp [CellTrace.parts])) hDirection
  have hDistanceCoefficient := trace.distanceCoefficient.output_contains_mul_of_allSound
    (soundPart trace.distanceCoefficient.operations (by simp [CellTrace.parts]))
    hDirectionCube hK
  have hDistance : trace.distanceCoefficient.output.Contains
      (chapterVIDHomogeneousDistanceCoefficient side L q r
        (chapterVIDRootFactorDerivativeQuadraticCoefficient u)) := by
    simpa [chapterVIDHomogeneousDistanceCoefficient] using hDistanceCoefficient
  constructor
  · exact hEndpoint
  · exact hDistance

theorem CellTrace.coefficients_pos_of_allSound
    {fixed : FixedTrace} {side : ChapterVIDOuterArcSide} {distance : Interval}
    (trace : CellTrace fixed side distance)
    (hall : ∀ operation ∈ trace.operations, operation.Sound)
    {L δ : ℝ} {q r p : ℂ}
    (hL : length.Contains L) (hδ : distance.Contains δ)
    (hq : normalizedEndpoint.Contains q) (hr : unitSquare.Contains r)
    (hp : unitSquare.Contains p)
    (hfixed :
      fixed.powers.inverse.output.Contains chapterVIDCollisionLift⁻¹ ∧
      fixed.powers.square.output.Contains (chapterVIDCollisionLift ^ 2) ∧
      fixed.powers.cube.output.Contains (chapterVIDCollisionLift ^ 3) ∧
      fixed.powers.fourth.output.Contains (chapterVIDCollisionLift ^ 4) ∧
      fixed.powers.inverseSquare.output.Contains (chapterVIDCollisionLift⁻¹ ^ 2) ∧
      fixed.powers.inverseCube.output.Contains (chapterVIDCollisionLift⁻¹ ^ 3) ∧
      fixed.powers.inverseFourth.output.Contains (chapterVIDCollisionLift⁻¹ ^ 4) ∧
      fixed.argumentBase.Contains
        (chapterVIDRootExponentialArgumentDifferenceCoefficient chapterVIDCollisionLift))
    (hu0 : chapterVIDCollisionLift +
      (chapterVIDMorseSideSign side * L : ℝ) * q + δ *
        chapterVIDHomogeneousConnectorDirection side L q r ≠ 0) :
    0 < (chapterVIDHomogeneousEndpointCoefficient side L δ q r p
      (chapterVIDRootFactorDerivativeQuadraticCoefficient
        (chapterVIDCollisionLift +
          (chapterVIDMorseSideSign side * L : ℝ) * q + δ *
            chapterVIDHomogeneousConnectorDirection side L q r))
      (chapterVIDRootFactorDerivativeParameterCoefficient
        (chapterVIDCollisionLift +
          (chapterVIDMorseSideSign side * L : ℝ) * q + δ *
            chapterVIDHomogeneousConnectorDirection side L q r))).re ∧
    0 < (chapterVIDHomogeneousDistanceCoefficient side L q r
      (chapterVIDRootFactorDerivativeQuadraticCoefficient
        (chapterVIDCollisionLift +
          (chapterVIDMorseSideSign side * L : ℝ) * q + δ *
            chapterVIDHomogeneousConnectorDirection side L q r))).re := by
  have houtputs := trace.outputs_contain_of_allSound hall hL hδ hq hr hp hfixed hu0
  have hEndpointLower : 0 < trace.endpointCoefficient.real.lower := by
    exact hall (.positiveLower trace.endpointCoefficient.real) (by
      simp [CellTrace.operations, CellTrace.parts])
  have hDistanceLower : 0 < trace.distanceCoefficient.output.real.lower := by
    exact hall (.positiveLower trace.distanceCoefficient.output.real) (by
      simp [CellTrace.operations, CellTrace.parts])
  constructor
  · have hlower : 0 < (trace.endpointCoefficient.real.lower : ℝ) / (2 : ℝ) ^ 20 :=
      div_pos (by exact_mod_cast hEndpointLower) (by positivity)
    exact hlower.trans_le houtputs.1.1.1
  · have hlower : 0 < (trace.distanceCoefficient.output.real.lower : ℝ) /
        (2 : ℝ) ^ 20 := div_pos (by exact_mod_cast hDistanceLower) (by positivity)
    exact hlower.trans_le houtputs.2.1.1

/-! ## Ten-row LeanCompCert shards -/

def shardCellIndex (shard : Fin 16) (offset : Fin 10) : Fin 160 :=
  ⟨10 * (shard : Nat) + (offset : Nat), by
    have hs := shard.isLt
    have ho := offset.isLt
    omega⟩

def referenceCellTrace (side : ChapterVIDOuterArcSide) (index : Fin 160) :
    CellTrace fixedTrace side (distanceCell index) :=
  cellTrace fixedTrace side (distanceCell index)

def shardOperations (side : ChapterVIDOuterArcSide) (shard : Fin 16) :
    List (DyadicOperation 20) :=
  fixedTrace.operations ++ (List.finRange 10).flatMap (fun offset : Fin 10 ↦
    (referenceCellTrace side (shardCellIndex shard offset)).operations)

def sideLabel : ChapterVIDOuterArcSide → String
  | .initial => "initial"
  | .final => "final"

def shardArtifactName (side : ChapterVIDOuterArcSide) (shard : Fin 16) : String :=
  s!"chapter_vi_homogeneous_seam_{sideLabel side}_{shard.val}"

/-- Bounded-fragment proof kept separate from execution, following the other large Chapter VI
campaigns. -/
structure ReferenceAdmissibility : Prop where
  shard : ∀ side shard, Admissible (batchClaims (shardOperations side shard))

/-- The 32 external observations: every exact Lean-derived ten-row artifact returned zero. -/
structure ReferenceRunVerdict (admissibility : ReferenceAdmissibility) : Prop where
  returnsZero : ∀ side shard,
    (batchComputation (shardArtifactName side shard)
      (shardOperations side shard)).Returns ((0 : Nat) : Int)

/-- Hash-bound receipts turn successful executions of the exact Lean-derived artifacts into the
run verdict consumed by the semantic proof.  `RunAdmission` is intentionally the sole empirical
boundary: it records that the identified binary was actually executed. -/
theorem ReferenceRunVerdict.ofReceipts
    (admissibility : ReferenceAdmissibility)
    (crypto : LeanCompCert.Attest.ReceiptCrypto)
    (receipt : ChapterVIDOuterArcSide → Fin 16 → LeanCompCert.Attest.RunReceipt)
    (kind : ChapterVIDOuterArcSide → Fin 16 → LeanCompCert.Attest.AttestationKind)
    (params nonce : ChapterVIDOuterArcSide → Fin 16 → String)
    (bound : ∀ side shard,
      LeanCompCert.Attest.receiptBindsProved crypto
        (batchArtifact (shardArtifactName side shard) (shardOperations side shard))
        (kind side shard) (params side shard) (nonce side shard) ((0 : Nat) : Int)
        (receipt side shard) = true)
    (admitted : ∀ side shard,
      LeanCompCert.Attest.RunAdmission crypto
        (batchArtifact (shardArtifactName side shard) (shardOperations side shard))
        (receipt side shard)) : ReferenceRunVerdict admissibility where
  returnsZero side shard :=
    returns_zero_of_receipt (shardArtifactName side shard) (shardOperations side shard)
      crypto (receipt side shard) (kind side shard) (params side shard) (nonce side shard)
      (bound side shard) (admitted side shard)

theorem shardCellIndex_div_mod (index : Fin 160) :
    shardCellIndex ⟨(index : Nat) / 10, by omega⟩ ⟨(index : Nat) % 10, Nat.mod_lt _ (by omega)⟩ =
      index := by
  apply Fin.ext
  simp [shardCellIndex]
  omega

theorem referenceCell_allSound
    (admissibility : ReferenceAdmissibility)
    (verdict : ReferenceRunVerdict admissibility)
    (side : ChapterVIDOuterArcSide) (index : Fin 160) :
    ∀ operation ∈ (referenceCellTrace side index).operations, operation.Sound := by
  let shard : Fin 16 := ⟨(index : Nat) / 10, by omega⟩
  let offset : Fin 10 := ⟨(index : Nat) % 10, Nat.mod_lt _ (by omega)⟩
  have hindex : shardCellIndex shard offset = index := by
    simpa [shard, offset] using shardCellIndex_div_mod index
  have hall := allSound_of_returns_zero (shardArtifactName side shard)
    (shardOperations side shard) (admissibility.shard side shard)
    (verdict.returnsZero side shard)
  intro operation hoperation
  apply hall operation
  rw [shardOperations, List.mem_append]
  right
  rw [List.mem_flatMap]
  refine ⟨offset, by simp, ?_⟩
  rw [← hindex] at hoperation
  exact hoperation

theorem fixed_allSound
    (admissibility : ReferenceAdmissibility)
    (verdict : ReferenceRunVerdict admissibility) :
    ∀ operation ∈ fixedTrace.operations, operation.Sound := by
  have hall := allSound_of_returns_zero (shardArtifactName .initial ⟨0, by omega⟩)
    (shardOperations .initial ⟨0, by omega⟩)
    (admissibility.shard .initial ⟨0, by omega⟩)
    (verdict.returnsZero .initial ⟨0, by omega⟩)
  intro operation hoperation
  exact hall operation (by simp [shardOperations, hoperation])

theorem exists_distanceCell_contains {δ : ℝ}
    (hδnonneg : 0 ≤ δ) (hδupper : δ ≤ 261 / 1024) :
    ∃ index : Fin 160, (distanceCell index).Contains δ := by
  let width : ℝ := 1671 / (2 : ℝ) ^ 20
  have hwidth : 0 < width := by positivity
  have hratioNonneg : 0 ≤ δ / width := div_nonneg hδnonneg hwidth.le
  let k : ℕ := ⌊δ / width⌋₊
  have hratioUpper : δ / width < 160 := by
    dsimp only [width]
    norm_num at hδupper ⊢
    linarith
  have hk : k < 160 := by
    exact (Nat.floor_lt hratioNonneg).mpr hratioUpper
  let index : Fin 160 := ⟨k, hk⟩
  refine ⟨index, ?_⟩
  have hlowerRaw : (k : ℝ) ≤ δ / width := Nat.floor_le hratioNonneg
  have hupperRaw : δ / width < (k : ℝ) + 1 := Nat.lt_floor_add_one _
  have hlower : (k : ℝ) * width ≤ δ := by
    rw [le_div_iff₀ hwidth] at hlowerRaw
    simpa [mul_comm] using hlowerRaw
  have hupper : δ ≤ ((k : ℝ) + 1) * width := by
    have := (div_lt_iff₀ hwidth).mp hupperRaw
    linarith
  unfold ChapterVISignedDyadicInterval.Contains ChapterVIRealInterval.Contains
  change (((Int.ofNat index * 1671 : ℤ) : ℝ) / (2 : ℝ) ^ 20 ≤ δ ∧
    δ ≤ ((Int.ofNat (index + 1) * 1671 : ℤ) : ℝ) / (2 : ℝ) ^ 20)
  dsimp only [index]
  constructor
  · convert hlower using 1 <;> simp [width] <;> ring
  · apply hupper.trans_eq
    push_cast
    simp [width]
    ring

theorem homogeneousCoefficientCertificate_of_runs
    {massProduct : ℂ} {b d : ℤ}
    (admissibility : ReferenceAdmissibility)
    (verdict : ReferenceRunVerdict admissibility)
    (model : ChapterVIDAnchoredConnectorModel massProduct b d)
    (hL : model.rootModel.L ≤ 1 / (2 : ℝ) ^ 20)
    (hDirection : ∀ side : ChapterVIDOuterArcSide,
      ‖chapterVIDNormalizedLocalEndpointDelta side model.κ model.rootModel.L -
        deriv chapterVIDGlobalContourFromMorse 0‖ < 1 / (2 : ℝ) ^ 10)
    (side : ChapterVIDOuterArcSide) :
    model.HomogeneousCoefficientCertificate side := by
  have hfixed := fixedTrace.contains_of_allSound
    (fixed_allSound admissibility verdict)
  have hLBox := length_contains model.rootModel.L_pos.le hL
  have hqBox := normalizedEndpoint_contains_of_direction_close (hDirection side)
  have hrBox : unitSquare.Contains (model.normalizedOuterEndpointDelta side) := by
    simpa [unitSquare,
      ChapterVIDMorseSlopeCompiled.normalizedParameterDeltaRectangle,
      ChapterVIDAnchoredConnectorModel.normalizedOuterEndpointDelta] using
      ChapterVIDMorseSlopeCompiled.normalizedParameterDeltaRectangle_contains_outerEndpointDelta
        model side
  have hpBox : unitSquare.Contains model.normalizedParameterDelta := by
    simpa [unitSquare,
      ChapterVIDMorseSlopeCompiled.normalizedParameterDeltaRectangle,
      ChapterVIDAnchoredConnectorModel.normalizedParameterDelta] using
      ChapterVIDMorseSlopeCompiled.normalizedParameterDeltaRectangle_contains model
  have coefficientPos (t : Set.Icc (0 : ℝ) 1)
      (ht : (t : ℝ) ∈ ChapterVIDConnectorFactorMonotonicity.collarInterval side) :
      0 < (model.homogeneousEndpointCoefficient side (t : ℝ)).re ∧
      0 < (model.homogeneousDistanceCoefficient side (t : ℝ)).re := by
    let δ := ChapterVIDConnectorFactorCrossing.localEndpointDistance side (t : ℝ)
    have hδnonneg : 0 ≤ δ := by
      cases side with
      | initial =>
          dsimp [δ, ChapterVIDConnectorFactorCrossing.localEndpointDistance]
          linarith [t.property.2]
      | final =>
          dsimp [δ, ChapterVIDConnectorFactorCrossing.localEndpointDistance]
          exact t.property.1
    have hδupper : δ ≤ 261 / 1024 := by
      cases side with
      | initial =>
          change (t : ℝ) ∈ Set.Icc (763 / 1024 : ℝ) 1 at ht
          dsimp [δ, ChapterVIDConnectorFactorCrossing.localEndpointDistance]
          linarith [ht.1]
      | final =>
          change (t : ℝ) ∈ Set.Icc 0 (261 / 1024 : ℝ) at ht
          exact ht.2
    obtain ⟨index, hδBox⟩ := exists_distanceCell_contains hδnonneg hδupper
    let trace := referenceCellTrace side index
    have hall := referenceCell_allSound admissibility verdict side index
    have hcoordinate : model.homogeneousConnectorCoordinate side (t : ℝ) =
        chapterVIDCollisionLift +
          (chapterVIDMorseSideSign side * model.rootModel.L : ℝ) *
              chapterVIDNormalizedLocalEndpointDelta side model.κ model.rootModel.L +
            δ * chapterVIDHomogeneousConnectorDirection side model.rootModel.L
              (chapterVIDNormalizedLocalEndpointDelta side model.κ model.rootModel.L)
              (model.normalizedOuterEndpointDelta side) := by
      have hdelta := model.homogeneousConnectorCoordinate_sub_collision side (t : ℝ)
      dsimp only [δ]
      push_cast at hdelta ⊢
      linear_combination hdelta
    have hu0 : chapterVIDCollisionLift +
        (chapterVIDMorseSideSign side * model.rootModel.L : ℝ) *
            chapterVIDNormalizedLocalEndpointDelta side model.κ model.rootModel.L +
          δ * chapterVIDHomogeneousConnectorDirection side model.rootModel.L
            (chapterVIDNormalizedLocalEndpointDelta side model.κ model.rootModel.L)
            (model.normalizedOuterEndpointDelta side) ≠ 0 := by
      intro heq
      apply model.homogeneousConnectorCoordinate_ne_zero side t.property
      rw [hcoordinate]
      exact heq
    have hpos := trace.coefficients_pos_of_allSound hall hLBox hδBox hqBox hrBox hpBox
      hfixed hu0
    rw [← hcoordinate] at hpos
    simpa [trace, referenceCellTrace,
      ChapterVIDAnchoredConnectorModel.homogeneousEndpointCoefficient,
      ChapterVIDAnchoredConnectorModel.homogeneousDistanceCoefficient, δ] using hpos
  refine ⟨?_, ?_⟩
  · intro t ht
    exact (coefficientPos t ht).1.le
  · intro t ht
    exact (coefficientPos t ht).2.le

/-- The table plus the exact homogeneous identity closes the analytic derivative sign on both
endpoint collars. -/
theorem orientedRealDerivativeCertificates_of_runs
    {massProduct : ℂ} {b d : ℤ}
    (admissibility : ReferenceAdmissibility)
    (verdict : ReferenceRunVerdict admissibility)
    (model : ChapterVIDAnchoredConnectorModel massProduct b d)
    (hL : model.rootModel.L ≤ 1 / (2 : ℝ) ^ 20)
    (hDirection : ∀ side : ChapterVIDOuterArcSide,
      ‖chapterVIDNormalizedLocalEndpointDelta side model.κ model.rootModel.L -
        deriv chapterVIDGlobalContourFromMorse 0‖ < 1 / (2 : ℝ) ^ 10) :
    ChapterVIDConnectorFactorCrossing.OrientedRealDerivativeCertificate
        model.toChapterVIDPrincipalConnectorModel .initial ∧
      ChapterVIDConnectorFactorCrossing.OrientedRealDerivativeCertificate
        model.toChapterVIDPrincipalConnectorModel .final := by
  constructor
  · exact (homogeneousCoefficientCertificate_of_runs admissibility verdict model hL
      hDirection .initial).toOrientedRealDerivativeCertificate model .initial
  · exact (homogeneousCoefficientCertificate_of_runs admissibility verdict model hL
      hDirection .final).toOrientedRealDerivativeCertificate model .final

/-- End-to-end analytic seam assembly using the homogeneous collar table in place of the older
conditional derivative campaigns.  The other compiled runs certify the outer arcs, companion
factor, and regularity facts already consumed by the five-piece contour theorem. -/
theorem exists_seamCompatibleContribution_tendsto_of_runs
    (admissibility : ReferenceAdmissibility)
    (verdict : ReferenceRunVerdict admissibility)
    (outerRun : ChapterVIDOuterArcPolarCompiledGrid.CompiledRunVerdict)
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDAnchoredConnectorModel massProduct b d)
    (hL : model.rootModel.L ≤ 1 / (2 : ℝ) ^ 20)
    (hDirection : ∀ side : ChapterVIDOuterArcSide,
      ‖chapterVIDNormalizedLocalEndpointDelta side model.κ model.rootModel.L -
        deriv chapterVIDGlobalContourFromMorse 0‖ < 1 / (2 : ℝ) ^ 10)
    (bulkRun : ChapterVIDConnectorFactorBulkReference.ReferenceCompiledRunVerdict)
    (derivativeRun :
      ChapterVIDConnectorFactorDerivativeReference.ReferenceCompiledRunVerdict)
    (curvatureRun :
      ChapterVIDConnectorFactorSecondDerivativeReference.ReferenceCompiledRunVerdict)
    (initialCertificate : ChapterVIDConnectorCompiledCertificate
      model.toChapterVIDPrincipalConnectorModel .initial)
    (finalCertificate : ChapterVIDConnectorCompiledCertificate
      model.toChapterVIDPrincipalConnectorModel .final) :
    ∃ compatible : ChapterVIDPrincipalConnectorModel.SeamCompatibleCertifiedConnectorPair
        outerRun model.toChapterVIDPrincipalConnectorModel,
      Filter.Tendsto
        (fun k : ℝ ↦ (-Real.log k)⁻¹ • compatible.fivePieceContribution k)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds ((2 * Real.pi * Complex.I : ℂ)⁻¹ *
          chapterVIDPrincipalMorseAmplitude massProduct b d (0, 0))) := by
  obtain ⟨initialDerivative, finalDerivative⟩ :=
    orientedRealDerivativeCertificates_of_runs admissibility verdict model hL hDirection
  exact ChapterVIDConnectorFactorCrossing.exists_seamCompatibleContribution_tendsto
    outerRun model bulkRun derivativeRun curvatureRun
    (initialDerivative.toPositiveCrossingCertificate model derivativeRun curvatureRun .initial)
    (finalDerivative.toPositiveCrossingCertificate model derivativeRun curvatureRun .final)
    initialCertificate finalCertificate

theorem exists_anchoredModel_with_orientedRealDerivativeCertificates
    (admissibility : ReferenceAdmissibility)
    (verdict : ReferenceRunVerdict admissibility)
    (massProduct : ℂ) (b d : ℤ) :
    ∃ model : ChapterVIDAnchoredConnectorModel massProduct b d,
      ChapterVIDConnectorFactorCrossing.OrientedRealDerivativeCertificate
          model.toChapterVIDPrincipalConnectorModel .initial ∧
        ChapterVIDConnectorFactorCrossing.OrientedRealDerivativeCertificate
          model.toChapterVIDPrincipalConnectorModel .final := by
  obtain ⟨model, hL, _, hDirection⟩ :=
    exists_chapterVIDAnchoredConnectorModel_bounded_direction massProduct b d
      (1 / (2 : ℝ) ^ 20) 1 (1 / (2 : ℝ) ^ 10)
      (by positivity) (by positivity) (by positivity)
  exact ⟨model, orientedRealDerivativeCertificates_of_runs admissibility verdict model hL
    hDirection⟩

end ChapterVIDHomogeneousCompiledTable
end PoincareChapterVI
