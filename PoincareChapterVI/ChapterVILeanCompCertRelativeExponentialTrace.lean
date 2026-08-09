/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.ChapterVILeanCompCertDependencyPreservingFactorDerivativeTrace

/-!
# A compiled relative exponential enclosure at Poincare's collision

The terminal derivative uses `exp (A(u) - A(D)) - 1`.  Evaluating two absolute exponentials would
destroy the common endpoint zero.  Here the exact difference is first evaluated in its factored
`(u-D)` form.  LeanCompCert checks that rational trace, and mathlib's complex exponential
remainder theorem widens it by the checked square of its norm.
-/

namespace PoincareChapterVI
namespace ChapterVILeanCompCertRelativeExponentialTrace

open ChapterVILeanCompCertBatch
open ChapterVILeanCompCertIntervalBridge

abbrev Interval (precision : ℕ) := ChapterVISignedDyadicInterval precision
abbrev Rectangle (precision : ℕ) := ChapterVISignedDyadicComplexRectangle precision

/-- Rounded rational evaluation of `A(u)-A(D)` in its dependency-preserving form. -/
structure ArgumentTrace {precision : ℕ}
    (coordinate coordinateDelta collision collisionInvCube : Rectangle precision)
    (coefficient100 : Interval precision) where
  coordinateSquare : ChapterVISignedDyadicComplexRectangle.MulTrace coordinate coordinate
  coordinateInv : ChapterVISignedDyadicComplexRectangle.InvTrace coordinate
  coordinateInvCube : ChapterVISignedDyadicComplexRectangle.CubeTrace coordinateInv.output
  coordinateTimesCollision : ChapterVISignedDyadicComplexRectangle.MulTrace coordinate collision
  collisionSquare : ChapterVISignedDyadicComplexRectangle.MulTrace collision collision
  deltaTimesQuadratic : ChapterVISignedDyadicComplexRectangle.MulTrace coordinateDelta
    ((coordinateSquare.output.add coordinateTimesCollision.output).add
      collisionSquare.output)
  inverseCubeProduct : ChapterVISignedDyadicComplexRectangle.MulTrace
    coordinateInvCube.output collisionInvCube
  argumentCore : ChapterVISignedDyadicComplexRectangle.MulTrace deltaTimesQuadratic.output
    ((ChapterVISignedDyadicComplexRectangle.pointInt precision 1).add
      inverseCubeProduct.output)
  scaled : ChapterVISignedDyadicComplexRectangle.RealMulTrace coefficient100 argumentCore.output

/- The order of `collisionSquare` has to be available in the dependent type of
`deltaTimesQuadratic`; a compact constructor-facing version is clearer than exposing that
implementation dependency to callers. -/

def ArgumentTrace.output {precision : ℕ}
    {coordinate coordinateDelta collision collisionInvCube : Rectangle precision}
    {coefficient100 : Interval precision}
    (trace : ArgumentTrace coordinate coordinateDelta collision collisionInvCube coefficient100) :
    Rectangle precision :=
  trace.scaled.output.neg

def ArgumentTrace.parts {precision : ℕ}
    {coordinate coordinateDelta collision collisionInvCube : Rectangle precision}
    {coefficient100 : Interval precision}
    (trace : ArgumentTrace coordinate coordinateDelta collision collisionInvCube coefficient100) :
    List (List (DyadicOperation precision)) :=
  [ trace.coordinateSquare.operations
  , trace.coordinateInv.operations
  , trace.coordinateInvCube.operations
  , trace.coordinateTimesCollision.operations
  , trace.collisionSquare.operations
  , trace.deltaTimesQuadratic.operations
  , trace.inverseCubeProduct.operations
  , trace.argumentCore.operations
  , trace.scaled.operations ]

def ArgumentTrace.operations {precision : ℕ}
    {coordinate coordinateDelta collision collisionInvCube : Rectangle precision}
    {coefficient100 : Interval precision}
    (trace : ArgumentTrace coordinate coordinateDelta collision collisionInvCube coefficient100) :
    List (DyadicOperation precision) :=
  trace.parts.flatten

/-- Executable, untrusted proposal for the relative argument trace. -/
def argumentTrace {precision : ℕ}
    (coordinate coordinateDelta collision collisionInvCube : Rectangle precision)
    (coefficient100 : Interval precision) :
    ArgumentTrace coordinate coordinateDelta collision collisionInvCube coefficient100 :=
  let coordinateSquare := ChapterVILeanCompCertProposals.mulTrace coordinate coordinate
  let coordinateInv := ChapterVILeanCompCertProposals.invTrace coordinate
  let coordinateInvCube := ChapterVILeanCompCertProposals.cubeTrace coordinateInv.output
  let coordinateTimesCollision := ChapterVILeanCompCertProposals.mulTrace coordinate collision
  let collisionSquare := ChapterVILeanCompCertProposals.mulTrace collision collision
  let deltaTimesQuadratic := ChapterVILeanCompCertProposals.mulTrace coordinateDelta
    ((coordinateSquare.output.add coordinateTimesCollision.output).add collisionSquare.output)
  let inverseCubeProduct := ChapterVILeanCompCertProposals.mulTrace
    coordinateInvCube.output collisionInvCube
  let argumentCore := ChapterVILeanCompCertProposals.mulTrace deltaTimesQuadratic.output
    ((ChapterVISignedDyadicComplexRectangle.pointInt precision 1).add
      inverseCubeProduct.output)
  let scaled := ChapterVILeanCompCertProposals.realMulTrace coefficient100 argumentCore.output
  { coordinateSquare := coordinateSquare
    coordinateInv := coordinateInv
    coordinateInvCube := coordinateInvCube
    coordinateTimesCollision := coordinateTimesCollision
    deltaTimesQuadratic := deltaTimesQuadratic
    collisionSquare := collisionSquare
    inverseCubeProduct := inverseCubeProduct
    argumentCore := argumentCore
    scaled := scaled }

theorem ArgumentTrace.output_contains_of_allSound
    {precision : ℕ}
    {coordinate coordinateDelta collision collisionInvCube : Rectangle precision}
    {coefficient100 : Interval precision}
    (trace : ArgumentTrace coordinate coordinateDelta collision collisionInvCube coefficient100)
    (hall : ∀ operation ∈ trace.operations, operation.Sound)
    {u : ℂ} (hu : u ≠ 0)
    (huBox : coordinate.Contains u)
    (huDelta : coordinateDelta.Contains (u - chapterVIDCollisionLift))
    (hCollision : collision.Contains chapterVIDCollisionLift)
    (hCollisionInvCube : collisionInvCube.Contains (chapterVIDCollisionLift⁻¹ ^ 3))
    (hCoefficient100 : coefficient100.Contains (100 / 30003 : ℝ)) :
    trace.output.Contains
      (chapterVIDRootExponentialArgument u -
        chapterVIDRootExponentialArgument chapterVIDCollisionLift) := by
  have soundPart (operations : List (DyadicOperation precision))
      (hpart : operations ∈ trace.parts) :
      ∀ operation ∈ operations, operation.Sound := by
    intro operation hoperation
    apply hall operation
    rw [ArgumentTrace.operations, List.mem_flatten]
    exact ⟨operations, hpart, hoperation⟩
  have hUSquare := trace.coordinateSquare.output_contains_mul_of_allSound
    (soundPart trace.coordinateSquare.operations (by simp [ArgumentTrace.parts])) huBox huBox
  have hUInv := trace.coordinateInv.output_contains_inv_of_allSound
    (soundPart trace.coordinateInv.operations (by simp [ArgumentTrace.parts])) huBox
  have hUInvCube := trace.coordinateInvCube.output_contains_cube_of_allSound
    (soundPart trace.coordinateInvCube.operations (by simp [ArgumentTrace.parts])) hUInv
  have hUTimesD := trace.coordinateTimesCollision.output_contains_mul_of_allSound
    (soundPart trace.coordinateTimesCollision.operations (by simp [ArgumentTrace.parts]))
    huBox hCollision
  have hDSquare := trace.collisionSquare.output_contains_mul_of_allSound
    (soundPart trace.collisionSquare.operations (by simp [ArgumentTrace.parts]))
    hCollision hCollision
  have hQuadratic := ChapterVISignedDyadicComplexRectangle.add_contains
    (ChapterVISignedDyadicComplexRectangle.add_contains hUSquare hUTimesD) hDSquare
  have hDeltaQuadratic := trace.deltaTimesQuadratic.output_contains_mul_of_allSound
    (soundPart trace.deltaTimesQuadratic.operations (by simp [ArgumentTrace.parts]))
    huDelta hQuadratic
  have hInverseCubeProduct := trace.inverseCubeProduct.output_contains_mul_of_allSound
    (soundPart trace.inverseCubeProduct.operations (by simp [ArgumentTrace.parts]))
    hUInvCube hCollisionInvCube
  have hOne := ChapterVISignedDyadicComplexRectangle.pointInt_contains precision 1
  have hCore := trace.argumentCore.output_contains_mul_of_allSound
    (soundPart trace.argumentCore.operations (by simp [ArgumentTrace.parts]))
    hDeltaQuadratic
    (ChapterVISignedDyadicComplexRectangle.add_contains hOne hInverseCubeProduct)
  have hScaled := trace.scaled.output_contains_of_allSound
    (soundPart trace.scaled.operations (by simp [ArgumentTrace.parts])) hCoefficient100 hCore
  have hCoefficientCast : ((100 / 30003 : ℝ) : ℂ) = (100 / 30003 : ℂ) := by
    rw [Complex.ofReal_div]
    norm_num
  rw [hCoefficientCast] at hScaled
  have hNeg := ChapterVISignedDyadicComplexRectangle.neg_contains hScaled
  change trace.scaled.output.neg.Contains _
  rw [chapterVIDRootExponentialArgument_sub_base hu]
  convert hNeg using 1
  unfold chapterVIDRootExponentialArgumentDifference
  ring

/-- Checked first-order Taylor enclosure for `exp argument - 1`. -/
structure ExpDeltaTrace {precision : ℕ} (argument : Rectangle precision) where
  argumentNorm : Interval precision
  argumentNormBound : argument.L1NormBound argumentNorm
  argumentNormSquare : Interval precision

def ExpDeltaTrace.normLeOneClaim {precision : ℕ} {argument : Rectangle precision}
    (trace : ExpDeltaTrace argument) : LeanCompCert.Ports.SignedProductClaims.Claim :=
  productClaim trace.argumentNorm.upper 1
    (ChapterVILeanCompCertProposals.scaleInt precision) 1

def ExpDeltaTrace.operations {precision : ℕ} {argument : Rectangle precision}
    (trace : ExpDeltaTrace argument) : List (DyadicOperation precision) :=
  [ .mul trace.argumentNorm trace.argumentNorm trace.argumentNormSquare
  , .rawClaim trace.normLeOneClaim ]

def ExpDeltaTrace.output {precision : ℕ} {argument : Rectangle precision}
    (trace : ExpDeltaTrace argument) : Rectangle precision :=
  argument.widenUpper trace.argumentNormSquare

/-- Executable proposal for the norm and Taylor-remainder bounds. -/
def expDeltaTrace {precision : ℕ} (argument : Rectangle precision) :
    ExpDeltaTrace argument :=
  let argumentNorm := ChapterVILeanCompCertProposals.l1NormInterval argument
  { argumentNorm := argumentNorm
    argumentNormBound := ChapterVILeanCompCertProposals.l1NormBound argument
    argumentNormSquare := ChapterVILeanCompCertProposals.mul precision argumentNorm argumentNorm }

theorem ExpDeltaTrace.output_contains_of_allSound
    {precision : ℕ} {argument : Rectangle precision}
    (trace : ExpDeltaTrace argument)
    (hall : ∀ operation ∈ trace.operations, operation.Sound)
    {a : ℂ} (ha : argument.Contains a) :
    trace.output.Contains (Complex.exp a - 1) := by
  have hnorm := trace.argumentNormBound.contains_norm ha
  have hmul : ChapterVISignedDyadicInterval.MulCertificate
      trace.argumentNorm trace.argumentNorm trace.argumentNormSquare := by
    exact hall (.mul trace.argumentNorm trace.argumentNorm trace.argumentNormSquare)
      (by simp [ExpDeltaTrace.operations])
  have hclaim : trace.normLeOneClaim.Holds := by
    exact hall (.rawClaim trace.normLeOneClaim) (by simp [ExpDeltaTrace.operations])
  have hupperInt : trace.argumentNorm.upper ≤
      ChapterVILeanCompCertProposals.scaleInt precision := by
    simpa [ExpDeltaTrace.normLeOneClaim, productClaim_holds_iff] using hclaim
  have hnormLeOne : ‖a‖ ≤ 1 := by
    apply hnorm.2.trans
    change (trace.argumentNorm.upper : ℝ) /
        ChapterVISignedDyadicInterval.scale precision ≤ 1
    rw [div_le_one (ChapterVISignedDyadicInterval.scale_pos precision)]
    change (trace.argumentNorm.upper : ℝ) ≤ (2 : ℝ) ^ precision
    unfold ChapterVILeanCompCertProposals.scaleInt at hupperInt
    exact_mod_cast hupperInt
  have hnormSquare := hmul.contains_mul hnorm hnorm
  apply ChapterVISignedDyadicComplexRectangle.widenUpper_contains_of_norm_sub_le ha
  have hremainder := Complex.norm_exp_sub_one_sub_id_le hnormLeOne
  have hremainder' : ‖(Complex.exp a - 1) - a‖ ≤ ‖a‖ ^ 2 := by
    simpa [sub_eq_add_neg, add_assoc] using hremainder
  calc
    ‖(Complex.exp a - 1) - a‖ ≤ ‖a‖ ^ 2 := hremainder'
    _ = ‖a‖ * ‖a‖ := by ring
    _ ≤ (trace.argumentNormSquare.upper : ℝ) /
        ChapterVISignedDyadicInterval.scale precision := hnormSquare.2

/-- Complete checked relative-exponential trace. -/
structure Trace {precision : ℕ}
    (coordinate coordinateDelta collision collisionInvCube : Rectangle precision)
    (coefficient100 : Interval precision) where
  argument : ArgumentTrace coordinate coordinateDelta collision collisionInvCube coefficient100
  exponential : ExpDeltaTrace argument.output

def Trace.operations {precision : ℕ}
    {coordinate coordinateDelta collision collisionInvCube : Rectangle precision}
    {coefficient100 : Interval precision}
    (trace : Trace coordinate coordinateDelta collision collisionInvCube coefficient100) :
    List (DyadicOperation precision) :=
  trace.argument.operations ++ trace.exponential.operations

def Trace.output {precision : ℕ}
    {coordinate coordinateDelta collision collisionInvCube : Rectangle precision}
    {coefficient100 : Interval precision}
    (trace : Trace coordinate coordinateDelta collision collisionInvCube coefficient100) :
    Rectangle precision :=
  trace.exponential.output

def relativeExpTrace {precision : ℕ}
    (coordinate coordinateDelta collision collisionInvCube : Rectangle precision)
    (coefficient100 : Interval precision) :
    Trace coordinate coordinateDelta collision collisionInvCube coefficient100 :=
  let argument := argumentTrace coordinate coordinateDelta collision collisionInvCube coefficient100
  ⟨argument, expDeltaTrace argument.output⟩

theorem Trace.output_contains_of_allSound
    {precision : ℕ}
    {coordinate coordinateDelta collision collisionInvCube : Rectangle precision}
    {coefficient100 : Interval precision}
    (trace : Trace coordinate coordinateDelta collision collisionInvCube coefficient100)
    (hall : ∀ operation ∈ trace.operations, operation.Sound)
    {u : ℂ} (hu : u ≠ 0)
    (huBox : coordinate.Contains u)
    (huDelta : coordinateDelta.Contains (u - chapterVIDCollisionLift))
    (hCollision : collision.Contains chapterVIDCollisionLift)
    (hCollisionInvCube : collisionInvCube.Contains (chapterVIDCollisionLift⁻¹ ^ 3))
    (hCoefficient100 : coefficient100.Contains (100 / 30003 : ℝ)) :
    trace.output.Contains
      (Complex.exp
        (chapterVIDRootExponentialArgument u -
          chapterVIDRootExponentialArgument chapterVIDCollisionLift) - 1) := by
  have hargumentSound : ∀ operation ∈ trace.argument.operations, operation.Sound := by
    intro operation hoperation
    exact hall operation (by simp [Trace.operations, hoperation])
  have hexponentialSound : ∀ operation ∈ trace.exponential.operations, operation.Sound := by
    intro operation hoperation
    exact hall operation (by simp [Trace.operations, hoperation])
  exact trace.exponential.output_contains_of_allSound hexponentialSound
    (trace.argument.output_contains_of_allSound hargumentSound hu huBox huDelta
      hCollision hCollisionInvCube hCoefficient100)

end ChapterVILeanCompCertRelativeExponentialTrace
end PoincareChapterVI
