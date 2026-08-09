/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.ChapterVIDEndpointAnchor
import PoincareChapterVI.ChapterVIDConnectorFactorSecondDerivativeReference

/-!
# Compiled enclosure of the inverse-Morse slope at D

The endpoint cone used by the homogeneous connector certificate is centered at the derivative of
the inverse Morse coordinate.  Its square is `2 / R″(D)`, where `R` is the literal root-coordinate
radicand.  This file evaluates `R″(D)` by one dependency-preserving LeanCompCert batch and turns
the result into a rational enclosure for the scale-free endpoint displacement.
-/

namespace PoincareChapterVI
namespace ChapterVIDMorseSlopeCompiled

open scoped unitInterval
open ChapterVILeanCompCertBatch
open ChapterVILeanCompCertIntervalBridge
open ChapterVILeanCompCertProposals
open ChapterVILeanCompCertCartesianRadicandTrace
open ChapterVILeanCompCertCartesianFactorSecondDerivativeTrace
open ChapterVIDConnectorFactorSecondDerivativeReference
open LeanCompCert.Ports.SignedProductClaims

abbrev Interval := ChapterVISignedDyadicInterval 20
abbrev Rectangle := ChapterVISignedDyadicComplexRectangle 20

def baseTrace := cartesianRadicandTrace
  ChapterVIDConnectorInputBounds.terminalZetaRectangle
  ChapterVIDConnectorInputBounds.localEndpointRectangle
  ChapterVIDOuterArcPolarCompiledGrid.exponentialCoefficient
  ChapterVIDOuterArcPolarCompiledGrid.inverse10001

def unitDirection : Rectangle :=
  ChapterVISignedDyadicComplexRectangle.pointInt 20 1

def plusSecondTrace := secondDerivativeTrace baseTrace logCoefficient secondCoefficient
  unitDirection

def curvatureTrace := mulTrace plusSecondTrace.output baseTrace.factorMinus

def lowerBoundClaim : Claim :=
  productClaim (-120 * (2 ^ 20)) 1 curvatureTrace.output.real.lower 1

def upperBoundClaim : Claim :=
  productClaim curvatureTrace.output.real.upper 1 (-95 * (2 ^ 20)) 1

/-- The complete 168-operation reference batch, including explicit claims for
`-120 ≤ Re R″(D) ≤ -95`. -/
def operations : List (DyadicOperation 20) :=
  baseTrace.operations ++ plusSecondTrace.operations ++ curvatureTrace.operations ++
    [.rawClaim lowerBoundClaim, .rawClaim upperBoundClaim]

def artifactName : String := "chapter_vi_morse_inverse_slope"

theorem terminalZetaRectangle_contains_base :
    ChapterVIDConnectorInputBounds.terminalZetaRectangle.Contains chapterVIDZRootBase := by
  obtain ⟨model⟩ := exists_chapterVIDAnchoredConnectorModel (0 : ℂ) 0 0
  have h := ChapterVIDConnectorInputBounds.terminalZetaRectangle_contains
    model.toChapterVIDPrincipalConnectorModel (1 : I)
  rw [ChapterVIDPrincipalConnectorModel.criticalValue_one] at h
  simpa using h

theorem curvatureTrace_output_contains_of_allSound
    (hall : ∀ operation ∈ operations, operation.Sound) :
    curvatureTrace.output.Contains
      (deriv (deriv (chapterVIDRootCoordinateRadicand chapterVIDZRootBase))
        chapterVIDCollisionLift) := by
  have hbase : ∀ operation ∈ baseTrace.operations, operation.Sound := by
    intro operation hoperation
    exact hall operation (by simp [operations, hoperation])
  have hsecond : ∀ operation ∈ plusSecondTrace.operations, operation.Sound := by
    intro operation hoperation
    exact hall operation (by simp [operations, hoperation])
  have hcurvature : ∀ operation ∈ curvatureTrace.operations, operation.Sound := by
    intro operation hoperation
    exact hall operation (by simp [operations, hoperation])
  have hζ := terminalZetaRectangle_contains_base
  have hu := ChapterVIDConnectorInputBounds.localEndpointRectangle_contains_collisionLift
  have hanomalies := baseTrace.anomalies_contain_of_allSound hbase hζ hu
    ChapterVIDOuterArcPolarCompiledGrid.exponentialCoefficient_contains
    chapterVIDZRootBase_ne_zero chapterVIDCollisionLift_ne_zero
  have hplusSecond := plusSecondTrace.output_contains_of_allSound hsecond hu hanomalies.1
    ChapterVIDOuterArcPolarCompiledGrid.inverse10001_contains logCoefficient_contains
    secondCoefficient_contains
    (ChapterVISignedDyadicComplexRectangle.pointInt_contains 20 1)
  have hfactors := baseTrace.factors_contain_sparse_of_allSound hbase hu
    ChapterVIDOuterArcPolarCompiledGrid.inverse10001_contains hanomalies.1 hanomalies.2
  have hminus : baseTrace.factorMinus.Contains
      (chapterVIDRootCoordinateCollisionFactorMinus chapterVIDZRootBase
        chapterVIDCollisionLift) := by
    rw [chapterVIDRootCoordinateCollisionFactorMinus_eq_polarCertificateFormula
      chapterVIDZRootBase_ne_zero chapterVIDCollisionLift_ne_zero]
    exact hfactors.2
  have hproduct := curvatureTrace.output_contains_mul_of_allSound hcurvature
    hplusSecond hminus
  rw [chapterVIDRootCoordinateRadicandSecondDerivative_base]
  convert hproduct using 1 <;> norm_num [unitDirection]

theorem curvature_re_mem_of_allSound
    (hall : ∀ operation ∈ operations, operation.Sound) :
    (deriv (deriv (chapterVIDRootCoordinateRadicand chapterVIDZRootBase))
        chapterVIDCollisionLift).re ∈ Set.Icc (-120 : ℝ) (-95 : ℝ) := by
  have hcontains := curvatureTrace_output_contains_of_allSound hall
  have hlowerSound := hall (.rawClaim lowerBoundClaim) (by simp [operations])
  have hupperSound := hall (.rawClaim upperBoundClaim) (by simp [operations])
  have hlowerRaw : (-120 : ℤ) * (2 ^ 20) ≤ curvatureTrace.output.real.lower := by
    simpa [DyadicOperation.Sound, lowerBoundClaim, productClaim_holds_iff] using hlowerSound
  have hupperRaw : curvatureTrace.output.real.upper ≤ (-95 : ℤ) * (2 ^ 20) := by
    simpa [DyadicOperation.Sound, upperBoundClaim, productClaim_holds_iff] using hupperSound
  constructor
  · calc
      (-120 : ℝ) = (((-120 : ℤ) * (2 ^ 20) : ℤ) : ℝ) / (2 : ℝ) ^ 20 := by
        norm_num
      _ ≤ (curvatureTrace.output.real.lower : ℝ) / (2 : ℝ) ^ 20 := by
        gcongr
      _ ≤ _ := hcontains.1.1
  · exact hcontains.1.2.trans (by
      change (curvatureTrace.output.real.upper : ℝ) / (2 : ℝ) ^ 20 ≤ -95
      rw [div_le_iff₀ (by positivity)]
      exact_mod_cast hupperRaw)

set_option maxRecDepth 1000000 in
theorem operations_admissible : Admissible (batchClaims operations) := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 1000000 in
/-- Kernel evaluation of the same verified computation used by the emitted LeanCompCert
artifact.  The batch is intentionally small (168 operations), so the slope input does not need an
external run admission. -/
theorem reference_returnsZero :
    (batchComputation artifactName operations).Returns ((0 : Nat) : Int) := by
  decide +kernel

theorem reference_allSound : ∀ operation ∈ operations, operation.Sound :=
  allSound_of_returns_zero artifactName operations operations_admissible reference_returnsZero

theorem curvature_re_mem_reference :
    (deriv (deriv (chapterVIDRootCoordinateRadicand chapterVIDZRootBase))
        chapterVIDCollisionLift).re ∈ Set.Icc (-120 : ℝ) (-95 : ℝ) :=
  curvature_re_mem_of_allSound reference_allSound

/-- Rational interval for the downward inverse-Morse slope. -/
theorem deriv_chapterVIDGlobalContourFromMorse_im_mem :
    (deriv chapterVIDGlobalContourFromMorse 0).im ∈
      Set.Ioo (-3 / 20 : ℝ) (-1 / 8 : ℝ) := by
  let y := (deriv chapterVIDGlobalContourFromMorse 0).im
  let c := -(deriv (deriv
    (chapterVIDRootCoordinateRadicand chapterVIDZRootBase)) chapterVIDCollisionLift).re
  have hyneg : y < 0 := deriv_chapterVIDGlobalContourFromMorse_im_neg
  have hcLower : 95 ≤ c := by
    dsimp only [c]
    linarith [curvature_re_mem_reference.2]
  have hcUpper : c ≤ 120 := by
    dsimp only [c]
    linarith [curvature_re_mem_reference.1]
  have hcNonneg : 0 ≤ c := by linarith
  have hproduct : y ^ 2 * c = 2 := by
    exact deriv_chapterVIDGlobalContourFromMorse_im_sq_mul_neg_curvature_re
  constructor
  · by_contra hnot
    have hy : y ≤ -3 / 20 := le_of_not_gt hnot
    have hsq : (9 / 400 : ℝ) ≤ y ^ 2 := by nlinarith
    have hmul : (9 / 400 : ℝ) * 95 ≤ y ^ 2 * c :=
      mul_le_mul hsq hcLower (by norm_num) (sq_nonneg y)
    nlinarith
  · by_contra hnot
    have hy : -1 / 8 ≤ y := le_of_not_gt hnot
    have hsq : y ^ 2 ≤ (1 / 64 : ℝ) := by nlinarith
    have hmul : y ^ 2 * c ≤ (1 / 64 : ℝ) * 120 :=
      mul_le_mul hsq hcUpper hcNonneg (by norm_num)
    nlinarith

/-- Dyadic enclosure of the scale-free displacement `(local-D)/v`.  Unlike an absolute endpoint
box, this remains nondegenerate when the selected Morse length shrinks. -/
def normalizedEndpointDeltaRectangle : Rectangle :=
  ⟨⟨-83887, 83887⟩, ⟨-262144, -65536⟩⟩

theorem normalizedEndpointDeltaRectangle_contains
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDAnchoredConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) :
    normalizedEndpointDeltaRectangle.Contains
      (chapterVIDNormalizedLocalEndpointDelta side model.κ model.rootModel.L) := by
  let q := chapterVIDNormalizedLocalEndpointDelta side model.κ model.rootModel.L
  let slope := deriv chapterVIDGlobalContourFromMorse 0
  have hcone : ‖q - slope‖ < -slope.im / 2 := by
    cases side with
    | initial => exact model.initialNormalizedLocalDelta_mem_directionCone
    | final => exact model.finalNormalizedLocalDelta_mem_directionCone
  have hslope := deriv_chapterVIDGlobalContourFromMorse_im_mem
  change slope.im ∈ Set.Ioo (-3 / 20 : ℝ) (-1 / 8 : ℝ) at hslope
  rcases hslope with ⟨hslopeLower, hslopeUpper⟩
  have hslopeRe := deriv_chapterVIDGlobalContourFromMorse_re_zero
  have hreNorm := (Complex.abs_re_le_norm (q - slope)).trans_lt hcone
  have himNorm := (Complex.abs_im_le_norm (q - slope)).trans_lt hcone
  have hre := abs_lt.mp hreNorm
  have him := abs_lt.mp himNorm
  rw [Complex.sub_re, hslopeRe, sub_zero] at hre
  rw [Complex.sub_im] at him
  change
    (((-83887 : ℤ) : ℝ) / (2 : ℝ) ^ 20 ≤ q.re ∧
      q.re ≤ ((83887 : ℤ) : ℝ) / (2 : ℝ) ^ 20) ∧
      (((-262144 : ℤ) : ℝ) / (2 : ℝ) ^ 20 ≤ q.im ∧
      q.im ≤ ((-65536 : ℤ) : ℝ) / (2 : ℝ) ^ 20)
  norm_num only [Int.cast_negSucc, Int.cast_ofNat, Nat.cast_ofNat, pow_succ,
    pow_zero, mul_one]
  constructor
  · constructor <;> linarith
  · constructor <;> linarith

end ChapterVIDMorseSlopeCompiled
end PoincareChapterVI
