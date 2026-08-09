/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.ChapterVILeanCompCertRadialTailDerivativeTrace
import PoincareChapterVI.ChapterVIDPinchingArcPrefixAdmissibility

/-!
# Compiled derivative table on the six final radial rows

Each of the twelve shards contains the 32 angular cells for one side and one radial row.  A
positive-lower check on the negated real output certifies a strictly negative radial derivative.
-/

namespace PoincareChapterVI

open ChapterVILeanCompCertBatch
open LeanCompCert.Ports.SignedProductClaims
open scoped unitInterval

namespace ChapterVIDRadialTailDerivativeCompiledGrid

abbrev Interval := ChapterVISignedDyadicInterval 20

def radialIndex (i : Fin 6) : Fin 28 := ⟨i + 22, by omega⟩

def radial (i : Fin 6) := ChapterVIDRadialClusteredCompiledGrid.trace (radialIndex i)

def velocity (i : Fin 6) :=
  ChapterVILeanCompCertRadialTailDerivativeTrace.velocityTrace
    (radial i).q (radial i).qSixthRoot (radial i).correctionFactor
    (radial i).qDelta (radial i).correctionDelta

def base (side : ChapterVIDPinchingArcSide) (i : Fin 6) (j : Fin 32) :=
  ChapterVILeanCompCertProposals.radicandTrace
    (radial i).qCubeRoot (radial i).radius
    (ChapterVIDPinchingArcPrefixCompiledGrid.unit side j)
    ChapterVIDOuterArcPolarCompiledGrid.exponentialCoefficient
    ChapterVIDOuterArcPolarCompiledGrid.inverse10001

def trace (side : ChapterVIDPinchingArcSide) (i : Fin 6) (j : Fin 32) :=
  ChapterVILeanCompCertRadialTailDerivativeTrace.derivativeTrace
    (base side i j) (velocity i).zetaLogVelocity (velocity i).radiusVelocity

def cellOperations (side : ChapterVIDPinchingArcSide) (i : Fin 6) (j : Fin 32) :
    List (DyadicOperation 20) :=
  (velocity i).operations ++ (trace side i j).operations ++
    [.positiveLower (trace side i j).output.real.neg]

def shardOperations (side : ChapterVIDPinchingArcSide) (i : Fin 6) :
    List (DyadicOperation 20) :=
  (List.finRange 32).flatMap fun j ↦ cellOperations side i j

def sideName : ChapterVIDPinchingArcSide → String
  | .upper => "upper"
  | .lower => "lower"

def shardArtifactName (side : ChapterVIDPinchingArcSide) (i : Fin 6) : String :=
  s!"PoincareChapterVI.radialTailDerivative20.{sideName side}.{i.val}"

theorem velocity_operations_mem (side : ChapterVIDPinchingArcSide) (i : Fin 6) (j : Fin 32)
    (operation : DyadicOperation 20) (hoperation : operation ∈ (velocity i).operations) :
    operation ∈ shardOperations side i := by
  rw [shardOperations, List.mem_flatMap]
  exact ⟨j, by simp, by simp [cellOperations, hoperation]⟩

theorem trace_operations_mem (side : ChapterVIDPinchingArcSide) (i : Fin 6) (j : Fin 32)
    (operation : DyadicOperation 20) (hoperation : operation ∈ (trace side i j).operations) :
    operation ∈ shardOperations side i := by
  rw [shardOperations, List.mem_flatMap]
  exact ⟨j, by simp, by simp [cellOperations, hoperation]⟩

theorem negativeUpper_mem (side : ChapterVIDPinchingArcSide) (i : Fin 6) (j : Fin 32) :
    DyadicOperation.positiveLower (trace side i j).output.real.neg ∈
      shardOperations side i := by
  rw [shardOperations, List.mem_flatMap]
  exact ⟨j, by simp, by simp [cellOperations]⟩

structure ShardVerdict (side : ChapterVIDPinchingArcSide) (i : Fin 6) : Prop where
  admissible : Admissible (batchClaims (shardOperations side i))
  returnsZero :
    (batchComputation (shardArtifactName side i) (shardOperations side i)).Returns
      ((0 : Nat) : Int)

structure CompiledVerdict : Prop where
  shard : ∀ side i, ShardVerdict side i

theorem output_upper_neg (verdict : CompiledVerdict)
    (side : ChapterVIDPinchingArcSide) (i : Fin 6) (j : Fin 32) :
    (trace side i j).output.real.upper < 0 := by
  have h := allSound_of_returns_zero (shardArtifactName side i)
    (shardOperations side i) (verdict.shard side i).admissible
      (verdict.shard side i).returnsZero
    (.positiveLower (trace side i j).output.real.neg) (negativeUpper_mem side i j)
  change 0 < -(trace side i j).output.real.upper at h
  omega

theorem output_contains_cell (verdict : CompiledVerdict)
    (side : ChapterVIDPinchingArcSide) (i : Fin 6) (j : Fin 32) (s t : I)
    (hlower : (chapterVICubicClusterNode 28 (radialIndex i) : ℝ) ≤ s)
    (hupper : (s : ℝ) ≤ chapterVICubicClusterNode 28 (radialIndex i + 1))
    (hunit : (ChapterVIDPinchingArcPrefixCompiledGrid.unit side j).Contains
      (chapterVIDRationalPinchingArcUnit side t)) :
    (trace side i j).output.Contains
      (chapterVIDRadialTailActualDerivative side t s) := by
  have hallVelocity : ∀ operation ∈ (velocity i).operations, operation.Sound := by
    intro operation hoperation
    exact allSound_of_returns_zero (shardArtifactName side i) (shardOperations side i)
      (verdict.shard side i).admissible (verdict.shard side i).returnsZero operation
      (velocity_operations_mem side i j operation hoperation)
  have hallTrace : ∀ operation ∈ (trace side i j).operations, operation.Sound := by
    intro operation hoperation
    exact allSound_of_returns_zero (shardArtifactName side i) (shardOperations side i)
      (verdict.shard side i).admissible (verdict.shard side i).returnsZero operation
      (trace_operations_mem side i j operation hoperation)
  have hroot := ChapterVIDRadialClusteredCompiledGrid.outputs_contain_cell
    (radialIndex i) hlower hupper
  have hinputs := ChapterVIDRadialClusteredCompiledGrid.velocity_inputs_contain_cell
    (radialIndex i) hlower hupper
  have hqDot : (radial i).qDelta.Contains
      (chapterVIDCriticalParameterModulus - 1) := by
    simpa [radial, ChapterVIDRadialTrace.Trace.qDelta,
      ChapterVIDRadialTrace.Trace.one, ChapterVIDRadialClusteredCompiledGrid.trace,
      ChapterVIDRadialClusteredCompiledGrid.endpoint,
      ChapterVILeanCompCertProposals.radialEndpointTrace] using
      ChapterVISignedDyadicInterval.sub_contains
      ChapterVIDRadialClusteredCompiledGrid.qD_contains
      (ChapterVISignedDyadicInterval.pointInt_contains 20 1)
  have hcorrectionDot : (radial i).correctionDelta.Contains
      (chapterVIDCertificateContourCorrection - 1) := by
    simpa [radial, ChapterVIDRadialTrace.Trace.correctionDelta,
      ChapterVIDRadialTrace.Trace.one, ChapterVIDRadialClusteredCompiledGrid.trace,
      ChapterVIDRadialClusteredCompiledGrid.endpoint,
      ChapterVILeanCompCertProposals.radialEndpointTrace] using
      ChapterVISignedDyadicInterval.sub_contains
      ChapterVIDRadialClusteredCompiledGrid.correction_contains
      (ChapterVISignedDyadicInterval.pointInt_contains 20 1)
  have hvel := (velocity i).outputs_contain_of_allSound hallVelocity
    hinputs.1 hinputs.2.1 hinputs.2.2 hqDot hcorrectionDot
  have hζlog : (velocity i).zetaLogVelocity.Contains
      ((chapterVIDCriticalParameterModulus - 1) * (3 : ℝ)⁻¹ *
        (chapterVIDCertificateParameter s)⁻¹) := hvel.1
  have hrdot : (velocity i).radiusVelocity.Contains
      (chapterVIDCertificateContourRadiusVelocityReal s) := by
    rw [chapterVIDCertificateContourRadiusVelocityReal_eq_log]
    exact hvel.2
  have hrLower : (1 / 5 : ℝ) ≤ chapterVIDCertificateContourRadius s :=
    (ChapterVIDOuterArcPolarCompiledGrid.radial_radius_bounds
      ChapterVIDOuterArcPolarCompiledGrid.referenceRunVerdict.toCompiledVerdict
      .initial (radialIndex i) j).1.trans
      hroot.2.1
  have hrUpper : chapterVIDCertificateContourRadius s ≤ 1 :=
    hroot.2.2.trans
      (ChapterVIDOuterArcPolarCompiledGrid.radial_radius_bounds
        ChapterVIDOuterArcPolarCompiledGrid.referenceRunVerdict.toCompiledVerdict
        .initial (radialIndex i) j).2
  have hargument :
      ‖chapterVIDRootExponentialArgument
        ((chapterVIDCertificateContourRadius s : ℂ) *
          chapterVIDRationalPinchingArcUnit side t)‖ ≤ 1 := by
    apply norm_chapterVIDRootExponentialArgument_le_one_of_mem_annulus
    · simpa [norm_mul, chapterVIDRationalPinchingArcUnit_norm,
        abs_of_pos (chapterVIDCertificateContourRadius_pos s)] using hrLower
    · simpa [norm_mul, chapterVIDRationalPinchingArcUnit_norm,
        abs_of_pos (chapterVIDCertificateContourRadius_pos s)] using hrUpper
  have hsemantic := (trace side i j).output_contains_of_allSound hallTrace
    hroot.1 hroot.2 hunit (chapterVIDRationalPinchingArcUnit_norm side t)
    ChapterVIDOuterArcPolarCompiledGrid.exponentialCoefficient_contains
    ChapterVIDOuterArcPolarCompiledGrid.inverse10001_contains
    (Real.rpow_pos_of_pos (chapterVIDCertificateParameter_pos s) _)
    (chapterVIDCertificateContourRadius_pos s) hargument hζlog hrdot
  rw [chapterVIDRadialTailActualDerivative,
    chapterVIDCertificateZetaVelocityReal_eq_log_mul,
    chapterVIDCertificateZetaReal_eq,
    chapterVIDCertificateContourRadiusReal_eq]
  exact hsemantic

theorem exists_radial_cell {s : I}
    (hprefix : (ChapterVIDPinchingArcPrefixCompiledGrid.prefixEnd : ℝ) ≤ (s : ℝ)) :
    ∃ i : Fin 6,
      (chapterVICubicClusterNode 28 (radialIndex i) : ℝ) ≤ s ∧
      (s : ℝ) ≤ chapterVICubicClusterNode 28 (radialIndex i + 1) := by
  rcases exists_mem_adjacent_node_interval
      (fun i ↦ (chapterVICubicClusterNode 28 (i + 22) : ℝ)) 6 (by norm_num)
      (by
        intro i j hij
        change ((chapterVICubicClusterNode 28 (i + 22) : ℚ) : ℝ) ≤
          ((chapterVICubicClusterNode 28 (j + 22) : ℚ) : ℝ)
        exact_mod_cast monotone_chapterVICubicClusterNode (by norm_num : 0 < 28)
          (by omega : i + 22 ≤ j + 22))
      (by simpa [ChapterVIDPinchingArcPrefixCompiledGrid.prefixEnd,
        ChapterVIDPinchingArcPrefixCompiledGrid.radialIndex] using hprefix)
      (by simpa using s.property.2) with ⟨i, hi, hlo, hup⟩
  exact ⟨⟨i, hi⟩, by simpa [radialIndex] using hlo, by simpa [radialIndex] using hup⟩

theorem derivative_re_neg (verdict : CompiledVerdict)
    (side : ChapterVIDPinchingArcSide) (t s : I)
    (hprefix : (ChapterVIDPinchingArcPrefixCompiledGrid.prefixEnd : ℝ) < (s : ℝ))
    (_hpre : (s : ℝ) < 1) :
    (chapterVIDRadialTailActualDerivative side t s).re < 0 := by
  rcases exists_radial_cell hprefix.le with ⟨i, hlower, hupper⟩
  rcases ChapterVIDPinchingArcPrefixCompiledGrid.exists_unit_contains side t with ⟨j, hunit⟩
  have hcontains := output_contains_cell verdict side i j s t hlower hupper hunit
  have hupperNeg :
      ((trace side i j).output.real.upper : ℝ) /
        ChapterVISignedDyadicInterval.scale 20 < 0 :=
    div_neg_of_neg_of_pos (by exact_mod_cast output_upper_neg verdict side i j)
      (ChapterVISignedDyadicInterval.scale_pos 20)
  exact hcontains.1.2.trans_lt hupperNeg

end ChapterVIDRadialTailDerivativeCompiledGrid

end PoincareChapterVI
