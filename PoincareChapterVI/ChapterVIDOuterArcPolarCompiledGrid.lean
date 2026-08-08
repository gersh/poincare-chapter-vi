/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.ChapterVIDRadialClusteredCompiledGrid
import PoincareChapterVI.ChapterVIDOuterArcUnitClusteredCompiledGrid

/-!
# Full compiled polar certificate for the two D outer arcs

The finite table contains 1,792 polar cells.  Its mathematical theorem is conditional on one
LeanCompCert run verdict, following LeanCompCert's scalable compiled-artifact route.  All analytic
interpretation, continuum coverage, and the reduction from the literal radicand to fixed-point
operations are proved in Lean; the run checks only finite signed-integer claims.
-/

namespace PoincareChapterVI

open ChapterVILeanCompCertBatch
open ChapterVILeanCompCertIntervalBridge
open LeanCompCert.Ports.SignedProductClaims
open scoped Topology unitInterval

namespace ChapterVIDOuterArcPolarCompiledGrid

abbrev Interval := ChapterVISignedDyadicInterval 20

def sideName : ChapterVIDOuterArcSide → String
  | .initial => "initial"
  | .final => "final"

def shardArtifactName (side : ChapterVIDOuterArcSide) (i : Fin 28) : String :=
  s!"PoincareChapterVI.outerPolarGrid20.{sideName side}.{i.val}"

def exponentialCoefficient : Interval := ⟨3494, 3495⟩

def inverse10001 : Interval := ⟨104, 105⟩

def unit (side : ChapterVIDOuterArcSide) (j : Fin 32) :=
  ChapterVIDOuterArcUnitTrace.outerOutput side
    (ChapterVIDOuterArcUnitClusteredCompiledGrid.trace j)

def trace (side : ChapterVIDOuterArcSide) (i : Fin 28) (j : Fin 32) :=
  let radial := ChapterVIDRadialClusteredCompiledGrid.trace i
  let unitValue := unit side j
  ChapterVILeanCompCertProposals.radicandTrace
    radial.qCubeRoot radial.radius unitValue exponentialCoefficient inverse10001

def radialLowerClaim (i : Fin 28) : Claim :=
  productClaim (2 ^ 20) 1
    (ChapterVIDRadialClusteredCompiledGrid.trace i).radius.lower 5

def radialUpperClaim (i : Fin 28) : Claim :=
  productClaim (ChapterVIDRadialClusteredCompiledGrid.trace i).radius.upper 1
    (2 ^ 20) 1

def cellOperations (side : ChapterVIDOuterArcSide) (i : Fin 28) (j : Fin 32) :
    List (DyadicOperation 20) :=
  let cellTrace := trace side i j
  cellTrace.operations ++
    [.positiveLower cellTrace.output.real,
      .rawClaim (radialLowerClaim i), .rawClaim (radialUpperClaim i)]

def shardOperations (side : ChapterVIDOuterArcSide) (i : Fin 28) :
    List (DyadicOperation 20) :=
  (List.finRange 32).flatMap fun j => cellOperations side i j

theorem trace_operations_mem (side : ChapterVIDOuterArcSide) (i : Fin 28) (j : Fin 32)
    (operation : DyadicOperation 20) (hoperation : operation ∈ (trace side i j).operations) :
    operation ∈ shardOperations side i := by
  rw [shardOperations, List.mem_flatMap]
  exact ⟨j, by simp, List.mem_append_left _ hoperation⟩

theorem positiveLower_mem (side : ChapterVIDOuterArcSide) (i : Fin 28) (j : Fin 32) :
    DyadicOperation.positiveLower (trace side i j).output.real ∈
      shardOperations side i := by
  rw [shardOperations, List.mem_flatMap]
  exact ⟨j, by simp, by simp [cellOperations]⟩

theorem radialLower_mem (side : ChapterVIDOuterArcSide) (i : Fin 28) (j : Fin 32) :
    DyadicOperation.rawClaim (radialLowerClaim i) ∈ shardOperations side i := by
  rw [shardOperations, List.mem_flatMap]
  exact ⟨j, by simp, by simp [cellOperations]⟩

theorem radialUpper_mem (side : ChapterVIDOuterArcSide) (i : Fin 28) (j : Fin 32) :
    DyadicOperation.rawClaim (radialUpperClaim i) ∈ shardOperations side i := by
  rw [shardOperations, List.mem_flatMap]
  exact ⟨j, by simp, by simp [cellOperations]⟩

/-- One radial row is one bounded-size CompCert artifact. -/
structure ShardVerdict (side : ChapterVIDOuterArcSide) (i : Fin 28) : Prop where
  admissible : Admissible (batchClaims (shardOperations side i))
  returnsZero :
    (batchComputation (shardArtifactName side i) (shardOperations side i)).Returns
      ((0 : Nat) : Int)

/-- The explicit finite execution obligation for all 56 independently rerunnable shards. -/
structure CompiledVerdict : Prop where
  shard : ∀ side i, ShardVerdict side i

theorem exponentialCoefficient_contains :
    exponentialCoefficient.Contains (100 / 30003 : ℝ) := by
  norm_num [exponentialCoefficient, ChapterVISignedDyadicInterval.Contains,
    ChapterVISignedDyadicInterval.toRealInterval, ChapterVIRealInterval.Contains,
    ChapterVISignedDyadicInterval.scale]

theorem inverse10001_contains : inverse10001.Contains (1 / 10001 : ℝ) := by
  norm_num [inverse10001, ChapterVISignedDyadicInterval.Contains,
    ChapterVISignedDyadicInterval.toRealInterval, ChapterVIRealInterval.Contains,
    ChapterVISignedDyadicInterval.scale]

theorem radial_radius_bounds (verdict : CompiledVerdict)
    (side : ChapterVIDOuterArcSide) (i : Fin 28) (j : Fin 32) :
    (1 / 5 : ℝ) ≤
        ((ChapterVIDRadialClusteredCompiledGrid.trace i).radius.lower : ℝ) /
          ChapterVISignedDyadicInterval.scale 20 ∧
      ((ChapterVIDRadialClusteredCompiledGrid.trace i).radius.upper : ℝ) /
          ChapterVISignedDyadicInterval.scale 20 ≤ 1 := by
  have hlower := allSound_of_returns_zero (shardArtifactName side i)
    (shardOperations side i) (verdict.shard side i).admissible
      (verdict.shard side i).returnsZero
    (.rawClaim (radialLowerClaim i)) (radialLower_mem side i j)
  have hupper := allSound_of_returns_zero (shardArtifactName side i)
    (shardOperations side i) (verdict.shard side i).admissible
      (verdict.shard side i).returnsZero
    (.rawClaim (radialUpperClaim i)) (radialUpper_mem side i j)
  simp only [DyadicOperation.Sound, radialLowerClaim, radialUpperClaim,
    productClaim_holds_iff, mul_one] at hlower hupper
  constructor
  · norm_num [ChapterVISignedDyadicInterval.scale]
    have hlowerReal : (1048576 : ℝ) ≤
        ((ChapterVIDRadialClusteredCompiledGrid.trace i).radius.lower : ℝ) * 5 := by
      exact_mod_cast hlower
    linarith
  · norm_num [ChapterVISignedDyadicInterval.scale]
    have hupperReal :
        ((ChapterVIDRadialClusteredCompiledGrid.trace i).radius.upper : ℝ) ≤ 1048576 := by
      exact_mod_cast hupper
    linarith

theorem output_lower_pos (verdict : CompiledVerdict)
    (side : ChapterVIDOuterArcSide) (i : Fin 28) (j : Fin 32) :
    0 < (trace side i j).output.real.lower :=
  allSound_of_returns_zero (shardArtifactName side i)
    (shardOperations side i) (verdict.shard side i).admissible
      (verdict.shard side i).returnsZero
    (.positiveLower (trace side i j).output.real) (positiveLower_mem side i j)

theorem output_contains_cell (verdict : CompiledVerdict)
    (side : ChapterVIDOuterArcSide) (i : Fin 28) (j : Fin 32)
    (st : I × I)
    (hζ : (ChapterVIDRadialClusteredCompiledGrid.trace i).qCubeRoot.Contains
      (chapterVIDCertificateParameter st.1 ^ ((3 : ℝ)⁻¹)))
    (hradius : (ChapterVIDRadialClusteredCompiledGrid.trace i).radius.Contains
      (chapterVIDCertificateContourRadius st.1))
    (hunit : (unit side j).Contains (chapterVIDRationalOuterArcUnit side st.2)) :
    (trace side i j).output.Contains (chapterVIDOuterArcRadicand side st) := by
  have hall : ∀ operation ∈ (trace side i j).operations, operation.Sound := by
    intro operation hoperation
    exact allSound_of_returns_zero (shardArtifactName side i)
      (shardOperations side i) (verdict.shard side i).admissible
        (verdict.shard side i).returnsZero operation
      (trace_operations_mem side i j operation hoperation)
  have hrBounds := radial_radius_bounds verdict side i j
  have hrLower : (1 / 5 : ℝ) ≤ chapterVIDCertificateContourRadius st.1 :=
    hrBounds.1.trans hradius.1
  have hrUpper : chapterVIDCertificateContourRadius st.1 ≤ 1 :=
    hradius.2.trans hrBounds.2
  have hargument := norm_chapterVIDOuterArcExponentialArgument_le_one
    side st hrLower hrUpper
  have hsemantic := (trace side i j).output_contains_rootCoordinateRadicand_of_allSound
    hall hζ hradius hunit (chapterVIDRationalOuterArcUnit_norm side st.2)
    exponentialCoefficient_contains inverse10001_contains
    (Real.rpow_pos_of_pos (chapterVIDCertificateParameter_pos st.1) _)
    (chapterVIDCertificateContourRadius_pos st.1) hargument
  rw [chapterVIDOuterArcRadicand, chapterVIDOuterArcPoint,
    chapterVIDCommonParameterRootPath_eq_certificateValue]
  exact hsemantic

theorem radicand_re_pos (verdict : CompiledVerdict)
    (side : ChapterVIDOuterArcSide) (st : I × I) :
    0 < (chapterVIDOuterArcRadicand side st).re := by
  rcases ChapterVIDRadialClusteredCompiledGrid.exists_outputs_contain st.1 with
    ⟨i, hζ, hradius⟩
  rcases ChapterVIDOuterArcUnitClusteredCompiledGrid.exists_outerOutput_contains side st.2 with
    ⟨j, hunit⟩
  have hcontains := output_contains_cell verdict side i j st hζ hradius hunit
  have hlower : 0 <
      ((trace side i j).output.real.lower : ℝ) / ChapterVISignedDyadicInterval.scale 20 :=
    div_pos (by exact_mod_cast output_lower_pos verdict side i j)
      (ChapterVISignedDyadicInterval.scale_pos 20)
  exact hlower.trans_le hcontains.1.1

/-- The compiled interval cover keeps the radicand away from zero on the whole parameter
rectangle, not merely at the finite mesh points. -/
theorem radicand_ne_zero (verdict : CompiledVerdict)
    (side : ChapterVIDOuterArcSide) (st : I × I) :
    chapterVIDOuterArcRadicand side st ≠ 0 := by
  intro hzero
  have hpos := radicand_re_pos verdict side st
  simp [hzero] at hpos

/-- The pointwise result from the compiled interval cover feeds the covering-space construction
and produces the compatible global square-root sheet required by Poincare's contour argument. -/
theorem exists_squareRootSheet (verdict : CompiledVerdict)
    (side : ChapterVIDOuterArcSide) (base : I × I) (baseRoot : ℂ)
    (hbaseRoot : baseRoot ^ 2 = chapterVIDOuterArcRadicand side base) :
    ∃ sheet : ChapterVIContinuousSquareRootSheet (chapterVIDOuterArcRadicand side),
      sheet.root base = baseRoot := by
  let : ContractibleSpace I :=
    (convex_Icc (0 : ℝ) 1).contractibleSpace (by simp)
  let : LocallyPathConnectedSpace I :=
    (convex_Icc (0 : ℝ) 1).locallyPathConnectedSpace
  let : LocallyPathConnectedSpace (I × I) := by
    refine LocallyPathConnectedSpace.of_bases
      (p := fun (point : I × I) (sets : Set I × Set I) ↦
        (sets.1 ∈ 𝓝 point.1 ∧ IsPathConnected sets.1) ∧
          (sets.2 ∈ 𝓝 point.2 ∧ IsPathConnected sets.2))
      (s := fun _ sets ↦ sets.1 ×ˢ sets.2) ?_ ?_
    · intro point
      rw [nhds_prod_eq]
      exact (path_connected_basis point.1).prod (path_connected_basis point.2)
    · intro _ sets hsets
      exact hsets.1.2.prod hsets.2.2
  exact exists_chapterVIContinuousSquareRootSheet
    (chapterVIDOuterArcRadicand side) (continuous_chapterVIDOuterArcRadicand side)
    (radicand_ne_zero verdict side) base baseRoot hbaseRoot

end ChapterVIDOuterArcPolarCompiledGrid

end PoincareChapterVI
