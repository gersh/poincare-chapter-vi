/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.ChapterVIDOuterArcPolarCompiledGrid

/-!
# Compiled full-circle prefix for Poincare's D contour

The existing polar certificate covers the two right-hand quarters for the complete parameter
interval.  This file treats the two omitted left-hand quarters on the compact prefix ending at
the twenty-second node of the 28-cell cubic radial mesh.  Thus all four quarters of the moving
circle are certified from the literal initial circle through

`s = 1 - (6 / 28)^3`.

Only signed fixed-point operations are left to the compiled checker.  The definitions below keep
the continuum cover, rotations of the rational unit quarter, literal-radicand interpretation,
and positive-real conclusion inside Lean.
-/

open Complex Real

namespace PoincareChapterVI

open ChapterVILeanCompCertBatch
open ChapterVILeanCompCertIntervalBridge
open LeanCompCert.Ports.SignedProductClaims
open scoped Topology unitInterval

/-- The two rational quarters which contain the pinching point `-1`. -/
inductive ChapterVIDPinchingArcSide
  | upper
  | lower
  deriving DecidableEq

/-- The four certified quarters, listed counterclockwise from the positive real axis. -/
inductive ChapterVIDCertifiedCircleQuarter
  | rightUpper
  | leftUpper
  | leftLower
  | rightLower
  deriving DecidableEq

/-- Counterclockwise parametrizations `i Q(t)` and `-Q(t)` of the upper-left and lower-left
quarters, where `Q` is the rational first-quadrant parametrization. -/
noncomputable def chapterVIDRationalPinchingArcUnit
    (side : ChapterVIDPinchingArcSide) (t : I) : ℂ :=
  match side with
  | .upper => Complex.I * chapterVIDRationalUnitQuarter t
  | .lower => -chapterVIDRationalUnitQuarter t

/-- A uniform name for the four rational quarter parametrizations used by the compiled tables. -/
noncomputable def chapterVIDCertifiedCircleQuarterUnit
    (side : ChapterVIDCertifiedCircleQuarter) (t : I) : ℂ :=
  match side with
  | .rightUpper => chapterVIDRationalOuterArcUnit .initial t
  | .leftUpper => chapterVIDRationalPinchingArcUnit .upper t
  | .leftLower => chapterVIDRationalPinchingArcUnit .lower t
  | .rightLower => chapterVIDRationalOuterArcUnit .final t

theorem continuous_chapterVIDRationalPinchingArcUnit
    (side : ChapterVIDPinchingArcSide) :
    Continuous (chapterVIDRationalPinchingArcUnit side) := by
  cases side
  · exact continuous_const.mul continuous_chapterVIDRationalUnitQuarter
  · exact continuous_chapterVIDRationalUnitQuarter.neg

theorem chapterVIDRationalPinchingArcUnit_norm
    (side : ChapterVIDPinchingArcSide) (t : I) :
    ‖chapterVIDRationalPinchingArcUnit side t‖ = 1 := by
  cases side <;> simp [chapterVIDRationalPinchingArcUnit,
    chapterVIDRationalUnitQuarter_norm]

/-- Every point of the ordinary unit circle belongs to one of the four rationally parametrized
quarters.  This is the geometric bridge from the certificate parametrization to Poincare's
standard angular contour. -/
theorem exists_chapterVIDCertifiedCircleQuarterUnit_eq
    {z : ℂ} (hnorm : ‖z‖ = 1) :
    ∃ side t, chapterVIDCertifiedCircleQuarterUnit side t = z := by
  by_cases hx : 0 ≤ z.re
  · by_cases hy : 0 ≤ z.im
    · obtain ⟨t, ht⟩ := exists_chapterVIDRationalUnitQuarter_eq hnorm hx hy
      exact ⟨.rightUpper, t, by simpa [chapterVIDCertifiedCircleQuarterUnit,
        chapterVIDRationalOuterArcUnit] using ht⟩
    · have hy' : z.im ≤ 0 := le_of_not_ge hy
      let q : ℂ := Complex.I * z
      have hqnorm : ‖q‖ = 1 := by simp [q, hnorm]
      have hqre : 0 ≤ q.re := by simpa [q, Complex.mul_re] using neg_nonneg.mpr hy'
      have hqim : 0 ≤ q.im := by simpa [q, Complex.mul_im] using hx
      obtain ⟨t, ht⟩ := exists_chapterVIDRationalUnitQuarter_eq hqnorm hqre hqim
      refine ⟨.rightLower, t, ?_⟩
      simp only [chapterVIDCertifiedCircleQuarterUnit, chapterVIDRationalOuterArcUnit]
      rw [ht]
      apply Complex.ext <;> simp [q, Complex.mul_re, Complex.mul_im]
  · have hx' : z.re ≤ 0 := le_of_not_ge hx
    by_cases hy : 0 ≤ z.im
    · let q : ℂ := -Complex.I * z
      have hqnorm : ‖q‖ = 1 := by simp [q, hnorm]
      have hqre : 0 ≤ q.re := by simpa [q, Complex.mul_re] using hy
      have hqim : 0 ≤ q.im := by simpa [q, Complex.mul_im] using neg_nonneg.mpr hx'
      obtain ⟨t, ht⟩ := exists_chapterVIDRationalUnitQuarter_eq hqnorm hqre hqim
      refine ⟨.leftUpper, t, ?_⟩
      simp only [chapterVIDCertifiedCircleQuarterUnit,
        chapterVIDRationalPinchingArcUnit]
      rw [ht]
      apply Complex.ext <;> simp [q, Complex.mul_re, Complex.mul_im]
    · have hy' : z.im ≤ 0 := le_of_not_ge hy
      have hnegNorm : ‖-z‖ = 1 := by simpa using hnorm
      obtain ⟨t, ht⟩ := exists_chapterVIDRationalUnitQuarter_eq hnegNorm
        (by simpa using neg_nonneg.mpr hx') (by simpa using neg_nonneg.mpr hy')
      exact ⟨.leftLower, t, by simpa [chapterVIDCertifiedCircleQuarterUnit,
        chapterVIDRationalPinchingArcUnit] using congrArg Neg.neg ht⟩

/-- The literal moving root-coordinate point on either pinching quarter. -/
noncomputable def chapterVIDPinchingArcPoint
    (side : ChapterVIDPinchingArcSide) (st : I × I) : ℂ :=
  (chapterVIDCertificateContourRadius st.1 : ℂ) *
    chapterVIDRationalPinchingArcUnit side st.2

theorem continuous_chapterVIDPinchingArcPoint
    (side : ChapterVIDPinchingArcSide) :
    Continuous (chapterVIDPinchingArcPoint side) := by
  unfold chapterVIDPinchingArcPoint
  exact (Complex.ofRealCLM.continuous.comp
      (continuous_chapterVIDCertificateContourRadius.comp continuous_fst)).mul
    ((continuous_chapterVIDRationalPinchingArcUnit side).comp continuous_snd)

theorem chapterVIDPinchingArcPoint_norm
    (side : ChapterVIDPinchingArcSide) (st : I × I) :
    ‖chapterVIDPinchingArcPoint side st‖ = chapterVIDCertificateContourRadius st.1 := by
  rw [chapterVIDPinchingArcPoint, norm_mul,
    chapterVIDRationalPinchingArcUnit_norm, mul_one, norm_real, Real.norm_eq_abs,
    abs_of_pos (chapterVIDCertificateContourRadius_pos st.1)]

theorem chapterVIDPinchingArcPoint_ne_zero
    (side : ChapterVIDPinchingArcSide) (st : I × I) :
    chapterVIDPinchingArcPoint side st ≠ 0 := by
  intro hzero
  have hnorm := congrArg norm hzero
  rw [chapterVIDPinchingArcPoint_norm] at hnorm
  norm_num at hnorm
  exact (chapterVIDCertificateContourRadius_pos st.1).ne' hnorm

/-- Poincare's literal transformed source radicand on a pinching quarter. -/
noncomputable def chapterVIDPinchingArcRadicand
    (side : ChapterVIDPinchingArcSide) (st : I × I) : ℂ :=
  chapterVIDRootCoordinateRadicand (chapterVIDCommonParameterRootPath st.1)
    (chapterVIDPinchingArcPoint side st)

theorem continuous_chapterVIDPinchingArcRadicand
    (side : ChapterVIDPinchingArcSide) :
    Continuous (chapterVIDPinchingArcRadicand side) := by
  exact continuous_chapterVIDRootCoordinateRadicand_comp
    (chapterVIDRootCoordinatePinch.parameterRoot.continuous.comp continuous_fst)
    (continuous_chapterVIDPinchingArcPoint side)
    (fun st ↦ chapterVIDCommonParameterRootPath_ne_zero st.1)
    (chapterVIDPinchingArcPoint_ne_zero side)

namespace ChapterVIDPinchingArcPrefixCompiledGrid

abbrev Interval := ChapterVISignedDyadicInterval 20

/-- The last radial node covered by the compact full-circle certificate. -/
def prefixEnd : ℚ := chapterVICubicClusterNode 28 22

theorem prefixEnd_eq : prefixEnd = 2717 / 2744 := by
  norm_num [prefixEnd, chapterVICubicClusterNode]

theorem prefixEnd_mem_Icc : (prefixEnd : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
  rw [prefixEnd_eq]
  norm_num

def sideName : ChapterVIDPinchingArcSide → String
  | .upper => "upper"
  | .lower => "lower"

def radialIndex (i : Fin 22) : Fin 28 := ⟨i, by omega⟩

def shardArtifactName (side : ChapterVIDPinchingArcSide) (i : Fin 22) : String :=
  s!"PoincareChapterVI.pinchingArcPrefix20.{sideName side}.{i.val}"

/-- Exact rectangle rotations of the already checked rational first-quarter trace. -/
def unit (side : ChapterVIDPinchingArcSide) (j : Fin 32) :
    ChapterVISignedDyadicComplexRectangle 20 :=
  let trace := ChapterVIDOuterArcUnitClusteredCompiledGrid.trace j
  match side with
  | .upper => ⟨trace.imagOut.neg, trace.realOut⟩
  | .lower => ⟨trace.realOut.neg, trace.imagOut.neg⟩

theorem unit_contains_cell
    (side : ChapterVIDPinchingArcSide) (j : Fin 32) {parameter : I}
    (hlower : (chapterVIQuadraticClusterNode 32 j : ℝ) ≤ parameter)
    (hupper : (parameter : ℝ) ≤ chapterVIQuadraticClusterNode 32 (j + 1)) :
    (unit side j).Contains (chapterVIDRationalPinchingArcUnit side parameter) := by
  have hquarter := ChapterVIDOuterArcUnitClusteredCompiledGrid.outerOutput_contains_cell
    .initial j hlower hupper
  cases side
  · constructor
    · simpa [unit, ChapterVIDOuterArcUnitTrace.outerOutput,
        ChapterVIDOuterArcUnitTrace.Trace.output,
        chapterVIDRationalPinchingArcUnit, chapterVIDRationalOuterArcUnit] using
          ChapterVISignedDyadicInterval.neg_contains hquarter.2
    · simpa [unit, ChapterVIDOuterArcUnitTrace.outerOutput,
        ChapterVIDOuterArcUnitTrace.Trace.output,
        chapterVIDRationalPinchingArcUnit, chapterVIDRationalOuterArcUnit] using hquarter.1
  · constructor
    · simpa [unit, ChapterVIDOuterArcUnitTrace.outerOutput,
        ChapterVIDOuterArcUnitTrace.Trace.output,
        chapterVIDRationalPinchingArcUnit, chapterVIDRationalOuterArcUnit] using
          ChapterVISignedDyadicInterval.neg_contains hquarter.1
    · simpa [unit, ChapterVIDOuterArcUnitTrace.outerOutput,
        ChapterVIDOuterArcUnitTrace.Trace.output,
        chapterVIDRationalPinchingArcUnit, chapterVIDRationalOuterArcUnit] using
          ChapterVISignedDyadicInterval.neg_contains hquarter.2

theorem exists_unit_contains
    (side : ChapterVIDPinchingArcSide) (parameter : I) :
    ∃ j : Fin 32,
      (unit side j).Contains (chapterVIDRationalPinchingArcUnit side parameter) := by
  rcases exists_mem_quadraticClusterCell 32 (by norm_num) parameter with
    ⟨j, hj, hlower, hupper⟩
  exact ⟨⟨j, hj⟩, unit_contains_cell side ⟨j, hj⟩ hlower hupper⟩

def trace (side : ChapterVIDPinchingArcSide) (i : Fin 22) (j : Fin 32) :=
  let radial := ChapterVIDRadialClusteredCompiledGrid.trace (radialIndex i)
  ChapterVILeanCompCertProposals.radicandTrace radial.qCubeRoot radial.radius (unit side j)
    ChapterVIDOuterArcPolarCompiledGrid.exponentialCoefficient
    ChapterVIDOuterArcPolarCompiledGrid.inverse10001

def radialLowerClaim (i : Fin 22) : Claim :=
  ChapterVIDOuterArcPolarCompiledGrid.radialLowerClaim (radialIndex i)

def radialUpperClaim (i : Fin 22) : Claim :=
  ChapterVIDOuterArcPolarCompiledGrid.radialUpperClaim (radialIndex i)

def cellOperations (side : ChapterVIDPinchingArcSide) (i : Fin 22) (j : Fin 32) :
    List (DyadicOperation 20) :=
  let cellTrace := trace side i j
  cellTrace.operations ++
    [.positiveLower cellTrace.output.real,
      .rawClaim (radialLowerClaim i), .rawClaim (radialUpperClaim i)]

def shardOperations (side : ChapterVIDPinchingArcSide) (i : Fin 22) :
    List (DyadicOperation 20) :=
  (List.finRange 32).flatMap fun j ↦ cellOperations side i j

theorem trace_operations_mem (side : ChapterVIDPinchingArcSide) (i : Fin 22) (j : Fin 32)
    (operation : DyadicOperation 20) (hoperation : operation ∈ (trace side i j).operations) :
    operation ∈ shardOperations side i := by
  rw [shardOperations, List.mem_flatMap]
  exact ⟨j, by simp, List.mem_append_left _ hoperation⟩

theorem positiveLower_mem (side : ChapterVIDPinchingArcSide) (i : Fin 22) (j : Fin 32) :
    DyadicOperation.positiveLower (trace side i j).output.real ∈
      shardOperations side i := by
  rw [shardOperations, List.mem_flatMap]
  exact ⟨j, by simp, by simp [cellOperations]⟩

theorem radialLower_mem (side : ChapterVIDPinchingArcSide) (i : Fin 22) (j : Fin 32) :
    DyadicOperation.rawClaim (radialLowerClaim i) ∈ shardOperations side i := by
  rw [shardOperations, List.mem_flatMap]
  exact ⟨j, by simp, by simp [cellOperations]⟩

theorem radialUpper_mem (side : ChapterVIDPinchingArcSide) (i : Fin 22) (j : Fin 32) :
    DyadicOperation.rawClaim (radialUpperClaim i) ∈ shardOperations side i := by
  rw [shardOperations, List.mem_flatMap]
  exact ⟨j, by simp, by simp [cellOperations]⟩

structure ShardVerdict (side : ChapterVIDPinchingArcSide) (i : Fin 22) : Prop where
  admissible : Admissible (batchClaims (shardOperations side i))
  returnsZero :
    (batchComputation (shardArtifactName side i) (shardOperations side i)).Returns
      ((0 : Nat) : Int)

structure CompiledVerdict : Prop where
  shard : ∀ side i, ShardVerdict side i

theorem radial_radius_bounds (verdict : CompiledVerdict)
    (side : ChapterVIDPinchingArcSide) (i : Fin 22) (j : Fin 32) :
    (1 / 5 : ℝ) ≤
        ((ChapterVIDRadialClusteredCompiledGrid.trace (radialIndex i)).radius.lower : ℝ) /
          ChapterVISignedDyadicInterval.scale 20 ∧
      ((ChapterVIDRadialClusteredCompiledGrid.trace (radialIndex i)).radius.upper : ℝ) /
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
    ChapterVIDOuterArcPolarCompiledGrid.radialLowerClaim,
    ChapterVIDOuterArcPolarCompiledGrid.radialUpperClaim,
    productClaim_holds_iff, mul_one] at hlower hupper
  constructor
  · norm_num [ChapterVISignedDyadicInterval.scale]
    have hlowerReal : (1048576 : ℝ) ≤
        ((ChapterVIDRadialClusteredCompiledGrid.trace (radialIndex i)).radius.lower : ℝ) * 5 := by
      exact_mod_cast hlower
    linarith
  · norm_num [ChapterVISignedDyadicInterval.scale]
    have hupperReal :
        ((ChapterVIDRadialClusteredCompiledGrid.trace (radialIndex i)).radius.upper : ℝ) ≤
          1048576 := by
      exact_mod_cast hupper
    linarith

theorem output_lower_pos (verdict : CompiledVerdict)
    (side : ChapterVIDPinchingArcSide) (i : Fin 22) (j : Fin 32) :
    0 < (trace side i j).output.real.lower :=
  allSound_of_returns_zero (shardArtifactName side i)
    (shardOperations side i) (verdict.shard side i).admissible
      (verdict.shard side i).returnsZero
    (.positiveLower (trace side i j).output.real) (positiveLower_mem side i j)

theorem output_contains_cell (verdict : CompiledVerdict)
    (side : ChapterVIDPinchingArcSide) (i : Fin 22) (j : Fin 32)
    (st : I × I)
    (hζ : (ChapterVIDRadialClusteredCompiledGrid.trace (radialIndex i)).qCubeRoot.Contains
      (chapterVIDCertificateParameter st.1 ^ ((3 : ℝ)⁻¹)))
    (hradius : (ChapterVIDRadialClusteredCompiledGrid.trace (radialIndex i)).radius.Contains
      (chapterVIDCertificateContourRadius st.1))
    (hunit : (unit side j).Contains (chapterVIDRationalPinchingArcUnit side st.2)) :
    (trace side i j).output.Contains (chapterVIDPinchingArcRadicand side st) := by
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
  have hargument :
      ‖chapterVIDRootExponentialArgument (chapterVIDPinchingArcPoint side st)‖ ≤ 1 := by
    apply norm_chapterVIDRootExponentialArgument_le_one_of_mem_annulus
    · simpa [chapterVIDPinchingArcPoint_norm] using hrLower
    · simpa [chapterVIDPinchingArcPoint_norm] using hrUpper
  have hsemantic := (trace side i j).output_contains_rootCoordinateRadicand_of_allSound
    hall hζ hradius hunit (chapterVIDRationalPinchingArcUnit_norm side st.2)
    ChapterVIDOuterArcPolarCompiledGrid.exponentialCoefficient_contains
    ChapterVIDOuterArcPolarCompiledGrid.inverse10001_contains
    (Real.rpow_pos_of_pos (chapterVIDCertificateParameter_pos st.1) _)
    (chapterVIDCertificateContourRadius_pos st.1) hargument
  rw [chapterVIDPinchingArcRadicand, chapterVIDPinchingArcPoint,
    chapterVIDCommonParameterRootPath_eq_certificateValue]
  exact hsemantic

theorem exists_radial_outputs_contain_of_le_prefixEnd
    (parameter : I) (hparameter : (parameter : ℝ) ≤ prefixEnd) :
    ∃ i : Fin 22,
      (ChapterVIDRadialClusteredCompiledGrid.trace (radialIndex i)).qCubeRoot.Contains
          (chapterVIDCertificateParameter parameter ^ ((3 : ℝ)⁻¹)) ∧
        (ChapterVIDRadialClusteredCompiledGrid.trace (radialIndex i)).radius.Contains
          (chapterVIDCertificateContourRadius parameter) := by
  rcases exists_mem_adjacent_node_interval
      (fun i ↦ (chapterVICubicClusterNode 28 i : ℝ)) 22 (by norm_num)
      (by
        intro i j hij
        change ((chapterVICubicClusterNode 28 i : ℚ) : ℝ) ≤
          ((chapterVICubicClusterNode 28 j : ℚ) : ℝ)
        exact_mod_cast monotone_chapterVICubicClusterNode (by norm_num : 0 < 28) hij)
      (by simpa using parameter.property.1)
      (by simpa [prefixEnd] using hparameter) with ⟨i, hi, hlower, hupper⟩
  let i22 : Fin 22 := ⟨i, hi⟩
  have hi28 : i < 28 := by omega
  exact ⟨i22, ChapterVIDRadialClusteredCompiledGrid.outputs_contain_cell
    ⟨i, hi28⟩ hlower hupper⟩

theorem radicand_re_pos (verdict : CompiledVerdict)
    (side : ChapterVIDPinchingArcSide) (st : I × I)
    (hprefix : (st.1 : ℝ) ≤ prefixEnd) :
    0 < (chapterVIDPinchingArcRadicand side st).re := by
  rcases exists_radial_outputs_contain_of_le_prefixEnd st.1 hprefix with
    ⟨i, hζ, hradius⟩
  rcases exists_unit_contains side st.2 with ⟨j, hunit⟩
  have hcontains := output_contains_cell verdict side i j st hζ hradius hunit
  have hlower : 0 <
      ((trace side i j).output.real.lower : ℝ) /
        ChapterVISignedDyadicInterval.scale 20 :=
    div_pos (by exact_mod_cast output_lower_pos verdict side i j)
      (ChapterVISignedDyadicInterval.scale_pos 20)
  exact hlower.trans_le hcontains.1.1

theorem radicand_ne_zero (verdict : CompiledVerdict)
    (side : ChapterVIDPinchingArcSide) (st : I × I)
    (hprefix : (st.1 : ℝ) ≤ prefixEnd) :
    chapterVIDPinchingArcRadicand side st ≠ 0 := by
  intro hzero
  have hpos := radicand_re_pos verdict side st hprefix
  simp [hzero] at hpos

end ChapterVIDPinchingArcPrefixCompiledGrid

end PoincareChapterVI
