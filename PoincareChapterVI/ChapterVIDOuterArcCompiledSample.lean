/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.ChapterVIDOuterArcs
import PoincareChapterVI.ChapterVILeanCompCertIntervalBridge

/-!
# First compiled sample on the D outer arc

At the initial corner of the initial outer-arc rectangle, both factors in the sparse radicand
are exactly `-10201 / 10001`.  This file encloses that value at 16 binary fractional bits and
uses the LeanCompCert signed-product program to certify their product.  It is the first concrete
row of the eventual two-dimensional outer-arc table.
-/

noncomputable section

open Complex Real
open scoped Topology unitInterval

namespace PoincareChapterVI

open ChapterVILeanCompCertIntervalBridge
open LeanCompCert.Ports.SignedProductClaims

def chapterVIDOuterArcOriginFactorInterval : ChapterVISignedDyadicInterval 16 :=
  ⟨-66847, -66846⟩

def chapterVIDOuterArcOriginProductInterval : ChapterVISignedDyadicInterval 16 :=
  ⟨68182, 68185⟩

theorem chapterVIDOuterArcOriginFactor_mem :
    chapterVIDOuterArcOriginFactorInterval.Contains (-10201 / 10001 : ℝ) := by
  constructor <;>
    norm_num [ChapterVISignedDyadicInterval.Contains,
      ChapterVISignedDyadicInterval.toRealInterval,
      ChapterVISignedDyadicInterval.scale, chapterVIDOuterArcOriginFactorInterval]

theorem chapterVIDOuterArcOriginMulClaims_admissible :
    Admissible (mulClaims chapterVIDOuterArcOriginFactorInterval
      chapterVIDOuterArcOriginFactorInterval chapterVIDOuterArcOriginProductInterval) := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem chapterVIDOuterArcOriginMulClaims_returns_zero :
    (claimComputation "chapter-vi-d-outer-arc-origin"
      (mulClaims chapterVIDOuterArcOriginFactorInterval
        chapterVIDOuterArcOriginFactorInterval chapterVIDOuterArcOriginProductInterval)).Returns
      ((0 : Nat) : Int) := by
  decide +kernel

/-- The compiled signed arithmetic proves a strictly positive enclosure of the origin sample. -/
theorem chapterVIDOuterArcOriginProduct_mem :
    chapterVIDOuterArcOriginProductInterval.Contains
      ((-10201 / 10001 : ℝ) * (-10201 / 10001 : ℝ)) := by
  exact mul_contains_of_compiled "chapter-vi-d-outer-arc-origin"
    chapterVIDOuterArcOriginFactorInterval chapterVIDOuterArcOriginFactorInterval
    chapterVIDOuterArcOriginProductInterval chapterVIDOuterArcOriginMulClaims_admissible
    chapterVIDOuterArcOriginMulClaims_returns_zero chapterVIDOuterArcOriginFactor_mem
    chapterVIDOuterArcOriginFactor_mem

theorem chapterVIDOuterArcOriginProduct_lower_pos :
    0 < (chapterVIDOuterArcOriginProductInterval.toRealInterval.lower) := by
  norm_num [ChapterVISignedDyadicInterval.toRealInterval,
    ChapterVISignedDyadicInterval.scale, chapterVIDOuterArcOriginProductInterval]

/-- Exact identification of this compiled row with Poincaré's literal transformed radicand. -/
theorem chapterVIDOuterArcRadicand_initial_origin :
    chapterVIDOuterArcRadicand .initial ((0 : I), (0 : I)) =
      ((-10201 / 10001 : ℝ) : ℂ) * ((-10201 / 10001 : ℝ) : ℂ) := by
  rw [chapterVIDOuterArcRadicand_eq_certificateFormula]
  have hroot : chapterVIPositiveRealCubicLift 1 = 1 := by
    norm_num [chapterVIPositiveRealCubicLift, chapterVIPositiveRealCubicValue]
  simp [chapterVIDOuterArcCertificateFormula, chapterVIDOuterArcPoint,
    chapterVIDRationalOuterArcUnit, chapterVIDRationalUnitQuarter, hroot]
  norm_num

theorem chapterVIDOuterArcRadicand_initial_origin_re_mem :
    chapterVIDOuterArcOriginProductInterval.Contains
      (chapterVIDOuterArcRadicand .initial ((0 : I), (0 : I))).re := by
  rw [chapterVIDOuterArcRadicand_initial_origin]
  simpa using chapterVIDOuterArcOriginProduct_mem

/-- The first concrete sample satisfies the positive-real-part target of the global cover. -/
theorem chapterVIDOuterArcRadicand_initial_origin_re_pos :
    0 < (chapterVIDOuterArcRadicand .initial ((0 : I), (0 : I))).re :=
  chapterVIDOuterArcOriginProduct_lower_pos.trans_le
    chapterVIDOuterArcRadicand_initial_origin_re_mem.1

end PoincareChapterVI
