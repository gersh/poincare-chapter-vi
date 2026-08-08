/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.ChapterVIDOuterArcs
import PoincareChapterVI.ChapterVILeanCompCertComplexTrace

/-!
# Compiled interval trace for the rational outer-arc unit point

The exact quarter parametrization `((1-t²)+2ti)/(1+t²)` is evaluated over an entire dyadic input
interval.  Every rounded multiplication and the positive reciprocal of `1+t²` appears in the
shared LeanCompCert operation batch; addition, subtraction, and the final `-i` rotation are exact
at a fixed binary scale.
-/

namespace PoincareChapterVI

open ChapterVILeanCompCertBatch
open scoped unitInterval

namespace ChapterVIDOuterArcUnitTrace

/-- Rounded intermediates for one input interval of the rational unit quarter. -/
structure Trace {precision : ℕ} (t : ChapterVISignedDyadicInterval precision) where
  tSq : ChapterVISignedDyadicInterval precision
  denominatorInv : ChapterVISignedDyadicInterval precision
  twoT : ChapterVISignedDyadicInterval precision
  realOut : ChapterVISignedDyadicInterval precision
  imagOut : ChapterVISignedDyadicInterval precision

def Trace.one {precision : ℕ} {t : ChapterVISignedDyadicInterval precision}
    (_trace : Trace t) : ChapterVISignedDyadicInterval precision :=
  ChapterVISignedDyadicInterval.pointInt precision 1

def Trace.two {precision : ℕ} {t : ChapterVISignedDyadicInterval precision}
    (_trace : Trace t) : ChapterVISignedDyadicInterval precision :=
  ChapterVISignedDyadicInterval.pointInt precision 2

def Trace.denominator {precision : ℕ} {t : ChapterVISignedDyadicInterval precision}
    (trace : Trace t) : ChapterVISignedDyadicInterval precision :=
  trace.one.add trace.tSq

def Trace.realNumerator {precision : ℕ} {t : ChapterVISignedDyadicInterval precision}
    (trace : Trace t) : ChapterVISignedDyadicInterval precision :=
  trace.one.sub trace.tSq

def Trace.operations {precision : ℕ} {t : ChapterVISignedDyadicInterval precision}
    (trace : Trace t) : List (DyadicOperation precision) :=
  [ .mul t t trace.tSq
  , .positiveReciprocal trace.denominator trace.denominatorInv
  , .mul trace.two t trace.twoT
  , .mul trace.realNumerator trace.denominatorInv trace.realOut
  , .mul trace.twoT trace.denominatorInv trace.imagOut ]

def Trace.output {precision : ℕ} {t : ChapterVISignedDyadicInterval precision}
    (trace : Trace t) : ChapterVISignedDyadicComplexRectangle precision :=
  ⟨trace.realOut, trace.imagOut⟩

theorem Trace.output_contains_quarter_of_allSound {precision : ℕ}
    {t : ChapterVISignedDyadicInterval precision} (trace : Trace t)
    (hall : ∀ operation ∈ trace.operations, operation.Sound)
    {parameter : I} (hparameter : t.Contains (parameter : ℝ)) :
    trace.output.Contains (chapterVIDRationalUnitQuarter parameter) := by
  have htSq : ChapterVISignedDyadicInterval.MulCertificate t t trace.tSq :=
    hall (.mul t t trace.tSq) (by simp [Trace.operations])
  have hdenInv : ChapterVISignedDyadicInterval.PositiveReciprocalCertificate
      trace.denominator trace.denominatorInv :=
    hall (.positiveReciprocal trace.denominator trace.denominatorInv)
      (by simp [Trace.operations])
  have htwoT : ChapterVISignedDyadicInterval.MulCertificate
      trace.two t trace.twoT :=
    hall (.mul trace.two t trace.twoT) (by simp [Trace.operations])
  have hre : ChapterVISignedDyadicInterval.MulCertificate
      trace.realNumerator trace.denominatorInv trace.realOut :=
    hall (.mul trace.realNumerator trace.denominatorInv trace.realOut)
      (by simp [Trace.operations])
  have him : ChapterVISignedDyadicInterval.MulCertificate
      trace.twoT trace.denominatorInv trace.imagOut :=
    hall (.mul trace.twoT trace.denominatorInv trace.imagOut)
      (by simp [Trace.operations])
  have hone := ChapterVISignedDyadicInterval.pointInt_contains precision 1
  have htwo := ChapterVISignedDyadicInterval.pointInt_contains precision 2
  have htSqValue := htSq.contains_mul hparameter hparameter
  have hdenominator : trace.denominator.Contains (1 + (parameter : ℝ) ^ 2) := by
    simpa [Trace.denominator, Trace.one, pow_two] using
      ChapterVISignedDyadicInterval.add_contains hone htSqValue
  have hdenominatorInv := hdenInv.contains_inv hdenominator
  have hrealNumerator : trace.realNumerator.Contains (1 - (parameter : ℝ) ^ 2) := by
    simpa [Trace.realNumerator, Trace.one, pow_two] using
      ChapterVISignedDyadicInterval.sub_contains hone htSqValue
  have htwoTValue := htwoT.contains_mul htwo hparameter
  have hrealValue := hre.contains_mul hrealNumerator hdenominatorInv
  have himagValue := him.contains_mul htwoTValue hdenominatorInv
  have hquarterRe : (chapterVIDRationalUnitQuarter parameter).re =
      (1 - (parameter : ℝ) ^ 2) / (1 + (parameter : ℝ) ^ 2) := by
    simp only [chapterVIDRationalUnitQuarter, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero,
      zero_mul, sub_zero, add_zero]
  have hquarterIm : (chapterVIDRationalUnitQuarter parameter).im =
      (2 * (parameter : ℝ)) / (1 + (parameter : ℝ) ^ 2) := by
    simp only [chapterVIDRationalUnitQuarter, Complex.add_im, Complex.ofReal_im,
      Complex.mul_im, Complex.ofReal_re, Complex.I_re, Complex.I_im, mul_zero,
      mul_one, zero_add, add_zero]
  constructor
  · rw [hquarterRe]
    simpa [Trace.output, div_eq_mul_inv] using hrealValue
  · rw [hquarterIm]
    simpa [Trace.output, div_eq_mul_inv] using himagValue

theorem Trace.output_contains_quarter_of_batch {precision : ℕ}
    {t : ChapterVISignedDyadicInterval precision} (trace : Trace t)
    (name : String) (operations : List (DyadicOperation precision))
    (hoperations : ∀ operation ∈ trace.operations, operation ∈ operations)
    (hadmissible : LeanCompCert.Ports.SignedProductClaims.Admissible
      (batchClaims operations))
    (hrun : (batchComputation name operations).Returns ((0 : Nat) : Int))
    {parameter : I} (hparameter : t.Contains (parameter : ℝ)) :
    trace.output.Contains (chapterVIDRationalUnitQuarter parameter) := by
  apply trace.output_contains_quarter_of_allSound
  · intro operation hoperation
    exact allSound_of_returns_zero name operations hadmissible hrun operation
      (hoperations operation hoperation)
  · exact hparameter

/-- Exact rectangle rotation for the final quarter. -/
def outerOutput {precision : ℕ} {t : ChapterVISignedDyadicInterval precision}
    (side : ChapterVIDOuterArcSide) (trace : Trace t) :
    ChapterVISignedDyadicComplexRectangle precision :=
  match side with
  | .initial => trace.output
  | .final => ⟨trace.imagOut, trace.realOut.neg⟩

theorem outerOutput_contains_of_allSound {precision : ℕ}
    {t : ChapterVISignedDyadicInterval precision}
    (side : ChapterVIDOuterArcSide) (trace : Trace t)
    (hall : ∀ operation ∈ trace.operations, operation.Sound)
    {parameter : I} (hparameter : t.Contains (parameter : ℝ)) :
    (outerOutput side trace).Contains
      (chapterVIDRationalOuterArcUnit side parameter) := by
  have hquarter := trace.output_contains_quarter_of_allSound hall hparameter
  cases side
  · exact hquarter
  · constructor
    · simpa [outerOutput, Trace.output, chapterVIDRationalOuterArcUnit] using hquarter.2
    · simpa [outerOutput, Trace.output, chapterVIDRationalOuterArcUnit] using
        ChapterVISignedDyadicInterval.neg_contains hquarter.1

end ChapterVIDOuterArcUnitTrace

end PoincareChapterVI
