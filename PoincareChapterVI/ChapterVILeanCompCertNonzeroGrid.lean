/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.ChapterVILeanCompCertComplexTrace

/-!
# Compiled nonvanishing grids for complex-valued functions

A complex rectangle excludes zero as soon as one of its four signed coordinate bounds is
strictly positive: positive real, negative real, positive imaginary, or negative imaginary.
This file turns that observation into a generic LeanCompCert grid interface. The compiled
program checks only signed-integer endpoint comparisons. Lean retains the proofs that the cells
cover the analytic parameter space and that each computed rectangle encloses the actual value.
-/

namespace PoincareChapterVI

open ChapterVILeanCompCertBatch
open LeanCompCert.Ports.SignedProductClaims

/-- Which signed coordinate separates a complex rectangle from zero. -/
inductive ChapterVIComplexZeroSeparation
  | realPositive
  | realNegative
  | imagPositive
  | imagNegative
  deriving DecidableEq, Repr

namespace ChapterVIComplexZeroSeparation

/-- The signed dyadic interval whose lower endpoint must be positive. -/
def interval {precision : ℕ}
    (separation : ChapterVIComplexZeroSeparation)
    (rectangle : ChapterVISignedDyadicComplexRectangle precision) :
    ChapterVISignedDyadicInterval precision :=
  match separation with
  | .realPositive => rectangle.real
  | .realNegative => rectangle.real.neg
  | .imagPositive => rectangle.imag
  | .imagNegative => rectangle.imag.neg

/-- The corresponding signed real coordinate of an actual complex value. -/
def value (separation : ChapterVIComplexZeroSeparation) (z : ℂ) : ℝ :=
  match separation with
  | .realPositive => z.re
  | .realNegative => -z.re
  | .imagPositive => z.im
  | .imagNegative => -z.im

theorem interval_contains_value
    {precision : ℕ}
    (separation : ChapterVIComplexZeroSeparation)
    {rectangle : ChapterVISignedDyadicComplexRectangle precision}
    {z : ℂ} (hz : rectangle.Contains z) :
    (separation.interval rectangle).Contains (separation.value z) := by
  cases separation with
  | realPositive => exact hz.1
  | realNegative => exact ChapterVISignedDyadicInterval.neg_contains hz.1
  | imagPositive => exact hz.2
  | imagNegative => exact ChapterVISignedDyadicInterval.neg_contains hz.2

theorem ne_zero_of_lower_pos
    {precision : ℕ}
    (separation : ChapterVIComplexZeroSeparation)
    {rectangle : ChapterVISignedDyadicComplexRectangle precision}
    {z : ℂ} (hz : rectangle.Contains z)
    (hlower : 0 < (separation.interval rectangle).lower) :
    z ≠ 0 := by
  have hvalue : 0 < separation.value z := by
    have hcontains := separation.interval_contains_value hz
    exact (by
      have hlowerReal : 0 <
          ((separation.interval rectangle).lower : ℝ) /
            ChapterVISignedDyadicInterval.scale precision :=
        div_pos (by exact_mod_cast hlower)
          (ChapterVISignedDyadicInterval.scale_pos precision)
      exact hlowerReal.trans_le hcontains.1)
  intro hzero
  subst z
  cases separation <;> simp [value] at hvalue

end ChapterVIComplexZeroSeparation

namespace ChapterVILeanCompCertNonzeroGrid

/-- The single compiled comparison attached to one complex interval cell. -/
def separationOperation {precision : ℕ}
    (rectangle : ChapterVISignedDyadicComplexRectangle precision)
    (separation : ChapterVIComplexZeroSeparation) : DyadicOperation precision :=
  .positiveLower (separation.interval rectangle)

/-- Flatten the separation checks for a finite grid into one LeanCompCert batch. -/
def operations {precision cells : ℕ}
    (output : Fin cells → ChapterVISignedDyadicComplexRectangle precision)
    (separation : Fin cells → ChapterVIComplexZeroSeparation) :
    List (DyadicOperation precision) :=
  List.ofFn fun cell ↦ separationOperation (output cell) (separation cell)

/-- Kernel-side interpretation of a proposed finite interval grid. The cover and containment
fields are analytic proofs; `admissible` proves that the emitted integer program lies inside the
verified LeanCompCert fragment. -/
structure Data (A : Type*) (precision cells : ℕ) (f : A → ℂ) where
  region : Fin cells → Set A
  output : Fin cells → ChapterVISignedDyadicComplexRectangle precision
  separation : Fin cells → ChapterVIComplexZeroSeparation
  covers : ∀ x : A, ∃ cell, x ∈ region cell
  contains : ∀ cell, ∀ x ∈ region cell, (output cell).Contains (f x)
  admissible : Admissible (batchClaims (operations output separation))

/-- The sole external observation: the verified compiled checker returned zero failures for
the emitted finite separation batch. -/
structure RunVerdict
    {A : Type*} {precision cells : ℕ} {f : A → ℂ}
    (name : String) (data : Data A precision cells f) : Prop where
  returnsZero :
    (batchComputation name (operations data.output data.separation)).Returns
      ((0 : Nat) : Int)

theorem operation_mem
    {precision cells : ℕ}
    (output : Fin cells → ChapterVISignedDyadicComplexRectangle precision)
    (separation : Fin cells → ChapterVIComplexZeroSeparation)
    (cell : Fin cells) :
    separationOperation (output cell) (separation cell) ∈
      operations output separation := by
  simp [operations]

/-- A successful compiled batch proves continuum nonvanishing after the Lean-checked cell cover
and interval-containment bridges are applied. -/
theorem ne_zero
    {A : Type*} {precision cells : ℕ} {f : A → ℂ}
    {name : String} {data : Data A precision cells f}
    (run : RunVerdict name data) (x : A) : f x ≠ 0 := by
  obtain ⟨cell, hx⟩ := data.covers x
  have hsound := allSound_of_returns_zero name
    (operations data.output data.separation) data.admissible run.returnsZero
    (separationOperation (data.output cell) (data.separation cell))
    (operation_mem data.output data.separation cell)
  exact (data.separation cell).ne_zero_of_lower_pos (data.contains cell x hx) hsound

end ChapterVILeanCompCertNonzeroGrid

end PoincareChapterVI
