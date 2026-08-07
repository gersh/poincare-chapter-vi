/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.Section103.Geometry
import PoincareChapterVI.Section103.Ruppert
import LeanCompCert.Verified.Decide
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.NumberTheory.Zsqrtd.GaussianInt

/-!
# A LeanCompCert-backed Ruppert rank certificate

Ruppert's criterion reduces the missing irreducibility step in Poincaré's §103 argument to the
full column rank of a 64-by-35 coefficient matrix.  This file reconstructs that matrix over
`ZMod 29` and checks a right inverse for a 35-by-35 row minor.

The modulus is not an assumption: reduction modulo 29 is a ring homomorphism from the Gaussian
integers after clearing denominators.  A nonzero minor after reduction therefore certifies that
the characteristic-zero minor is nonzero.  The finite equality below is discharged with
LeanCompCert's `verified_decide`, which expands to kernel evaluation rather than
`native_decide`.
-/

noncomputable section

open scoped BigOperators

namespace PoincareChapterVI

private abbrev F29 := ZMod 29

private instance : Fact (Nat.Prime 29) := ⟨by decide⟩

open Zsqrtd

/-- Coefficients of the dehomogenized polynomial `P(x,y,1)`, reduced modulo 29 after a
common denominator has been cleared and the Gaussian unit is sent to `12`, a square root of
`-1` modulo 29.  Rows and columns are the x- and y-degrees, respectively. -/
def chapterVIRuppertFCoefficient : Fin 5 → Fin 5 → F29 :=
  !![0, 0, 23, 0, 0;
     0, 15, 5, 18, 0;
     24, 8, 26, 19, 24;
     0, 10, 13, 8, 0;
     0, 0, 23, 0, 0]

/-- The 64-by-35 Ruppert coefficient matrix over an arbitrary commutative ring. -/
def chapterVIRuppertMatrixOf {R : Type*} [CommRing R]
    (coefficient : Fin 5 → Fin 5 → R) : Matrix (Fin 64) (Fin 35) R := fun row column ↦
  let rx := row.val / 8
  let ry := row.val % 8
  if _hg : column.val < 20 then
    let s := column.val / 5
    let t := column.val % 5
    ∑ a : Fin 5, ∑ b : Fin 5,
      if rx = a.val + s ∧ ry + 1 = b.val + t then
        ((t : R) - (b.val : R)) * coefficient a b
      else 0
  else
    let q := column.val - 20
    let s := q / 3
    let t := q % 3
    ∑ a : Fin 5, ∑ b : Fin 5,
      if rx + 1 = a.val + s ∧ ry = b.val + t then
        ((a.val : R) - (s : R)) * coefficient a b
      else 0

/-- The 64-by-35 coefficient matrix for
`f * ∂y g + h * ∂x f - g * ∂y f - f * ∂x h`.
The first twenty columns encode `g` of bidegree at most `(3,4)`; the last fifteen encode
`h` of bidegree at most `(4,2)`. -/
def chapterVIRuppertMatrix : Matrix (Fin 64) (Fin 35) F29 :=
  chapterVIRuppertMatrixOf chapterVIRuppertFCoefficient

/-- The characteristic-zero Ruppert matrix with all denominators cleared. -/
def chapterVIRuppertGaussianMatrix : Matrix (Fin 64) (Fin 35) GaussianInt :=
  chapterVIRuppertMatrixOf chapterVISection103AffineGaussianCoefficient

/-- Reduction of Gaussian integers modulo 29, sending `i` to `12`; indeed `12² = -1`. -/
def chapterVIGaussianMod29 : GaussianInt →+* F29 :=
  Zsqrtd.lift ⟨12, by decide⟩

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
/-- The exact Gaussian matrix reduces to eight times the rationally normalized matrix.  The
factor eight is `50700 mod 29`. -/
theorem chapterVIRuppertGaussianMatrix_mod29 :
    chapterVIRuppertGaussianMatrix.map chapterVIGaussianMod29 =
      (8 : F29) • chapterVIRuppertMatrix := by
  verified_decide

/-- Rows selected by exact fraction-free row reduction over the Gaussian rationals. -/
def chapterVIRuppertPivotRow : Fin 35 → Fin 64 :=
  ![1, 2, 3, 4, 5, 8, 9, 10, 11, 12, 13, 14, 17, 18, 19, 20, 21,
    24, 25, 26, 27, 28, 29, 30, 32, 33, 34, 35, 36, 37, 38, 40, 41, 42, 43]

/-- The square row minor whose determinant is 24 modulo 29. -/
def chapterVIRuppertMinor : Matrix (Fin 35) (Fin 35) F29 := fun row column ↦
  chapterVIRuppertMatrix (chapterVIRuppertPivotRow row) column

/-- The corresponding characteristic-zero Gaussian-integer minor. -/
def chapterVIRuppertGaussianMinor : Matrix (Fin 35) (Fin 35) GaussianInt := fun row column ↦
  chapterVIRuppertGaussianMatrix (chapterVIRuppertPivotRow row) column

private def chapterVIRuppertInverseData : Array Nat := #[
  22, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  6, 14, 6, 24, 4, 0, 5, 4, 12, 8, 5, 13, 7, 10, 21, 22, 4, 28, 24, 22, 19, 0, 14, 28, 26, 14, 25, 17, 10, 9, 21, 0, 5, 0, 23,
  10, 0, 20, 15, 19, 7, 9, 2, 15, 3, 22, 27, 12, 23, 10, 3, 6, 10, 19, 6, 19, 20, 17, 6, 10, 28, 16, 25, 16, 5, 9, 2, 11, 27, 19,
  2, 0, 18, 13, 25, 15, 8, 1, 27, 3, 21, 15, 1, 2, 6, 12, 21, 28, 21, 10, 5, 17, 15, 23, 25, 7, 26, 4, 4, 21, 1, 26, 26, 0, 23,
  0, 0, 0, 0, 10, 0, 0, 0, 0, 0, 0, 18, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  6, 23, 8, 3, 11, 14, 27, 24, 27, 11, 8, 26, 4, 10, 23, 8, 28, 18, 24, 27, 23, 17, 15, 1, 8, 14, 8, 28, 26, 21, 10, 6, 0, 0, 11,
  20, 2, 1, 24, 10, 10, 9, 14, 21, 0, 20, 3, 23, 22, 19, 0, 3, 7, 7, 20, 7, 12, 24, 2, 5, 21, 17, 25, 10, 13, 21, 22, 26, 5, 19,
  24, 0, 15, 1, 17, 12, 15, 14, 6, 7, 3, 28, 2, 5, 22, 10, 26, 18, 11, 15, 25, 26, 27, 22, 22, 3, 17, 21, 3, 10, 13, 19, 5, 21, 0,
  6, 17, 17, 7, 26, 28, 27, 10, 15, 8, 22, 27, 27, 3, 27, 0, 26, 9, 15, 6, 3, 10, 21, 7, 27, 10, 6, 27, 21, 22, 19, 15, 5, 6, 12,
  8, 6, 21, 26, 6, 11, 19, 5, 2, 18, 4, 27, 25, 19, 6, 21, 1, 11, 5, 2, 6, 12, 14, 28, 21, 15, 21, 1, 3, 8, 19, 23, 0, 0, 18,
  18, 18, 7, 2, 14, 2, 0, 27, 25, 27, 20, 18, 25, 26, 22, 17, 15, 17, 10, 6, 26, 14, 13, 22, 25, 1, 21, 27, 6, 27, 7, 3, 1, 8, 11,
  6, 4, 21, 0, 28, 20, 4, 15, 10, 7, 9, 20, 6, 28, 24, 1, 8, 0, 17, 9, 2, 1, 27, 9, 1, 22, 21, 28, 5, 10, 20, 7, 14, 22, 5,
  3, 16, 12, 13, 19, 18, 28, 21, 4, 19, 23, 26, 8, 7, 19, 0, 19, 5, 13, 13, 10, 1, 16, 7, 7, 12, 28, 23, 19, 12, 23, 26, 7, 28, 12,
  3, 20, 14, 16, 3, 22, 17, 15, 14, 14, 22, 1, 14, 13, 22, 8, 25, 1, 12, 17, 8, 22, 14, 17, 27, 28, 1, 27, 22, 12, 24, 5, 24, 16, 2,
  6, 26, 15, 27, 11, 8, 24, 0, 5, 11, 9, 14, 8, 21, 20, 2, 3, 2, 26, 22, 17, 20, 10, 4, 9, 12, 10, 14, 20, 8, 23, 7, 26, 8, 26,
  0, 25, 8, 28, 22, 5, 12, 24, 22, 11, 4, 21, 24, 19, 1, 10, 26, 17, 1, 9, 20, 22, 6, 23, 20, 8, 17, 0, 1, 5, 16, 27, 15, 0, 17,
  24, 15, 19, 8, 25, 2, 0, 26, 2, 4, 26, 25, 0, 23, 15, 19, 4, 17, 28, 4, 18, 24, 3, 24, 14, 4, 5, 1, 13, 17, 6, 9, 9, 13, 8,
  6, 1, 7, 25, 21, 0, 10, 13, 19, 22, 21, 11, 7, 9, 21, 4, 27, 21, 20, 3, 3, 14, 2, 3, 12, 28, 20, 0, 20, 19, 5, 26, 8, 14, 23,
  24, 2, 14, 6, 16, 22, 16, 15, 22, 14, 23, 9, 4, 6, 19, 10, 20, 21, 10, 26, 1, 6, 17, 3, 13, 6, 28, 26, 8, 24, 13, 19, 22, 22, 17,
  0, 3, 2, 16, 4, 21, 5, 14, 22, 27, 16, 17, 28, 7, 21, 0, 12, 21, 16, 2, 8, 13, 6, 17, 23, 13, 1, 0, 2, 19, 19, 1, 24, 0, 26,
  25, 0, 0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  2, 16, 27, 21, 19, 10, 12, 23, 15, 19, 27, 8, 28, 12, 16, 27, 22, 10, 23, 15, 16, 3, 18, 7, 27, 11, 27, 22, 8, 2, 12, 13, 0, 0, 19,
  0, 0, 0, 0, 18, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  2, 9, 28, 25, 21, 26, 23, 11, 23, 17, 0, 25, 10, 18, 26, 12, 28, 5, 20, 13, 28, 7, 28, 27, 8, 2, 9, 15, 28, 15, 7, 11, 24, 0, 2,
  20, 6, 26, 26, 2, 9, 19, 5, 2, 18, 21, 2, 25, 19, 6, 21, 1, 11, 5, 2, 6, 12, 14, 28, 21, 15, 21, 1, 3, 8, 19, 23, 0, 0, 18,
  25, 10, 24, 13, 11, 14, 1, 19, 11, 4, 27, 10, 4, 24, 16, 18, 13, 27, 10, 23, 15, 8, 19, 2, 2, 3, 3, 25, 9, 15, 23, 16, 26, 0, 24,
  26, 27, 28, 2, 23, 13, 9, 22, 21, 25, 18, 13, 14, 4, 21, 25, 2, 21, 27, 20, 27, 23, 9, 18, 13, 23, 16, 21, 12, 27, 0, 3, 14, 0, 9,
  17, 21, 1, 21, 22, 25, 1, 21, 22, 26, 5, 4, 18, 2, 27, 6, 14, 19, 2, 5, 9, 17, 28, 1, 0, 1, 9, 23, 24, 19, 23, 14, 8, 0, 21,
  22, 11, 18, 0, 27, 25, 5, 0, 22, 10, 15, 2, 27, 2, 14, 1, 4, 10, 10, 28, 28, 16, 9, 17, 22, 2, 8, 28, 22, 1, 16, 2, 13, 0, 1,
  12, 3, 20, 12, 5, 14, 7, 10, 25, 24, 11, 13, 10, 19, 27, 22, 21, 4, 26, 1, 22, 19, 3, 5, 7, 6, 23, 17, 0, 0, 18, 12, 20, 0, 26,
  26, 27, 3, 18, 26, 27, 10, 26, 25, 19, 2, 22, 23, 4, 4, 15, 19, 13, 21, 3, 26, 13, 3, 1, 13, 15, 13, 12, 23, 15, 25, 21, 10, 0, 6,
  2, 0, 10, 20, 24, 11, 0, 2, 18, 27, 19, 27, 12, 14, 14, 3, 0, 20, 15, 5, 5, 10, 20, 1, 8, 18, 5, 11, 6, 4, 22, 15, 17, 0, 3,
  1, 2, 20, 11, 18, 7, 27, 7, 3, 3, 13, 27, 21, 15, 10, 20, 3, 13, 19, 21, 22, 3, 28, 6, 19, 21, 11, 13, 22, 25, 17, 6, 3, 0, 17,
  24, 20, 8, 10, 25, 14, 2, 28, 20, 25, 18, 5, 11, 25, 8, 24, 10, 2, 18, 26, 14, 10, 1, 20, 22, 2, 26, 11, 10, 14, 23, 20, 21, 0, 9,
  13, 20, 11, 2, 21, 0, 25, 2, 5, 14, 13, 12, 2, 3, 26, 5, 12, 5, 17, 19, 0, 25, 22, 9, 19, 15, 15, 18, 8, 26, 14, 23, 11, 0, 13
]

/-- An inverse certificate for `chapterVIRuppertMinor`, stored in row-major order. -/
def chapterVIRuppertInverse : Matrix (Fin 35) (Fin 35) F29 := fun row column ↦
  chapterVIRuppertInverseData[row.val * 35 + column.val]!

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
/-- The finite certificate: all 1,225 entries of the matrix product are checked in the kernel. -/
theorem chapterVIRuppertInverse_mul_minor :
    chapterVIRuppertInverse * chapterVIRuppertMinor = 1 := by
  verified_decide

/-- The finite-field minor has nonzero determinant. -/
theorem chapterVIRuppertMinor_det_ne_zero : chapterVIRuppertMinor.det ≠ 0 := by
  intro hzero
  have hdet := congrArg Matrix.det chapterVIRuppertInverse_mul_minor
  rw [Matrix.det_mul, Matrix.det_one, hzero, mul_zero] at hdet
  exact zero_ne_one hdet

/-- Restricting the reduction theorem to the selected rows gives the reduction of the minor. -/
theorem chapterVIRuppertGaussianMinor_mod29 :
    chapterVIGaussianMod29.mapMatrix chapterVIRuppertGaussianMinor =
      (8 : F29) • chapterVIRuppertMinor := by
  ext row column
  exact congrArg (fun matrix ↦ matrix (chapterVIRuppertPivotRow row) column)
    chapterVIRuppertGaussianMatrix_mod29

/-- The exact characteristic-zero minor is nonzero.  If its determinant vanished, its image
modulo 29 would vanish, contradicting the checked finite-field inverse. -/
theorem chapterVIRuppertGaussianMinor_det_ne_zero :
    chapterVIRuppertGaussianMinor.det ≠ 0 := by
  intro hzero
  have hmap := chapterVIGaussianMod29.map_det chapterVIRuppertGaussianMinor
  rw [hzero, map_zero, chapterVIRuppertGaussianMinor_mod29, Matrix.det_smul] at hmap
  have hproduct : (8 : F29) ^ 35 * chapterVIRuppertMinor.det = 0 := hmap.symm
  exact chapterVIRuppertMinor_det_ne_zero
    ((mul_eq_zero.mp hproduct).resolve_left (pow_ne_zero _ (by decide)))

/-- The cleared characteristic-zero Ruppert matrix, embedded in the complex numbers. -/
def chapterVIComplexRuppertMatrix : Matrix (Fin 64) (Fin 35) ℂ :=
  chapterVIRuppertGaussianMatrix.map GaussianInt.toComplex

/-- Its selected square row minor. -/
def chapterVIComplexRuppertMinor : Matrix (Fin 35) (Fin 35) ℂ :=
  GaussianInt.toComplex.mapMatrix chapterVIRuppertGaussianMinor

/-- The complex minor has nonzero determinant. -/
theorem chapterVIComplexRuppertMinor_det_ne_zero :
    chapterVIComplexRuppertMinor.det ≠ 0 := by
  intro hzero
  have hmap := GaussianInt.toComplex.map_det chapterVIRuppertGaussianMinor
  change GaussianInt.toComplex chapterVIRuppertGaussianMinor.det =
    chapterVIComplexRuppertMinor.det at hmap
  rw [hzero] at hmap
  exact chapterVIRuppertGaussianMinor_det_ne_zero
    (GaussianInt.toComplex_eq_zero.mp hmap)

/-- Consequently all 35 Ruppert columns are linearly independent over `ℂ`. -/
theorem chapterVIComplexRuppertMatrix_mulVec_eq_zero
    (v : Fin 35 → ℂ) (h : chapterVIComplexRuppertMatrix.mulVec v = 0) : v = 0 := by
  apply Matrix.eq_zero_of_mulVec_eq_zero chapterVIComplexRuppertMinor_det_ne_zero
  funext row
  exact congrFun h (chapterVIRuppertPivotRow row)

/-- Hence the selected Ruppert minor, and therefore the full 64-by-35 matrix, has trivial
right kernel over `ZMod 29`. -/
theorem chapterVIRuppertMinor_mulVec_eq_zero
    (v : Fin 35 → F29) (h : chapterVIRuppertMinor.mulVec v = 0) : v = 0 := by
  have hleft := congrArg (fun matrix ↦ matrix.mulVec v)
    chapterVIRuppertInverse_mul_minor
  rw [← Matrix.mulVec_mulVec] at hleft
  simp only [Matrix.one_mulVec] at hleft
  rw [h] at hleft
  simpa using hleft.symm

end PoincareChapterVI
