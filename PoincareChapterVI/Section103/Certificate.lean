/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# An exact non-invariance certificate for Poincaré's Chapter VI, §103

The final paragraph of §103 argues geometrically that a nontrivial relative motion of two spatial
ellipses cannot preserve the degree-six zero-distance curve. This file records the exact
determinant arising from one rational spatial configuration in the accompanying research audit.

The three columns are infinitesimal rotations of the second ellipse about the coordinate axes.
The rows are the coefficients of `x*y*z^4`, `x*y^2*z^3`, and `x^2*y*z^3` in the corresponding
directional derivatives of Poincaré's polynomial `P`. Their nonzero determinant certifies that no
nonzero infinitesimal relative rotation kills all three coefficients.

This is one component of the §103 argument. A later file must derive this matrix from the actual
ellipse parametrization and combine it with the projective intersection theorem.
-/

noncomputable section

namespace PoincareChapterVI

/-- The three-by-three coefficient minor for infinitesimal relative rotations in the exact
spatial configuration used by `research/chapter_vi_section_103_audit.py`. -/
def chapterVISection103RotationMinor : Matrix (Fin 3) (Fin 3) ℂ :=
  !![(-224 / 325 : ℂ) + 4 / 15 * Complex.I,
      (-1 / 3 : ℂ) - 56 / 65 * Complex.I,
      (746 / 975 : ℂ) + 44 / 195 * Complex.I;
    -8 / 39 * Complex.I,
      (10 / 39 : ℂ),
      (-20 / 39 : ℂ) - 16 / 39 * Complex.I;
    0,
      (2 / 5 : ℂ) + 336 / 325 * Complex.I,
      (-4 / 5 : ℂ) + 24 / 65 * Complex.I]

/-- Exact value of the coefficient-minor determinant. -/
theorem chapterVISection103RotationMinor_det :
    chapterVISection103RotationMinor.det =
      (40256 / 274625 : ℂ) - 151552 / 274625 * Complex.I := by
  apply Complex.ext <;>
    norm_num [Matrix.det_fin_three, chapterVISection103RotationMinor,
      Matrix.cons_val_two, Complex.mul_re, Complex.mul_im]

/-- The infinitesimal relative-rotation certificate is nonsingular. -/
theorem chapterVISection103RotationMinor_det_ne_zero :
    chapterVISection103RotationMinor.det ≠ 0 := by
  rw [chapterVISection103RotationMinor_det]
  intro hzero
  have hreal := congrArg Complex.re hzero
  norm_num at hreal

end PoincareChapterVI
