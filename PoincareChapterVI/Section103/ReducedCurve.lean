/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.Section103.ProjectiveIrreducibility

/-!
# The degree-seven reduced curve in Poincaré's Chapter VI, §103

For the exact pair of Kepler ellipses fixed in `Geometry`, Poincaré's reduced derivative equation
is a homogeneous curve `R = 0` of degree seven.  This file records its cleared Gaussian-integer
coefficient table and proves the first hypothesis needed for the source's `6 · 7` Bézout count:
the irreducible sextic `P` and `R` have no common component.

The table is `438750 · R` for the choices `τ = 1/3`, `τ' = 1/5`, and lattice coefficients
`a = -2`, `c = 3` used by the exact research audit.  A later local-intersection module will connect
the two order-eight resultants at infinity and the order-two affine-origin contribution to an
appropriate projective Bézout theorem.
-/

noncomputable section

open scoped BigOperators

namespace PoincareChapterVI

private abbrev Trivar := MvPolynomial (Fin 3) ℂ
private abbrev YZBivar := MvPolynomial (Fin 2) ℂ

/-- Exact Gaussian coefficients of `438750 · R`.  Row and column are the exponents of `x` and
`y`; the exponent of `z` is `7 - xDegree - yDegree`. -/
def chapterVISection103ReducedGaussianCoefficient : Fin 5 → Fin 5 → GaussianInt :=
  !![⟨0, 0⟩, ⟨90285, -99840⟩, ⟨-136890, 0⟩, ⟨-112515, 62400⟩, ⟨0, 0⟩;
     ⟨106500, -96000⟩, ⟨-1051430, 914464⟩, ⟨1041300, -468000⟩,
       ⟨-38470, 186464⟩, ⟨88500, -60000⟩;
     ⟨-150000, 0⟩, ⟨1388400, -112320⟩, ⟨0, 0⟩,
       ⟨-1388400, -112320⟩, ⟨150000, 0⟩;
     ⟨-88500, -60000⟩, ⟨38470, 186464⟩, ⟨-1041300, -468000⟩,
       ⟨1051430, 914464⟩, ⟨-106500, -96000⟩;
     ⟨0, 0⟩, ⟨112515, 62400⟩, ⟨136890, 0⟩, ⟨-90285, -99840⟩, ⟨0, 0⟩]

def chapterVIReducedProjectiveMonomial (a b : ℕ) : Fin 3 →₀ ℕ :=
  Finsupp.single 0 a + Finsupp.single 1 b + Finsupp.single 2 (7 - a - b)

/-- The exact cleared degree-seven curve paired with
`chapterVISection103ProjectivePolynomial`. -/
def chapterVISection103ReducedProjectivePolynomial : Trivar :=
  ∑ a : Fin 5, ∑ b : Fin 5,
    MvPolynomial.monomial (chapterVIReducedProjectiveMonomial a.val b.val)
      (chapterVISection103ReducedGaussianCoefficient a b : ℂ)

private theorem chapterVI_reducedProjectiveMonomial_degree
    (a b : ℕ) (hab : a + b ≤ 7) :
    (chapterVIReducedProjectiveMonomial a b).degree = 7 := by
  rw [Finsupp.degree_eq_sum]
  simp [chapterVIReducedProjectiveMonomial, Fin.sum_univ_succ]
  omega

theorem chapterVI_section103ReducedProjectivePolynomial_isHomogeneous :
    chapterVISection103ReducedProjectivePolynomial.IsHomogeneous 7 := by
  unfold chapterVISection103ReducedProjectivePolynomial
  apply MvPolynomial.IsHomogeneous.sum
  intro a ha
  apply MvPolynomial.IsHomogeneous.sum
  intro b hb
  by_cases hcoeff : chapterVISection103ReducedGaussianCoefficient a b = 0
  · simp [hcoeff, MvPolynomial.isHomogeneous_zero]
  · apply MvPolynomial.isHomogeneous_monomial
    apply chapterVI_reducedProjectiveMonomial_degree
    by_contra hab
    fin_cases a <;> fin_cases b <;>
      norm_num [chapterVISection103ReducedGaussianCoefficient] at hab
    all_goals exact hcoeff rfl

/-- Restriction to the projective line `x = 0`, with coordinates `(y,z)`. -/
def chapterVISetXZero : Trivar →+* YZBivar :=
  MvPolynomial.eval₂Hom MvPolynomial.C ![0, MvPolynomial.X 0, MvPolynomial.X 1]

private def chapterVIYZMonomial (yDegree zDegree : ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 yDegree + Finsupp.single 1 zDegree

private theorem chapterVI_YZMonomial_inj {a b c d : ℕ} :
    chapterVIYZMonomial a b = chapterVIYZMonomial c d ↔ a = c ∧ b = d := by
  constructor
  · intro h
    exact ⟨by simpa [chapterVIYZMonomial] using congrArg (fun e ↦ e 0) h,
      by simpa [chapterVIYZMonomial] using congrArg (fun e ↦ e 1) h⟩
  · rintro ⟨rfl, rfl⟩
    rfl

private def chapterVIProjectYZ (d : Fin 3 →₀ ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 (d 1) + Finsupp.single 1 (d 2)

private theorem chapterVI_setXZero_monomial (d : Fin 3 →₀ ℕ) (c : ℂ) :
    chapterVISetXZero (MvPolynomial.monomial d c) =
      if d 0 = 0 then MvPolynomial.monomial (chapterVIProjectYZ d) c else 0 := by
  by_cases hd : d 0 = 0
  · simp [chapterVISetXZero, chapterVIProjectYZ, MvPolynomial.monomial_eq,
      Finsupp.prod_fintype, Fin.prod_univ_succ, Matrix.cons_val_two, hd]
  · simp [chapterVISetXZero, MvPolynomial.monomial_eq,
      Finsupp.prod_fintype, Fin.prod_univ_succ, Matrix.cons_val_two, hd]

private theorem chapterVI_projectYZ_projectiveMonomial (a b : ℕ) :
    chapterVIProjectYZ (chapterVIProjectiveMonomial a b) =
      chapterVIYZMonomial b (6 - a - b) := by
  ext i
  fin_cases i <;>
    simp [chapterVIProjectYZ, chapterVIProjectiveMonomial, chapterVIYZMonomial]

private theorem chapterVI_projectiveMonomial_apply_zero (a b : ℕ) :
    chapterVIProjectiveMonomial a b 0 = a := by
  simp [chapterVIProjectiveMonomial]

private theorem chapterVI_projectYZ_reducedProjectiveMonomial (a b : ℕ) :
    chapterVIProjectYZ (chapterVIReducedProjectiveMonomial a b) =
      chapterVIYZMonomial b (7 - a - b) := by
  ext i
  fin_cases i <;>
    simp [chapterVIProjectYZ, chapterVIReducedProjectiveMonomial, chapterVIYZMonomial]

private theorem chapterVI_reducedProjectiveMonomial_apply_zero (a b : ℕ) :
    chapterVIReducedProjectiveMonomial a b 0 = a := by
  simp [chapterVIReducedProjectiveMonomial]

theorem chapterVI_setXZero_section103ProjectivePolynomial :
    chapterVISetXZero chapterVISection103ProjectivePolynomial =
      MvPolynomial.monomial (chapterVIYZMonomial 2 4) 4563 := by
  simp [chapterVISection103ProjectivePolynomial, chapterVI_setXZero_monomial,
    chapterVI_projectiveMonomial_apply_zero, chapterVI_projectYZ_projectiveMonomial,
    chapterVISection103AffineGaussianCoefficient, GaussianInt.toComplex_def,
    Fin.sum_univ_succ]

theorem chapterVI_setXZero_reducedCoefficient_16_ne_zero :
    MvPolynomial.coeff (chapterVIYZMonomial 1 6)
      (chapterVISetXZero chapterVISection103ReducedProjectivePolynomial) ≠ 0 := by
  simp [chapterVISection103ReducedProjectivePolynomial,
    chapterVI_setXZero_monomial, chapterVI_reducedProjectiveMonomial_apply_zero,
    chapterVI_projectYZ_reducedProjectiveMonomial,
    chapterVISection103ReducedGaussianCoefficient, GaussianInt.toComplex_def,
    MvPolynomial.coeff_monomial,
    chapterVI_YZMonomial_inj, Fin.sum_univ_succ]
  norm_num [Complex.ext_iff]

theorem chapterVI_section103ProjectivePolynomial_not_dvd_reduced :
    ¬ chapterVISection103ProjectivePolynomial ∣
      chapterVISection103ReducedProjectivePolynomial := by
  intro hdvd
  obtain ⟨q, hq⟩ := hdvd
  have himage := congrArg chapterVISetXZero hq
  have hcoefficient := congrArg
    (MvPolynomial.coeff (chapterVIYZMonomial 1 6)) himage
  rw [map_mul, chapterVI_setXZero_section103ProjectivePolynomial] at hcoefficient
  rw [MvPolynomial.coeff_monomial_mul'] at hcoefficient
  have hnotle : ¬ chapterVIYZMonomial 2 4 ≤ chapterVIYZMonomial 1 6 := by
    intro hle
    have := Finsupp.le_def.mp hle 0
    simp [chapterVIYZMonomial] at this
  simp [hnotle] at hcoefficient
  exact chapterVI_setXZero_reducedCoefficient_16_ne_zero hcoefficient

/-- The exact sextic and reduced septic have no common component. -/
theorem chapterVI_section103Projective_reduced_isRelPrime :
    IsRelPrime chapterVISection103ProjectivePolynomial
      chapterVISection103ReducedProjectivePolynomial := by
  rw [chapterVI_section103ProjectivePolynomial_irreducible.isRelPrime_iff_not_dvd]
  exact chapterVI_section103ProjectivePolynomial_not_dvd_reduced

end PoincareChapterVI
