/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.Section103.ReducedCurveSource
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Local intersection data for Poincaré's Chapter VI, §103

This file begins the kernel-checked reconstruction of the three exceptional local contributions
in Poincaré's intersection count.  At the affine origin it identifies the quadratic tangent cone
of the sextic and the tangent line of the reduced septic directly from the dehomogenized source
curves.  It then proves that the tangent line is not a component of the tangent cone—the precise
transversality input behind the claimed local contribution `2`.

The general theorem turning these initial forms into a local intersection multiplicity is still
separate; no intersection number is asserted here without that theorem.
-/

noncomputable section

open scoped BigOperators

namespace PoincareChapterVI

private abbrev Bivar := MvPolynomial (Fin 2) ℂ

private def chapterVIOriginMonomial (a b : ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 a + Finsupp.single 1 b

private theorem chapterVI_originMonomial_inj {a b c d : ℕ} :
    chapterVIOriginMonomial a b = chapterVIOriginMonomial c d ↔
      a = c ∧ b = d := by
  constructor
  · intro h
    exact ⟨by simpa [chapterVIOriginMonomial] using congrArg (fun e ↦ e 0) h,
      by simpa [chapterVIOriginMonomial] using congrArg (fun e ↦ e 1) h⟩
  · rintro ⟨rfl, rfl⟩
    rfl

private theorem chapterVI_originMonomial_degree (a b : ℕ) :
    (chapterVIOriginMonomial a b).degree = a + b := by
  rw [Finsupp.degree_eq_sum]
  simp [chapterVIOriginMonomial, Fin.sum_univ_succ]

private theorem chapterVI_homogeneousComponent_originMonomial (n a b : ℕ) (c : ℂ) :
    MvPolynomial.homogeneousComponent n
        (MvPolynomial.monomial (chapterVIOriginMonomial a b) c) =
      if n = a + b then MvPolynomial.monomial (chapterVIOriginMonomial a b) c else 0 := by
  apply MvPolynomial.homogeneousComponent_of_mem
  exact MvPolynomial.isHomogeneous_monomial c (chapterVI_originMonomial_degree a b)

/-- The cleared reduced septic in the affine chart `z = 1`. -/
def chapterVISection103ReducedAffinePolynomial : Bivar :=
  ∑ a : Fin 5, ∑ b : Fin 5,
    MvPolynomial.monomial (chapterVIOriginMonomial a.val b.val)
      (chapterVISection103ReducedGaussianCoefficient a b : ℂ)

private theorem chapterVI_dehomogenize_reducedTerm (a b : ℕ) (c : ℂ) :
    chapterVIDehomogenizeZ
        (MvPolynomial.monomial (chapterVIReducedProjectiveMonomial a b) c) =
      MvPolynomial.monomial (chapterVIOriginMonomial a b) c := by
  simp [chapterVIDehomogenizeZ, chapterVIReducedProjectiveMonomial,
    chapterVIOriginMonomial,
    MvPolynomial.monomial_eq, Finsupp.prod_fintype, Fin.prod_univ_succ]

/-- Dehomogenizing the projective septic at `z = 1` gives its affine presentation. -/
theorem chapterVI_dehomogenize_section103ReducedProjectivePolynomial :
    chapterVIDehomogenizeZ chapterVISection103ReducedProjectivePolynomial =
      chapterVISection103ReducedAffinePolynomial := by
  simp [chapterVISection103ReducedProjectivePolynomial,
    chapterVISection103ReducedAffinePolynomial, map_sum,
    chapterVI_dehomogenize_reducedTerm]

/-- The quadratic tangent cone of the cleared sextic at the affine origin. -/
def chapterVISection103OriginSexticTangentCone : Bivar :=
  MvPolynomial.monomial (chapterVIOriginMonomial 2 0) 7500 +
    MvPolynomial.monomial (chapterVIOriginMonomial 1 1)
      (21320 - 33280 * Complex.I) +
    MvPolynomial.monomial (chapterVIOriginMonomial 0 2) 4563

/-- The tangent line of the cleared reduced septic at the affine origin. -/
def chapterVISection103OriginReducedTangentLine : Bivar :=
  MvPolynomial.monomial (chapterVIOriginMonomial 1 0)
      (106500 - 96000 * Complex.I) +
    MvPolynomial.monomial (chapterVIOriginMonomial 0 1)
      (90285 - 99840 * Complex.I)

/-- The degree-two initial form of the affine sextic is the displayed tangent cone. -/
theorem chapterVI_section103AffinePolynomial_homogeneousComponent_two :
    MvPolynomial.homogeneousComponent 2 chapterVISection103AffinePolynomial =
      chapterVISection103OriginSexticTangentCone := by
  change MvPolynomial.homogeneousComponent 2
    (∑ a : Fin 5, ∑ b : Fin 5,
      MvPolynomial.monomial (chapterVIOriginMonomial a.val b.val)
        (chapterVISection103AffineGaussianCoefficient a b : ℂ)) =
    chapterVISection103OriginSexticTangentCone
  simp [chapterVI_homogeneousComponent_originMonomial,
    chapterVISection103AffineGaussianCoefficient, GaussianInt.toComplex_def,
    chapterVISection103OriginSexticTangentCone, Fin.sum_univ_succ]
  ring

/-- The degree-one initial form of the affine septic is the displayed tangent line. -/
theorem chapterVI_section103ReducedAffinePolynomial_homogeneousComponent_one :
    MvPolynomial.homogeneousComponent 1 chapterVISection103ReducedAffinePolynomial =
      chapterVISection103OriginReducedTangentLine := by
  simp [chapterVISection103ReducedAffinePolynomial,
    chapterVI_homogeneousComponent_originMonomial,
    chapterVISection103ReducedGaussianCoefficient, GaussianInt.toComplex_def,
    chapterVISection103OriginReducedTangentLine, Fin.sum_univ_succ]
  ring

private def chapterVIOriginReducedXCoefficient : ℂ := 106500 - 96000 * Complex.I
private def chapterVIOriginReducedYCoefficient : ℂ := 90285 - 99840 * Complex.I

private def chapterVIOriginTangentDirectionEval : Bivar →+* ℂ :=
  MvPolynomial.eval
    ![chapterVIOriginReducedYCoefficient, -chapterVIOriginReducedXCoefficient]

/-- The displayed direction lies on the septic's tangent line. -/
theorem chapterVI_originTangentDirectionEval_reducedTangentLine :
    chapterVIOriginTangentDirectionEval chapterVISection103OriginReducedTangentLine = 0 := by
  simp [chapterVIOriginTangentDirectionEval,
    chapterVISection103OriginReducedTangentLine,
    chapterVIOriginReducedXCoefficient, chapterVIOriginReducedYCoefficient,
    chapterVIOriginMonomial, MvPolynomial.eval_monomial,
    Finsupp.prod_fintype, Fin.prod_univ_succ]
  ring

/-- The same direction does not lie on the sextic's quadratic tangent cone. -/
theorem chapterVI_originTangentDirectionEval_sexticTangentCone_ne_zero :
    chapterVIOriginTangentDirectionEval chapterVISection103OriginSexticTangentCone ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  norm_num [chapterVIOriginTangentDirectionEval,
    chapterVISection103OriginSexticTangentCone,
    chapterVIOriginReducedXCoefficient, chapterVIOriginReducedYCoefficient,
    chapterVIOriginMonomial, MvPolynomial.eval_monomial,
    Finsupp.prod_fintype, Fin.prod_univ_succ, pow_two,
    Complex.mul_re, Complex.mul_im] at hre

/-- The septic tangent line is not a component of the sextic tangent cone. -/
theorem chapterVI_section103OriginReducedTangentLine_not_dvd_sexticTangentCone :
    ¬ chapterVISection103OriginReducedTangentLine ∣
      chapterVISection103OriginSexticTangentCone := by
  intro h
  obtain ⟨q, hq⟩ := h
  have he := congrArg chapterVIOriginTangentDirectionEval hq
  rw [map_mul] at he
  rw [chapterVI_originTangentDirectionEval_reducedTangentLine] at he
  simp only [zero_mul] at he
  exact chapterVI_originTangentDirectionEval_sexticTangentCone_ne_zero he

/-- `p` has no terms below degree `n`, and its degree-`n` homogeneous component is nonzero. -/
def HasInitialDegree (p : MvPolynomial σ ℂ) (n : ℕ) : Prop :=
  MvPolynomial.homogeneousComponent n p ≠ 0 ∧
    ∀ m < n, MvPolynomial.homogeneousComponent m p = 0

private theorem chapterVI_section103AffinePolynomial_homogeneousComponent_zero :
    MvPolynomial.homogeneousComponent 0 chapterVISection103AffinePolynomial = 0 := by
  change MvPolynomial.homogeneousComponent 0
    (∑ a : Fin 5, ∑ b : Fin 5,
      MvPolynomial.monomial (chapterVIOriginMonomial a.val b.val)
        (chapterVISection103AffineGaussianCoefficient a b : ℂ)) = 0
  simp only [map_sum, chapterVI_homogeneousComponent_originMonomial]
  simp [chapterVISection103AffineGaussianCoefficient, GaussianInt.toComplex_def,
    Fin.sum_univ_succ]

private theorem chapterVI_section103AffinePolynomial_homogeneousComponent_one :
    MvPolynomial.homogeneousComponent 1 chapterVISection103AffinePolynomial = 0 := by
  change MvPolynomial.homogeneousComponent 1
    (∑ a : Fin 5, ∑ b : Fin 5,
      MvPolynomial.monomial (chapterVIOriginMonomial a.val b.val)
        (chapterVISection103AffineGaussianCoefficient a b : ℂ)) = 0
  simp [chapterVI_homogeneousComponent_originMonomial,
    chapterVISection103AffineGaussianCoefficient, GaussianInt.toComplex_def,
    Fin.sum_univ_succ]

private theorem chapterVI_section103ReducedAffinePolynomial_homogeneousComponent_zero :
    MvPolynomial.homogeneousComponent 0 chapterVISection103ReducedAffinePolynomial = 0 := by
  unfold chapterVISection103ReducedAffinePolynomial
  simp only [map_sum, chapterVI_homogeneousComponent_originMonomial]
  simp [chapterVISection103ReducedGaussianCoefficient, GaussianInt.toComplex_def,
    Fin.sum_univ_succ]

/-- The cleared affine sextic has initial degree exactly two at the origin. -/
theorem chapterVI_section103AffinePolynomial_hasInitialDegree_two :
    HasInitialDegree chapterVISection103AffinePolynomial 2 := by
  constructor
  · rw [chapterVI_section103AffinePolynomial_homogeneousComponent_two]
    intro hzero
    apply chapterVI_originTangentDirectionEval_sexticTangentCone_ne_zero
    rw [hzero, map_zero]
  · intro m hm
    interval_cases m
    · exact chapterVI_section103AffinePolynomial_homogeneousComponent_zero
    · exact chapterVI_section103AffinePolynomial_homogeneousComponent_one

/-- The cleared affine reduced septic is smooth at the origin: its initial degree is one. -/
theorem chapterVI_section103ReducedAffinePolynomial_hasInitialDegree_one :
    HasInitialDegree chapterVISection103ReducedAffinePolynomial 1 := by
  constructor
  · rw [chapterVI_section103ReducedAffinePolynomial_homogeneousComponent_one]
    intro hzero
    have hcoefficient := congrArg
      (MvPolynomial.coeff (chapterVIOriginMonomial 1 0)) hzero
    norm_num [chapterVISection103OriginReducedTangentLine,
      MvPolynomial.coeff_add, MvPolynomial.coeff_monomial,
      chapterVI_originMonomial_inj, Complex.ext_iff] at hcoefficient
  · intro m hm
    interval_cases m
    exact chapterVI_section103ReducedAffinePolynomial_homogeneousComponent_zero

/-- Affine chart centered at the projective point `(1 : 0 : 0)`, with local coordinates
`(y,z)`. -/
def chapterVISetXOne : MvPolynomial (Fin 3) ℂ →+* Bivar :=
  MvPolynomial.eval₂Hom MvPolynomial.C ![1, MvPolynomial.X 0, MvPolynomial.X 1]

/-- Affine chart centered at the projective point `(0 : 1 : 0)`, with local coordinates
`(x,z)`. -/
def chapterVISetYOne : MvPolynomial (Fin 3) ℂ →+* Bivar :=
  MvPolynomial.eval₂Hom MvPolynomial.C ![MvPolynomial.X 0, 1, MvPolynomial.X 1]

/-- The cleared sextic in the `(1 : 0 : 0)` chart. -/
def chapterVISection103XInfinitySextic : Bivar :=
  ∑ a : Fin 5, ∑ b : Fin 5,
    MvPolynomial.monomial
      (chapterVIOriginMonomial b.val (6 - a.val - b.val))
      (chapterVISection103AffineGaussianCoefficient a b : ℂ)

/-- The cleared septic in the `(1 : 0 : 0)` chart. -/
def chapterVISection103XInfinityReduced : Bivar :=
  ∑ a : Fin 5, ∑ b : Fin 5,
    MvPolynomial.monomial
      (chapterVIOriginMonomial b.val (7 - a.val - b.val))
      (chapterVISection103ReducedGaussianCoefficient a b : ℂ)

/-- The cleared sextic in the `(0 : 1 : 0)` chart. -/
def chapterVISection103YInfinitySextic : Bivar :=
  ∑ a : Fin 5, ∑ b : Fin 5,
    MvPolynomial.monomial
      (chapterVIOriginMonomial a.val (6 - a.val - b.val))
      (chapterVISection103AffineGaussianCoefficient a b : ℂ)

/-- The cleared septic in the `(0 : 1 : 0)` chart. -/
def chapterVISection103YInfinityReduced : Bivar :=
  ∑ a : Fin 5, ∑ b : Fin 5,
    MvPolynomial.monomial
      (chapterVIOriginMonomial a.val (7 - a.val - b.val))
      (chapterVISection103ReducedGaussianCoefficient a b : ℂ)

private theorem chapterVI_setXOne_projectiveTerm (a b : ℕ) (c : ℂ) :
    chapterVISetXOne (MvPolynomial.monomial (chapterVIProjectiveMonomial a b) c) =
      MvPolynomial.monomial (chapterVIOriginMonomial b (6 - a - b)) c := by
  simp [chapterVISetXOne, chapterVIProjectiveMonomial, chapterVIOriginMonomial,
    MvPolynomial.monomial_eq, Finsupp.prod_fintype, Fin.prod_univ_succ]

private theorem chapterVI_setXOne_reducedTerm (a b : ℕ) (c : ℂ) :
    chapterVISetXOne
        (MvPolynomial.monomial (chapterVIReducedProjectiveMonomial a b) c) =
      MvPolynomial.monomial (chapterVIOriginMonomial b (7 - a - b)) c := by
  simp [chapterVISetXOne, chapterVIReducedProjectiveMonomial,
    chapterVIOriginMonomial, MvPolynomial.monomial_eq, Finsupp.prod_fintype,
    Fin.prod_univ_succ]

private theorem chapterVI_setYOne_projectiveTerm (a b : ℕ) (c : ℂ) :
    chapterVISetYOne (MvPolynomial.monomial (chapterVIProjectiveMonomial a b) c) =
      MvPolynomial.monomial (chapterVIOriginMonomial a (6 - a - b)) c := by
  simp [chapterVISetYOne, chapterVIProjectiveMonomial, chapterVIOriginMonomial,
    MvPolynomial.monomial_eq, Finsupp.prod_fintype, Fin.prod_univ_succ]

private theorem chapterVI_setYOne_reducedTerm (a b : ℕ) (c : ℂ) :
    chapterVISetYOne
        (MvPolynomial.monomial (chapterVIReducedProjectiveMonomial a b) c) =
      MvPolynomial.monomial (chapterVIOriginMonomial a (7 - a - b)) c := by
  simp [chapterVISetYOne, chapterVIReducedProjectiveMonomial,
    chapterVIOriginMonomial, MvPolynomial.monomial_eq, Finsupp.prod_fintype,
    Fin.prod_univ_succ]

theorem chapterVI_setXOne_section103ProjectivePolynomial :
    chapterVISetXOne chapterVISection103ProjectivePolynomial =
      chapterVISection103XInfinitySextic := by
  simp [chapterVISection103ProjectivePolynomial,
    chapterVISection103XInfinitySextic, map_sum, chapterVI_setXOne_projectiveTerm]

theorem chapterVI_setXOne_section103ReducedProjectivePolynomial :
    chapterVISetXOne chapterVISection103ReducedProjectivePolynomial =
      chapterVISection103XInfinityReduced := by
  simp [chapterVISection103ReducedProjectivePolynomial,
    chapterVISection103XInfinityReduced, map_sum, chapterVI_setXOne_reducedTerm]

theorem chapterVI_setYOne_section103ProjectivePolynomial :
    chapterVISetYOne chapterVISection103ProjectivePolynomial =
      chapterVISection103YInfinitySextic := by
  simp [chapterVISection103ProjectivePolynomial,
    chapterVISection103YInfinitySextic, map_sum, chapterVI_setYOne_projectiveTerm]

theorem chapterVI_setYOne_section103ReducedProjectivePolynomial :
    chapterVISetYOne chapterVISection103ReducedProjectivePolynomial =
      chapterVISection103YInfinityReduced := by
  simp [chapterVISection103ReducedProjectivePolynomial,
    chapterVISection103YInfinityReduced, map_sum, chapterVI_setYOne_reducedTerm]

/-- Lowest form of the sextic at `(1 : 0 : 0)`. -/
def chapterVISection103XInfinitySexticInitial : Bivar :=
  MvPolynomial.monomial (chapterVIOriginMonomial 2 0) 4563

/-- Lowest form of the septic at `(1 : 0 : 0)`. -/
def chapterVISection103XInfinityReducedInitial : Bivar :=
  MvPolynomial.monomial (chapterVIOriginMonomial 1 2) (112515 + 62400 * Complex.I) +
    MvPolynomial.monomial (chapterVIOriginMonomial 2 1) 136890 +
    MvPolynomial.monomial (chapterVIOriginMonomial 3 0) (-90285 - 99840 * Complex.I)

/-- Lowest form of the sextic at `(0 : 1 : 0)`. -/
def chapterVISection103YInfinitySexticInitial : Bivar :=
  MvPolynomial.monomial (chapterVIOriginMonomial 2 0) 7500

/-- Lowest form of the septic at `(0 : 1 : 0)`. -/
def chapterVISection103YInfinityReducedInitial : Bivar :=
  MvPolynomial.monomial (chapterVIOriginMonomial 1 2) (88500 - 60000 * Complex.I) +
    MvPolynomial.monomial (chapterVIOriginMonomial 2 1) 150000 +
    MvPolynomial.monomial (chapterVIOriginMonomial 3 0) (-106500 - 96000 * Complex.I)

theorem chapterVI_section103XInfinitySextic_homogeneousComponent_two :
    MvPolynomial.homogeneousComponent 2 chapterVISection103XInfinitySextic =
      chapterVISection103XInfinitySexticInitial := by
  simp [chapterVISection103XInfinitySextic,
    chapterVI_homogeneousComponent_originMonomial,
    chapterVISection103AffineGaussianCoefficient, GaussianInt.toComplex_def,
    chapterVISection103XInfinitySexticInitial, Fin.sum_univ_succ]

theorem chapterVI_section103XInfinityReduced_homogeneousComponent_three :
    MvPolynomial.homogeneousComponent 3 chapterVISection103XInfinityReduced =
      chapterVISection103XInfinityReducedInitial := by
  simp [chapterVISection103XInfinityReduced,
    chapterVI_homogeneousComponent_originMonomial,
    chapterVISection103ReducedGaussianCoefficient, GaussianInt.toComplex_def,
    chapterVISection103XInfinityReducedInitial, Fin.sum_univ_succ]
  ring

theorem chapterVI_section103YInfinitySextic_homogeneousComponent_two :
    MvPolynomial.homogeneousComponent 2 chapterVISection103YInfinitySextic =
      chapterVISection103YInfinitySexticInitial := by
  simp [chapterVISection103YInfinitySextic,
    chapterVI_homogeneousComponent_originMonomial,
    chapterVISection103AffineGaussianCoefficient, GaussianInt.toComplex_def,
    chapterVISection103YInfinitySexticInitial, Fin.sum_univ_succ]

theorem chapterVI_section103YInfinityReduced_homogeneousComponent_three :
    MvPolynomial.homogeneousComponent 3 chapterVISection103YInfinityReduced =
      chapterVISection103YInfinityReducedInitial := by
  simp [chapterVISection103YInfinityReduced,
    chapterVI_homogeneousComponent_originMonomial,
    chapterVISection103ReducedGaussianCoefficient, GaussianInt.toComplex_def,
    chapterVISection103YInfinityReducedInitial, Fin.sum_univ_succ]
  ring

private theorem chapterVI_xInfinitySexticInitial_ne_zero :
    chapterVISection103XInfinitySexticInitial ≠ 0 := by
  simp [chapterVISection103XInfinitySexticInitial]

private theorem chapterVI_yInfinitySexticInitial_ne_zero :
    chapterVISection103YInfinitySexticInitial ≠ 0 := by
  simp [chapterVISection103YInfinitySexticInitial]

private theorem chapterVI_xInfinityReducedInitial_ne_zero :
    chapterVISection103XInfinityReducedInitial ≠ 0 := by
  intro hzero
  have hcoeff := congrArg
    (MvPolynomial.coeff (chapterVIOriginMonomial 1 2)) hzero
  norm_num [chapterVISection103XInfinityReducedInitial,
    MvPolynomial.coeff_add, MvPolynomial.coeff_monomial,
    chapterVI_originMonomial_inj, Complex.ext_iff] at hcoeff

private theorem chapterVI_yInfinityReducedInitial_ne_zero :
    chapterVISection103YInfinityReducedInitial ≠ 0 := by
  intro hzero
  have hcoeff := congrArg
    (MvPolynomial.coeff (chapterVIOriginMonomial 1 2)) hzero
  norm_num [chapterVISection103YInfinityReducedInitial,
    MvPolynomial.coeff_add, MvPolynomial.coeff_monomial,
    chapterVI_originMonomial_inj, Complex.ext_iff] at hcoeff

/-- The sextic has multiplicity two at `(1 : 0 : 0)`. -/
theorem chapterVI_section103XInfinitySextic_hasInitialDegree_two :
    HasInitialDegree chapterVISection103XInfinitySextic 2 := by
  constructor
  · rw [chapterVI_section103XInfinitySextic_homogeneousComponent_two]
    exact chapterVI_xInfinitySexticInitial_ne_zero
  · intro m hm
    interval_cases m <;>
      unfold chapterVISection103XInfinitySextic <;>
      simp only [map_sum, chapterVI_homogeneousComponent_originMonomial] <;>
      simp [chapterVISection103AffineGaussianCoefficient, GaussianInt.toComplex_def,
        Fin.sum_univ_succ]

/-- The reduced septic has multiplicity three at `(1 : 0 : 0)`. -/
theorem chapterVI_section103XInfinityReduced_hasInitialDegree_three :
    HasInitialDegree chapterVISection103XInfinityReduced 3 := by
  constructor
  · rw [chapterVI_section103XInfinityReduced_homogeneousComponent_three]
    exact chapterVI_xInfinityReducedInitial_ne_zero
  · intro m hm
    interval_cases m <;>
      unfold chapterVISection103XInfinityReduced <;>
      simp only [map_sum, chapterVI_homogeneousComponent_originMonomial] <;>
      simp [chapterVISection103ReducedGaussianCoefficient, GaussianInt.toComplex_def,
        Fin.sum_univ_succ]

/-- The sextic has multiplicity two at `(0 : 1 : 0)`. -/
theorem chapterVI_section103YInfinitySextic_hasInitialDegree_two :
    HasInitialDegree chapterVISection103YInfinitySextic 2 := by
  constructor
  · rw [chapterVI_section103YInfinitySextic_homogeneousComponent_two]
    exact chapterVI_yInfinitySexticInitial_ne_zero
  · intro m hm
    interval_cases m <;>
      unfold chapterVISection103YInfinitySextic <;>
      simp only [map_sum, chapterVI_homogeneousComponent_originMonomial] <;>
      simp [chapterVISection103AffineGaussianCoefficient, GaussianInt.toComplex_def,
        Fin.sum_univ_succ]

/-- The reduced septic has multiplicity three at `(0 : 1 : 0)`. -/
theorem chapterVI_section103YInfinityReduced_hasInitialDegree_three :
    HasInitialDegree chapterVISection103YInfinityReduced 3 := by
  constructor
  · rw [chapterVI_section103YInfinityReduced_homogeneousComponent_three]
    exact chapterVI_yInfinityReducedInitial_ne_zero
  · intro m hm
    interval_cases m <;>
      unfold chapterVISection103YInfinityReduced <;>
      simp only [map_sum, chapterVI_homogeneousComponent_originMonomial] <;>
      simp [chapterVISection103ReducedGaussianCoefficient, GaussianInt.toComplex_def,
        Fin.sum_univ_succ]

end PoincareChapterVI
