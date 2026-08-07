/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.Section103.LocalAlgebra

/-!
# The affine-origin certificate in Poincaré's Section 103

This file makes the tangent calculation at the affine origin exact.  Both Section 103
polynomials are expressed in the local coordinates `x²` and `y + αx`; the determinant of the
change-of-generators matrix is then proved nonzero at the origin.  Consequently their localized
intersection ideal is exactly `(x², y + αx)`.
-/

noncomputable section

open scoped BigOperators

namespace PoincareChapterVI

private abbrev BivarC := MvPolynomial (Fin 2) ℂ
private def ox : BivarC := MvPolynomial.X 0
private def oy : BivarC := MvPolynomial.X 1

def originAlpha : ℂ :=
  (6564100 : ℂ) / 6194669 + (672000 / 6194669 : ℂ) * Complex.I

def originLine : BivarC := oy + MvPolynomial.C originAlpha * ox

def powerDiffQuotient (v w : BivarC) (n : Nat) : BivarC :=
  ∑ k ∈ Finset.range n, v ^ (n - 1 - k) * w ^ k

theorem line_mul_powerDiffQuotient (n : Fin 5) :
    originLine * powerDiffQuotient oy (-MvPolynomial.C originAlpha * ox) n.val =
      oy ^ n.val - (-MvPolynomial.C originAlpha * ox) ^ n.val := by
  fin_cases n <;>
    norm_num [powerDiffQuotient, Finset.sum_range_succ, originLine] <;> ring

def originP_c : BivarC :=
  ∑ a : Fin 5, ∑ b : Fin 5,
    MvPolynomial.C (chapterVISection103AffineGaussianCoefficient a b : ℂ) *
      MvPolynomial.C ((-originAlpha) ^ b.val) * ox ^ (a.val + b.val - 2)

def originP_u : BivarC :=
  ∑ a : Fin 5, ∑ b : Fin 5,
    MvPolynomial.C (chapterVISection103AffineGaussianCoefficient a b : ℂ) *
      ox ^ a.val * powerDiffQuotient oy (-MvPolynomial.C originAlpha * ox) b.val

def originRResidualCoefficient (a b : Fin 5) : ℂ :=
  (chapterVISection103ReducedGaussianCoefficient a b : ℂ) -
    if a.val = 1 ∧ b.val = 0 then 106500 - 96000 * Complex.I
    else if a.val = 0 ∧ b.val = 1 then 90285 - 99840 * Complex.I
    else 0

def originR_t : BivarC :=
  ∑ a : Fin 5, ∑ b : Fin 5,
    MvPolynomial.C (originRResidualCoefficient a b) *
      MvPolynomial.C ((-originAlpha) ^ b.val) * ox ^ (a.val + b.val - 2)

def originR_s0 : BivarC :=
  ∑ a : Fin 5, ∑ b : Fin 5,
    MvPolynomial.C (originRResidualCoefficient a b) *
      ox ^ a.val * powerDiffQuotient oy (-MvPolynomial.C originAlpha * ox) b.val

def originR_s : BivarC :=
  MvPolynomial.C (90285 - 99840 * Complex.I) + originR_s0

def originRawTangent : BivarC :=
  MvPolynomial.C (106500 - 96000 * Complex.I) * ox +
    MvPolynomial.C (90285 - 99840 * Complex.I) * oy

theorem originP_factorization :
    chapterVISection103AffinePolynomial =
      ox ^ 2 * originP_c + originLine * originP_u := by
  change (∑ a : Fin 5, ∑ b : Fin 5,
    MvPolynomial.monomial
      (Finsupp.single 0 a.val + Finsupp.single 1 b.val)
      (chapterVISection103AffineGaussianCoefficient a b : ℂ)) = _
  simp [originP_c, originP_u, Fin.sum_univ_succ, ox, oy,
    MvPolynomial.monomial_eq, Finsupp.prod_fintype, Fin.prod_univ_succ,
    powerDiffQuotient, Finset.sum_range_succ, originLine,
    chapterVISection103AffineGaussianCoefficient, GaussianInt.toComplex_def]
  ring

theorem originR_factorization :
    chapterVISection103ReducedAffinePolynomial =
      ox ^ 2 * originR_t + originLine * originR_s := by
  have halpha : (90285 - 99840 * Complex.I) * originAlpha =
      (106500 - 96000 * Complex.I) := by
    apply Complex.ext <;>
      norm_num [originAlpha, Complex.mul_re, Complex.mul_im]
  have hraw : originRawTangent =
      MvPolynomial.C (90285 - 99840 * Complex.I) * originLine := by
    unfold originRawTangent originLine
    rw [mul_add, ← mul_assoc, ← map_mul, halpha]
    ring
  have hres :
      chapterVISection103ReducedAffinePolynomial - originRawTangent =
        ox ^ 2 * originR_t + originLine * originR_s0 := by
    change (∑ a : Fin 5, ∑ b : Fin 5,
      MvPolynomial.monomial
        (Finsupp.single 0 a.val + Finsupp.single 1 b.val)
        (chapterVISection103ReducedGaussianCoefficient a b : ℂ)) - _ = _
    simp [originRawTangent, originR_t, originR_s0, originRResidualCoefficient,
      Fin.sum_univ_succ, ox, oy,
      MvPolynomial.monomial_eq, Finsupp.prod_fintype, Fin.prod_univ_succ,
      powerDiffQuotient, Finset.sum_range_succ, originLine,
      chapterVISection103ReducedGaussianCoefficient, GaussianInt.toComplex_def]
    norm_num [originAlpha]
    simp only [map_ofNat]
    ring
  calc
    chapterVISection103ReducedAffinePolynomial =
        (chapterVISection103ReducedAffinePolynomial - originRawTangent) +
          originRawTangent := by ring
    _ = (ox ^ 2 * originR_t + originLine * originR_s0) +
          MvPolynomial.C (90285 - 99840 * Complex.I) * originLine := by
      rw [hres, hraw]
    _ = ox ^ 2 * originR_t + originLine * originR_s := by
      simp only [originR_s]
      ring

theorem origin_det_nonzero :
    MvPolynomial.eval (0 : Fin 2 → ℂ)
      (originP_c * originR_s - originP_u * originR_t) ≠ 0 := by
  have hc : MvPolynomial.eval (0 : Fin 2 → ℂ) originP_c =
      4563 * originAlpha ^ 2 - (21320 - 33280 * Complex.I) * originAlpha + 7500 := by
    simp only [originP_c, ox, map_sum, map_mul, map_pow, MvPolynomial.eval_C,
      MvPolynomial.eval_X, Pi.zero_apply]
    norm_num [originAlpha, Fin.sum_univ_succ,
      chapterVISection103AffineGaussianCoefficient, GaussianInt.toComplex_def]
    ring
  have hs : MvPolynomial.eval (0 : Fin 2 → ℂ) originR_s =
      90285 - 99840 * Complex.I := by
    simp only [originR_s, originR_s0, ox, oy, map_add, map_sum, map_mul, map_pow,
      MvPolynomial.eval_C, MvPolynomial.eval_X, Pi.zero_apply]
    norm_num [originRResidualCoefficient, powerDiffQuotient,
      Finset.sum_range_succ, Fin.sum_univ_succ,
      chapterVISection103ReducedGaussianCoefficient,
      GaussianInt.toComplex_def]
  have hu : MvPolynomial.eval (0 : Fin 2 → ℂ) originP_u = 0 := by
    simp only [originP_u, ox, oy, map_sum, map_mul, map_pow, MvPolynomial.eval_C,
      MvPolynomial.eval_X, Pi.zero_apply]
    norm_num [powerDiffQuotient, Finset.sum_range_succ, Fin.sum_univ_succ,
      chapterVISection103AffineGaussianCoefficient,
      GaussianInt.toComplex_def]
  rw [map_sub, map_mul, map_mul, hc, hs, hu, zero_mul, sub_zero]
  apply mul_ne_zero
  · intro h
    have hr := congrArg Complex.re h
    norm_num [originAlpha, pow_two, Complex.div_re, Complex.div_im, Complex.mul_re,
      Complex.mul_im, Complex.normSq_apply] at hr
  · norm_num [Complex.ext_iff]

/-- The two Section 103 germs at the affine origin generate exactly the curvilinear double-point
ideal `(x², y + αx)` in the local ring. -/
theorem chapterVI_origin_localIntersectionIdeal_eq :
    localIntersectionIdeal ℂ 0 chapterVISection103AffinePolynomial
        chapterVISection103ReducedAffinePolynomial =
      Ideal.span {
        algebraMap (PlanePolynomial ℂ) (PlaneLocalRing ℂ 0) (ox ^ 2),
        algebraMap (PlanePolynomial ℂ) (PlaneLocalRing ℂ 0) originLine} :=
  localIntersectionIdeal_eq_of_matrixFactorization ℂ 0
    chapterVISection103AffinePolynomial chapterVISection103ReducedAffinePolynomial
    (ox ^ 2) originLine originP_c originP_u originR_t originR_s
    originP_factorization originR_factorization origin_det_nonzero

end PoincareChapterVI
