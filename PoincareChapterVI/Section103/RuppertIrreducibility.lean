/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.Section103.RuppertNormalization
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.IntervalCases

/-!
# Absolute irreducibility of the Chapter VI affine curve

This file closes the exceptional case left by the bounded Ruppert-kernel calculation. It gives
an exact finite certificate that the Chapter VI quartic, viewed as a polynomial in `y` over
`ℂ(x)`, is coprime to its derivative. The certificate specializes the Gaussian-integer
coefficient polynomial at `x = 1`, maps `i` to `4` in `ZMod 17`, and checks the explicit Bézout
identity

`(y² + 7y) f + (4 + 15y + 5y² + 4y³) f' = 1`.

Nonvanishing of the specialized resultant lifts through Gaussian integers and complex
polynomials to `ℂ(x)`. Combined with the two normalized differential equations and the
full-rank Ruppert certificate, this proves that every factorization has a unit factor and hence
that the exact affine polynomial is irreducible over `ℂ`.
-/

noncomputable section

open scoped BigOperators

namespace PoincareChapterVI

private abbrev F17 := ZMod 17
private instance : Fact (Nat.Prime 17) := ⟨by decide⟩

private abbrev XIndex := {j : Fin 2 // j ≠ 1}
private abbrev GaussianX := MvPolynomial XIndex GaussianInt
private abbrev ComplexX := MvPolynomial XIndex ℂ

private def xIndex : XIndex := ⟨0, by decide⟩

def chapterVIGaussianPolynomialY : Polynomial GaussianX :=
  ∑ a : Fin 5, ∑ b : Fin 5,
    Polynomial.monomial b.val
      (MvPolynomial.monomial (Finsupp.single xIndex a.val)
        (chapterVISection103AffineGaussianCoefficient a b))

def chapterVIGaussianMod17 : GaussianInt →+* F17 :=
  Zsqrtd.lift ⟨4, by decide⟩

def chapterVICoefficientSpecialization17 : GaussianX →+* F17 :=
  MvPolynomial.eval₂Hom chapterVIGaussianMod17 (fun _ ↦ 1)

def chapterVISpecializedPolynomial17 : Polynomial F17 :=
  Polynomial.C 3 + Polynomial.C 13 * Polynomial.X +
    Polynomial.C 7 * Polynomial.X ^ 2 + Polynomial.C 16 * Polynomial.X ^ 3 +
      Polynomial.C 3 * Polynomial.X ^ 4

private def chapterVISpecializedBezoutLeft17 : Polynomial F17 :=
  Polynomial.C 7 * Polynomial.X + Polynomial.X ^ 2

private def chapterVISpecializedBezoutRight17 : Polynomial F17 :=
  Polynomial.C 4 + Polynomial.C 15 * Polynomial.X +
    Polynomial.C 5 * Polynomial.X ^ 2 + Polynomial.C 4 * Polynomial.X ^ 3

private theorem chapterVI_sum_antidiagonal_pair {M : Type} [AddCommMonoid M]
    (f : ℕ × ℕ → M) (n : ℕ) :
    ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, f p =
      ∑ k ∈ Finset.range n.succ, f (k, n - k) := by
  simpa using Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j ↦ f (i, j)) n

private theorem chapterVISpecializedPolynomial17_derivative :
    chapterVISpecializedPolynomial17.derivative =
      Polynomial.C 13 + Polynomial.C 14 * Polynomial.X +
        Polynomial.C 14 * Polynomial.X ^ 2 + Polynomial.C 12 * Polynomial.X ^ 3 := by
  have h72 : Polynomial.C (7 : F17) * Polynomial.C 2 = Polynomial.C 14 := by
    rw [← Polynomial.C_mul]
    congr 1
  have h163 : Polynomial.C (16 : F17) * Polynomial.C 3 = Polynomial.C 14 := by
    rw [← Polynomial.C_mul]
    congr 1
  have h34 : Polynomial.C (3 : F17) * Polynomial.C 4 = Polynomial.C 12 := by
    rw [← Polynomial.C_mul]
    congr 1
  simp [chapterVISpecializedPolynomial17, Polynomial.derivative_add,
    Polynomial.derivative_mul, Polynomial.derivative_pow]
  ring_nf
  rw [h72, mul_assoc, h163, mul_assoc, h34]
  ring

set_option maxHeartbeats 2000000 in
theorem chapterVI_specializedBezout17 :
    chapterVISpecializedBezoutLeft17 * chapterVISpecializedPolynomial17 +
      chapterVISpecializedBezoutRight17 * chapterVISpecializedPolynomial17.derivative = 1 := by
  rw [chapterVISpecializedPolynomial17_derivative]
  have hdegree :
      (chapterVISpecializedBezoutLeft17 * chapterVISpecializedPolynomial17 +
        chapterVISpecializedBezoutRight17 *
          (Polynomial.C 13 + Polynomial.C 14 * Polynomial.X +
            Polynomial.C 14 * Polynomial.X ^ 2 +
              Polynomial.C 12 * Polynomial.X ^ 3)).natDegree ≤ 6 := by
    unfold chapterVISpecializedBezoutLeft17 chapterVISpecializedBezoutRight17
      chapterVISpecializedPolynomial17
    compute_degree
  ext n
  by_cases hn : n ≤ 6
  · interval_cases n <;>
      simp only [chapterVISpecializedBezoutLeft17, chapterVISpecializedBezoutRight17,
        chapterVISpecializedPolynomial17, Polynomial.coeff_add, Polynomial.coeff_mul] <;>
      simp_rw [chapterVI_sum_antidiagonal_pair] <;>
      norm_num [Finset.sum_range_succ, Polynomial.coeff_X,
        Polynomial.coeff_one] <;> decide
  · have hn' : 6 < n := by omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hdegree hn')]
    symm
    exact Polynomial.coeff_eq_zero_of_natDegree_lt
      (p := (1 : Polynomial F17)) (n := n) (by
        simpa only [Polynomial.natDegree_one] using (show 0 < n by omega))

theorem chapterVI_gaussianPolynomial_specializes_mod17 :
    chapterVIGaussianPolynomialY.map chapterVICoefficientSpecialization17 =
      chapterVISpecializedPolynomial17 := by
  have hdegree : chapterVISpecializedPolynomial17.natDegree ≤ 4 := by
    unfold chapterVISpecializedPolynomial17
    compute_degree
  have hgaussianDegree : chapterVIGaussianPolynomialY.natDegree ≤ 4 := by
    unfold chapterVIGaussianPolynomialY
    refine Polynomial.natDegree_sum_le_of_forall_le Finset.univ _ ?_
    intro a ha
    refine Polynomial.natDegree_sum_le_of_forall_le Finset.univ _ ?_
    intro b hb
    exact (Polynomial.natDegree_monomial_le _).trans (by omega)
  ext n
  by_cases hn : n ≤ 4
  · interval_cases n <;>
      norm_num [chapterVIGaussianPolynomialY, chapterVICoefficientSpecialization17,
        chapterVIGaussianMod17, chapterVISection103AffineGaussianCoefficient,
        xIndex, Fin.sum_univ_succ, chapterVISpecializedPolynomial17,
        Polynomial.coeff_add, Polynomial.coeff_mul, Polynomial.coeff_monomial] <;>
      try simp_rw [chapterVI_sum_antidiagonal_pair] <;>
      norm_num [Finset.sum_range_succ, Polynomial.coeff_X]
    all_goals decide
  · have h0 : n ≠ 0 := by omega
    have h1 : n ≠ 1 := by omega
    have h2 : n ≠ 2 := by omega
    have h3 : n ≠ 3 := by omega
    have h4 : n ≠ 4 := by omega
    rw [Polynomial.coeff_map,
      Polynomial.coeff_eq_zero_of_natDegree_lt
        (p := chapterVIGaussianPolynomialY) (n := n)
        (lt_of_le_of_lt hgaussianDegree (by omega))]
    simp only [map_zero]
    symm
    exact Polynomial.coeff_eq_zero_of_natDegree_lt
      (p := chapterVISpecializedPolynomial17) (n := n)
      (lt_of_le_of_lt hdegree (by omega))

theorem chapterVI_specializedResultant17_ne_zero :
    Polynomial.resultant chapterVISpecializedPolynomial17
      chapterVISpecializedPolynomial17.derivative 4 3 ≠ 0 := by
  have hcoprime : IsCoprime chapterVISpecializedPolynomial17
      chapterVISpecializedPolynomial17.derivative :=
    ⟨chapterVISpecializedBezoutLeft17, chapterVISpecializedBezoutRight17,
      chapterVI_specializedBezout17⟩
  have hresultant := Polynomial.resultant_ne_zero chapterVISpecializedPolynomial17
    chapterVISpecializedPolynomial17.derivative hcoprime
  have hdegree : chapterVISpecializedPolynomial17.natDegree = 4 := by
    apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    · unfold chapterVISpecializedPolynomial17
      compute_degree
    · unfold chapterVISpecializedPolynomial17
      simp only [Polynomial.coeff_add, Polynomial.coeff_mul]
      simp_rw [chapterVI_sum_antidiagonal_pair]
      norm_num [Finset.sum_range_succ, Polynomial.coeff_X]
      decide
  have hderivativeDegree : chapterVISpecializedPolynomial17.derivative.natDegree = 3 := by
    rw [chapterVISpecializedPolynomial17_derivative]
    apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    · compute_degree
    · simp only [Polynomial.coeff_add, Polynomial.coeff_mul]
      simp_rw [chapterVI_sum_antidiagonal_pair]
      norm_num [Finset.sum_range_succ, Polynomial.coeff_X]
      decide
  simpa [hdegree, hderivativeDegree] using hresultant

theorem chapterVI_gaussianResultant_ne_zero :
    Polynomial.resultant chapterVIGaussianPolynomialY
      chapterVIGaussianPolynomialY.derivative 4 3 ≠ 0 := by
  intro hzero
  have hmap := congrArg chapterVICoefficientSpecialization17 hzero
  rw [← Polynomial.resultant_map_map] at hmap
  rw [chapterVI_gaussianPolynomial_specializes_mod17,
    ← Polynomial.derivative_map,
    chapterVI_gaussianPolynomial_specializes_mod17] at hmap
  exact chapterVI_specializedResultant17_ne_zero hmap

def chapterVIGaussianToComplexX : GaussianX →+* ComplexX :=
  MvPolynomial.map GaussianInt.toComplex

def chapterVIGaussianPolynomialYComplex : Polynomial ComplexX :=
  chapterVIGaussianPolynomialY.map chapterVIGaussianToComplexX

theorem chapterVI_complexResultant_ne_zero :
    Polynomial.resultant chapterVIGaussianPolynomialYComplex
      chapterVIGaussianPolynomialYComplex.derivative 4 3 ≠ 0 := by
  rw [chapterVIGaussianPolynomialYComplex, Polynomial.derivative_map,
    Polynomial.resultant_map_map]
  simpa [chapterVIGaussianToComplexX] using
    (MvPolynomial.map_injective GaussianInt.toComplex
      GaussianInt.toComplex_injective).ne chapterVI_gaussianResultant_ne_zero

private theorem chapterVI_gaussianComplexTerm_eq (a b : ℕ) (c : GaussianInt) :
    Polynomial.monomial b
        (MvPolynomial.monomial (Finsupp.single xIndex a) (GaussianInt.toComplex c)) =
      chapterVIAsPolynomialY
        (MvPolynomial.monomial (chapterVIBivariateMonomial a b)
          (GaussianInt.toComplex c)) := by
  simp only [chapterVIAsPolynomialY, AlgEquiv.trans_apply,
    MvPolynomial.renameEquiv_apply, MvPolynomial.rename_monomial,
    MvPolynomial.optionEquivLeft_monomial]
  have hnone :
      (Finsupp.mapDomain (Equiv.optionSubtypeNe (1 : Fin 2)).symm
        (chapterVIBivariateMonomial a b)) none = b := by
    rw [Finsupp.mapDomain_equiv_apply]
    exact chapterVI_bivariateMonomial_apply_one a b
  have hsome :
      (Finsupp.mapDomain (Equiv.optionSubtypeNe (1 : Fin 2)).symm
        (chapterVIBivariateMonomial a b)).some = Finsupp.single xIndex a := by
    ext j
    change
      (Finsupp.mapDomain (Equiv.optionSubtypeNe (1 : Fin 2)).symm
        (chapterVIBivariateMonomial a b)) (some j) =
      (Finsupp.single xIndex a) j
    rw [Finsupp.mapDomain_equiv_apply]
    have hj : j = xIndex := by
      apply Subtype.ext
      apply Fin.ext
      simp [xIndex]
      have hjlt := j.val.isLt
      have hjne : j.val ≠ 1 := j.property
      omega
    subst j
    have heq :
        (Equiv.optionSubtypeNe (1 : Fin 2)).symm.symm (some xIndex) = 0 := by
      rfl
    rw [heq, chapterVI_bivariateMonomial_apply_zero]
    simp
  rw [hnone, hsome]

theorem chapterVI_gaussianPolynomialYComplex_eq :
    chapterVIGaussianPolynomialYComplex =
      chapterVIAsPolynomialY chapterVISection103AffinePolynomial := by
  change
    Polynomial.map (MvPolynomial.map GaussianInt.toComplex)
        (∑ a : Fin 5, ∑ b : Fin 5,
          Polynomial.monomial b.val
            (MvPolynomial.monomial (Finsupp.single xIndex a.val)
              (chapterVISection103AffineGaussianCoefficient a b))) =
      chapterVIAsPolynomialY
        (∑ a : Fin 5, ∑ b : Fin 5,
          MvPolynomial.monomial (chapterVIBivariateMonomial a.val b.val)
            (GaussianInt.toComplex (chapterVISection103AffineGaussianCoefficient a b)))
  simp_rw [Polynomial.map_sum, Polynomial.map_monomial,
    MvPolynomial.map_monomial, map_sum]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  exact chapterVI_gaussianComplexTerm_eq a.val b.val _

theorem chapterVI_gaussianPolynomialYComplex_natDegree :
    chapterVIGaussianPolynomialYComplex.natDegree = 4 := by
  rw [chapterVI_gaussianPolynomialYComplex_eq,
    chapterVI_natDegree_asPolynomialY,
    chapterVI_section103Polynomial_degreeOf_y]

theorem chapterVI_gaussianPolynomialYComplex_derivative_natDegree :
    chapterVIGaussianPolynomialYComplex.derivative.natDegree = 3 := by
  rw [Polynomial.natDegree_derivative,
    chapterVI_gaussianPolynomialYComplex_natDegree]

private abbrev ComplexXFraction := FractionRing ComplexX
private abbrev ChapterVIBivar := MvPolynomial (Fin 2) ℂ

def chapterVIComplexPolynomialFractionY : Polynomial ComplexXFraction :=
  chapterVIGaussianPolynomialYComplex.map (algebraMap ComplexX ComplexXFraction)

theorem chapterVI_fractionResultant_ne_zero :
    Polynomial.resultant chapterVIComplexPolynomialFractionY
      chapterVIComplexPolynomialFractionY.derivative 4 3 ≠ 0 := by
  rw [chapterVIComplexPolynomialFractionY, Polynomial.derivative_map,
    Polynomial.resultant_map_map]
  simpa using (IsFractionRing.injective ComplexX ComplexXFraction).ne
    chapterVI_complexResultant_ne_zero

theorem chapterVI_fractionPolynomial_natDegree :
    chapterVIComplexPolynomialFractionY.natDegree = 4 := by
  rw [chapterVIComplexPolynomialFractionY,
    Polynomial.natDegree_map_eq_of_injective
      (IsFractionRing.injective ComplexX ComplexXFraction),
    chapterVI_gaussianPolynomialYComplex_natDegree]

theorem chapterVI_fractionPolynomial_derivative_natDegree :
    chapterVIComplexPolynomialFractionY.derivative.natDegree = 3 := by
  rw [Polynomial.natDegree_derivative, chapterVI_fractionPolynomial_natDegree]

theorem chapterVI_fractionPolynomial_isCoprime_derivative :
    IsCoprime chapterVIComplexPolynomialFractionY
      chapterVIComplexPolynomialFractionY.derivative := by
  by_contra hnot
  apply chapterVI_fractionResultant_ne_zero
  have hnonzero : chapterVIComplexPolynomialFractionY ≠ 0 := by
    intro hzero
    have := congrArg Polynomial.natDegree hzero
    simp [chapterVI_fractionPolynomial_natDegree] at this
  have hresultantZero :
      Polynomial.resultant chapterVIComplexPolynomialFractionY
        chapterVIComplexPolynomialFractionY.derivative = 0 :=
    Polynomial.resultant_eq_zero_iff.mpr ⟨Or.inl hnonzero, hnot⟩
  simpa [chapterVI_fractionPolynomial_natDegree,
    chapterVI_fractionPolynomial_derivative_natDegree] using hresultantZero

private theorem chapterVI_factor_coprimes_of_separable
    (F A B : Polynomial ComplexXFraction) (hfactor : F = A * B)
    (hseparable : IsCoprime F F.derivative) :
    IsCoprime A B ∧ IsCoprime A A.derivative := by
  subst F
  rcases hseparable with ⟨u, v, huv⟩
  rw [Polynomial.derivative_mul] at huv
  constructor
  · refine ⟨u * B + v * B.derivative, v * A.derivative, ?_⟩
    calc
      (u * B + v * B.derivative) * A + (v * A.derivative) * B =
          u * (A * B) + v * (A.derivative * B + A * B.derivative) := by ring
      _ = 1 := huv
  · refine ⟨u * B + v * B.derivative, v * B, ?_⟩
    calc
      (u * B + v * B.derivative) * A + (v * B) * A.derivative =
          u * (A * B) + v * (A.derivative * B + A * B.derivative) := by ring
      _ = 1 := huv

private theorem chapterVI_factor_isUnit_of_normalized
    (F A B U : Polynomial ComplexXFraction) (hfactor : F = A * B)
    (hnormalized : B * A.derivative - U * F.derivative = 0)
    (hseparable : IsCoprime F F.derivative) (hunit : IsUnit (1 - U)) :
    IsUnit A := by
  have hcops := chapterVI_factor_coprimes_of_separable F A B hfactor hseparable
  have heq : (1 - U) * (B * A.derivative) = U * (A * B.derivative) := by
    rw [hfactor, Polynomial.derivative_mul] at hnormalized
    linear_combination hnormalized
  have hdivWithUnit : A ∣ (1 - U) * (B * A.derivative) := by
    rw [heq]
    exact ⟨U * B.derivative, by ring⟩
  have hdiv : A ∣ B * A.derivative := hunit.dvd_mul_left.mp hdivWithUnit
  exact (hcops.1.mul_right hcops.2).isUnit_of_dvd hdiv

def chapterVIAsFractionPolynomialY : ChapterVIBivar →+* Polynomial ComplexXFraction :=
  (Polynomial.mapRingHom (algebraMap ComplexX ComplexXFraction)).comp
    chapterVIAsPolynomialY.toRingEquiv.toRingHom

theorem chapterVI_asFractionPolynomialY_pderiv (p : ChapterVIBivar) :
    chapterVIAsFractionPolynomialY (MvPolynomial.pderiv 1 p) =
      (chapterVIAsFractionPolynomialY p).derivative := by
  change Polynomial.map (algebraMap ComplexX ComplexXFraction)
      (chapterVIAsPolynomialY (MvPolynomial.pderiv 1 p)) =
    (Polynomial.map (algebraMap ComplexX ComplexXFraction)
      (chapterVIAsPolynomialY p)).derivative
  rw [chapterVI_asPolynomialY_pderiv, Polynomial.derivative_map]

theorem chapterVI_natDegree_asFractionPolynomialY (p : ChapterVIBivar) :
    (chapterVIAsFractionPolynomialY p).natDegree = p.degreeOf (1 : Fin 2) := by
  change (Polynomial.map (algebraMap ComplexX ComplexXFraction)
    (chapterVIAsPolynomialY p)).natDegree = _
  rw [Polynomial.natDegree_map_eq_of_injective
    (IsFractionRing.injective ComplexX ComplexXFraction),
    chapterVI_natDegree_asPolynomialY]

theorem chapterVI_asFractionPolynomialY_section103 :
    chapterVIAsFractionPolynomialY chapterVISection103AffinePolynomial =
      chapterVIComplexPolynomialFractionY := by
  change Polynomial.map (algebraMap ComplexX ComplexXFraction)
      (chapterVIAsPolynomialY chapterVISection103AffinePolynomial) =
    Polynomial.map (algebraMap ComplexX ComplexXFraction)
      chapterVIGaussianPolynomialYComplex
  rw [chapterVI_gaussianPolynomialYComplex_eq]

private def chapterVIFractionScalar : ℂ →+* ComplexXFraction :=
  (algebraMap ComplexX ComplexXFraction).comp MvPolynomial.C

private theorem chapterVI_asFractionPolynomialY_smul
    (c : ℂ) (p : ChapterVIBivar) :
    chapterVIAsFractionPolynomialY (c • p) =
      Polynomial.C (chapterVIFractionScalar c) * chapterVIAsFractionPolynomialY p := by
  rw [Algebra.smul_def, map_mul]
  change Polynomial.map (algebraMap ComplexX ComplexXFraction)
      (chapterVIAsPolynomialY (MvPolynomial.C c)) *
        chapterVIAsFractionPolynomialY p = _
  simp [chapterVIAsPolynomialY, chapterVIFractionScalar]

private theorem chapterVIFractionScalar_injective :
    Function.Injective chapterVIFractionScalar := by
  exact (IsFractionRing.injective ComplexX ComplexXFraction).comp
    (MvPolynomial.C_injective XIndex ℂ)

theorem chapterVI_middleFactor_isUnit_in_fractionY
    (a b : ChapterVIBivar) (ha : a ≠ 0) (hb : b ≠ 0)
    (hfactor : chapterVISection103AffinePolynomial = a * b)
    (hdegreePos : 0 < a.degreeOf (1 : Fin 2))
    (hdegreeLt : a.degreeOf (1 : Fin 2) < 4) :
    IsUnit (chapterVIAsFractionPolynomialY a) := by
  let c : ℂ := (a.degreeOf (1 : Fin 2) : ℂ) / 4
  let U : Polynomial ComplexXFraction := Polynomial.C (chapterVIFractionScalar c)
  have hfactorMapped := congrArg chapterVIAsFractionPolynomialY hfactor
  rw [map_mul, chapterVI_asFractionPolynomialY_section103] at hfactorMapped
  obtain ⟨hxzero, hyzero⟩ :=
    chapterVI_normalizedFactor_components_eq_zero a b ha hb hfactor
  have hnormalized := congrArg chapterVIAsFractionPolynomialY hyzero
  rw [map_sub, map_mul, chapterVI_asFractionPolynomialY_pderiv,
    chapterVI_asFractionPolynomialY_smul,
    chapterVI_asFractionPolynomialY_pderiv,
    chapterVI_asFractionPolynomialY_section103, map_zero] at hnormalized
  have hc : c ≠ 1 := by
    dsimp only [c]
    interval_cases hdegree : a.degreeOf (1 : Fin 2) <;> norm_num
  have hs : chapterVIFractionScalar c ≠ 1 := by
    rw [← map_one chapterVIFractionScalar]
    exact chapterVIFractionScalar_injective.ne hc
  have hscalarUnit : IsUnit (1 - chapterVIFractionScalar c) :=
    isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hs.symm)
  have hunit : IsUnit (1 - U) := by
    have hC : 1 - U = Polynomial.C (1 - chapterVIFractionScalar c) := by
      simp [U]
    rw [hC]
    exact Polynomial.isUnit_C.mpr hscalarUnit
  exact chapterVI_factor_isUnit_of_normalized
    chapterVIComplexPolynomialFractionY
    (chapterVIAsFractionPolynomialY a)
    (chapterVIAsFractionPolynomialY b) U hfactorMapped hnormalized
    chapterVI_fractionPolynomial_isCoprime_derivative hunit

private abbrev XCoeff := MvPolynomial {j : Fin 2 // j ≠ 0} ℂ

private instance : CharZero XCoeff :=
  CharZero.of_addMonoidHom (MvPolynomial.C : ℂ →+* XCoeff).toAddMonoidHom
    MvPolynomial.C_1 (MvPolynomial.C_injective _ _)

def chapterVIAsPolynomialX : ChapterVIBivar ≃ₐ[ℂ] Polynomial XCoeff :=
  (MvPolynomial.renameEquiv ℂ (Equiv.optionSubtypeNe (0 : Fin 2)).symm).trans
    (MvPolynomial.optionEquivLeft ℂ {j : Fin 2 // j ≠ 0})

@[simp] theorem chapterVI_asPolynomialX_X_zero :
    chapterVIAsPolynomialX (MvPolynomial.X 0) = Polynomial.X := by
  simp [chapterVIAsPolynomialX, Equiv.optionSubtypeNe_symm_apply]

@[simp] theorem chapterVI_asPolynomialX_X_one :
    chapterVIAsPolynomialX (MvPolynomial.X 1) =
      Polynomial.C (MvPolynomial.X ⟨1, by decide⟩) := by
  simp [chapterVIAsPolynomialX, Equiv.optionSubtypeNe_symm_apply]

theorem chapterVI_asPolynomialX_pderiv (p : ChapterVIBivar) :
    chapterVIAsPolynomialX (MvPolynomial.pderiv 0 p) =
      (chapterVIAsPolynomialX p).derivative := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [chapterVIAsPolynomialX]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
      rw [MvPolynomial.pderiv_mul]
      fin_cases i <;> simp [hp]

theorem chapterVI_natDegree_asPolynomialX (p : ChapterVIBivar) :
    (chapterVIAsPolynomialX p).natDegree = p.degreeOf (0 : Fin 2) := by
  simpa [chapterVIAsPolynomialX] using
    (MvPolynomial.degreeOf_eq_natDegree (R := ℂ) (0 : Fin 2) p).symm

private theorem chapterVI_degreeOf_x_eq_zero_of_pderiv_eq_zero
    (p : ChapterVIBivar) (hzero : MvPolynomial.pderiv 0 p = 0) :
    p.degreeOf (0 : Fin 2) = 0 := by
  have hmapped := congrArg chapterVIAsPolynomialX hzero
  rw [chapterVI_asPolynomialX_pderiv, map_zero] at hmapped
  rw [← chapterVI_natDegree_asPolynomialX]
  exact Polynomial.derivative_eq_zero.mp hmapped

private theorem chapterVI_degreeOf_y_eq_zero_of_pderiv_eq_zero
    (p : ChapterVIBivar) (hzero : MvPolynomial.pderiv 1 p = 0) :
    p.degreeOf (1 : Fin 2) = 0 := by
  have hmapped := congrArg chapterVIAsPolynomialY hzero
  rw [chapterVI_asPolynomialY_pderiv, map_zero] at hmapped
  rw [← chapterVI_natDegree_asPolynomialY]
  exact Polynomial.derivative_eq_zero.mp hmapped

private theorem chapterVI_isUnit_of_both_pderiv_eq_zero
    (p : ChapterVIBivar) (hp : p ≠ 0)
    (hx : MvPolynomial.pderiv 0 p = 0)
    (hy : MvPolynomial.pderiv 1 p = 0) : IsUnit p := by
  have hdx := chapterVI_degreeOf_x_eq_zero_of_pderiv_eq_zero p hx
  have hdy := chapterVI_degreeOf_y_eq_zero_of_pderiv_eq_zero p hy
  have hvars : p.vars = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i hi
    rw [MvPolynomial.mem_vars_iff_degreeOf_ne_zero] at hi
    fin_cases i
    · exact hi hdx
    · exact hi hdy
  have heq : p = MvPolynomial.C (MvPolynomial.coeff 0 p) :=
    MvPolynomial.vars_eq_empty_iff_eq_C.mp hvars
  have hcoeff : MvPolynomial.coeff 0 p ≠ 0 := by
    intro hzero
    apply hp
    rw [heq, hzero, MvPolynomial.C_0]
  rw [heq]
  exact (isUnit_iff_ne_zero.mpr hcoeff).map MvPolynomial.C

/-- The normalized Ruppert equations, together with the separability certificate, exclude
every proper factor of the affine Chapter VI polynomial. -/
theorem chapterVI_section103_factor_isUnit
    (a b : ChapterVIBivar)
    (hfactor : chapterVISection103AffinePolynomial = a * b) :
    IsUnit a ∨ IsUnit b := by
  have ha : a ≠ 0 := by
    intro hzero
    apply chapterVI_section103Polynomial_ne_zero
    simpa [hzero] using hfactor
  have hb : b ≠ 0 := by
    intro hzero
    apply chapterVI_section103Polynomial_ne_zero
    simpa [hzero] using hfactor
  have hsum := (chapterVI_factor_degree_sums a b ha hb hfactor).2
  obtain ⟨hxzero, hyzero⟩ :=
    chapterVI_normalizedFactor_components_eq_zero a b ha hb hfactor
  by_cases hdegreeZero : a.degreeOf (1 : Fin 2) = 0
  · left
    have hy : MvPolynomial.pderiv 1 a = 0 :=
      chapterVI_pderiv_eq_zero_of_degreeOf_eq_zero 1 a hdegreeZero
    have hxproduct : b * MvPolynomial.pderiv 0 a = 0 := by
      simpa [hdegreeZero] using hxzero
    have hx : MvPolynomial.pderiv 0 a = 0 :=
      (mul_eq_zero.mp hxproduct).resolve_left hb
    exact chapterVI_isUnit_of_both_pderiv_eq_zero a ha hx hy
  by_cases hdegreeFour : a.degreeOf (1 : Fin 2) = 4
  · right
    have hbDegree : b.degreeOf (1 : Fin 2) = 0 := by omega
    have hy : MvPolynomial.pderiv 1 b = 0 :=
      chapterVI_pderiv_eq_zero_of_degreeOf_eq_zero 1 b hbDegree
    have hxnormalized := hxzero
    rw [hfactor, MvPolynomial.pderiv_mul] at hxnormalized
    norm_num [hdegreeFour] at hxnormalized
    have hxproduct : a * MvPolynomial.pderiv 0 b = 0 := by
      linear_combination -hxnormalized
    have hx : MvPolynomial.pderiv 0 b = 0 :=
      (mul_eq_zero.mp hxproduct).resolve_left ha
    exact chapterVI_isUnit_of_both_pderiv_eq_zero b hb hx hy
  · have hdegreePos : 0 < a.degreeOf (1 : Fin 2) := by omega
    have hdegreeLt : a.degreeOf (1 : Fin 2) < 4 := by omega
    have hunitFraction := chapterVI_middleFactor_isUnit_in_fractionY
      a b ha hb hfactor hdegreePos hdegreeLt
    obtain ⟨r, hr, hrA⟩ := Polynomial.isUnit_iff.mp hunitFraction
    have hdegreeMapped : (chapterVIAsFractionPolynomialY a).natDegree = 0 := by
      rw [← hrA]
      simp
    rw [chapterVI_natDegree_asFractionPolynomialY] at hdegreeMapped
    omega

/-- The exact affine polynomial used in Poincaré's §103 argument is absolutely irreducible
over `ℂ`. -/
theorem chapterVI_section103AffinePolynomial_irreducible :
    Irreducible chapterVISection103AffinePolynomial := by
  rw [irreducible_iff]
  constructor
  · intro hunit
    have hmapped := hunit.map chapterVIAsPolynomialY.toRingEquiv.toRingHom
    obtain ⟨r, hr, hrF⟩ := Polynomial.isUnit_iff.mp hmapped
    have hrF' : Polynomial.C r =
        chapterVIAsPolynomialY chapterVISection103AffinePolynomial := hrF
    have hdegree :
        (chapterVIAsPolynomialY chapterVISection103AffinePolynomial).natDegree = 0 := by
      rw [← hrF']
      simp
    rw [chapterVI_natDegree_asPolynomialY,
      chapterVI_section103Polynomial_degreeOf_y] at hdegree
    omega
  · intro a b hfactor
    exact chapterVI_section103_factor_isUnit a b hfactor

end PoincareChapterVI
