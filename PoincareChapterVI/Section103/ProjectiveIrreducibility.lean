/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.Section103.RuppertIrreducibility
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.RingTheory.MvPolynomial.Homogeneous

noncomputable section

open scoped BigOperators

namespace PoincareChapterVI

private abbrev Bivar := MvPolynomial (Fin 2) ℂ
private abbrev Trivar := MvPolynomial (Fin 3) ℂ

def chapterVIProjectiveMonomial (a b : ℕ) : Fin 3 →₀ ℕ :=
  Finsupp.single 0 a + Finsupp.single 1 b + Finsupp.single 2 (6 - a - b)

def chapterVISection103ProjectivePolynomial : Trivar :=
  ∑ a : Fin 5, ∑ b : Fin 5,
    MvPolynomial.monomial (chapterVIProjectiveMonomial a.val b.val)
      (chapterVISection103AffineGaussianCoefficient a b : ℂ)

def chapterVIDehomogenizeZ : Trivar →+* Bivar :=
  MvPolynomial.eval₂Hom MvPolynomial.C ![MvPolynomial.X 0, MvPolynomial.X 1, 1]

private theorem chapterVI_bivariateMonomial_eq (a b : ℕ) :
    chapterVIBivariateMonomial a b =
      Finsupp.single (0 : Fin 2) a + Finsupp.single (1 : Fin 2) b := by
  ext i
  fin_cases i
  · simp
  · simp

private theorem chapterVI_dehomogenize_projectiveTerm (a b : ℕ) (c : ℂ) :
    chapterVIDehomogenizeZ
        (MvPolynomial.monomial (chapterVIProjectiveMonomial a b) c) =
      MvPolynomial.monomial (chapterVIBivariateMonomial a b) c := by
  rw [chapterVI_bivariateMonomial_eq]
  simp [chapterVIDehomogenizeZ, chapterVIProjectiveMonomial,
    MvPolynomial.monomial_eq, Finsupp.prod_fintype, Fin.prod_univ_succ]

theorem chapterVI_dehomogenize_section103ProjectivePolynomial :
    chapterVIDehomogenizeZ chapterVISection103ProjectivePolynomial =
      chapterVISection103AffinePolynomial := by
  change chapterVIDehomogenizeZ
      (∑ a : Fin 5, ∑ b : Fin 5,
        MvPolynomial.monomial (chapterVIProjectiveMonomial a.val b.val)
          (chapterVISection103AffineGaussianCoefficient a b : ℂ)) =
    ∑ a : Fin 5, ∑ b : Fin 5,
      MvPolynomial.monomial (chapterVIBivariateMonomial a.val b.val)
        (chapterVISection103AffineGaussianCoefficient a b : ℂ)
  simp [map_sum, chapterVI_dehomogenize_projectiveTerm]

private theorem chapterVI_projectiveMonomial_degree
    (a b : ℕ) (hab : a + b ≤ 6) :
    (chapterVIProjectiveMonomial a b).degree = 6 := by
  rw [Finsupp.degree_eq_sum]
  simp [chapterVIProjectiveMonomial, Fin.sum_univ_succ]
  omega

theorem chapterVI_section103ProjectivePolynomial_isHomogeneous :
    chapterVISection103ProjectivePolynomial.IsHomogeneous 6 := by
  unfold chapterVISection103ProjectivePolynomial
  apply MvPolynomial.IsHomogeneous.sum
  intro a ha
  apply MvPolynomial.IsHomogeneous.sum
  intro b hb
  by_cases hcoeff : chapterVISection103AffineGaussianCoefficient a b = 0
  · simp [hcoeff, MvPolynomial.isHomogeneous_zero]
  · apply MvPolynomial.isHomogeneous_monomial
    apply chapterVI_projectiveMonomial_degree
    by_contra hab
    fin_cases a <;> fin_cases b <;>
      norm_num [chapterVISection103AffineGaussianCoefficient] at hab <;>
      apply hcoeff <;> rfl

def chapterVIHomogeneousScaling : Trivar →+* Polynomial Trivar :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp MvPolynomial.C)
    (fun i ↦ Polynomial.X * Polynomial.C (MvPolynomial.X i))

private theorem chapterVI_scaling_term (d : Fin 3 →₀ ℕ) (c : ℂ) :
    Polynomial.C (MvPolynomial.C c) *
        ∏ i, (Polynomial.X * Polynomial.C (MvPolynomial.X i)) ^ d i =
      Polynomial.monomial d.degree (MvPolynomial.monomial d c) := by
  rw [Finsupp.degree_eq_sum]
  simp [Fin.prod_univ_succ, MvPolynomial.monomial_eq,
    Finsupp.prod_fintype]
  rw [← Polynomial.C_mul_X_pow_eq_monomial]
  simp only [map_mul, map_pow]
  simp [Fin.sum_univ_succ, pow_add]
  ring

theorem chapterVI_homogeneousScaling_eq_sum (p : Trivar) :
    chapterVIHomogeneousScaling p =
      ∑ d ∈ p.support,
        Polynomial.monomial d.degree (MvPolynomial.monomial d (MvPolynomial.coeff d p)) := by
  change MvPolynomial.eval₂ (Polynomial.C.comp MvPolynomial.C)
      (fun i ↦ Polynomial.X * Polynomial.C (MvPolynomial.X i)) p = _
  rw [MvPolynomial.eval₂_eq']
  apply Finset.sum_congr rfl
  intro d hd
  exact chapterVI_scaling_term d _

theorem chapterVI_homogeneousScaling_of_isHomogeneous
    {p : Trivar} {n : ℕ} (hp : p.IsHomogeneous n) :
    chapterVIHomogeneousScaling p = Polynomial.monomial n p := by
  induction hp using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero => simp
  | add p q hp hq ihp ihq => simp [ihp, ihq]
  | monomial d r hd =>
      rw [chapterVI_homogeneousScaling_eq_sum]
      by_cases hr : r = 0
      · simp [hr]
      · have hd' : d.degree = n := by
          rw [Finsupp.degree_eq_weight_one]
          exact hd
        rw [MvPolynomial.support_monomial]
        simp [hr, hd']

theorem chapterVI_homogeneousScaling_eval_one (p : Trivar) :
    Polynomial.eval 1 (chapterVIHomogeneousScaling p) = p := by
  rw [chapterVI_homogeneousScaling_eq_sum]
  rw [Polynomial.eval_finsetSum]
  simp only [Polynomial.eval_monomial, one_pow, mul_one]
  exact p.as_sum.symm

theorem chapterVI_homogeneousScaling_injective :
    Function.Injective chapterVIHomogeneousScaling := by
  intro p q hpq
  simpa only [chapterVI_homogeneousScaling_eval_one] using
    congrArg (Polynomial.eval 1) hpq

private theorem chapterVI_coeff_coeff_homogeneousScaling
    (p : Trivar) (d : Fin 3 →₀ ℕ) (hd : MvPolynomial.coeff d p ≠ 0) :
    MvPolynomial.coeff d
        ((chapterVIHomogeneousScaling p).coeff d.degree) =
      MvPolynomial.coeff d p := by
  rw [chapterVI_homogeneousScaling_eq_sum]
  rw [Polynomial.finsetSum_coeff, MvPolynomial.coeff_sum]
  rw [Finset.sum_eq_single d]
  · simp [MvPolynomial.coeff_monomial]
  · intro x hx hxd
    by_cases hdegree : x.degree = d.degree
    · simp [hdegree, MvPolynomial.coeff_monomial, hxd]
    · simp [Polynomial.coeff_monomial, hdegree]
  · intro hnot
    exact False.elim (hnot (MvPolynomial.mem_support_iff.mpr hd))

private theorem chapterVI_isHomogeneous_of_homogeneousScaling_eq
    {p : Trivar} {n : ℕ}
    (hscale : chapterVIHomogeneousScaling p = Polynomial.monomial n p) :
    p.IsHomogeneous n := by
  intro d hd
  have hcoeff := congrArg
    (fun q : Polynomial Trivar ↦ MvPolynomial.coeff d (q.coeff d.degree)) hscale
  rw [chapterVI_coeff_coeff_homogeneousScaling p d hd] at hcoeff
  by_contra hdegree
  have hdegree' : n ≠ d.degree := by
    intro heq
    apply hdegree
    rw [Finsupp.degree_eq_weight_one] at heq
    exact heq.symm
  simp [Polynomial.coeff_monomial, hdegree'] at hcoeff
  exact hd hcoeff

private theorem chapterVI_polynomial_eq_monomial_of_natTrailingDegree_eq_natDegree
    (p : Polynomial Trivar) (_hp : p ≠ 0)
    (hdegree : p.natTrailingDegree = p.natDegree) :
    p = Polynomial.monomial p.natDegree p.leadingCoeff := by
  apply Polynomial.ext
  intro k
  rcases lt_trichotomy k p.natDegree with hlt | heq | hgt
  · rw [Polynomial.coeff_eq_zero_of_lt_natTrailingDegree (by omega)]
    simp [Polynomial.coeff_monomial, ne_of_gt hlt]
  · subst k
    simp
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt hgt]
    simp [Polynomial.coeff_monomial, ne_of_lt hgt]

theorem chapterVI_factors_of_homogeneous_are_homogeneous
    {P A B : Trivar} {n : ℕ} (hP : P.IsHomogeneous n) (hPzero : P ≠ 0)
    (hfactor : P = A * B) :
    ∃ aDegree bDegree : ℕ,
      A.IsHomogeneous aDegree ∧ B.IsHomogeneous bDegree ∧
        aDegree + bDegree = n := by
  have hA : A ≠ 0 := by
    intro hzero
    apply hPzero
    simpa [hzero] using hfactor
  have hB : B ≠ 0 := by
    intro hzero
    apply hPzero
    simpa [hzero] using hfactor
  let SA := chapterVIHomogeneousScaling A
  let SB := chapterVIHomogeneousScaling B
  have hSA : SA ≠ 0 := chapterVI_homogeneousScaling_injective.ne hA
  have hSB : SB ≠ 0 := chapterVI_homogeneousScaling_injective.ne hB
  have hscaled : Polynomial.monomial n P = SA * SB := by
    rw [← chapterVI_homogeneousScaling_of_isHomogeneous hP]
    simpa [SA, SB] using congrArg chapterVIHomogeneousScaling hfactor
  have hdegreeSum : SA.natDegree + SB.natDegree = n := by
    rw [← Polynomial.natDegree_mul hSA hSB, ← hscaled,
      Polynomial.natDegree_monomial]
    simp [hPzero]
  have htrailingSum : SA.natTrailingDegree + SB.natTrailingDegree = n := by
    rw [← Polynomial.natTrailingDegree_mul hSA hSB, ← hscaled,
      Polynomial.natTrailingDegree_monomial hPzero]
  have hSATrailing : SA.natTrailingDegree = SA.natDegree := by
    have hleA := Polynomial.natTrailingDegree_le_natDegree SA
    have hleB := Polynomial.natTrailingDegree_le_natDegree SB
    omega
  have hSBTrailing : SB.natTrailingDegree = SB.natDegree := by
    have hleA := Polynomial.natTrailingDegree_le_natDegree SA
    have hleB := Polynomial.natTrailingDegree_le_natDegree SB
    omega
  have hSAmonomial :=
    chapterVI_polynomial_eq_monomial_of_natTrailingDegree_eq_natDegree SA hSA hSATrailing
  have hSBmonomial :=
    chapterVI_polynomial_eq_monomial_of_natTrailingDegree_eq_natDegree SB hSB hSBTrailing
  have hSALeading : SA.leadingCoeff = A := by
    have := congrArg (Polynomial.eval 1) hSAmonomial
    symm
    simpa [SA, chapterVI_homogeneousScaling_eval_one] using this
  have hSBLeading : SB.leadingCoeff = B := by
    have := congrArg (Polynomial.eval 1) hSBmonomial
    symm
    simpa [SB, chapterVI_homogeneousScaling_eval_one] using this
  refine ⟨SA.natDegree, SB.natDegree, ?_, ?_, hdegreeSum⟩
  · apply chapterVI_isHomogeneous_of_homogeneousScaling_eq
    simpa only [SA, hSALeading] using hSAmonomial
  · apply chapterVI_isHomogeneous_of_homogeneousScaling_eq
    simpa only [SB, hSBLeading] using hSBmonomial

def chapterVIProjectToBivar (d : Fin 3 →₀ ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 (d 0) + Finsupp.single 1 (d 1)

private theorem chapterVI_dehomogenize_monomial
    (d : Fin 3 →₀ ℕ) (c : ℂ) :
    chapterVIDehomogenizeZ (MvPolynomial.monomial d c) =
      MvPolynomial.monomial (chapterVIProjectToBivar d) c := by
  simp [chapterVIDehomogenizeZ, chapterVIProjectToBivar,
    MvPolynomial.monomial_eq, Finsupp.prod_fintype, Fin.prod_univ_succ]

theorem chapterVI_dehomogenize_eq_sum (p : Trivar) :
    chapterVIDehomogenizeZ p =
      ∑ d ∈ p.support,
        MvPolynomial.monomial (chapterVIProjectToBivar d)
          (MvPolynomial.coeff d p) := by
  calc
    chapterVIDehomogenizeZ p =
        chapterVIDehomogenizeZ
          (∑ d ∈ p.support, MvPolynomial.monomial d (MvPolynomial.coeff d p)) :=
      congrArg chapterVIDehomogenizeZ p.as_sum
    _ = _ := by
      simp only [map_sum, chapterVI_dehomogenize_monomial]

private theorem chapterVI_projectToBivar_injective_at_degree
    {d e : Fin 3 →₀ ℕ} (hdegree : d.degree = e.degree)
    (hproject : chapterVIProjectToBivar d = chapterVIProjectToBivar e) :
    d = e := by
  have h0 : d 0 = e 0 := by
    simpa [chapterVIProjectToBivar] using congrArg (fun m : Fin 2 →₀ ℕ ↦ m 0) hproject
  have h1 : d 1 = e 1 := by
    simpa [chapterVIProjectToBivar] using congrArg (fun m : Fin 2 →₀ ℕ ↦ m 1) hproject
  have hdDegree : d.degree = d 0 + d 1 + d 2 := by
    rw [Finsupp.degree_eq_sum]
    simp [Fin.sum_univ_succ, Nat.add_assoc]
  have heDegree : e.degree = e 0 + e 1 + e 2 := by
    rw [Finsupp.degree_eq_sum]
    simp [Fin.sum_univ_succ, Nat.add_assoc]
  have h2 : d (2 : Fin 3) = e 2 := by omega
  ext i
  fin_cases i
  · exact h0
  · exact h1
  · simpa using h2

private theorem chapterVI_coeff_dehomogenize_of_homogeneous
    {p : Trivar} {n : ℕ} (hp : p.IsHomogeneous n)
    (d : Fin 3 →₀ ℕ) (hd : MvPolynomial.coeff d p ≠ 0) :
    MvPolynomial.coeff (chapterVIProjectToBivar d)
        (chapterVIDehomogenizeZ p) = MvPolynomial.coeff d p := by
  rw [chapterVI_dehomogenize_eq_sum, MvPolynomial.coeff_sum]
  rw [Finset.sum_eq_single d]
  · simp [MvPolynomial.coeff_monomial]
  · intro e he hed
    have hecoeff : MvPolynomial.coeff e p ≠ 0 :=
      MvPolynomial.mem_support_iff.mp he
    have hedegree : e.degree = n := by
      rw [Finsupp.degree_eq_weight_one]
      exact hp hecoeff
    have hddegree : d.degree = n := by
      rw [Finsupp.degree_eq_weight_one]
      exact hp hd
    by_cases hproject : chapterVIProjectToBivar e = chapterVIProjectToBivar d
    · exact False.elim (hed (chapterVI_projectToBivar_injective_at_degree
        (hedegree.trans hddegree.symm) hproject))
    · simp [MvPolynomial.coeff_monomial, hproject]
  · intro hnot
    exact False.elim (hnot (MvPolynomial.mem_support_iff.mpr hd))

private theorem chapterVI_X2_dvd_of_homogeneous_dehomogenize_isUnit
    {p : Trivar} {n : ℕ} (hp : p.IsHomogeneous n)
    (hn : 0 < n) (hunit : IsUnit (chapterVIDehomogenizeZ p)) :
    MvPolynomial.X (2 : Fin 3) ∣ p := by
  obtain ⟨c, hc, hconstant⟩ :=
    MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp hunit
  rw [p.as_sum]
  apply Finset.dvd_sum
  intro d hd
  rw [MvPolynomial.X_dvd_monomial]
  right
  by_contra hd2
  have hdcoeff : MvPolynomial.coeff d p ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hd
  have hddegree : d.degree = n := by
    rw [Finsupp.degree_eq_weight_one]
    exact hp hdcoeff
  have hproject : chapterVIProjectToBivar d ≠ 0 := by
    intro hzero
    have hd0 : d 0 = 0 := by
      simpa [chapterVIProjectToBivar] using
        congrArg (fun m : Fin 2 →₀ ℕ ↦ m 0) hzero
    have hd1 : d 1 = 0 := by
      simpa [chapterVIProjectToBivar] using
        congrArg (fun m : Fin 2 →₀ ℕ ↦ m 1) hzero
    have hdDegree' : d.degree = d 0 + d 1 + d 2 := by
      rw [Finsupp.degree_eq_sum]
      simp [Fin.sum_univ_succ, Nat.add_assoc]
    omega
  have hcoefficient :=
    chapterVI_coeff_dehomogenize_of_homogeneous hp d hdcoeff
  rw [hconstant] at hcoefficient
  have hproject' : (0 : Fin 2 →₀ ℕ) ≠ chapterVIProjectToBivar d :=
    Ne.symm hproject
  simp [hproject'] at hcoefficient
  exact hdcoeff hcoefficient.symm

theorem chapterVI_section103ProjectivePolynomial_ne_zero :
    chapterVISection103ProjectivePolynomial ≠ 0 := by
  intro hzero
  have himage := congrArg chapterVIDehomogenizeZ hzero
  rw [chapterVI_dehomogenize_section103ProjectivePolynomial, map_zero] at himage
  exact chapterVI_section103Polynomial_ne_zero himage

private theorem chapterVI_projectiveMonomial_inj {a b c d : ℕ} :
    chapterVIProjectiveMonomial a b = chapterVIProjectiveMonomial c d ↔
      a = c ∧ b = d := by
  constructor
  · intro h
    constructor
    · simpa [chapterVIProjectiveMonomial] using
        congrArg (fun e : Fin 3 →₀ ℕ ↦ e 0) h
    · simpa [chapterVIProjectiveMonomial] using
        congrArg (fun e : Fin 3 →₀ ℕ ↦ e 1) h
  · rintro ⟨rfl, rfl⟩
    rfl

private theorem chapterVI_section103ProjectivePolynomial_coefficient_42_ne_zero :
    MvPolynomial.coeff (chapterVIProjectiveMonomial 4 2)
      chapterVISection103ProjectivePolynomial ≠ 0 := by
  change MvPolynomial.coeff (chapterVIProjectiveMonomial 4 2)
    (∑ a : Fin 5, ∑ b : Fin 5,
      MvPolynomial.monomial (chapterVIProjectiveMonomial a.val b.val)
        (chapterVISection103AffineGaussianCoefficient a b : ℂ)) ≠ 0
  norm_num [MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial,
    chapterVI_projectiveMonomial_inj, chapterVISection103AffineGaussianCoefficient,
    GaussianInt.toComplex_def, Fin.sum_univ_succ]

theorem chapterVI_X2_not_dvd_section103ProjectivePolynomial :
    ¬ MvPolynomial.X (2 : Fin 3) ∣ chapterVISection103ProjectivePolynomial := by
  intro hdvd
  obtain ⟨q, hq⟩ := hdvd
  apply chapterVI_section103ProjectivePolynomial_coefficient_42_ne_zero
  rw [hq, MvPolynomial.coeff_X_mul']
  simp [chapterVIProjectiveMonomial]

private theorem chapterVI_isUnit_of_isHomogeneous_zero
    {p : Trivar} (hp : p.IsHomogeneous 0) (hpzero : p ≠ 0) : IsUnit p := by
  have hdegree : p.totalDegree = 0 :=
    (MvPolynomial.totalDegree_zero_iff_isHomogeneous (Fin 3)).mpr hp
  have hconstant : p = MvPolynomial.C (MvPolynomial.coeff 0 p) :=
    MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hdegree
  rw [hconstant] at hpzero ⊢
  simpa using hpzero

/-- The cleared homogeneous sextic defining Poincaré's explicit §103 curve is irreducible.

The proof transfers the affine irreducibility certificate to projective space.  The key point in
the reverse direction is that a positive-degree homogeneous factor whose `z = 1`
dehomogenization is a unit must be divisible by `z`; the displayed sextic has a nonzero `x⁴y²`
coefficient, so `z` does not divide it. -/
theorem chapterVI_section103ProjectivePolynomial_irreducible :
    Irreducible chapterVISection103ProjectivePolynomial := by
  constructor
  · intro hunit
    have hdegreeZero :=
      (MvPolynomial.isUnit_iff_totalDegree_of_isReduced.mp hunit).2
    have hdegreeSix :=
      chapterVI_section103ProjectivePolynomial_isHomogeneous.totalDegree
        chapterVI_section103ProjectivePolynomial_ne_zero
    omega
  · intro A B hfactor
    obtain ⟨aDegree, bDegree, hA, hB, hdegree⟩ :=
      chapterVI_factors_of_homogeneous_are_homogeneous
        chapterVI_section103ProjectivePolynomial_isHomogeneous
        chapterVI_section103ProjectivePolynomial_ne_zero hfactor
    have hAzero : A ≠ 0 := by
      intro hzero
      apply chapterVI_section103ProjectivePolynomial_ne_zero
      simpa [hzero] using hfactor
    have hBzero : B ≠ 0 := by
      intro hzero
      apply chapterVI_section103ProjectivePolynomial_ne_zero
      simpa [hzero] using hfactor
    have hAffineFactor :
        chapterVISection103AffinePolynomial =
          chapterVIDehomogenizeZ A * chapterVIDehomogenizeZ B := by
      calc
        chapterVISection103AffinePolynomial =
            chapterVIDehomogenizeZ chapterVISection103ProjectivePolynomial :=
          chapterVI_dehomogenize_section103ProjectivePolynomial.symm
        _ = chapterVIDehomogenizeZ (A * B) := congrArg chapterVIDehomogenizeZ hfactor
        _ = chapterVIDehomogenizeZ A * chapterVIDehomogenizeZ B :=
          map_mul chapterVIDehomogenizeZ A B
    rcases chapterVI_section103AffinePolynomial_irreducible.isUnit_or_isUnit
        hAffineFactor with hAffineA | hAffineB
    · by_cases ha : aDegree = 0
      · left
        subst aDegree
        exact chapterVI_isUnit_of_isHomogeneous_zero hA hAzero
      · have hXdvdA := chapterVI_X2_dvd_of_homogeneous_dehomogenize_isUnit
          hA (Nat.pos_of_ne_zero ha) hAffineA
        exfalso
        apply chapterVI_X2_not_dvd_section103ProjectivePolynomial
        rw [hfactor]
        exact dvd_mul_of_dvd_left hXdvdA B
    · by_cases hb : bDegree = 0
      · right
        subst bDegree
        exact chapterVI_isUnit_of_isHomogeneous_zero hB hBzero
      · have hXdvdB := chapterVI_X2_dvd_of_homogeneous_dehomogenize_isUnit
          hB (Nat.pos_of_ne_zero hb) hAffineB
        exfalso
        apply chapterVI_X2_not_dvd_section103ProjectivePolynomial
        rw [hfactor]
        exact dvd_mul_of_dvd_right hXdvdB A

end PoincareChapterVI
