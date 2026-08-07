/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.Section103.RuppertKernel
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-!
# Bounded polynomial completeness for the Chapter VI Ruppert certificate

Ruppert's bivariate irreducibility criterion uses solutions `(g,h)` with separate-variable
degree bounds `(3,4)` and `(4,2)` for the bidegree-`(4,4)` polynomial occurring in Poincaré's
§103 calculation. `RuppertKernel` proves triviality for an explicit 35-coordinate encoding.
This file proves that the encoding represents every polynomial pair in those boxes and upgrades
the certificate to a theorem quantified over arbitrary bounded bivariate polynomials.
-/

noncomputable section

open scoped BigOperators

namespace PoincareChapterVI

private abbrev Bivar := MvPolynomial (Fin 2) ℂ

private def xVar : Fin 2 := 0
private def yVar : Fin 2 := 1

/-- Separate-variable bidegree bound, stated directly as vanishing of coefficients outside the
rectangle `[0,xDegree] × [0,yDegree]`. -/
def chapterVIHasBidegreeAtMost (xDegree yDegree : Nat) (p : Bivar) : Prop :=
  ∀ d, MvPolynomial.coeff d p ≠ 0 → d xVar ≤ xDegree ∧ d yVar ≤ yDegree

@[simp] theorem chapterVI_bivariateMonomial_apply_zero (a b : Nat) :
    chapterVIBivariateMonomial a b 0 = a := by
  change (Finsupp.single (0 : Fin 2) a + Finsupp.single (1 : Fin 2) b) 0 = a
  simp

@[simp] theorem chapterVI_bivariateMonomial_apply_one (a b : Nat) :
    chapterVIBivariateMonomial a b 1 = b := by
  change (Finsupp.single (0 : Fin 2) a + Finsupp.single (1 : Fin 2) b) 1 = b
  simp

theorem chapterVI_bivariateMonomial_inj {a b c d : Nat} :
    chapterVIBivariateMonomial a b = chapterVIBivariateMonomial c d ↔
      a = c ∧ b = d := by
  constructor
  · intro h
    exact ⟨by simpa using congrArg (fun e ↦ e 0) h,
      by simpa using congrArg (fun e ↦ e 1) h⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem chapterVI_hasBidegreeAtMost_iff_degreeOf (xDegree yDegree : Nat) (p : Bivar) :
    chapterVIHasBidegreeAtMost xDegree yDegree p ↔
      p.degreeOf (0 : Fin 2) ≤ xDegree ∧ p.degreeOf (1 : Fin 2) ≤ yDegree := by
  constructor
  · intro hp
    constructor
    · rw [MvPolynomial.degreeOf_le_iff]
      intro d hd
      exact (hp d (MvPolynomial.mem_support_iff.mp hd)).1
    · rw [MvPolynomial.degreeOf_le_iff]
      intro d hd
      exact (hp d (MvPolynomial.mem_support_iff.mp hd)).2
  · rintro ⟨hx, hy⟩ d hd
    have hmem : d ∈ p.support := MvPolynomial.mem_support_iff.mpr hd
    exact ⟨MvPolynomial.degreeOf_le_iff.mp hx d hmem,
      MvPolynomial.degreeOf_le_iff.mp hy d hmem⟩

theorem chapterVIHasBidegreeAtMost.zero (xDegree yDegree : Nat) :
    chapterVIHasBidegreeAtMost xDegree yDegree (0 : Bivar) := by
  intro d hd
  simp at hd

theorem chapterVIHasBidegreeAtMost.mono {xDegree yDegree xDegree' yDegree' : Nat}
    {p : Bivar} (hp : chapterVIHasBidegreeAtMost xDegree yDegree p)
    (hx : xDegree ≤ xDegree') (hy : yDegree ≤ yDegree') :
    chapterVIHasBidegreeAtMost xDegree' yDegree' p := by
  intro d hd
  exact ⟨(hp d hd).1.trans hx, (hp d hd).2.trans hy⟩

theorem chapterVIHasBidegreeAtMost.mul
    {xDegree yDegree xDegree' yDegree' : Nat} {p q : Bivar}
    (hp : chapterVIHasBidegreeAtMost xDegree yDegree p)
    (hq : chapterVIHasBidegreeAtMost xDegree' yDegree' q) :
    chapterVIHasBidegreeAtMost (xDegree + xDegree') (yDegree + yDegree') (p * q) := by
  rw [chapterVI_hasBidegreeAtMost_iff_degreeOf] at hp hq ⊢
  exact ⟨(MvPolynomial.degreeOf_mul_le 0 p q).trans (Nat.add_le_add hp.1 hq.1),
    (MvPolynomial.degreeOf_mul_le 1 p q).trans (Nat.add_le_add hp.2 hq.2)⟩

theorem chapterVIHasBidegreeAtMost.sub
    {xDegree yDegree : Nat} {p q : Bivar}
    (hp : chapterVIHasBidegreeAtMost xDegree yDegree p)
    (hq : chapterVIHasBidegreeAtMost xDegree yDegree q) :
    chapterVIHasBidegreeAtMost xDegree yDegree (p - q) := by
  rw [chapterVI_hasBidegreeAtMost_iff_degreeOf] at hp hq ⊢
  exact ⟨(MvPolynomial.degreeOf_sub_le 0 p q).trans (max_le hp.1 hq.1),
    (MvPolynomial.degreeOf_sub_le 1 p q).trans (max_le hp.2 hq.2)⟩

theorem chapterVIHasBidegreeAtMost.smul
    {xDegree yDegree : Nat} {p : Bivar}
    (hp : chapterVIHasBidegreeAtMost xDegree yDegree p) (c : ℂ) :
    chapterVIHasBidegreeAtMost xDegree yDegree (c • p) := by
  intro d hd
  rw [MvPolynomial.coeff_smul] at hd
  exact hp d (fun hpzero ↦ hd (by simp [hpzero]))

theorem chapterVIHasBidegreeAtMost.pderiv_x
    {xDegree yDegree : Nat} {p : Bivar}
    (hp : chapterVIHasBidegreeAtMost xDegree yDegree p) :
    chapterVIHasBidegreeAtMost (xDegree - 1) yDegree (MvPolynomial.pderiv 0 p) := by
  intro d hd
  rw [MvPolynomial.coeff_pderiv] at hd
  have hcoefficient : MvPolynomial.coeff (d + Finsupp.single 0 1) p ≠ 0 := by
    intro hzero
    simp [hzero] at hd
  obtain ⟨hx, hy⟩ := hp _ hcoefficient
  simp [xVar, yVar] at hx hy ⊢
  omega

theorem chapterVIHasBidegreeAtMost.pderiv_y
    {xDegree yDegree : Nat} {p : Bivar}
    (hp : chapterVIHasBidegreeAtMost xDegree yDegree p) :
    chapterVIHasBidegreeAtMost xDegree (yDegree - 1) (MvPolynomial.pderiv 1 p) := by
  intro d hd
  rw [MvPolynomial.coeff_pderiv] at hd
  have hcoefficient : MvPolynomial.coeff (d + Finsupp.single 1 1) p ≠ 0 := by
    intro hzero
    simp [hzero] at hd
  obtain ⟨hx, hy⟩ := hp _ hcoefficient
  simp [xVar, yVar] at hx hy ⊢
  omega

theorem chapterVI_pderiv_eq_zero_of_degreeOf_eq_zero
    (i : Fin 2) (p : Bivar) (hdegree : p.degreeOf i = 0) :
    MvPolynomial.pderiv i p = 0 := by
  ext d
  rw [MvPolynomial.coeff_pderiv, MvPolynomial.coeff_zero]
  have hcoefficient : MvPolynomial.coeff (d + Finsupp.single i 1) p = 0 := by
    by_contra hne
    have hmem : d + Finsupp.single i 1 ∈ p.support :=
      MvPolynomial.mem_support_iff.mpr hne
    have hle := MvPolynomial.monomial_le_degreeOf i hmem
    simp [hdegree] at hle
  rw [hcoefficient, zero_mul]

theorem chapterVI_section103Polynomial_bidegreeAtMost :
    chapterVIHasBidegreeAtMost 4 4 chapterVISection103AffinePolynomial := by
  intro d hd
  change MvPolynomial.coeff d
    (∑ a : Fin 5, ∑ b : Fin 5,
      MvPolynomial.monomial (chapterVIBivariateMonomial a.val b.val)
        (chapterVISection103AffineGaussianCoefficient a b : ℂ)) ≠ 0 at hd
  change d 0 ≤ 4 ∧ d 1 ≤ 4
  constructor
  · by_contra hx
    have hx' : 4 < d 0 := by omega
    apply hd
    simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
    apply Finset.sum_eq_zero
    intro a _
    apply Finset.sum_eq_zero
    intro b _
    split_ifs with heq
    · have heval := congrArg (fun e ↦ e 0) heq
      simp at heval
      omega
    · rfl
  · by_contra hy
    have hy' : 4 < d 1 := by omega
    apply hd
    simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
    apply Finset.sum_eq_zero
    intro a _
    apply Finset.sum_eq_zero
    intro b _
    split_ifs with heq
    · have heval := congrArg (fun e ↦ e 1) heq
      simp at heval
      omega
    · rfl

theorem chapterVI_section103Polynomial_coefficient_42_ne_zero :
    MvPolynomial.coeff (chapterVIBivariateMonomial 4 2)
      chapterVISection103AffinePolynomial ≠ 0 := by
  change MvPolynomial.coeff (chapterVIBivariateMonomial 4 2)
    (∑ a : Fin 5, ∑ b : Fin 5,
      MvPolynomial.monomial (chapterVIBivariateMonomial a.val b.val)
        (chapterVISection103AffineGaussianCoefficient a b : ℂ)) ≠ 0
  norm_num [MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial,
    chapterVI_bivariateMonomial_inj, chapterVISection103AffineGaussianCoefficient,
    GaussianInt.toComplex_def, Fin.sum_univ_succ]

theorem chapterVI_section103Polynomial_coefficient_24_ne_zero :
    MvPolynomial.coeff (chapterVIBivariateMonomial 2 4)
      chapterVISection103AffinePolynomial ≠ 0 := by
  change MvPolynomial.coeff (chapterVIBivariateMonomial 2 4)
    (∑ a : Fin 5, ∑ b : Fin 5,
      MvPolynomial.monomial (chapterVIBivariateMonomial a.val b.val)
        (chapterVISection103AffineGaussianCoefficient a b : ℂ)) ≠ 0
  norm_num [MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial,
    chapterVI_bivariateMonomial_inj, chapterVISection103AffineGaussianCoefficient,
    GaussianInt.toComplex_def, Fin.sum_univ_succ]

theorem chapterVI_section103Polynomial_degreeOf_x :
    chapterVISection103AffinePolynomial.degreeOf (0 : Fin 2) = 4 := by
  apply Nat.le_antisymm
  · exact (chapterVI_hasBidegreeAtMost_iff_degreeOf 4 4 _).mp
      chapterVI_section103Polynomial_bidegreeAtMost |>.1
  · have hmem : chapterVIBivariateMonomial 4 2 ∈
        chapterVISection103AffinePolynomial.support :=
      MvPolynomial.mem_support_iff.mpr
        chapterVI_section103Polynomial_coefficient_42_ne_zero
    simpa using MvPolynomial.monomial_le_degreeOf
      (f := chapterVISection103AffinePolynomial) 0 hmem

theorem chapterVI_section103Polynomial_degreeOf_y :
    chapterVISection103AffinePolynomial.degreeOf (1 : Fin 2) = 4 := by
  apply Nat.le_antisymm
  · exact (chapterVI_hasBidegreeAtMost_iff_degreeOf 4 4 _).mp
      chapterVI_section103Polynomial_bidegreeAtMost |>.2
  · have hmem : chapterVIBivariateMonomial 2 4 ∈
        chapterVISection103AffinePolynomial.support :=
      MvPolynomial.mem_support_iff.mpr
        chapterVI_section103Polynomial_coefficient_24_ne_zero
    simpa using MvPolynomial.monomial_le_degreeOf
      (f := chapterVISection103AffinePolynomial) 1 hmem

theorem chapterVI_section103Polynomial_ne_zero :
    chapterVISection103AffinePolynomial ≠ 0 := by
  intro hzero
  apply chapterVI_section103Polynomial_coefficient_42_ne_zero
  rw [hzero]
  exact MvPolynomial.coeff_zero _

theorem chapterVI_factor_degree_sums
    (a b : Bivar) (ha : a ≠ 0) (hb : b ≠ 0)
    (hfactor : chapterVISection103AffinePolynomial = a * b) :
    a.degreeOf 0 + b.degreeOf 0 = 4 ∧ a.degreeOf 1 + b.degreeOf 1 = 4 := by
  constructor
  · rw [← MvPolynomial.degreeOf_mul_eq ha hb, ← hfactor,
      chapterVI_section103Polynomial_degreeOf_x]
  · rw [← MvPolynomial.degreeOf_mul_eq ha hb, ← hfactor,
      chapterVI_section103Polynomial_degreeOf_y]

theorem chapterVI_factor_xDerivative_bidegree
    (a b : Bivar) (ha : a ≠ 0) (hb : b ≠ 0)
    (hfactor : chapterVISection103AffinePolynomial = a * b) :
    chapterVIHasBidegreeAtMost 3 4 (b * MvPolynomial.pderiv 0 a) := by
  let ax := a.degreeOf (0 : Fin 2)
  let ay := a.degreeOf (1 : Fin 2)
  let bx := b.degreeOf (0 : Fin 2)
  let bY := b.degreeOf (1 : Fin 2)
  have haBound : chapterVIHasBidegreeAtMost ax ay a :=
    (chapterVI_hasBidegreeAtMost_iff_degreeOf ax ay a).mpr ⟨le_rfl, le_rfl⟩
  have hbBound : chapterVIHasBidegreeAtMost bx bY b :=
    (chapterVI_hasBidegreeAtMost_iff_degreeOf bx bY b).mpr ⟨le_rfl, le_rfl⟩
  obtain ⟨hdegreeX, hdegreeY⟩ := chapterVI_factor_degree_sums a b ha hb hfactor
  change ax + bx = 4 at hdegreeX
  change ay + bY = 4 at hdegreeY
  by_cases hax : ax = 0
  · have hderiv : MvPolynomial.pderiv 0 a = 0 :=
      chapterVI_pderiv_eq_zero_of_degreeOf_eq_zero 0 a hax
    rw [hderiv, mul_zero]
    exact chapterVIHasBidegreeAtMost.zero 3 4
  · have hbound := hbBound.mul haBound.pderiv_x
    apply hbound.mono <;> omega

theorem chapterVI_factor_yDerivative_bidegree
    (a b : Bivar) (ha : a ≠ 0) (hb : b ≠ 0)
    (hfactor : chapterVISection103AffinePolynomial = a * b) :
    chapterVIHasBidegreeAtMost 4 3 (b * MvPolynomial.pderiv 1 a) := by
  let ax := a.degreeOf (0 : Fin 2)
  let ay := a.degreeOf (1 : Fin 2)
  let bx := b.degreeOf (0 : Fin 2)
  let bY := b.degreeOf (1 : Fin 2)
  have haBound : chapterVIHasBidegreeAtMost ax ay a :=
    (chapterVI_hasBidegreeAtMost_iff_degreeOf ax ay a).mpr ⟨le_rfl, le_rfl⟩
  have hbBound : chapterVIHasBidegreeAtMost bx bY b :=
    (chapterVI_hasBidegreeAtMost_iff_degreeOf bx bY b).mpr ⟨le_rfl, le_rfl⟩
  obtain ⟨hdegreeX, hdegreeY⟩ := chapterVI_factor_degree_sums a b ha hb hfactor
  change ax + bx = 4 at hdegreeX
  change ay + bY = 4 at hdegreeY
  by_cases hay : ay = 0
  · have hderiv : MvPolynomial.pderiv 1 a = 0 :=
      chapterVI_pderiv_eq_zero_of_degreeOf_eq_zero 1 a hay
    rw [hderiv, mul_zero]
    exact chapterVIHasBidegreeAtMost.zero 4 3
  · have hbound := hbBound.mul haBound.pderiv_y
    apply hbound.mono <;> omega

theorem chapterVI_normalizedFactor_preliminary_bidegrees
    (a b : Bivar) (ha : a ≠ 0) (hb : b ≠ 0)
    (hfactor : chapterVISection103AffinePolynomial = a * b) (scalar : ℂ) :
    chapterVIHasBidegreeAtMost 3 4
        (b * MvPolynomial.pderiv 0 a -
          scalar • MvPolynomial.pderiv 0 chapterVISection103AffinePolynomial) ∧
      chapterVIHasBidegreeAtMost 4 3
        (b * MvPolynomial.pderiv 1 a -
          scalar • MvPolynomial.pderiv 1 chapterVISection103AffinePolynomial) := by
  constructor
  · exact (chapterVI_factor_xDerivative_bidegree a b ha hb hfactor).sub
      (chapterVI_section103Polynomial_bidegreeAtMost.pderiv_x.smul scalar)
  · exact (chapterVI_factor_yDerivative_bidegree a b ha hb hfactor).sub
      (chapterVI_section103Polynomial_bidegreeAtMost.pderiv_y.smul scalar)

/-- Encode the coefficients of a candidate Ruppert pair in the same order as the certified
35-column matrix: twenty coefficients of `g`, followed by fifteen coefficients of `h`. -/
def chapterVIRuppertEncode (g h : Bivar) : Fin 35 → ℂ := fun column ↦
  if _hcolumn : column.val < 20 then
    MvPolynomial.coeff
      (chapterVIBivariateMonomial (column.val / 5) (column.val % 5)) g
  else
    MvPolynomial.coeff
      (chapterVIBivariateMonomial ((column.val - 20) / 3) ((column.val - 20) % 3)) h

private theorem chapterVI_ruppertEncode_g_apply (g h : Bivar) (s : Fin 4) (t : Fin 5) :
    chapterVIRuppertEncode g h ⟨s.val * 5 + t.val, by omega⟩ =
      MvPolynomial.coeff (chapterVIBivariateMonomial s.val t.val) g := by
  have hcolumn : s.val * 5 + t.val < 20 := by omega
  simp only [chapterVIRuppertEncode, hcolumn, dite_true]
  congr 2 <;> omega

private theorem chapterVI_ruppertEncode_h_apply (g h : Bivar) (s : Fin 5) (t : Fin 3) :
    chapterVIRuppertEncode g h ⟨20 + s.val * 3 + t.val, by omega⟩ =
      MvPolynomial.coeff (chapterVIBivariateMonomial s.val t.val) h := by
  have hcolumn : ¬ 20 + s.val * 3 + t.val < 20 := by omega
  simp only [chapterVIRuppertEncode, hcolumn, dite_false]
  congr 2 <;> omega

private theorem chapterVI_ruppertG_encode_eq_box (g h : Bivar) :
    chapterVIRuppertGPolynomial (chapterVIRuppertEncode g h) =
      ∑ s : Fin 4, ∑ t : Fin 5,
        MvPolynomial.monomial (chapterVIBivariateMonomial s.val t.val)
          (MvPolynomial.coeff (chapterVIBivariateMonomial s.val t.val) g) := by
  change
    (∑ s : Fin 4, ∑ t : Fin 5,
      MvPolynomial.monomial (chapterVIBivariateMonomial s.val t.val)
        (chapterVIRuppertEncode g h ⟨s.val * 5 + t.val, by omega⟩)) = _
  congr 1
  funext s
  congr 1
  funext t
  rw [chapterVI_ruppertEncode_g_apply]

private theorem chapterVI_bidegreeBox_expansion
    (xDegree yDegree : Nat) (p : Bivar)
    (hp : chapterVIHasBidegreeAtMost xDegree yDegree p) :
    (∑ s : Fin (xDegree + 1), ∑ t : Fin (yDegree + 1),
      MvPolynomial.monomial (chapterVIBivariateMonomial s.val t.val)
        (MvPolynomial.coeff (chapterVIBivariateMonomial s.val t.val) p)) = p := by
  classical
  ext d
  by_cases hd : MvPolynomial.coeff d p = 0
  · simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
    rw [hd]
    apply Finset.sum_eq_zero
    intro s _
    apply Finset.sum_eq_zero
    intro t _
    split_ifs with heq
    · simpa [heq] using hd
    · rfl
  · obtain ⟨hx, hy⟩ := hp d hd
    have hd_eq : d = chapterVIBivariateMonomial (d xVar) (d yVar) := by
      ext i
      fin_cases i <;> simp [xVar, yVar]
    rw [hd_eq]
    let sx : Fin (xDegree + 1) := ⟨d xVar, by omega⟩
    let ty : Fin (yDegree + 1) := ⟨d yVar, by omega⟩
    have hsx (s : Fin (xDegree + 1)) : s.val = d xVar ↔ s = sx := by
      constructor
      · intro hs
        apply Fin.ext
        exact hs
      · rintro rfl
        rfl
    have hty (t : Fin (yDegree + 1)) : t.val = d yVar ↔ t = ty := by
      constructor
      · intro ht
        apply Fin.ext
        exact ht
      · rintro rfl
        rfl
    simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial,
      chapterVI_bivariateMonomial_inj, hsx, hty]
    rw [Finset.sum_eq_single sx]
    · rw [Finset.sum_eq_single ty]
      · simp [sx, ty]
      · intro t _ ht
        simp [ht]
      · simp
    · intro s _ hs
      simp [hs]
    · simp

/-- The first twenty encoded coordinates reconstruct every polynomial in the `(3,4)` box. -/
theorem chapterVI_ruppertG_encode_eq (g h : Bivar)
    (hg : chapterVIHasBidegreeAtMost 3 4 g) :
    chapterVIRuppertGPolynomial (chapterVIRuppertEncode g h) = g := by
  rw [chapterVI_ruppertG_encode_eq_box]
  exact chapterVI_bidegreeBox_expansion 3 4 g hg

private theorem chapterVI_ruppertH_encode_eq_box (g h : Bivar) :
    chapterVIRuppertHPolynomial (chapterVIRuppertEncode g h) =
      ∑ s : Fin 5, ∑ t : Fin 3,
        MvPolynomial.monomial (chapterVIBivariateMonomial s.val t.val)
          (MvPolynomial.coeff (chapterVIBivariateMonomial s.val t.val) h) := by
  change
    (∑ s : Fin 5, ∑ t : Fin 3,
      MvPolynomial.monomial (chapterVIBivariateMonomial s.val t.val)
        (chapterVIRuppertEncode g h ⟨20 + s.val * 3 + t.val, by omega⟩)) = _
  congr 1
  funext s
  congr 1
  funext t
  rw [chapterVI_ruppertEncode_h_apply]

/-- The last fifteen encoded coordinates reconstruct every polynomial in the `(4,2)` box. -/
theorem chapterVI_ruppertH_encode_eq (g h : Bivar)
    (hh : chapterVIHasBidegreeAtMost 4 2 h) :
    chapterVIRuppertHPolynomial (chapterVIRuppertEncode g h) = h := by
  rw [chapterVI_ruppertH_encode_eq_box]
  exact chapterVI_bidegreeBox_expansion 4 2 h hh

/-- The checked 35-column certificate has trivial kernel for every pair of bivariate
polynomials in Ruppert's required degree boxes, not merely for a preselected coefficient
vector. -/
theorem chapterVI_boundedRuppertKernel_trivial (g h : Bivar)
    (hg : chapterVIHasBidegreeAtMost 3 4 g)
    (hh : chapterVIHasBidegreeAtMost 4 2 h)
    (hsolution : chapterVIRuppertExpression
      (MvPolynomial.pderiv (0 : Fin 2)) (MvPolynomial.pderiv (1 : Fin 2))
      chapterVISection103AffinePolynomial g h = 0) :
    g = 0 ∧ h = 0 := by
  let v := chapterVIRuppertEncode g h
  have hG : chapterVIRuppertGPolynomial v = g := chapterVI_ruppertG_encode_eq g h hg
  have hH : chapterVIRuppertHPolynomial v = h := chapterVI_ruppertH_encode_eq g h hh
  have hv : v = 0 := by
    apply chapterVI_encodedRuppertKernel_trivial
    change chapterVIRuppertExpression
      (MvPolynomial.pderiv (0 : Fin 2)) (MvPolynomial.pderiv (1 : Fin 2))
      chapterVISection103AffinePolynomial
      (chapterVIRuppertGPolynomial v) (chapterVIRuppertHPolynomial v) = 0
    rw [hG, hH]
    exact hsolution
  constructor
  · rw [← hG, hv]
    change (∑ s : Fin 4, ∑ t : Fin 5,
      MvPolynomial.monomial (chapterVIBivariateMonomial s.val t.val) 0) = 0
    simp
  · rw [← hH, hv]
    change (∑ s : Fin 5, ∑ t : Fin 3,
      MvPolynomial.monomial (chapterVIBivariateMonomial s.val t.val) 0) = 0
    simp

end PoincareChapterVI
