/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.Section103.ResultantSoundness
import Mathlib.Algebra.MvPolynomial.Polynomial

/-!
# The certified resultants are those of the geometric chart equations

This file transports the Section 103 resultant certificates from their efficient `ℚ[i]`
representation to the exact complex chart polynomials obtained by dehomogenizing Poincaré's
projective sextic and reduced septic.  In particular, the genuine Mathlib resultants of those
chart equations vanish to order exactly eight in the coordinate transverse to the line at
infinity.

This is an elimination-theoretic statement.  Identifying that order with local intersection
multiplicity is a separate geometric theorem and is not assumed here.
-/

namespace PoincareChapterVI.Section103Resultant

open PoincareChapterVI
open PoincareChapterVI.Section103Source
open Section103Resultant

theorem qi_sexticCoefficient (a b : Fin 5) :
    qiToComplex (sexticCoefficient a b) =
      (chapterVISection103AffineGaussianCoefficient a b : ℂ) := by
  fin_cases a <;> fin_cases b <;>
    norm_num [sexticCoefficient, chapterVISection103AffineGaussianCoefficient,
      qiToComplex, GaussianInt.toComplex_def, QuadraticAlgebra.re, QuadraticAlgebra.im]

theorem qi_reducedCoefficient (a b : Fin 5) :
    qiToComplex (reducedCoefficient a b) =
      (chapterVISection103ReducedGaussianCoefficient a b : ℂ) := by
  fin_cases a <;> fin_cases b <;>
    norm_num [reducedCoefficient, chapterVISection103ReducedGaussianCoefficient,
      qiToComplex, GaussianInt.toComplex_def, QuadraticAlgebra.re, QuadraticAlgebra.im]

theorem sparsePolynomial_zmonomial (n : Nat) (q : QI) :
    sparsePolynomial (zmonomial n q) = Polynomial.monomial n q := by
  by_cases h : q = 0 <;> simp [zmonomial, sparsePolynomial, h]

theorem sparsePolynomial_append (p q : ZSparse) :
    sparsePolynomial (p ++ q) = sparsePolynomial p + sparsePolynomial q := by
  induction p with
  | nil => simp [sparsePolynomial]
  | cons t p ih => simp [sparsePolynomial, ih, add_assoc]

theorem sparsePolynomial_zsum (p : List ZSparse) :
    sparsePolynomial (zsum p) = (p.map sparsePolynomial).sum := by
  induction p with
  | nil => simp [zsum, sparsePolynomial]
  | cons p ps ih =>
      unfold zsum at ih ⊢
      rw [List.flatten_cons, sparsePolynomial_append, List.map_cons, List.sum_cons, ih]

noncomputable def bivarMonomial (a b : Nat) : Fin 2 →₀ Nat :=
  Finsupp.single 0 a + Finsupp.single 1 b

noncomputable def bivarToIterated :
    MvPolynomial (Fin 2) ℂ →+* Polynomial (Polynomial ℂ) :=
  (Polynomial.mapRingHom (MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)).toRingHom).comp
    (MvPolynomial.finSuccEquiv ℂ 1).toRingHom

@[simp] theorem bivarToIterated_C (c : ℂ) :
    bivarToIterated (MvPolynomial.C c) = Polynomial.C (Polynomial.C c) := by
  change Polynomial.map _ ((MvPolynomial.finSuccEquiv ℂ 1) (MvPolynomial.C c)) = _
  rw [MvPolynomial.C_eq_algebraMap,
    (MvPolynomial.finSuccEquiv ℂ 1).commutes c]
  change Polynomial.map _ (Polynomial.C (MvPolynomial.C c)) = _
  rw [Polynomial.map_C]
  congr 1
  simp [MvPolynomial.uniqueAlgEquiv]

@[simp] theorem bivarToIterated_X_zero :
    bivarToIterated (MvPolynomial.X (0 : Fin 2)) = Polynomial.X := by
  simp [bivarToIterated, MvPolynomial.finSuccEquiv_X_zero]

@[simp] theorem bivarToIterated_X_one :
    bivarToIterated (MvPolynomial.X (1 : Fin 2)) = Polynomial.C Polynomial.X := by
  change Polynomial.map _
    ((MvPolynomial.finSuccEquiv ℂ 1) (MvPolynomial.X (Fin.succ 0))) = _
  rw [MvPolynomial.finSuccEquiv_X_succ, Polynomial.map_C]
  simp [MvPolynomial.uniqueAlgEquiv]

theorem bivarToIterated_monomial (a b : Nat) (c : ℂ) :
    bivarToIterated (MvPolynomial.monomial (bivarMonomial a b) c) =
      Polynomial.monomial a (Polynomial.monomial b c) := by
  rw [MvPolynomial.monomial_eq]
  simp only [map_mul, bivarToIterated_C]
  simp [bivarMonomial, Finsupp.prod_fintype, Fin.prod_univ_succ]
  rw [← Polynomial.C_mul_X_pow_eq_monomial,
    ← Polynomial.C_mul_X_pow_eq_monomial]
  rw [map_mul, map_pow]
  ring

noncomputable def xChartSexticIterated : Polynomial (Polynomial ℂ) :=
  bivarToIterated chapterVISection103XInfinitySextic

noncomputable def xChartReducedIterated : Polynomial (Polynomial ℂ) :=
  bivarToIterated chapterVISection103XInfinityReduced

noncomputable def yChartSexticIterated : Polynomial (Polynomial ℂ) :=
  bivarToIterated chapterVISection103YInfinitySextic

noncomputable def yChartReducedIterated : Polynomial (Polynomial ℂ) :=
  bivarToIterated chapterVISection103YInfinityReduced

theorem xChartSexticIterated_eq :
    xChartSexticIterated =
      (assembledPolynomial xSexticCoefficient).map (Polynomial.mapRingHom qiToComplex) := by
  change bivarToIterated
    (∑ a : Fin 5, ∑ b : Fin 5,
      MvPolynomial.monomial (bivarMonomial b.val (6 - a.val - b.val))
        (chapterVISection103AffineGaussianCoefficient a b : ℂ)) = _
  simp [bivarToIterated_monomial, assembledPolynomial, xSexticCoefficient,
    sparsePolynomial_zsum, sparsePolynomial_zmonomial, qi_sexticCoefficient,
    Polynomial.map_monomial, Fin.sum_univ_succ]
  ring

theorem xChartReducedIterated_eq :
    xChartReducedIterated =
      (assembledPolynomial xReducedCoefficient).map (Polynomial.mapRingHom qiToComplex) := by
  change bivarToIterated
    (∑ a : Fin 5, ∑ b : Fin 5,
      MvPolynomial.monomial (bivarMonomial b.val (7 - a.val - b.val))
        (chapterVISection103ReducedGaussianCoefficient a b : ℂ)) = _
  simp [bivarToIterated_monomial, assembledPolynomial, xReducedCoefficient,
    sparsePolynomial_zsum, sparsePolynomial_zmonomial, qi_reducedCoefficient,
    Polynomial.map_monomial, Fin.sum_univ_succ]
  ring

theorem yChartSexticIterated_eq :
    yChartSexticIterated =
      (assembledPolynomial ySexticCoefficient).map (Polynomial.mapRingHom qiToComplex) := by
  change bivarToIterated
    (∑ a : Fin 5, ∑ b : Fin 5,
      MvPolynomial.monomial (bivarMonomial a.val (6 - a.val - b.val))
        (chapterVISection103AffineGaussianCoefficient a b : ℂ)) = _
  simp [bivarToIterated_monomial, assembledPolynomial, ySexticCoefficient,
    sparsePolynomial_zsum, sparsePolynomial_zmonomial, qi_sexticCoefficient,
    Polynomial.map_monomial, Fin.sum_univ_succ]

theorem yChartReducedIterated_eq :
    yChartReducedIterated =
      (assembledPolynomial yReducedCoefficient).map (Polynomial.mapRingHom qiToComplex) := by
  change bivarToIterated
    (∑ a : Fin 5, ∑ b : Fin 5,
      MvPolynomial.monomial (bivarMonomial a.val (7 - a.val - b.val))
        (chapterVISection103ReducedGaussianCoefficient a b : ℂ)) = _
  simp [bivarToIterated_monomial, assembledPolynomial, yReducedCoefficient,
    sparsePolynomial_zsum, sparsePolynomial_zmonomial, qi_reducedCoefficient,
    Polynomial.map_monomial, Fin.sum_univ_succ]

noncomputable def xGeometricChartResultant : Polynomial ℂ :=
  xChartSexticIterated.resultant xChartReducedIterated 4 4

noncomputable def yGeometricChartResultant : Polynomial ℂ :=
  yChartSexticIterated.resultant yChartReducedIterated 4 4

theorem xGeometricChartResultant_eq_map :
    xGeometricChartResultant = xChartResultant.map qiToComplex := by
  rw [xGeometricChartResultant, xChartSexticIterated_eq, xChartReducedIterated_eq,
    Polynomial.resultant_map_map]
  rfl

theorem yGeometricChartResultant_eq_map :
    yGeometricChartResultant = yChartResultant.map qiToComplex := by
  rw [yGeometricChartResultant, yChartSexticIterated_eq, yChartReducedIterated_eq,
    Polynomial.resultant_map_map]
  rfl

theorem qiToComplex_injective : Function.Injective qiToComplex := by
  intro q r h
  apply QuadraticAlgebra.ext
  · have hr := congrArg Complex.re h
    simpa [qiToComplex, Complex.mul_re] using hr
  · have hi := congrArg Complex.im h
    simpa [qiToComplex, Complex.mul_im] using hi

theorem xGeometricChartResultant_natTrailingDegree :
    xGeometricChartResultant.natTrailingDegree = 8 := by
  rw [xGeometricChartResultant_eq_map]
  have hc : (xChartResultant.map qiToComplex).coeff 8 ≠ 0 := by
    rw [Polynomial.coeff_map, xChartResultant_coeff_eight]
    exact (map_ne_zero qiToComplex).2 (by decide)
  apply Nat.le_antisymm (Polynomial.natTrailingDegree_le_of_ne_zero hc)
  apply Polynomial.le_natTrailingDegree
  · exact (Polynomial.map_ne_zero_iff qiToComplex_injective).2 (by
      intro h
      have ht := xChartResultant_natTrailingDegree
      simp [h] at ht)
  · intro n hn
    rw [Polynomial.coeff_map, xChartResultant_coeff_below_eight ⟨n, hn⟩, map_zero]

theorem yGeometricChartResultant_natTrailingDegree :
    yGeometricChartResultant.natTrailingDegree = 8 := by
  rw [yGeometricChartResultant_eq_map]
  have hc : (yChartResultant.map qiToComplex).coeff 8 ≠ 0 := by
    rw [Polynomial.coeff_map, yChartResultant_coeff_eight]
    exact (map_ne_zero qiToComplex).2 (by decide)
  apply Nat.le_antisymm (Polynomial.natTrailingDegree_le_of_ne_zero hc)
  apply Polynomial.le_natTrailingDegree
  · exact (Polynomial.map_ne_zero_iff qiToComplex_injective).2 (by
      intro h
      have ht := yChartResultant_natTrailingDegree
      simp [h] at ht)
  · intro n hn
    rw [Polynomial.coeff_map, yChartResultant_coeff_below_eight ⟨n, hn⟩, map_zero]

end PoincareChapterVI.Section103Resultant
