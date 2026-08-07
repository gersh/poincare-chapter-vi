/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.Separable
import PoincareChapterVI.Section103.AffineEliminationSoundness
import PoincareChapterVI.Section103.InfinityChartNormalForm

/-!
# The twenty-four finite Section 103 intersections

The exact affine sextic and septic have lexicographic shape basis
`x + h(y), y² q(y)`, where `q` has degree twenty-four, nonzero constant term, and no repeated
root.  Thus the origin is the double affine contribution and the remaining affine intersection
consists of twenty-four distinct points.
-/

noncomputable section

namespace PoincareChapterVI.AffineIntersectionCount

open AffineEliminationData
open AffineEliminationCertificate

private abbrev Bivar := MvPolynomial (Fin 2) ℂ

def embedY : Polynomial ℂ →+* Bivar :=
  Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X 1)

def sparseToPolynomial (polynomial : Sparse) : Polynomial ℂ :=
  (polynomial.map fun term =>
    Polynomial.monomial term.exp.y (Section103Source.qiToComplex term.coeff)).sum

def shapeTailPolynomial : Polynomial ℂ := sparseToPolynomial shapeTail

def residualPolynomialComplex : Polynomial ℂ := sparseToPolynomial residualPolynomial

theorem toMv_eq_embedY_sparseToPolynomial (polynomial : Sparse)
    (hx : ∀ term ∈ polynomial, term.exp.x = 0) :
    toMv polynomial = embedY (sparseToPolynomial polynomial) := by
  induction polynomial with
  | nil => simp [toMv, sparseToPolynomial]
  | cons term rest ih =>
      have hterm : term.exp.x = 0 := hx term (by simp)
      have hrest : ∀ value ∈ rest, value.exp.x = 0 := by
        intro value hvalue
        exact hx value (by simp [hvalue])
      change termToMv term + toMv rest =
        embedY (Polynomial.monomial term.exp.y
          (Section103Source.qiToComplex term.coeff) + sparseToPolynomial rest)
      rw [map_add, ih hrest]
      congr 1
      simp [termToMv, expFinsupp, hterm, embedY,
        Polynomial.coe_eval₂RingHom, Polynomial.eval₂_monomial,
        MvPolynomial.monomial_eq, Finsupp.prod_fintype, Fin.prod_univ_succ]

private theorem shapeTail_has_no_x (term : Term) (hterm : term ∈ shapeTail) :
    term.exp.x = 0 := by
  simp only [shapeTail, List.mem_cons, List.not_mem_nil, or_false] at hterm
  rcases hterm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl
  all_goals rfl

private theorem residualPolynomial_has_no_x (term : Term)
    (hterm : term ∈ residualPolynomial) : term.exp.x = 0 := by
  simp only [residualPolynomial, List.mem_cons, List.not_mem_nil, or_false] at hterm
  rcases hterm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl
  all_goals rfl

theorem toMv_shapePolynomial :
    toMv shapePolynomial = MvPolynomial.X 0 + embedY shapeTailPolynomial := by
  rw [shape_from_tail_mv]
  change toMv (add variableX shapeTail) = _
  rw [toMv_add,
    toMv_eq_embedY_sparseToPolynomial shapeTail shapeTail_has_no_x]
  have hvariableX : toMv variableX = MvPolynomial.X 0 := by
    norm_num [toMv, variableX, termToMv, expFinsupp,
      MvPolynomial.monomial_eq, Finsupp.prod_fintype, Fin.prod_univ_succ]
  rw [hvariableX]
  rfl

theorem toMv_eliminant :
    toMv eliminant = MvPolynomial.X 1 ^ 2 * embedY residualPolynomialComplex := by
  rw [eliminant_from_residual_mv]
  change toMv (mul variableYSquared residualPolynomial) = _
  rw [toMv_mul,
    toMv_eq_embedY_sparseToPolynomial residualPolynomial residualPolynomial_has_no_x]
  have hvariableYSquared : toMv variableYSquared = MvPolynomial.X 1 ^ 2 := by
    norm_num [toMv, variableYSquared, termToMv, expFinsupp,
      MvPolynomial.monomial_eq, Finsupp.prod_fintype, Fin.prod_univ_succ]
  rw [hvariableYSquared]
  rfl

theorem bivarToIterated_termToMv (term : Term) :
    Section103Resultant.bivarToIterated (termToMv term) =
      Polynomial.monomial term.exp.x
        (Polynomial.monomial term.exp.y (Section103Source.qiToComplex term.coeff)) := by
  change Section103Resultant.bivarToIterated
      (MvPolynomial.monomial
        (Section103Resultant.bivarMonomial term.exp.x term.exp.y)
        (Section103Source.qiToComplex term.coeff)) = _
  exact Section103Resultant.bivarToIterated_monomial _ _ _

theorem chapterVIBivariateMonomial_eq_bivarMonomial (a b : ℕ) :
    chapterVIBivariateMonomial a b = Section103Resultant.bivarMonomial a b := by
  change Finsupp.single (0 : Fin 2) a + Finsupp.single 1 b =
    Finsupp.single 0 a + Finsupp.single 1 b
  rfl

theorem toMv_affineSextic :
    toMv affineSextic = chapterVISection103AffinePolynomial := by
  change toMv affineSextic = ∑ a : Fin 5, ∑ b : Fin 5,
    MvPolynomial.monomial (Section103Resultant.bivarMonomial a.val b.val)
      (chapterVISection103AffineGaussianCoefficient a b : ℂ)
  apply InfinityChartNormalForm.bivarToIterated_injective
  simp [toMv, affineSextic, bivarToIterated_termToMv,
    Section103Resultant.bivarToIterated_monomial,
    chapterVISection103AffineGaussianCoefficient, Section103Source.qiToComplex,
    GaussianInt.toComplex_def, Fin.sum_univ_succ]
  ring

theorem toMv_affineSeptic :
    toMv affineSeptic = chapterVISection103ReducedAffinePolynomial := by
  change toMv affineSeptic = ∑ a : Fin 5, ∑ b : Fin 5,
    MvPolynomial.monomial (Section103Resultant.bivarMonomial a.val b.val)
      (chapterVISection103ReducedGaussianCoefficient a b : ℂ)
  apply InfinityChartNormalForm.bivarToIterated_injective
  simp [toMv, affineSeptic, bivarToIterated_termToMv,
    Section103Resultant.bivarToIterated_monomial,
    chapterVISection103ReducedGaussianCoefficient,
    Section103Source.qiToComplex, GaussianInt.toComplex_def,
    Fin.sum_univ_succ]
  ring

theorem shape_basis_identity :
    MvPolynomial.X 0 + embedY shapeTailPolynomial =
      toMv shapeLeft * chapterVISection103AffinePolynomial +
        toMv shapeRight * chapterVISection103ReducedAffinePolynomial := by
  calc
    MvPolynomial.X 0 + embedY shapeTailPolynomial = toMv shapePolynomial :=
      toMv_shapePolynomial.symm
    _ = toMv shapeMembershipLeft := shape_membership_mv.symm
    _ = toMv shapeLeft * chapterVISection103AffinePolynomial +
          toMv shapeRight * chapterVISection103ReducedAffinePolynomial := by
      rw [shapeMembershipLeft, toMv_add, toMv_mul, toMv_mul,
        toMv_affineSextic, toMv_affineSeptic]

theorem eliminant_basis_identity :
    MvPolynomial.X 1 ^ 2 * embedY residualPolynomialComplex =
      toMv eliminantLeft * chapterVISection103AffinePolynomial +
        toMv eliminantRight * chapterVISection103ReducedAffinePolynomial := by
  calc
    MvPolynomial.X 1 ^ 2 * embedY residualPolynomialComplex = toMv eliminant :=
      toMv_eliminant.symm
    _ = toMv eliminantMembershipLeft := eliminant_membership_mv.symm
    _ = toMv eliminantLeft * chapterVISection103AffinePolynomial +
          toMv eliminantRight * chapterVISection103ReducedAffinePolynomial := by
      rw [eliminantMembershipLeft, toMv_add, toMv_mul, toMv_mul,
        toMv_affineSextic, toMv_affineSeptic]

theorem affineSextic_reconstruction :
    chapterVISection103AffinePolynomial =
      toMv sexticQuotientShape *
          (MvPolynomial.X 0 + embedY shapeTailPolynomial) +
        toMv sexticQuotientEliminant *
          (MvPolynomial.X 1 ^ 2 * embedY residualPolynomialComplex) := by
  calc
    chapterVISection103AffinePolynomial = toMv affineSextic := toMv_affineSextic.symm
    _ = toMv sexticReconstructionLeft := sextic_reconstruction_mv.symm
    _ = toMv sexticQuotientShape * toMv shapePolynomial +
          toMv sexticQuotientEliminant * toMv eliminant := by
      rw [sexticReconstructionLeft, toMv_add, toMv_mul, toMv_mul]
    _ = _ := by rw [toMv_shapePolynomial, toMv_eliminant]

theorem affineSeptic_reconstruction :
    chapterVISection103ReducedAffinePolynomial =
      toMv septicQuotientShape *
          (MvPolynomial.X 0 + embedY shapeTailPolynomial) +
        toMv septicQuotientEliminant *
          (MvPolynomial.X 1 ^ 2 * embedY residualPolynomialComplex) := by
  calc
    chapterVISection103ReducedAffinePolynomial = toMv affineSeptic := toMv_affineSeptic.symm
    _ = toMv septicReconstructionLeft := septic_reconstruction_mv.symm
    _ = toMv septicQuotientShape * toMv shapePolynomial +
          toMv septicQuotientEliminant * toMv eliminant := by
      rw [septicReconstructionLeft, toMv_add, toMv_mul, toMv_mul]
    _ = _ := by rw [toMv_shapePolynomial, toMv_eliminant]

theorem eval_embedY (point : Fin 2 → ℂ) (polynomial : Polynomial ℂ) :
    MvPolynomial.eval point (embedY polynomial) = polynomial.eval (point 1) := by
  induction polynomial using Polynomial.induction_on' with
  | add left right hleft hright => simp [hleft, hright]
  | monomial degree coefficient =>
      simp [embedY, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_monomial,
        MvPolynomial.eval_monomial, expFinsupp, Finsupp.prod_fintype,
        Fin.prod_univ_succ]

theorem residualPolynomialComplex_natDegree :
    residualPolynomialComplex.natDegree = 24 := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · unfold residualPolynomialComplex sparseToPolynomial
    simp only [residualPolynomial, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil]
    compute_degree
  · norm_num [residualPolynomialComplex, sparseToPolynomial, residualPolynomial,
      Section103Source.qiToComplex, QuadraticAlgebra.re, QuadraticAlgebra.im,
      Polynomial.coeff_sum, Polynomial.coeff_monomial]

theorem residualPolynomialComplex_coeff_zero_ne_zero :
    residualPolynomialComplex.coeff 0 ≠ 0 := by
  intro hzero
  have hre := congrArg Complex.re hzero
  norm_num [residualPolynomialComplex, sparseToPolynomial, residualPolynomial,
    Section103Source.qiToComplex, QuadraticAlgebra.re, QuadraticAlgebra.im,
    Polynomial.coeff_sum, Polynomial.coeff_monomial] at hre

private abbrev F53 := ZMod 53

private instance : Fact (Nat.Prime 53) := ⟨by decide⟩

def polynomialOfCoefficientList {R : Type*} [Semiring R] :
    List R → Polynomial R
  | [] => 0
  | coefficient :: rest =>
      Polynomial.C coefficient + Polynomial.X * polynomialOfCoefficientList rest

theorem polynomialOfCoefficientList_map {R S : Type*} [Semiring R] [Semiring S]
    (hom : R →+* S) (coefficients : List R) :
    (polynomialOfCoefficientList coefficients).map hom =
      polynomialOfCoefficientList (coefficients.map hom) := by
  induction coefficients with
  | nil => simp [polynomialOfCoefficientList]
  | cons coefficient rest ih =>
      simp [polynomialOfCoefficientList, ih]

theorem polynomialOfCoefficientList_coeff {R : Type*} [Semiring R]
    (coefficients : List R) (degree : ℕ) :
    (polynomialOfCoefficientList coefficients).coeff degree =
      coefficients.getD degree 0 := by
  induction coefficients generalizing degree with
  | nil => simp [polynomialOfCoefficientList]
  | cons coefficient rest ih =>
      cases degree with
      | zero => simp [polynomialOfCoefficientList]
      | succ degree =>
          simpa [polynomialOfCoefficientList, ih] using
            Polynomial.coeff_X_mul (polynomialOfCoefficientList rest) degree

theorem polynomialOfCoefficientList_natDegree_le (R : Type*) [Semiring R]
    (coefficients : List R) :
    (polynomialOfCoefficientList coefficients).natDegree ≤ coefficients.length - 1 := by
  cases coefficients with
  | nil => simp [polynomialOfCoefficientList]
  | cons coefficient rest =>
      rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
      intro degree hdegree
      rw [polynomialOfCoefficientList_coeff]
      exact List.getD_eq_default (l := coefficient :: rest) (d := (0 : R)) (by
        omega)

def addCoefficientLists {R : Type*} [AddMonoid R] : List R → List R → List R
  | [], right => right
  | left, [] => left
  | left :: lefts, right :: rights =>
      (left + right) :: addCoefficientLists lefts rights

def scaleCoefficientList {R : Type*} [Semiring R] (scalar : R) : List R → List R
  | [] => []
  | coefficient :: rest =>
      scalar * coefficient :: scaleCoefficientList scalar rest

theorem scaleCoefficientList_eq_map {R : Type*} [Semiring R]
    (scalar : R) (coefficients : List R) :
    scaleCoefficientList scalar coefficients =
      coefficients.map fun coefficient => scalar * coefficient := by
  induction coefficients with
  | nil => rfl
  | cons coefficient rest ih =>
      simp [scaleCoefficientList, ih]

def multiplyCoefficientLists {R : Type*} [Semiring R] : List R → List R → List R
  | [], _ => []
  | coefficient :: rest, right =>
      addCoefficientLists (scaleCoefficientList coefficient right)
        (0 :: multiplyCoefficientLists rest right)

def weightedCoefficientList {R : Type*} [Semiring R] (weight : ℕ) : List R → List R
  | [] => []
  | coefficient :: rest =>
      (weight : R) * coefficient :: weightedCoefficientList (weight + 1) rest

def derivativeCoefficientList {R : Type*} [Semiring R] : List R → List R
  | [] => []
  | _ :: rest => weightedCoefficientList 1 rest

theorem polynomialOfCoefficientList_add {R : Type*} [CommSemiring R]
    (left right : List R) :
    polynomialOfCoefficientList (addCoefficientLists left right) =
      polynomialOfCoefficientList left + polynomialOfCoefficientList right := by
  induction left generalizing right with
  | nil => simp [addCoefficientLists, polynomialOfCoefficientList]
  | cons left lefts ih =>
      cases right with
      | nil => simp [addCoefficientLists, polynomialOfCoefficientList]
      | cons right rights =>
          simp [addCoefficientLists, polynomialOfCoefficientList, ih]
          ring

theorem polynomialOfCoefficientList_scale {R : Type*} [CommSemiring R]
    (scalar : R) (coefficients : List R) :
    polynomialOfCoefficientList (scaleCoefficientList scalar coefficients) =
      Polynomial.C scalar * polynomialOfCoefficientList coefficients := by
  induction coefficients with
  | nil => simp [scaleCoefficientList, polynomialOfCoefficientList]
  | cons coefficient rest ih =>
      simp [scaleCoefficientList, polynomialOfCoefficientList, ih]
      ring

theorem polynomialOfCoefficientList_multiply {R : Type*} [CommSemiring R]
    (left right : List R) :
    polynomialOfCoefficientList (multiplyCoefficientLists left right) =
      polynomialOfCoefficientList left * polynomialOfCoefficientList right := by
  induction left with
  | nil => simp [multiplyCoefficientLists, polynomialOfCoefficientList]
  | cons coefficient rest ih =>
      rw [multiplyCoefficientLists, polynomialOfCoefficientList_add,
        polynomialOfCoefficientList_scale]
      simp [polynomialOfCoefficientList, ih]
      ring

theorem polynomialOfCoefficientList_weighted {R : Type*} [CommSemiring R]
    (weight : ℕ) (coefficients : List R) :
    polynomialOfCoefficientList (weightedCoefficientList weight coefficients) =
      Polynomial.C (weight : R) * polynomialOfCoefficientList coefficients +
        Polynomial.X * (polynomialOfCoefficientList coefficients).derivative := by
  induction coefficients generalizing weight with
  | nil => simp [weightedCoefficientList, polynomialOfCoefficientList]
  | cons coefficient rest ih =>
      simp [weightedCoefficientList, polynomialOfCoefficientList, ih,
        Polynomial.derivative_add, Polynomial.derivative_mul, Nat.cast_add,
        Nat.cast_one]
      ring

theorem polynomialOfCoefficientList_derivative {R : Type*} [CommSemiring R]
    (coefficients : List R) :
    polynomialOfCoefficientList (derivativeCoefficientList coefficients) =
      (polynomialOfCoefficientList coefficients).derivative := by
  cases coefficients with
  | nil => simp [derivativeCoefficientList, polynomialOfCoefficientList]
  | cons coefficient rest =>
      rw [derivativeCoefficientList, polynomialOfCoefficientList_weighted]
      simp [polynomialOfCoefficientList, Polynomial.derivative_add,
        Polynomial.derivative_mul]

def gaussianResidualPolynomial : Polynomial GaussianInt :=
  polynomialOfCoefficientList (gaussianResidual.map Prod.snd)

def gaussianMod53 : GaussianInt →+* F53 :=
  Zsqrtd.lift ⟨23, by decide⟩

def modularResidualPolynomial : Polynomial F53 :=
  polynomialOfCoefficientList (modularResidual.map fun coefficient => (coefficient : F53))

def modularBezoutLeftPolynomial : Polynomial F53 :=
  polynomialOfCoefficientList (modularBezoutLeft.map fun coefficient => (coefficient : F53))

def modularBezoutRightPolynomial : Polynomial F53 :=
  polynomialOfCoefficientList (modularBezoutRight.map fun coefficient => (coefficient : F53))

def modularResidualCoefficients : List F53 :=
  modularResidual.map fun coefficient => (coefficient : F53)

def modularBezoutLeftCoefficients : List F53 :=
  modularBezoutLeft.map fun coefficient => (coefficient : F53)

def modularBezoutRightCoefficients : List F53 :=
  modularBezoutRight.map fun coefficient => (coefficient : F53)

def modularBezoutCertificateCoefficients : List F53 :=
  addCoefficientLists
    (multiplyCoefficientLists modularBezoutLeftCoefficients modularResidualCoefficients)
    (multiplyCoefficientLists modularBezoutRightCoefficients
      (derivativeCoefficientList modularResidualCoefficients))

set_option maxRecDepth 100000 in
theorem gaussianResidualPolynomial_specializes_mod53 :
    gaussianResidualPolynomial.map gaussianMod53 = modularResidualPolynomial := by
  rw [gaussianResidualPolynomial, polynomialOfCoefficientList_map]
  have hcoefficients :
      (gaussianResidual.map Prod.snd).map gaussianMod53 =
        modularResidual.map fun coefficient => (coefficient : F53) := by
    verified_decide
  simpa [modularResidualPolynomial] using
    congrArg polynomialOfCoefficientList hcoefficients

set_option maxRecDepth 100000 in
theorem modularBezout_coefficient_certificate :
    modularBezoutCertificateCoefficients = 1 :: List.replicate 46 0 := by
  verified_decide

set_option maxRecDepth 100000 in
theorem modularResidual_bezout :
    modularBezoutLeftPolynomial * modularResidualPolynomial +
      modularBezoutRightPolynomial * modularResidualPolynomial.derivative = 1 := by
  have hcertificate := congrArg polynomialOfCoefficientList
    modularBezout_coefficient_certificate
  rw [modularBezoutCertificateCoefficients, polynomialOfCoefficientList_add,
    polynomialOfCoefficientList_multiply, polynomialOfCoefficientList_multiply,
    polynomialOfCoefficientList_derivative] at hcertificate
  simpa [modularBezoutLeftCoefficients, modularBezoutRightCoefficients,
    modularResidualCoefficients, modularBezoutLeftPolynomial,
    modularBezoutRightPolynomial, modularResidualPolynomial,
    polynomialOfCoefficientList, List.replicate_succ] using hcertificate

set_option maxRecDepth 100000 in
theorem modularResidualPolynomial_natDegree :
    modularResidualPolynomial.natDegree = 24 := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · simpa [modularResidualPolynomial, modularResidual] using
      polynomialOfCoefficientList_natDegree_le F53
        (modularResidual.map fun coefficient => (coefficient : F53))
  · rw [modularResidualPolynomial, polynomialOfCoefficientList_coeff]
    norm_num [modularResidual]
    decide

set_option maxRecDepth 100000 in
theorem modularResidualPolynomial_derivative_natDegree :
    modularResidualPolynomial.derivative.natDegree = 23 := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · exact (Polynomial.natDegree_derivative_le _).trans (by
      rw [modularResidualPolynomial_natDegree])
  · rw [Polynomial.coeff_derivative, modularResidualPolynomial,
      polynomialOfCoefficientList_coeff]
    norm_num [modularResidual]
    decide

set_option maxRecDepth 100000 in
theorem gaussianResidualPolynomial_natDegree :
    gaussianResidualPolynomial.natDegree = 24 := by
  apply Nat.le_antisymm
  · simpa [gaussianResidualPolynomial, gaussianResidual] using
      polynomialOfCoefficientList_natDegree_le GaussianInt
        (gaussianResidual.map Prod.snd)
  · have hmap :
        (gaussianResidualPolynomial.map gaussianMod53).natDegree ≤
          gaussianResidualPolynomial.natDegree := Polynomial.natDegree_map_le
    rw [gaussianResidualPolynomial_specializes_mod53,
      modularResidualPolynomial_natDegree] at hmap
    exact hmap

set_option maxRecDepth 100000 in
theorem gaussianResidualPolynomial_derivative_natDegree :
    gaussianResidualPolynomial.derivative.natDegree = 23 := by
  rw [Polynomial.natDegree_derivative, gaussianResidualPolynomial_natDegree]

theorem modularResidual_resultant_ne_zero :
    Polynomial.resultant modularResidualPolynomial
      modularResidualPolynomial.derivative 24 23 ≠ 0 := by
  have hcoprime :
      IsCoprime modularResidualPolynomial modularResidualPolynomial.derivative :=
    ⟨modularBezoutLeftPolynomial, modularBezoutRightPolynomial,
      modularResidual_bezout⟩
  have hresultant := Polynomial.resultant_ne_zero modularResidualPolynomial
    modularResidualPolynomial.derivative hcoprime
  simpa [modularResidualPolynomial_natDegree,
    modularResidualPolynomial_derivative_natDegree] using hresultant

theorem gaussianResidual_resultant_ne_zero :
    Polynomial.resultant gaussianResidualPolynomial
      gaussianResidualPolynomial.derivative 24 23 ≠ 0 := by
  intro hzero
  have hmap := congrArg gaussianMod53 hzero
  rw [← Polynomial.resultant_map_map] at hmap
  rw [gaussianResidualPolynomial_specializes_mod53,
    ← Polynomial.derivative_map,
    gaussianResidualPolynomial_specializes_mod53] at hmap
  exact modularResidual_resultant_ne_zero hmap

def gaussianResidualPolynomialComplex : Polynomial ℂ :=
  gaussianResidualPolynomial.map GaussianInt.toComplex

theorem gaussianResidualComplex_resultant_ne_zero :
    Polynomial.resultant gaussianResidualPolynomialComplex
      gaussianResidualPolynomialComplex.derivative 24 23 ≠ 0 := by
  rw [gaussianResidualPolynomialComplex, Polynomial.derivative_map,
    Polynomial.resultant_map_map]
  simpa using GaussianInt.toComplex_injective.ne
    gaussianResidual_resultant_ne_zero

def residualQIPolynomial : Polynomial AffineEliminationData.QI :=
  polynomialOfCoefficientList (residualPolynomial.reverse.map Term.coeff)

def residualQICoefficients : List AffineEliminationData.QI :=
  residualPolynomial.reverse.map Term.coeff

def gaussianToQI (value : GaussianInt) : AffineEliminationData.QI :=
  ⟨value.re, value.im⟩

def gaussianResidualQICoefficients : List AffineEliminationData.QI :=
  gaussianResidual.map fun term => gaussianToQI term.2

set_option maxRecDepth 100000 in
theorem gaussianResidualQI_scale_certificate :
    gaussianResidualQICoefficients =
      residualQICoefficients.map fun coefficient =>
        (gaussianScale : AffineEliminationData.QI) * coefficient := by
  verified_decide

set_option maxRecDepth 100000 in
theorem qiToComplex_gaussianToQI (value : GaussianInt) :
    Section103Source.qiToComplex (gaussianToQI value) =
      GaussianInt.toComplex value := by
  rw [GaussianInt.toComplex_def]
  change (((value.re : ℤ) : ℂ) + ((value.im : ℤ) : ℂ) * Complex.I) =
    (value.re : ℂ) + (value.im : ℂ) * Complex.I
  norm_num

theorem residualPolynomialComplex_eq_map_residualQI :
    residualPolynomialComplex =
      residualQIPolynomial.map Section103Source.qiToComplex := by
  unfold residualPolynomialComplex sparseToPolynomial residualQIPolynomial
  simp [residualPolynomial, polynomialOfCoefficientList]
  simp only [← Polynomial.C_mul_X_pow_eq_monomial]
  ring

theorem gaussianResidualPolynomialComplex_eq_scale :
    gaussianResidualPolynomialComplex =
      Polynomial.C (gaussianScale : ℂ) * residualPolynomialComplex := by
  have hcoefficients := congrArg
    (List.map Section103Source.qiToComplex)
    gaussianResidualQI_scale_certificate
  have hcomplex :
      (gaussianResidual.map Prod.snd).map GaussianInt.toComplex =
        scaleCoefficientList (gaussianScale : ℂ)
          (residualQICoefficients.map Section103Source.qiToComplex) := by
    simpa [gaussianResidualQICoefficients, residualQICoefficients,
      List.map_map, Function.comp_def, qiToComplex_gaussianToQI,
      scaleCoefficientList_eq_map, List.map_reverse] using hcoefficients
  rw [gaussianResidualPolynomialComplex, gaussianResidualPolynomial,
    polynomialOfCoefficientList_map, hcomplex,
    polynomialOfCoefficientList_scale]
  rw [← polynomialOfCoefficientList_map]
  congr 1
  simpa [residualQIPolynomial, residualQICoefficients] using
    residualPolynomialComplex_eq_map_residualQI.symm

theorem gaussianResidualPolynomialComplex_natDegree :
    gaussianResidualPolynomialComplex.natDegree = 24 := by
  rw [gaussianResidualPolynomialComplex,
    Polynomial.natDegree_map_eq_of_injective GaussianInt.toComplex_injective,
    gaussianResidualPolynomial_natDegree]

theorem gaussianResidualPolynomialComplex_derivative_natDegree :
    gaussianResidualPolynomialComplex.derivative.natDegree = 23 := by
  rw [Polynomial.natDegree_derivative,
    gaussianResidualPolynomialComplex_natDegree]

theorem gaussianResidualPolynomialComplex_isCoprime_derivative :
    IsCoprime gaussianResidualPolynomialComplex
      gaussianResidualPolynomialComplex.derivative := by
  by_contra hnot
  apply gaussianResidualComplex_resultant_ne_zero
  have hnonzero : gaussianResidualPolynomialComplex ≠ 0 := by
    intro hzero
    have hdegree := congrArg Polynomial.natDegree hzero
    simp [gaussianResidualPolynomialComplex_natDegree] at hdegree
  have hresultantZero :
      Polynomial.resultant gaussianResidualPolynomialComplex
        gaussianResidualPolynomialComplex.derivative = 0 :=
    Polynomial.resultant_eq_zero_iff.mpr ⟨Or.inl hnonzero, hnot⟩
  simpa [gaussianResidualPolynomialComplex_natDegree,
    gaussianResidualPolynomialComplex_derivative_natDegree] using hresultantZero

theorem residualPolynomialComplex_separable :
    residualPolynomialComplex.Separable := by
  rw [Polynomial.separable_def]
  have hcoprime := gaussianResidualPolynomialComplex_isCoprime_derivative
  rw [gaussianResidualPolynomialComplex_eq_scale,
    Polynomial.derivative_C_mul] at hcoprime
  have hscale : (gaussianScale : ℂ) ≠ 0 := by
    norm_num [gaussianScale]
  have hscaleUnit : IsUnit (gaussianScale : ℂ) :=
    isUnit_iff_ne_zero.mpr hscale
  exact (isCoprime_mul_unit_left (Polynomial.isUnit_C.mpr hscaleUnit)
    residualPolynomialComplex residualPolynomialComplex.derivative).mp hcoprime

def residualRoots : Finset ℂ := residualPolynomialComplex.roots.toFinset

theorem residualRoots_card : residualRoots.card = 24 := by
  rw [residualRoots,
    Multiset.toFinset_card_of_nodup
      (Polynomial.nodup_roots residualPolynomialComplex_separable),
    IsAlgClosed.card_roots_eq_natDegree,
    residualPolynomialComplex_natDegree]

def residualPoint (root : ℂ) (index : Fin 2) : ℂ :=
  if index = 0 then -shapeTailPolynomial.eval root else root

theorem residualPoint_zero (root : ℂ) :
    residualPoint root 0 = -shapeTailPolynomial.eval root := by
  simp [residualPoint]

theorem residualPoint_one (root : ℂ) : residualPoint root 1 = root := by
  simp [residualPoint]

theorem residualPoint_injective : Function.Injective residualPoint := by
  intro left right hequal
  simpa [residualPoint] using congrFun hequal 1

def finiteIntersectionPoints : Finset (Fin 2 → ℂ) :=
  residualRoots.image residualPoint

theorem finiteIntersectionPoints_card : finiteIntersectionPoints.card = 24 := by
  rw [finiteIntersectionPoints,
    Finset.card_image_of_injective _ residualPoint_injective,
    residualRoots_card]

theorem eval_shape_basis (point : Fin 2 → ℂ) :
    MvPolynomial.eval point
        (MvPolynomial.X 0 + embedY shapeTailPolynomial) =
      point 0 + shapeTailPolynomial.eval (point 1) := by
  simp [eval_embedY]

theorem eval_eliminant_basis (point : Fin 2 → ℂ) :
    MvPolynomial.eval point
        (MvPolynomial.X 1 ^ 2 * embedY residualPolynomialComplex) =
      point 1 ^ 2 * residualPolynomialComplex.eval (point 1) := by
  simp [eval_embedY]

theorem common_zero_iff_shape_and_eliminant (point : Fin 2 → ℂ) :
    MvPolynomial.eval point chapterVISection103AffinePolynomial = 0 ∧
        MvPolynomial.eval point chapterVISection103ReducedAffinePolynomial = 0 ↔
      point 0 + shapeTailPolynomial.eval (point 1) = 0 ∧
        point 1 ^ 2 * residualPolynomialComplex.eval (point 1) = 0 := by
  constructor
  · rintro ⟨hsextic, hseptic⟩
    constructor
    · have hshape := congrArg (MvPolynomial.eval point) shape_basis_identity
      simpa [eval_shape_basis, eval_embedY, hsextic, hseptic] using hshape
    · have heliminant := congrArg (MvPolynomial.eval point) eliminant_basis_identity
      simpa [eval_eliminant_basis, eval_embedY, hsextic, hseptic] using heliminant
  · rintro ⟨hshape, heliminant⟩
    constructor
    · have hsextic := congrArg (MvPolynomial.eval point) affineSextic_reconstruction
      simpa [eval_shape_basis, eval_eliminant_basis, eval_embedY,
        hshape, heliminant] using hsextic
    · have hseptic := congrArg (MvPolynomial.eval point) affineSeptic_reconstruction
      simpa [eval_shape_basis, eval_eliminant_basis, eval_embedY,
        hshape, heliminant] using hseptic

theorem shapeTailPolynomial_eval_zero : shapeTailPolynomial.eval 0 = 0 := by
  norm_num [shapeTailPolynomial, sparseToPolynomial, shapeTail,
    Section103Source.qiToComplex, QuadraticAlgebra.re, QuadraticAlgebra.im]

theorem residualPolynomialComplex_ne_zero : residualPolynomialComplex ≠ 0 := by
  intro hzero
  have hdegree := congrArg Polynomial.natDegree hzero
  simp [residualPolynomialComplex_natDegree] at hdegree

theorem mem_residualRoots_iff (root : ℂ) :
    root ∈ residualRoots ↔ residualPolynomialComplex.eval root = 0 := by
  rw [residualRoots, Multiset.mem_toFinset,
    Polynomial.mem_roots residualPolynomialComplex_ne_zero,
    Polynomial.IsRoot.def]

theorem common_zero_iff_origin_or_finiteIntersectionPoints
    (point : Fin 2 → ℂ) :
    MvPolynomial.eval point chapterVISection103AffinePolynomial = 0 ∧
        MvPolynomial.eval point chapterVISection103ReducedAffinePolynomial = 0 ↔
      point = 0 ∨ point ∈ finiteIntersectionPoints := by
  rw [common_zero_iff_shape_and_eliminant]
  constructor
  · rintro ⟨hshape, heliminant⟩
    rcases mul_eq_zero.mp heliminant with hy | hresidual
    · have hyzero : point 1 = 0 := by
        exact (pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp hy
      have hxzero : point 0 = 0 := by
        simpa [hyzero, shapeTailPolynomial_eval_zero] using hshape
      left
      funext index
      fin_cases index <;> simp [hxzero, hyzero]
    · right
      rw [finiteIntersectionPoints, Finset.mem_image]
      refine ⟨point 1, (mem_residualRoots_iff _).mpr hresidual, ?_⟩
      funext index
      fin_cases index
      · simp [residualPoint]
        exact neg_eq_of_add_eq_zero_right (by simpa [add_comm] using hshape)
      · simp [residualPoint]
  · rintro (rfl | hpoint)
    · constructor
      · simp [shapeTailPolynomial_eval_zero]
      · simp
    · rw [finiteIntersectionPoints, Finset.mem_image] at hpoint
      rcases hpoint with ⟨root, hroot, rfl⟩
      constructor
      · simp [residualPoint]
      · simp [residualPoint, (mem_residualRoots_iff root).mp hroot]

theorem origin_not_mem_finiteIntersectionPoints :
    (0 : Fin 2 → ℂ) ∉ finiteIntersectionPoints := by
  intro horigin
  rw [finiteIntersectionPoints, Finset.mem_image] at horigin
  rcases horigin with ⟨root, hroot, hpoint⟩
  have hrootZero : root = 0 := by
    simpa [residualPoint] using congrFun hpoint 1
  have heval : residualPolynomialComplex.eval 0 = 0 := by
    simpa [hrootZero] using (mem_residualRoots_iff root).mp hroot
  have hcoeff : residualPolynomialComplex.coeff 0 = 0 := by
    rw [Polynomial.coeff_zero_eq_eval_zero]
    exact heval
  exact residualPolynomialComplex_coeff_zero_ne_zero hcoeff

end PoincareChapterVI.AffineIntersectionCount
