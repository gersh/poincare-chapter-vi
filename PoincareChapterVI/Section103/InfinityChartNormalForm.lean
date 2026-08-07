/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.Section103.InfinityLocalModel
import PoincareChapterVI.Section103.InfinityNormalFormSoundness
import PoincareChapterVI.Section103.ChartResultant

/-!
# Identification of the two infinity chart ideals with the triangular normal form

The finite certificates are transported to the exact complex chart equations.  Their cofactor
has nonzero value at the chart origin and is therefore a unit in the plane local ring.  This
identifies each two-generator chart ideal with its three-generator triangular local-model ideal.
-/

noncomputable section

namespace PoincareChapterVI.InfinityChartNormalForm

open InfinityNormalFormData
open InfinityNormalFormCertificate
open InfinityLocalModel

private abbrev Bivar := MvPolynomial (Fin 2) ℂ

def xA : ℂ := Section103Source.qiToComplex xCoeff1
def xB : ℂ := Section103Source.qiToComplex xCoeff2
def xC : ℂ := Section103Source.qiToComplex xCoeff3
def xD : ℂ := Section103Source.qiToComplex xCoeff4

def yA : ℂ := Section103Source.qiToComplex yCoeff1
def yB : ℂ := Section103Source.qiToComplex yCoeff2
def yC : ℂ := Section103Source.qiToComplex yCoeff3
def yD : ℂ := Section103Source.qiToComplex yCoeff4

theorem bivarToIterated_injective :
    Function.Injective Section103Resultant.bivarToIterated := by
  intro p q h
  apply (MvPolynomial.finSuccEquiv ℂ 1).injective
  apply Polynomial.map_injective
    (MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)).toRingHom
    (MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)).injective
  exact h

theorem bivarToIterated_termToMv (term : Term) :
    Section103Resultant.bivarToIterated (termToMv term) =
      Polynomial.monomial term.exp.y
        (Polynomial.monomial term.exp.z (Section103Source.qiToComplex term.coeff)) := by
  change Section103Resultant.bivarToIterated
      (MvPolynomial.monomial
        (Section103Resultant.bivarMonomial term.exp.y term.exp.z)
        (Section103Source.qiToComplex term.coeff)) = _
  exact Section103Resultant.bivarToIterated_monomial _ _ _

theorem toMv_xF : toMv xF = chapterVISection103XInfinitySextic := by
  change toMv xF = ∑ a : Fin 5, ∑ b : Fin 5,
    MvPolynomial.monomial
      (Section103Resultant.bivarMonomial b.val (6 - a.val - b.val))
      (chapterVISection103AffineGaussianCoefficient a b : ℂ)
  apply bivarToIterated_injective
  simp [toMv, xF, bivarToIterated_termToMv,
    Section103Resultant.bivarToIterated_monomial,
    chapterVISection103AffineGaussianCoefficient, Section103Source.qiToComplex,
    GaussianInt.toComplex_def, Fin.sum_univ_succ]
  ring

theorem toMv_xG : toMv xG = chapterVISection103XInfinityReduced := by
  change toMv xG = ∑ a : Fin 5, ∑ b : Fin 5,
    MvPolynomial.monomial
      (Section103Resultant.bivarMonomial b.val (7 - a.val - b.val))
      (chapterVISection103ReducedGaussianCoefficient a b : ℂ)
  apply bivarToIterated_injective
  simp [toMv, xG, bivarToIterated_termToMv,
    Section103Resultant.bivarToIterated_monomial,
    chapterVISection103ReducedGaussianCoefficient, Section103Source.qiToComplex,
    GaussianInt.toComplex_def, Fin.sum_univ_succ]
  ring

theorem toMv_yF : toMv yF = chapterVISection103YInfinitySextic := by
  change toMv yF = ∑ a : Fin 5, ∑ b : Fin 5,
    MvPolynomial.monomial
      (Section103Resultant.bivarMonomial a.val (6 - a.val - b.val))
      (chapterVISection103AffineGaussianCoefficient a b : ℂ)
  apply bivarToIterated_injective
  simp [toMv, yF, bivarToIterated_termToMv,
    Section103Resultant.bivarToIterated_monomial,
    chapterVISection103AffineGaussianCoefficient, Section103Source.qiToComplex,
    GaussianInt.toComplex_def, Fin.sum_univ_succ]
  ring

theorem toMv_yG : toMv yG = chapterVISection103YInfinityReduced := by
  change toMv yG = ∑ a : Fin 5, ∑ b : Fin 5,
    MvPolynomial.monomial
      (Section103Resultant.bivarMonomial a.val (7 - a.val - b.val))
      (chapterVISection103ReducedGaussianCoefficient a b : ℂ)
  apply bivarToIterated_injective
  simp [toMv, yG, bivarToIterated_termToMv,
    Section103Resultant.bivarToIterated_monomial,
    chapterVISection103ReducedGaussianCoefficient, Section103Source.qiToComplex,
    GaussianInt.toComplex_def, Fin.sum_univ_succ]
  ring

theorem toMv_xH1 : toMv xH1 = firstRelation xA xB := by
  change toMv xH1 = MvPolynomial.X 0 ^ 2 + MvPolynomial.C xA * MvPolynomial.X 1 ^ 4 +
    MvPolynomial.C xB * MvPolynomial.X 1 ^ 5
  apply bivarToIterated_injective
  simp [toMv, xH1, bivarToIterated_termToMv, xA, xB, xCoeff1, xCoeff2,
    Section103Source.qiToComplex, ← Polynomial.C_mul_X_pow_eq_monomial]
  ring

theorem toMv_xH2 : toMv xH2 = secondRelation xC xD := by
  change toMv xH2 = MvPolynomial.X 0 * MvPolynomial.X 1 ^ 2 +
    MvPolynomial.C xC * MvPolynomial.X 1 ^ 4 +
    MvPolynomial.C xD * MvPolynomial.X 1 ^ 5
  apply bivarToIterated_injective
  simp [toMv, xH2, bivarToIterated_termToMv, xC, xD, xCoeff3, xCoeff4,
    Section103Source.qiToComplex, ← Polynomial.C_mul_X_pow_eq_monomial]
  ring

theorem toMv_xH3 : toMv xH3 = thirdRelation := by
  change toMv xH3 = MvPolynomial.X 1 ^ 6
  apply bivarToIterated_injective
  simp [toMv, xH3, bivarToIterated_termToMv, Section103Source.qiToComplex,
    ← Polynomial.C_mul_X_pow_eq_monomial]

theorem toMv_yH1 : toMv yH1 = firstRelation yA yB := by
  change toMv yH1 = MvPolynomial.X 0 ^ 2 + MvPolynomial.C yA * MvPolynomial.X 1 ^ 4 +
    MvPolynomial.C yB * MvPolynomial.X 1 ^ 5
  apply bivarToIterated_injective
  simp [toMv, yH1, bivarToIterated_termToMv, yA, yB, yCoeff1, yCoeff2,
    Section103Source.qiToComplex, ← Polynomial.C_mul_X_pow_eq_monomial]
  ring

theorem toMv_yH2 : toMv yH2 = secondRelation yC yD := by
  change toMv yH2 = MvPolynomial.X 0 * MvPolynomial.X 1 ^ 2 +
    MvPolynomial.C yC * MvPolynomial.X 1 ^ 4 +
    MvPolynomial.C yD * MvPolynomial.X 1 ^ 5
  apply bivarToIterated_injective
  simp [toMv, yH2, bivarToIterated_termToMv, yC, yD, yCoeff3, yCoeff4,
    Section103Source.qiToComplex, ← Polynomial.C_mul_X_pow_eq_monomial]
  ring

theorem toMv_yH3 : toMv yH3 = thirdRelation := by
  change toMv yH3 = MvPolynomial.X 1 ^ 6
  apply bivarToIterated_injective
  simp [toMv, yH3, bivarToIterated_termToMv, Section103Source.qiToComplex,
    ← Polynomial.C_mul_X_pow_eq_monomial]

theorem xCofactor_eval_zero_ne_zero :
    MvPolynomial.eval (0 : Fin 2 → ℂ) (toMv xCofactor) ≠ 0 := by
  rw [eval_zero_toMv]
  norm_num [coefficient, xCofactor, Section103Source.qiToComplex,
    QuadraticAlgebra.re, QuadraticAlgebra.im, Complex.ext_iff]

theorem yCofactor_eval_zero_ne_zero :
    MvPolynomial.eval (0 : Fin 2 → ℂ) (toMv yCofactor) ≠ 0 := by
  rw [eval_zero_toMv]
  norm_num [coefficient, yCofactor, Section103Source.qiToComplex,
    QuadraticAlgebra.re, QuadraticAlgebra.im, Complex.ext_iff]

theorem x_localized_first_identity :
    toMv xCofactor * firstRelation xA xB =
      toMv xLocalizedLeft1 * chapterVISection103XInfinitySextic +
        toMv xLocalizedRight1 * chapterVISection103XInfinityReduced := by
  simpa [xLocalizedFirstLeft, xLocalizedFirstRight, toMv_add, toMv_mul,
    toMv_xF, toMv_xG, toMv_xH1] using x_localized_first_mv.symm

theorem x_localized_second_identity :
    toMv xCofactor * secondRelation xC xD =
      toMv xLocalizedLeft2 * chapterVISection103XInfinitySextic +
        toMv xLocalizedRight2 * chapterVISection103XInfinityReduced := by
  simpa [xLocalizedSecondLeft, xLocalizedSecondRight, toMv_add, toMv_mul,
    toMv_xF, toMv_xG, toMv_xH2] using x_localized_second_mv.symm

theorem x_localized_third_identity :
    toMv xCofactor * thirdRelation =
      toMv xLocalizedLeft3 * chapterVISection103XInfinitySextic +
        toMv xLocalizedRight3 * chapterVISection103XInfinityReduced := by
  simpa [xLocalizedThirdLeft, xLocalizedThirdRight, toMv_add, toMv_mul,
    toMv_xF, toMv_xG, toMv_xH3] using x_localized_third_mv.symm

theorem y_localized_first_identity :
    toMv yCofactor * firstRelation yA yB =
      toMv yLocalizedLeft1 * chapterVISection103YInfinitySextic +
        toMv yLocalizedRight1 * chapterVISection103YInfinityReduced := by
  simpa [yLocalizedFirstLeft, yLocalizedFirstRight, toMv_add, toMv_mul,
    toMv_yF, toMv_yG, toMv_yH1] using y_localized_first_mv.symm

theorem y_localized_second_identity :
    toMv yCofactor * secondRelation yC yD =
      toMv yLocalizedLeft2 * chapterVISection103YInfinitySextic +
        toMv yLocalizedRight2 * chapterVISection103YInfinityReduced := by
  simpa [yLocalizedSecondLeft, yLocalizedSecondRight, toMv_add, toMv_mul,
    toMv_yF, toMv_yG, toMv_yH2] using y_localized_second_mv.symm

theorem y_localized_third_identity :
    toMv yCofactor * thirdRelation =
      toMv yLocalizedLeft3 * chapterVISection103YInfinitySextic +
        toMv yLocalizedRight3 * chapterVISection103YInfinityReduced := by
  simpa [yLocalizedThirdLeft, yLocalizedThirdRight, toMv_add, toMv_mul,
    toMv_yF, toMv_yG, toMv_yH3] using y_localized_third_mv.symm

theorem x_chart_first_identity :
    chapterVISection103XInfinitySextic =
      toMv xFQuotient1 * firstRelation xA xB +
        (toMv xFQuotient2 * secondRelation xC xD +
          toMv xFQuotient3 * thirdRelation) := by
  simpa [xChartFirstLeft, xChartFirstRight, linearCombination, toMv_add, toMv_mul,
    toMv_xF, toMv_xH1, toMv_xH2, toMv_xH3] using x_chart_first_mv.symm

theorem x_chart_second_identity :
    chapterVISection103XInfinityReduced =
      toMv xGQuotient1 * firstRelation xA xB +
        (toMv xGQuotient2 * secondRelation xC xD +
          toMv xGQuotient3 * thirdRelation) := by
  simpa [xChartSecondLeft, xChartSecondRight, linearCombination, toMv_add, toMv_mul,
    toMv_xG, toMv_xH1, toMv_xH2, toMv_xH3] using x_chart_second_mv.symm

theorem y_chart_first_identity :
    chapterVISection103YInfinitySextic =
      toMv yFQuotient1 * firstRelation yA yB +
        (toMv yFQuotient2 * secondRelation yC yD +
          toMv yFQuotient3 * thirdRelation) := by
  simpa [yChartFirstLeft, yChartFirstRight, linearCombination, toMv_add, toMv_mul,
    toMv_yF, toMv_yH1, toMv_yH2, toMv_yH3] using y_chart_first_mv.symm

theorem y_chart_second_identity :
    chapterVISection103YInfinityReduced =
      toMv yGQuotient1 * firstRelation yA yB +
        (toMv yGQuotient2 * secondRelation yC yD +
          toMv yGQuotient3 * thirdRelation) := by
  simpa [yChartSecondLeft, yChartSecondRight, linearCombination, toMv_add, toMv_mul,
    toMv_yG, toMv_yH1, toMv_yH2, toMv_yH3] using y_chart_second_mv.symm

/-! ## Passage from polynomial certificates to the local ring -/

/-- Exact membership certificates in both directions identify a two-generator chart ideal with
the triangular three-generator ideal after localization.  The common cofactor in the reverse
certificates is invertible because it does not vanish at the center of the chart. -/
theorem localIntersectionIdeal_eq_localModelIdeal_of_certificates
    (a b c d : ℂ)
    (f g H A1 B1 A2 B2 A3 B3
      Qf1 Qf2 Qf3 Qg1 Qg2 Qg3 : PlanePolynomial ℂ)
    (hH : MvPolynomial.eval (0 : Fin 2 → ℂ) H ≠ 0)
    (hh1 : H * firstRelation a b = A1 * f + B1 * g)
    (hh2 : H * secondRelation c d = A2 * f + B2 * g)
    (hh3 : H * thirdRelation = A3 * f + B3 * g)
    (hf : f = Qf1 * firstRelation a b +
      (Qf2 * secondRelation c d + Qf3 * thirdRelation))
    (hg : g = Qg1 * firstRelation a b +
      (Qg2 * secondRelation c d + Qg3 * thirdRelation)) :
    localIntersectionIdeal ℂ 0 f g = localModelIdeal a b c d := by
  let φ : PlanePolynomial ℂ →+* PlaneLocalRing ℂ 0 := algebraMap _ _
  let I := localIntersectionIdeal ℂ 0 f g
  let J := localModelIdeal a b c d
  have hHmem : H ∈ affinePointComplement ℂ 0 := by
    simpa [affinePointComplement, affinePointIdeal, Ideal.primeCompl,
      RingHom.mem_ker] using hH
  have hHunit : IsUnit (φ H) :=
    IsLocalization.map_units (PlaneLocalRing ℂ 0) ⟨H, hHmem⟩
  have hfI : φ f ∈ I := by
    change φ f ∈ Ideal.span {φ f, φ g}
    exact Ideal.subset_span (Set.mem_insert _ _)
  have hgI : φ g ∈ I := by
    change φ g ∈ Ideal.span {φ f, φ g}
    exact Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have h1J : φ (firstRelation a b) ∈ J := by
    exact Ideal.subset_span (Set.mem_insert _ _)
  have h2J : φ (secondRelation c d) ∈ J := by
    exact Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have h3J : φ thirdRelation ∈ J := by
    exact Ideal.subset_span
      (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  apply le_antisymm
  · change I ≤ J
    dsimp only [I, J]
    unfold localIntersectionIdeal
    refine Ideal.span_le.2 ?_
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · rw [hf, map_add, map_mul, map_add, map_mul, map_mul]
      exact J.add_mem (J.mul_mem_left _ h1J)
        (J.add_mem (J.mul_mem_left _ h2J) (J.mul_mem_left _ h3J))
    · rw [hg, map_add, map_mul, map_add, map_mul, map_mul]
      exact J.add_mem (J.mul_mem_left _ h1J)
        (J.add_mem (J.mul_mem_left _ h2J) (J.mul_mem_left _ h3J))
  · change J ≤ I
    dsimp only [I, J]
    unfold localModelIdeal
    refine Ideal.span_le.2 ?_
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · apply (Ideal.unit_mul_mem_iff_mem I hHunit).1
      have mapped := congrArg φ hh1
      simp only [map_mul, map_add] at mapped
      rw [mapped]
      exact I.add_mem (I.mul_mem_left _ hfI) (I.mul_mem_left _ hgI)
    · apply (Ideal.unit_mul_mem_iff_mem I hHunit).1
      have mapped := congrArg φ hh2
      simp only [map_mul, map_add] at mapped
      rw [mapped]
      exact I.add_mem (I.mul_mem_left _ hfI) (I.mul_mem_left _ hgI)
    · apply (Ideal.unit_mul_mem_iff_mem I hHunit).1
      have mapped := congrArg φ hh3
      simp only [map_mul, map_add] at mapped
      rw [mapped]
      exact I.add_mem (I.mul_mem_left _ hfI) (I.mul_mem_left _ hgI)

theorem chapterVI_xInfinity_localIntersectionIdeal_eq_localModelIdeal :
    localIntersectionIdeal ℂ 0 chapterVISection103XInfinitySextic
        chapterVISection103XInfinityReduced = localModelIdeal xA xB xC xD :=
  localIntersectionIdeal_eq_localModelIdeal_of_certificates xA xB xC xD
    chapterVISection103XInfinitySextic chapterVISection103XInfinityReduced
    (toMv xCofactor)
    (toMv xLocalizedLeft1) (toMv xLocalizedRight1)
    (toMv xLocalizedLeft2) (toMv xLocalizedRight2)
    (toMv xLocalizedLeft3) (toMv xLocalizedRight3)
    (toMv xFQuotient1) (toMv xFQuotient2) (toMv xFQuotient3)
    (toMv xGQuotient1) (toMv xGQuotient2) (toMv xGQuotient3)
    xCofactor_eval_zero_ne_zero x_localized_first_identity
    x_localized_second_identity x_localized_third_identity
    x_chart_first_identity x_chart_second_identity

theorem chapterVI_yInfinity_localIntersectionIdeal_eq_localModelIdeal :
    localIntersectionIdeal ℂ 0 chapterVISection103YInfinitySextic
        chapterVISection103YInfinityReduced = localModelIdeal yA yB yC yD :=
  localIntersectionIdeal_eq_localModelIdeal_of_certificates yA yB yC yD
    chapterVISection103YInfinitySextic chapterVISection103YInfinityReduced
    (toMv yCofactor)
    (toMv yLocalizedLeft1) (toMv yLocalizedRight1)
    (toMv yLocalizedLeft2) (toMv yLocalizedRight2)
    (toMv yLocalizedLeft3) (toMv yLocalizedRight3)
    (toMv yFQuotient1) (toMv yFQuotient2) (toMv yFQuotient3)
    (toMv yGQuotient1) (toMv yGQuotient2) (toMv yGQuotient3)
    yCofactor_eval_zero_ne_zero y_localized_first_identity
    y_localized_second_identity y_localized_third_identity
    y_chart_first_identity y_chart_second_identity

/-- The intrinsic local intersection multiplicity at `(1 : 0 : 0)` is eight. -/
theorem chapterVIXInfinityLocalIntersectionMultiplicity_eq_eight :
    chapterVIXInfinityLocalIntersectionMultiplicity = 8 := by
  unfold chapterVIXInfinityLocalIntersectionMultiplicity localIntersectionMultiplicity
    LocalIntersectionAlgebra
  rw [chapterVI_xInfinity_localIntersectionIdeal_eq_localModelIdeal]
  exact localModelIdeal_quotient_length_eq_eight xA xB xC xD

/-- The intrinsic local intersection multiplicity at `(0 : 1 : 0)` is eight. -/
theorem chapterVIYInfinityLocalIntersectionMultiplicity_eq_eight :
    chapterVIYInfinityLocalIntersectionMultiplicity = 8 := by
  unfold chapterVIYInfinityLocalIntersectionMultiplicity localIntersectionMultiplicity
    LocalIntersectionAlgebra
  rw [chapterVI_yInfinity_localIntersectionIdeal_eq_localModelIdeal]
  exact localModelIdeal_quotient_length_eq_eight yA yB yC yD

end PoincareChapterVI.InfinityChartNormalForm
