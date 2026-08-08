/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.ChapterVICurveAlgebra
import PoincareChapterVI.Section103.AffineIntersectionCount
import PoincareChapterVI.Section103.AffineTransversality
import PoincareChapterVI.Section103.LocalIntersection
import PoincareChapterVI.Section103.SingularityParameterTangent

/-!
# The reduced septic as the constant-singularity-value derivative

This file joins three parts of Poincaré's §103 argument:

* the explicit logarithmic differential of his singularity parameter `z(x,y)`;
* the general differentiation identity for `P = ∑ᵢ Uᵢ²`;
* the LeanCompCert-normalized sextic and reduced septic used in the finite intersection proof.

The result identifies every certified finite intersection with a point where the derivative of
the sextic in the constant-`z` direction vanishes.
-/

noncomputable section

namespace PoincareChapterVI.ReducedCurveTangent

open scoped BigOperators
open Section103Source
open AffineIntersectionCount
open AffineTransversality
open SingularityParameterTangent

private abbrev Bivar := MvPolynomial (Fin 2) ℂ

private def sourceAffineCubic (coordinate : Fin 3) : Bivar :=
  chapterVICubicFamily 0 1
    (chapterVISection103CubicCoefficient 0)
    (chapterVISection103CubicCoefficient 1)
    (chapterVISection103CubicCoefficient 2)
    (chapterVISection103CubicCoefficient 3)
    (chapterVISection103CubicCoefficient 4) coordinate

private def sourceAffineCurve : Bivar :=
  chapterVICurvePolynomial sourceAffineCubic

private def sourceAffineFirstOutside : Bivar :=
  MvPolynomial.C (3 : ℂ) * MvPolynomial.C (1 + (1 / 3 : ℂ) ^ 2) *
    (MvPolynomial.X 1 - MvPolynomial.C (1 / 5)) *
    (1 - MvPolynomial.C (1 / 5) * MvPolynomial.X 1)

private def sourceAffineSecondOutside : Bivar :=
  MvPolynomial.C (-2 : ℂ) * MvPolynomial.C (1 + (1 / 5 : ℂ) ^ 2) *
    (MvPolynomial.X 0 - MvPolynomial.C (1 / 3)) *
    (1 - MvPolynomial.C (1 / 3) * MvPolynomial.X 0)

private def sourceAffineFirstReduced (coordinate : Fin 3) : Bivar :=
  chapterVICubicFirstReduced 0
    (chapterVISection103CubicCoefficient 0)
    (chapterVISection103CubicCoefficient 4) coordinate

private def sourceAffineSecondReduced (coordinate : Fin 3) : Bivar :=
  chapterVICubicSecondReduced 1
    (chapterVISection103CubicCoefficient 1)
    (chapterVISection103CubicCoefficient 3) coordinate

private def sourceAffineReduced : Bivar :=
  sourceAffineFirstOutside *
      (∑ coordinate : Fin 3,
        sourceAffineFirstReduced coordinate *
          sourceAffineCubic coordinate) -
    sourceAffineSecondOutside *
      (∑ coordinate : Fin 3,
        sourceAffineSecondReduced coordinate *
          sourceAffineCubic coordinate)

private theorem dehomogenize_sourceCubic (coordinate : Fin 3) :
    chapterVIDehomogenizeZ (sourceCubic coordinate) = sourceAffineCubic coordinate := by
  simp [sourceCubic, sourceAffineCubic, chapterVICubicFamily, chapterVICubicForm,
    mvX, mvY, mvZ, chapterVIDehomogenizeZ]

/-- The compiled source certificate, dehomogenized to the affine chart used for the 24 points. -/
theorem sourceAffineCurve_normalization :
    MvPolynomial.C 50700 * sourceAffineCurve = chapterVISection103AffinePolynomial := by
  have h := congrArg chapterVIDehomogenizeZ
    chapterVISection103_curveSource_eq_projectivePolynomial
  simp only [map_mul] at h
  rw [show chapterVIDehomogenizeZ (MvPolynomial.C 50700) = MvPolynomial.C 50700 by
    simp [chapterVIDehomogenizeZ]] at h
  simpa [sourceAffineCurve, chapterVICurvePolynomial, map_sum, map_pow,
    dehomogenize_sourceCubic,
    chapterVI_dehomogenize_section103ProjectivePolynomial] using h

private theorem dehomogenize_firstOutside :
    chapterVIDehomogenizeZ (MvPolynomial.C 3 * sourceFirstOutside) =
      sourceAffineFirstOutside := by
  simp [sourceFirstOutside, sourceAffineFirstOutside, mvY, mvZ,
    chapterVIDehomogenizeZ]
  ring

private theorem dehomogenize_secondOutside :
    chapterVIDehomogenizeZ (MvPolynomial.C (-2) * sourceSecondOutside) =
      sourceAffineSecondOutside := by
  simp [sourceSecondOutside, sourceAffineSecondOutside, mvX, mvZ,
    chapterVIDehomogenizeZ]
  ring

private theorem dehomogenize_firstReduced (coordinate : Fin 3) :
    chapterVIDehomogenizeZ (sourceFirstReduced coordinate) =
      sourceAffineFirstReduced coordinate := by
  simp [sourceFirstReduced, sourceAffineFirstReduced, chapterVICubicFirstReduced,
    mvX, mvZ, chapterVIDehomogenizeZ]

private theorem dehomogenize_secondReduced (coordinate : Fin 3) :
    chapterVIDehomogenizeZ (sourceSecondReduced coordinate) =
      sourceAffineSecondReduced coordinate := by
  simp [sourceSecondReduced, sourceAffineSecondReduced, chapterVICubicSecondReduced,
    mvY, mvZ, chapterVIDehomogenizeZ]

private theorem dehomogenize_reducedSource :
    chapterVIDehomogenizeZ chapterVISection103ReducedSourcePolynomial =
      sourceAffineReduced := by
  simp only [chapterVISection103ReducedSourcePolynomial, sourceAffineReduced,
    map_sub, map_mul, map_sum, dehomogenize_firstReduced,
    dehomogenize_secondReduced, dehomogenize_sourceCubic]
  rw [← dehomogenize_firstOutside, ← dehomogenize_secondOutside]
  simp only [map_mul]

/-- The existing compiled reduced-curve certificate, dehomogenized to the affine chart. -/
theorem sourceAffineReduced_normalization :
    MvPolynomial.C 438750 * sourceAffineReduced =
      chapterVISection103ReducedAffinePolynomial := by
  have h := congrArg chapterVIDehomogenizeZ
    chapterVISection103_reducedSource_eq_projectivePolynomial
  simp only [map_mul] at h
  rw [show chapterVIDehomogenizeZ (MvPolynomial.C 438750) = MvPolynomial.C 438750 by
    simp [chapterVIDehomogenizeZ]] at h
  simpa [dehomogenize_reducedSource,
    chapterVI_dehomogenize_section103ReducedProjectivePolynomial] using h

/-- Poincaré's exact differentiation-and-reduction identity before clearing coefficients. -/
theorem sourceAffine_derivative_reduction :
    sourceAffineFirstOutside * MvPolynomial.X 0 ^ 2 *
          MvPolynomial.pderiv 0 sourceAffineCurve -
        sourceAffineSecondOutside * MvPolynomial.X 1 ^ 2 *
          MvPolynomial.pderiv 1 sourceAffineCurve =
      2 * MvPolynomial.X 0 * MvPolynomial.X 1 * sourceAffineReduced +
        2 * (sourceAffineFirstOutside * MvPolynomial.X 0 -
          sourceAffineSecondOutside * MvPolynomial.X 1) * sourceAffineCurve := by
  unfold sourceAffineCurve sourceAffineReduced sourceAffineCubic
    sourceAffineFirstReduced sourceAffineSecondReduced
  exact chapterVI_cubicDerivativeCurveEquation_reduction
    (R := ℂ) (0 : Fin 2) (1 : Fin 2) (by decide)
    (chapterVISection103CubicCoefficient 0)
    (chapterVISection103CubicCoefficient 1)
    (chapterVISection103CubicCoefficient 2)
    (chapterVISection103CubicCoefficient 3)
    (chapterVISection103CubicCoefficient 4)
    sourceAffineFirstOutside sourceAffineSecondOutside

private theorem eval_sourceAffineCurve_eq_zero
    (point : Fin 2 → ℂ)
    (hzero : MvPolynomial.eval point chapterVISection103AffinePolynomial = 0) :
    MvPolynomial.eval point sourceAffineCurve = 0 := by
  have h := congrArg (MvPolynomial.eval point) sourceAffineCurve_normalization
  simp only [map_mul, MvPolynomial.eval_C] at h
  rw [hzero] at h
  exact (mul_eq_zero.mp h).resolve_left (by norm_num)

private theorem eval_sourceAffineReduced_eq_zero
    (point : Fin 2 → ℂ)
    (hzero : MvPolynomial.eval point chapterVISection103ReducedAffinePolynomial = 0) :
    MvPolynomial.eval point sourceAffineReduced = 0 := by
  have h := congrArg (MvPolynomial.eval point) sourceAffineReduced_normalization
  simp only [map_mul, MvPolynomial.eval_C] at h
  rw [hzero] at h
  exact (mul_eq_zero.mp h).resolve_left (by norm_num)

private theorem eval_sourceAffine_directionalDerivative_eq_zero
    (point : Fin 2 → ℂ)
    (hcurve : MvPolynomial.eval point chapterVISection103AffinePolynomial = 0)
    (hreduced : MvPolynomial.eval point chapterVISection103ReducedAffinePolynomial = 0) :
    MvPolynomial.eval point (MvPolynomial.pderiv 0 sourceAffineCurve) *
          (constantSingularityTangent (-2) 3 (1 / 3) (1 / 5)
            (point 0) (point 1)).1 +
        MvPolynomial.eval point (MvPolynomial.pderiv 1 sourceAffineCurve) *
          (constantSingularityTangent (-2) 3 (1 / 3) (1 / 5)
            (point 0) (point 1)).2 = 0 := by
  have h := congrArg (MvPolynomial.eval point) sourceAffine_derivative_reduction
  have hsP := eval_sourceAffineCurve_eq_zero point hcurve
  have hsR := eval_sourceAffineReduced_eq_zero point hreduced
  simp only [map_sub, map_mul, map_add, map_pow, MvPolynomial.eval_X,
    MvPolynomial.eval_ofNat, hsP, hsR, mul_zero, add_zero] at h
  have hVx :
      (constantSingularityTangent (-2) 3 (1 / 3) (1 / 5)
        (point 0) (point 1)).1 =
        MvPolynomial.eval point sourceAffineFirstOutside * (point 0) ^ 2 := by
    simp [constantSingularityTangent, sourceAffineFirstOutside]
    norm_num
    ring
  have hVy :
      (constantSingularityTangent (-2) 3 (1 / 3) (1 / 5)
        (point 0) (point 1)).2 =
        -(MvPolynomial.eval point sourceAffineSecondOutside * (point 1) ^ 2) := by
    simp [constantSingularityTangent, sourceAffineSecondOutside]
    norm_num
    ring
  rw [hVx, hVy]
  ring_nf at h ⊢
  exact h

/-- At every common zero of the certified sextic and reduced septic, the derivative of the
certified sextic in Poincaré's polynomial constant-`z` direction vanishes. -/
theorem clearedCurve_constantSingularityTangentDerivative_eq_zero
    (point : Fin 2 → ℂ)
    (hcurve : MvPolynomial.eval point chapterVISection103AffinePolynomial = 0)
    (hreduced : MvPolynomial.eval point chapterVISection103ReducedAffinePolynomial = 0) :
    MvPolynomial.eval point (MvPolynomial.pderiv 0 chapterVISection103AffinePolynomial) *
          (constantSingularityTangent (-2) 3 (1 / 3) (1 / 5)
            (point 0) (point 1)).1 +
        MvPolynomial.eval point (MvPolynomial.pderiv 1 chapterVISection103AffinePolynomial) *
          (constantSingularityTangent (-2) 3 (1 / 3) (1 / 5)
            (point 0) (point 1)).2 = 0 := by
  have hsource := eval_sourceAffine_directionalDerivative_eq_zero point hcurve hreduced
  have hx := congrArg
    (fun polynomial ↦ MvPolynomial.eval point (MvPolynomial.pderiv 0 polynomial))
    sourceAffineCurve_normalization
  have hy := congrArg
    (fun polynomial ↦ MvPolynomial.eval point (MvPolynomial.pderiv 1 polynomial))
    sourceAffineCurve_normalization
  simp only [map_mul, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_C, zero_mul,
    MvPolynomial.eval_C, zero_add] at hx hy
  rw [← hx, ← hy]
  calc
    50700 * MvPolynomial.eval point (MvPolynomial.pderiv 0 sourceAffineCurve) *
          (constantSingularityTangent (-2) 3 (1 / 3) (1 / 5)
            (point 0) (point 1)).1 +
        50700 * MvPolynomial.eval point (MvPolynomial.pderiv 1 sourceAffineCurve) *
          (constantSingularityTangent (-2) 3 (1 / 3) (1 / 5)
            (point 0) (point 1)).2 =
        50700 *
          (MvPolynomial.eval point (MvPolynomial.pderiv 0 sourceAffineCurve) *
              (constantSingularityTangent (-2) 3 (1 / 3) (1 / 5)
                (point 0) (point 1)).1 +
            MvPolynomial.eval point (MvPolynomial.pderiv 1 sourceAffineCurve) *
              (constantSingularityTangent (-2) 3 (1 / 3) (1 / 5)
                (point 0) (point 1)).2) := by ring
    _ = 0 := by rw [hsource, mul_zero]

/-- The preceding derivative identity applies simultaneously to all twenty-four finite points
in Poincaré's intersection argument. -/
theorem finiteIntersectionPoint_constantSingularityTangentDerivative_eq_zero
    (point : Fin 2 → ℂ) (hpoint : point ∈ finiteIntersectionPoints) :
    MvPolynomial.eval point (MvPolynomial.pderiv 0 chapterVISection103AffinePolynomial) *
          (constantSingularityTangent (-2) 3 (1 / 3) (1 / 5)
            (point 0) (point 1)).1 +
        MvPolynomial.eval point (MvPolynomial.pderiv 1 chapterVISection103AffinePolynomial) *
          (constantSingularityTangent (-2) 3 (1 / 3) (1 / 5)
            (point 0) (point 1)).2 = 0 := by
  have hcommon :=
    (common_zero_iff_origin_or_finiteIntersectionPoints point).mpr (Or.inr hpoint)
  exact clearedCurve_constantSingularityTangentDerivative_eq_zero point hcommon.1 hcommon.2

/-- Neither affine coordinate vanishes at any of the twenty-four finite intersections. -/
theorem finiteIntersectionPoint_coordinates_ne_zero
    (point : Fin 2 → ℂ) (hpoint : point ∈ finiteIntersectionPoints) :
    point 0 ≠ 0 ∧ point 1 ≠ 0 := by
  have hy := point_one_ne_zero_of_mem_finiteIntersectionPoints point hpoint
  refine ⟨?_, hy⟩
  intro hx
  have hcurve :=
    (common_zero_iff_origin_or_finiteIntersectionPoints point).mpr (Or.inr hpoint) |>.1
  have hsource := eval_sourceAffineCurve_eq_zero point hcurve
  have hformula :
      MvPolynomial.eval point sourceAffineCurve = (9 / 100 : ℂ) * (point 1) ^ 2 := by
    simp [sourceAffineCurve, sourceAffineCubic, chapterVICurvePolynomial,
      chapterVICubicFamily, chapterVICubicForm,
      chapterVISection103_cubicCoefficient_eq_complexTable,
      chapterVISection103CubicComplexCoefficient, Fin.sum_univ_succ,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
      Matrix.tail_cons, Fin.isValue, hx]
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [hformula] at hsource
  have hyPow : (point 1) ^ 2 = 0 :=
    (mul_eq_zero.mp hsource).resolve_left (by norm_num)
  exact hy ((pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp hyPow)

private theorem sourceSextic_ne_zero_at_logCriticalPair
    (x y : ℂ)
    (hx : x = 1 / 3 ∨ x = 3) (hy : y = 1 / 5 ∨ y = 5) :
    MvPolynomial.eval ![x, y] chapterVISection103AffinePolynomial ≠ 0 := by
  have hsource : MvPolynomial.eval ![x, y] sourceAffineCurve ≠ 0 := by
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
      intro hzero <;> have hre := congrArg Complex.re hzero <;>
      norm_num (config := { maxSteps := 1000000 })
        [sourceAffineCurve, sourceAffineCubic, chapterVICurvePolynomial,
        chapterVICubicFamily, chapterVICubicForm,
        chapterVISection103_cubicCoefficient_eq_complexTable,
        chapterVISection103CubicComplexCoefficient, Fin.sum_univ_succ,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.cons_val_four,
        Matrix.head_cons, Matrix.tail_cons, Fin.isValue,
        pow_two, Complex.mul_re, Complex.mul_im] at hre
  intro hzero
  have hnormalization := congrArg (MvPolynomial.eval ![x, y])
    sourceAffineCurve_normalization
  simp only [map_mul, MvPolynomial.eval_C, hzero] at hnormalization
  exact hsource ((mul_eq_zero.mp hnormalization).resolve_left (by norm_num))

private theorem firstLogCoefficient_zero_iff
    {x : ℂ} (hx : x ≠ 0) :
    halfAngleLogCoefficient (-2) (1 / 3) x = 0 ↔ x = 1 / 3 ∨ x = 3 := by
  unfold halfAngleLogCoefficient
  constructor
  · intro h
    field_simp [hx] at h
    norm_num at h
    rcases h with h | h
    · left
      linear_combination (1 / 3) * h
    · right
      linear_combination -h
  · rintro (rfl | rfl) <;> norm_num

private theorem secondLogCoefficient_zero_iff
    {y : ℂ} (hy : y ≠ 0) :
    halfAngleLogCoefficient 3 (1 / 5) y = 0 ↔ y = 1 / 5 ∨ y = 5 := by
  unfold halfAngleLogCoefficient
  constructor
  · intro h
    field_simp [hy] at h
    norm_num at h
    rcases h with h | h
    · left
      linear_combination (1 / 5) * h
    · right
      linear_combination -h
  · rintro (rfl | rfl) <;> norm_num

/-- Poincaré's logarithmic `dz/z` covector is nonzero at every certified finite point. -/
theorem finiteIntersectionPoint_logDifferential_ne_zero
    (point : Fin 2 → ℂ) (hpoint : point ∈ finiteIntersectionPoints) :
    halfAngleLogCoefficient (-2) (1 / 3) (point 0) ≠ 0 ∨
      halfAngleLogCoefficient 3 (1 / 5) (point 1) ≠ 0 := by
  have hcoordinates := finiteIntersectionPoint_coordinates_ne_zero point hpoint
  by_contra hboth
  push Not at hboth
  have hx := (firstLogCoefficient_zero_iff hcoordinates.1).mp hboth.1
  have hy := (secondLogCoefficient_zero_iff hcoordinates.2).mp hboth.2
  have hcurve :=
    (common_zero_iff_origin_or_finiteIntersectionPoints point).mpr (Or.inr hpoint) |>.1
  have hpointEq : point = ![point 0, point 1] := by
    funext i
    fin_cases i <;> rfl
  rw [hpointEq] at hcurve
  exact sourceSextic_ne_zero_at_logCriticalPair (point 0) (point 1) hx hy hcurve

/-- At a certified singular point, every velocity preserving Poincaré's singularity parameter
is tangent to the sextic.  This is the precise linear-algebra step implicit between `dz = 0`
and equation (2) in §103. -/
theorem finiteIntersectionPoint_curveDerivative_eq_zero_of_logDifferential_eq_zero
    (point velocity : Fin 2 → ℂ) (hpoint : point ∈ finiteIntersectionPoints)
    (hlog : singularityLogDifferential (-2) 3 (1 / 3) (1 / 5)
      (point 0) (point 1) (velocity 0, velocity 1) = 0) :
    MvPolynomial.eval point (MvPolynomial.pderiv 0 chapterVISection103AffinePolynomial) *
          velocity 0 +
        MvPolynomial.eval point (MvPolynomial.pderiv 1 chapterVISection103AffinePolynomial) *
          velocity 1 = 0 := by
  let A := halfAngleLogCoefficient (-2) (1 / 3) (point 0)
  let B := halfAngleLogCoefficient 3 (1 / 5) (point 1)
  let Px := MvPolynomial.eval point
    (MvPolynomial.pderiv 0 chapterVISection103AffinePolynomial)
  let Py := MvPolynomial.eval point
    (MvPolynomial.pderiv 1 chapterVISection103AffinePolynomial)
  let K := (point 0) ^ 2 * (point 1) ^ 2 *
    (1 + (1 / 3 : ℂ) ^ 2) * (1 + (1 / 5 : ℂ) ^ 2)
  have hcoordinates := finiteIntersectionPoint_coordinates_ne_zero point hpoint
  have hK : K ≠ 0 := by
    dsimp [K]
    exact mul_ne_zero
      (mul_ne_zero
        (mul_ne_zero (pow_ne_zero 2 hcoordinates.1) (pow_ne_zero 2 hcoordinates.2))
        (by norm_num))
      (by norm_num)
  have hVx :
      (constantSingularityTangent (-2) 3 (1 / 3) (1 / 5)
        (point 0) (point 1)).1 = K * B := by
    dsimp [K, B]
    unfold constantSingularityTangent halfAngleLogCoefficient
    field_simp [hcoordinates.2]
  have hVy :
      (constantSingularityTangent (-2) 3 (1 / 3) (1 / 5)
        (point 0) (point 1)).2 = -(K * A) := by
    dsimp [K, A]
    unfold constantSingularityTangent halfAngleLogCoefficient
    field_simp [hcoordinates.1]
  have htangent :=
    finiteIntersectionPoint_constantSingularityTangentDerivative_eq_zero point hpoint
  change Px *
      (constantSingularityTangent (-2) 3 (1 / 3) (1 / 5)
        (point 0) (point 1)).1 +
      Py *
      (constantSingularityTangent (-2) 3 (1 / 3) (1 / 5)
        (point 0) (point 1)).2 = 0 at htangent
  rw [hVx, hVy] at htangent
  have hcross : Px * B - Py * A = 0 := by
    apply (mul_eq_zero.mp ?_).resolve_left hK
    linear_combination htangent
  change A * velocity 0 + B * velocity 1 = 0 at hlog
  change Px * velocity 0 + Py * velocity 1 = 0
  rcases finiteIntersectionPoint_logDifferential_ne_zero point hpoint with hA | hB
  · change A ≠ 0 at hA
    apply (mul_eq_zero.mp ?_).resolve_left hA
    linear_combination Px * hlog - velocity 1 * hcross
  · change B ≠ 0 at hB
    apply (mul_eq_zero.mp ?_).resolve_left hB
    linear_combination Py * hlog + velocity 0 * hcross

end PoincareChapterVI.ReducedCurveTangent
