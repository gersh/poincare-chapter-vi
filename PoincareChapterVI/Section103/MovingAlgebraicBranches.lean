/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.Section103.ReducedCurveTangent
import PoincareChapterVI.Section103.RotationFamily
import PoincareChapterVI.Section103.SingularBranches
import Mathlib.Analysis.Analytic.Polynomial

/-!
# Moving algebraic branches in Poincaré's Section 103 argument

This file constructs the two moving algebraic equations to which the complex implicit-function
theorem is applied.  The first is the squared-distance sextic of the genuine Cayley rotation
family.  The second is Poincaré's reduced degree-seven equation, formed from the same moving
cubic coefficients.  At the base configuration the two equations are exactly the certified
integer polynomials whose twenty-four finite intersections were proved transverse.
-/

noncomputable section

namespace PoincareChapterVI.MovingAlgebraicBranches

open scoped BigOperators
open Section103Source
open AffineIntersectionCount
open AffineTransversality
open RotationSource
open RotationFamily
open SingularBranches
open SingularityParameterTangent
open ReducedCurveTangent

private abbrev Bivar := MvPolynomial (Fin 2) ℂ

-- Keep the overlapping complex calculus instances coherent on Lean 4.33-rc2.
@[reducible] local instance (priority := 20000) complexNormedAddCommGroupForCalculus :
    NormedAddCommGroup ℂ :=
  { Complex.instNormedAddCommGroup with
    toAddCommGroup :=
      DenselyNormedField.toNontriviallyNormedField.toDivisionRing.toAddCommGroup }

@[reducible] local instance (priority := 20000) complexAddCommGroupForCalculus :
    AddCommGroup ℂ :=
  complexNormedAddCommGroupForCalculus.toAddCommGroup

attribute [local instance 20000] NormedAlgebra.toNormedSpace NormedSpace.toModule

private theorem complexAddCommGroupForCalculus_eq_field :
    complexAddCommGroupForCalculus =
      DenselyNormedField.toNontriviallyNormedField.toDivisionRing.toAddCommGroup := by
  rfl

/-- Evaluation of a bivariate polynomial on product coordinates. -/
def evalPair (polynomial : Bivar) (fiber : Fiber) : ℂ :=
  MvPolynomial.eval ![fiber.1, fiber.2] polynomial

/-- The gradient of a bivariate polynomial, represented as a continuous linear map on product
coordinates. -/
def polynomialGradient (polynomial : Bivar) (fiber : Fiber) : Fiber →L[ℂ] ℂ :=
  let point : Fin 2 → ℂ := ![fiber.1, fiber.2]
  let dx := MvPolynomial.eval point (MvPolynomial.pderiv 0 polynomial)
  let dy := MvPolynomial.eval point (MvPolynomial.pderiv 1 polynomial)
  ({ toFun := fun velocity ↦ dx * velocity.1 + dy * velocity.2
     map_add' := by
       intro left right
       dsimp
       ring
     map_smul' := by
       intro scalar velocity
       dsimp
       ring } : Fiber →ₗ[ℂ] ℂ).toContinuousLinearMap

@[simp] theorem polynomialGradient_apply (polynomial : Bivar)
    (fiber velocity : Fiber) :
    polynomialGradient polynomial fiber velocity =
      MvPolynomial.eval ![fiber.1, fiber.2] (MvPolynomial.pderiv 0 polynomial) *
          velocity.1 +
        MvPolynomial.eval ![fiber.1, fiber.2] (MvPolynomial.pderiv 1 polynomial) *
          velocity.2 :=
  rfl

/-- Exact Fréchet derivative of multivariate-polynomial evaluation in the two affine
coordinates. -/
theorem hasFDerivAt_evalPair (polynomial : Bivar) (fiber : Fiber) :
    HasFDerivAt (evalPair polynomial) (polynomialGradient polynomial fiber) fiber := by
  induction polynomial using MvPolynomial.induction_on with
  | C constant =>
      have hgradient : polynomialGradient (MvPolynomial.C constant) fiber = 0 := by
        apply ContinuousLinearMap.ext
        intro velocity
        simp [polynomialGradient]
      rw [hgradient]
      exact (hasFDerivAt_const constant fiber :
          HasFDerivAt (fun _ : Fiber ↦ constant) (0 : Fiber →L[ℂ] ℂ) fiber)
        |>.congr_of_eventuallyEq (Filter.Eventually.of_forall fun point ↦ by
          simp [evalPair])
  | add left right hleft hright =>
      have hgradient : polynomialGradient (left + right) fiber =
          polynomialGradient left fiber + polynomialGradient right fiber := by
        apply ContinuousLinearMap.ext
        intro velocity
        simp [polynomialGradient]
        ring
      rw [hgradient]
      exact (hleft.add hright).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun point ↦ by simp [evalPair])
  | mul_X polynomial index hpolynomial =>
      fin_cases index
      · change HasFDerivAt
          (evalPair (polynomial * MvPolynomial.X (0 : Fin 2)))
          (polynomialGradient (polynomial * MvPolynomial.X (0 : Fin 2)) fiber) fiber
        have hgradient :
            polynomialGradient (polynomial * MvPolynomial.X (0 : Fin 2)) fiber =
              evalPair polynomial fiber • ContinuousLinearMap.fst ℂ ℂ ℂ +
                fiber.1 • polynomialGradient polynomial fiber := by
          apply ContinuousLinearMap.ext
          intro velocity
          simp [polynomialGradient, evalPair, MvPolynomial.pderiv_X]
          ring
        rw [hgradient]
        exact (hpolynomial.mul (hasFDerivAt_fst (𝕜 := ℂ) (p := fiber)))
          |>.congr_of_eventuallyEq (Filter.Eventually.of_forall fun point ↦ by
            simp [evalPair])
      · change HasFDerivAt
          (evalPair (polynomial * MvPolynomial.X (1 : Fin 2)))
          (polynomialGradient (polynomial * MvPolynomial.X (1 : Fin 2)) fiber) fiber
        have hgradient :
            polynomialGradient (polynomial * MvPolynomial.X (1 : Fin 2)) fiber =
              evalPair polynomial fiber • ContinuousLinearMap.snd ℂ ℂ ℂ +
                fiber.2 • polynomialGradient polynomial fiber := by
          apply ContinuousLinearMap.ext
          intro velocity
          simp [polynomialGradient, evalPair, MvPolynomial.pderiv_X]
          ring
        rw [hgradient]
        exact (hpolynomial.mul (hasFDerivAt_snd (𝕜 := ℂ) (p := fiber)))
          |>.congr_of_eventuallyEq (Filter.Eventually.of_forall fun point ↦ by
            simp [evalPair])

/-- One coordinate of the moving homogenized cubic after setting the projective variable to one. -/
def movingAffineCubicPolynomial (rotation : Fin 3 → ℂ) (γ : ℂ)
    (coordinate : Fin 3) : Bivar :=
  chapterVICubicFamily 0 1
    (movingCubicCoefficient rotation γ 0)
    (movingCubicCoefficient rotation γ 1)
    (movingCubicCoefficient rotation γ 2)
    (movingCubicCoefficient rotation γ 3)
    (movingCubicCoefficient rotation γ 4) coordinate

/-- The moving squared-distance sextic as an actual bivariate polynomial. -/
def movingAffineCurvePolynomial (rotation : Fin 3 → ℂ) (γ : ℂ) : Bivar :=
  chapterVICurvePolynomial (movingAffineCubicPolynomial rotation γ)

private def firstOutside : Bivar :=
  MvPolynomial.C (3 : ℂ) * MvPolynomial.C (1 + (1 / 3 : ℂ) ^ 2) *
    (MvPolynomial.X 1 - MvPolynomial.C (1 / 5)) *
    (1 - MvPolynomial.C (1 / 5) * MvPolynomial.X 1)

private def secondOutside : Bivar :=
  MvPolynomial.C (-2 : ℂ) * MvPolynomial.C (1 + (1 / 5 : ℂ) ^ 2) *
    (MvPolynomial.X 0 - MvPolynomial.C (1 / 3)) *
    (1 - MvPolynomial.C (1 / 3) * MvPolynomial.X 0)

private def movingFirstReduced (rotation : Fin 3 → ℂ) (γ : ℂ)
    (coordinate : Fin 3) : Bivar :=
  chapterVICubicFirstReduced 0
    (movingCubicCoefficient rotation γ 0)
    (movingCubicCoefficient rotation γ 4) coordinate

private def movingSecondReduced (rotation : Fin 3 → ℂ) (γ : ℂ)
    (coordinate : Fin 3) : Bivar :=
  chapterVICubicSecondReduced 1
    (movingCubicCoefficient rotation γ 1)
    (movingCubicCoefficient rotation γ 3) coordinate

/-- Poincaré's moving reduced degree-seven equation, before clearing rational coefficients. -/
def movingAffineReducedPolynomial (rotation : Fin 3 → ℂ) (γ : ℂ) : Bivar :=
  firstOutside *
      (∑ coordinate : Fin 3,
        movingFirstReduced rotation γ coordinate *
          movingAffineCubicPolynomial rotation γ coordinate) -
    secondOutside *
      (∑ coordinate : Fin 3,
        movingSecondReduced rotation γ coordinate *
          movingAffineCubicPolynomial rotation γ coordinate)

@[simp] theorem movingAffineCubicPolynomial_zero
    (rotation : Fin 3 → ℂ) (coordinate : Fin 3) :
    movingAffineCubicPolynomial rotation 0 coordinate =
      chapterVICubicFamily 0 1
        (chapterVISection103CubicCoefficient 0)
        (chapterVISection103CubicCoefficient 1)
        (chapterVISection103CubicCoefficient 2)
        (chapterVISection103CubicCoefficient 3)
        (chapterVISection103CubicCoefficient 4) coordinate := by
  unfold movingAffineCubicPolynomial
  congr 1 <;> funext i <;> simp

/-- Polynomial evaluation agrees with the scalar moving-distance formula already connected to
the physical Cayley rotation. -/
theorem eval_movingAffineCurvePolynomial (rotation : Fin 3 → ℂ) (γ : ℂ)
    (point : Fin 2 → ℂ) :
    MvPolynomial.eval point (movingAffineCurvePolynomial rotation γ) =
      movingAffineDistance rotation γ point := by
  simp [movingAffineCurvePolynomial, movingAffineCubicPolynomial,
    movingAffineDistance, movingAffineCubic, affineCubicMonomial,
    chapterVICurvePolynomial, chapterVICubicFamily, chapterVICubicForm,
    cubicExponent, Fin.sum_univ_succ]
  ring

/-- Evaluation of one moving cubic polynomial agrees with the scalar five-monomial formula. -/
theorem eval_movingAffineCubicPolynomial (rotation : Fin 3 → ℂ) (γ : ℂ)
    (point : Fin 2 → ℂ) (coordinate : Fin 3) :
    MvPolynomial.eval point (movingAffineCubicPolynomial rotation γ coordinate) =
      movingAffineCubic rotation γ point coordinate := by
  simp [movingAffineCubicPolynomial, movingAffineCubic, affineCubicMonomial,
    chapterVICubicFamily, chapterVICubicForm, cubicExponent, Fin.sum_univ_succ]
  ring

/-- Scalar value of the first outside factor in Poincaré's reduced equation. -/
def firstOutsideValue (fiber : Fiber) : ℂ :=
  3 * (1 + (1 / 3 : ℂ) ^ 2) * (fiber.2 - 1 / 5) * (1 - (1 / 5) * fiber.2)

/-- Scalar value of the second outside factor in Poincaré's reduced equation. -/
def secondOutsideValue (fiber : Fiber) : ℂ :=
  (-2) * (1 + (1 / 5 : ℂ) ^ 2) * (fiber.1 - 1 / 3) * (1 - (1 / 3) * fiber.1)

/-- Scalar value of the first reduced quadratic factor. -/
def movingFirstReducedValue (rotation : Fin 3 → ℂ) (γ : ℂ)
    (fiber : Fiber) (coordinate : Fin 3) : ℂ :=
  movingCubicCoefficient rotation γ 0 coordinate * fiber.1 ^ 2 -
    movingCubicCoefficient rotation γ 4 coordinate

/-- Scalar value of the second reduced quadratic factor. -/
def movingSecondReducedValue (rotation : Fin 3 → ℂ) (γ : ℂ)
    (fiber : Fiber) (coordinate : Fin 3) : ℂ :=
  movingCubicCoefficient rotation γ 1 coordinate * fiber.2 ^ 2 -
    movingCubicCoefficient rotation γ 3 coordinate

/-- Scalar presentation of the moving reduced degree-seven equation. -/
def movingAffineReducedValue (rotation : Fin 3 → ℂ) (γ : ℂ)
    (fiber : Fiber) : ℂ :=
  let point : Fin 2 → ℂ := ![fiber.1, fiber.2]
  firstOutsideValue fiber *
      (∑ coordinate : Fin 3,
        movingFirstReducedValue rotation γ fiber coordinate *
          movingAffineCubic rotation γ point coordinate) -
    secondOutsideValue fiber *
      (∑ coordinate : Fin 3,
        movingSecondReducedValue rotation γ fiber coordinate *
          movingAffineCubic rotation γ point coordinate)

/-- The scalar reduced formula is exactly evaluation of the moving polynomial. -/
theorem eval_movingAffineReducedPolynomial (rotation : Fin 3 → ℂ) (γ : ℂ)
    (fiber : Fiber) :
    MvPolynomial.eval ![fiber.1, fiber.2]
        (movingAffineReducedPolynomial rotation γ) =
      movingAffineReducedValue rotation γ fiber := by
  simp [movingAffineReducedPolynomial, movingAffineReducedValue,
    movingFirstReduced, movingSecondReduced, movingFirstReducedValue,
    movingSecondReducedValue, firstOutside, secondOutside,
    firstOutsideValue, secondOutsideValue, eval_movingAffineCubicPolynomial,
    chapterVICubicFirstReduced, chapterVICubicSecondReduced]

/-- The moving sextic specializes to the exact certified source sextic. -/
@[simp] theorem movingAffineCurvePolynomial_zero (rotation : Fin 3 → ℂ) :
    movingAffineCurvePolynomial rotation 0 = ReducedCurveTangent.sourceAffineCurve := by
  have hcoeff : movingCubicCoefficient rotation 0 =
      chapterVISection103CubicCoefficient := by
    funext slot coordinate
    exact movingCubicCoefficient_zero rotation slot coordinate
  unfold movingAffineCurvePolynomial movingAffineCubicPolynomial
    ReducedCurveTangent.sourceAffineCurve ReducedCurveTangent.sourceAffineCubic
  rw [hcoeff]

/-- The moving sextic specializes to the exact LeanCompCert-normalized polynomial. -/
theorem movingAffineCurvePolynomial_zero_normalization (rotation : Fin 3 → ℂ) :
    MvPolynomial.C 50700 * movingAffineCurvePolynomial rotation 0 =
      chapterVISection103AffinePolynomial := by
  rw [movingAffineCurvePolynomial_zero]
  exact ReducedCurveTangent.sourceAffineCurve_normalization

/-- The moving reduced curve specializes to the exact certified source septic. -/
@[simp] theorem movingAffineReducedPolynomial_zero (rotation : Fin 3 → ℂ) :
    movingAffineReducedPolynomial rotation 0 =
      ReducedCurveTangent.sourceAffineReduced := by
  have hcoeff : movingCubicCoefficient rotation 0 =
      chapterVISection103CubicCoefficient := by
    funext slot coordinate
    exact movingCubicCoefficient_zero rotation slot coordinate
  unfold movingAffineReducedPolynomial ReducedCurveTangent.sourceAffineReduced
    movingFirstReduced ReducedCurveTangent.sourceAffineFirstReduced
    movingSecondReduced ReducedCurveTangent.sourceAffineSecondReduced
    movingAffineCubicPolynomial ReducedCurveTangent.sourceAffineCubic
    firstOutside ReducedCurveTangent.sourceAffineFirstOutside
    secondOutside ReducedCurveTangent.sourceAffineSecondOutside
  rw [hcoeff]

/-- The moving reduced curve specializes to the exact LeanCompCert-normalized polynomial. -/
theorem movingAffineReducedPolynomial_zero_normalization (rotation : Fin 3 → ℂ) :
    MvPolynomial.C 438750 * movingAffineReducedPolynomial rotation 0 =
      chapterVISection103ReducedAffinePolynomial := by
  rw [movingAffineReducedPolynomial_zero]
  exact ReducedCurveTangent.sourceAffineReduced_normalization

/-- The cleared pair of equations used for the algebraic implicit-function branch. -/
def movingSystem (rotation : Fin 3 → ℂ) (γ : ℂ) (fiber : Fiber) : Equation :=
  let point : Fin 2 → ℂ := ![fiber.1, fiber.2]
  (50700 * MvPolynomial.eval point (movingAffineCurvePolynomial rotation γ),
    438750 * MvPolynomial.eval point (movingAffineReducedPolynomial rotation γ))

/-- Fiber derivative of the two moving polynomial equations. -/
def movingFiberDerivative (rotation : Fin 3 → ℂ) (γ : ℂ) (fiber : Fiber) :
    Fiber →L[ℂ] Equation :=
  ((50700 : ℂ) • polynomialGradient (movingAffineCurvePolynomial rotation γ) fiber).prod
    ((438750 : ℂ) • polynomialGradient (movingAffineReducedPolynomial rotation γ) fiber)

/-- Exact derivative of the moving system in its two affine coordinates. -/
theorem hasFDerivAt_movingSystem_fiber (rotation : Fin 3 → ℂ)
    (γ : ℂ) (fiber : Fiber) :
    HasFDerivAt (movingSystem rotation γ)
      (movingFiberDerivative rotation γ fiber) fiber := by
  have hP := (hasFDerivAt_evalPair
    (movingAffineCurvePolynomial rotation γ) fiber).const_mul (50700 : ℂ)
  have hR := (hasFDerivAt_evalPair
    (movingAffineReducedPolynomial rotation γ) fiber).const_mul (438750 : ℂ)
  convert hP.prodMk hR using 1 <;> rfl

/-- At the base parameter, the moving system is evaluation of the two certified polynomials. -/
theorem movingSystem_zero (rotation : Fin 3 → ℂ) (fiber : Fiber) :
    movingSystem rotation 0 fiber =
      (MvPolynomial.eval ![fiber.1, fiber.2] chapterVISection103AffinePolynomial,
        MvPolynomial.eval ![fiber.1, fiber.2]
          chapterVISection103ReducedAffinePolynomial) := by
  have hP := congrArg (MvPolynomial.eval ![fiber.1, fiber.2])
    (movingAffineCurvePolynomial_zero_normalization rotation)
  have hR := congrArg (MvPolynomial.eval ![fiber.1, fiber.2])
    (movingAffineReducedPolynomial_zero_normalization rotation)
  simp only [map_mul, MvPolynomial.eval_C] at hP hR
  exact Prod.ext hP hR

/-- At the base parameter, the exact fiber derivative is the certified sextic--septic
Jacobian. -/
theorem movingFiberDerivative_zero_eq_affineJacobian
    (rotation : Fin 3 → ℂ) (point : Fin 2 → ℂ) :
    movingFiberDerivative rotation 0 (point 0, point 1) =
      affineJacobian chapterVISection103AffinePolynomial
        chapterVISection103ReducedAffinePolynomial point := by
  have hpoint : ![point 0, point 1] = point := by
    funext i
    fin_cases i <;> rfl
  have hPx := congrArg
    (fun polynomial ↦ MvPolynomial.eval point (MvPolynomial.pderiv 0 polynomial))
    (movingAffineCurvePolynomial_zero_normalization rotation)
  have hPy := congrArg
    (fun polynomial ↦ MvPolynomial.eval point (MvPolynomial.pderiv 1 polynomial))
    (movingAffineCurvePolynomial_zero_normalization rotation)
  have hRx := congrArg
    (fun polynomial ↦ MvPolynomial.eval point (MvPolynomial.pderiv 0 polynomial))
    (movingAffineReducedPolynomial_zero_normalization rotation)
  have hRy := congrArg
    (fun polynomial ↦ MvPolynomial.eval point (MvPolynomial.pderiv 1 polynomial))
    (movingAffineReducedPolynomial_zero_normalization rotation)
  simp only [map_mul, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_C, zero_mul,
    MvPolynomial.eval_C, zero_add] at hPx hPy hRx hRy
  rw [movingAffineCurvePolynomial_zero] at hPx hPy
  rw [movingAffineReducedPolynomial_zero] at hRx hRy
  apply ContinuousLinearMap.ext
  intro velocity
  apply Prod.ext
  · simp [movingFiberDerivative, polynomialGradient, affineJacobian, hpoint]
    linear_combination hPx * velocity.1 + hPy * velocity.2
  · simp [movingFiberDerivative, polynomialGradient, affineJacobian, hpoint]
    linear_combination hRx * velocity.1 + hRy * velocity.2

/-- The certified transversality result supplies the invertible fiber derivative required by
the implicit-function theorem at each of the twenty-four finite intersections. -/
theorem movingFiberDerivative_base_isInvertible (rotation : Fin 3 → ℂ)
    (point : Fin 2 → ℂ) (hpoint : point ∈ finiteIntersectionPoints) :
    (movingFiberDerivative rotation 0 (point 0, point 1)).IsInvertible := by
  rw [movingFiberDerivative_zero_eq_affineJacobian]
  exact source_affineJacobian_isInvertible point hpoint

/-- Each rational Cayley cosine entry is analytic at the base parameter. -/
@[fun_prop] theorem analyticAt_cayleyCos_mul (speed : ℂ) :
    AnalyticAt ℂ (fun γ ↦ cayleyCos (γ * speed)) 0 := by
  unfold cayleyCos
  have hnumerator : AnalyticAt ℂ (fun γ : ℂ ↦ 1 - (γ * speed) ^ 2 / 4) 0 := by
    fun_prop
  have hdenominator : AnalyticAt ℂ (fun γ : ℂ ↦ 1 + (γ * speed) ^ 2 / 4) 0 := by
    fun_prop
  exact hnumerator.div hdenominator (by norm_num)

/-- Each rational Cayley sine entry is analytic at the base parameter. -/
@[fun_prop] theorem analyticAt_cayleySin_mul (speed : ℂ) :
    AnalyticAt ℂ (fun γ ↦ cayleySin (γ * speed)) 0 := by
  unfold cayleySin
  have hnumerator : AnalyticAt ℂ (fun γ : ℂ ↦ γ * speed) 0 := by
    fun_prop
  have hdenominator : AnalyticAt ℂ (fun γ : ℂ ↦ 1 + (γ * speed) ^ 2 / 4) 0 := by
    fun_prop
  exact hnumerator.div hdenominator (by norm_num)

/-- Every entry of one Cayley axis rotation is analytic at the base parameter. -/
@[fun_prop] theorem analyticAt_axisRotation_entry (axis : Fin 3) (speed : ℂ)
    (row column : Fin 3) :
    AnalyticAt ℂ (fun γ ↦ axisRotation axis (γ * speed) row column) 0 := by
  fin_cases axis <;> fin_cases row <;> fin_cases column <;>
    simp only [axisRotation, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.isValue]
  all_goals first
    | exact analyticAt_const
    | exact analyticAt_cayleyCos_mul speed
    | exact analyticAt_cayleySin_mul speed
    | exact (analyticAt_cayleySin_mul speed).neg

/-- Every matrix entry of the full three-axis rotation is analytic at the base parameter. -/
@[fun_prop] theorem analyticAt_rotationMatrix_entry (rotation : Fin 3 → ℂ)
    (row column : Fin 3) :
    AnalyticAt ℂ (fun γ ↦ rotationMatrix rotation γ row column) 0 := by
  simp only [rotationMatrix, Matrix.mul_apply]
  apply Finset.analyticAt_fun_sum
  intro middle₂ _
  apply AnalyticAt.mul
  · apply Finset.analyticAt_fun_sum
    intro middle₁ _
    exact (analyticAt_axisRotation_entry 0 (rotation 0) row middle₁).mul
      (analyticAt_axisRotation_entry 1 (rotation 1) middle₁ middle₂)
  · exact analyticAt_axisRotation_entry 2 (rotation 2) middle₂ column

/-- Every coordinate of the moving major axis is analytic at the base parameter. -/
@[fun_prop] theorem analyticAt_movingMajorAxis_apply (rotation : Fin 3 → ℂ)
    (coordinate : Fin 3) :
    AnalyticAt ℂ (fun γ ↦ movingMajorAxis rotation γ coordinate) 0 := by
  simp only [movingMajorAxis, Matrix.mulVec, dotProduct]
  apply Finset.analyticAt_fun_sum
  intro column _
  exact (analyticAt_rotationMatrix_entry rotation coordinate column).mul analyticAt_const

/-- Every coordinate of the moving minor axis is analytic at the base parameter. -/
@[fun_prop] theorem analyticAt_movingMinorAxis_apply (rotation : Fin 3 → ℂ)
    (coordinate : Fin 3) :
    AnalyticAt ℂ (fun γ ↦ movingMinorAxis rotation γ coordinate) 0 := by
  simp only [movingMinorAxis, Matrix.mulVec, dotProduct]
  apply Finset.analyticAt_fun_sum
  intro column _
  exact (analyticAt_rotationMatrix_entry rotation coordinate column).mul analyticAt_const

/-- Every moving cubic coefficient is analytic at the base parameter. -/
@[fun_prop] theorem analyticAt_movingCubicCoefficient (rotation : Fin 3 → ℂ)
    (slot : Fin 5) (coordinate : Fin 3) :
    AnalyticAt ℂ (fun γ ↦ movingCubicCoefficient rotation γ slot coordinate) 0 := by
  fin_cases slot <;> simp [movingCubicCoefficient]
  all_goals fun_prop

/-- A moving coefficient remains analytic when viewed as a function of the joint
`(parameter, fiber)` variable. -/
theorem analyticAt_joint_movingCubicCoefficient (rotation : Fin 3 → ℂ)
    (fiber : Fiber) (slot : Fin 5) (coordinate : Fin 3) :
    AnalyticAt ℂ
      (fun input : ℂ × Fiber ↦
        movingCubicCoefficient rotation input.1 slot coordinate)
      (0, fiber) := by
  have hfst : AnalyticAt ℂ (fun input : ℂ × Fiber ↦ input.1) (0, fiber) :=
    analyticAt_fst
  simpa [Function.comp_def] using AnalyticAt.comp
    (g := fun γ ↦ movingCubicCoefficient rotation γ slot coordinate)
    (f := fun input : ℂ × Fiber ↦ input.1) (x := (0, fiber))
    (analyticAt_movingCubicCoefficient rotation slot coordinate) hfst

/-- Each affine cubic monomial is analytic in the joint variable. -/
theorem analyticAt_joint_affineCubicMonomial (fiber : Fiber) (slot : Fin 5) :
    AnalyticAt ℂ
      (fun input : ℂ × Fiber ↦
        affineCubicMonomial ![input.2.1, input.2.2] slot)
      (0, fiber) := by
  have hfiber : AnalyticAt ℂ (fun input : ℂ × Fiber ↦ input.2) (0, fiber) :=
    analyticAt_snd
  have hx : AnalyticAt ℂ (fun input : ℂ × Fiber ↦ input.2.1) (0, fiber) := by
    simpa [Function.comp_def] using
      (analyticAt_fst (𝕜 := ℂ) (p := fiber)).comp hfiber
  have hy : AnalyticAt ℂ (fun input : ℂ × Fiber ↦ input.2.2) (0, fiber) := by
    simpa [Function.comp_def] using
      (analyticAt_snd (𝕜 := ℂ) (p := fiber)).comp hfiber
  change AnalyticAt ℂ
    (fun input : ℂ × Fiber ↦
      input.2.1 ^ cubicExponent slot 0 * input.2.2 ^ cubicExponent slot 1)
    (0, fiber)
  exact (hx.pow _).mul (hy.pow _)

/-- The first affine fiber coordinate is analytic in the joint variable. -/
theorem analyticAt_joint_fiber_fst (fiber : Fiber) :
    AnalyticAt ℂ (fun input : ℂ × Fiber ↦ input.2.1) (0, fiber) := by
  have hfiber : AnalyticAt ℂ (fun input : ℂ × Fiber ↦ input.2) (0, fiber) :=
    analyticAt_snd
  simpa [Function.comp_def] using
    (analyticAt_fst (𝕜 := ℂ) (p := fiber)).comp hfiber

/-- The second affine fiber coordinate is analytic in the joint variable. -/
theorem analyticAt_joint_fiber_snd (fiber : Fiber) :
    AnalyticAt ℂ (fun input : ℂ × Fiber ↦ input.2.2) (0, fiber) := by
  have hfiber : AnalyticAt ℂ (fun input : ℂ × Fiber ↦ input.2) (0, fiber) :=
    analyticAt_snd
  simpa [Function.comp_def] using
    (analyticAt_snd (𝕜 := ℂ) (p := fiber)).comp hfiber

/-- Each coordinate of the moving affine cubic is jointly analytic. -/
theorem analyticAt_joint_movingAffineCubic (rotation : Fin 3 → ℂ)
    (fiber : Fiber) (coordinate : Fin 3) :
    AnalyticAt ℂ
      (fun input : ℂ × Fiber ↦
        movingAffineCubic rotation input.1 ![input.2.1, input.2.2] coordinate)
      (0, fiber) := by
  unfold movingAffineCubic
  apply Finset.analyticAt_fun_sum
  intro slot _
  exact (analyticAt_joint_movingCubicCoefficient rotation fiber slot coordinate).mul
    (analyticAt_joint_affineCubicMonomial fiber slot)

/-- The moving squared-distance sextic is jointly analytic. -/
theorem analyticAt_joint_movingAffineDistance (rotation : Fin 3 → ℂ)
    (fiber : Fiber) :
    AnalyticAt ℂ
      (fun input : ℂ × Fiber ↦
        movingAffineDistance rotation input.1 ![input.2.1, input.2.2])
      (0, fiber) := by
  unfold movingAffineDistance
  apply Finset.analyticAt_fun_sum
  intro coordinate _
  exact (analyticAt_joint_movingAffineCubic rotation fiber coordinate).pow 2

/-- The first outside factor of the reduced equation is jointly analytic. -/
theorem analyticAt_joint_firstOutsideValue (fiber : Fiber) :
    AnalyticAt ℂ (fun input : ℂ × Fiber ↦ firstOutsideValue input.2) (0, fiber) := by
  unfold firstOutsideValue
  have hy := analyticAt_joint_fiber_snd fiber
  exact (((analyticAt_const.mul analyticAt_const).mul (hy.sub analyticAt_const)).mul
    (analyticAt_const.sub (analyticAt_const.mul hy)))

/-- The second outside factor of the reduced equation is jointly analytic. -/
theorem analyticAt_joint_secondOutsideValue (fiber : Fiber) :
    AnalyticAt ℂ (fun input : ℂ × Fiber ↦ secondOutsideValue input.2) (0, fiber) := by
  unfold secondOutsideValue
  have hx := analyticAt_joint_fiber_fst fiber
  exact (((analyticAt_const.mul analyticAt_const).mul (hx.sub analyticAt_const)).mul
    (analyticAt_const.sub (analyticAt_const.mul hx)))

/-- The first moving reduced quadratic factor is jointly analytic. -/
theorem analyticAt_joint_movingFirstReducedValue (rotation : Fin 3 → ℂ)
    (fiber : Fiber) (coordinate : Fin 3) :
    AnalyticAt ℂ
      (fun input : ℂ × Fiber ↦
        movingFirstReducedValue rotation input.1 input.2 coordinate)
      (0, fiber) := by
  unfold movingFirstReducedValue
  exact ((analyticAt_joint_movingCubicCoefficient rotation fiber 0 coordinate).mul
    ((analyticAt_joint_fiber_fst fiber).pow 2)).sub
      (analyticAt_joint_movingCubicCoefficient rotation fiber 4 coordinate)

/-- The second moving reduced quadratic factor is jointly analytic. -/
theorem analyticAt_joint_movingSecondReducedValue (rotation : Fin 3 → ℂ)
    (fiber : Fiber) (coordinate : Fin 3) :
    AnalyticAt ℂ
      (fun input : ℂ × Fiber ↦
        movingSecondReducedValue rotation input.1 input.2 coordinate)
      (0, fiber) := by
  unfold movingSecondReducedValue
  exact ((analyticAt_joint_movingCubicCoefficient rotation fiber 1 coordinate).mul
    ((analyticAt_joint_fiber_snd fiber).pow 2)).sub
      (analyticAt_joint_movingCubicCoefficient rotation fiber 3 coordinate)

/-- Poincaré's moving reduced degree-seven equation is jointly analytic. -/
theorem analyticAt_joint_movingAffineReducedValue (rotation : Fin 3 → ℂ)
    (fiber : Fiber) :
    AnalyticAt ℂ
      (fun input : ℂ × Fiber ↦ movingAffineReducedValue rotation input.1 input.2)
      (0, fiber) := by
  unfold movingAffineReducedValue
  apply AnalyticAt.sub
  · apply AnalyticAt.mul (analyticAt_joint_firstOutsideValue fiber)
    apply Finset.analyticAt_fun_sum
    intro coordinate _
    exact (analyticAt_joint_movingFirstReducedValue rotation fiber coordinate).mul
      (analyticAt_joint_movingAffineCubic rotation fiber coordinate)
  · apply AnalyticAt.mul (analyticAt_joint_secondOutsideValue fiber)
    apply Finset.analyticAt_fun_sum
    intro coordinate _
    exact (analyticAt_joint_movingSecondReducedValue rotation fiber coordinate).mul
      (analyticAt_joint_movingAffineCubic rotation fiber coordinate)

/-- The pair of moving algebraic equations is jointly analytic near every base fiber. -/
theorem analyticAt_movingSystem (rotation : Fin 3 → ℂ) (fiber : Fiber) :
    AnalyticAt ℂ (Function.uncurry (movingSystem rotation)) (0, fiber) := by
  have hPraw : AnalyticAt ℂ
      (fun input : ℂ × Fiber ↦
        50700 * movingAffineDistance rotation input.1 ![input.2.1, input.2.2])
      (0, fiber) :=
    analyticAt_const.mul (analyticAt_joint_movingAffineDistance rotation fiber)
  have hP : AnalyticAt ℂ
      (fun input : ℂ × Fiber ↦
        50700 * MvPolynomial.eval ![input.2.1, input.2.2]
          (movingAffineCurvePolynomial rotation input.1))
      (0, fiber) :=
    hPraw.congr (Filter.Eventually.of_forall fun input ↦ by
      dsimp
      rw [eval_movingAffineCurvePolynomial])
  have hRraw : AnalyticAt ℂ
      (fun input : ℂ × Fiber ↦
        438750 * movingAffineReducedValue rotation input.1 input.2)
      (0, fiber) :=
    analyticAt_const.mul (analyticAt_joint_movingAffineReducedValue rotation fiber)
  have hR : AnalyticAt ℂ
      (fun input : ℂ × Fiber ↦
        438750 * MvPolynomial.eval ![input.2.1, input.2.2]
          (movingAffineReducedPolynomial rotation input.1))
      (0, fiber) :=
    hRraw.congr (Filter.Eventually.of_forall fun input ↦ by
      dsimp
      rw [eval_movingAffineReducedPolynomial])
  convert hP.prod hR using 1 <;> rfl

/-- The parameter-direction partial derivative extracted from the joint derivative. -/
def movingParameterDerivative (rotation : Fin 3 → ℂ) (γ : ℂ) (fiber : Fiber) :
    ℂ →L[ℂ] Equation :=
  (fderiv ℂ (Function.uncurry (movingSystem rotation)) (γ, fiber)).comp
    (ContinuousLinearMap.inl ℂ ℂ Fiber)

/-- The fiber-direction partial derivative extracted from the joint derivative. -/
def movingFiberPartialDerivative (rotation : Fin 3 → ℂ) (γ : ℂ) (fiber : Fiber) :
    Fiber →L[ℂ] Equation :=
  (fderiv ℂ (Function.uncurry (movingSystem rotation)) (γ, fiber)).comp
    (ContinuousLinearMap.inr ℂ ℂ Fiber)

private theorem hasFDerivAt_parameterInsertion (γ : ℂ) (fiber : Fiber) :
    HasFDerivAt (fun parameter : ℂ ↦ (parameter, fiber))
      (ContinuousLinearMap.inl ℂ ℂ Fiber) γ := by
  convert (hasFDerivAt_id (𝕜 := ℂ) γ).prodMk (hasFDerivAt_const fiber γ) using 1 <;> rfl

private theorem hasFDerivAt_fiberInsertion (γ : ℂ) (fiber : Fiber) :
    HasFDerivAt (fun value : Fiber ↦ (γ, value))
      (ContinuousLinearMap.inr ℂ ℂ Fiber) fiber := by
  convert (hasFDerivAt_const γ fiber).prodMk (hasFDerivAt_id (𝕜 := ℂ) fiber) using 1 <;> rfl

private theorem hasFDerivAt_movingSystem_parameter_of_analyticAt
    (rotation : Fin 3 → ℂ) (γ : ℂ) (fiber : Fiber)
    (hanalytic : AnalyticAt ℂ (Function.uncurry (movingSystem rotation)) (γ, fiber)) :
    HasFDerivAt (movingSystem rotation · fiber)
      (movingParameterDerivative rotation γ fiber) γ := by
  have hjoint := hanalytic.contDiffAt.differentiableAt_one.hasFDerivAt
  have hcomposition := hjoint.comp γ
    (hasFDerivAt_parameterInsertion γ fiber)
  convert hcomposition using 1 <;> rfl

private theorem hasFDerivAt_movingSystem_fiber_of_analyticAt
    (rotation : Fin 3 → ℂ) (γ : ℂ) (fiber : Fiber)
    (hanalytic : AnalyticAt ℂ (Function.uncurry (movingSystem rotation)) (γ, fiber)) :
    HasFDerivAt (movingSystem rotation γ)
      (movingFiberPartialDerivative rotation γ fiber) fiber := by
  have hjoint := hanalytic.contDiffAt.differentiableAt_one.hasFDerivAt
  have hcomposition := hjoint.comp fiber
    (hasFDerivAt_fiberInsertion γ fiber)
  convert hcomposition using 1 <;> rfl

/-- The joint derivative partial in the fiber agrees at the base parameter with the exact
polynomial-gradient derivative. -/
theorem movingFiberPartialDerivative_zero_eq (rotation : Fin 3 → ℂ) (fiber : Fiber) :
    movingFiberPartialDerivative rotation 0 fiber = movingFiberDerivative rotation 0 fiber := by
  exact (hasFDerivAt_movingSystem_fiber_of_analyticAt rotation 0 fiber
    (analyticAt_movingSystem rotation fiber)).unique
      (hasFDerivAt_movingSystem_fiber rotation 0 fiber)

private theorem continuousAt_movingParameterDerivative (rotation : Fin 3 → ℂ)
    (fiber : Fiber) :
    ContinuousAt (Function.uncurry (movingParameterDerivative rotation)) (0, fiber) := by
  have hcont : ContDiffAt ℂ 1 (Function.uncurry (movingSystem rotation)) (0, fiber) :=
    (analyticAt_movingSystem rotation fiber).contDiffAt
  have hderivative := hcont.continuousAt_fderiv one_ne_zero
  convert hderivative.clm_comp continuousAt_const using 1 <;> rfl

private theorem continuousAt_movingFiberPartialDerivative (rotation : Fin 3 → ℂ)
    (fiber : Fiber) :
    ContinuousAt (Function.uncurry (movingFiberPartialDerivative rotation)) (0, fiber) := by
  have hcont : ContDiffAt ℂ 1 (Function.uncurry (movingSystem rotation)) (0, fiber) :=
    (analyticAt_movingSystem rotation fiber).contDiffAt
  have hderivative := hcont.continuousAt_fderiv one_ne_zero
  convert hderivative.clm_comp continuousAt_const using 1 <;> rfl

/-- The concrete local singular system at one of Poincaré's twenty-four finite points. -/
def movingLocalSystem (rotation : Fin 3 → ℂ) (point : Fin 2 → ℂ)
    (hpoint : point ∈ finiteIntersectionPoints) : LocalSingularSystem where
  system := movingSystem rotation
  base := (point 0, point 1)
  parameterDerivative := movingParameterDerivative rotation
  fiberDerivative := movingFiberPartialDerivative rotation
  hasFDerivAt_parameter := by
    filter_upwards [(analyticAt_movingSystem rotation (point 0, point 1)).eventually_analyticAt]
      with input hinput
    exact hasFDerivAt_movingSystem_parameter_of_analyticAt rotation input.1 input.2 hinput
  hasFDerivAt_fiber := by
    filter_upwards [(analyticAt_movingSystem rotation (point 0, point 1)).eventually_analyticAt]
      with input hinput
    exact hasFDerivAt_movingSystem_fiber_of_analyticAt rotation input.1 input.2 hinput
  continuousAt_parameterDerivative :=
    continuousAt_movingParameterDerivative rotation (point 0, point 1)
  continuousAt_fiberDerivative :=
    continuousAt_movingFiberPartialDerivative rotation (point 0, point 1)
  fiberDerivative_isInvertible := by
    rw [movingFiberPartialDerivative_zero_eq]
    exact movingFiberDerivative_base_isInvertible rotation point hpoint
  base_is_singular := by
    rw [movingSystem_zero]
    have hcommon :=
      (common_zero_iff_origin_or_finiteIntersectionPoints point).mpr (Or.inr hpoint)
    have hpointEq : ![point 0, point 1] = point := by
      funext i
      fin_cases i <;> rfl
    simpa [hpointEq] using hcommon

/-- Every certified finite intersection is a zero of the moving system at the base parameter. -/
theorem movingSystem_base_is_zero (rotation : Fin 3 → ℂ)
    (point : Fin 2 → ℂ) (hpoint : point ∈ finiteIntersectionPoints) :
    movingSystem rotation 0 (point 0, point 1) = 0 := by
  rw [movingSystem_zero]
  have hcommon :=
    (common_zero_iff_origin_or_finiteIntersectionPoints point).mpr (Or.inr hpoint)
  have hpointEq : ![point 0, point 1] = point := by
    funext i
    fin_cases i <;> rfl
  simpa [hpointEq] using hcommon

/-- The first component of the parameter partial derivative is the certified infinitesimal
rotation source, with the same clearing factor as the moving sextic. -/
theorem movingParameterDerivative_first_eq_source (rotation : Fin 3 → ℂ)
    (point : Fin 2 → ℂ) :
    ((movingParameterDerivative rotation 0 (point 0, point 1)) 1).1 =
      50700 * MvPolynomial.eval point
        (∑ axis, rotation axis • affineDirectionalPolynomial axis) := by
  have hpartial :=
    (hasFDerivAt_movingSystem_parameter_of_analyticAt rotation 0 (point 0, point 1)
      (analyticAt_movingSystem rotation (point 0, point 1))).hasDerivAt
  have hsource :=
    (hasDerivAt_movingAffineDistance_eq_source rotation point).const_mul (50700 : ℂ)
  have hfirst : HasDerivAt
      (fun γ ↦ (movingSystem rotation γ (point 0, point 1)).1)
      ((movingParameterDerivative rotation 0 (point 0, point 1)) 1).1 0 :=
    hpartial.fst
  have hsource' : HasDerivAt
      (fun γ ↦ (movingSystem rotation γ (point 0, point 1)).1)
      (50700 * MvPolynomial.eval point
        (∑ axis, rotation axis • affineDirectionalPolynomial axis)) 0 := by
    convert hsource using 1
    · exact complexAddCommGroupForCalculus_eq_field
    · funext γ
      simp only [movingSystem]
      rw [eval_movingAffineCurvePolynomial]
      congr 2
      funext i
      fin_cases i <;> rfl
  exact hfirst.unique hsource'

/-- The derivative selected by the implicit-function theorem satisfies the linearization of
the two moving equations. -/
theorem movingLocalSystem_linearized_eq_zero (rotation : Fin 3 → ℂ)
    (point : Fin 2 → ℂ) (hpoint : point ∈ finiteIntersectionPoints) :
    (movingLocalSystem rotation point hpoint).fiberDerivative 0
          (movingLocalSystem rotation point hpoint).base
          ((movingLocalSystem rotation point hpoint).branchFDeriv 1) +
        (movingLocalSystem rotation point hpoint).parameterDerivative 0
          (movingLocalSystem rotation point hpoint).base 1 = 0 := by
  let data := movingLocalSystem rotation point hpoint
  have hinvertible := data.fiberDerivative_isInvertible
  change data.fiberDerivative 0 data.base (data.branchFDeriv 1) +
      data.parameterDerivative 0 data.base 1 = 0
  simp only [LocalSingularSystem.branchFDeriv, ContinuousLinearMap.comp_apply,
    neg_apply, map_neg]
  rw [hinvertible.self_apply_inverse]
  simp

/-- Poincaré's §102 input, stated only for the concrete branches constructed above: the
singularity parameter attached to each of the twenty-four roots is locally constant when the
chosen infinitesimal rotation fixes the two essential coordinates. -/
structure BranchSingularityConstancy (rotation : Fin 3 → ℂ) : Prop where
  eventually_constant : ∀ (point : Fin 2 → ℂ)
      (hpoint : point ∈ finiteIntersectionPoints),
    (fun γ ↦ halfAngleSingularityParameter (-2) 3 (1 / 3) (1 / 5)
      ((movingLocalSystem rotation point hpoint).branch γ).1
      ((movingLocalSystem rotation point hpoint).branch γ).2) =ᶠ[nhds 0]
    (fun _ ↦ halfAngleSingularityParameter (-2) 3 (1 / 3) (1 / 5)
      (point 0) (point 1))

/-- Constancy of the singularity parameter forces the velocity of the concrete IFT branch to
lie in the kernel of Poincaré's logarithmic differential. -/
theorem branch_logDifferential_eq_zero (rotation : Fin 3 → ℂ)
    (constancy : BranchSingularityConstancy rotation)
    (point : Fin 2 → ℂ) (hpoint : point ∈ finiteIntersectionPoints) :
    singularityLogDifferential (-2) 3 (1 / 3) (1 / 5)
      (point 0) (point 1)
      ((movingLocalSystem rotation point hpoint).branchFDeriv 1) = 0 := by
  let data := movingLocalSystem rotation point hpoint
  have hcoordinates := finiteIntersectionPoint_coordinates_ne_zero point hpoint
  have hconstant :
      (fun γ ↦ halfAngleSingularityParameter (-2) 3 (1 / 3) (1 / 5)
        (data.branch γ).1 (data.branch γ).2) =ᶠ[nhds 0]
      (fun _ ↦ halfAngleSingularityParameter (-2) 3 (1 / 3) (1 / 5)
        ((fun γ ↦ (data.branch γ).1) 0)
        ((fun γ ↦ (data.branch γ).2) 0)) := by
    simpa [data, movingLocalSystem] using constancy.eventually_constant point hpoint
  have hlog := singularityLogDifferential_eq_zero_of_eventually_constant
    (-2) 3 (1 / 3) (1 / 5)
    data.timeBranch_hasDerivAt data.singularValueBranch_hasDerivAt
    (by simpa [data, movingLocalSystem] using hcoordinates.1)
    (by simpa [data, movingLocalSystem] using hcoordinates.2)
    (by norm_num) (by norm_num) hconstant
  simpa [data, movingLocalSystem] using hlog

/-- The fiber contribution to the first moving equation vanishes along a branch on which
Poincaré's singularity parameter is constant.  The key tangent implication is the formalized
`dz = 0` step from §103. -/
theorem branch_fiberDerivative_first_eq_zero (rotation : Fin 3 → ℂ)
    (constancy : BranchSingularityConstancy rotation)
    (point : Fin 2 → ℂ) (hpoint : point ∈ finiteIntersectionPoints) :
    ((movingLocalSystem rotation point hpoint).fiberDerivative 0
      (movingLocalSystem rotation point hpoint).base
      ((movingLocalSystem rotation point hpoint).branchFDeriv 1)).1 = 0 := by
  let data := movingLocalSystem rotation point hpoint
  let velocity := data.branchFDeriv 1
  let velocityPoint : Fin 2 → ℂ := ![velocity.1, velocity.2]
  have hlog := branch_logDifferential_eq_zero rotation constancy point hpoint
  have hcurve :=
    finiteIntersectionPoint_curveDerivative_eq_zero_of_logDifferential_eq_zero
      point velocityPoint hpoint (by simpa [data, velocity, velocityPoint] using hlog)
  change ((movingFiberPartialDerivative rotation 0 (point 0, point 1)) velocity).1 = 0
  rw [movingFiberPartialDerivative_zero_eq,
    movingFiberDerivative_zero_eq_affineJacobian]
  have hvelocity : (velocityPoint 0, velocityPoint 1) = velocity := by
    simp [velocityPoint]
  rw [← hvelocity, affineJacobian_apply]
  exact hcurve

/-- Poincaré's equation (2), now derived for the actual moving algebraic branches: the
infinitesimal rotation source vanishes at every certified finite intersection. -/
theorem source_vanishes_of_branchSingularityConstancy
    (rotation : Fin 3 → ℂ) (constancy : BranchSingularityConstancy rotation)
    (point : Fin 2 → ℂ) (hpoint : point ∈ finiteIntersectionPoints) :
    MvPolynomial.eval point
      (∑ axis, rotation axis • affineDirectionalPolynomial axis) = 0 := by
  let data := movingLocalSystem rotation point hpoint
  have hlinear := movingLocalSystem_linearized_eq_zero rotation point hpoint
  have hfirst := congrArg Prod.fst hlinear
  have hfiber := branch_fiberDerivative_first_eq_zero rotation constancy point hpoint
  have hparameter := movingParameterDerivative_first_eq_source rotation point
  change
    (data.fiberDerivative 0 data.base (data.branchFDeriv 1)).1 +
      (data.parameterDerivative 0 data.base 1).1 = 0 at hfirst
  change (data.fiberDerivative 0 data.base (data.branchFDeriv 1)).1 = 0 at hfiber
  change (data.parameterDerivative 0 data.base 1).1 =
    50700 * MvPolynomial.eval point
      (∑ axis, rotation axis • affineDirectionalPolynomial axis) at hparameter
  rw [hfiber, zero_add, hparameter] at hfirst
  exact (mul_eq_zero.mp hfirst).resolve_left (by norm_num)

/-- The complete §103 finite conclusion for the constructed branches.  Once §102 supplies
local constancy of the singularity parameters, the LeanCompCert restriction certificate forces
the infinitesimal spatial rotation to vanish. -/
theorem rotation_eq_zero_of_branchSingularityConstancy
    (rotation : Fin 3 → ℂ) (constancy : BranchSingularityConstancy rotation) :
    rotation = 0 := by
  apply rotation_eq_zero_of_source_vanishes rotation
  intro point hpoint
  exact source_vanishes_of_branchSingularityConstancy rotation constancy point hpoint

/-- The §102 dimension count joined directly to the concrete analytic branches and the §103
LeanCompCert calculation.  The sole remaining analytic premise says that a rotation fixing the
two essential coordinates makes Poincaré's singularity parameter locally constant along each
of the twenty-four branches. -/
theorem not_twoParameter_movingAlgebraicFamily
    (essentialCoordinates : (Fin 3 → ℂ) →L[ℂ] (Fin 2 → ℂ))
    (constancy_of_kernel : ∀ rotation,
      essentialCoordinates rotation = 0 → BranchSingularityConstancy rotation) :
    False := by
  have hdimension :
      Module.finrank ℂ (Fin 2 → ℂ) < Module.finrank ℂ (Fin 3 → ℂ) := by
    simp
  have hkernel : LinearMap.ker essentialCoordinates.toLinearMap ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt hdimension
  obtain ⟨rotation, hrotationKernel, hrotationNonzero⟩ :=
    (LinearMap.ker essentialCoordinates.toLinearMap).ne_bot_iff.mp hkernel
  have hcoordinates : essentialCoordinates rotation = 0 := hrotationKernel
  have hrotationZero : rotation = 0 :=
    rotation_eq_zero_of_branchSingularityConstancy rotation
      (constancy_of_kernel rotation hcoordinates)
  exact hrotationNonzero hrotationZero

end PoincareChapterVI.MovingAlgebraicBranches
