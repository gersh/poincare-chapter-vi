/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.Section103.AffineIntersectionCount
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Transversality of the twenty-four finite Section 103 intersections

The bidirectional shape-basis certificate and the separability certificate do more than count
the finite intersections: together they imply that every one of the twenty-four non-origin
intersections is transverse.  This file extracts that consequence.  It is the algebraic
nondegeneracy needed to apply an implicit-function theorem to the moving curve pair.
-/

noncomputable section

namespace PoincareChapterVI.AffineTransversality

open AffineIntersectionCount
open AffineEliminationData
open AffineEliminationCertificate

private abbrev Bivar := MvPolynomial (Fin 2) ℂ

/-- Determinant of the two gradients at an affine point. -/
def affineJacobianDet (first second : Bivar) (point : Fin 2 → ℂ) : ℂ :=
  MvPolynomial.eval point (MvPolynomial.pderiv 0 first) *
      MvPolynomial.eval point (MvPolynomial.pderiv 1 second) -
    MvPolynomial.eval point (MvPolynomial.pderiv 1 first) *
      MvPolynomial.eval point (MvPolynomial.pderiv 0 second)

/-- The two-gradient derivative of a pair of affine polynomial equations. -/
def affineJacobian (first second : Bivar) (point : Fin 2 → ℂ) :
    (ℂ × ℂ) →L[ℂ] (ℂ × ℂ) :=
  let firstX := MvPolynomial.eval point (MvPolynomial.pderiv 0 first)
  let firstY := MvPolynomial.eval point (MvPolynomial.pderiv 1 first)
  let secondX := MvPolynomial.eval point (MvPolynomial.pderiv 0 second)
  let secondY := MvPolynomial.eval point (MvPolynomial.pderiv 1 second)
  ({ toFun := fun velocity ↦
      (firstX * velocity.1 + firstY * velocity.2,
        secondX * velocity.1 + secondY * velocity.2)
     map_add' := by
       intro left right
       ext <;> dsimp <;> ring
     map_smul' := by
       intro scalar velocity
       ext <;> dsimp <;> ring } : (ℂ × ℂ) →ₗ[ℂ] (ℂ × ℂ)).toContinuousLinearMap

@[simp] theorem affineJacobian_apply (first second : Bivar) (point velocity : Fin 2 → ℂ) :
    affineJacobian first second point (velocity 0, velocity 1) =
      (MvPolynomial.eval point (MvPolynomial.pderiv 0 first) * velocity 0 +
          MvPolynomial.eval point (MvPolynomial.pderiv 1 first) * velocity 1,
        MvPolynomial.eval point (MvPolynomial.pderiv 0 second) * velocity 0 +
          MvPolynomial.eval point (MvPolynomial.pderiv 1 second) * velocity 1) :=
  rfl

/-- A two-by-two affine Jacobian with nonzero determinant is a continuous linear equivalence. -/
def affineJacobianEquiv (first second : Bivar) (point : Fin 2 → ℂ)
    (hdet : affineJacobianDet first second point ≠ 0) :
    (ℂ × ℂ) ≃ₗ[ℂ] (ℂ × ℂ) :=
  let a := MvPolynomial.eval point (MvPolynomial.pderiv 0 first)
  let b := MvPolynomial.eval point (MvPolynomial.pderiv 1 first)
  let c := MvPolynomial.eval point (MvPolynomial.pderiv 0 second)
  let d := MvPolynomial.eval point (MvPolynomial.pderiv 1 second)
  let determinant := a * d - b * c
  { toFun := fun velocity ↦
      (a * velocity.1 + b * velocity.2, c * velocity.1 + d * velocity.2)
    invFun := fun value ↦
      ((d * value.1 - b * value.2) / determinant,
        (a * value.2 - c * value.1) / determinant)
    left_inv := by
      intro velocity
      have hdet' : determinant ≠ 0 := hdet
      ext <;> dsimp
      all_goals field_simp
      all_goals ring
    right_inv := by
      intro value
      have hdet' : determinant ≠ 0 := hdet
      ext <;> dsimp
      all_goals field_simp
      all_goals ring
    map_add' := by
      intro left right
      ext <;> dsimp <;> ring
    map_smul' := by
      intro scalar velocity
      ext <;> dsimp <;> ring }

theorem affineJacobian_isInvertible_of_det_ne_zero
    (first second : Bivar) (point : Fin 2 → ℂ)
    (hdet : affineJacobianDet first second point ≠ 0) :
    (affineJacobian first second point).IsInvertible := by
  refine ⟨(affineJacobianEquiv first second point hdet).toContinuousLinearEquiv, ?_⟩
  apply ContinuousLinearMap.ext
  intro velocity
  rfl

theorem pderiv_zero_embedY (polynomial : Polynomial ℂ) :
    MvPolynomial.pderiv 0 (embedY polynomial) = 0 := by
  induction polynomial using Polynomial.induction_on' with
  | add left right hleft hright => simp [hleft, hright]
  | monomial degree coefficient =>
      simp [embedY, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_monomial]

theorem eval_pderiv_one_embedY (point : Fin 2 → ℂ) (polynomial : Polynomial ℂ) :
    MvPolynomial.eval point (MvPolynomial.pderiv 1 (embedY polynomial)) =
      polynomial.derivative.eval (point 1) := by
  induction polynomial using Polynomial.induction_on' with
  | add left right hleft hright =>
      simp [hleft, hright, Polynomial.derivative_add]
  | monomial degree coefficient =>
      simp [embedY, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_monomial,
        Polynomial.derivative_monomial]
      ring

/-- At a common zero, replacing two equations by polynomial linear combinations multiplies
their Jacobian determinant by the determinant of the coefficient matrix. -/
theorem affineJacobianDet_linearCombination_at_commonZero
    (first second a b c d : Bivar) (point : Fin 2 → ℂ)
    (hfirst : MvPolynomial.eval point first = 0)
    (hsecond : MvPolynomial.eval point second = 0) :
    affineJacobianDet (a * first + b * second) (c * first + d * second) point =
      (MvPolynomial.eval point a * MvPolynomial.eval point d -
        MvPolynomial.eval point b * MvPolynomial.eval point c) *
          affineJacobianDet first second point := by
  simp [affineJacobianDet, hfirst, hsecond]
  ring

theorem residual_derivative_ne_zero_at_finiteIntersection
    (point : Fin 2 → ℂ) (hpoint : point ∈ finiteIntersectionPoints) :
    residualPolynomialComplex.derivative.eval (point 1) ≠ 0 := by
  rw [finiteIntersectionPoints, Finset.mem_image] at hpoint
  rcases hpoint with ⟨root, hroot, rfl⟩
  apply residualPolynomialComplex_separable.eval₂_derivative_ne_zero
    (RingHom.id ℂ)
  simpa [residualPoint] using (mem_residualRoots_iff root).mp hroot

theorem point_one_ne_zero_of_mem_finiteIntersectionPoints
    (point : Fin 2 → ℂ) (hpoint : point ∈ finiteIntersectionPoints) :
    point 1 ≠ 0 := by
  intro hzero
  have hcommon := (common_zero_iff_origin_or_finiteIntersectionPoints point).mpr
    (Or.inr hpoint)
  have hshape := (common_zero_iff_shape_and_eliminant point).mp hcommon |>.1
  have hxzero : point 0 = 0 := by
    simpa [hzero, shapeTailPolynomial_eval_zero] using hshape
  have hpointZero : point = 0 := by
    funext i
    fin_cases i <;> simp [hxzero, hzero]
  exact origin_not_mem_finiteIntersectionPoints (hpointZero ▸ hpoint)

/-- The triangular shape equations have nonzero Jacobian at every residual point. -/
theorem shape_affineJacobianDet_ne_zero
    (point : Fin 2 → ℂ) (hpoint : point ∈ finiteIntersectionPoints) :
    affineJacobianDet
      (MvPolynomial.X 0 + embedY shapeTailPolynomial)
      (MvPolynomial.X 1 ^ 2 * embedY residualPolynomialComplex) point ≠ 0 := by
  have hroot : residualPolynomialComplex.eval (point 1) = 0 := by
    have hcommon := (common_zero_iff_origin_or_finiteIntersectionPoints point).mpr
      (Or.inr hpoint)
    have helim := (common_zero_iff_shape_and_eliminant point).mp hcommon |>.2
    rcases mul_eq_zero.mp helim with hpointZero | hroot
    · exact False.elim ((point_one_ne_zero_of_mem_finiteIntersectionPoints point hpoint)
        ((pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp hpointZero))
    · exact hroot
  have hy := point_one_ne_zero_of_mem_finiteIntersectionPoints point hpoint
  have hderivative := residual_derivative_ne_zero_at_finiteIntersection point hpoint
  simp [affineJacobianDet, pderiv_zero_embedY, eval_pderiv_one_embedY,
    eval_embedY, hroot]
  exact ⟨hy, hderivative⟩

/-- The exact sextic and reduced septic meet transversely at each of the twenty-four finite
non-origin intersections. -/
theorem source_affineJacobianDet_ne_zero
    (point : Fin 2 → ℂ) (hpoint : point ∈ finiteIntersectionPoints) :
    affineJacobianDet chapterVISection103AffinePolynomial
      chapterVISection103ReducedAffinePolynomial point ≠ 0 := by
  have hcommon := (common_zero_iff_origin_or_finiteIntersectionPoints point).mpr
    (Or.inr hpoint)
  have hcombination := affineJacobianDet_linearCombination_at_commonZero
    chapterVISection103AffinePolynomial chapterVISection103ReducedAffinePolynomial
    (toMv shapeLeft) (toMv shapeRight) (toMv eliminantLeft) (toMv eliminantRight)
    point hcommon.1 hcommon.2
  rw [← shape_basis_identity, ← eliminant_basis_identity] at hcombination
  intro hzero
  have : affineJacobianDet
      (MvPolynomial.X 0 + embedY shapeTailPolynomial)
      (MvPolynomial.X 1 ^ 2 * embedY residualPolynomialComplex) point = 0 := by
    rw [hcombination, hzero, mul_zero]
  exact shape_affineJacobianDet_ne_zero point hpoint this

/-- IFT-ready form of finite transversality for the exact source sextic and septic. -/
theorem source_affineJacobian_isInvertible
    (point : Fin 2 → ℂ) (hpoint : point ∈ finiteIntersectionPoints) :
    (affineJacobian chapterVISection103AffinePolynomial
      chapterVISection103ReducedAffinePolynomial point).IsInvertible :=
  affineJacobian_isInvertible_of_det_ne_zero _ _ _
    (source_affineJacobianDet_ne_zero point hpoint)

end PoincareChapterVI.AffineTransversality
