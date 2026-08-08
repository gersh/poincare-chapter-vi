/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import Mathlib.LinearAlgebra.Determinant
import PoincareChapterVI.Section103.MovingAlgebraicBranches

/-!
# Poincaré's two-essential-coordinate argument in Chapter VI, §102

On pp. 328--329 Poincaré argues that, if the additional uniform integral existed, the singular
roots would depend on only two of the three orientation parameters.  Consequently the Jacobian
of any three roots with respect to inclination and the two perihelion longitudes would vanish.

The following formulation records exactly the differential consequence used in §103.  It is
deliberately weaker than requiring the roots to be locally constant on a straight parameter line:
their differentials merely factor through a two-dimensional space.  Rank--nullity then supplies
one nonzero orientation direction in which every singular root is stationary.  The concrete
moving-curve formalization turns that stationarity into Poincaré's equation (2), and its
LeanCompCert certificate gives the contradiction.

The remaining historical input is the `rank_le_two` field (or, in the optional coordinate
formulation below, `factors`): it must ultimately be derived from the coefficient relations
supplied by the putative uniform integral in Chapter V and the singularity classification in
§§93--100.
-/

noncomputable section

namespace PoincareChapterVI.ChapterVISection102

open AffineIntersectionCount
open MovingAlgebraicBranches

private abbrev Orientation := Fin 3 → ℂ
private abbrev Essential := Fin 2 → ℂ
private abbrev FiniteSingularPoint :=
  { point : Fin 2 → ℂ // point ∈ finiteIntersectionPoints }

/-- The block-triangular determinant reduction on p. 329.  The first-kind parameters `τ,τ'`
depend separately and nontrivially on the two eccentricities, so vanishing of the full five-by-five
Jacobian forces vanishing of the three-by-three orientation Jacobian of any three second-kind
roots.  The lower-left block is unrestricted because those roots may also depend on eccentricity. -/
theorem orientationJacobian_det_eq_zero_of_fullJacobian_det_eq_zero
    (dτ dτ' : ℂ) (hdτ : dτ ≠ 0) (hdτ' : dτ' ≠ 0)
    (eccentricityDerivative : Matrix (Fin 3) (Fin 2) ℂ)
    (orientationDerivative : Matrix (Fin 3) (Fin 3) ℂ)
    (hfull : (Matrix.fromBlocks (Matrix.diagonal ![dτ, dτ']) 0
      eccentricityDerivative orientationDerivative).det = 0) :
    orientationDerivative.det = 0 := by
  rw [Matrix.det_fromBlocks_zero₁₂] at hfull
  have hdiagonal : (Matrix.diagonal ![dτ, dτ'] : Matrix (Fin 2) (Fin 2) ℂ).det =
      dτ * dτ' := by
    simp [Fin.prod_univ_succ]
  rw [hdiagonal] at hfull
  exact (mul_eq_zero.mp hfull).resolve_left (mul_ne_zero hdτ hdτ')

/-- Intrinsic differential-rank formulation of the last sentence of §102: with eccentricities
fixed, the complete collection of second-kind singular roots has rank at most two as a function
of the three orientation parameters. -/
structure SecondKindRootDifferential where
  differential : Orientation →L[ℂ] (FiniteSingularPoint → ℂ)
  agrees : ∀ (rotation : Orientation) (point : FiniteSingularPoint),
    branchSingularityParameterDerivative rotation point.1 point.2 =
      differential rotation point
  rank_le_two : Module.finrank ℂ differential.toLinearMap.range ≤ 2

/-- The root differential is not additional data: it is canonically assembled from the exact
directional derivatives of the 24 moving algebraic IFT branches. -/
def concreteSecondKindRootDifferential :
    Orientation →L[ℂ] (FiniteSingularPoint → ℂ) :=
  ContinuousLinearMap.pi fun point ↦
    branchSingularityDifferential point.1 point.2

@[simp] theorem concreteSecondKindRootDifferential_apply
    (rotation : Orientation) (point : FiniteSingularPoint) :
    concreteSecondKindRootDifferential rotation point =
      branchSingularityParameterDerivative rotation point.1 point.2 := by
  exact branchSingularityDifferential_apply rotation point.1 point.2

/-- Package the canonical differential once the sole §102 rank bound is known. -/
def concreteSecondKindRootDifferentialData
    (hrank : Module.finrank ℂ
      concreteSecondKindRootDifferential.toLinearMap.range ≤ 2) :
    SecondKindRootDifferential where
  differential := concreteSecondKindRootDifferential
  agrees := fun rotation point ↦
    (concreteSecondKindRootDifferential_apply rotation point).symm
  rank_le_two := hrank

/-- A rank-at-most-two differential on the three orientation parameters has a nonzero common
stationary direction for all twenty-four roots. -/
theorem exists_nonzero_stationary_direction (roots : SecondKindRootDifferential) :
    ∃ rotation : Orientation, rotation ≠ 0 ∧ BranchSingularityStationarity rotation := by
  have hkernel : LinearMap.ker roots.differential.toLinearMap ≠ ⊥ := by
    intro hbot
    have hinjective : Function.Injective roots.differential :=
      LinearMap.ker_eq_bot.mp hbot
    have hrange : Module.finrank ℂ roots.differential.toLinearMap.range =
        Module.finrank ℂ Orientation :=
      LinearMap.finrank_range_of_inj hinjective
    have : Module.finrank ℂ Orientation ≤ 2 := hrange ▸ roots.rank_le_two
    norm_num at this
  obtain ⟨rotation, hrotationKernel, hrotationNonzero⟩ :=
    (LinearMap.ker roots.differential.toLinearMap).ne_bot_iff.mp hkernel
  refine ⟨rotation, hrotationNonzero, ⟨?_⟩⟩
  intro point hpoint
  let indexedPoint : FiniteSingularPoint := ⟨point, hpoint⟩
  have hzero : roots.differential rotation = 0 := hrotationKernel
  rw [roots.agrees rotation indexedPoint]
  exact congrFun hzero indexedPoint

/-- Poincaré's §102 rank conclusion contradicts the fully formalized §103 calculation. -/
theorem not_rankAtMostTwo_secondKindRootDifferential
    (roots : SecondKindRootDifferential) : False := by
  obtain ⟨rotation, hrotationNonzero, hstationary⟩ :=
    exists_nonzero_stationary_direction roots
  exact hrotationNonzero
    (rotation_eq_zero_of_branchSingularityStationarity rotation hstationary)

/-- The remaining §102 statement in its minimal form: the exact, already-constructed root
differential cannot have rank at most two.  Thus deriving Poincaré's asserted rank bound from a
putative uniform integral immediately finishes the §102--103 contradiction. -/
theorem not_concreteSecondKindRootDifferential_rank_le_two
    (hrank : Module.finrank ℂ
      concreteSecondKindRootDifferential.toLinearMap.range ≤ 2) :
    False :=
  not_rankAtMostTwo_secondKindRootDifferential
    (concreteSecondKindRootDifferentialData hrank)

/-- Differential form of Poincaré's assertion that all second-kind singular roots depend on only
two essential coordinates.  Each root has a covector on the two-dimensional essential-coordinate
space, and its derivative in an orientation direction is the pullback of that covector. -/
structure TwoCoordinateDifferentialFactorization
    (essentialCoordinates : Orientation →L[ℂ] Essential) where
  singularityDifferential :
    (point : Fin 2 → ℂ) → point ∈ finiteIntersectionPoints → Essential →L[ℂ] ℂ
  factors : ∀ (rotation : Orientation) (point : Fin 2 → ℂ)
      (hpoint : point ∈ finiteIntersectionPoints),
    branchSingularityParameterDerivative rotation point hpoint =
      singularityDifferential point hpoint (essentialCoordinates rotation)

/-- A direction in the kernel of the two essential coordinates makes every concrete singular
branch stationary to first order. -/
theorem stationarity_of_mem_ker
    (essentialCoordinates : Orientation →L[ℂ] Essential)
    (factorization : TwoCoordinateDifferentialFactorization essentialCoordinates)
    (rotation : Orientation) (hrotation : essentialCoordinates rotation = 0) :
    BranchSingularityStationarity rotation where
  derivative_eq_zero := by
    intro point hpoint
    rw [factorization.factors rotation point hpoint, hrotation]
    exact map_zero _

/-- Differential of any three selected singular roots.  Poincaré writes the determinant of a
coordinate matrix for this map on p. 329. -/
def threeRootDifferential
    (essentialCoordinates : Orientation →L[ℂ] Essential)
    (factorization : TwoCoordinateDifferentialFactorization essentialCoordinates)
    (point : Fin 3 → Fin 2 → ℂ)
    (hpoint : ∀ i, point i ∈ finiteIntersectionPoints) : Orientation →L[ℂ] Orientation :=
  (ContinuousLinearMap.pi fun i ↦
    factorization.singularityDifferential (point i) (hpoint i)).comp essentialCoordinates

/-- The three-root Jacobian in §102 vanishes because its differential factors through a
two-dimensional space. -/
theorem threeRootDifferential_det_eq_zero
    (essentialCoordinates : Orientation →L[ℂ] Essential)
    (factorization : TwoCoordinateDifferentialFactorization essentialCoordinates)
    (point : Fin 3 → Fin 2 → ℂ)
    (hpoint : ∀ i, point i ∈ finiteIntersectionPoints) :
    (threeRootDifferential essentialCoordinates factorization point hpoint).toLinearMap.det = 0 := by
  rw [LinearMap.det_eq_zero_iff_ker_ne_bot]
  have hdimension : Module.finrank ℂ Essential < Module.finrank ℂ Orientation := by
    simp
  have hkernel : LinearMap.ker essentialCoordinates.toLinearMap ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt hdimension
  obtain ⟨rotation, hrotationKernel, hrotationNonzero⟩ :=
    (LinearMap.ker essentialCoordinates.toLinearMap).ne_bot_iff.mp hkernel
  apply (LinearMap.ker
    (threeRootDifferential essentialCoordinates factorization point hpoint).toLinearMap).ne_bot_iff.mpr
  refine ⟨rotation, ?_, hrotationNonzero⟩
  have hrotationZero : essentialCoordinates rotation = 0 := hrotationKernel
  change threeRootDifferential essentialCoordinates factorization point hpoint rotation = 0
  ext i
  simp [threeRootDifferential, hrotationZero]

/-- Source-faithful §102--103 contradiction at the differential level.  A common factorization
of the singular-root differentials through two coordinates supplies a nonzero stationary
rotation; the concrete §103 branch calculation and finite certificate force it to be zero. -/
theorem not_twoCoordinateDifferentialFactorization
    (essentialCoordinates : Orientation →L[ℂ] Essential)
    (factorization : TwoCoordinateDifferentialFactorization essentialCoordinates) :
    False := by
  have hdimension : Module.finrank ℂ Essential < Module.finrank ℂ Orientation := by
    simp
  have hkernel : LinearMap.ker essentialCoordinates.toLinearMap ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt hdimension
  obtain ⟨rotation, hrotationKernel, hrotationNonzero⟩ :=
    (LinearMap.ker essentialCoordinates.toLinearMap).ne_bot_iff.mp hkernel
  have hcoordinates : essentialCoordinates rotation = 0 := hrotationKernel
  have hrotationZero : rotation = 0 :=
    rotation_eq_zero_of_branchSingularityStationarity rotation
      (stationarity_of_mem_ker essentialCoordinates factorization rotation hcoordinates)
  exact hrotationNonzero hrotationZero

end PoincareChapterVI.ChapterVISection102
