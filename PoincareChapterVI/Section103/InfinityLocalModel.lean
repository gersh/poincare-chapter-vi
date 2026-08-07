/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.Section103.LocalAlgebra
import PoincareChapterVI.Section103.TriangularAlgebra

/-!
# The triangular model as a quotient of the plane local ring

This file evaluates the two local coordinates in the explicit eight-dimensional triangular
algebra and extends that evaluation through the localization at the affine origin.  The extension
is possible because every polynomial outside the origin ideal has nonzero constant coordinate,
and hence maps to a unit in the finite model.
-/

noncomputable section

namespace PoincareChapterVI

namespace InfinityLocalModel

open TriangularAlgebra

variable {K : Type*} [Field K] (a b c d : K)

abbrev Model := TriangularAlgebra K a b c d

def constantCoeffAlgHom : Model a b c d →ₐ[K] K where
  __ := constantCoeff
  commutes' r := by
    change (C (a := a) (b := b) (c := c) (d := d) r).coeff 0 = r
    rfl

def polynomialAlgHom : PlanePolynomial K →ₐ[K] Model a b c d :=
  MvPolynomial.aeval ![
    Y (K := K) (a := a) (b := b) (c := c) (d := d),
    Z (K := K) (a := a) (b := b) (c := c) (d := d)]

@[simp] theorem polynomialAlgHom_X_zero :
    polynomialAlgHom a b c d (MvPolynomial.X (0 : Fin 2)) =
      Y (K := K) (a := a) (b := b) (c := c) (d := d) := by
  simp [polynomialAlgHom]

@[simp] theorem polynomialAlgHom_X_one :
    polynomialAlgHom a b c d (MvPolynomial.X (1 : Fin 2)) =
      Z (K := K) (a := a) (b := b) (c := c) (d := d) := by
  simp [polynomialAlgHom]

theorem constantCoeff_polynomialAlgHom (f : PlanePolynomial K) :
    constantCoeffAlgHom a b c d (polynomialAlgHom a b c d f) =
      MvPolynomial.eval (0 : Fin 2 → K) f := by
  let lhs : PlanePolynomial K →ₐ[K] K :=
    (constantCoeffAlgHom a b c d).comp (polynomialAlgHom a b c d)
  let rhs : PlanePolynomial K →ₐ[K] K := MvPolynomial.aeval 0
  have h : lhs = rhs := by
    ext i
    fin_cases i <;>
      simp [lhs, rhs, constantCoeffAlgHom, polynomialAlgHom,
        Y, Z, TriangularAlgebra.basis, linearEquivTuple]
  exact DFunLike.congr_fun h f

theorem polynomialAlgHom_unit (s : affinePointComplement K 0) :
    IsUnit (polynomialAlgHom a b c d s) := by
  rw [isUnit_iff_coeff_zero_ne]
  change constantCoeffAlgHom a b c d (polynomialAlgHom a b c d s) ≠ 0
  rw [constantCoeff_polynomialAlgHom]
  simpa [affinePointComplement, affinePointIdeal, Ideal.primeCompl,
    RingHom.mem_ker] using s.property

def localRingHom : PlaneLocalRing K 0 →+* Model a b c d :=
  IsLocalization.lift (polynomialAlgHom_unit a b c d)

theorem localRingHom_algebraMap (f : PlanePolynomial K) :
    localRingHom a b c d
        (algebraMap (PlanePolynomial K) (PlaneLocalRing K 0) f) =
      polynomialAlgHom a b c d f :=
  IsLocalization.lift_eq (polynomialAlgHom_unit a b c d) f

private def py : PlanePolynomial K := MvPolynomial.X 0
private def pz : PlanePolynomial K := MvPolynomial.X 1

def firstRelation : PlanePolynomial K :=
  py ^ 2 + MvPolynomial.C a * pz ^ 4 + MvPolynomial.C b * pz ^ 5

def secondRelation : PlanePolynomial K :=
  py * pz ^ 2 + MvPolynomial.C c * pz ^ 4 + MvPolynomial.C d * pz ^ 5

def thirdRelation : PlanePolynomial K := pz ^ 6

@[simp] theorem polynomialAlgHom_firstRelation :
    polynomialAlgHom a b c d (firstRelation a b) = 0 := by
  simpa [firstRelation, py, pz] using
    (Y_sq (K := K) (a := a) (b := b) (c := c) (d := d))

@[simp] theorem polynomialAlgHom_secondRelation :
    polynomialAlgHom a b c d (secondRelation c d) = 0 := by
  simpa [secondRelation, py, pz] using
    (Y_mul_Z_sq (K := K) (a := a) (b := b) (c := c) (d := d))

@[simp] theorem polynomialAlgHom_thirdRelation :
    polynomialAlgHom a b c d thirdRelation = 0 := by
  simpa [thirdRelation, pz] using
    (Z_pow_six (K := K) (a := a) (b := b) (c := c) (d := d))

def localModelIdeal : Ideal (PlaneLocalRing K 0) :=
  Ideal.span {
    algebraMap (PlanePolynomial K) (PlaneLocalRing K 0) (firstRelation a b),
    algebraMap (PlanePolynomial K) (PlaneLocalRing K 0) (secondRelation c d),
    algebraMap (PlanePolynomial K) (PlaneLocalRing K 0) thirdRelation}

theorem localModelIdeal_le_ker :
    localModelIdeal a b c d ≤ RingHom.ker (localRingHom a b c d) := by
  refine Ideal.span_le.2 ?_
  intro f hf
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hf
  rcases hf with rfl | rfl | rfl <;>
    simp [RingHom.mem_ker, localRingHom_algebraMap]

end InfinityLocalModel

end PoincareChapterVI
