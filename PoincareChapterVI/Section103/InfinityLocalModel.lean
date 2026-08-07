/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.Section103.LocalAlgebra
import PoincareChapterVI.Section103.OriginMultiplicity
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

/-- Adjoining one socle generator produces a covering ideal.  The hypothesis says that the
maximal ideal annihilates the new class modulo the old ideal. -/
theorem covBy_span_singleton_sup
    (A : Type*) [CommRing A] [IsLocalRing A] (I : Ideal A) (x : A)
    (hx : x ∉ I)
    (hmx : ∀ r ∈ IsLocalRing.maximalIdeal A, r * x ∈ I) :
    I ⋖ Ideal.span {x} ⊔ I := by
  rw [SetLike.covBy_iff]
  refine ⟨lt_of_le_of_ne le_sup_right ?_, ?_⟩
  · intro h
    apply hx
    rw [h]
    exact Ideal.mem_sup_left (Ideal.mem_span_singleton_self x)
  · intro L z hIL hLU hzI hzL
    have hzU : z ∈ Ideal.span {x} ⊔ I := hLU hzL
    obtain ⟨r, q, hq, hr⟩ := Ideal.mem_span_singleton_sup.mp hzU
    have hr_unit : IsUnit r := by
      by_contra hr_nonunit
      have hrm : r ∈ IsLocalRing.maximalIdeal A := by
        rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
        exact hr_nonunit
      apply hzI
      rw [← hr]
      exact I.add_mem (hmx r hrm) hq
    apply le_antisymm hLU
    refine sup_le ?_ hIL
    rw [Ideal.span_singleton_le_iff_mem]
    apply (Ideal.unit_mul_mem_iff_mem L hr_unit).1
    have hrxL : r * x ∈ L := by
      rw [← hr] at hzL
      simpa using L.sub_mem hzL (hIL hq)
    exact hrxL

def localY : PlaneLocalRing K 0 :=
  algebraMap (PlanePolynomial K) (PlaneLocalRing K 0) py

def localZ : PlaneLocalRing K 0 :=
  algebraMap (PlanePolynomial K) (PlaneLocalRing K 0) pz

@[simp] theorem localRingHom_localY :
    localRingHom a b c d localY =
      Y (K := K) (a := a) (b := b) (c := c) (d := d) := by
  simp [localY, localRingHom_algebraMap, py]

@[simp] theorem localRingHom_localZ :
    localRingHom a b c d localZ =
      Z (K := K) (a := a) (b := b) (c := c) (d := d) := by
  simp [localZ, localRingHom_algebraMap, pz]

theorem affinePointIdeal_zero_eq_span_vars :
    affinePointIdeal K 0 = Ideal.span {py, pz} := by
  have hpoint : affinePointIdeal K 0 = MvPolynomial.idealOfVars (Fin 2) K := by
    ext f
    rw [mem_idealOfVars_iff_constantCoeff_eq_zero]
    simp [affinePointIdeal]
  have hrange : Set.range (MvPolynomial.X : Fin 2 → PlanePolynomial K) = {py, pz} := by
    ext f
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp [py, pz]
    · intro hf
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hf
      rcases hf with rfl | rfl
      · exact ⟨0, by simp [py]⟩
      · exact ⟨1, by simp [pz]⟩
  rw [hpoint, MvPolynomial.idealOfVars, hrange]

local instance pointIdeal_isPrime : (affinePointIdeal K 0).IsPrime :=
  affinePointIdeal_isPrime K 0

local instance planeLocalRing_isLocalRing : IsLocalRing (PlaneLocalRing K 0) := by
  infer_instance

theorem maximalIdeal_eq_span_localY_localZ :
    IsLocalRing.maximalIdeal (PlaneLocalRing K 0) = Ideal.span {localY, localZ} := by
  rw [← Localization.AtPrime.map_eq_maximalIdeal]
  let φ : PlanePolynomial K →+* PlaneLocalRing K 0 := algebraMap _ _
  calc
    Ideal.map φ (affinePointIdeal K 0) = Ideal.map φ (Ideal.span {py, pz}) :=
      congrArg (Ideal.map φ) (affinePointIdeal_zero_eq_span_vars (K := K))
    _ = Ideal.span (φ '' {py, pz}) := Ideal.map_span φ _
    _ = Ideal.span {φ py, φ pz} := by
      congr 1
      ext f
      simp [eq_comm]
    _ = Ideal.span {localY, localZ} := rfl

def filtrationIdeal0 : Ideal (PlaneLocalRing K 0) := localModelIdeal a b c d
def filtrationIdeal1 : Ideal (PlaneLocalRing K 0) := Ideal.span {localZ ^ 5} ⊔ filtrationIdeal0 a b c d
def filtrationIdeal2 : Ideal (PlaneLocalRing K 0) := Ideal.span {localZ ^ 4} ⊔ filtrationIdeal1 a b c d
def filtrationIdeal3 : Ideal (PlaneLocalRing K 0) := Ideal.span {localZ ^ 3} ⊔ filtrationIdeal2 a b c d
def filtrationIdeal4 : Ideal (PlaneLocalRing K 0) := Ideal.span {localZ ^ 2} ⊔ filtrationIdeal3 a b c d
def filtrationIdeal5 : Ideal (PlaneLocalRing K 0) :=
  Ideal.span {localY * localZ} ⊔ filtrationIdeal4 a b c d
def filtrationIdeal6 : Ideal (PlaneLocalRing K 0) := Ideal.span {localZ} ⊔ filtrationIdeal5 a b c d
def filtrationIdeal7 : Ideal (PlaneLocalRing K 0) := Ideal.span {localY} ⊔ filtrationIdeal6 a b c d

theorem filtrationIdeal0_le_filtrationIdeal1 :
    filtrationIdeal0 a b c d ≤ filtrationIdeal1 a b c d := le_sup_right

theorem filtrationIdeal1_le_filtrationIdeal2 :
    filtrationIdeal1 a b c d ≤ filtrationIdeal2 a b c d := le_sup_right

theorem filtrationIdeal2_le_filtrationIdeal3 :
    filtrationIdeal2 a b c d ≤ filtrationIdeal3 a b c d := le_sup_right

theorem filtrationIdeal3_le_filtrationIdeal4 :
    filtrationIdeal3 a b c d ≤ filtrationIdeal4 a b c d := le_sup_right

theorem filtrationIdeal4_le_filtrationIdeal5 :
    filtrationIdeal4 a b c d ≤ filtrationIdeal5 a b c d := le_sup_right

theorem filtrationIdeal5_le_filtrationIdeal6 :
    filtrationIdeal5 a b c d ≤ filtrationIdeal6 a b c d := le_sup_right

theorem filtrationIdeal6_le_filtrationIdeal7 :
    filtrationIdeal6 a b c d ≤ filtrationIdeal7 a b c d := le_sup_right

theorem coordinate_zero_of_mem_adjoin
    (I : Ideal (PlaneLocalRing K 0)) (x q : PlaneLocalRing K 0) (i : Fin 8)
    (hI : ∀ u ∈ I, (localRingHom a b c d u).coeff i = 0)
    (hx : ∀ r : PlaneLocalRing K 0,
      (localRingHom a b c d r * localRingHom a b c d x).coeff i = 0)
    (hq : q ∈ Ideal.span {x} ⊔ I) :
    (localRingHom a b c d q).coeff i = 0 := by
  obtain ⟨r, u, hu, hru⟩ := Ideal.mem_span_singleton_sup.mp hq
  rw [← hru, map_add, map_mul]
  rw [TriangularAlgebra.coeff_add, hx r, hI u hu, add_zero]

theorem coordinate_zero_of_mem_filtrationIdeal0
    (q : PlaneLocalRing K 0) (hq : q ∈ filtrationIdeal0 a b c d) (i : Fin 8) :
    (localRingHom a b c d q).coeff i = 0 := by
  have hqker : q ∈ RingHom.ker (localRingHom a b c d) :=
    localModelIdeal_le_ker a b c d hq
  simpa [RingHom.mem_ker] using congrArg (fun x : Model a b c d => x.coeff i) hqker

private theorem mul_Z_pow_five_coord_four (r : Model a b c d) :
    (r * Z ^ 5).coeff 4 = 0 := by
  simp [Z, TriangularAlgebra.basis, linearEquivTuple, TriangularAlgebra.mul, pow_succ]

private theorem mul_Z_pow_five_coord_three (r : Model a b c d) :
    (r * Z ^ 5).coeff 3 = 0 := by
  simp [Z, TriangularAlgebra.basis, linearEquivTuple, TriangularAlgebra.mul, pow_succ]

private theorem mul_Z_pow_four_coord_three (r : Model a b c d) :
    (r * Z ^ 4).coeff 3 = 0 := by
  simp [Z, TriangularAlgebra.basis, linearEquivTuple, TriangularAlgebra.mul, pow_succ]

theorem localZ_pow_five_not_mem_filtrationIdeal0 :
    localZ ^ 5 ∉ filtrationIdeal0 a b c d := by
  intro hmem
  have hzero := coordinate_zero_of_mem_filtrationIdeal0 a b c d (localZ ^ 5) hmem 5
  simp [localRingHom_localZ, Z, TriangularAlgebra.basis, linearEquivTuple,
    TriangularAlgebra.mul, pow_succ] at hzero

theorem localZ_pow_four_not_mem_filtrationIdeal1 :
    localZ ^ 4 ∉ filtrationIdeal1 a b c d := by
  intro hmem
  have hzero : (localRingHom a b c d (localZ ^ 4)).coeff 4 = 0 :=
    coordinate_zero_of_mem_adjoin a b c d (filtrationIdeal0 a b c d)
      (localZ ^ 5) (localZ ^ 4) 4
      (fun u hu => coordinate_zero_of_mem_filtrationIdeal0 a b c d u hu 4)
      (fun r => by simpa using (mul_Z_pow_five_coord_four
        (a := a) (b := b) (c := c) (d := d) (localRingHom a b c d r))) hmem
  simp [localRingHom_localZ, Z, TriangularAlgebra.basis, linearEquivTuple,
    TriangularAlgebra.mul, pow_succ] at hzero

theorem localZ_pow_three_not_mem_filtrationIdeal2 :
    localZ ^ 3 ∉ filtrationIdeal2 a b c d := by
  intro hmem
  have hI1 : ∀ u ∈ filtrationIdeal1 a b c d,
      (localRingHom a b c d u).coeff 3 = 0 := by
    intro u hu
    exact coordinate_zero_of_mem_adjoin a b c d (filtrationIdeal0 a b c d)
      (localZ ^ 5) u 3
      (fun v hv => coordinate_zero_of_mem_filtrationIdeal0 a b c d v hv 3)
      (fun r => by simpa using (mul_Z_pow_five_coord_three
        (a := a) (b := b) (c := c) (d := d) (localRingHom a b c d r))) hu
  have hzero : (localRingHom a b c d (localZ ^ 3)).coeff 3 = 0 :=
    coordinate_zero_of_mem_adjoin a b c d (filtrationIdeal1 a b c d)
      (localZ ^ 4) (localZ ^ 3) 3 hI1
      (fun r => by simpa using (mul_Z_pow_four_coord_three
        (a := a) (b := b) (c := c) (d := d) (localRingHom a b c d r))) hmem
  simp [localRingHom_localZ, Z, TriangularAlgebra.basis, linearEquivTuple,
    TriangularAlgebra.mul, pow_succ] at hzero

theorem localZ_pow_two_not_mem_filtrationIdeal3 :
    localZ ^ 2 ∉ filtrationIdeal3 a b c d := by
  intro hmem
  have hI1 : ∀ u ∈ filtrationIdeal1 a b c d,
      (localRingHom a b c d u).coeff 2 = 0 := by
    intro u hu
    exact coordinate_zero_of_mem_adjoin a b c d (filtrationIdeal0 a b c d)
      (localZ ^ 5) u 2
      (fun v hv => coordinate_zero_of_mem_filtrationIdeal0 a b c d v hv 2)
      (fun r => by
        simp [localRingHom_localZ, Z, TriangularAlgebra.basis, linearEquivTuple,
          TriangularAlgebra.mul, pow_succ]) hu
  have hI2 : ∀ u ∈ filtrationIdeal2 a b c d,
      (localRingHom a b c d u).coeff 2 = 0 := by
    intro u hu
    exact coordinate_zero_of_mem_adjoin a b c d (filtrationIdeal1 a b c d)
      (localZ ^ 4) u 2 hI1
      (fun r => by
        simp [localRingHom_localZ, Z, TriangularAlgebra.basis, linearEquivTuple,
          TriangularAlgebra.mul, pow_succ]) hu
  have hI3 : ∀ u ∈ filtrationIdeal3 a b c d,
      (localRingHom a b c d u).coeff 2 = 0 := by
    intro u hu
    exact coordinate_zero_of_mem_adjoin a b c d (filtrationIdeal2 a b c d)
      (localZ ^ 3) u 2 hI2
      (fun r => by
        simp [localRingHom_localZ, Z, TriangularAlgebra.basis, linearEquivTuple,
          TriangularAlgebra.mul, pow_succ]) hu
  have hzero : (localRingHom a b c d (localZ ^ 2)).coeff 2 = 0 := hI3 _ hmem
  simp [localRingHom_localZ, Z, TriangularAlgebra.basis, linearEquivTuple,
    TriangularAlgebra.mul, pow_succ] at hzero

theorem coordinate_zero_of_mem_filtrationIdeal4 (i : Fin 8)
    (h5 : ∀ r : PlaneLocalRing K 0,
      (localRingHom a b c d r * Z ^ 5).coeff i = 0)
    (h4 : ∀ r : PlaneLocalRing K 0,
      (localRingHom a b c d r * Z ^ 4).coeff i = 0)
    (h3 : ∀ r : PlaneLocalRing K 0,
      (localRingHom a b c d r * Z ^ 3).coeff i = 0)
    (h2 : ∀ r : PlaneLocalRing K 0,
      (localRingHom a b c d r * Z ^ 2).coeff i = 0)
    (u : PlaneLocalRing K 0) (hu : u ∈ filtrationIdeal4 a b c d) :
    (localRingHom a b c d u).coeff i = 0 := by
  have hI1 : ∀ v ∈ filtrationIdeal1 a b c d,
      (localRingHom a b c d v).coeff i = 0 := by
    intro v hv
    exact coordinate_zero_of_mem_adjoin a b c d (filtrationIdeal0 a b c d)
      (localZ ^ 5) v i
      (fun w hw => coordinate_zero_of_mem_filtrationIdeal0 a b c d w hw i)
      (fun r => by simpa [localRingHom_localZ] using h5 r) hv
  have hI2 : ∀ v ∈ filtrationIdeal2 a b c d,
      (localRingHom a b c d v).coeff i = 0 := by
    intro v hv
    exact coordinate_zero_of_mem_adjoin a b c d (filtrationIdeal1 a b c d)
      (localZ ^ 4) v i hI1
      (fun r => by simpa [localRingHom_localZ] using h4 r) hv
  have hI3 : ∀ v ∈ filtrationIdeal3 a b c d,
      (localRingHom a b c d v).coeff i = 0 := by
    intro v hv
    exact coordinate_zero_of_mem_adjoin a b c d (filtrationIdeal2 a b c d)
      (localZ ^ 3) v i hI2
      (fun r => by simpa [localRingHom_localZ] using h3 r) hv
  exact coordinate_zero_of_mem_adjoin a b c d (filtrationIdeal3 a b c d)
    (localZ ^ 2) u i hI3
    (fun r => by simpa [localRingHom_localZ] using h2 r) hu

theorem coordinate_zero_of_mem_filtrationIdeal5 (i : Fin 8)
    (h4 : ∀ u ∈ filtrationIdeal4 a b c d,
      (localRingHom a b c d u).coeff i = 0)
    (hyz : ∀ r : PlaneLocalRing K 0,
      (localRingHom a b c d r * (Y * Z)).coeff i = 0)
    (u : PlaneLocalRing K 0) (hu : u ∈ filtrationIdeal5 a b c d) :
    (localRingHom a b c d u).coeff i = 0 :=
  coordinate_zero_of_mem_adjoin a b c d (filtrationIdeal4 a b c d)
    (localY * localZ) u i h4
    (fun r => by simpa [localRingHom_localY, localRingHom_localZ] using hyz r) hu

theorem coordinate_zero_of_mem_filtrationIdeal6 (i : Fin 8)
    (h5 : ∀ u ∈ filtrationIdeal5 a b c d,
      (localRingHom a b c d u).coeff i = 0)
    (hz : ∀ r : PlaneLocalRing K 0,
      (localRingHom a b c d r * Z).coeff i = 0)
    (u : PlaneLocalRing K 0) (hu : u ∈ filtrationIdeal6 a b c d) :
    (localRingHom a b c d u).coeff i = 0 :=
  coordinate_zero_of_mem_adjoin a b c d (filtrationIdeal5 a b c d)
    localZ u i h5
    (fun r => by simpa [localRingHom_localZ] using hz r) hu

theorem localY_mul_localZ_not_mem_filtrationIdeal4 :
    localY * localZ ∉ filtrationIdeal4 a b c d := by
  intro hmem
  have hzero : (localRingHom a b c d (localY * localZ)).coeff 7 = 0 :=
    coordinate_zero_of_mem_filtrationIdeal4 a b c d 7
      (fun r => by simp [Z, TriangularAlgebra.basis, linearEquivTuple,
        TriangularAlgebra.mul, pow_succ])
      (fun r => by simp [Z, TriangularAlgebra.basis, linearEquivTuple,
        TriangularAlgebra.mul, pow_succ])
      (fun r => by simp [Z, TriangularAlgebra.basis, linearEquivTuple,
        TriangularAlgebra.mul, pow_succ])
      (fun r => by simp [Z, TriangularAlgebra.basis, linearEquivTuple,
        TriangularAlgebra.mul, pow_succ]) _ hmem
  simp [localRingHom_localY, localRingHom_localZ, Y, Z, TriangularAlgebra.basis,
    linearEquivTuple, TriangularAlgebra.mul] at hzero

theorem localZ_not_mem_filtrationIdeal5 :
    localZ ∉ filtrationIdeal5 a b c d := by
  intro hmem
  have hI4 : ∀ u ∈ filtrationIdeal4 a b c d,
      (localRingHom a b c d u).coeff 1 = 0 :=
    coordinate_zero_of_mem_filtrationIdeal4 a b c d 1
      (fun r => by simp [Z, TriangularAlgebra.basis, linearEquivTuple,
        TriangularAlgebra.mul, pow_succ])
      (fun r => by simp [Z, TriangularAlgebra.basis, linearEquivTuple,
        TriangularAlgebra.mul, pow_succ])
      (fun r => by simp [Z, TriangularAlgebra.basis, linearEquivTuple,
        TriangularAlgebra.mul, pow_succ])
      (fun r => by simp [Z, TriangularAlgebra.basis, linearEquivTuple,
        TriangularAlgebra.mul, pow_succ])
  have hzero : (localRingHom a b c d localZ).coeff 1 = 0 :=
    coordinate_zero_of_mem_filtrationIdeal5 a b c d 1 hI4
      (fun r => by simp [Y, Z, TriangularAlgebra.basis, linearEquivTuple,
        TriangularAlgebra.mul]) _ hmem
  simp [localRingHom_localZ, Z, TriangularAlgebra.basis, linearEquivTuple] at hzero

theorem localY_not_mem_filtrationIdeal6 :
    localY ∉ filtrationIdeal6 a b c d := by
  intro hmem
  have hI4 : ∀ u ∈ filtrationIdeal4 a b c d,
      (localRingHom a b c d u).coeff 6 = 0 :=
    coordinate_zero_of_mem_filtrationIdeal4 a b c d 6
      (fun r => by simp [Z, TriangularAlgebra.basis, linearEquivTuple,
        TriangularAlgebra.mul, pow_succ])
      (fun r => by simp [Z, TriangularAlgebra.basis, linearEquivTuple,
        TriangularAlgebra.mul, pow_succ])
      (fun r => by simp [Z, TriangularAlgebra.basis, linearEquivTuple,
        TriangularAlgebra.mul, pow_succ])
      (fun r => by simp [Z, TriangularAlgebra.basis, linearEquivTuple,
        TriangularAlgebra.mul, pow_succ])
  have hI5 : ∀ u ∈ filtrationIdeal5 a b c d,
      (localRingHom a b c d u).coeff 6 = 0 :=
    coordinate_zero_of_mem_filtrationIdeal5 a b c d 6 hI4
      (fun r => by simp [Y, Z, TriangularAlgebra.basis, linearEquivTuple,
        TriangularAlgebra.mul])
  have hzero : (localRingHom a b c d localY).coeff 6 = 0 :=
    coordinate_zero_of_mem_filtrationIdeal6 a b c d 6 hI5
      (fun r => by simp [Z, TriangularAlgebra.basis, linearEquivTuple,
        TriangularAlgebra.mul]) _ hmem
  simp [localRingHom_localY, Y, TriangularAlgebra.basis, linearEquivTuple] at hzero

theorem local_firstRelation_mem_filtrationIdeal0 :
    localY ^ 2 + algebraMap K (PlaneLocalRing K 0) a * localZ ^ 4 +
      algebraMap K (PlaneLocalRing K 0) b * localZ ^ 5 ∈ filtrationIdeal0 a b c d := by
  have hC (r : K) :
      algebraMap (PlanePolynomial K) (PlaneLocalRing K 0) (MvPolynomial.C r) =
        algebraMap K (PlaneLocalRing K 0) r := by
    rw [MvPolynomial.C_eq_algebraMap]
    exact IsScalarTower.algebraMap_apply K (PlanePolynomial K) (PlaneLocalRing K 0) r
  have h := Ideal.subset_span (s := {
    algebraMap (PlanePolynomial K) (PlaneLocalRing K 0) (firstRelation a b),
    algebraMap (PlanePolynomial K) (PlaneLocalRing K 0) (secondRelation c d),
    algebraMap (PlanePolynomial K) (PlaneLocalRing K 0) thirdRelation})
    (Set.mem_insert _ _)
  simpa [filtrationIdeal0, localModelIdeal, firstRelation, localY, localZ, py, pz, hC]
    using h

theorem local_secondRelation_mem_filtrationIdeal0 :
    localY * localZ ^ 2 + algebraMap K (PlaneLocalRing K 0) c * localZ ^ 4 +
      algebraMap K (PlaneLocalRing K 0) d * localZ ^ 5 ∈ filtrationIdeal0 a b c d := by
  have hC (r : K) :
      algebraMap (PlanePolynomial K) (PlaneLocalRing K 0) (MvPolynomial.C r) =
        algebraMap K (PlaneLocalRing K 0) r := by
    rw [MvPolynomial.C_eq_algebraMap]
    exact IsScalarTower.algebraMap_apply K (PlanePolynomial K) (PlaneLocalRing K 0) r
  have h := Ideal.subset_span (s := {
    algebraMap (PlanePolynomial K) (PlaneLocalRing K 0) (firstRelation a b),
    algebraMap (PlanePolynomial K) (PlaneLocalRing K 0) (secondRelation c d),
    algebraMap (PlanePolynomial K) (PlaneLocalRing K 0) thirdRelation})
    (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  simpa [filtrationIdeal0, localModelIdeal, secondRelation, localY, localZ, py, pz, hC]
    using h

theorem localZ_pow_six_mem_filtrationIdeal0 :
    localZ ^ 6 ∈ filtrationIdeal0 a b c d := by
  have h := Ideal.subset_span (s := {
    algebraMap (PlanePolynomial K) (PlaneLocalRing K 0) (firstRelation a b),
    algebraMap (PlanePolynomial K) (PlaneLocalRing K 0) (secondRelation c d),
    algebraMap (PlanePolynomial K) (PlaneLocalRing K 0) thirdRelation})
    (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  simpa [filtrationIdeal0, localModelIdeal, thirdRelation, localZ, pz] using h

theorem maximal_mul_mem_of_localY_localZ
    (I : Ideal (PlaneLocalRing K 0)) (x r : PlaneLocalRing K 0)
    (hy : localY * x ∈ I) (hz : localZ * x ∈ I)
    (hr : r ∈ IsLocalRing.maximalIdeal (PlaneLocalRing K 0)) : r * x ∈ I := by
  rw [maximalIdeal_eq_span_localY_localZ (K := K)] at hr
  obtain ⟨s, t, hst⟩ := Ideal.mem_span_pair.mp hr
  have hs : s * (localY * x) ∈ I := I.mul_mem_left s hy
  have ht : t * (localZ * x) ∈ I := I.mul_mem_left t hz
  rw [← hst]
  convert I.add_mem hs ht using 1 <;> ring

set_option maxHeartbeats 2000000 in
theorem filtrationIdeal0_covBy_filtrationIdeal1 :
    filtrationIdeal0 a b c d ⋖ filtrationIdeal1 a b c d := by
  apply covBy_span_singleton_sup (PlaneLocalRing K 0) (filtrationIdeal0 a b c d)
    (localZ ^ 5) (localZ_pow_five_not_mem_filtrationIdeal0 a b c d)
  intro r hr
  apply maximal_mul_mem_of_localY_localZ (K := K) (filtrationIdeal0 a b c d)
    (localZ ^ 5) r
  · have hrel : localY * localZ ^ 2 + algebraMap K (PlaneLocalRing K 0) c * localZ ^ 4 +
        algebraMap K (PlaneLocalRing K 0) d * localZ ^ 5 ∈ filtrationIdeal0 a b c d :=
      local_secondRelation_mem_filtrationIdeal0 a b c d
    have hz6 : localZ ^ 6 ∈ filtrationIdeal0 a b c d :=
      localZ_pow_six_mem_filtrationIdeal0 a b c d
    have hz7 : localZ ^ 7 ∈ filtrationIdeal0 a b c d := by
      have hraw := (filtrationIdeal0 a b c d).mul_mem_left localZ hz6
      convert hraw using 1 <;> ring
    have hz8 : localZ ^ 8 ∈ filtrationIdeal0 a b c d := by
      have hraw := (filtrationIdeal0 a b c d).mul_mem_left localZ hz7
      convert hraw using 1 <;> ring
    have hmul : localZ ^ 3 *
        (localY * localZ ^ 2 + algebraMap K (PlaneLocalRing K 0) c * localZ ^ 4 +
          algebraMap K (PlaneLocalRing K 0) d * localZ ^ 5) ∈ filtrationIdeal0 a b c d :=
      (filtrationIdeal0 a b c d).mul_mem_left (localZ ^ 3) hrel
    have hc7 := (filtrationIdeal0 a b c d).mul_mem_left
      (algebraMap K (PlaneLocalRing K 0) c) hz7
    have hd8 := (filtrationIdeal0 a b c d).mul_mem_left
      (algebraMap K (PlaneLocalRing K 0) d) hz8
    have hsub := (filtrationIdeal0 a b c d).sub_mem
      ((filtrationIdeal0 a b c d).sub_mem hmul hc7) hd8
    convert hsub using 1 <;> ring
  · have hz6 := localZ_pow_six_mem_filtrationIdeal0 a b c d
    convert hz6 using 1 <;> ring
  · exact hr

theorem filtrationIdeal1_covBy_filtrationIdeal2 :
    filtrationIdeal1 a b c d ⋖ filtrationIdeal2 a b c d := by
  apply covBy_span_singleton_sup (PlaneLocalRing K 0) (filtrationIdeal1 a b c d)
    (localZ ^ 4) (localZ_pow_four_not_mem_filtrationIdeal1 a b c d)
  intro r hr
  apply maximal_mul_mem_of_localY_localZ (K := K) (filtrationIdeal1 a b c d)
    (localZ ^ 4) r
  · have hrel := local_secondRelation_mem_filtrationIdeal0 a b c d
    have hrel1 : _ ∈ filtrationIdeal1 a b c d :=
      (show filtrationIdeal0 a b c d ≤ filtrationIdeal1 a b c d from le_sup_right) hrel
    have hz6 : localZ ^ 6 ∈ filtrationIdeal1 a b c d :=
      (show filtrationIdeal0 a b c d ≤ filtrationIdeal1 a b c d from le_sup_right)
        (localZ_pow_six_mem_filtrationIdeal0 a b c d)
    have hz7 : localZ ^ 7 ∈ filtrationIdeal1 a b c d := by
      have hraw := (filtrationIdeal1 a b c d).mul_mem_left localZ hz6
      convert hraw using 1 <;> ring
    have hmul := (filtrationIdeal1 a b c d).mul_mem_left (localZ ^ 2) hrel1
    have hc6 := (filtrationIdeal1 a b c d).mul_mem_left
      (algebraMap K (PlaneLocalRing K 0) c) hz6
    have hd7 := (filtrationIdeal1 a b c d).mul_mem_left
      (algebraMap K (PlaneLocalRing K 0) d) hz7
    have hsub := (filtrationIdeal1 a b c d).sub_mem
      ((filtrationIdeal1 a b c d).sub_mem hmul hc6) hd7
    convert hsub using 1 <;> ring
  · have h : localZ ^ 5 ∈ filtrationIdeal1 a b c d :=
      Ideal.mem_sup_left (Ideal.mem_span_singleton_self (localZ ^ 5))
    convert h using 1 <;> ring
  · exact hr

theorem filtrationIdeal2_covBy_filtrationIdeal3 :
    filtrationIdeal2 a b c d ⋖ filtrationIdeal3 a b c d := by
  apply covBy_span_singleton_sup (PlaneLocalRing K 0) (filtrationIdeal2 a b c d)
    (localZ ^ 3) (localZ_pow_three_not_mem_filtrationIdeal2 a b c d)
  intro r hr
  apply maximal_mul_mem_of_localY_localZ (K := K) (filtrationIdeal2 a b c d)
    (localZ ^ 3) r
  · have hrel2 : localY * localZ ^ 2 + algebraMap K (PlaneLocalRing K 0) c * localZ ^ 4 +
        algebraMap K (PlaneLocalRing K 0) d * localZ ^ 5 ∈ filtrationIdeal2 a b c d :=
      (show filtrationIdeal1 a b c d ≤ filtrationIdeal2 a b c d from le_sup_right)
        ((show filtrationIdeal0 a b c d ≤ filtrationIdeal1 a b c d from le_sup_right)
          (local_secondRelation_mem_filtrationIdeal0 a b c d))
    have hz5 : localZ ^ 5 ∈ filtrationIdeal2 a b c d :=
      (show filtrationIdeal1 a b c d ≤ filtrationIdeal2 a b c d from le_sup_right)
        (Ideal.mem_sup_left (Ideal.mem_span_singleton_self (localZ ^ 5)))
    have hz6 : localZ ^ 6 ∈ filtrationIdeal2 a b c d :=
      (show filtrationIdeal1 a b c d ≤ filtrationIdeal2 a b c d from le_sup_right)
        ((show filtrationIdeal0 a b c d ≤ filtrationIdeal1 a b c d from le_sup_right)
          (localZ_pow_six_mem_filtrationIdeal0 a b c d))
    have hmul := (filtrationIdeal2 a b c d).mul_mem_left localZ hrel2
    have hc5 := (filtrationIdeal2 a b c d).mul_mem_left
      (algebraMap K (PlaneLocalRing K 0) c) hz5
    have hd6 := (filtrationIdeal2 a b c d).mul_mem_left
      (algebraMap K (PlaneLocalRing K 0) d) hz6
    have hsub := (filtrationIdeal2 a b c d).sub_mem
      ((filtrationIdeal2 a b c d).sub_mem hmul hc5) hd6
    convert hsub using 1 <;> ring
  · have h : localZ ^ 4 ∈ filtrationIdeal2 a b c d :=
      Ideal.mem_sup_left (Ideal.mem_span_singleton_self (localZ ^ 4))
    convert h using 1 <;> ring
  · exact hr

theorem filtrationIdeal3_covBy_filtrationIdeal4 :
    filtrationIdeal3 a b c d ⋖ filtrationIdeal4 a b c d := by
  apply covBy_span_singleton_sup (PlaneLocalRing K 0) (filtrationIdeal3 a b c d)
    (localZ ^ 2) (localZ_pow_two_not_mem_filtrationIdeal3 a b c d)
  intro r hr
  apply maximal_mul_mem_of_localY_localZ (K := K) (filtrationIdeal3 a b c d)
    (localZ ^ 2) r
  · have hrel3 : localY * localZ ^ 2 + algebraMap K (PlaneLocalRing K 0) c * localZ ^ 4 +
        algebraMap K (PlaneLocalRing K 0) d * localZ ^ 5 ∈ filtrationIdeal3 a b c d :=
      (show filtrationIdeal2 a b c d ≤ filtrationIdeal3 a b c d from le_sup_right)
        ((show filtrationIdeal1 a b c d ≤ filtrationIdeal2 a b c d from le_sup_right)
          ((show filtrationIdeal0 a b c d ≤ filtrationIdeal1 a b c d from le_sup_right)
            (local_secondRelation_mem_filtrationIdeal0 a b c d)))
    have hz4 : localZ ^ 4 ∈ filtrationIdeal3 a b c d :=
      (show filtrationIdeal2 a b c d ≤ filtrationIdeal3 a b c d from le_sup_right)
        (Ideal.mem_sup_left (Ideal.mem_span_singleton_self (localZ ^ 4)))
    have hz5 : localZ ^ 5 ∈ filtrationIdeal3 a b c d :=
      (show filtrationIdeal2 a b c d ≤ filtrationIdeal3 a b c d from le_sup_right)
        ((show filtrationIdeal1 a b c d ≤ filtrationIdeal2 a b c d from le_sup_right)
          (Ideal.mem_sup_left (Ideal.mem_span_singleton_self (localZ ^ 5))))
    have hc4 := (filtrationIdeal3 a b c d).mul_mem_left
      (algebraMap K (PlaneLocalRing K 0) c) hz4
    have hd5 := (filtrationIdeal3 a b c d).mul_mem_left
      (algebraMap K (PlaneLocalRing K 0) d) hz5
    have hsub := (filtrationIdeal3 a b c d).sub_mem
      ((filtrationIdeal3 a b c d).sub_mem hrel3 hc4) hd5
    convert hsub using 1 <;> ring
  · have h : localZ ^ 3 ∈ filtrationIdeal3 a b c d :=
      Ideal.mem_sup_left (Ideal.mem_span_singleton_self (localZ ^ 3))
    convert h using 1 <;> ring
  · exact hr

theorem filtrationIdeal4_covBy_filtrationIdeal5 :
    filtrationIdeal4 a b c d ⋖ filtrationIdeal5 a b c d := by
  apply covBy_span_singleton_sup (PlaneLocalRing K 0) (filtrationIdeal4 a b c d)
    (localY * localZ) (localY_mul_localZ_not_mem_filtrationIdeal4 a b c d)
  intro r hr
  apply maximal_mul_mem_of_localY_localZ (K := K) (filtrationIdeal4 a b c d)
    (localY * localZ) r
  · have h04 : filtrationIdeal0 a b c d ≤ filtrationIdeal4 a b c d :=
      le_trans (filtrationIdeal0_le_filtrationIdeal1 a b c d)
        (le_trans (filtrationIdeal1_le_filtrationIdeal2 a b c d)
          (le_trans (filtrationIdeal2_le_filtrationIdeal3 a b c d)
            (filtrationIdeal3_le_filtrationIdeal4 a b c d)))
    have h14 : filtrationIdeal1 a b c d ≤ filtrationIdeal4 a b c d :=
      le_trans (filtrationIdeal1_le_filtrationIdeal2 a b c d)
        (le_trans (filtrationIdeal2_le_filtrationIdeal3 a b c d)
          (filtrationIdeal3_le_filtrationIdeal4 a b c d))
    have hrel := h04 (local_firstRelation_mem_filtrationIdeal0 a b c d)
    have hz5 : localZ ^ 5 ∈ filtrationIdeal4 a b c d :=
      h14 (Ideal.mem_sup_left (Ideal.mem_span_singleton_self (localZ ^ 5)))
    have hz6 : localZ ^ 6 ∈ filtrationIdeal4 a b c d :=
      h04 (localZ_pow_six_mem_filtrationIdeal0 a b c d)
    have hmul := (filtrationIdeal4 a b c d).mul_mem_left localZ hrel
    have ha5 := (filtrationIdeal4 a b c d).mul_mem_left
      (algebraMap K (PlaneLocalRing K 0) a) hz5
    have hb6 := (filtrationIdeal4 a b c d).mul_mem_left
      (algebraMap K (PlaneLocalRing K 0) b) hz6
    have hsub := (filtrationIdeal4 a b c d).sub_mem
      ((filtrationIdeal4 a b c d).sub_mem hmul ha5) hb6
    convert hsub using 1 <;> ring
  · have h04 : filtrationIdeal0 a b c d ≤ filtrationIdeal4 a b c d :=
      le_trans (filtrationIdeal0_le_filtrationIdeal1 a b c d)
        (le_trans (filtrationIdeal1_le_filtrationIdeal2 a b c d)
          (le_trans (filtrationIdeal2_le_filtrationIdeal3 a b c d)
            (filtrationIdeal3_le_filtrationIdeal4 a b c d)))
    have h14 : filtrationIdeal1 a b c d ≤ filtrationIdeal4 a b c d :=
      le_trans (filtrationIdeal1_le_filtrationIdeal2 a b c d)
        (le_trans (filtrationIdeal2_le_filtrationIdeal3 a b c d)
          (filtrationIdeal3_le_filtrationIdeal4 a b c d))
    have h24 : filtrationIdeal2 a b c d ≤ filtrationIdeal4 a b c d :=
      le_trans (filtrationIdeal2_le_filtrationIdeal3 a b c d)
        (filtrationIdeal3_le_filtrationIdeal4 a b c d)
    have hrel := h04 (local_secondRelation_mem_filtrationIdeal0 a b c d)
    have hz4 : localZ ^ 4 ∈ filtrationIdeal4 a b c d :=
      h24 (Ideal.mem_sup_left (Ideal.mem_span_singleton_self (localZ ^ 4)))
    have hz5 : localZ ^ 5 ∈ filtrationIdeal4 a b c d :=
      h14 (Ideal.mem_sup_left (Ideal.mem_span_singleton_self (localZ ^ 5)))
    have hc4 := (filtrationIdeal4 a b c d).mul_mem_left
      (algebraMap K (PlaneLocalRing K 0) c) hz4
    have hd5 := (filtrationIdeal4 a b c d).mul_mem_left
      (algebraMap K (PlaneLocalRing K 0) d) hz5
    have hsub := (filtrationIdeal4 a b c d).sub_mem
      ((filtrationIdeal4 a b c d).sub_mem hrel hc4) hd5
    convert hsub using 1 <;> ring
  · exact hr

theorem filtrationIdeal5_covBy_filtrationIdeal6 :
    filtrationIdeal5 a b c d ⋖ filtrationIdeal6 a b c d := by
  apply covBy_span_singleton_sup (PlaneLocalRing K 0) (filtrationIdeal5 a b c d)
    localZ (localZ_not_mem_filtrationIdeal5 a b c d)
  intro r hr
  apply maximal_mul_mem_of_localY_localZ (K := K) (filtrationIdeal5 a b c d) localZ r
  · exact Ideal.mem_sup_left (Ideal.mem_span_singleton_self (localY * localZ))
  · have hz2 : localZ ^ 2 ∈ filtrationIdeal5 a b c d :=
      (filtrationIdeal4_le_filtrationIdeal5 a b c d)
        (Ideal.mem_sup_left (Ideal.mem_span_singleton_self (localZ ^ 2)))
    convert hz2 using 1 <;> ring
  · exact hr

theorem filtrationIdeal6_covBy_filtrationIdeal7 :
    filtrationIdeal6 a b c d ⋖ filtrationIdeal7 a b c d := by
  apply covBy_span_singleton_sup (PlaneLocalRing K 0) (filtrationIdeal6 a b c d)
    localY (localY_not_mem_filtrationIdeal6 a b c d)
  intro r hr
  apply maximal_mul_mem_of_localY_localZ (K := K) (filtrationIdeal6 a b c d) localY r
  · have h04 : filtrationIdeal0 a b c d ≤ filtrationIdeal4 a b c d :=
      le_trans (filtrationIdeal0_le_filtrationIdeal1 a b c d)
        (le_trans (filtrationIdeal1_le_filtrationIdeal2 a b c d)
          (le_trans (filtrationIdeal2_le_filtrationIdeal3 a b c d)
            (filtrationIdeal3_le_filtrationIdeal4 a b c d)))
    have h46 : filtrationIdeal4 a b c d ≤ filtrationIdeal6 a b c d :=
      le_trans (filtrationIdeal4_le_filtrationIdeal5 a b c d)
        (filtrationIdeal5_le_filtrationIdeal6 a b c d)
    have h24 : filtrationIdeal2 a b c d ≤ filtrationIdeal4 a b c d :=
      le_trans (filtrationIdeal2_le_filtrationIdeal3 a b c d)
        (filtrationIdeal3_le_filtrationIdeal4 a b c d)
    have h14 : filtrationIdeal1 a b c d ≤ filtrationIdeal4 a b c d :=
      le_trans (filtrationIdeal1_le_filtrationIdeal2 a b c d) h24
    have hrel := h46 (h04 (local_firstRelation_mem_filtrationIdeal0 a b c d))
    have hz4 : localZ ^ 4 ∈ filtrationIdeal6 a b c d :=
      h46 (h24 (Ideal.mem_sup_left (Ideal.mem_span_singleton_self (localZ ^ 4))))
    have hz5 : localZ ^ 5 ∈ filtrationIdeal6 a b c d :=
      h46 (h14 (Ideal.mem_sup_left (Ideal.mem_span_singleton_self (localZ ^ 5))))
    have ha4 := (filtrationIdeal6 a b c d).mul_mem_left
      (algebraMap K (PlaneLocalRing K 0) a) hz4
    have hb5 := (filtrationIdeal6 a b c d).mul_mem_left
      (algebraMap K (PlaneLocalRing K 0) b) hz5
    have hsub := (filtrationIdeal6 a b c d).sub_mem
      ((filtrationIdeal6 a b c d).sub_mem hrel ha4) hb5
    convert hsub using 1 <;> ring
  · have hyz : localY * localZ ∈ filtrationIdeal6 a b c d :=
      (filtrationIdeal5_le_filtrationIdeal6 a b c d)
        (Ideal.mem_sup_left (Ideal.mem_span_singleton_self (localY * localZ)))
    convert hyz using 1 <;> ring
  · exact hr

theorem localModelIdeal_le_maximalIdeal :
    localModelIdeal a b c d ≤ IsLocalRing.maximalIdeal (PlaneLocalRing K 0) := by
  let m := IsLocalRing.maximalIdeal (PlaneLocalRing K 0)
  change localModelIdeal a b c d ≤ m
  have hm : m = Ideal.span {localY, localZ} := maximalIdeal_eq_span_localY_localZ (K := K)
  have hy : localY ∈ m := by
    rw [hm]
    exact Ideal.subset_span (Set.mem_insert _ _)
  have hz : localZ ∈ m := by
    rw [hm]
    exact Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hC (r : K) :
      algebraMap (PlanePolynomial K) (PlaneLocalRing K 0) (MvPolynomial.C r) =
        algebraMap K (PlaneLocalRing K 0) r := by
    rw [MvPolynomial.C_eq_algebraMap]
    exact IsScalarTower.algebraMap_apply K (PlanePolynomial K) (PlaneLocalRing K 0) r
  refine Ideal.span_le.2 ?_
  intro f hf
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hf
  rcases hf with rfl | rfl | rfl
  · have h : localY ^ 2 + algebraMap K (PlaneLocalRing K 0) a * localZ ^ 4 +
        algebraMap K (PlaneLocalRing K 0) b * localZ ^ 5 ∈ m :=
      m.add_mem (m.add_mem (m.pow_mem_of_mem hy 2 (by norm_num))
        (m.mul_mem_left _ (m.pow_mem_of_mem hz 4 (by norm_num))))
        (m.mul_mem_left _ (m.pow_mem_of_mem hz 5 (by norm_num)))
    simpa [firstRelation, localY, localZ, py, pz, hC] using h
  · have h : localY * localZ ^ 2 + algebraMap K (PlaneLocalRing K 0) c * localZ ^ 4 +
        algebraMap K (PlaneLocalRing K 0) d * localZ ^ 5 ∈ m :=
      m.add_mem (m.add_mem (m.mul_mem_left localY (m.pow_mem_of_mem hz 2 (by norm_num)))
        (m.mul_mem_left _ (m.pow_mem_of_mem hz 4 (by norm_num))))
        (m.mul_mem_left _ (m.pow_mem_of_mem hz 5 (by norm_num)))
    simpa [secondRelation, localY, localZ, py, pz, hC] using h
  · have h : localZ ^ 6 ∈ m := m.pow_mem_of_mem hz 6 (by norm_num)
    simpa [thirdRelation, localZ, pz] using h

theorem filtrationIdeal7_eq_maximalIdeal :
    filtrationIdeal7 a b c d = IsLocalRing.maximalIdeal (PlaneLocalRing K 0) := by
  let m := IsLocalRing.maximalIdeal (PlaneLocalRing K 0)
  have hm : m = Ideal.span {localY, localZ} := maximalIdeal_eq_span_localY_localZ (K := K)
  have hy : localY ∈ m := by
    rw [hm]
    exact Ideal.subset_span (Set.mem_insert _ _)
  have hz : localZ ∈ m := by
    rw [hm]
    exact Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hspan (x : PlaneLocalRing K 0) (hx : x ∈ m) : Ideal.span {x} ≤ m :=
    Ideal.span_le.2 (by simpa using hx)
  apply le_antisymm
  · simp only [filtrationIdeal7, filtrationIdeal6, filtrationIdeal5, filtrationIdeal4,
      filtrationIdeal3, filtrationIdeal2, filtrationIdeal1, filtrationIdeal0]
    exact sup_le (hspan localY hy)
      (sup_le (hspan localZ hz)
          (sup_le (hspan (localY * localZ) (m.mul_mem_left localY hz))
          (sup_le (hspan (localZ ^ 2) (m.pow_mem_of_mem hz 2 (by norm_num)))
            (sup_le (hspan (localZ ^ 3) (m.pow_mem_of_mem hz 3 (by norm_num)))
              (sup_le (hspan (localZ ^ 4) (m.pow_mem_of_mem hz 4 (by norm_num)))
                (sup_le (hspan (localZ ^ 5) (m.pow_mem_of_mem hz 5 (by norm_num)))
                  (localModelIdeal_le_maximalIdeal a b c d)))))))
  · change m ≤ filtrationIdeal7 a b c d
    rw [hm]
    refine Ideal.span_le.2 ?_
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact Ideal.mem_sup_left (Ideal.mem_span_singleton_self localY)
    · exact filtrationIdeal6_le_filtrationIdeal7 a b c d
        (Ideal.mem_sup_left (Ideal.mem_span_singleton_self localZ))

theorem filtrationIdeal7_covBy_top :
    filtrationIdeal7 a b c d ⋖ (⊤ : Ideal (PlaneLocalRing K 0)) := by
  rw [filtrationIdeal7_eq_maximalIdeal a b c d]
  exact (Ideal.isMaximal_def.mp
    (inferInstance : (IsLocalRing.maximalIdeal (PlaneLocalRing K 0)).IsMaximal)).covBy_top

private theorem orderIso_map_covBy_eight {α β : Type*} [PartialOrder α] [PartialOrder β]
    (e : α ≃o β) {x y : α} (h : x ⋖ y) : e x ⋖ e y := by
  rw [covBy_iff_lt_and_eq_or_eq] at h ⊢
  refine ⟨e.lt_iff_lt.mpr h.1, ?_⟩
  intro z hxz hzy
  have hxz' : x ≤ e.symm z := by simpa using e.symm.monotone hxz
  have hzy' : e.symm z ≤ y := by simpa using e.symm.monotone hzy
  rcases h.2 (e.symm z) hxz' hzy' with hz | hz
  · left
    simpa using congrArg e hz
  · right
    simpa using congrArg e hz

/-- Eight covering relations from an ideal to the top give its quotient a composition series
of length eight. -/
theorem length_quotient_eq_eight_of_covBy
    (A : Type*) [CommRing A] (J0 J1 J2 J3 J4 J5 J6 J7 : Ideal A)
    (h01 : J0 ⋖ J1) (h12 : J1 ⋖ J2) (h23 : J2 ⋖ J3) (h34 : J3 ⋖ J4)
    (h45 : J4 ⋖ J5) (h56 : J5 ⋖ J6) (h67 : J6 ⋖ J7)
    (h7T : J7 ⋖ (⊤ : Ideal A)) :
    Module.length A (A ⧸ J0) = 8 := by
  let e := Submodule.comapMkQRelIso J0
  have h02 : J0 ≤ J2 := h01.le.trans h12.le
  have h03 : J0 ≤ J3 := h02.trans h23.le
  have h04 : J0 ≤ J4 := h03.trans h34.le
  have h05 : J0 ≤ J5 := h04.trans h45.le
  have h06 : J0 ≤ J6 := h05.trans h56.le
  have h07 : J0 ≤ J7 := h06.trans h67.le
  let N0 : Submodule A (A ⧸ J0) := e.symm ⟨J0, show J0 ≤ J0 from le_rfl⟩
  let N1 : Submodule A (A ⧸ J0) := e.symm ⟨J1, h01.le⟩
  let N2 : Submodule A (A ⧸ J0) := e.symm ⟨J2, h02⟩
  let N3 : Submodule A (A ⧸ J0) := e.symm ⟨J3, h03⟩
  let N4 : Submodule A (A ⧸ J0) := e.symm ⟨J4, h04⟩
  let N5 : Submodule A (A ⧸ J0) := e.symm ⟨J5, h05⟩
  let N6 : Submodule A (A ⧸ J0) := e.symm ⟨J6, h06⟩
  let N7 : Submodule A (A ⧸ J0) := e.symm ⟨J7, h07⟩
  let N8 : Submodule A (A ⧸ J0) :=
    e.symm ⟨⊤, show J0 ≤ (⊤ : Ideal A) from le_top⟩
  have subtypeCovBy {P Q : Ideal A} (hP : J0 ≤ P) (h : P ⋖ Q) :
      (⟨P, hP⟩ : Set.Ici J0) ⋖ ⟨Q, hP.trans h.le⟩ := by
    rw [covBy_iff_lt_and_eq_or_eq] at h ⊢
    refine ⟨h.1, ?_⟩
    intro R hPR hRQ
    rcases h.2 R.1 hPR hRQ with hR | hR
    · exact Or.inl (Subtype.ext hR)
    · exact Or.inr (Subtype.ext hR)
  have hN01 : N0 ⋖ N1 := orderIso_map_covBy_eight e.symm (subtypeCovBy le_rfl h01)
  have hN12 : N1 ⋖ N2 := orderIso_map_covBy_eight e.symm (subtypeCovBy h01.le h12)
  have hN23 : N2 ⋖ N3 := orderIso_map_covBy_eight e.symm (subtypeCovBy h02 h23)
  have hN34 : N3 ⋖ N4 := orderIso_map_covBy_eight e.symm (subtypeCovBy h03 h34)
  have hN45 : N4 ⋖ N5 := orderIso_map_covBy_eight e.symm (subtypeCovBy h04 h45)
  have hN56 : N5 ⋖ N6 := orderIso_map_covBy_eight e.symm (subtypeCovBy h05 h56)
  have hN67 : N6 ⋖ N7 := orderIso_map_covBy_eight e.symm (subtypeCovBy h06 h67)
  have hN78 : N7 ⋖ N8 := orderIso_map_covBy_eight e.symm (subtypeCovBy h07 h7T)
  have hN0 : N0 = ⊥ := by
    change Submodule.map J0.mkQ J0 = ⊥
    apply le_antisymm
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := hy
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hx
    · exact bot_le
  have hN8 : N8 = ⊤ := by
    change Submodule.map J0.mkQ ⊤ = ⊤
    rw [Submodule.map_top, LinearMap.range_eq_top]
    exact Ideal.Quotient.mk_surjective
  let s : CompositionSeries (Submodule A (A ⧸ J0)) := {
    length := 8
    toFun := ![N0, N1, N2, N3, N4, N5, N6, N7, N8]
    step := by
      intro i
      fin_cases i
      · exact hN01
      · exact hN12
      · exact hN23
      · exact hN34
      · exact hN45
      · exact hN56
      · exact hN67
      · exact hN78
  }
  rw [← Module.length_compositionSeries s (by exact hN0) (by exact hN8)]
  rfl

/-- The quotient of the plane local ring by the triangular local-model ideal has intrinsic
module length eight. -/
theorem localModelIdeal_quotient_length_eq_eight :
    Module.length (PlaneLocalRing K 0)
      ((PlaneLocalRing K 0) ⧸ localModelIdeal a b c d) = 8 :=
  length_quotient_eq_eight_of_covBy (PlaneLocalRing K 0)
    (filtrationIdeal0 a b c d) (filtrationIdeal1 a b c d)
    (filtrationIdeal2 a b c d) (filtrationIdeal3 a b c d)
    (filtrationIdeal4 a b c d) (filtrationIdeal5 a b c d)
    (filtrationIdeal6 a b c d) (filtrationIdeal7 a b c d)
    (filtrationIdeal0_covBy_filtrationIdeal1 a b c d)
    (filtrationIdeal1_covBy_filtrationIdeal2 a b c d)
    (filtrationIdeal2_covBy_filtrationIdeal3 a b c d)
    (filtrationIdeal3_covBy_filtrationIdeal4 a b c d)
    (filtrationIdeal4_covBy_filtrationIdeal5 a b c d)
    (filtrationIdeal5_covBy_filtrationIdeal6 a b c d)
    (filtrationIdeal6_covBy_filtrationIdeal7 a b c d)
    (filtrationIdeal7_covBy_top a b c d)

end InfinityLocalModel

end PoincareChapterVI
