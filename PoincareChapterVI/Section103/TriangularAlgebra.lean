/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import Mathlib

/-!
# The eight-dimensional local model at the points at infinity

The local standard bases occurring in the two infinity charts of Poincare's Section 103 have
the common triangular shape

`Y^2 + a Z^4 + b Z^5,   Y Z^2 + c Z^4 + d Z^5,   Z^6`.

This file constructs the resulting eight-dimensional algebra directly.  Its ordered basis is

`1, Z, Z^2, Z^3, Z^4, Z^5, Y, Y Z`.

Keeping this elementary finite model separate from the large chart certificates makes the local
length calculation reusable and auditable.
-/

noncomputable section

namespace PoincareChapterVI

/-- The finite algebra with relations
`Y^2 = -a Z^4 - b Z^5`, `Y Z^2 = -c Z^4 - d Z^5`, and `Z^6 = 0`.

Coordinates `0,...,7` correspond respectively to
`1, Z, Z^2, Z^3, Z^4, Z^5, Y, YZ`. -/
@[ext]
structure TriangularAlgebra (K : Type*) (a b c d : K) where
  coeff : Fin 8 -> K

namespace TriangularAlgebra

variable {K : Type*} {a b c d : K}

instance [Zero K] : Zero (TriangularAlgebra K a b c d) :=
  ⟨⟨fun _ => 0⟩⟩

instance [Add K] : Add (TriangularAlgebra K a b c d) :=
  ⟨fun x y => ⟨fun i => x.coeff i + y.coeff i⟩⟩

instance [Neg K] : Neg (TriangularAlgebra K a b c d) :=
  ⟨fun x => ⟨fun i => -x.coeff i⟩⟩

instance [Sub K] : Sub (TriangularAlgebra K a b c d) :=
  ⟨fun x y => ⟨fun i => x.coeff i - y.coeff i⟩⟩

instance {S : Type*} [SMul S K] : SMul S (TriangularAlgebra K a b c d) :=
  ⟨fun r x => ⟨fun i => r • x.coeff i⟩⟩

def one [Zero K] [One K] : TriangularAlgebra K a b c d :=
  ⟨![1, 0, 0, 0, 0, 0, 0, 0]⟩

instance [Zero K] [One K] : One (TriangularAlgebra K a b c d) := ⟨one⟩

/-- Multiplication reduced in the ordered basis
`1, Z, Z^2, Z^3, Z^4, Z^5, Y, YZ`. -/
def mul [CommRing K] (x y : TriangularAlgebra K a b c d) :
    TriangularAlgebra K a b c d :=
  ⟨![
    x.coeff 0 * y.coeff 0,
    x.coeff 0 * y.coeff 1 + x.coeff 1 * y.coeff 0,
    x.coeff 0 * y.coeff 2 + x.coeff 1 * y.coeff 1 + x.coeff 2 * y.coeff 0,
    x.coeff 0 * y.coeff 3 + x.coeff 1 * y.coeff 2 +
      x.coeff 2 * y.coeff 1 + x.coeff 3 * y.coeff 0,
    x.coeff 0 * y.coeff 4 + x.coeff 1 * y.coeff 3 +
      x.coeff 2 * y.coeff 2 + x.coeff 3 * y.coeff 1 + x.coeff 4 * y.coeff 0 -
      a * x.coeff 6 * y.coeff 6 -
      c * (x.coeff 2 * y.coeff 6 + x.coeff 1 * y.coeff 7 +
        x.coeff 6 * y.coeff 2 + x.coeff 7 * y.coeff 1),
    x.coeff 0 * y.coeff 5 + x.coeff 1 * y.coeff 4 +
      x.coeff 2 * y.coeff 3 + x.coeff 3 * y.coeff 2 +
      x.coeff 4 * y.coeff 1 + x.coeff 5 * y.coeff 0 -
      b * x.coeff 6 * y.coeff 6 -
      a * (x.coeff 6 * y.coeff 7 + x.coeff 7 * y.coeff 6) -
      d * (x.coeff 2 * y.coeff 6 + x.coeff 1 * y.coeff 7 +
        x.coeff 6 * y.coeff 2 + x.coeff 7 * y.coeff 1) -
      c * (x.coeff 3 * y.coeff 6 + x.coeff 2 * y.coeff 7 +
        x.coeff 6 * y.coeff 3 + x.coeff 7 * y.coeff 2),
    x.coeff 0 * y.coeff 6 + x.coeff 6 * y.coeff 0,
    x.coeff 0 * y.coeff 7 + x.coeff 1 * y.coeff 6 +
      x.coeff 6 * y.coeff 1 + x.coeff 7 * y.coeff 0]⟩

instance [CommRing K] : Mul (TriangularAlgebra K a b c d) := ⟨mul⟩

@[simp] theorem coeff_mul [CommRing K] (x y : TriangularAlgebra K a b c d) (i : Fin 8) :
    (x * y).coeff i = (mul x y).coeff i := rfl

@[simp] theorem coeff_zero [Zero K] (i : Fin 8) :
    (0 : TriangularAlgebra K a b c d).coeff i = 0 := rfl

@[simp] theorem coeff_add [Add K] (x y : TriangularAlgebra K a b c d) (i : Fin 8) :
    (x + y).coeff i = x.coeff i + y.coeff i := rfl

@[simp] theorem coeff_neg [Neg K] (x : TriangularAlgebra K a b c d) (i : Fin 8) :
    (-x).coeff i = -x.coeff i := rfl

@[simp] theorem coeff_sub [Sub K] (x y : TriangularAlgebra K a b c d) (i : Fin 8) :
    (x - y).coeff i = x.coeff i - y.coeff i := rfl

@[simp] theorem coeff_smul {S : Type*} [SMul S K] (r : S) (x : TriangularAlgebra K a b c d)
    (i : Fin 8) : (r • x).coeff i = r • x.coeff i := rfl

@[simp] theorem coeff_one [Zero K] [One K] (i : Fin 8) :
    (1 : TriangularAlgebra K a b c d).coeff i = if i = 0 then 1 else 0 := by
  fin_cases i <;> rfl

instance [AddCommGroup K] : AddCommGroup (TriangularAlgebra K a b c d) := by
  let f : TriangularAlgebra K a b c d -> (Fin 8 -> K) := fun x => x.coeff
  have hf : Function.Injective f := fun x y h => TriangularAlgebra.ext h
  refine Function.Injective.addCommGroup f hf rfl ?_ ?_ ?_ ?_ ?_
  all_goals intros; rfl

instance [CommRing K] : NonUnitalNonAssocRing (TriangularAlgebra K a b c d) where
  left_distrib x y z := by
    ext i
    fin_cases i <;> simp [mul] <;> ring
  right_distrib x y z := by
    ext i
    fin_cases i <;> simp [mul] <;> ring
  zero_mul x := by ext i; fin_cases i <;> simp [mul]
  mul_zero x := by ext i; fin_cases i <;> simp [mul]

instance [CommRing K] : NonAssocRing (TriangularAlgebra K a b c d) where
  one_mul x := by ext i; fin_cases i <;> simp [mul]
  mul_one x := by ext i; fin_cases i <;> simp [mul]

instance [CommRing K] : Module K (TriangularAlgebra K a b c d) where
  one_smul x := by ext i; simp
  mul_smul r s x := by ext i; exact _root_.mul_assoc r s (x.coeff i)
  smul_add r x y := by ext i; exact mul_add r (x.coeff i) (y.coeff i)
  smul_zero r := by ext i; simp
  add_smul r s x := by ext i; exact add_mul r s (x.coeff i)
  zero_smul x := by ext i; simp

theorem smul_mul [CommRing K] (r : K) (x y : TriangularAlgebra K a b c d) :
    (r • x) * y = r • (x * y) := by
  ext i
  fin_cases i <;> simp [mul, smul_eq_mul] <;> ring

theorem mul_smul [CommRing K] (r : K) (x y : TriangularAlgebra K a b c d) :
    x * (r • y) = r • (x * y) := by
  ext i
  fin_cases i <;> simp [mul, smul_eq_mul] <;> ring

def linearEquivTuple [CommRing K] :
    TriangularAlgebra K a b c d ≃ₗ[K] (Fin 8 -> K) where
  toFun x := x.coeff
  invFun f := ⟨f⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The coordinate basis `1, Z, ..., Z^5, Y, YZ`. -/
def basis [CommRing K] : Module.Basis (Fin 8) K (TriangularAlgebra K a b c d) :=
  Module.Basis.ofEquivFun linearEquivTuple

set_option maxHeartbeats 20000000 in
theorem mul_assoc [CommRing K] (x y z : TriangularAlgebra K a b c d) :
    (x * y) * z = x * (y * z) := by
  ext i
  fin_cases i <;> simp [mul] <;> ring

instance [CommRing K] : CommRing (TriangularAlgebra K a b c d) where
  mul_assoc := mul_assoc
  mul_comm x y := by
    ext i
    fin_cases i <;> simp [mul] <;> ring

def C [CommRing K] (r : K) : TriangularAlgebra K a b c d :=
  ⟨![r, 0, 0, 0, 0, 0, 0, 0]⟩

@[simp] theorem coeff_C [CommRing K] (r : K) (i : Fin 8) :
    (C (a := a) (b := b) (c := c) (d := d) r).coeff i = if i = 0 then r else 0 := by
  fin_cases i <;> rfl

def algebraMap [CommRing K] : K →+* TriangularAlgebra K a b c d where
  toFun := C
  map_one' := by ext i; fin_cases i <;> simp [C]
  map_mul' r s := by ext i; fin_cases i <;> simp [C, mul]
  map_zero' := by ext i; fin_cases i <;> simp [C]
  map_add' r s := by ext i; fin_cases i <;> simp [C]

instance [CommRing K] : Algebra K (TriangularAlgebra K a b c d) where
  algebraMap := algebraMap
  commutes' r x := by
    ext i
    fin_cases i <;> simp [algebraMap, C, mul] <;> ring
  smul_def' r x := by
    ext i
    fin_cases i <;> simp [algebraMap, C, mul, smul_eq_mul]

instance [CommRing K] : Module.Free K (TriangularAlgebra K a b c d) :=
  Module.Free.of_basis basis

instance [CommRing K] : Module.Finite K (TriangularAlgebra K a b c d) :=
  Module.Finite.of_basis basis

theorem finrank_eq_eight [Field K] :
    Module.finrank K (TriangularAlgebra K a b c d) = 8 := by
  rw [Module.finrank_eq_card_basis
    (basis (K := K) (a := a) (b := b) (c := c) (d := d))]
  rfl

/-- The images of the two local coordinates in the finite model. -/
def Z [CommRing K] : TriangularAlgebra K a b c d :=
  (basis (K := K) (a := a) (b := b) (c := c) (d := d)) 1

def Y [CommRing K] : TriangularAlgebra K a b c d :=
  (basis (K := K) (a := a) (b := b) (c := c) (d := d)) 6

theorem Z_pow_six [CommRing K] :
    (Z (K := K) (a := a) (b := b) (c := c) (d := d)) ^ 6 = 0 := by
  ext i
  fin_cases i <;> simp [Z, basis, linearEquivTuple, mul, pow_succ]

theorem Y_sq [CommRing K] :
    (Y (K := K) (a := a) (b := b) (c := c) (d := d)) ^ 2 +
      C (a := a) (b := b) (c := c) (d := d) a * Z ^ 4 +
      C (a := a) (b := b) (c := c) (d := d) b * Z ^ 5 = 0 := by
  ext i
  fin_cases i <;>
    simp [Y, Z, basis, linearEquivTuple, C, mul, pow_succ]

theorem Y_mul_Z_sq [CommRing K] :
    Y (K := K) (a := a) (b := b) (c := c) (d := d) * Z ^ 2 +
      C (a := a) (b := b) (c := c) (d := d) c * Z ^ 4 +
      C (a := a) (b := b) (c := c) (d := d) d * Z ^ 5 = 0 := by
  ext i
  fin_cases i <;>
    simp [Y, Z, basis, linearEquivTuple, C, mul, pow_succ]

end TriangularAlgebra

end PoincareChapterVI
