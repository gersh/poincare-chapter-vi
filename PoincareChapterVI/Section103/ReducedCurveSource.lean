/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import LeanCompCert.Verified.Decide
import Mathlib.Algebra.QuadraticAlgebra.Basic
import PoincareChapterVI.Section103.Geometry
import PoincareChapterVI.Section103.ReducedCurve

/-!
# Source normalization for Poincaré's reduced degree-seven curve

This file evaluates the reduced derivative equation from its cubic coordinate coefficients and
proves, inside Lean's kernel, that clearing denominators by `438750` gives the Gaussian-integer
table in `ReducedCurve`.  The computation uses a sparse list representation over `ℚ[i]`; its
finite coefficient cube is discharged by LeanCompCert's native-code certificate mechanism and
then bridged back to `MvPolynomial (Fin 3) ℂ` by proved interpretation lemmas.
-/

open scoped BigOperators

namespace PoincareChapterVI

namespace Section103Source

noncomputable section

abbrev QI := QuadraticAlgebra ℚ (-1) 0

instance : Fact (∀ r : ℚ, r ^ 2 ≠ (-1 : ℚ) + 0 * r) :=
  ⟨by intro r h; nlinarith [sq_nonneg r]⟩

structure Exp where
  x : ℕ
  y : ℕ
  z : ℕ
deriving DecidableEq

structure Term where
  exp : Exp
  coeff : QI
deriving DecidableEq

abbrev Sparse := List Term

def constant (q : QI) : Sparse := [⟨⟨0, 0, 0⟩, q⟩]
def x : Sparse := [⟨⟨1, 0, 0⟩, 1⟩]
def y : Sparse := [⟨⟨0, 1, 0⟩, 1⟩]
def z : Sparse := [⟨⟨0, 0, 1⟩, 1⟩]

def neg (p : Sparse) : Sparse := p.map fun t ↦ ⟨t.exp, -t.coeff⟩
def add (p q : Sparse) : Sparse := p ++ q
def sub (p q : Sparse) : Sparse := add p (neg q)

def mulExp (a b : Exp) : Exp := ⟨a.x + b.x, a.y + b.y, a.z + b.z⟩

def mul (p q : Sparse) : Sparse :=
  p.flatMap fun s ↦ q.map fun t ↦ ⟨mulExp s.exp t.exp, s.coeff * t.coeff⟩

def power (p : Sparse) : ℕ → Sparse
  | 0 => constant 1
  | n + 1 => mul (power p n) p

def cubicCoefficient : Fin 5 → Fin 3 → QI :=
  ![![⟨1 / 2, 0⟩, ⟨0, -2 / 5⟩, ⟨0, 0⟩],
    ![⟨2 / 3, 8 / 65⟩, ⟨-2 / 3, -4 / 13⟩, ⟨-1 / 3, 56 / 65⟩],
    ![⟨-217 / 195, 0⟩, ⟨20 / 39, 0⟩, ⟨10 / 39, 0⟩],
    ![⟨2 / 3, -8 / 65⟩, ⟨-2 / 3, 4 / 13⟩, ⟨-1 / 3, -56 / 65⟩],
    ![⟨1 / 2, 0⟩, ⟨0, 2 / 5⟩, ⟨0, 0⟩]]

def cubic (i : Fin 3) : Sparse :=
  add (mul (mul (constant (cubicCoefficient 0 i)) (power x 2)) y)
    (add (mul (mul (constant (cubicCoefficient 1 i)) x) (power y 2))
      (add (mul (mul (mul (constant (cubicCoefficient 2 i)) x) y) z)
        (add (mul (mul (constant (cubicCoefficient 3 i)) x) (power z 2))
          (mul (mul (constant (cubicCoefficient 4 i)) y) (power z 2)))))

def firstOutside : Sparse :=
  mul
    (mul (constant (1 + (1 / 3 : QI) ^ 2)) (sub y (mul (constant (1 / 5)) z)))
    (sub z (mul (constant (1 / 5)) y))

def secondOutside : Sparse :=
  mul
    (mul (constant (1 + (1 / 5 : QI) ^ 2)) (sub x (mul (constant (1 / 3)) z)))
    (sub z (mul (constant (1 / 3)) x))

def firstReduced (i : Fin 3) : Sparse :=
  sub (mul (constant (cubicCoefficient 0 i)) (power x 2))
    (mul (constant (cubicCoefficient 4 i)) (power z 2))

def secondReduced (i : Fin 3) : Sparse :=
  sub (mul (constant (cubicCoefficient 1 i)) (power y 2))
    (mul (constant (cubicCoefficient 3 i)) (power z 2))

def sumCoordinates (f : Fin 3 → Sparse) : Sparse := add (f 0) (add (f 1) (f 2))

def source : Sparse :=
  sub
    (mul (mul (constant 3) firstOutside)
      (sumCoordinates fun i ↦ mul (firstReduced i) (cubic i)))
    (mul (mul (constant (-2)) secondOutside)
      (sumCoordinates fun i ↦ mul (secondReduced i) (cubic i)))

def reducedCoefficient : Fin 5 → Fin 5 → QI :=
  ![![⟨0, 0⟩, ⟨90285, -99840⟩, ⟨-136890, 0⟩, ⟨-112515, 62400⟩, ⟨0, 0⟩],
    ![⟨106500, -96000⟩, ⟨-1051430, 914464⟩, ⟨1041300, -468000⟩,
      ⟨-38470, 186464⟩, ⟨88500, -60000⟩],
    ![⟨-150000, 0⟩, ⟨1388400, -112320⟩, ⟨0, 0⟩,
      ⟨-1388400, -112320⟩, ⟨150000, 0⟩],
    ![⟨-88500, -60000⟩, ⟨38470, 186464⟩, ⟨-1041300, -468000⟩,
      ⟨1051430, 914464⟩, ⟨-106500, -96000⟩],
    ![⟨0, 0⟩, ⟨112515, 62400⟩, ⟨136890, 0⟩, ⟨-90285, -99840⟩, ⟨0, 0⟩]]

def cleared : Sparse :=
  (List.ofFn fun a : Fin 5 ↦
    List.ofFn fun b : Fin 5 ↦
      ⟨⟨a.val, b.val, 7 - a.val - b.val⟩, reducedCoefficient a b⟩).flatten

def coefficient : Sparse → Exp → QI
  | [], _ => 0
  | t :: p, e => (if t.exp = e then t.coeff else 0) + coefficient p e

abbrev Index := Fin 8
abbrev Cube := Index → Index → Index → QI

def coefficientCube (p : Sparse) : Cube := fun a b c ↦ coefficient p ⟨a.val, b.val, c.val⟩

def scale (q : QI) (p : Sparse) : Sparse := mul (constant q) p

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
theorem certificate : coefficientCube (scale 438750 source) = coefficientCube cleared := by
  verified_decide

def bounded (p : Sparse) : Bool :=
  p.all fun t ↦ t.exp.x < 8 && t.exp.y < 8 && t.exp.z < 8

theorem source_bounded : bounded (scale 438750 source) = true := by verified_decide
theorem cleared_bounded : bounded cleared = true := by verified_decide

noncomputable def qiToComplex : QI →+* ℂ where
  toFun q := (q.re : ℂ) + (q.im : ℂ) * Complex.I
  map_zero' := by norm_num
  map_one' := by simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  map_add' q r := by
    simp [QuadraticAlgebra.re_add, QuadraticAlgebra.im_add]
    ring
  map_mul' q r := by
    apply Complex.ext <;>
      simp [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul,
        Complex.mul_re, Complex.mul_im] <;> ring

def expFinsupp (e : Exp) : Fin 3 →₀ ℕ :=
  Finsupp.single 0 e.x + Finsupp.single 1 e.y + Finsupp.single 2 e.z

theorem expFinsupp_injective : Function.Injective expFinsupp := by
  intro e f h
  cases e with
  | mk ex ey ez =>
    cases f with
    | mk fx fy fz =>
      simp only [expFinsupp] at h
      have hx := congrArg (fun d : Fin 3 →₀ ℕ ↦ d 0) h
      have hy := congrArg (fun d : Fin 3 →₀ ℕ ↦ d 1) h
      have hz := congrArg (fun d : Fin 3 →₀ ℕ ↦ d 2) h
      simp at hx hy hz
      subst fx
      subst fy
      subst fz
      rfl

def termToMv (t : Term) : MvPolynomial (Fin 3) ℂ :=
  MvPolynomial.monomial (expFinsupp t.exp) (qiToComplex t.coeff)

def toMv (p : Sparse) : MvPolynomial (Fin 3) ℂ :=
  (p.map termToMv).sum

private theorem expFinsupp_mulExp (e f : Exp) :
    expFinsupp (mulExp e f) = expFinsupp e + expFinsupp f := by
  ext i
  fin_cases i <;> simp [expFinsupp, mulExp]

private theorem termToMv_mul (s t : Term) :
    termToMv ⟨mulExp s.exp t.exp, s.coeff * t.coeff⟩ =
      termToMv s * termToMv t := by
  simp [termToMv, expFinsupp_mulExp, MvPolynomial.monomial_mul]

theorem toMv_add (p q : Sparse) : toMv (add p q) = toMv p + toMv q := by
  simp [toMv, add]

theorem toMv_neg (p : Sparse) : toMv (neg p) = -toMv p := by
  induction p with
  | nil => simp [toMv, neg]
  | cons t p ih =>
      change termToMv ⟨t.exp, -t.coeff⟩ + toMv (neg p) =
        -(termToMv t + toMv p)
      rw [ih]
      simp [termToMv]
      abel

theorem toMv_sub (p q : Sparse) : toMv (sub p q) = toMv p - toMv q := by
  simp [sub, toMv_add, toMv_neg, sub_eq_add_neg]

private theorem toMv_mul_single_left (s : Term) (q : Sparse) :
    toMv (q.map fun t ↦ ⟨mulExp s.exp t.exp, s.coeff * t.coeff⟩) =
      termToMv s * toMv q := by
  induction q with
  | nil => simp [toMv]
  | cons t q ih =>
      change
        termToMv ⟨mulExp s.exp t.exp, s.coeff * t.coeff⟩ +
            toMv (q.map fun u ↦
              ⟨mulExp s.exp u.exp, s.coeff * u.coeff⟩) =
          termToMv s * (termToMv t + toMv q)
      rw [ih, termToMv_mul, mul_add]

theorem toMv_mul (p q : Sparse) : toMv (mul p q) = toMv p * toMv q := by
  induction p with
  | nil => simp [toMv, mul]
  | cons s p ih =>
      have hleft : toMv (mul (s :: p) q) =
          toMv (q.map fun t ↦
            ⟨mulExp s.exp t.exp, s.coeff * t.coeff⟩) + toMv (mul p q) := by
        simp [mul, toMv]
      have hright : toMv (s :: p) = termToMv s + toMv p := rfl
      rw [hleft, hright, toMv_mul_single_left, ih, add_mul]

theorem toMv_constant (q : QI) :
    toMv (constant q) = MvPolynomial.C (qiToComplex q) := by
  simp [toMv, constant, termToMv, expFinsupp]

theorem toMv_power (p : Sparse) (n : ℕ) :
    toMv (power p n) = toMv p ^ n := by
  induction n with
  | zero => simp [power, toMv_constant]
  | succ n ih => simp [power, toMv_mul, ih, pow_succ]

theorem coeff_toMv (p : Sparse) (e : Exp) :
    MvPolynomial.coeff (expFinsupp e) (toMv p) = qiToComplex (coefficient p e) := by
  induction p with
  | nil => simp [toMv, coefficient]
  | cons t p ih =>
      by_cases h : t.exp = e
      · subst e
        have hmv : toMv (t :: p) = termToMv t + toMv p := rfl
        have hcoeff : coefficient (t :: p) t.exp =
            t.coeff + coefficient p t.exp := by simp [coefficient]
        rw [hmv, hcoeff]
        simp [termToMv, ih]
      · have h' : expFinsupp t.exp ≠ expFinsupp e :=
          fun heq ↦ h (expFinsupp_injective heq)
        have hmv : toMv (t :: p) = termToMv t + toMv p := rfl
        have hcoeff : coefficient (t :: p) e = coefficient p e := by
          simp [coefficient, h]
        rw [hmv, hcoeff]
        simp [termToMv, ih, h']

private theorem coefficient_eq_zero_of_not_bounded
    {p : Sparse} (hp : bounded p = true) (e : Exp)
    (he : ¬(e.x < 8 ∧ e.y < 8 ∧ e.z < 8)) : coefficient p e = 0 := by
  induction p with
  | nil => simp [coefficient]
  | cons t p ih =>
      have hp' :
          ((t.exp.x < 8 ∧ t.exp.y < 8) ∧ t.exp.z < 8) ∧ bounded p = true := by
        simpa [bounded] using hp
      have ht : t.exp.x < 8 ∧ t.exp.y < 8 ∧ t.exp.z < 8 := by
        exact ⟨hp'.1.1.1, hp'.1.1.2, hp'.1.2⟩
      have hne : t.exp ≠ e := by
        intro h
        subst e
        exact he ht
      simp [coefficient, hne, ih hp'.2]

private theorem coefficient_eq_of_cube_eq
    {p q : Sparse} (hcube : coefficientCube p = coefficientCube q)
    (hp : bounded p = true) (hq : bounded q = true) (e : Exp) :
    coefficient p e = coefficient q e := by
  by_cases he : e.x < 8 ∧ e.y < 8 ∧ e.z < 8
  · let a : Index := ⟨e.x, he.1⟩
    let b : Index := ⟨e.y, he.2.1⟩
    let c : Index := ⟨e.z, he.2.2⟩
    exact congrFun (congrFun (congrFun hcube a) b) c
  · rw [coefficient_eq_zero_of_not_bounded hp e he,
      coefficient_eq_zero_of_not_bounded hq e he]

private def expOfFinsupp (d : Fin 3 →₀ ℕ) : Exp := ⟨d 0, d 1, d 2⟩

private theorem expFinsupp_expOfFinsupp (d : Fin 3 →₀ ℕ) :
    expFinsupp (expOfFinsupp d) = d := by
  ext i
  fin_cases i <;> simp [expFinsupp, expOfFinsupp]

theorem toMv_eq_of_cube_eq
    {p q : Sparse} (hcube : coefficientCube p = coefficientCube q)
    (hp : bounded p = true) (hq : bounded q = true) : toMv p = toMv q := by
  apply MvPolynomial.ext
  intro d
  rw [← expFinsupp_expOfFinsupp d, coeff_toMv, coeff_toMv]
  exact congrArg qiToComplex
    (coefficient_eq_of_cube_eq hcube hp hq (expOfFinsupp d))

theorem mv_certificate : toMv (scale 438750 source) = toMv cleared :=
  toMv_eq_of_cube_eq certificate source_bounded cleared_bounded

private abbrev Trivar := MvPolynomial (Fin 3) ℂ

private def mvX : Trivar := MvPolynomial.X 0
private def mvY : Trivar := MvPolynomial.X 1
private def mvZ : Trivar := MvPolynomial.X 2

/-- The source cubic `Uᵢ` obtained from the two physical ellipses in `Geometry`. -/
def sourceCubic (coordinate : Fin 3) : Trivar :=
  MvPolynomial.C (chapterVISection103CubicCoefficient 0 coordinate) * mvX ^ 2 * mvY +
    MvPolynomial.C (chapterVISection103CubicCoefficient 1 coordinate) * mvX * mvY ^ 2 +
    MvPolynomial.C (chapterVISection103CubicCoefficient 2 coordinate) * mvX * mvY * mvZ +
    MvPolynomial.C (chapterVISection103CubicCoefficient 3 coordinate) * mvX * mvZ ^ 2 +
    MvPolynomial.C (chapterVISection103CubicCoefficient 4 coordinate) * mvY * mvZ ^ 2

private def sourceFirstOutside : Trivar :=
  MvPolynomial.C (1 + (1 / 3 : ℂ) ^ 2) *
    (mvY - MvPolynomial.C (1 / 5) * mvZ) *
    (mvZ - MvPolynomial.C (1 / 5) * mvY)

private def sourceSecondOutside : Trivar :=
  MvPolynomial.C (1 + (1 / 5 : ℂ) ^ 2) *
    (mvX - MvPolynomial.C (1 / 3) * mvZ) *
    (mvZ - MvPolynomial.C (1 / 3) * mvX)

private def sourceFirstReduced (coordinate : Fin 3) : Trivar :=
  MvPolynomial.C (chapterVISection103CubicCoefficient 0 coordinate) * mvX ^ 2 -
    MvPolynomial.C (chapterVISection103CubicCoefficient 4 coordinate) * mvZ ^ 2

private def sourceSecondReduced (coordinate : Fin 3) : Trivar :=
  MvPolynomial.C (chapterVISection103CubicCoefficient 1 coordinate) * mvY ^ 2 -
    MvPolynomial.C (chapterVISection103CubicCoefficient 3 coordinate) * mvZ ^ 2

/-- Poincaré's reduced derivative equation for `τ = 1/3`, `τ' = 1/5` and the
lattice relation `-2 n + 3 n' = 0`, written before coefficient expansion. -/
def chapterVISection103ReducedSourcePolynomial : Trivar :=
  MvPolynomial.C 3 * sourceFirstOutside *
      (∑ coordinate : Fin 3, sourceFirstReduced coordinate * sourceCubic coordinate) -
    MvPolynomial.C (-2) * sourceSecondOutside *
      (∑ coordinate : Fin 3, sourceSecondReduced coordinate * sourceCubic coordinate)

private theorem qiToComplex_cubicCoefficient (slot : Fin 5) (coordinate : Fin 3) :
    qiToComplex (cubicCoefficient slot coordinate) =
      chapterVISection103CubicCoefficient slot coordinate := by
  rw [chapterVISection103_cubicCoefficient_eq_complexTable]
  fin_cases slot <;> fin_cases coordinate <;> apply Complex.ext <;>
    norm_num [qiToComplex, cubicCoefficient,
      chapterVISection103CubicComplexCoefficient, Complex.mul_re, Complex.mul_im]

private theorem qiToComplex_rat (q : ℚ) :
    qiToComplex (q : QI) = (q : ℂ) := by
  apply Complex.ext <;> simp [qiToComplex]

private theorem qiToComplex_two : qiToComplex (2 : QI) = (2 : ℂ) := by
  norm_num [qiToComplex, QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat]

private theorem qiToComplex_three : qiToComplex (3 : QI) = (3 : ℂ) := by
  norm_num [qiToComplex, QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat]

private theorem qiToComplex_five : qiToComplex (5 : QI) = (5 : ℂ) := by
  norm_num [qiToComplex, QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat]

private theorem qiToComplex_clearing :
    qiToComplex (438750 : QI) = (438750 : ℂ) := by
  norm_num [qiToComplex, QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat]

private theorem toMv_x : toMv x = mvX := by
  simp [x, toMv, termToMv, expFinsupp, mvX, MvPolynomial.X]

private theorem toMv_y : toMv y = mvY := by
  simp [y, toMv, termToMv, expFinsupp, mvY, MvPolynomial.X]

private theorem toMv_z : toMv z = mvZ := by
  simp [z, toMv, termToMv, expFinsupp, mvZ, MvPolynomial.X]

private theorem toMv_cubic (coordinate : Fin 3) :
    toMv (cubic coordinate) = sourceCubic coordinate := by
  simp [cubic, sourceCubic, toMv_add, toMv_mul, toMv_constant, toMv_power,
    toMv_x, toMv_y, toMv_z, qiToComplex_cubicCoefficient]
  ring

private theorem toMv_source : toMv source = chapterVISection103ReducedSourcePolynomial := by
  simp [source, chapterVISection103ReducedSourcePolynomial, firstOutside, secondOutside,
    firstReduced, secondReduced, sumCoordinates, sourceFirstOutside, sourceSecondOutside,
    sourceFirstReduced, sourceSecondReduced, toMv_sub, toMv_add, toMv_mul,
    toMv_constant, toMv_power, toMv_x, toMv_y, toMv_z, toMv_cubic,
    qiToComplex_cubicCoefficient, qiToComplex_two, qiToComplex_three,
    qiToComplex_five, map_inv₀, Fin.sum_univ_succ]

private theorem qiToComplex_reducedCoefficient (a b : Fin 5) :
    qiToComplex (reducedCoefficient a b) =
      (chapterVISection103ReducedGaussianCoefficient a b : ℂ) := by
  fin_cases a <;> fin_cases b <;> apply Complex.ext <;>
    norm_num [qiToComplex, reducedCoefficient,
      chapterVISection103ReducedGaussianCoefficient, GaussianInt.toComplex_def,
      Complex.mul_re, Complex.mul_im]

private theorem reducedProjectiveMonomial_eq_expFinsupp (a b : ℕ) :
    chapterVIReducedProjectiveMonomial a b =
      expFinsupp ⟨a, b, 7 - a - b⟩ := by
  rfl

private theorem toMv_cleared :
    toMv cleared = chapterVISection103ReducedProjectivePolynomial := by
  simp [cleared, toMv, termToMv,
    chapterVISection103ReducedProjectivePolynomial,
    reducedProjectiveMonomial_eq_expFinsupp,
    qiToComplex_reducedCoefficient, Fin.sum_univ_succ]
  abel

/-- Kernel-checked source-to-table normalization.  This closes the computational gap between
Poincaré's reduced derivative formula and the exact septic used in the projective argument. -/
theorem chapterVISection103_reducedSource_eq_projectivePolynomial :
    MvPolynomial.C 438750 * chapterVISection103ReducedSourcePolynomial =
      chapterVISection103ReducedProjectivePolynomial := by
  rw [← toMv_source, ← toMv_cleared, ← mv_certificate]
  simp [scale, toMv_mul, toMv_constant, qiToComplex_clearing]

end

end Section103Source

end PoincareChapterVI
