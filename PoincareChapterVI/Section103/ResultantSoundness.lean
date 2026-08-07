/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.Section103.IntersectionResultant
import Mathlib.LinearAlgebra.Matrix.Determinant.Bird.Correctness
import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
# Soundness of the Section 103 resultant certificates

This file closes the semantic gap between the finite coefficient calculations in
`IntersectionResultant` and Mathlib's `Polynomial.resultant`:

* a nine-coefficient jet implements exactly the coefficients of polynomial arithmetic below
  degree nine;
* an array implementation of Bird's recurrence is proved coefficientwise equal to Mathlib's
  verified `BirdDet.birdDet`;
* the concrete arrays are identified with Mathlib's Sylvester matrices; and
* the two chart resultants are proved to have trailing degree exactly eight.

The numerical leaf computations use LeanCompCert's kernel-backed `verified_decide`; the original
independently computed sparse certificates remain in `IntersectionResultant`.
-/

namespace PoincareChapterVI.Section103Resultant

open Section103Resultant

structure Jet where
  data : Array QI
deriving DecidableEq

def jetCoeff (p : Jet) (n : Nat) : QI := p.data.getD n 0

def jetZero : Jet := ⟨Array.replicate 9 0⟩
def jetOne : Jet := ⟨Array.ofFn fun n : Fin 9 ↦ if n.val = 0 then 1 else 0⟩
def jetAdd (p q : Jet) : Jet :=
  ⟨Array.ofFn fun n : Fin 9 ↦ jetCoeff p n.val + jetCoeff q n.val⟩
def jetNeg (p : Jet) : Jet :=
  ⟨Array.ofFn fun n : Fin 9 ↦ -jetCoeff p n.val⟩
def jetMul (p q : Jet) : Jet :=
  ⟨Array.ofFn fun n : Fin 9 ↦
    ∑ k ∈ Finset.range (n.val + 1), jetCoeff p k * jetCoeff q (n.val - k)⟩

def jetOfSparse (p : ZSparse) : Jet :=
  ⟨Array.ofFn fun n : Fin 9 ↦ zcoefficient p n.val⟩

def jetMatrixGet (A : Array Jet) (i j : Nat) : Jet := A.getD (8 * i + j) jetZero

def jetSumFrom (n lo : Nat) (f : Nat → Jet) : Jet :=
  if lo < n then jetAdd (f lo) (jetSumFrom n (lo + 1) f) else jetZero

def jetStepEntry (A F : Array Jet) (i j : Nat) : Jet :=
  jetAdd
    (jetNeg (jetMul (jetSumFrom 8 (i + 1) fun k ↦ jetMatrixGet F k k)
      (jetMatrixGet A i j)))
    (jetSumFrom 8 (i + 1) fun k ↦ jetMul (jetMatrixGet F i k) (jetMatrixGet A k j))

def jetStep (A F : Array Jet) : Array Jet :=
  Array.ofFn fun k : Fin 64 ↦
    jetStepEntry A F (k.val / 8) (k.val % 8)

def jetIterate (A : Array Jet) : Nat → Array Jet
  | 0 => A
  | n + 1 => jetStep A (jetIterate A n)

def jetBirdDet8 (A : Array Jet) : Jet :=
  jetNeg ((jetIterate A 7).getD 0 jetZero)

def matrixArray (M : Eight → Eight → ZSparse) : Array Jet :=
  Array.ofFn fun k : Fin 64 ↦
    jetOfSparse (M ⟨k.val / 8, by omega⟩ ⟨k.val % 8, Nat.mod_lt _ (by omega)⟩)

noncomputable def sparsePolynomial : ZSparse → Polynomial QI
  | [] => 0
  | t :: p => Polynomial.monomial t.exp t.coeff + sparsePolynomial p

def Agrees (p : Jet) (P : Polynomial QI) : Prop :=
  ∀ n, n < 9 → jetCoeff p n = P.coeff n

theorem Agrees.congr_right {p : Jet} {P Q : Polynomial QI}
    (h : Agrees p P) (e : P = Q) : Agrees p Q := e ▸ h

theorem jetCoeff_zero {n : Nat} (hn : n < 9) : jetCoeff jetZero n = 0 := by
  simp [jetCoeff, jetZero, hn]

theorem jetCoeff_one {n : Nat} (hn : n < 9) :
    jetCoeff jetOne n = (1 : Polynomial QI).coeff n := by
  simp [jetCoeff, jetOne, hn, Polynomial.coeff_one]

theorem jetCoeff_add {p q : Jet} {n : Nat} (hn : n < 9) :
    jetCoeff (jetAdd p q) n = jetCoeff p n + jetCoeff q n := by
  simp [jetCoeff, jetAdd, hn]

theorem jetCoeff_neg {p : Jet} {n : Nat} (hn : n < 9) :
    jetCoeff (jetNeg p) n = -jetCoeff p n := by
  simp [jetCoeff, jetNeg, hn]

theorem jetCoeff_mul {p q : Jet} {n : Nat} (hn : n < 9) :
    jetCoeff (jetMul p q) n =
      ∑ k ∈ Finset.range (n + 1), jetCoeff p k * jetCoeff q (n - k) := by
  simp [jetCoeff, jetMul, hn]

theorem agrees_zero : Agrees jetZero 0 := by
  intro n hn
  simp [jetCoeff_zero hn]

theorem agrees_one : Agrees jetOne 1 := by
  intro n hn
  exact jetCoeff_one hn

theorem Agrees.add {p q : Jet} {P Q : Polynomial QI}
    (hp : Agrees p P) (hq : Agrees q Q) : Agrees (jetAdd p q) (P + Q) := by
  intro n hn
  rw [jetCoeff_add hn, Polynomial.coeff_add, hp n hn, hq n hn]

theorem Agrees.neg {p : Jet} {P : Polynomial QI}
    (hp : Agrees p P) : Agrees (jetNeg p) (-P) := by
  intro n hn
  rw [jetCoeff_neg hn, Polynomial.coeff_neg, hp n hn]

theorem Agrees.mul {p q : Jet} {P Q : Polynomial QI}
    (hp : Agrees p P) (hq : Agrees q Q) : Agrees (jetMul p q) (P * Q) := by
  intro n hn
  rw [jetCoeff_mul hn, Polynomial.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j ↦ P.coeff i * Q.coeff j) n]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k < 9 := lt_of_lt_of_le (Finset.mem_range.mp hk) (by omega)
  have hnk : n - k < 9 := by omega
  rw [hp k hk', hq (n - k) hnk]

theorem agrees_sparsePolynomial (p : ZSparse) :
    Agrees (jetOfSparse p) (sparsePolynomial p) := by
  intro n hn
  simp only [jetCoeff, jetOfSparse]
  simp [Array.getD, hn]
  induction p with
  | nil => simp [zcoefficient, sparsePolynomial]
  | cons t p ih =>
      simp [zcoefficient, sparsePolynomial, Polynomial.coeff_add,
        Polynomial.coeff_monomial, ih]

def MatrixAgrees (F : Array Jet) (G : Nat → Nat → Polynomial QI) : Prop :=
  ∀ i j, i < 8 → j < 8 → Agrees (jetMatrixGet F i j) (G i j)

theorem jetSumFrom_agrees (f : Nat → Jet) (g : Nat → Polynomial QI)
    (hfg : ∀ k, k < 8 → Agrees (f k) (g k)) (lo : Nat) :
    Agrees (jetSumFrom 8 lo f) (BirdDet.sumFrom 8 lo g) := by
  induction lo using BirdDet.sumFrom_induct 8 with
  | step lo hlo ih =>
      rw [BirdDet.sumFrom_step 8 lo g hlo]
      rw [jetSumFrom]
      simp only [hlo, if_true]
      exact (hfg lo hlo).add ih
  | stop lo hlo =>
      rw [BirdDet.sumFrom_stop 8 lo g hlo]
      rw [jetSumFrom]
      simp only [hlo, if_false]
      exact agrees_zero

theorem jetStepEntry_agrees {A F : Array Jet} {PA : Array (Polynomial QI)}
    {Q : Nat → Nat → Polynomial QI}
    (hA : MatrixAgrees A (BirdDet.get 8 PA)) (hF : MatrixAgrees F Q)
    {i j : Nat} (hi : i < 8) (hj : j < 8) :
    Agrees (jetStepEntry A F i j) (BirdDet.stepEntry 8 PA Q i j) := by
  unfold jetStepEntry BirdDet.stepEntry
  have hdiag : Agrees (jetSumFrom 8 (i + 1) fun k ↦ jetMatrixGet F k k)
      (BirdDet.sumFrom 8 (i + 1) fun k ↦ Q k k) :=
    jetSumFrom_agrees _ _ (fun k hk ↦ hF k k hk hk) _
  have hrow : Agrees
      (jetSumFrom 8 (i + 1) fun k ↦ jetMul (jetMatrixGet F i k) (jetMatrixGet A k j))
      (BirdDet.sumFrom 8 (i + 1) fun k ↦ Q i k * BirdDet.get 8 PA k j) :=
    jetSumFrom_agrees _ _ (fun k hk ↦ (hF i k hi hk).mul (hA k j hk hj)) _
  convert (hdiag.mul (hA i j hi hj)).neg.add hrow using 1
  all_goals ring

theorem jetStep_agrees {A F : Array Jet} {PA : Array (Polynomial QI)}
    {Q : Nat → Nat → Polynomial QI}
    (hA : MatrixAgrees A (BirdDet.get 8 PA)) (hF : MatrixAgrees F Q) :
    MatrixAgrees (jetStep A F) (BirdDet.stepEntry 8 PA Q) := by
  intro i j hi hj
  have h := jetStepEntry_agrees hA hF hi hj
  have hidx : 8 * i + j < 64 := by omega
  have hdiv : (8 * i + j) / 8 = i := by omega
  have hmod : (8 * i + j) % 8 = j := by omega
  simpa [jetMatrixGet, jetStep, Array.getD, hidx, hdiv, hmod] using h

noncomputable def polynomialMatrix (M : Eight → Eight → ZSparse) :
    Matrix Eight Eight (Polynomial QI) :=
  fun i j ↦ sparsePolynomial (M i j)

noncomputable def polynomialMatrixArray (M : Eight → Eight → ZSparse) :
    Array (Polynomial QI) :=
  Array.ofFn fun k : Fin 64 ↦
    sparsePolynomial (M ⟨k.val / 8, by omega⟩
      ⟨k.val % 8, Nat.mod_lt _ (by omega)⟩)

theorem matrixArray_agrees (M : Eight → Eight → ZSparse) :
    MatrixAgrees (matrixArray M) (BirdDet.get 8 (polynomialMatrixArray M)) := by
  intro i j hi hj
  have hidx : 8 * i + j < 64 := by omega
  have hdiv : (8 * i + j) / 8 = i := by omega
  have hmod : (8 * i + j) % 8 = j := by omega
  have hget : BirdDet.get 8 (polynomialMatrixArray M) i j =
      sparsePolynomial (M ⟨i, hi⟩ ⟨j, hj⟩) := by
    simp [BirdDet.get, polynomialMatrixArray, Array.getD, hidx, hdiv, hmod]
  rw [hget]
  simpa [matrixArray, jetMatrixGet, Array.getD, hidx, hdiv, hmod] using
    agrees_sparsePolynomial (M ⟨i, hi⟩ ⟨j, hj⟩)

theorem jetIterate_agrees {A : Array Jet} {PA : Array (Polynomial QI)}
    (hA : MatrixAgrees A (BirdDet.get 8 PA)) : ∀ t,
    MatrixAgrees (jetIterate A t)
      ((BirdDet.stepEntry 8 PA)^[t] (BirdDet.get 8 PA)) := by
  intro t
  induction t with
  | zero => simpa [jetIterate]
  | succ t ih =>
      simpa [jetIterate, Function.iterate_succ_apply'] using jetStep_agrees hA ih

theorem jetBirdDet8_agrees {A : Array Jet} {PA : Array (Polynomial QI)}
    (hA : MatrixAgrees A (BirdDet.get 8 PA)) :
    Agrees (jetBirdDet8 A) (BirdDet.birdDet 8 PA) := by
  have h := jetIterate_agrees hA 7 0 0 (by omega) (by omega)
  have hn := h.neg
  rw [BirdDet.birdDet_succ]
  simpa only [jetBirdDet8, jetMatrixGet] using hn
    |>.congr_right (by ring)

theorem ofArray_polynomialMatrixArray (M : Eight → Eight → ZSparse)
    (hsize : (polynomialMatrixArray M).size = 8 * 8) :
    Matrix.ofArray (polynomialMatrixArray M) hsize = polynomialMatrix M := by
  rw [Matrix.ofArray_eq_of_getD]
  apply Matrix.ext
  intro i j
  have hidx : 8 * i.val + j.val < 64 := by omega
  have hdiv : (8 * i.val + j.val) / 8 = i.val := by omega
  simp [polynomialMatrixArray, polynomialMatrix, Matrix.of_apply,
    Array.getD, hidx, hdiv, Nat.mod_eq_of_lt j.isLt]

theorem jetDeterminant_agrees (M : Eight → Eight → ZSparse) :
    Agrees (jetBirdDet8 (matrixArray M)) (polynomialMatrix M).det := by
  have hsize : (polynomialMatrixArray M).size = 8 * 8 := by
    rw [polynomialMatrixArray, Array.size_ofFn]
  have hbird : Agrees (jetBirdDet8 (matrixArray M))
      (BirdDet.birdDet 8 (polynomialMatrixArray M)) :=
    jetBirdDet8_agrees (matrixArray_agrees M)
  have hdet : (polynomialMatrix M).det =
      BirdDet.birdDet 8 (polynomialMatrixArray M) := by
    calc
      _ = (Matrix.ofArray (polynomialMatrixArray M) hsize).det := by
        rw [ofArray_polynomialMatrixArray M hsize]
      _ = _ := BirdDet.det_eq_birdDet _ hsize
  exact hbird.congr_right hdet.symm

noncomputable def assembledPolynomial (p : Fin 5 → ZSparse) :
    Polynomial (Polynomial QI) :=
  ∑ k, Polynomial.monomial k.val (sparsePolynomial (p k))

theorem assembledPolynomial_coeff (p : Fin 5 → ZSparse) (n : Nat) :
    (assembledPolynomial p).coeff n = sparsePolynomial (coeffAt p n) := by
  by_cases hn : n < 5
  · have heq (k : Fin 5) : (k.val = n) ↔ k = ⟨n, hn⟩ := by
      simp [Fin.ext_iff]
    simp [assembledPolynomial, coeffAt, hn, Polynomial.coeff_monomial, heq]
  · have hn' (k : Fin 5) : k.val ≠ n := by omega
    simp [assembledPolynomial, coeffAt, hn, Polynomial.coeff_monomial, hn',
      sparsePolynomial]

theorem polynomialMatrix_sylvester (p q : Fin 5 → ZSparse) :
    polynomialMatrix (sylvester p q) =
      Polynomial.sylvester (assembledPolynomial p) (assembledPolynomial q) 4 4 := by
  apply Matrix.ext
  intro i col
  refine @Fin.addCases 4 4 (fun col ↦
    polynomialMatrix (sylvester p q) i col =
      Polynomial.sylvester (assembledPolynomial p) (assembledPolynomial q) 4 4 i col)
    ?_ ?_ col
  · intro j4
    rw [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_left]
    fin_cases i <;> fin_cases j4 <;>
      simp [polynomialMatrix, sylvester,
        assembledPolynomial_coeff, coeffAt, sparsePolynomial]
  · intro j4
    rw [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_right]
    fin_cases i <;> fin_cases j4 <;>
      simp [polynomialMatrix, sylvester,
        assembledPolynomial_coeff, coeffAt, sparsePolynomial]

theorem jetResultant_agrees (p q : Fin 5 → ZSparse) :
    Agrees (jetBirdDet8 (matrixArray (sylvester p q)))
      ((assembledPolynomial p).resultant (assembledPolynomial q) 4 4) := by
  have h := jetDeterminant_agrees (sylvester p q)
  apply h.congr_right
  rw [polynomialMatrix_sylvester]
  rfl

noncomputable def xChartResultant : Polynomial QI :=
  (assembledPolynomial xSexticCoefficient).resultant
    (assembledPolynomial xReducedCoefficient) 4 4

noncomputable def yChartResultant : Polynomial QI :=
  (assembledPolynomial ySexticCoefficient).resultant
    (assembledPolynomial yReducedCoefficient) 4 4

def xJet : Jet := jetBirdDet8
  (matrixArray (sylvester xSexticCoefficient xReducedCoefficient))

def yJet : Jet := jetBirdDet8
  (matrixArray (sylvester ySexticCoefficient yReducedCoefficient))

theorem xJet_agrees_resultant : Agrees xJet xChartResultant := by
  simpa [xJet, xChartResultant] using
    jetResultant_agrees xSexticCoefficient xReducedCoefficient

theorem yJet_agrees_resultant : Agrees yJet yChartResultant := by
  simpa [yJet, yChartResultant] using
    jetResultant_agrees ySexticCoefficient yReducedCoefficient

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
theorem xJet_certificate :
    (∀ n : Fin 8, jetCoeff xJet n.val = 0) ∧
      jetCoeff xJet 8 =
        ⟨4818158998095220357263684627656250000,
          10850659278679505837928529530000000000⟩ := by
  verified_decide

theorem xJet_below : ∀ n : Fin 8, jetCoeff xJet n.val = 0 := xJet_certificate.1

theorem xJet_eight : jetCoeff xJet 8 =
    ⟨4818158998095220357263684627656250000,
      10850659278679505837928529530000000000⟩ := xJet_certificate.2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
theorem yJet_certificate :
    (∀ n : Fin 8, jetCoeff yJet n.val = 0) ∧
      jetCoeff yJet 8 =
        ⟨-4598471310720574147795898437500000000,
          -31742888552352893718562500000000000000⟩ := by
  verified_decide

theorem yJet_below : ∀ n : Fin 8, jetCoeff yJet n.val = 0 := yJet_certificate.1

theorem yJet_eight : jetCoeff yJet 8 =
    ⟨-4598471310720574147795898437500000000,
      -31742888552352893718562500000000000000⟩ := yJet_certificate.2

theorem xChartResultant_coeff_below_eight :
    ∀ n : Fin 8, xChartResultant.coeff n.val = 0 := by
  intro n
  calc
    _ = jetCoeff xJet n.val := (xJet_agrees_resultant n.val (by omega)).symm
    _ = 0 := xJet_below n

theorem xChartResultant_coeff_eight : xChartResultant.coeff 8 =
    ⟨4818158998095220357263684627656250000,
      10850659278679505837928529530000000000⟩ := by
  calc
    _ = jetCoeff xJet 8 := (xJet_agrees_resultant 8 (by omega)).symm
    _ = _ := xJet_eight

theorem yChartResultant_coeff_below_eight :
    ∀ n : Fin 8, yChartResultant.coeff n.val = 0 := by
  intro n
  calc
    _ = jetCoeff yJet n.val := (yJet_agrees_resultant n.val (by omega)).symm
    _ = 0 := yJet_below n

theorem yChartResultant_coeff_eight : yChartResultant.coeff 8 =
    ⟨-4598471310720574147795898437500000000,
      -31742888552352893718562500000000000000⟩ := by
  calc
    _ = jetCoeff yJet 8 := (yJet_agrees_resultant 8 (by omega)).symm
    _ = _ := yJet_eight

theorem xChartResultant_natTrailingDegree : xChartResultant.natTrailingDegree = 8 := by
  have hc : xChartResultant.coeff 8 ≠ 0 := by
    rw [xChartResultant_coeff_eight]
    decide
  apply Nat.le_antisymm (Polynomial.natTrailingDegree_le_of_ne_zero hc)
  apply Polynomial.le_natTrailingDegree
  · intro hp
    apply hc
    simp [hp]
  · intro n hn
    exact xChartResultant_coeff_below_eight ⟨n, hn⟩

theorem yChartResultant_natTrailingDegree : yChartResultant.natTrailingDegree = 8 := by
  have hc : yChartResultant.coeff 8 ≠ 0 := by
    rw [yChartResultant_coeff_eight]
    decide
  apply Nat.le_antisymm (Polynomial.natTrailingDegree_le_of_ne_zero hc)
  apply Polynomial.le_natTrailingDegree
  · intro hp
    apply hc
    simp [hp]
  · intro n hn
    exact yChartResultant_coeff_below_eight ⟨n, hn⟩

end PoincareChapterVI.Section103Resultant
