/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.Section103.AffineEliminationCertificateChecks

/-!
# Soundness of the affine-elimination certificates

The executable balanced-map normalizer denotes the original sparse polynomial.  Consequently its
four checked Boolean equalities become equalities in `MvPolynomial (Fin 2) ℂ`.
-/

noncomputable section

namespace PoincareChapterVI.AffineEliminationCertificate

open AffineEliminationData

def mapCoefficient (terms : Std.TreeMap ℕ QI) (exponent : Exp) : QI :=
  terms[expKey exponent]?.getD 0

theorem exp_ext {left right : Exp} (hx : left.x = right.x) (hy : left.y = right.y) :
    left = right := by
  cases left
  cases right
  simp_all

theorem mapCoefficient_insertTerm (terms : Std.TreeMap ℕ QI) (term : Term)
    (exponent : Exp) :
    mapCoefficient (insertTerm terms term) exponent =
      mapCoefficient terms exponent +
        if term.exp = exponent then term.coeff else 0 := by
  unfold mapCoefficient insertTerm
  rw [Std.TreeMap.getElem?_alter]
  by_cases h : term.exp = exponent
  · subst exponent
    simp
    split <;> simp_all
  · have hkey : expKey term.exp ≠ expKey exponent := by
      intro equality
      apply h
      exact exp_ext (Nat.pair_eq_pair.mp equality).1
        (Nat.pair_eq_pair.mp equality).2
    have hc : compare (expKey term.exp) (expKey exponent) ≠ .eq := by
      simpa using hkey
    simp [hc, h]

theorem mapCoefficient_accumulate (polynomial : Sparse) (terms : Std.TreeMap ℕ QI)
    (exponent : Exp) :
    mapCoefficient (accumulate polynomial terms) exponent =
      mapCoefficient terms exponent + coefficient polynomial exponent := by
  induction polynomial generalizing terms with
  | nil => simp [accumulate, coefficient]
  | cons term rest ih =>
      rw [accumulate, ih, mapCoefficient_insertTerm]
      simp only [coefficient]
      split <;> ring

theorem mapCoefficient_normalMap (polynomial : Sparse) (exponent : Exp) :
    mapCoefficient (normalMap polynomial) exponent = coefficient polynomial exponent := by
  rw [normalMap, mapCoefficient_accumulate]
  simp [mapCoefficient]

theorem coefficient_eq_of_normalMap_beq {left right : Sparse}
    (h : normalMap left == normalMap right) (exponent : Exp) :
    coefficient left exponent = coefficient right exponent := by
  have hequiv := Std.TreeMap.equiv_of_beq h
  have hget : (normalMap left)[expKey exponent]? =
      (normalMap right)[expKey exponent]? := hequiv.getElem?_eq
  rw [← mapCoefficient_normalMap left exponent,
    ← mapCoefficient_normalMap right exponent]
  exact congrArg (fun value : Option QI => value.getD 0) hget

def expFinsupp (exponent : Exp) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 exponent.x + Finsupp.single 1 exponent.y

theorem expFinsupp_injective : Function.Injective expFinsupp := by
  intro left right h
  exact exp_ext
    (by simpa [expFinsupp] using congrArg (fun value => value 0) h)
    (by simpa [expFinsupp] using congrArg (fun value => value 1) h)

def termToMv (term : Term) : MvPolynomial (Fin 2) ℂ :=
  MvPolynomial.monomial (expFinsupp term.exp)
    (PoincareChapterVI.Section103Source.qiToComplex term.coeff)

def toMv (polynomial : Sparse) : MvPolynomial (Fin 2) ℂ :=
  (polynomial.map termToMv).sum

theorem expFinsupp_mulExp (left right : Exp) :
    expFinsupp (mulExp left right) = expFinsupp left + expFinsupp right := by
  ext i
  fin_cases i <;> simp [expFinsupp, mulExp]

theorem termToMv_mul (left right : Term) :
    termToMv ⟨mulExp left.exp right.exp, left.coeff * right.coeff⟩ =
      termToMv left * termToMv right := by
  simp [termToMv, expFinsupp_mulExp, MvPolynomial.monomial_mul]

theorem toMv_add (left right : Sparse) :
    toMv (add left right) = toMv left + toMv right := by
  simp [toMv, add]

theorem toMv_mul_single_left (term : Term) (right : Sparse) :
    toMv (right.map fun rightTerm =>
      ⟨mulExp term.exp rightTerm.exp, term.coeff * rightTerm.coeff⟩) =
      termToMv term * toMv right := by
  induction right with
  | nil => simp [toMv]
  | cons rightTerm rest ih =>
      change
        termToMv ⟨mulExp term.exp rightTerm.exp, term.coeff * rightTerm.coeff⟩ +
            toMv (rest.map fun value =>
              ⟨mulExp term.exp value.exp, term.coeff * value.coeff⟩) =
          termToMv term * (termToMv rightTerm + toMv rest)
      rw [ih, termToMv_mul, mul_add]

theorem toMv_mul (left right : Sparse) :
    toMv (mul left right) = toMv left * toMv right := by
  induction left with
  | nil => simp [toMv, mul]
  | cons term rest ih =>
      have hleft : toMv (mul (term :: rest) right) =
          toMv (right.map fun rightTerm =>
            ⟨mulExp term.exp rightTerm.exp, term.coeff * rightTerm.coeff⟩) +
            toMv (mul rest right) := by
        simp [mul, toMv]
      have hright : toMv (term :: rest) = termToMv term + toMv rest := rfl
      rw [hleft, hright, toMv_mul_single_left, ih, add_mul]

theorem coeff_toMv (polynomial : Sparse) (exponent : Exp) :
    MvPolynomial.coeff (expFinsupp exponent) (toMv polynomial) =
      PoincareChapterVI.Section103Source.qiToComplex
        (coefficient polynomial exponent) := by
  induction polynomial with
  | nil => simp [toMv, coefficient]
  | cons term rest ih =>
      by_cases h : term.exp = exponent
      · subst exponent
        change MvPolynomial.coeff (expFinsupp term.exp)
            (termToMv term + toMv rest) = _
        simp [termToMv, coefficient, ih]
      · have h' : expFinsupp term.exp ≠ expFinsupp exponent :=
          fun equality => h (expFinsupp_injective equality)
        change MvPolynomial.coeff (expFinsupp exponent)
            (termToMv term + toMv rest) = _
        simp [termToMv, coefficient, ih, h, h']

def expOfFinsupp (exponent : Fin 2 →₀ ℕ) : Exp :=
  ⟨exponent 0, exponent 1⟩

theorem expFinsupp_expOfFinsupp (exponent : Fin 2 →₀ ℕ) :
    expFinsupp (expOfFinsupp exponent) = exponent := by
  ext i
  fin_cases i <;> simp [expFinsupp, expOfFinsupp]

theorem toMv_eq_of_normalMap_beq {left right : Sparse}
    (h : normalMap left == normalMap right) : toMv left = toMv right := by
  apply MvPolynomial.ext
  intro exponent
  rw [← expFinsupp_expOfFinsupp exponent, coeff_toMv, coeff_toMv]
  exact congrArg PoincareChapterVI.Section103Source.qiToComplex
    (coefficient_eq_of_normalMap_beq h (expOfFinsupp exponent))

theorem shape_from_tail_mv : toMv shapePolynomial = toMv shapeFromTail :=
  toMv_eq_of_normalMap_beq shape_from_tail_certificate

theorem eliminant_from_residual_mv : toMv eliminant = toMv eliminantFromResidual :=
  toMv_eq_of_normalMap_beq eliminant_from_residual_certificate

set_option maxRecDepth 100000 in
section

theorem shape_membership_mv :
    toMv shapeMembershipLeft = toMv shapePolynomial :=
  toMv_eq_of_normalMap_beq shape_membership_certificate

theorem eliminant_membership_mv :
    toMv eliminantMembershipLeft = toMv eliminant :=
  toMv_eq_of_normalMap_beq eliminant_membership_certificate

theorem sextic_reconstruction_mv :
    toMv sexticReconstructionLeft = toMv affineSextic :=
  toMv_eq_of_normalMap_beq sextic_reconstruction_certificate

theorem septic_reconstruction_mv :
    toMv septicReconstructionLeft = toMv affineSeptic :=
  toMv_eq_of_normalMap_beq septic_reconstruction_certificate

end

end PoincareChapterVI.AffineEliminationCertificate
