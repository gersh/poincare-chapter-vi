/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.Section103.InfinityNormalFormCertificateChecks

/-!
# Soundness of the infinity normal-form certificates

This file proves once that the executable balanced-map normalizer denotes the same bivariate
polynomial as the original sparse term list.  The ten checked Boolean identities therefore
become genuine equalities in `MvPolynomial (Fin 2) ℂ`.
-/

noncomputable section

namespace PoincareChapterVI.InfinityNormalFormCertificate

open InfinityNormalFormData

def mapCoefficient (terms : Std.TreeMap ℕ QI) (exponent : Exp) : QI :=
  terms[expKey exponent]?.getD 0

theorem exp_ext {left right : Exp} (hy : left.y = right.y) (hz : left.z = right.z) :
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

theorem mapCoefficient_accumulate (p : Sparse) (terms : Std.TreeMap ℕ QI)
    (exponent : Exp) :
    mapCoefficient (accumulate p terms) exponent =
      mapCoefficient terms exponent + coefficient p exponent := by
  induction p generalizing terms with
  | nil => simp [accumulate, coefficient]
  | cons term rest ih =>
      rw [accumulate, ih, mapCoefficient_insertTerm]
      simp only [coefficient]
      split <;> ring

theorem mapCoefficient_normalMap (p : Sparse) (exponent : Exp) :
    mapCoefficient (normalMap p) exponent = coefficient p exponent := by
  rw [normalMap, mapCoefficient_accumulate]
  simp [mapCoefficient]

theorem coefficient_eq_of_normalMap_beq {p q : Sparse}
    (h : normalMap p == normalMap q) (exponent : Exp) :
    coefficient p exponent = coefficient q exponent := by
  have hequiv := Std.TreeMap.equiv_of_beq h
  have hget : (normalMap p)[expKey exponent]? = (normalMap q)[expKey exponent]? :=
    hequiv.getElem?_eq
  rw [← mapCoefficient_normalMap p exponent, ← mapCoefficient_normalMap q exponent]
  exact congrArg (fun value : Option QI => value.getD 0) hget

def expFinsupp (exponent : Exp) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 exponent.y + Finsupp.single 1 exponent.z

theorem expFinsupp_injective : Function.Injective expFinsupp := by
  intro left right h
  exact exp_ext
    (by simpa [expFinsupp] using congrArg (fun value => value 0) h)
    (by simpa [expFinsupp] using congrArg (fun value => value 1) h)

def termToMv (term : Term) : MvPolynomial (Fin 2) ℂ :=
  MvPolynomial.monomial (expFinsupp term.exp)
    (PoincareChapterVI.Section103Source.qiToComplex term.coeff)

def toMv (p : Sparse) : MvPolynomial (Fin 2) ℂ :=
  (p.map termToMv).sum

theorem expFinsupp_mulExp (left right : Exp) :
    expFinsupp (mulExp left right) = expFinsupp left + expFinsupp right := by
  ext i
  fin_cases i <;> simp [expFinsupp, mulExp]

theorem termToMv_mul (left right : Term) :
    termToMv ⟨mulExp left.exp right.exp, left.coeff * right.coeff⟩ =
      termToMv left * termToMv right := by
  simp [termToMv, expFinsupp_mulExp, MvPolynomial.monomial_mul]

theorem toMv_add (p q : Sparse) : toMv (add p q) = toMv p + toMv q := by
  simp [toMv, add]

theorem toMv_mul_single_left (term : Term) (q : Sparse) :
    toMv (q.map fun right =>
      ⟨mulExp term.exp right.exp, term.coeff * right.coeff⟩) =
      termToMv term * toMv q := by
  induction q with
  | nil => simp [toMv]
  | cons right rest ih =>
      change
        termToMv ⟨mulExp term.exp right.exp, term.coeff * right.coeff⟩ +
            toMv (rest.map fun value =>
              ⟨mulExp term.exp value.exp, term.coeff * value.coeff⟩) =
          termToMv term * (termToMv right + toMv rest)
      rw [ih, termToMv_mul, mul_add]

theorem toMv_mul (p q : Sparse) : toMv (mul p q) = toMv p * toMv q := by
  induction p with
  | nil => simp [toMv, mul]
  | cons term rest ih =>
      have hleft : toMv (mul (term :: rest) q) =
          toMv (q.map fun right =>
            ⟨mulExp term.exp right.exp, term.coeff * right.coeff⟩) +
            toMv (mul rest q) := by
        simp [mul, toMv]
      have hright : toMv (term :: rest) = termToMv term + toMv rest := rfl
      rw [hleft, hright, toMv_mul_single_left, ih, add_mul]

theorem coeff_toMv (p : Sparse) (exponent : Exp) :
    MvPolynomial.coeff (expFinsupp exponent) (toMv p) =
      PoincareChapterVI.Section103Source.qiToComplex (coefficient p exponent) := by
  induction p with
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

theorem eval_zero_toMv (p : Sparse) :
    MvPolynomial.eval (0 : Fin 2 → ℂ) (toMv p) =
      PoincareChapterVI.Section103Source.qiToComplex (coefficient p ⟨0, 0⟩) := by
  rw [show MvPolynomial.eval (0 : Fin 2 → ℂ) (toMv p) =
      MvPolynomial.constantCoeff (toMv p) by
    exact DFunLike.congr_fun MvPolynomial.eval_zero (toMv p)]
  rw [MvPolynomial.constantCoeff_eq]
  simpa [expFinsupp] using coeff_toMv p ⟨0, 0⟩

def expOfFinsupp (exponent : Fin 2 →₀ ℕ) : Exp :=
  ⟨exponent 0, exponent 1⟩

theorem expFinsupp_expOfFinsupp (exponent : Fin 2 →₀ ℕ) :
    expFinsupp (expOfFinsupp exponent) = exponent := by
  ext i
  fin_cases i <;> simp [expFinsupp, expOfFinsupp]

theorem toMv_eq_of_normalMap_beq {p q : Sparse}
    (h : normalMap p == normalMap q) : toMv p = toMv q := by
  apply MvPolynomial.ext
  intro exponent
  rw [← expFinsupp_expOfFinsupp exponent, coeff_toMv, coeff_toMv]
  exact congrArg PoincareChapterVI.Section103Source.qiToComplex
    (coefficient_eq_of_normalMap_beq h (expOfFinsupp exponent))

set_option maxRecDepth 100000 in
section

theorem x_localized_first_mv : toMv xLocalizedFirstLeft = toMv xLocalizedFirstRight :=
  toMv_eq_of_normalMap_beq x_localized_first_certificate

theorem x_localized_second_mv : toMv xLocalizedSecondLeft = toMv xLocalizedSecondRight :=
  toMv_eq_of_normalMap_beq x_localized_second_certificate

theorem x_localized_third_mv : toMv xLocalizedThirdLeft = toMv xLocalizedThirdRight :=
  toMv_eq_of_normalMap_beq x_localized_third_certificate

theorem y_localized_first_mv : toMv yLocalizedFirstLeft = toMv yLocalizedFirstRight :=
  toMv_eq_of_normalMap_beq y_localized_first_certificate

theorem y_localized_second_mv : toMv yLocalizedSecondLeft = toMv yLocalizedSecondRight :=
  toMv_eq_of_normalMap_beq y_localized_second_certificate

theorem y_localized_third_mv : toMv yLocalizedThirdLeft = toMv yLocalizedThirdRight :=
  toMv_eq_of_normalMap_beq y_localized_third_certificate

theorem x_chart_first_mv : toMv xChartFirstLeft = toMv xChartFirstRight :=
  toMv_eq_of_normalMap_beq x_chart_first_certificate

theorem x_chart_second_mv : toMv xChartSecondLeft = toMv xChartSecondRight :=
  toMv_eq_of_normalMap_beq x_chart_second_certificate

theorem y_chart_first_mv : toMv yChartFirstLeft = toMv yChartFirstRight :=
  toMv_eq_of_normalMap_beq y_chart_first_certificate

theorem y_chart_second_mv : toMv yChartSecondLeft = toMv yChartSecondRight :=
  toMv_eq_of_normalMap_beq y_chart_second_certificate

end

end PoincareChapterVI.InfinityNormalFormCertificate
