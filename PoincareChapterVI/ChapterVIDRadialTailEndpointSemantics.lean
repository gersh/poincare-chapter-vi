/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.ChapterVIDRadialTailEndpointTrace
import Mathlib.Analysis.Convex.Deriv

namespace PoincareChapterVI.ChapterVIDRadialTailEndpointTrace

open ChapterVIFieldExpression Expr
open scoped unitInterval

noncomputable section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

@[simp] def baseValues (x : ℝ) : Fin 5 → ℂ :=
  ![(x : ℂ), chapterVIDCollisionLift, chapterVIDY, 0, Complex.I]

@[simp] def exactValues (side : ChapterVIDPinchingArcSide) (x : ℝ) : Fin 5 → ℂ :=
  ![(x : ℂ), chapterVIDCollisionLift, chapterVIDY,
    Complex.exp ((argument side).eval (baseValues x)), Complex.I]

theorem argument_eval_exact_eq_base (side : ChapterVIDPinchingArcSide) (x : ℝ) :
    (argument side).eval (exactValues side x) =
      (argument side).eval (baseValues x) := by
  cases side <;> rfl

def endpointComplex (side : ChapterVIDPinchingArcSide) (x : ℝ) : ℂ :=
  (radicand side).eval (exactValues side x)

def endpointReal (side : ChapterVIDPinchingArcSide) (x : ℝ) : ℝ :=
  (endpointComplex side x).re

def basicVelocityValue : Fin 5 → ℂ
  | 0 => 1
  | _ => 0

theorem basicVelocityValue_eq (values : Fin 5 → ℂ) (i : Fin 5) :
    basicVelocityValue i = (basicVelocity i).eval values := by
  fin_cases i <;> simp [basicVelocityValue, basicVelocity, Expr.eval]

attribute [irreducible] basicVelocityValue

def endpointVelocity (side : ChapterVIDPinchingArcSide) (x : ℝ) (i : Fin 5) : ℂ :=
  (velocity side i).eval (exactValues side x)

def endpointAcceleration (side : ChapterVIDPinchingArcSide) (x : ℝ) (i : Fin 5) : ℂ :=
  (velocity side i).directionalEval (exactValues side x) (endpointVelocity side x)

def endpointFirst (side : ChapterVIDPinchingArcSide) (x : ℝ) : ℂ :=
  (radicand side).directionalEval (exactValues side x)
    (endpointVelocity side x)

def endpointSecond (side : ChapterVIDPinchingArcSide) (x : ℝ) : ℂ :=
  (radicand side).secondDirectionalEval (exactValues side x)
    (endpointVelocity side x) (endpointAcceleration side x)

theorem endpointVelocity_eq (side : ChapterVIDPinchingArcSide) (x : ℝ) (i : Fin 5) :
    endpointVelocity side x i = (velocity side i).eval (exactValues side x) := rfl

theorem endpointAcceleration_eq (side : ChapterVIDPinchingArcSide) (x : ℝ) (i : Fin 5) :
    endpointAcceleration side x i =
      (velocity side i).directionalEval (exactValues side x) (endpointVelocity side x) := rfl

theorem endpointFirst_eq (side : ChapterVIDPinchingArcSide) (x : ℝ) :
    endpointFirst side x = (radicand side).directionalEval (exactValues side x)
      (endpointVelocity side x) := rfl

theorem endpointSecond_eq (side : ChapterVIDPinchingArcSide) (x : ℝ) :
    endpointSecond side x =
      (radicand side).secondDirectionalEval (exactValues side x)
        (endpointVelocity side x) (endpointAcceleration side x) := rfl

/-- The compact second-order evaluator used by the analytic proof is exactly the directional
derivative enclosed by the compiled jet trace. -/
theorem endpointSecond_eq_directional_first
    (side : ChapterVIDPinchingArcSide) (x : ℝ) :
    endpointSecond side x =
      (firstDerivative side).directionalEval (exactValues side x)
        (endpointVelocity side x) := by
  rw [endpointSecond_eq]
  have hv : endpointVelocity side x =
      fun i ↦ (velocity side i).eval (exactValues side x) := by
    funext i
    exact endpointVelocity_eq side x i
  have ha : endpointAcceleration side x = fun i ↦
      (velocity side i).directionalEval (exactValues side x)
        (fun j ↦ (velocity side j).eval (exactValues side x)) := by
    funext i
    rw [endpointAcceleration_eq, hv]
  rw [hv, ha, secondDirectionalEval_eq_directional]
  rfl

attribute [irreducible] endpointVelocity endpointAcceleration endpointFirst endpointSecond

private theorem denominator_ne_zero (x : ℝ) : (1 + (x : ℂ) ^ 2) ≠ 0 := by
  norm_cast
  nlinarith [sq_nonneg x]

private theorem quarter_ne_zero (x : ℝ) :
    (((1 - (x : ℂ) ^ 2) + 2 * x * Complex.I) / (1 + (x : ℂ) ^ 2)) ≠ 0 := by
  apply div_ne_zero
  · intro h
    have him := congrArg Complex.im h
    have him' : 2 * x = 0 := by
      simpa [pow_two, Complex.add_im, Complex.sub_im, Complex.mul_im] using him
    have hx : x = 0 := by linarith
    subst x
    norm_num at h
  · exact denominator_ne_zero x

private theorem eval_u_ne_zero (side : ChapterVIDPinchingArcSide) (x : ℝ) :
    (u side).eval (exactValues side x) ≠ 0 := by
  have hD := chapterVIDCollisionLift_ne_zero
  have hq := quarter_ne_zero x
  cases side
  · simpa [u, unit, quarter, r, t, collision, imaginaryUnit, Expr.eval] using
      mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr hD) Complex.I_ne_zero) hq
  · simpa [u, unit, quarter, r, t, collision, imaginaryUnit, Expr.eval] using
      mul_ne_zero (neg_ne_zero.mpr hD) (neg_ne_zero.mpr hq)

private theorem eval_anomaly_ne_zero (side : ChapterVIDPinchingArcSide) (x : ℝ) :
    (anomaly side).eval (exactValues side x) ≠ 0 := by
  have hY : chapterVIDYReal ≠ 0 := by
    simpa [chapterVIDY_eq_ofReal] using chapterVIDY_ne_zero
  have h := And.intro hY (And.intro (eval_u_ne_zero side x)
    chapterVIDCollisionLift_ne_zero)
  simpa [anomaly, yBase, exponential, collision, r, Expr.eval] using h

private theorem quarter_defined {values : Fin 5 → ℂ}
    (h : 1 + (values 0) ^ 2 ≠ 0) : quarter.DefinedAt values := by
  simp only [quarter, t, imaginaryUnit, r, Expr.definedAt_div,
    Expr.definedAt_add, Expr.definedAt_neg, Expr.definedAt_sub,
    Expr.definedAt_mul, Expr.definedAt_pow_succ, Expr.definedAt_var,
    Expr.definedAt_ofNat, Expr.eval_add, Expr.eval_pow, Expr.eval_var,
    Expr.eval_ofNat, Expr.eval, Expr.DefinedAt, and_self, true_and]
  convert h using 1 <;> norm_num

private theorem u_defined (side : ChapterVIDPinchingArcSide)
    {values : Fin 5 → ℂ} (hq : quarter.DefinedAt values) :
    (u side).DefinedAt values := by
  cases side <;> simp only [u, unit, collision, imaginaryUnit, r,
    Expr.definedAt_mul, Expr.definedAt_neg, Expr.definedAt_var, hq, and_self]

private theorem argument_defined_of (side : ChapterVIDPinchingArcSide)
    {values : Fin 5 → ℂ} (hu : (u side).DefinedAt values)
    (huNe : (u side).eval values ≠ 0) (hD : values 1 ≠ 0) :
    (argument side).DefinedAt values := by
  simp only [argument, collision, r, Expr.definedAt_mul, Expr.definedAt_div,
    Expr.definedAt_sub, Expr.definedAt_inv, Expr.definedAt_pow_succ,
    Expr.definedAt_var, Expr.definedAt_ofNat, Expr.eval_var, hu, huNe,
    hD, inv_ne_zero, true_and, and_self]
  exact ⟨by norm_num [Expr.DefinedAt, Expr.eval], ⟨huNe, trivial⟩,
    ⟨hD, trivial⟩⟩

private theorem anomaly_defined_of (side : ChapterVIDPinchingArcSide)
    {values : Fin 5 → ℂ} (hu : (u side).DefinedAt values)
    (hD : values 1 ≠ 0) : (anomaly side).DefinedAt values := by
  simp only [anomaly, yBase, exponential, collision, r, Expr.definedAt_mul,
    Expr.definedAt_inv, Expr.definedAt_var, Expr.eval_var, hu]
  aesop

private theorem radicand_defined_of (side : ChapterVIDPinchingArcSide)
    {values : Fin 5 → ℂ} (hu : (u side).DefinedAt values)
    (huNe : (u side).eval values ≠ 0) (ha : (anomaly side).DefinedAt values)
    (haNe : (anomaly side).eval values ≠ 0) :
    (radicand side).DefinedAt values := by
  simp only [radicand, factorPlus, factorMinus, Expr.definedAt_mul,
    Expr.definedAt_sub, Expr.definedAt_div, Expr.definedAt_add,
    Expr.definedAt_inv, Expr.definedAt_pow_succ, Expr.definedAt_ofNat,
    Expr.eval_pow, Expr.eval_ofNat, hu, huNe, ha, haNe]
  all_goals norm_num [Expr.DefinedAt, Expr.eval] <;> aesop

private theorem argument_defined (side : ChapterVIDPinchingArcSide) (x : ℝ) :
    (argument side).DefinedAt (exactValues side x) := by
  have hquarter : (quarter : E).DefinedAt (exactValues side x) :=
    quarter_defined (by simpa [exactValues] using denominator_ne_zero x)
  exact argument_defined_of side (u_defined side hquarter)
    (eval_u_ne_zero side x) (by simpa [exactValues] using chapterVIDCollisionLift_ne_zero)

private theorem radicand_defined (side : ChapterVIDPinchingArcSide) (x : ℝ) :
    (radicand side).DefinedAt (exactValues side x) := by
  have hquarter : (quarter : E).DefinedAt (exactValues side x) :=
    quarter_defined (by simpa [exactValues] using denominator_ne_zero x)
  have hu := u_defined side hquarter
  have hD : exactValues side x 1 ≠ 0 := by
    simpa [exactValues] using chapterVIDCollisionLift_ne_zero
  exact radicand_defined_of side hu (eval_u_ne_zero side x)
    (anomaly_defined_of side hu hD) (eval_anomaly_ne_zero side x)

private theorem velocity_paths (side : ChapterVIDPinchingArcSide) (x : ℝ) :
    ∀ i, HasDerivAt (fun y ↦ exactValues side y i)
      (endpointVelocity side x i) x := by
  intro i
  fin_cases i
  · rw [endpointVelocity_eq]
    simpa [exactValues, velocity, Expr.eval] using (hasDerivAt_id x).ofReal_comp
  · rw [endpointVelocity_eq]
    simpa [exactValues, velocity, Expr.eval] using
      (hasDerivAt_const x chapterVIDCollisionLift)
  · rw [endpointVelocity_eq]
    simpa [exactValues, velocity, Expr.eval] using (hasDerivAt_const x chapterVIDY)
  · have hdefinedBase : (argument side).DefinedAt (baseValues x) := by
      have hquarter : (quarter : E).DefinedAt (baseValues x) :=
        quarter_defined (by simpa [baseValues] using denominator_ne_zero x)
      have hu := u_defined side hquarter
      have huNe : (u side).eval (baseValues x) ≠ 0 := by
        have heq : (u side).eval (baseValues x) =
            (u side).eval (exactValues side x) := by cases side <;> rfl
        rw [heq]
        exact eval_u_ne_zero side x
      exact argument_defined_of side hu huNe
        (by simpa [baseValues] using chapterVIDCollisionLift_ne_zero)
    have hbasePaths : ∀ j, HasDerivAt (fun y ↦ baseValues y j)
        (basicVelocityValue j) x := by
      intro j
      fin_cases j
      · rw [basicVelocityValue_eq (baseValues x)]
        simpa [baseValues, basicVelocity, Expr.eval] using
          (hasDerivAt_id x).ofReal_comp
      · rw [basicVelocityValue_eq (baseValues x)]
        simpa [baseValues, basicVelocity, Expr.eval] using
          (hasDerivAt_const x chapterVIDCollisionLift)
      · rw [basicVelocityValue_eq (baseValues x)]
        simpa [baseValues, basicVelocity, Expr.eval] using
          (hasDerivAt_const x chapterVIDY)
      · rw [basicVelocityValue_eq (baseValues x)]
        simpa [baseValues, basicVelocity, Expr.eval] using
          (hasDerivAt_const x (0 : ℂ))
      · rw [basicVelocityValue_eq (baseValues x)]
        simpa [baseValues, basicVelocity, Expr.eval] using
          (hasDerivAt_const x Complex.I)
    have harg := Expr.hasDerivAt_eval_semantic
      (paths := fun j y ↦ baseValues y j) (argument side) hdefinedBase hbasePaths
    apply harg.cexp.congr_deriv
    rw [endpointVelocity_eq]
    change _ = (exponential * (argument side).directional basicVelocity).eval
      (exactValues side x)
    rw [Expr.eval_mul]
    have hv : basicVelocityValue =
        (fun j ↦ (basicVelocity j).eval (fun i ↦ baseValues x i)) := by
      funext j
      exact basicVelocityValue_eq _ j
    rw [hv, directionalEval_eq_eval_directional
      (fun i ↦ baseValues x i) basicVelocity (argument side)]
    have hvalues : ∀ i, i ≠ (3 : Fin 5) → baseValues x i = exactValues side x i := by
      intro i hi
      fin_cases i <;> simp_all [baseValues, exactValues]
    have hdir := Expr.eval_eq_of_eq_except
      (left := baseValues x) (right := exactValues side x)
      (expression := (argument side).directional basicVelocity)
      (by cases side <;> decide +kernel) hvalues
    rw [hdir]
    rfl
  · rw [endpointVelocity_eq]
    simpa [exactValues, velocity, Expr.eval] using (hasDerivAt_const x Complex.I)

theorem hasDerivAt_uEval (side : ChapterVIDPinchingArcSide) (x : ℝ) :
    HasDerivAt (fun y ↦ (u side).eval (exactValues side y))
      ((u side).directionalEval (exactValues side x) (endpointVelocity side x)) x := by
  have hquarter : (quarter : E).DefinedAt (exactValues side x) :=
    quarter_defined (by simpa [exactValues] using denominator_ne_zero x)
  exact Expr.hasDerivAt_eval_semantic (u side) (u_defined side hquarter)
    (velocity_paths side x)

theorem hasDerivAt_factorPlusEval (side : ChapterVIDPinchingArcSide) (x : ℝ) :
    HasDerivAt (fun y ↦ (factorPlus side).eval (exactValues side y))
      ((factorPlus side).directionalEval (exactValues side x)
        (endpointVelocity side x)) x := by
  have hdefined := radicand_defined side x
  simp only [radicand, Expr.definedAt_mul] at hdefined
  exact Expr.hasDerivAt_eval_semantic (factorPlus side) hdefined.1
    (velocity_paths side x)

theorem hasDerivAt_factorMinusEval (side : ChapterVIDPinchingArcSide) (x : ℝ) :
    HasDerivAt (fun y ↦ (factorMinus side).eval (exactValues side y))
      ((factorMinus side).directionalEval (exactValues side x)
        (endpointVelocity side x)) x := by
  have hdefined := radicand_defined side x
  simp only [radicand, Expr.definedAt_mul] at hdefined
  exact Expr.hasDerivAt_eval_semantic (factorMinus side) hdefined.2
    (velocity_paths side x)

theorem hasDerivAt_endpointComplex (side : ChapterVIDPinchingArcSide) (x : ℝ) :
    HasDerivAt (endpointComplex side)
      (endpointFirst side x) x := by
  apply (Expr.hasDerivAt_eval_semantic (radicand side) (radicand_defined side x)
    (velocity_paths side x)).congr_deriv
  exact (endpointFirst_eq side x).symm

private theorem velocity_defined (side : ChapterVIDPinchingArcSide) (x : ℝ) :
    ∀ i, (velocity side i).DefinedAt (exactValues side x) := by
  intro i
  fin_cases i
  · trivial
  · trivial
  · trivial
  · exact ⟨trivial, directional_definedAt (argument_defined side x) (by
      intro j
      fin_cases j <;> trivial)⟩
  · trivial

theorem hasDerivAt_first (side : ChapterVIDPinchingArcSide) (x : ℝ) :
    HasDerivAt (endpointFirst side) (endpointSecond side x) x := by
  have hvelocityPaths : ∀ i, HasDerivAt
      (fun y ↦ endpointVelocity side y i)
      (endpointAcceleration side x i) x := by
    intro i
    have h := Expr.hasDerivAt_eval_semantic (velocity side i)
      (velocity_defined side x i) (velocity_paths side x)
    apply (h.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun y ↦
      endpointVelocity_eq side y i))).congr_deriv
    exact (endpointAcceleration_eq side x i).symm
  have h := Expr.hasDerivAt_directionalEval (radicand side)
    (radicand_defined side x) (velocity_paths side x) hvelocityPaths
      (fun _ ↦ rfl)
  apply (h.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun y ↦
    endpointFirst_eq side y))).congr_deriv
  exact (endpointSecond_eq side x).symm

theorem hasDerivAt_endpointReal (side : ChapterVIDPinchingArcSide) (x : ℝ) :
    HasDerivAt (endpointReal side)
      (endpointFirst side x).re x := by
  exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt x
    (hasDerivAt_endpointComplex side x)

theorem hasSecondDerivAt_endpointReal (side : ChapterVIDPinchingArcSide) (x : ℝ) :
    HasDerivAt
      (fun y ↦ (endpointFirst side y).re) (endpointSecond side x).re x := by
  exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt x (hasDerivAt_first side x)

end
end PoincareChapterVI.ChapterVIDRadialTailEndpointTrace
