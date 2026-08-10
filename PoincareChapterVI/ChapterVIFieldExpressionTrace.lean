/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.ChapterVILeanCompCertProposals

/-!
# Differentiable field expressions with compiled interval traces

Formal differentiation happens before interval evaluation, so repeated occurrences of a radial
variable retain their algebraic dependency.  The evaluator then reduces every multiplication and
reciprocal to the existing signed-dyadic LeanCompCert operations.
-/

noncomputable section

namespace PoincareChapterVI

open ChapterVILeanCompCertBatch

namespace ChapterVIFieldExpression

inductive Expr (arity : ℕ) where
  | var (index : Fin arity)
  | integer (value : ℤ)
  | add (left right : Expr arity)
  | neg (argument : Expr arity)
  | mul (left right : Expr arity)
  | inv (argument : Expr arity)
  deriving DecidableEq, Repr

namespace Expr

instance {arity : ℕ} : Zero (Expr arity) := ⟨.integer 0⟩
instance {arity : ℕ} : One (Expr arity) := ⟨.integer 1⟩
instance {arity : ℕ} : Add (Expr arity) := ⟨.add⟩
instance {arity : ℕ} : Neg (Expr arity) := ⟨.neg⟩
instance {arity : ℕ} : Sub (Expr arity) := ⟨fun x y ↦ .add x (.neg y)⟩
instance {arity : ℕ} : Mul (Expr arity) := ⟨.mul⟩
instance {arity : ℕ} : Inv (Expr arity) := ⟨.inv⟩
instance {arity : ℕ} : Div (Expr arity) := ⟨fun x y ↦ .mul x (.inv y)⟩
instance {arity : ℕ} : OfNat (Expr arity) n := ⟨.integer n⟩

def int {arity : ℕ} (value : ℤ) : Expr arity := .integer value

def npow {arity : ℕ} (expression : Expr arity) : ℕ → Expr arity
  | 0 => 1
  | n + 1 => expression.npow n * expression

instance {arity : ℕ} : Pow (Expr arity) ℕ := ⟨npow⟩

def eval {arity : ℕ} (values : Fin arity → ℂ) : Expr arity → ℂ
  | .var index => values index
  | .integer value => value
  | .add left right => left.eval values + right.eval values
  | .neg argument => -argument.eval values
  | .mul left right => left.eval values * right.eval values
  | .inv argument => (argument.eval values)⁻¹

/-- `VariablesBelow bound e` is a decidable certificate that every register read by `e`
has index strictly below `bound`. -/
def VariablesBelow {arity : ℕ} (bound : ℕ) : Expr arity → Bool
  | .var index => index.val < bound
  | .integer _ => true
  | .add left right | .mul left right =>
      left.VariablesBelow bound && right.VariablesBelow bound
  | .neg argument | .inv argument => argument.VariablesBelow bound

theorem eval_eq_of_eq_below {arity bound : ℕ} {left right : Fin arity → ℂ}
    {expression : Expr arity} (hvariables : expression.VariablesBelow bound = true)
    (hvalues : ∀ i, i.val < bound → left i = right i) :
    expression.eval left = expression.eval right := by
  induction expression with
  | var i => exact hvalues i (by simpa [VariablesBelow] using hvariables)
  | integer _ => rfl
  | add x y ihx ihy =>
      simp only [VariablesBelow, Bool.and_eq_true] at hvariables
      simp only [eval, ihx hvariables.1, ihy hvariables.2]
  | neg x ih => simp only [VariablesBelow] at hvariables; simp only [eval, ih hvariables]
  | mul x y ihx ihy =>
      simp only [VariablesBelow, Bool.and_eq_true] at hvariables
      simp only [eval, ihx hvariables.1, ihy hvariables.2]
  | inv x ih => simp only [VariablesBelow] at hvariables; simp only [eval, ih hvariables]

/-- Decidable certificate that an expression does not read one distinguished register. -/
def AvoidsVariable {arity : ℕ} (forbidden : Fin arity) : Expr arity → Bool
  | .var index => index != forbidden
  | .integer _ => true
  | .add left right | .mul left right =>
      left.AvoidsVariable forbidden && right.AvoidsVariable forbidden
  | .neg argument | .inv argument => argument.AvoidsVariable forbidden

theorem eval_eq_of_eq_except {arity : ℕ} {left right : Fin arity → ℂ}
    {forbidden : Fin arity} {expression : Expr arity}
    (havoids : expression.AvoidsVariable forbidden = true)
    (hvalues : ∀ i, i ≠ forbidden → left i = right i) :
    expression.eval left = expression.eval right := by
  induction expression with
  | var i =>
      apply hvalues i
      simpa [AvoidsVariable, bne_iff_ne] using havoids
  | integer _ => rfl
  | add x y ihx ihy =>
      simp only [AvoidsVariable, Bool.and_eq_true] at havoids
      simp only [eval, ihx havoids.1, ihy havoids.2]
  | neg x ih => simp only [AvoidsVariable] at havoids; simp only [eval, ih havoids]
  | mul x y ihx ihy =>
      simp only [AvoidsVariable, Bool.and_eq_true] at havoids
      simp only [eval, ihx havoids.1, ihy havoids.2]
  | inv x ih => simp only [AvoidsVariable] at havoids; simp only [eval, ih havoids]

def DefinedAt {arity : ℕ} (values : Fin arity → ℂ) : Expr arity → Prop
  | .var _ => True
  | .integer _ => True
  | .add left right => left.DefinedAt values ∧ right.DefinedAt values
  | .neg argument => argument.DefinedAt values
  | .mul left right => left.DefinedAt values ∧ right.DefinedAt values
  | .inv argument => argument.DefinedAt values ∧ argument.eval values ≠ 0

@[simp] theorem definedAt_var {arity : ℕ} (values : Fin arity → ℂ) (i) :
    (var i).DefinedAt values := trivial
@[simp] theorem definedAt_integer {arity : ℕ} (values : Fin arity → ℂ) (z : ℤ) :
    (integer z : Expr arity).DefinedAt values := trivial
@[simp] theorem definedAt_ofNat {arity : ℕ} (values : Fin arity → ℂ) (n : ℕ) :
    (OfNat.ofNat n : Expr arity).DefinedAt values := trivial
@[simp] theorem definedAt_add {arity : ℕ} (values : Fin arity → ℂ) (x y) :
    (x + y : Expr arity).DefinedAt values ↔ x.DefinedAt values ∧ y.DefinedAt values := Iff.rfl
@[simp] theorem definedAt_neg {arity : ℕ} (values : Fin arity → ℂ) (x) :
    (-x : Expr arity).DefinedAt values ↔ x.DefinedAt values := Iff.rfl
@[simp] theorem definedAt_sub {arity : ℕ} (values : Fin arity → ℂ) (x y) :
    (x - y : Expr arity).DefinedAt values ↔ x.DefinedAt values ∧ y.DefinedAt values := Iff.rfl
@[simp] theorem definedAt_mul {arity : ℕ} (values : Fin arity → ℂ) (x y) :
    (x * y : Expr arity).DefinedAt values ↔ x.DefinedAt values ∧ y.DefinedAt values := Iff.rfl
@[simp] theorem definedAt_inv {arity : ℕ} (values : Fin arity → ℂ) (x) :
    (x⁻¹ : Expr arity).DefinedAt values ↔
      x.DefinedAt values ∧ x.eval values ≠ 0 := Iff.rfl
@[simp] theorem definedAt_div {arity : ℕ} (values : Fin arity → ℂ) (x y) :
    (x / y : Expr arity).DefinedAt values ↔
      x.DefinedAt values ∧ y.DefinedAt values ∧ y.eval values ≠ 0 := Iff.rfl
@[simp] theorem definedAt_pow_succ {arity : ℕ} (values : Fin arity → ℂ)
    (x : Expr arity) (n : ℕ) : (x ^ (n + 1)).DefinedAt values ↔ x.DefinedAt values := by
  induction n with
  | zero =>
      change (True ∧ x.DefinedAt values) ↔ x.DefinedAt values
      simp
  | succ n ih =>
      change ((x ^ (n + 1)).DefinedAt values ∧ x.DefinedAt values) ↔
        x.DefinedAt values
      simp [ih]

def directional {arity : ℕ} (velocity : Fin arity → Expr arity) :
    Expr arity → Expr arity
  | .var index => velocity index
  | .integer _ => 0
  | .add left right => left.directional velocity + right.directional velocity
  | .neg argument => -(argument.directional velocity)
  | .mul left right =>
      left.directional velocity * right + left * right.directional velocity
  | .inv argument => -(argument.directional velocity * argument⁻¹ * argument⁻¹)

theorem directional_definedAt {arity : ℕ} {values : Fin arity → ℂ}
    {velocity : Fin arity → Expr arity} {expression : Expr arity}
    (hexpression : expression.DefinedAt values)
    (hvelocity : ∀ i, (velocity i).DefinedAt values) :
    (expression.directional velocity).DefinedAt values := by
  induction expression with
  | var i => exact hvelocity i
  | integer _ => trivial
  | add left right ihLeft ihRight =>
      exact ⟨ihLeft hexpression.1, ihRight hexpression.2⟩
  | neg argument ih => exact ih hexpression
  | mul left right ihLeft ihRight =>
      exact ⟨⟨ihLeft hexpression.1, hexpression.2⟩,
        ⟨hexpression.1, ihRight hexpression.2⟩⟩
  | inv argument ih =>
      exact ⟨⟨ih hexpression.1, hexpression⟩, hexpression⟩

def directionalEval {arity : ℕ} (values velocity : Fin arity → ℂ) :
    Expr arity → ℂ
  | .var index => velocity index
  | .integer _ => 0
  | .add left right => left.directionalEval values velocity +
      right.directionalEval values velocity
  | .neg argument => -argument.directionalEval values velocity
  | .mul left right =>
      left.directionalEval values velocity * right.eval values +
        left.eval values * right.directionalEval values velocity
  | .inv argument =>
      -(argument.directionalEval values velocity * (argument.eval values)⁻¹ *
        (argument.eval values)⁻¹)

@[simp] theorem directionalEval_eq_eval_directional
    {arity : ℕ} (values : Fin arity → ℂ) (velocity : Fin arity → Expr arity)
    (expression : Expr arity) :
    expression.directionalEval values (fun i ↦ (velocity i).eval values) =
      (expression.directional velocity).eval values := by
  induction expression with
  | var i => rfl
  | integer n => norm_num [directionalEval, directional, eval]
  | add x y ihx ihy => simp [directionalEval, directional, eval, ihx, ihy]
  | neg x ih => simp [directionalEval, directional, eval, ih]
  | mul x y ihx ihy => simp [directionalEval, directional, eval, ihx, ihy]
  | inv x ih => simp [directionalEval, directional, eval, ih]

/-- The second directional value, represented recursively rather than by constructing the
usually much larger twice-differentiated expression tree.  `velocity` is the first derivative of
the input paths and `acceleration` their second derivative. -/
def secondDirectionalEval {arity : ℕ}
    (values velocity acceleration : Fin arity → ℂ) : Expr arity → ℂ
  | .var index => acceleration index
  | .integer _ => 0
  | .add left right =>
      left.secondDirectionalEval values velocity acceleration +
        right.secondDirectionalEval values velocity acceleration
  | .neg argument => -argument.secondDirectionalEval values velocity acceleration
  | .mul left right =>
      left.secondDirectionalEval values velocity acceleration * right.eval values +
        left.directionalEval values velocity * right.directionalEval values velocity +
        left.directionalEval values velocity * right.directionalEval values velocity +
        left.eval values * right.secondDirectionalEval values velocity acceleration
  | .inv argument =>
      2 * argument.directionalEval values velocity ^ 2 *
          (argument.eval values)⁻¹ ^ 3 -
        argument.secondDirectionalEval values velocity acceleration *
          (argument.eval values)⁻¹ ^ 2

/-- Recursive second directional evaluation agrees with differentiating the symbolic first
directional expression.  This lets interval jets and analytic chain rules share a value without
forcing Lean to elaborate the expanded derivative tree. -/
theorem secondDirectionalEval_eq_directional
    {arity : ℕ} (values : Fin arity → ℂ) (velocity : Fin arity → Expr arity)
    (expression : Expr arity) :
    expression.secondDirectionalEval values (fun i ↦ (velocity i).eval values)
        (fun i ↦ (velocity i).directionalEval values
          (fun j ↦ (velocity j).eval values)) =
      (expression.directional velocity).directionalEval values
        (fun i ↦ (velocity i).eval values) := by
  induction expression with
  | var i => rfl
  | integer n => norm_num [secondDirectionalEval, directionalEval, directional, eval]
  | add x y ihx ihy =>
      simp only [secondDirectionalEval, directionalEval, directional, eval, ihx, ihy]
  | neg x ih => simp only [secondDirectionalEval, directionalEval, directional, eval, ih]
  | mul x y ihx ihy =>
      simp only [secondDirectionalEval, directionalEval, directional, eval, ihx, ihy]
      rw [← directionalEval_eq_eval_directional values velocity x,
        ← directionalEval_eq_eval_directional values velocity y]
      ring
  | inv x ih =>
      simp only [secondDirectionalEval, directionalEval, directional, eval, ih]
      rw [← directionalEval_eq_eval_directional values velocity x]
      ring

def smartAdd {arity : ℕ} (x y : Expr arity) : Expr arity :=
  if x = .integer 0 then y else if y = .integer 0 then x else .add x y

def smartNeg {arity : ℕ} (x : Expr arity) : Expr arity :=
  match x with
  | .neg y => y
  | x => .neg x

def smartMul {arity : ℕ} (x y : Expr arity) : Expr arity :=
  if x = .integer 0 ∨ y = .integer 0 then .integer 0
  else .mul x y

def smartInv {arity : ℕ} (x : Expr arity) : Expr arity :=
  match x with
  | .inv y => y
  | x => .inv x

def normalize {arity : ℕ} : Expr arity → Expr arity
  | .var i => .var i
  | .integer n => .integer n
  | .add x y => smartAdd x.normalize y.normalize
  | .neg x => smartNeg x.normalize
  | .mul x y => smartMul x.normalize y.normalize
  | .inv x => smartInv x.normalize

def nodeCount {arity : ℕ} : Expr arity → ℕ
  | .var _ | .integer _ => 1
  | .neg x | .inv x => x.nodeCount + 1
  | .add x y | .mul x y => x.nodeCount + y.nodeCount + 1

@[simp] theorem eval_var {arity : ℕ} (values : Fin arity → ℂ) (i) :
    (var i).eval values = values i := rfl
@[simp] theorem eval_integer {arity : ℕ} (values : Fin arity → ℂ) (z : ℤ) :
    (integer z : Expr arity).eval values = z := rfl
@[simp] theorem eval_ofNat {arity : ℕ} (values : Fin arity → ℂ) (n : ℕ) :
    (OfNat.ofNat n : Expr arity).eval values = n := rfl
@[simp] theorem eval_add {arity : ℕ} (values : Fin arity → ℂ) (x y) :
    (x + y : Expr arity).eval values = x.eval values + y.eval values := rfl
@[simp] theorem eval_neg {arity : ℕ} (values : Fin arity → ℂ) (x) :
    (-x : Expr arity).eval values = -x.eval values := rfl
@[simp] theorem eval_sub {arity : ℕ} (values : Fin arity → ℂ) (x y) :
    (x - y : Expr arity).eval values = x.eval values - y.eval values := rfl
@[simp] theorem eval_mul {arity : ℕ} (values : Fin arity → ℂ) (x y) :
    (x * y : Expr arity).eval values = x.eval values * y.eval values := rfl
@[simp] theorem eval_inv {arity : ℕ} (values : Fin arity → ℂ) (x) :
    (x⁻¹ : Expr arity).eval values = (x.eval values)⁻¹ := rfl
@[simp] theorem eval_div {arity : ℕ} (values : Fin arity → ℂ) (x y) :
    (x / y : Expr arity).eval values = x.eval values / y.eval values := rfl
@[simp] theorem eval_pow {arity : ℕ} (values : Fin arity → ℂ) (x : Expr arity) (n : ℕ) :
    (x ^ n).eval values = (x.eval values) ^ n := by
  induction n with
  | zero =>
      change ((1 : ℤ) : ℂ) = 1
      norm_num
  | succ n ih =>
      change (x.npow n).eval values = (x.eval values) ^ n at ih
      change (x.npow n).eval values * x.eval values = (x.eval values) ^ (n + 1)
      rw [ih, pow_succ]

theorem eval_normalize {arity : ℕ} (values : Fin arity → ℂ) (x : Expr arity) :
    x.normalize.eval values = x.eval values := by
  induction x with
  | var i => rfl
  | integer n => rfl
  | add x y ihx ihy =>
      simp only [normalize]
      by_cases hx : x.normalize = .integer 0 <;>
        by_cases hy : y.normalize = .integer 0 <;>
          simp_all [smartAdd, eval]
  | neg x ih =>
      simp only [normalize]
      generalize hx : x.normalize = xn at ih ⊢
      cases xn <;> simp_all [smartNeg, eval]
      all_goals rw [← ih]; simp
  | mul x y ihx ihy =>
      simp only [normalize]
      by_cases hzero : x.normalize = .integer 0 ∨ y.normalize = .integer 0
      · rcases hzero with hx | hy
        · have hxEval : x.eval values = 0 := by
            rw [← ihx, hx]
            norm_num [eval]
          simp [smartMul, hx, eval, hxEval]
        · have hyEval : y.eval values = 0 := by
            rw [← ihy, hy]
            norm_num [eval]
          simp [smartMul, hy, eval, hyEval]
      · simp [smartMul, hzero, eval, ihx, ihy]
  | inv x ih =>
      simp only [normalize]
      generalize hx : x.normalize = xn at ih ⊢
      cases xn <;> simp_all [smartInv, eval]
      all_goals rw [← ih]; simp

theorem hasDerivAt_eval
    {arity : ℕ} {paths : Fin arity → ℝ → ℂ}
    {velocity : Fin arity → Expr arity} {s : ℝ}
    (expression : Expr arity)
    (hdefined : expression.DefinedAt (fun i ↦ paths i s))
    (hpaths : ∀ i, HasDerivAt (paths i)
      ((velocity i).eval (fun j ↦ paths j s)) s) :
    HasDerivAt (fun x ↦ expression.eval (fun i ↦ paths i x))
      ((expression.directional velocity).eval (fun i ↦ paths i s)) s := by
  induction expression with
  | var i => exact hpaths i
  | integer z =>
      apply (hasDerivAt_const s (z : ℂ)).congr_deriv
      norm_num [eval, directional]
  | add left right ihLeft ihRight =>
      exact (ihLeft hdefined.1).add (ihRight hdefined.2)
  | neg argument ih => exact (ih hdefined).neg
  | mul left right ihLeft ihRight => exact (ihLeft hdefined.1).mul (ihRight hdefined.2)
  | inv argument ih =>
      apply ((ih hdefined.1).inv hdefined.2).congr_deriv
      simp [directional]
      ring

/-- Semantic form of `hasDerivAt_eval`, useful when the input velocities are values rather than
symbolic expressions. -/
theorem hasDerivAt_eval_semantic
    {arity : ℕ} {paths : Fin arity → ℝ → ℂ} {velocity : Fin arity → ℂ} {s : ℝ}
    (expression : Expr arity)
    (hdefined : expression.DefinedAt (fun i ↦ paths i s))
    (hpaths : ∀ i, HasDerivAt (paths i) (velocity i) s) :
    HasDerivAt (fun x ↦ expression.eval (fun i ↦ paths i x))
      (expression.directionalEval (fun i ↦ paths i s) velocity) s := by
  induction expression with
  | var i => exact hpaths i
  | integer z => simpa [eval, directionalEval] using (hasDerivAt_const s (z : ℂ))
  | add left right ihLeft ihRight => exact (ihLeft hdefined.1).add (ihRight hdefined.2)
  | neg argument ih => exact (ih hdefined).neg
  | mul left right ihLeft ihRight => exact (ihLeft hdefined.1).mul (ihRight hdefined.2)
  | inv argument ih =>
      apply ((ih hdefined.1).inv hdefined.2).congr_deriv
      simp [directionalEval]
      ring

/-- Chain rule for a first directional value, with the second derivative kept in the compact
recursive representation `secondDirectionalEval`. -/
theorem hasDerivAt_directionalEval
    {arity : ℕ} {paths velocityPaths : Fin arity → ℝ → ℂ}
    {velocity acceleration : Fin arity → ℂ} {s : ℝ}
    (expression : Expr arity)
    (hdefined : expression.DefinedAt (fun i ↦ paths i s))
    (hpaths : ∀ i, HasDerivAt (paths i) (velocity i) s)
    (hvelocityPaths : ∀ i, HasDerivAt (velocityPaths i) (acceleration i) s)
    (hvelocityAt : ∀ i, velocityPaths i s = velocity i) :
    HasDerivAt
      (fun x ↦ expression.directionalEval (fun i ↦ paths i x)
        (fun i ↦ velocityPaths i x))
      (expression.secondDirectionalEval (fun i ↦ paths i s) velocity acceleration) s := by
  induction expression with
  | var i => simpa [directionalEval, secondDirectionalEval] using hvelocityPaths i
  | integer n => simpa [directionalEval, secondDirectionalEval] using
      (hasDerivAt_const s (0 : ℂ))
  | add left right ihLeft ihRight =>
      convert (ihLeft hdefined.1).add (ihRight hdefined.2) using 1 <;> rfl
  | neg argument ih =>
      convert (ih hdefined).neg using 1 <;> rfl
  | mul left right ihLeft ihRight =>
      have hleft' := hasDerivAt_eval_semantic left hdefined.1 hpaths
      have hright' := hasDerivAt_eval_semantic right hdefined.2 hpaths
      have h := ((ihLeft hdefined.1).mul hright').add (hleft'.mul (ihRight hdefined.2))
      change HasDerivAt
        (fun x ↦ left.directionalEval (fun i ↦ paths i x)
            (fun i ↦ velocityPaths i x) * right.eval (fun i ↦ paths i x) +
          left.eval (fun i ↦ paths i x) * right.directionalEval
            (fun i ↦ paths i x) (fun i ↦ velocityPaths i x))
        (left.secondDirectionalEval (fun i ↦ paths i s) velocity acceleration *
            right.eval (fun i ↦ paths i s) +
          left.directionalEval (fun i ↦ paths i s) velocity *
              right.directionalEval (fun i ↦ paths i s) velocity +
          left.directionalEval (fun i ↦ paths i s) velocity *
              right.directionalEval (fun i ↦ paths i s) velocity +
          left.eval (fun i ↦ paths i s) *
            right.secondDirectionalEval (fun i ↦ paths i s) velocity acceleration) s
      apply h.congr_deriv
      have hv : (fun i ↦ velocityPaths i s) = velocity := funext hvelocityAt
      rw [hv]
      ring
  | inv argument ih =>
      have harg := hasDerivAt_eval_semantic argument hdefined.1 hpaths
      have hinv := harg.inv hdefined.2
      have h := (((ih hdefined.1).mul hinv).mul hinv).neg
      change HasDerivAt
        (fun x ↦ -(argument.directionalEval (fun i ↦ paths i x)
            (fun i ↦ velocityPaths i x) *
          (argument.eval (fun i ↦ paths i x))⁻¹ *
          (argument.eval (fun i ↦ paths i x))⁻¹))
        (2 * argument.directionalEval (fun i ↦ paths i s) velocity ^ 2 *
            (argument.eval (fun i ↦ paths i s))⁻¹ ^ 3 -
          argument.secondDirectionalEval (fun i ↦ paths i s) velocity acceleration *
            (argument.eval (fun i ↦ paths i s))⁻¹ ^ 2) s
      apply h.congr_deriv
      have hv : (fun i ↦ velocityPaths i s) = velocity := funext hvelocityAt
      rw [hv]
      simp only [Pi.inv_apply, Pi.mul_apply]
      simp_rw [hvelocityAt]
      ring

-- Downstream certificate files must use the two bridge theorems above rather than unfold the
-- recursive value into a many-thousand-node term during definitional equality checking.
/-- A second chain-rule step without materializing the (often very large) domain proof for the
symbolic directional derivative.  Keeping this wrapper polymorphic in `expression` is important
for generated certificates: elaboration then retains `directional_definedAt` as one theorem
application instead of reducing it through the whole derivative syntax tree. -/
theorem hasDerivAt_directional_eval
    {arity : ℕ} {paths : Fin arity → ℝ → ℂ}
    {velocity : Fin arity → Expr arity} {s : ℝ}
    (expression : Expr arity)
    (hdefined : expression.DefinedAt (fun i ↦ paths i s))
    (hvelocityDefined : ∀ i, (velocity i).DefinedAt (fun j ↦ paths j s))
    (hpaths : ∀ i, HasDerivAt (paths i)
      ((velocity i).eval (fun j ↦ paths j s)) s) :
    HasDerivAt
      (fun x ↦ (expression.directional velocity).eval (fun i ↦ paths i x))
      (((expression.directional velocity).directional velocity).eval
        (fun i ↦ paths i s)) s := by
  exact hasDerivAt_eval (expression.directional velocity)
    (directional_definedAt hdefined hvelocityDefined) hpaths

/-! ## Signed-dyadic evaluator -/

abbrev Rectangle (precision : ℕ) := ChapterVISignedDyadicComplexRectangle precision

inductive Derivation {arity precision : ℕ} (boxes : Fin arity → Rectangle precision) :
    Expr arity → Rectangle precision → Type
  | var (index : Fin arity) : Derivation boxes (.var index) (boxes index)
  | integer (value : ℤ) : Derivation boxes (.integer value)
      (ChapterVISignedDyadicComplexRectangle.pointInt precision value)
  | add {left right leftOutput rightOutput}
      (leftTrace : Derivation boxes left leftOutput)
      (rightTrace : Derivation boxes right rightOutput) :
      Derivation boxes (.add left right) (leftOutput.add rightOutput)
  | neg {argument output} (argumentTrace : Derivation boxes argument output) :
      Derivation boxes (.neg argument) output.neg
  | mul {left right leftOutput rightOutput}
      (leftTrace : Derivation boxes left leftOutput)
      (rightTrace : Derivation boxes right rightOutput)
      (operation : ChapterVISignedDyadicComplexRectangle.MulTrace leftOutput rightOutput) :
      Derivation boxes (.mul left right) operation.output
  | inv {argument output} (argumentTrace : Derivation boxes argument output)
      (operation : ChapterVISignedDyadicComplexRectangle.InvTrace output) :
      Derivation boxes (.inv argument) operation.output

structure Trace {arity precision : ℕ} (boxes : Fin arity → Rectangle precision)
    (expression : Expr arity) where
  output : Rectangle precision
  derivation : Derivation boxes expression output

def Derivation.operations {arity precision : ℕ} {boxes : Fin arity → Rectangle precision} :
    {expression : Expr arity} → {output : Rectangle precision} →
      Derivation boxes expression output → List (DyadicOperation precision)
  | _, _, .var _ => []
  | _, _, .integer _ => []
  | _, _, .add leftTrace rightTrace => leftTrace.operations ++ rightTrace.operations
  | _, _, .neg argumentTrace => argumentTrace.operations
  | _, _, .mul leftTrace rightTrace operation =>
      leftTrace.operations ++ rightTrace.operations ++ operation.operations
  | _, _, .inv argumentTrace operation => argumentTrace.operations ++ operation.operations

def Trace.operations {arity precision : ℕ} {boxes : Fin arity → Rectangle precision}
    {expression : Expr arity} (trace : Trace boxes expression) : List (DyadicOperation precision) :=
  trace.derivation.operations

def proposeTrace {arity precision : ℕ} (boxes : Fin arity → Rectangle precision) :
    (expression : Expr arity) → Trace boxes expression
  | .var index => ⟨boxes index, .var index⟩
  | .integer value => ⟨ChapterVISignedDyadicComplexRectangle.pointInt precision value,
      .integer value⟩
  | .add left right => by
      let leftTrace := proposeTrace boxes left
      let rightTrace := proposeTrace boxes right
      exact ⟨leftTrace.output.add rightTrace.output,
        .add leftTrace.derivation rightTrace.derivation⟩
  | .neg argument => by
      let argumentTrace := proposeTrace boxes argument
      exact ⟨argumentTrace.output.neg, .neg argumentTrace.derivation⟩
  | .mul left right => by
      let leftTrace := proposeTrace boxes left
      let rightTrace := proposeTrace boxes right
      let operation := ChapterVILeanCompCertProposals.mulTrace
        leftTrace.output rightTrace.output
      exact ⟨operation.output, .mul leftTrace.derivation rightTrace.derivation operation⟩
  | .inv argument => by
      let argumentTrace := proposeTrace boxes argument
      let operation := ChapterVILeanCompCertProposals.invTrace argumentTrace.output
      exact ⟨operation.output, .inv argumentTrace.derivation operation⟩

def TraceValid {arity precision : ℕ} (boxes : Fin arity → Rectangle precision) :
    Expr arity → Bool
  | .var _ | .integer _ => true
  | .add left right | .mul left right => TraceValid boxes left && TraceValid boxes right
  | .neg argument => TraceValid boxes argument
  | .inv argument =>
      let argumentTrace := proposeTrace boxes argument
      TraceValid boxes argument &&
        decide (0 < (ChapterVILeanCompCertProposals.invTrace argumentTrace.output).normSq.lower)

theorem proposeTrace_operations_sound
    {arity precision : ℕ} (boxes : Fin arity → Rectangle precision) (expression : Expr arity)
    (hvalid : TraceValid boxes expression = true) :
    ∀ operation ∈ (proposeTrace boxes expression).operations, operation.Sound := by
  induction expression with
  | var i => simp [proposeTrace, Trace.operations, Derivation.operations]
  | integer z => simp [proposeTrace, Trace.operations, Derivation.operations]
  | add left right ihLeft ihRight =>
      simp only [TraceValid, Bool.and_eq_true] at hvalid
      intro operation hoperation
      simp only [proposeTrace, Trace.operations, Derivation.operations] at hoperation
      rcases List.mem_append.mp hoperation with hleft | hright
      · exact ihLeft hvalid.1 operation hleft
      · exact ihRight hvalid.2 operation hright
  | neg argument ih =>
      simpa [proposeTrace, Trace.operations, Derivation.operations] using ih hvalid
  | mul left right ihLeft ihRight =>
      simp only [TraceValid, Bool.and_eq_true] at hvalid
      intro operation hoperation
      simp only [proposeTrace, Trace.operations, Derivation.operations] at hoperation
      rcases List.mem_append.mp hoperation with hchildren | hmul
      rcases List.mem_append.mp hchildren with hleft | hright
      · exact ihLeft hvalid.1 operation hleft
      · exact ihRight hvalid.2 operation hright
      · exact ChapterVILeanCompCertProposals.mulTrace_operations_sound _ _ operation hmul
  | inv argument ih =>
      simp only [TraceValid, Bool.and_eq_true, decide_eq_true_eq] at hvalid
      intro operation hoperation
      simp only [proposeTrace, Trace.operations, Derivation.operations] at hoperation
      rcases List.mem_append.mp hoperation with hargument | hinv
      · exact ih hvalid.1 operation hargument
      · exact ChapterVILeanCompCertProposals.invTrace_operations_sound _ hvalid.2 operation hinv

theorem Derivation.output_contains_of_allSound
    {arity precision : ℕ} {boxes : Fin arity → Rectangle precision}
    {expression : Expr arity} {output : Rectangle precision}
    (trace : Derivation boxes expression output)
    (hall : ∀ operation ∈ trace.operations, operation.Sound)
    {values : Fin arity → ℂ} (hvalues : ∀ i, (boxes i).Contains (values i)) :
    output.Contains (expression.eval values) := by
  induction trace with
  | var index => exact hvalues index
  | integer value => exact ChapterVISignedDyadicComplexRectangle.pointInt_contains precision value
  | add leftTrace rightTrace ihLeft ihRight =>
      exact ChapterVISignedDyadicComplexRectangle.add_contains
        (ihLeft (by intro op hop; exact hall op (by simp [Derivation.operations, hop])))
        (ihRight (by intro op hop; exact hall op (by simp [Derivation.operations, hop])))
  | neg argumentTrace ih =>
      exact ChapterVISignedDyadicComplexRectangle.neg_contains
        (ih (by intro op hop; exact hall op (by simp [Derivation.operations, hop])))
  | mul leftTrace rightTrace operation ihLeft ihRight =>
      exact operation.output_contains_mul_of_allSound
        (by intro op hop; exact hall op (by simp [Derivation.operations, hop]))
        (ihLeft (by intro op hop; exact hall op (by simp [Derivation.operations, hop])))
        (ihRight (by intro op hop; exact hall op (by simp [Derivation.operations, hop])))
  | inv argumentTrace operation ih =>
      exact operation.output_contains_inv_of_allSound
        (by intro op hop; exact hall op (by simp [Derivation.operations, hop]))
        (ih (by intro op hop; exact hall op (by simp [Derivation.operations, hop])))

theorem Trace.output_contains_of_allSound
    {arity precision : ℕ} {boxes : Fin arity → Rectangle precision}
    {expression : Expr arity} (trace : Trace boxes expression)
    (hall : ∀ operation ∈ trace.operations, operation.Sound)
    {values : Fin arity → ℂ} (hvalues : ∀ i, (boxes i).Contains (values i)) :
    trace.output.Contains (expression.eval values) :=
  trace.derivation.output_contains_of_allSound hall hvalues

/-! ## Forward directional jets

Unlike expanding `directional` into a new expression, this evaluator visits every node of the
original expression once.  It carries the value and directional derivative together and reuses
the already-computed child outputs in the product and reciprocal rules. -/

inductive JetDerivation {arity precision : ℕ}
    (boxes : Fin arity → Rectangle precision)
    (velocityOutputs : Fin arity → Rectangle precision) :
    Expr arity → Rectangle precision → Rectangle precision → Type
  | var (index : Fin arity) :
      JetDerivation boxes velocityOutputs (.var index) (boxes index) (velocityOutputs index)
  | integer (value : ℤ) :
      JetDerivation boxes velocityOutputs (.integer value)
        (ChapterVISignedDyadicComplexRectangle.pointInt precision value)
        (ChapterVISignedDyadicComplexRectangle.pointInt precision 0)
  | add {left right leftValue rightValue leftDerivative rightDerivative}
      (leftTrace : JetDerivation boxes velocityOutputs left leftValue leftDerivative)
      (rightTrace : JetDerivation boxes velocityOutputs right rightValue rightDerivative) :
      JetDerivation boxes velocityOutputs (.add left right)
        (leftValue.add rightValue) (leftDerivative.add rightDerivative)
  | neg {argument value derivative}
      (argumentTrace : JetDerivation boxes velocityOutputs argument value derivative) :
      JetDerivation boxes velocityOutputs (.neg argument) value.neg derivative.neg
  | mul {left right leftValue rightValue leftDerivative rightDerivative}
      (leftTrace : JetDerivation boxes velocityOutputs left leftValue leftDerivative)
      (rightTrace : JetDerivation boxes velocityOutputs right rightValue rightDerivative)
      (valueOperation : ChapterVISignedDyadicComplexRectangle.MulTrace leftValue rightValue)
      (leftOperation : ChapterVISignedDyadicComplexRectangle.MulTrace leftDerivative rightValue)
      (rightOperation : ChapterVISignedDyadicComplexRectangle.MulTrace leftValue rightDerivative) :
      JetDerivation boxes velocityOutputs (.mul left right) valueOperation.output
        (leftOperation.output.add rightOperation.output)
  | inv {argument value derivative}
      (argumentTrace : JetDerivation boxes velocityOutputs argument value derivative)
      (valueOperation : ChapterVISignedDyadicComplexRectangle.InvTrace value)
      (firstOperation : ChapterVISignedDyadicComplexRectangle.MulTrace
        derivative valueOperation.output)
      (secondOperation : ChapterVISignedDyadicComplexRectangle.MulTrace
        firstOperation.output valueOperation.output) :
      JetDerivation boxes velocityOutputs (.inv argument) valueOperation.output
        secondOperation.output.neg

structure JetTrace {arity precision : ℕ} (boxes : Fin arity → Rectangle precision)
    (velocityOutputs : Fin arity → Rectangle precision) (expression : Expr arity) where
  value : Rectangle precision
  derivative : Rectangle precision
  derivation : JetDerivation boxes velocityOutputs expression value derivative

def JetDerivation.operations {arity precision : ℕ}
    {boxes : Fin arity → Rectangle precision}
    {velocityOutputs : Fin arity → Rectangle precision} :
    {expression : Expr arity} → {value derivative : Rectangle precision} →
      JetDerivation boxes velocityOutputs expression value derivative →
      List (DyadicOperation precision)
  | _, _, _, .var _ => []
  | _, _, _, .integer _ => []
  | _, _, _, .add leftTrace rightTrace =>
      leftTrace.operations ++ rightTrace.operations
  | _, _, _, .neg argumentTrace => argumentTrace.operations
  | _, _, _, .mul leftTrace rightTrace valueOperation leftOperation rightOperation =>
      leftTrace.operations ++ rightTrace.operations ++ valueOperation.operations ++
        leftOperation.operations ++ rightOperation.operations
  | _, _, _, .inv argumentTrace valueOperation firstOperation secondOperation =>
      argumentTrace.operations ++ valueOperation.operations ++ firstOperation.operations ++
        secondOperation.operations

def JetTrace.operations {arity precision : ℕ}
    {boxes : Fin arity → Rectangle precision}
    {velocityOutputs : Fin arity → Rectangle precision} {expression : Expr arity}
    (trace : JetTrace boxes velocityOutputs expression) : List (DyadicOperation precision) :=
  trace.derivation.operations

def proposeJetTrace {arity precision : ℕ} (boxes : Fin arity → Rectangle precision)
    (velocityOutputs : Fin arity → Rectangle precision) :
    (expression : Expr arity) → JetTrace boxes velocityOutputs expression
  | .var index => ⟨boxes index, velocityOutputs index, .var index⟩
  | .integer value =>
      ⟨ChapterVISignedDyadicComplexRectangle.pointInt precision value,
        ChapterVISignedDyadicComplexRectangle.pointInt precision 0, .integer value⟩
  | .add left right => by
      let leftTrace := proposeJetTrace boxes velocityOutputs left
      let rightTrace := proposeJetTrace boxes velocityOutputs right
      exact ⟨leftTrace.value.add rightTrace.value,
        leftTrace.derivative.add rightTrace.derivative,
        .add leftTrace.derivation rightTrace.derivation⟩
  | .neg argument => by
      let argumentTrace := proposeJetTrace boxes velocityOutputs argument
      exact ⟨argumentTrace.value.neg, argumentTrace.derivative.neg,
        .neg argumentTrace.derivation⟩
  | .mul left right => by
      let leftTrace := proposeJetTrace boxes velocityOutputs left
      let rightTrace := proposeJetTrace boxes velocityOutputs right
      let valueOperation := ChapterVILeanCompCertProposals.mulTrace
        leftTrace.value rightTrace.value
      let leftOperation := ChapterVILeanCompCertProposals.mulTrace
        leftTrace.derivative rightTrace.value
      let rightOperation := ChapterVILeanCompCertProposals.mulTrace
        leftTrace.value rightTrace.derivative
      exact ⟨valueOperation.output, leftOperation.output.add rightOperation.output,
        .mul leftTrace.derivation rightTrace.derivation valueOperation leftOperation
          rightOperation⟩
  | .inv argument => by
      let argumentTrace := proposeJetTrace boxes velocityOutputs argument
      let valueOperation := ChapterVILeanCompCertProposals.invTrace argumentTrace.value
      let firstOperation := ChapterVILeanCompCertProposals.mulTrace
        argumentTrace.derivative valueOperation.output
      let secondOperation := ChapterVILeanCompCertProposals.mulTrace
        firstOperation.output valueOperation.output
      exact ⟨valueOperation.output, secondOperation.output.neg,
        .inv argumentTrace.derivation valueOperation firstOperation secondOperation⟩

/-- The sole side condition for a rectangular jet trace is positivity of every reciprocal
norm-square enclosure. -/
def JetTraceValid {arity precision : ℕ} (boxes : Fin arity → Rectangle precision)
    (velocityOutputs : Fin arity → Rectangle precision) : Expr arity → Bool
  | .var _ | .integer _ => true
  | .add left right | .mul left right =>
      JetTraceValid boxes velocityOutputs left && JetTraceValid boxes velocityOutputs right
  | .neg argument => JetTraceValid boxes velocityOutputs argument
  | .inv argument =>
      let argumentTrace := proposeJetTrace boxes velocityOutputs argument
      JetTraceValid boxes velocityOutputs argument &&
        decide (0 < (ChapterVILeanCompCertProposals.invTrace argumentTrace.value).normSq.lower)

theorem proposeJetTrace_operations_sound
    {arity precision : ℕ} (boxes : Fin arity → Rectangle precision)
    (velocityOutputs : Fin arity → Rectangle precision) (expression : Expr arity)
    (hvalid : JetTraceValid boxes velocityOutputs expression = true) :
    ∀ operation ∈ (proposeJetTrace boxes velocityOutputs expression).operations,
      operation.Sound := by
  induction expression with
  | var i => simp [proposeJetTrace, JetTrace.operations, JetDerivation.operations]
  | integer z => simp [proposeJetTrace, JetTrace.operations, JetDerivation.operations]
  | add left right ihLeft ihRight =>
      simp only [JetTraceValid, Bool.and_eq_true] at hvalid
      intro operation hoperation
      simp only [proposeJetTrace, JetTrace.operations, JetDerivation.operations,
        ] at hoperation
      rcases List.mem_append.mp hoperation with hleft | hright
      · exact ihLeft hvalid.1 operation hleft
      · exact ihRight hvalid.2 operation hright
  | neg argument ih =>
      simpa [proposeJetTrace, JetTrace.operations, JetDerivation.operations] using ih hvalid
  | mul left right ihLeft ihRight =>
      simp only [JetTraceValid, Bool.and_eq_true] at hvalid
      intro operation hoperation
      simp only [proposeJetTrace, JetTrace.operations, JetDerivation.operations,
        ] at hoperation
      rcases List.mem_append.mp hoperation with hchildren | hrightProduct
      rcases List.mem_append.mp hchildren with hchildren | hleftProduct
      rcases List.mem_append.mp hchildren with hchildren | hvalue
      rcases List.mem_append.mp hchildren with hleft | hright
      · exact ihLeft hvalid.1 operation hleft
      · exact ihRight hvalid.2 operation hright
      · exact ChapterVILeanCompCertProposals.mulTrace_operations_sound _ _ operation hvalue
      · exact ChapterVILeanCompCertProposals.mulTrace_operations_sound _ _ operation hleftProduct
      · exact ChapterVILeanCompCertProposals.mulTrace_operations_sound _ _ operation hrightProduct
  | inv argument ih =>
      simp only [JetTraceValid, Bool.and_eq_true, decide_eq_true_eq] at hvalid
      intro operation hoperation
      simp only [proposeJetTrace, JetTrace.operations, JetDerivation.operations,
        ] at hoperation
      rcases List.mem_append.mp hoperation with hchildren | hsecond
      rcases List.mem_append.mp hchildren with hchildren | hfirst
      rcases List.mem_append.mp hchildren with hargument | hvalue
      · exact ih hvalid.1 operation hargument
      · exact ChapterVILeanCompCertProposals.invTrace_operations_sound _ hvalid.2 operation hvalue
      · exact ChapterVILeanCompCertProposals.mulTrace_operations_sound _ _ operation hfirst
      · exact ChapterVILeanCompCertProposals.mulTrace_operations_sound _ _ operation hsecond

theorem JetDerivation.outputs_contain_of_allSound
    {arity precision : ℕ} {boxes : Fin arity → Rectangle precision}
    {velocityOutputs : Fin arity → Rectangle precision}
    {expression : Expr arity} {value derivative : Rectangle precision}
    (trace : JetDerivation boxes velocityOutputs expression value derivative)
    (hall : ∀ operation ∈ trace.operations, operation.Sound)
    {values velocities : Fin arity → ℂ}
    (hvalues : ∀ i, (boxes i).Contains (values i))
    (hvelocity : ∀ i, (velocityOutputs i).Contains (velocities i)) :
    value.Contains (expression.eval values) ∧
      derivative.Contains (expression.directionalEval values velocities) := by
  induction trace with
  | var index => exact ⟨hvalues index, hvelocity index⟩
  | integer constant =>
      constructor
      · exact ChapterVISignedDyadicComplexRectangle.pointInt_contains precision constant
      · change (ChapterVISignedDyadicComplexRectangle.pointInt precision 0).Contains (0 : ℂ)
        simpa only [Int.cast_zero] using
          (ChapterVISignedDyadicComplexRectangle.pointInt_contains precision (0 : ℤ))
  | add leftTrace rightTrace ihLeft ihRight =>
      have hleft := ihLeft
        (by intro op hop; exact hall op (by simp [JetDerivation.operations, hop]))
      have hright := ihRight
        (by intro op hop; exact hall op (by simp [JetDerivation.operations, hop]))
      exact ⟨ChapterVISignedDyadicComplexRectangle.add_contains hleft.1 hright.1,
        ChapterVISignedDyadicComplexRectangle.add_contains hleft.2 hright.2⟩
  | neg argumentTrace ih =>
      have hargument := ih
        (by intro op hop; exact hall op (by simp [JetDerivation.operations, hop]))
      exact ⟨ChapterVISignedDyadicComplexRectangle.neg_contains hargument.1,
        ChapterVISignedDyadicComplexRectangle.neg_contains hargument.2⟩
  | mul leftTrace rightTrace valueOperation leftOperation rightOperation ihLeft ihRight =>
      have hleft := ihLeft
        (by intro op hop; exact hall op (by simp [JetDerivation.operations, hop]))
      have hright := ihRight
        (by intro op hop; exact hall op (by simp [JetDerivation.operations, hop]))
      have hvalue := valueOperation.output_contains_mul_of_allSound
        (by intro op hop; exact hall op (by simp [JetDerivation.operations, hop]))
        hleft.1 hright.1
      have hleftProduct := leftOperation.output_contains_mul_of_allSound
        (by intro op hop; exact hall op (by simp [JetDerivation.operations, hop]))
        hleft.2 hright.1
      have hrightProduct := rightOperation.output_contains_mul_of_allSound
        (by intro op hop; exact hall op (by simp [JetDerivation.operations, hop]))
        hleft.1 hright.2
      exact ⟨hvalue,
        ChapterVISignedDyadicComplexRectangle.add_contains hleftProduct hrightProduct⟩
  | inv argumentTrace valueOperation firstOperation secondOperation ih =>
      have hargument := ih
        (by intro op hop; exact hall op (by simp [JetDerivation.operations, hop]))
      have hvalue := valueOperation.output_contains_inv_of_allSound
        (by intro op hop; exact hall op (by simp [JetDerivation.operations, hop]))
        hargument.1
      have hfirst := firstOperation.output_contains_mul_of_allSound
        (by intro op hop; exact hall op (by simp [JetDerivation.operations, hop]))
        hargument.2 hvalue
      have hsecond := secondOperation.output_contains_mul_of_allSound
        (by intro op hop; exact hall op (by simp [JetDerivation.operations, hop]))
        hfirst hvalue
      exact ⟨hvalue, ChapterVISignedDyadicComplexRectangle.neg_contains hsecond⟩

theorem JetTrace.outputs_contain_of_allSound
    {arity precision : ℕ} {boxes : Fin arity → Rectangle precision}
    {velocityOutputs : Fin arity → Rectangle precision}
    {expression : Expr arity} (trace : JetTrace boxes velocityOutputs expression)
    (hall : ∀ operation ∈ trace.operations, operation.Sound)
    {values velocities : Fin arity → ℂ}
    (hvalues : ∀ i, (boxes i).Contains (values i))
    (hvelocity : ∀ i, (velocityOutputs i).Contains (velocities i)) :
    trace.value.Contains (expression.eval values) ∧
      trace.derivative.Contains (expression.directionalEval values velocities) :=
  trace.derivation.outputs_contain_of_allSound hall hvalues hvelocity

theorem JetTrace.outputs_contain_directional_of_allSound
    {arity precision : ℕ} {boxes : Fin arity → Rectangle precision}
    {velocity : Fin arity → Expr arity}
    {velocityOutputs : Fin arity → Rectangle precision}
    {expression : Expr arity} (trace : JetTrace boxes velocityOutputs expression)
    (hall : ∀ operation ∈ trace.operations, operation.Sound)
    {values : Fin arity → ℂ} (hvalues : ∀ i, (boxes i).Contains (values i))
    (hvelocity : ∀ i, (velocityOutputs i).Contains ((velocity i).eval values)) :
    trace.value.Contains (expression.eval values) ∧
      trace.derivative.Contains ((expression.directional velocity).eval values) := by
  rw [← directionalEval_eq_eval_directional]
  exact trace.outputs_contain_of_allSound hall hvalues hvelocity

/-! ## Straight-line, shared-expression programs

An assignment stores its result in a fixed register.  Subsequent expressions refer to that
register as an ordinary variable.  This is the certificate-level common-subexpression
elimination used by the radial-tail repair. -/

structure Assignment (arity : ℕ) where
  target : Fin arity
  expression : Expr arity
  deriving DecidableEq, Repr

def Assignment.updateValues {arity : ℕ} (assignment : Assignment arity)
    (values : Fin arity → ℂ) : Fin arity → ℂ :=
  Function.update values assignment.target (assignment.expression.eval values)

def Assignment.updateVelocities {arity : ℕ} (assignment : Assignment arity)
    (values velocities : Fin arity → ℂ) : Fin arity → ℂ :=
  Function.update velocities assignment.target
    (assignment.expression.directionalEval values velocities)

def evalProgram {arity : ℕ} : List (Assignment arity) →
    (Fin arity → ℂ) → Fin arity → ℂ
  | [], values => values
  | assignment :: rest, values =>
      evalProgram rest (assignment.updateValues values)

/-- A compact, executable certificate that a program assigns consecutive registers and that
each right-hand side reads only inputs or registers assigned earlier. -/
def ProgramWellFormedFrom {arity : ℕ} : ℕ → List (Assignment arity) → Bool
  | _, [] => true
  | next, assignment :: rest =>
      (assignment.target.val == next) &&
        assignment.expression.VariablesBelow next &&
        ProgramWellFormedFrom (next + 1) rest

/-- Soundness of dependency-ordered straight-line evaluation.  If every assignment has its
claimed value in an exact reference state, execution agrees with that state on all registers
covered by the consecutive program. -/
theorem evalProgram_eq_exact_below {arity start : ℕ}
    {program : List (Assignment arity)} {values exact : Fin arity → ℂ}
    (hwell : ProgramWellFormedFrom start program = true)
    (hinput : ∀ i, i.val < start → values i = exact i)
    (hassign : ∀ assignment ∈ program,
      assignment.expression.eval exact = exact assignment.target) :
    ∀ i, i.val < start + program.length → evalProgram program values i = exact i := by
  induction program generalizing start values with
  | nil =>
      intro i hi
      simpa only [List.length_nil, Nat.add_zero, evalProgram] using hinput i hi
  | cons assignment rest ih =>
      simp only [ProgramWellFormedFrom, Bool.and_eq_true] at hwell
      rcases hwell with ⟨⟨htarget, hvariables⟩, hrest⟩
      have htargetNat : assignment.target.val = start := by
        simpa only [beq_iff_eq] using htarget
      have hexpression : assignment.expression.eval values = exact assignment.target := by
        rw [eval_eq_of_eq_below hvariables hinput, hassign assignment (by simp)]
      have hupdated : ∀ i, i.val < start + 1 →
          assignment.updateValues values i = exact i := by
        intro i hi
        by_cases hitarget : i = assignment.target
        · subst i
          simp [Assignment.updateValues, hexpression]
        · have hilower : i.val < start := by
            omega
          simp [Assignment.updateValues, Function.update, hitarget, hinput i hilower]
      intro i hi
      rw [evalProgram]
      apply ih hrest hupdated
      · intro next hnext
        exact hassign next (by simp [hnext])
      · simp only [List.length_cons] at hi
        omega

@[simp] theorem evalProgram_append {arity : ℕ}
    (first second : List (Assignment arity)) (values : Fin arity → ℂ) (i : Fin arity) :
    evalProgram (first ++ second) values i =
      evalProgram second (evalProgram first values) i := by
  induction first generalizing values with
  | nil => rfl
  | cons assignment rest ih =>
      simp only [List.cons_append, evalProgram]
      exact ih (assignment.updateValues values)

theorem evalProgram_preserves {arity : ℕ}
    (program : List (Assignment arity)) (values : Fin arity → ℂ) (i : Fin arity)
    (htarget : ∀ assignment ∈ program, assignment.target ≠ i) :
    evalProgram program values i = values i := by
  induction program generalizing values with
  | nil => rfl
  | cons assignment rest ih =>
      rw [evalProgram, ih]
      · have hne : i ≠ assignment.target :=
          fun h ↦ htarget assignment (by simp) h.symm
        simp [Assignment.updateValues, Function.update, hne]
      · intro next hnext
        exact htarget next (by simp [hnext])

def evalProgramVelocity {arity : ℕ} : List (Assignment arity) →
    (Fin arity → ℂ) → (Fin arity → ℂ) → Fin arity → ℂ
  | [], _, velocities => velocities
  | assignment :: rest, values, velocities =>
      evalProgramVelocity rest (assignment.updateValues values)
        (assignment.updateVelocities values velocities)

inductive ProgramDerivation {arity precision : ℕ} :
    (Fin arity → Rectangle precision) → List (Assignment arity) →
      (Fin arity → Rectangle precision) → Type
  | nil (boxes) : ProgramDerivation boxes [] boxes
  | cons {boxes outputBoxes : Fin arity → Rectangle precision}
      {assignment : Assignment arity} {rest : List (Assignment arity)}
      {assignmentOutput : Rectangle precision}
      (head : Derivation boxes assignment.expression assignmentOutput)
      (tail : ProgramDerivation
        (Function.update boxes assignment.target assignmentOutput) rest outputBoxes) :
      ProgramDerivation boxes (assignment :: rest) outputBoxes

structure ProgramTrace {arity precision : ℕ} (boxes : Fin arity → Rectangle precision)
    (program : List (Assignment arity)) where
  outputBoxes : Fin arity → Rectangle precision
  derivation : ProgramDerivation boxes program outputBoxes

def ProgramDerivation.operations {arity precision : ℕ} :
    {boxes outputBoxes : Fin arity → Rectangle precision} →
      {program : List (Assignment arity)} →
      ProgramDerivation boxes program outputBoxes → List (DyadicOperation precision)
  | _, _, _, .nil _ => []
  | _, _, _, .cons head tail => head.operations ++ tail.operations

def ProgramTrace.operations {arity precision : ℕ}
    {boxes : Fin arity → Rectangle precision} {program : List (Assignment arity)}
    (trace : ProgramTrace boxes program) : List (DyadicOperation precision) :=
  trace.derivation.operations

def proposeProgramTrace {arity precision : ℕ}
    (boxes : Fin arity → Rectangle precision) :
    (program : List (Assignment arity)) → ProgramTrace boxes program
  | [] => ⟨boxes, .nil boxes⟩
  | assignment :: rest => by
      let head := proposeTrace boxes assignment.expression
      let tail := proposeProgramTrace
        (Function.update boxes assignment.target head.output) rest
      exact ⟨tail.outputBoxes, .cons head.derivation tail.derivation⟩

theorem ProgramDerivation.outputs_contain_of_allSound
    {arity precision : ℕ} {boxes outputBoxes : Fin arity → Rectangle precision}
    {program : List (Assignment arity)}
    (trace : ProgramDerivation boxes program outputBoxes)
    (hall : ∀ operation ∈ trace.operations, operation.Sound)
    {values : Fin arity → ℂ} (hvalues : ∀ i, (boxes i).Contains (values i)) :
    ∀ i, (outputBoxes i).Contains (evalProgram program values i) := by
  induction trace generalizing values with
  | nil boxes => exact hvalues
  | @cons boxes outputBoxes assignment rest assignmentOutput head tail ih =>
      have hhead : assignmentOutput.Contains (assignment.expression.eval values) :=
        head.output_contains_of_allSound
          (by intro op hop; exact hall op (by simp [ProgramDerivation.operations, hop]))
          hvalues
      have hupdated : ∀ i,
          (Function.update boxes assignment.target assignmentOutput i).Contains
            (assignment.updateValues values i) := by
        intro i
        by_cases hi : i = assignment.target
        · subst i
          simpa [Assignment.updateValues] using hhead
        · simpa [Assignment.updateValues, Function.update, hi] using hvalues i
      exact ih
        (by intro op hop; exact hall op (by simp [ProgramDerivation.operations, hop]))
        hupdated

theorem ProgramTrace.outputs_contain_of_allSound
    {arity precision : ℕ} {boxes : Fin arity → Rectangle precision}
    {program : List (Assignment arity)} (trace : ProgramTrace boxes program)
    (hall : ∀ operation ∈ trace.operations, operation.Sound)
    {values : Fin arity → ℂ} (hvalues : ∀ i, (boxes i).Contains (values i)) :
    ∀ i, (trace.outputBoxes i).Contains (evalProgram program values i) :=
  trace.derivation.outputs_contain_of_allSound hall hvalues

inductive JetProgramDerivation {arity precision : ℕ} :
    (Fin arity → Rectangle precision) → (Fin arity → Rectangle precision) →
      List (Assignment arity) → (Fin arity → Rectangle precision) →
      (Fin arity → Rectangle precision) → Type
  | nil (valueBoxes velocityBoxes) :
      JetProgramDerivation valueBoxes velocityBoxes [] valueBoxes velocityBoxes
  | cons {valueBoxes velocityBoxes outputValueBoxes outputVelocityBoxes :
        Fin arity → Rectangle precision}
      {assignment : Assignment arity} {rest : List (Assignment arity)}
      {assignmentValue assignmentVelocity : Rectangle precision}
      (head : JetDerivation valueBoxes velocityBoxes assignment.expression
        assignmentValue assignmentVelocity)
      (tail : JetProgramDerivation
        (Function.update valueBoxes assignment.target assignmentValue)
        (Function.update velocityBoxes assignment.target assignmentVelocity)
        rest outputValueBoxes outputVelocityBoxes) :
      JetProgramDerivation valueBoxes velocityBoxes (assignment :: rest)
        outputValueBoxes outputVelocityBoxes

structure JetProgramTrace {arity precision : ℕ}
    (valueBoxes velocityBoxes : Fin arity → Rectangle precision)
    (program : List (Assignment arity)) where
  outputValueBoxes : Fin arity → Rectangle precision
  outputVelocityBoxes : Fin arity → Rectangle precision
  derivation : JetProgramDerivation valueBoxes velocityBoxes program
    outputValueBoxes outputVelocityBoxes

def JetProgramDerivation.operations {arity precision : ℕ} :
    {valueBoxes velocityBoxes outputValueBoxes outputVelocityBoxes :
      Fin arity → Rectangle precision} → {program : List (Assignment arity)} →
      JetProgramDerivation valueBoxes velocityBoxes program outputValueBoxes
        outputVelocityBoxes → List (DyadicOperation precision)
  | _, _, _, _, _, .nil _ _ => []
  | _, _, _, _, _, .cons head tail => head.operations ++ tail.operations

def JetProgramTrace.operations {arity precision : ℕ}
    {valueBoxes velocityBoxes : Fin arity → Rectangle precision}
    {program : List (Assignment arity)}
    (trace : JetProgramTrace valueBoxes velocityBoxes program) :
    List (DyadicOperation precision) := trace.derivation.operations

def proposeJetProgramTrace {arity precision : ℕ}
    (valueBoxes velocityBoxes : Fin arity → Rectangle precision) :
    (program : List (Assignment arity)) →
      JetProgramTrace valueBoxes velocityBoxes program
  | [] => ⟨valueBoxes, velocityBoxes, .nil valueBoxes velocityBoxes⟩
  | assignment :: rest => by
      let head := proposeJetTrace valueBoxes velocityBoxes assignment.expression
      let tail := proposeJetProgramTrace
        (Function.update valueBoxes assignment.target head.value)
        (Function.update velocityBoxes assignment.target head.derivative) rest
      exact ⟨tail.outputValueBoxes, tail.outputVelocityBoxes,
        .cons head.derivation tail.derivation⟩

theorem JetProgramDerivation.outputs_contain_of_allSound
    {arity precision : ℕ}
    {valueBoxes velocityBoxes outputValueBoxes outputVelocityBoxes :
      Fin arity → Rectangle precision} {program : List (Assignment arity)}
    (trace : JetProgramDerivation valueBoxes velocityBoxes program
      outputValueBoxes outputVelocityBoxes)
    (hall : ∀ operation ∈ trace.operations, operation.Sound)
    {values velocities : Fin arity → ℂ}
    (hvalues : ∀ i, (valueBoxes i).Contains (values i))
    (hvelocities : ∀ i, (velocityBoxes i).Contains (velocities i)) :
    (∀ i, (outputValueBoxes i).Contains (evalProgram program values i)) ∧
      (∀ i, (outputVelocityBoxes i).Contains
        (evalProgramVelocity program values velocities i)) := by
  induction trace generalizing values velocities with
  | nil valueBoxes velocityBoxes => exact ⟨hvalues, hvelocities⟩
  | @cons valueBoxes velocityBoxes outputValueBoxes outputVelocityBoxes assignment rest
      assignmentValue assignmentVelocity head tail ih =>
      have hhead := head.outputs_contain_of_allSound
        (by intro op hop; exact hall op (by simp [JetProgramDerivation.operations, hop]))
        hvalues hvelocities
      have hupdatedValues : ∀ i,
          (Function.update valueBoxes assignment.target assignmentValue i).Contains
            (assignment.updateValues values i) := by
        intro i
        by_cases hi : i = assignment.target
        · subst i
          simpa [Assignment.updateValues] using hhead.1
        · simpa [Assignment.updateValues, Function.update, hi] using hvalues i
      have hupdatedVelocities : ∀ i,
          (Function.update velocityBoxes assignment.target assignmentVelocity i).Contains
            (assignment.updateVelocities values velocities i) := by
        intro i
        by_cases hi : i = assignment.target
        · subst i
          simpa [Assignment.updateVelocities] using hhead.2
        · simpa [Assignment.updateVelocities, Function.update, hi] using hvelocities i
      exact ih
        (by intro op hop; exact hall op (by simp [JetProgramDerivation.operations, hop]))
        hupdatedValues hupdatedVelocities

theorem JetProgramTrace.outputs_contain_of_allSound
    {arity precision : ℕ}
    {valueBoxes velocityBoxes : Fin arity → Rectangle precision}
    {program : List (Assignment arity)}
    (trace : JetProgramTrace valueBoxes velocityBoxes program)
    (hall : ∀ operation ∈ trace.operations, operation.Sound)
    {values velocities : Fin arity → ℂ}
    (hvalues : ∀ i, (valueBoxes i).Contains (values i))
    (hvelocities : ∀ i, (velocityBoxes i).Contains (velocities i)) :
    (∀ i, (trace.outputValueBoxes i).Contains (evalProgram program values i)) ∧
      (∀ i, (trace.outputVelocityBoxes i).Contains
        (evalProgramVelocity program values velocities i)) :=
  trace.derivation.outputs_contain_of_allSound hall hvalues hvelocities

-- All recursive proofs in this file are complete.  Downstream generated certificates should use
-- the bridge theorems rather than unfold these evaluators into very large conversion terms.
attribute [irreducible] directionalEval secondDirectionalEval

end Expr

end ChapterVIFieldExpression

end PoincareChapterVI
