/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.ChapterVIFieldExpressionTrace

/-!
# First-order bivariate Taylor models over signed dyadic rectangles

A model represents `center + radial*x + angular*y + error` for `|x|,|y| <= 1`.  The proposal
functions below retain this decomposition through a shared straight-line field program.
-/

namespace PoincareChapterVI

open ChapterVILeanCompCertBatch
open ChapterVIFieldExpression

namespace ChapterVILeanCompCertAffineTrace

set_option linter.unusedSimpArgs false

abbrev Rectangle (precision : ℕ) := ChapterVISignedDyadicComplexRectangle precision

structure Model (precision : ℕ) where
  center : Rectangle precision
  radial : Rectangle precision
  angular : Rectangle precision
  error : Rectangle precision

def zero (precision : ℕ) : Model precision :=
  let z := ChapterVISignedDyadicComplexRectangle.pointInt precision 0
  ⟨z, z, z, z⟩

def integer (precision : ℕ) (value : ℤ) : Model precision :=
  let z := ChapterVISignedDyadicComplexRectangle.pointInt precision 0
  ⟨ChapterVISignedDyadicComplexRectangle.pointInt precision value, z, z, z⟩

def Model.add {precision : ℕ} (x y : Model precision) : Model precision :=
  ⟨x.center.add y.center, x.radial.add y.radial, x.angular.add y.angular,
    x.error.add y.error⟩

def Model.neg {precision : ℕ} (x : Model precision) : Model precision :=
  ⟨x.center.neg, x.radial.neg, x.angular.neg, x.error.neg⟩

def symmetric {precision : ℕ} (x : Rectangle precision) : Rectangle precision :=
  let realBudget := ChapterVILeanCompCertProposals.componentBudget x.real
  let imagBudget := ChapterVILeanCompCertProposals.componentBudget x.imag
  ⟨⟨-realBudget, realBudget⟩, ⟨-imagBudget, imagBudget⟩⟩

def Model.deviation {precision : ℕ} (x : Model precision) : Rectangle precision :=
  (symmetric x.radial).add (symmetric x.angular) |>.add x.error

def Model.range {precision : ℕ} (x : Model precision) : Rectangle precision :=
  x.center.add x.deviation

structure Proposed (precision : ℕ) where
  output : Model precision
  operations : List (DyadicOperation precision)

def proposeMul {precision : ℕ} (x y : Model precision) : Proposed precision :=
  let center := ChapterVILeanCompCertProposals.mulTrace x.center y.center
  let radialLeft := ChapterVILeanCompCertProposals.mulTrace x.radial y.center
  let radialRight := ChapterVILeanCompCertProposals.mulTrace x.center y.radial
  let angularLeft := ChapterVILeanCompCertProposals.mulTrace x.angular y.center
  let angularRight := ChapterVILeanCompCertProposals.mulTrace x.center y.angular
  let centerErrorRight := ChapterVILeanCompCertProposals.mulTrace x.center y.error
  let errorLeftCenter := ChapterVILeanCompCertProposals.mulTrace x.error y.center
  let deviationProduct := ChapterVILeanCompCertProposals.mulTrace x.deviation y.deviation
  { output :=
      ⟨center.output,
        radialLeft.output.add radialRight.output,
        angularLeft.output.add angularRight.output,
        (centerErrorRight.output.add errorLeftCenter.output).add deviationProduct.output⟩
    operations := center.operations ++ radialLeft.operations ++ radialRight.operations ++
      angularLeft.operations ++ angularRight.operations ++ centerErrorRight.operations ++
      errorLeftCenter.operations ++ deviationProduct.operations }

def proposeInv {precision : ℕ} (x : Model precision) : Proposed precision :=
  let centerInv := ChapterVILeanCompCertProposals.invTrace x.center
  let centerInvSq := ChapterVILeanCompCertProposals.mulTrace
    centerInv.output centerInv.output
  let radialProduct := ChapterVILeanCompCertProposals.mulTrace centerInvSq.output x.radial
  let angularProduct := ChapterVILeanCompCertProposals.mulTrace centerInvSq.output x.angular
  let errorLinear := ChapterVILeanCompCertProposals.mulTrace centerInvSq.output x.error
  let deviationSq := ChapterVILeanCompCertProposals.mulTrace x.deviation x.deviation
  let quadraticScale := ChapterVILeanCompCertProposals.mulTrace
    centerInvSq.output deviationSq.output
  let fullInv := ChapterVILeanCompCertProposals.invTrace x.range
  let quadraticTail := ChapterVILeanCompCertProposals.mulTrace
    quadraticScale.output fullInv.output
  { output :=
      ⟨centerInv.output, radialProduct.output.neg, angularProduct.output.neg,
        errorLinear.output.neg.add quadraticTail.output⟩
    operations := centerInv.operations ++ centerInvSq.operations ++ radialProduct.operations ++
      angularProduct.operations ++ errorLinear.operations ++ deviationSq.operations ++
      quadraticScale.operations ++ fullInv.operations ++ quadraticTail.operations }

theorem proposeMul_operations_sound {precision : ℕ} (x y : Model precision) :
    ∀ operation ∈ (proposeMul x y).operations, operation.Sound := by
  let a := ChapterVILeanCompCertProposals.mulTrace x.center y.center
  let b := ChapterVILeanCompCertProposals.mulTrace x.radial y.center
  let c := ChapterVILeanCompCertProposals.mulTrace x.center y.radial
  let d := ChapterVILeanCompCertProposals.mulTrace x.angular y.center
  let e := ChapterVILeanCompCertProposals.mulTrace x.center y.angular
  let f := ChapterVILeanCompCertProposals.mulTrace x.center y.error
  let g := ChapterVILeanCompCertProposals.mulTrace x.error y.center
  let h := ChapterVILeanCompCertProposals.mulTrace x.deviation y.deviation
  intro operation hoperation
  change operation ∈ a.operations ++ b.operations ++ c.operations ++ d.operations ++
    e.operations ++ f.operations ++ g.operations ++ h.operations at hoperation
  rcases List.mem_append.mp hoperation with hoperation | hh
  · rcases List.mem_append.mp hoperation with hoperation | hg
    · rcases List.mem_append.mp hoperation with hoperation | hf
      · rcases List.mem_append.mp hoperation with hoperation | he
        · rcases List.mem_append.mp hoperation with hoperation | hd
          · rcases List.mem_append.mp hoperation with hoperation | hc
            · rcases List.mem_append.mp hoperation with ha | hb
              · exact ChapterVILeanCompCertProposals.mulTrace_operations_sound _ _ operation ha
              · exact ChapterVILeanCompCertProposals.mulTrace_operations_sound _ _ operation hb
            · exact ChapterVILeanCompCertProposals.mulTrace_operations_sound _ _ operation hc
          · exact ChapterVILeanCompCertProposals.mulTrace_operations_sound _ _ operation hd
        · exact ChapterVILeanCompCertProposals.mulTrace_operations_sound _ _ operation he
      · exact ChapterVILeanCompCertProposals.mulTrace_operations_sound _ _ operation hf
    · exact ChapterVILeanCompCertProposals.mulTrace_operations_sound _ _ operation hg
  · exact ChapterVILeanCompCertProposals.mulTrace_operations_sound _ _ operation hh

theorem proposeInv_operations_sound {precision : ℕ} (x : Model precision)
    (hcenter : 0 < (ChapterVILeanCompCertProposals.invTrace x.center).normSq.lower)
    (hrange : 0 < (ChapterVILeanCompCertProposals.invTrace x.range).normSq.lower) :
    ∀ operation ∈ (proposeInv x).operations, operation.Sound := by
  let a := ChapterVILeanCompCertProposals.invTrace x.center
  let b := ChapterVILeanCompCertProposals.mulTrace a.output a.output
  let c := ChapterVILeanCompCertProposals.mulTrace b.output x.radial
  let d := ChapterVILeanCompCertProposals.mulTrace b.output x.angular
  let e := ChapterVILeanCompCertProposals.mulTrace b.output x.error
  let f := ChapterVILeanCompCertProposals.mulTrace x.deviation x.deviation
  let g := ChapterVILeanCompCertProposals.mulTrace b.output f.output
  let h := ChapterVILeanCompCertProposals.invTrace x.range
  let i := ChapterVILeanCompCertProposals.mulTrace g.output h.output
  intro operation hoperation
  change operation ∈ a.operations ++ b.operations ++ c.operations ++ d.operations ++
    e.operations ++ f.operations ++ g.operations ++ h.operations ++ i.operations at hoperation
  rcases List.mem_append.mp hoperation with hoperation | hi
  · rcases List.mem_append.mp hoperation with hoperation | hh
    · rcases List.mem_append.mp hoperation with hoperation | hg
      · rcases List.mem_append.mp hoperation with hoperation | hf
        · rcases List.mem_append.mp hoperation with hoperation | he
          · rcases List.mem_append.mp hoperation with hoperation | hd
            · rcases List.mem_append.mp hoperation with hoperation | hc
              · rcases List.mem_append.mp hoperation with ha | hb
                · exact ChapterVILeanCompCertProposals.invTrace_operations_sound _ hcenter operation ha
                · exact ChapterVILeanCompCertProposals.mulTrace_operations_sound _ _ operation hb
              · exact ChapterVILeanCompCertProposals.mulTrace_operations_sound _ _ operation hc
            · exact ChapterVILeanCompCertProposals.mulTrace_operations_sound _ _ operation hd
          · exact ChapterVILeanCompCertProposals.mulTrace_operations_sound _ _ operation he
        · exact ChapterVILeanCompCertProposals.mulTrace_operations_sound _ _ operation hf
      · exact ChapterVILeanCompCertProposals.mulTrace_operations_sound _ _ operation hg
    · exact ChapterVILeanCompCertProposals.invTrace_operations_sound _ hrange operation hh
  · exact ChapterVILeanCompCertProposals.mulTrace_operations_sound _ _ operation hi

def proposeExpression {arity precision : ℕ} (inputs : Fin arity → Model precision) :
    ChapterVIFieldExpression.Expr arity → Proposed precision
  | .var i => ⟨inputs i, []⟩
  | .integer value => ⟨integer precision value, []⟩
  | .add x y =>
      let tx := proposeExpression inputs x
      let ty := proposeExpression inputs y
      ⟨tx.output.add ty.output, tx.operations ++ ty.operations⟩
  | .neg x =>
      let tx := proposeExpression inputs x
      ⟨tx.output.neg, tx.operations⟩
  | .mul x y =>
      let tx := proposeExpression inputs x
      let ty := proposeExpression inputs y
      let product := proposeMul tx.output ty.output
      ⟨product.output, tx.operations ++ ty.operations ++ product.operations⟩
  | .inv x =>
      let tx := proposeExpression inputs x
      let inverse := proposeInv tx.output
      ⟨inverse.output, tx.operations ++ inverse.operations⟩

structure ProgramTrace {arity precision : ℕ} (inputs : Fin arity → Model precision)
    (program : List (ChapterVIFieldExpression.Expr.Assignment arity)) where
  outputs : Fin arity → Model precision
  operations : List (DyadicOperation precision)

def proposeProgram {arity precision : ℕ} (inputs : Fin arity → Model precision) :
    (program : List (ChapterVIFieldExpression.Expr.Assignment arity)) →
      ProgramTrace inputs program
  | [] => ⟨inputs, []⟩
  | assignment :: rest =>
      let head := proposeExpression inputs assignment.expression
      let tail := proposeProgram (Function.update inputs assignment.target head.output) rest
      ⟨tail.outputs, head.operations ++ tail.operations⟩

/-! ## Arbitrary-precision validity of generated traces -/

/-- The only side conditions not automatic for the generated outward rounding are positivity
of the two norm-square denominators at every reciprocal. -/
def ExpressionValid {arity precision : ℕ} (inputs : Fin arity → Model precision) :
    ChapterVIFieldExpression.Expr arity → Bool
  | .var _ | .integer _ => true
  | .add x y | .mul x y => ExpressionValid inputs x && ExpressionValid inputs y
  | .neg x => ExpressionValid inputs x
  | .inv x =>
      let tx := proposeExpression inputs x
      ExpressionValid inputs x &&
        decide (0 < (ChapterVILeanCompCertProposals.invTrace tx.output.center).normSq.lower) &&
        decide (0 < (ChapterVILeanCompCertProposals.invTrace tx.output.range).normSq.lower)

theorem proposeExpression_operations_sound {arity precision : ℕ}
    (inputs : Fin arity → Model precision) (expression : ChapterVIFieldExpression.Expr arity)
    (hvalid : ExpressionValid inputs expression = true) :
    ∀ operation ∈ (proposeExpression inputs expression).operations, operation.Sound := by
  induction expression with
  | var i => simp [proposeExpression]
  | integer z => simp [proposeExpression]
  | add x y ihx ihy =>
      simp only [ExpressionValid, Bool.and_eq_true] at hvalid
      intro operation hoperation
      simp only [proposeExpression, List.mem_append] at hoperation
      exact hoperation.elim (ihx hvalid.1 operation) (ihy hvalid.2 operation)
  | neg x ih =>
      simpa [proposeExpression] using ih hvalid
  | mul x y ihx ihy =>
      simp only [ExpressionValid, Bool.and_eq_true] at hvalid
      intro operation hoperation
      simp only [proposeExpression, List.mem_append] at hoperation
      rcases hoperation with hoperation | hoperation
      · rcases hoperation with hoperation | hoperation
        · exact ihx hvalid.1 operation hoperation
        · exact ihy hvalid.2 operation hoperation
      · exact proposeMul_operations_sound _ _ operation hoperation
  | inv x ih =>
      simp only [ExpressionValid, Bool.and_eq_true, decide_eq_true_eq] at hvalid
      intro operation hoperation
      simp only [proposeExpression, List.mem_append] at hoperation
      rcases hoperation with hoperation | hoperation
      · exact ih hvalid.1.1 operation hoperation
      · exact proposeInv_operations_sound _ hvalid.1.2 hvalid.2 operation hoperation

def ProgramValid {arity precision : ℕ} (inputs : Fin arity → Model precision) :
    List (ChapterVIFieldExpression.Expr.Assignment arity) → Bool
  | [] => true
  | assignment :: rest =>
      let head := proposeExpression inputs assignment.expression
      ExpressionValid inputs assignment.expression &&
        ProgramValid (Function.update inputs assignment.target head.output) rest

theorem proposeProgram_operations_sound {arity precision : ℕ}
    (inputs : Fin arity → Model precision)
    (program : List (ChapterVIFieldExpression.Expr.Assignment arity))
    (hvalid : ProgramValid inputs program = true) :
    ∀ operation ∈ (proposeProgram inputs program).operations, operation.Sound := by
  induction program generalizing inputs with
  | nil => simp [proposeProgram]
  | cons assignment rest ih =>
      simp only [ProgramValid, Bool.and_eq_true] at hvalid
      intro operation hoperation
      simp only [proposeProgram, List.mem_append] at hoperation
      rcases hoperation with hoperation | hoperation
      · exact proposeExpression_operations_sound inputs assignment.expression hvalid.1
          operation hoperation
      · exact ih (inputs := Function.update inputs assignment.target
          (proposeExpression inputs assignment.expression).output)
          hvalid.2 operation hoperation

/-! ## Semantic reconstruction -/

/-- A Taylor model contains a value when its four components reconstruct that value at the
shared normalized cell coordinates `radialParameter` and `angularParameter`. -/
def Model.Contains {precision : ℕ} (model : Model precision)
    (radialParameter angularParameter : ℝ) (value : ℂ) : Prop :=
  ∃ center radial angular error : ℂ,
    model.center.Contains center ∧ model.radial.Contains radial ∧
      model.angular.Contains angular ∧ model.error.Contains error ∧
      value = center + (radialParameter : ℂ) * radial +
        (angularParameter : ℂ) * angular + error

theorem zero_contains (precision : ℕ) (x y : ℝ) :
    (zero precision).Contains x y 0 := by
  refine ⟨0, 0, 0, 0, ?_, ?_, ?_, ?_, by ring⟩
  all_goals simpa [zero] using
    ChapterVISignedDyadicComplexRectangle.pointInt_contains precision 0

theorem integer_contains (precision : ℕ) (value : ℤ) (x y : ℝ) :
    (integer precision value).Contains x y value := by
  refine ⟨value, 0, 0, 0, ?_, ?_, ?_, ?_, by ring⟩
  · simpa [integer] using
      ChapterVISignedDyadicComplexRectangle.pointInt_contains precision value
  all_goals simpa [integer] using
    ChapterVISignedDyadicComplexRectangle.pointInt_contains precision 0

theorem Model.add_contains {precision : ℕ} {x y : Model precision}
    {radialParameter angularParameter : ℝ} {a b : ℂ}
    (ha : x.Contains radialParameter angularParameter a)
    (hb : y.Contains radialParameter angularParameter b) :
    (x.add y).Contains radialParameter angularParameter (a + b) := by
  obtain ⟨ac, ar, aa, ae, hac, har, haa, hae, rfl⟩ := ha
  obtain ⟨bc, br, ba, be, hbc, hbr, hba, hbe, rfl⟩ := hb
  refine ⟨ac + bc, ar + br, aa + ba, ae + be, ?_, ?_, ?_, ?_, by ring⟩
  · exact ChapterVISignedDyadicComplexRectangle.add_contains hac hbc
  · exact ChapterVISignedDyadicComplexRectangle.add_contains har hbr
  · exact ChapterVISignedDyadicComplexRectangle.add_contains haa hba
  · exact ChapterVISignedDyadicComplexRectangle.add_contains hae hbe

theorem Model.neg_contains {precision : ℕ} {x : Model precision}
    {radialParameter angularParameter : ℝ} {a : ℂ}
    (ha : x.Contains radialParameter angularParameter a) :
    x.neg.Contains radialParameter angularParameter (-a) := by
  obtain ⟨c, r, w, e, hc, hr, hw, he, rfl⟩ := ha
  refine ⟨-c, -r, -w, -e, ?_, ?_, ?_, ?_, by ring⟩
  · exact ChapterVISignedDyadicComplexRectangle.neg_contains hc
  · exact ChapterVISignedDyadicComplexRectangle.neg_contains hr
  · exact ChapterVISignedDyadicComplexRectangle.neg_contains hw
  · exact ChapterVISignedDyadicComplexRectangle.neg_contains he

private theorem symmetricInterval_contains_mul {precision : ℕ}
    {interval : ChapterVISignedDyadicInterval precision} {x z : ℝ}
    (hx : |x| ≤ 1) (hz : interval.Contains z) :
    (⟨-ChapterVILeanCompCertProposals.componentBudget interval,
        ChapterVILeanCompCertProposals.componentBudget interval⟩ :
      ChapterVISignedDyadicInterval precision).Contains (x * z) := by
  have hlower :
      -ChapterVILeanCompCertProposals.componentBudget interval ≤ interval.lower := by
    simp [ChapterVILeanCompCertProposals.componentBudget]
    omega
  have hupper :
      interval.upper ≤ ChapterVILeanCompCertProposals.componentBudget interval := by
    simp [ChapterVILeanCompCertProposals.componentBudget]
  have hzBounds :
      -(ChapterVILeanCompCertProposals.componentBudget interval : ℝ) /
          ChapterVISignedDyadicInterval.scale precision ≤ z ∧
      z ≤ (ChapterVILeanCompCertProposals.componentBudget interval : ℝ) /
          ChapterVISignedDyadicInterval.scale precision := by
    constructor
    · exact ((div_le_div_iff_of_pos_right
        (ChapterVISignedDyadicInterval.scale_pos precision)).2
          (by exact_mod_cast hlower)).trans hz.1
    · exact hz.2.trans ((div_le_div_iff_of_pos_right
        (ChapterVISignedDyadicInterval.scale_pos precision)).2
          (by exact_mod_cast hupper))
  have hbudget : 0 ≤
      (ChapterVILeanCompCertProposals.componentBudget interval : ℝ) /
        ChapterVISignedDyadicInterval.scale precision := by
    apply div_nonneg
    · exact_mod_cast (show 0 ≤ ChapterVILeanCompCertProposals.componentBudget interval by
        simp [ChapterVILeanCompCertProposals.componentBudget])
    · exact (ChapterVISignedDyadicInterval.scale_pos precision).le
  have hzBounds' :
      -((ChapterVILeanCompCertProposals.componentBudget interval : ℝ) /
          ChapterVISignedDyadicInterval.scale precision) ≤ z ∧
      z ≤ (ChapterVILeanCompCertProposals.componentBudget interval : ℝ) /
          ChapterVISignedDyadicInterval.scale precision := by
    exact ⟨by simpa only [neg_div] using hzBounds.1, hzBounds.2⟩
  have hzAbs : |z| ≤
      (ChapterVILeanCompCertProposals.componentBudget interval : ℝ) /
        ChapterVISignedDyadicInterval.scale precision := abs_le.mpr hzBounds'
  have hproduct : |x * z| ≤
      (ChapterVILeanCompCertProposals.componentBudget interval : ℝ) /
        ChapterVISignedDyadicInterval.scale precision := by
    rw [abs_mul]
    calc
      |x| * |z| ≤ 1 *
          ((ChapterVILeanCompCertProposals.componentBudget interval : ℝ) /
            ChapterVISignedDyadicInterval.scale precision) :=
        mul_le_mul hx hzAbs (abs_nonneg z) (by norm_num)
      _ = _ := one_mul _
  constructor
  · change ((-ChapterVILeanCompCertProposals.componentBudget interval : ℤ) : ℝ) /
        ChapterVISignedDyadicInterval.scale precision ≤ x * z
    simpa only [Int.cast_neg, neg_div] using (abs_le.mp hproduct).1
  · change x * z ≤
      (ChapterVILeanCompCertProposals.componentBudget interval : ℝ) /
        ChapterVISignedDyadicInterval.scale precision
    exact (abs_le.mp hproduct).2

private theorem symmetric_contains_real_mul {precision : ℕ}
    {rectangle : Rectangle precision} {x : ℝ} {z : ℂ}
    (hx : |x| ≤ 1) (hz : rectangle.Contains z) :
    (symmetric rectangle).Contains ((x : ℂ) * z) := by
  constructor
  · simpa [symmetric, Complex.mul_re] using
      symmetricInterval_contains_mul hx hz.1
  · simpa [symmetric, Complex.mul_im] using
      symmetricInterval_contains_mul hx hz.2

theorem Model.deviation_contains {precision : ℕ} {model : Model precision}
    {radialParameter angularParameter : ℝ} {radial angular error : ℂ}
    (hradialParameter : |radialParameter| ≤ 1)
    (hangularParameter : |angularParameter| ≤ 1)
    (hradial : model.radial.Contains radial)
    (hangular : model.angular.Contains angular)
    (herror : model.error.Contains error) :
    model.deviation.Contains
      ((radialParameter : ℂ) * radial + (angularParameter : ℂ) * angular + error) := by
  exact ChapterVISignedDyadicComplexRectangle.add_contains
    (ChapterVISignedDyadicComplexRectangle.add_contains
      (symmetric_contains_real_mul hradialParameter hradial)
      (symmetric_contains_real_mul hangularParameter hangular)) herror

theorem Model.range_contains {precision : ℕ} {model : Model precision}
    {radialParameter angularParameter : ℝ} {value : ℂ}
    (hradialParameter : |radialParameter| ≤ 1)
    (hangularParameter : |angularParameter| ≤ 1)
    (hvalue : model.Contains radialParameter angularParameter value) :
    model.range.Contains value := by
  obtain ⟨center, radial, angular, error, hc, hr, ha, he, rfl⟩ := hvalue
  simpa [Model.range, add_assoc] using ChapterVISignedDyadicComplexRectangle.add_contains hc
    (Model.deviation_contains hradialParameter hangularParameter hr ha he)

theorem proposeMul_output_contains {precision : ℕ} {x y : Model precision}
    {radialParameter angularParameter : ℝ} {a b : ℂ}
    (hradialParameter : |radialParameter| ≤ 1)
    (hangularParameter : |angularParameter| ≤ 1)
    (hall : ∀ operation ∈ (proposeMul x y).operations, operation.Sound)
    (ha : x.Contains radialParameter angularParameter a)
    (hb : y.Contains radialParameter angularParameter b) :
    (proposeMul x y).output.Contains radialParameter angularParameter (a * b) := by
  obtain ⟨xc, xr, xa, xe, hxc, hxr, hxa, hxe, rfl⟩ := ha
  obtain ⟨yc, yr, ya, ye, hyc, hyr, hya, hye, rfl⟩ := hb
  let center := ChapterVILeanCompCertProposals.mulTrace x.center y.center
  let radialLeft := ChapterVILeanCompCertProposals.mulTrace x.radial y.center
  let radialRight := ChapterVILeanCompCertProposals.mulTrace x.center y.radial
  let angularLeft := ChapterVILeanCompCertProposals.mulTrace x.angular y.center
  let angularRight := ChapterVILeanCompCertProposals.mulTrace x.center y.angular
  let centerErrorRight := ChapterVILeanCompCertProposals.mulTrace x.center y.error
  let errorLeftCenter := ChapterVILeanCompCertProposals.mulTrace x.error y.center
  let deviationProduct := ChapterVILeanCompCertProposals.mulTrace x.deviation y.deviation
  have sound (trace : ChapterVISignedDyadicComplexRectangle.MulTrace x.center y.center)
      (htrace : trace = center) : ∀ operation ∈ trace.operations, operation.Sound := by
    subst trace
    intro operation hoperation
    exact hall operation (by simp [proposeMul, center, radialLeft, radialRight, angularLeft,
      angularRight, centerErrorRight, errorLeftCenter, deviationProduct, hoperation])
  have hcenter : center.output.Contains (xc * yc) :=
    center.output_contains_mul_of_allSound (sound center rfl) hxc hyc
  have hradialLeft : radialLeft.output.Contains (xr * yc) :=
    radialLeft.output_contains_mul_of_allSound
      (by
        intro operation hoperation
        exact hall operation (by simp [proposeMul, center, radialLeft, radialRight, angularLeft,
          angularRight, centerErrorRight, errorLeftCenter, deviationProduct, hoperation])) hxr hyc
  have hradialRight : radialRight.output.Contains (xc * yr) :=
    radialRight.output_contains_mul_of_allSound
      (by
        intro operation hoperation
        exact hall operation (by simp [proposeMul, center, radialLeft, radialRight, angularLeft,
          angularRight, centerErrorRight, errorLeftCenter, deviationProduct, hoperation])) hxc hyr
  have hangularLeft : angularLeft.output.Contains (xa * yc) :=
    angularLeft.output_contains_mul_of_allSound
      (by
        intro operation hoperation
        exact hall operation (by simp [proposeMul, center, radialLeft, radialRight, angularLeft,
          angularRight, centerErrorRight, errorLeftCenter, deviationProduct, hoperation])) hxa hyc
  have hangularRight : angularRight.output.Contains (xc * ya) :=
    angularRight.output_contains_mul_of_allSound
      (by
        intro operation hoperation
        exact hall operation (by simp [proposeMul, center, radialLeft, radialRight, angularLeft,
          angularRight, centerErrorRight, errorLeftCenter, deviationProduct, hoperation])) hxc hya
  have hcenterErrorRight : centerErrorRight.output.Contains (xc * ye) :=
    centerErrorRight.output_contains_mul_of_allSound
      (by
        intro operation hoperation
        exact hall operation (by simp [proposeMul, center, radialLeft, radialRight, angularLeft,
          angularRight, centerErrorRight, errorLeftCenter, deviationProduct, hoperation])) hxc hye
  have herrorLeftCenter : errorLeftCenter.output.Contains (xe * yc) :=
    errorLeftCenter.output_contains_mul_of_allSound
      (by
        intro operation hoperation
        exact hall operation (by simp [proposeMul, center, radialLeft, radialRight, angularLeft,
          angularRight, centerErrorRight, errorLeftCenter, deviationProduct, hoperation])) hxe hyc
  have hxDeviation := Model.deviation_contains hradialParameter hangularParameter hxr hxa hxe
  have hyDeviation := Model.deviation_contains hradialParameter hangularParameter hyr hya hye
  have hdeviationProduct : deviationProduct.output.Contains
      (((radialParameter : ℂ) * xr + (angularParameter : ℂ) * xa + xe) *
        ((radialParameter : ℂ) * yr + (angularParameter : ℂ) * ya + ye)) :=
    deviationProduct.output_contains_mul_of_allSound
      (by
        intro operation hoperation
        exact hall operation (by simp [proposeMul, center, radialLeft, radialRight, angularLeft,
          angularRight, centerErrorRight, errorLeftCenter, deviationProduct, hoperation]))
      hxDeviation hyDeviation
  refine ⟨xc * yc, xr * yc + xc * yr, xa * yc + xc * ya,
    xc * ye + xe * yc +
      (((radialParameter : ℂ) * xr + (angularParameter : ℂ) * xa + xe) *
        ((radialParameter : ℂ) * yr + (angularParameter : ℂ) * ya + ye)),
    ?_, ?_, ?_, ?_, by ring⟩
  · simpa [proposeMul, center, radialLeft, radialRight, angularLeft, angularRight,
      centerErrorRight, errorLeftCenter, deviationProduct] using hcenter
  · simpa [proposeMul, center, radialLeft, radialRight, angularLeft, angularRight,
      centerErrorRight, errorLeftCenter, deviationProduct] using
        ChapterVISignedDyadicComplexRectangle.add_contains hradialLeft hradialRight
  · simpa [proposeMul, center, radialLeft, radialRight, angularLeft, angularRight,
      centerErrorRight, errorLeftCenter, deviationProduct] using
        ChapterVISignedDyadicComplexRectangle.add_contains hangularLeft hangularRight
  · simpa [proposeMul, center, radialLeft, radialRight, angularLeft, angularRight,
      centerErrorRight, errorLeftCenter, deviationProduct, add_assoc] using
        ChapterVISignedDyadicComplexRectangle.add_contains
          (ChapterVISignedDyadicComplexRectangle.add_contains
            hcenterErrorRight herrorLeftCenter) hdeviationProduct

private theorem invTrace_input_ne_zero {precision : ℕ}
    {input : Rectangle precision}
    (trace : ChapterVISignedDyadicComplexRectangle.InvTrace input)
    (hall : ∀ operation ∈ trace.operations, operation.Sound)
    {value : ℂ} (hvalue : input.Contains value) : value ≠ 0 := by
  have hreSq : ChapterVISignedDyadicInterval.MulCertificate
      input.real input.real trace.realSq :=
    hall (.mul input.real input.real trace.realSq) (by
      simp [ChapterVISignedDyadicComplexRectangle.InvTrace.operations])
  have himSq : ChapterVISignedDyadicInterval.MulCertificate
      input.imag input.imag trace.imagSq :=
    hall (.mul input.imag input.imag trace.imagSq) (by
      simp [ChapterVISignedDyadicComplexRectangle.InvTrace.operations])
  have hrecip : ChapterVISignedDyadicInterval.PositiveReciprocalCertificate
      trace.normSq trace.normInv :=
    hall (.positiveReciprocal trace.normSq trace.normInv) (by
      simp [ChapterVISignedDyadicComplexRectangle.InvTrace.operations])
  have hnorm : trace.normSq.Contains (Complex.normSq value) := by
    rw [Complex.normSq_apply]
    exact ChapterVISignedDyadicInterval.add_contains
      (hreSq.contains_mul hvalue.1 hvalue.1)
      (himSq.contains_mul hvalue.2 hvalue.2)
  intro hzero
  subst value
  have hlowerPos : 0 < (trace.normSq.lower : ℝ) /
      ChapterVISignedDyadicInterval.scale precision :=
    div_pos (by exact_mod_cast hrecip.input_lower_pos)
      (ChapterVISignedDyadicInterval.scale_pos precision)
  simp only [Complex.normSq_zero] at hnorm
  have hlowerNonpos := hnorm.1
  change (trace.normSq.lower : ℝ) /
      ChapterVISignedDyadicInterval.scale precision ≤ 0 at hlowerNonpos
  linarith

theorem proposeInv_output_contains {precision : ℕ} {x : Model precision}
    {radialParameter angularParameter : ℝ} {a : ℂ}
    (hradialParameter : |radialParameter| ≤ 1)
    (hangularParameter : |angularParameter| ≤ 1)
    (hall : ∀ operation ∈ (proposeInv x).operations, operation.Sound)
    (ha : x.Contains radialParameter angularParameter a) :
    (proposeInv x).output.Contains radialParameter angularParameter a⁻¹ := by
  obtain ⟨c, r, w, e, hc, hr, hw, he, haValue⟩ := ha
  let d : ℂ := (radialParameter : ℂ) * r + (angularParameter : ℂ) * w + e
  have haEq : a = c + d := by simpa [d, add_assoc] using haValue
  let centerInv := ChapterVILeanCompCertProposals.invTrace x.center
  let centerInvSq := ChapterVILeanCompCertProposals.mulTrace
    centerInv.output centerInv.output
  let radialProduct := ChapterVILeanCompCertProposals.mulTrace centerInvSq.output x.radial
  let angularProduct := ChapterVILeanCompCertProposals.mulTrace centerInvSq.output x.angular
  let errorLinear := ChapterVILeanCompCertProposals.mulTrace centerInvSq.output x.error
  let deviationSq := ChapterVILeanCompCertProposals.mulTrace x.deviation x.deviation
  let quadraticScale := ChapterVILeanCompCertProposals.mulTrace
    centerInvSq.output deviationSq.output
  let fullInv := ChapterVILeanCompCertProposals.invTrace x.range
  let quadraticTail := ChapterVILeanCompCertProposals.mulTrace
    quadraticScale.output fullInv.output
  have hsound (operations : List (DyadicOperation precision))
      (hoperations : ∀ operation ∈ operations,
        operation ∈ (proposeInv x).operations) :
      ∀ operation ∈ operations, operation.Sound := by
    intro operation hoperation
    exact hall operation (hoperations operation hoperation)
  have hcenterInvSound : ∀ operation ∈ centerInv.operations, operation.Sound :=
    hsound centerInv.operations (by
      intro operation hoperation
      simp [proposeInv, centerInv, centerInvSq, radialProduct, angularProduct,
        errorLinear, deviationSq, quadraticScale, fullInv, quadraticTail, hoperation])
  have hcenterInv : centerInv.output.Contains c⁻¹ :=
    centerInv.output_contains_inv_of_allSound hcenterInvSound hc
  have hcenterInvSq : centerInvSq.output.Contains (c⁻¹ * c⁻¹) :=
    centerInvSq.output_contains_mul_of_allSound
      (hsound centerInvSq.operations (by
        intro operation hoperation
        simp [proposeInv, centerInv, centerInvSq, radialProduct, angularProduct,
          errorLinear, deviationSq, quadraticScale, fullInv, quadraticTail, hoperation]))
      hcenterInv hcenterInv
  have hradialProduct : radialProduct.output.Contains ((c⁻¹ * c⁻¹) * r) :=
    radialProduct.output_contains_mul_of_allSound
      (hsound radialProduct.operations (by
        intro operation hoperation
        simp [proposeInv, centerInv, centerInvSq, radialProduct, angularProduct,
          errorLinear, deviationSq, quadraticScale, fullInv, quadraticTail, hoperation]))
      hcenterInvSq hr
  have hangularProduct : angularProduct.output.Contains ((c⁻¹ * c⁻¹) * w) :=
    angularProduct.output_contains_mul_of_allSound
      (hsound angularProduct.operations (by
        intro operation hoperation
        simp [proposeInv, centerInv, centerInvSq, radialProduct, angularProduct,
          errorLinear, deviationSq, quadraticScale, fullInv, quadraticTail, hoperation]))
      hcenterInvSq hw
  have herrorLinear : errorLinear.output.Contains ((c⁻¹ * c⁻¹) * e) :=
    errorLinear.output_contains_mul_of_allSound
      (hsound errorLinear.operations (by
        intro operation hoperation
        simp [proposeInv, centerInv, centerInvSq, radialProduct, angularProduct,
          errorLinear, deviationSq, quadraticScale, fullInv, quadraticTail, hoperation]))
      hcenterInvSq he
  have hdeviation := Model.deviation_contains hradialParameter hangularParameter hr hw he
  have hdeviationSq : deviationSq.output.Contains (d * d) := by
    apply deviationSq.output_contains_mul_of_allSound
      (hsound deviationSq.operations (by
        intro operation hoperation
        simp [proposeInv, centerInv, centerInvSq, radialProduct, angularProduct,
          errorLinear, deviationSq, quadraticScale, fullInv, quadraticTail, hoperation]))
    · simpa [d] using hdeviation
    · simpa [d] using hdeviation
  have hquadraticScale : quadraticScale.output.Contains ((c⁻¹ * c⁻¹) * (d * d)) :=
    quadraticScale.output_contains_mul_of_allSound
      (hsound quadraticScale.operations (by
        intro operation hoperation
        simp [proposeInv, centerInv, centerInvSq, radialProduct, angularProduct,
          errorLinear, deviationSq, quadraticScale, fullInv, quadraticTail, hoperation]))
      hcenterInvSq hdeviationSq
  have hrange := Model.range_contains hradialParameter hangularParameter
    (show x.Contains radialParameter angularParameter a from
      ⟨c, r, w, e, hc, hr, hw, he, haValue⟩)
  have hfullInvSound : ∀ operation ∈ fullInv.operations, operation.Sound :=
    hsound fullInv.operations (by
      intro operation hoperation
      simp [proposeInv, centerInv, centerInvSq, radialProduct, angularProduct,
        errorLinear, deviationSq, quadraticScale, fullInv, quadraticTail, hoperation])
  have hfullInv : fullInv.output.Contains a⁻¹ :=
    fullInv.output_contains_inv_of_allSound hfullInvSound hrange
  have hquadraticTail : quadraticTail.output.Contains
      (((c⁻¹ * c⁻¹) * (d * d)) * a⁻¹) :=
    quadraticTail.output_contains_mul_of_allSound
      (hsound quadraticTail.operations (by
        intro operation hoperation
        simp [proposeInv, centerInv, centerInvSq, radialProduct, angularProduct,
          errorLinear, deviationSq, quadraticScale, fullInv, quadraticTail, hoperation]))
      hquadraticScale hfullInv
  have hcNe : c ≠ 0 := invTrace_input_ne_zero centerInv hcenterInvSound hc
  have haNe : a ≠ 0 := invTrace_input_ne_zero fullInv hfullInvSound hrange
  have hcdNe : c + d ≠ 0 := by
    intro hzero
    apply haNe
    rw [haEq, hzero]
  have hinverseIdentity :
      a⁻¹ = c⁻¹ - (radialParameter : ℂ) * ((c⁻¹ * c⁻¹) * r) -
          (angularParameter : ℂ) * ((c⁻¹ * c⁻¹) * w) +
        (-(c⁻¹ * c⁻¹ * e) + ((c⁻¹ * c⁻¹) * (d * d)) * a⁻¹) := by
    rw [haEq]
    change (c + d)⁻¹ = c⁻¹ - (radialParameter : ℂ) * (c⁻¹ * c⁻¹ * r) -
      (angularParameter : ℂ) * (c⁻¹ * c⁻¹ * w) +
        (-(c⁻¹ * c⁻¹ * e) + c⁻¹ * c⁻¹ * (d * d) * (c + d)⁻¹)
    field_simp [hcNe, hcdNe]
    unfold d
    ring
  refine ⟨c⁻¹, -((c⁻¹ * c⁻¹) * r), -((c⁻¹ * c⁻¹) * w),
    -((c⁻¹ * c⁻¹) * e) + ((c⁻¹ * c⁻¹) * (d * d)) * a⁻¹,
    ?_, ?_, ?_, ?_, ?_⟩
  · simpa [proposeInv, centerInv, centerInvSq, radialProduct, angularProduct,
      errorLinear, deviationSq, quadraticScale, fullInv, quadraticTail] using hcenterInv
  · simpa [proposeInv, centerInv, centerInvSq, radialProduct, angularProduct,
      errorLinear, deviationSq, quadraticScale, fullInv, quadraticTail] using
        ChapterVISignedDyadicComplexRectangle.neg_contains hradialProduct
  · simpa [proposeInv, centerInv, centerInvSq, radialProduct, angularProduct,
      errorLinear, deviationSq, quadraticScale, fullInv, quadraticTail] using
        ChapterVISignedDyadicComplexRectangle.neg_contains hangularProduct
  · simpa [proposeInv, centerInv, centerInvSq, radialProduct, angularProduct,
      errorLinear, deviationSq, quadraticScale, fullInv, quadraticTail] using
        ChapterVISignedDyadicComplexRectangle.add_contains
          (ChapterVISignedDyadicComplexRectangle.neg_contains herrorLinear) hquadraticTail
  · simpa [sub_eq_add_neg, add_assoc] using hinverseIdentity

theorem proposeExpression_output_contains {arity precision : ℕ}
    (inputs : Fin arity → Model precision)
    (expression : ChapterVIFieldExpression.Expr arity)
    {radialParameter angularParameter : ℝ}
    (hradialParameter : |radialParameter| ≤ 1)
    (hangularParameter : |angularParameter| ≤ 1)
    (hall : ∀ operation ∈ (proposeExpression inputs expression).operations,
      operation.Sound)
    {values : Fin arity → ℂ}
    (hinputs : ∀ i, (inputs i).Contains radialParameter angularParameter (values i)) :
    (proposeExpression inputs expression).output.Contains radialParameter angularParameter
      (expression.eval values) := by
  induction expression with
  | var i => simpa [proposeExpression] using hinputs i
  | integer value =>
      simpa [proposeExpression, ChapterVIFieldExpression.Expr.eval] using
        integer_contains precision value radialParameter angularParameter
  | add x y ihx ihy =>
      have hx := ihx (by
        intro operation hoperation
        exact hall operation (by simp [proposeExpression, hoperation]))
      have hy := ihy (by
        intro operation hoperation
        exact hall operation (by simp [proposeExpression, hoperation]))
      simpa [proposeExpression, ChapterVIFieldExpression.Expr.eval] using Model.add_contains hx hy
  | neg x ih =>
      have hx := ih (by
        intro operation hoperation
        exact hall operation (by simp [proposeExpression, hoperation]))
      simpa [proposeExpression, ChapterVIFieldExpression.Expr.eval] using Model.neg_contains hx
  | mul x y ihx ihy =>
      have hx := ihx (by
        intro operation hoperation
        exact hall operation (by simp [proposeExpression, hoperation]))
      have hy := ihy (by
        intro operation hoperation
        exact hall operation (by simp [proposeExpression, hoperation]))
      apply proposeMul_output_contains hradialParameter hangularParameter
      · intro operation hoperation
        exact hall operation (by simp [proposeExpression, hoperation])
      · exact hx
      · exact hy
  | inv x ih =>
      have hx := ih (by
        intro operation hoperation
        exact hall operation (by simp [proposeExpression, hoperation]))
      apply proposeInv_output_contains hradialParameter hangularParameter
      · intro operation hoperation
        exact hall operation (by simp [proposeExpression, hoperation])
      · exact hx

theorem ProgramTrace.outputs_contain_of_allSound {arity precision : ℕ}
    {inputs : Fin arity → Model precision}
    {program : List (ChapterVIFieldExpression.Expr.Assignment arity)}
    {radialParameter angularParameter : ℝ}
    (hradialParameter : |radialParameter| ≤ 1)
    (hangularParameter : |angularParameter| ≤ 1)
    (hall : ∀ operation ∈ (proposeProgram inputs program).operations, operation.Sound)
    {values : Fin arity → ℂ}
    (hinputs : ∀ i, (inputs i).Contains radialParameter angularParameter (values i)) :
    ∀ i, ((proposeProgram inputs program).outputs i).Contains radialParameter angularParameter
      (ChapterVIFieldExpression.Expr.evalProgram program values i) := by
  induction program generalizing inputs values with
  | nil =>
      intro i
      simpa [proposeProgram, ChapterVIFieldExpression.Expr.evalProgram] using hinputs i
  | cons assignment rest ih =>
      let head := proposeExpression inputs assignment.expression
      have hhead : head.output.Contains radialParameter angularParameter
          (assignment.expression.eval values) :=
        proposeExpression_output_contains inputs assignment.expression
          hradialParameter hangularParameter
          (by
            intro operation hoperation
            exact hall operation (by simp [proposeProgram, head, hoperation]))
          hinputs
      have hupdated : ∀ i,
          (Function.update inputs assignment.target head.output i).Contains
            radialParameter angularParameter (assignment.updateValues values i) := by
        intro i
        by_cases hi : i = assignment.target
        · subst i
          simpa [ChapterVIFieldExpression.Expr.Assignment.updateValues] using hhead
        · simpa [ChapterVIFieldExpression.Expr.Assignment.updateValues,
            Function.update, hi] using hinputs i
      have htail := ih (inputs := Function.update inputs assignment.target head.output)
        (values := assignment.updateValues values)
        (by
          intro operation hoperation
          exact hall operation (by simp [proposeProgram, head, hoperation]))
        hupdated
      simpa [proposeProgram, head, ChapterVIFieldExpression.Expr.evalProgram] using htail

end ChapterVILeanCompCertAffineTrace

end PoincareChapterVI
