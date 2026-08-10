/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.ChapterVIDRadialTailBaseCenteredSemantics
import PoincareChapterVI.ChapterVIDRadialTailCenteredKernel

/-! # Semantic certificate for the collision-base-centred radial-tail table -/

noncomputable section

namespace PoincareChapterVI
namespace ChapterVIDRadialTailCenteredCertificate

open Complex Real Set
open scoped unitInterval
open ChapterVIFieldExpression Expr
open ChapterVILeanCompCertAffineTrace
open ChapterVIDRadialTailBaseCenteredProgram
open ChapterVIDRadialTailBaseCenteredSemantics
open ChapterVIDRadialTailCellInputTrace
open ChapterVIDRadialTailTaylorSemantics
open ChapterVIDRadialTailCenteredCompiledGrid

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem imaginaryUnit_contains (x y : ℝ) :
    ChapterVIDRadialTailBaseCenteredAffineTrace.imaginaryUnit.Contains x y Complex.I := by
  refine ⟨Complex.I, 0, 0, 0, ?_, ?_, ?_, ?_, by ring⟩
  · constructor <;> norm_num [ChapterVIDRadialTailBaseCenteredAffineTrace.imaginaryUnit,
      ChapterVISignedDyadicComplexRectangle.Contains,
      ChapterVISignedDyadicInterval.Contains,
      ChapterVISignedDyadicInterval.toRealInterval,
      ChapterVIRealInterval.Contains,
      ChapterVISignedDyadicInterval.scale]
  all_goals simpa [ChapterVIDRadialTailBaseCenteredAffineTrace.imaginaryUnit,
    ChapterVIDRadialTailBaseCenteredAffineTrace.zeroRectangle] using
      ChapterVISignedDyadicComplexRectangle.pointInt_contains 40 0

theorem zetaBase_contains (x y : ℝ) :
    ChapterVIDRadialTailBaseConstantTrace.zetaBase.Contains x y chapterVIDZRootBase := by
  have h := ChapterVIDRadialTailBaseConstantTrace.zetaBase_contains x y
  convert h using 1
  simp [chapterVIDZRootBase,
    chapterVIPositiveRealCubicLift, chapterVIPositiveRealCubicValue,
    max_eq_left chapterVIDCriticalParameterModulus_pos.le]

private theorem pModel_contains_any_angular (row : Fin 6) (index : Fin 16)
    {s : ℝ} (hs : s ∈ Icc (radialStart row index : ℝ) (radialEnd row index : ℝ))
    (y : ℝ) :
    (pModel row index).Contains
      ((s - radialCenter row index) / radialHalfWidth row index) y (pValue s : ℂ) := by
  obtain ⟨c, r, w, e, hc, hr, _hw, he, hvalue⟩ := pModel_contains row index hs
  refine ⟨c, r, 0, e, hc, hr, ?_, he, ?_⟩
  · simpa [pModel, ChapterVIDRadialTailCellInputTrace.zeroRectangle] using
      ChapterVISignedDyadicComplexRectangle.pointInt_contains 40 0
  · simpa using hvalue

private theorem tModel_contains_any_radial (side : ChapterVIDPinchingArcSide) (row : Fin 6)
    (index : Fin (angularCells side row)) (t : I)
    (ht : (t : ℝ) ∈ Icc (angularStart side row index : ℝ)
      (angularEnd side row index : ℝ)) (x : ℝ) :
    (tModel side row index).Contains x
      (((t : ℝ) - angularCenter side row index) / angularHalfWidth side row index) (t : ℂ) := by
  obtain ⟨c, r, w, e, hc, _hr, hw, he, hvalue⟩ := tModel_contains side row index ht
  refine ⟨c, 0, w, e, hc, ?_, hw, he, ?_⟩
  · simpa [tModel, ChapterVIDRadialTailCellInputTrace.zeroRectangle] using
      ChapterVISignedDyadicComplexRectangle.pointInt_contains 40 0
  · simpa using hvalue

private theorem normalized_radial_bound (row : Fin 6) (index : Fin 16)
    {s : ℝ} (hs : s ∈ Icc (radialStart row index : ℝ) (radialEnd row index : ℝ)) :
    |(s - radialCenter row index) / radialHalfWidth row index| ≤ 1 := by
  rw [abs_le]
  constructor <;> fin_cases row <;> fin_cases index <;>
    norm_num [radialCenter, radialHalfWidth, radialStart, radialEnd,
      rowStart, rowEnd, radialRow, chapterVICubicClusterNode] at hs ⊢ <;> linarith

private theorem normalized_angular_bound (side : ChapterVIDPinchingArcSide) (row : Fin 6)
    (index : Fin (angularCells side row)) {t : ℝ}
    (ht : t ∈ Icc (angularStart side row index : ℝ)
      (angularEnd side row index : ℝ)) :
    |(t - angularCenter side row index) / angularHalfWidth side row index| ≤ 1 := by
  rw [abs_le]
  constructor <;> cases side <;> fin_cases row <;> fin_cases index <;>
    norm_num [angularCenter, angularHalfWidth, angularStart, angularEnd,
      angularCells, chapterVIQuadraticClusterNode] at ht ⊢ <;> linarith

private theorem inputs_contain
    (side : ChapterVIDPinchingArcSide) (row : Fin 6) (radial : Fin 16)
    (angular : Fin (angularCells side row)) {s : ℝ} (t : I) {remainder : ℂ}
    (hs : s ∈ Icc (radialStart row radial : ℝ) (radialEnd row radial : ℝ))
    (ht : (t : ℝ) ∈ Icc (angularStart side row angular : ℝ)
      (angularEnd side row angular : ℝ))
    (hrem : ‖remainder‖ ≤ (1 / 3 : ℝ) ^ 6 / 512) :
    let x := (s - radialCenter row radial) / radialHalfWidth row radial
    let y := ((t : ℝ) - angularCenter side row angular) / angularHalfWidth side row angular
    ∀ i, (inputs side row radial angular i).Contains x y
      (exactInputs t s remainder i) := by
  dsimp
  intro i
  fin_cases i <;> simp [inputs,
    ChapterVIDRadialTailBaseCenteredAffineTrace.inputModels, exactInputs]
  · exact pModel_contains_any_angular row radial hs _
  · exact tModel_contains_any_radial side row angular t ht _
  · exact remainderModel_contains hrem _ _
  · convert ChapterVIDRadialTailBaseConstantTrace.qdot_contains
      ((s - radialCenter row radial) / radialHalfWidth row radial)
      (((t : ℝ) - angularCenter side row angular) / angularHalfWidth side row angular) using 1 <;>
        push_cast <;> ring
  · convert ChapterVIDRadialTailBaseConstantTrace.cdot_contains _ _
      (normalized_radial_bound row radial hs) (normalized_angular_bound side row angular ht) using 1 <;>
        push_cast <;> ring
  · exact imaginaryUnit_contains _ _
  · exact ChapterVIDRadialTailBaseConstantTrace.collisionModel_contains _ _
  · exact ChapterVIDRadialTailBaseConstantTrace.collisionInv_contains _ _
      (normalized_radial_bound row radial hs) (normalized_angular_bound side row angular ht)
  · exact ChapterVIDRadialTailBaseConstantTrace.collisionSq_contains _ _
      (normalized_radial_bound row radial hs) (normalized_angular_bound side row angular ht)
  · simpa [collisionLift_inv_pow_three] using
      ChapterVIDRadialTailBaseConstantTrace.collisionInvCube_contains _ _
        (normalized_radial_bound row radial hs) (normalized_angular_bound side row angular ht)
  · simpa [inv_pow] using
      ChapterVIDRadialTailBaseConstantTrace.collisionInvFourth_contains _ _
        (normalized_radial_bound row radial hs) (normalized_angular_bound side row angular ht)
  · simpa [chapterVIDY_eq_ofReal] using
      ChapterVIDRadialTailBaseConstantTrace.yBase_contains
        ((s - radialCenter row radial) / radialHalfWidth row radial)
        (((t : ℝ) - angularCenter side row angular) / angularHalfWidth side row angular)
  · exact zetaBase_contains _ _
  all_goals exact zero_contains 40 _ _

theorem argument_norm_le_one_third
    (side : ChapterVIDPinchingArcSide) (row : Fin 6) (radial : Fin 16)
    (angular : Fin (angularCells side row)) {s : ℝ} (t : I)
    (hs : s ∈ Icc (radialStart row radial : ℝ) (radialEnd row radial : ℝ))
    (ht : (t : ℝ) ∈ Icc (angularStart side row angular : ℝ)
      (angularEnd side row angular : ℝ)) :
    ‖exactArgument side t s‖ ≤ 1 / 3 := by
  let x : ℝ := (s - radialCenter row radial) / radialHalfWidth row radial
  let y : ℝ := ((t : ℝ) - angularCenter side row angular) / angularHalfWidth side row angular
  have hx : |x| ≤ 1 := normalized_radial_bound row radial hs
  have hy : |y| ≤ 1 := normalized_angular_bound side row angular ht
  have hprogram := ProgramTrace.outputs_contain_of_allSound hx hy
    (all_operations_sound side row radial angular)
    (inputs_contain side row radial angular t hs ht (remainder := 0) (by norm_num)) 21
  have hargumentModel :
      ((ChapterVIDRadialTailBaseCenteredAffineTrace.trace side
        (inputs side row radial angular)).outputs 21).Contains x y
          (exactArgument side t s) := by
    rw [exactArgument_independent side t s 0] at hprogram
    simpa [ChapterVIDRadialTailBaseCenteredAffineTrace.trace] using hprogram
  have hrange : (cellArgument side row radial angular).Contains
      (exactArgument side t s) := by
    exact Model.range_contains hx hy hargumentModel
  have hnorm := (ChapterVILeanCompCertProposals.l1NormBound
    (cellArgument side row radial angular)).contains_norm hrange
  have hupper : ‖exactArgument side t s‖ ≤
      ((ChapterVILeanCompCertProposals.componentBudget
          (cellArgument side row radial angular).real +
        ChapterVILeanCompCertProposals.componentBudget
          (cellArgument side row radial angular).imag : ℤ) : ℝ) /
          ChapterVISignedDyadicInterval.scale 40 := by
    simpa [ChapterVILeanCompCertProposals.l1NormInterval,
      ChapterVISignedDyadicInterval.Contains,
      ChapterVISignedDyadicInterval.toRealInterval] using hnorm.2
  calc
    ‖exactArgument side t s‖ ≤ _ := hupper
    _ ≤ 1 / 3 := by
      rw [div_le_iff₀ (ChapterVISignedDyadicInterval.scale_pos 40)]
      have hbudget := all_argument_l1_bound side row radial angular
      have hbudgetReal :
          ((ChapterVILeanCompCertProposals.componentBudget
              (cellArgument side row radial angular).real +
            ChapterVILeanCompCertProposals.componentBudget
              (cellArgument side row radial angular).imag : ℤ) : ℝ) ≤
            366503875925 := by exact_mod_cast hbudget
      simp only [Int.cast_add] at hbudgetReal
      norm_num [ChapterVISignedDyadicInterval.scale]
      linarith

theorem output_contains_cell
    (side : ChapterVIDPinchingArcSide) (row : Fin 6) (radial : Fin 16)
    (angular : Fin (angularCells side row)) {s : ℝ} (t : I)
    (hs : s ∈ Icc (radialStart row radial : ℝ) (radialEnd row radial : ℝ))
    (ht : (t : ℝ) ∈ Icc (angularStart side row angular : ℝ)
      (angularEnd side row angular : ℝ)) :
    (cellOutput side row radial angular).Contains
      (chapterVIDRadialTailActualDerivative side t s) := by
  let st : I := ⟨s, by
    have hstart : 0 ≤ (radialStart row radial : ℝ) := by
      fin_cases row <;> fin_cases radial <;>
        norm_num [radialStart, rowStart, rowEnd, radialRow, chapterVICubicClusterNode]
    exact hstart.trans hs.1, by
    have hend : (radialEnd row radial : ℝ) ≤ 1 := by
      fin_cases row <;> fin_cases radial <;>
        norm_num [radialEnd, rowStart, rowEnd, radialRow, chapterVICubicClusterNode]
    exact hs.2.trans hend⟩
  let remainder := exactRemainder side t s
  have harg := argument_norm_le_one_third side row radial angular t hs ht
  have hrem : ‖remainder‖ ≤ (1 / 3 : ℝ) ^ 6 / 512 := by
    unfold remainder exactRemainder
    calc
      _ ≤ ‖exactArgument side t s‖ ^ 6 / 512 :=
        ChapterVILeanCompCertHighOrderAnomalyTrace.norm_exp_sub_expPolynomial_le
          (harg.trans (by norm_num))
      _ ≤ (1 / 3 : ℝ) ^ 6 / 512 := by gcongr
  let x : ℝ := (s - radialCenter row radial) / radialHalfWidth row radial
  let y : ℝ := ((t : ℝ) - angularCenter side row angular) / angularHalfWidth side row angular
  have hx : |x| ≤ 1 := normalized_radial_bound row radial hs
  have hy : |y| ≤ 1 := normalized_angular_bound side row angular ht
  have hprogram := ProgramTrace.outputs_contain_of_allSound hx hy
    (all_operations_sound side row radial angular)
    (inputs_contain side row radial angular t hs ht hrem) 52
  have hmodel :
      (ChapterVIDRadialTailBaseCenteredAffineTrace.output side
        (inputs side row radial angular)).Contains x y
          (chapterVIDRadialTailActualDerivative side t st) := by
    change ((ChapterVIDRadialTailBaseCenteredAffineTrace.trace side
      (inputs side row radial angular)).outputs 52).Contains x y
        (evalProgram (program side) (exactInputs t s remainder) 52) at hprogram
    rw [show s = (st : ℝ) by rfl,
      show remainder = exactRemainder side t st by rfl,
      evalProgram_eq_actualDerivative] at hprogram
    simpa [ChapterVIDRadialTailBaseCenteredAffineTrace.output] using hprogram
  exact Model.range_contains hx hy hmodel

theorem exists_radial_row {s : I}
    (hprefix : (ChapterVIDPinchingArcPrefixCompiledGrid.prefixEnd : ℝ) ≤ (s : ℝ)) :
    ∃ row : Fin 6, (rowStart row : ℝ) ≤ (s : ℝ) ∧ (s : ℝ) ≤ rowEnd row := by
  rcases exists_mem_adjacent_node_interval
      (fun i ↦ (chapterVICubicClusterNode 28 (i + 22) : ℝ)) 6 (by norm_num)
      (by
        intro i j hij
        change ((chapterVICubicClusterNode 28 (i + 22) : ℚ) : ℝ) ≤
          ((chapterVICubicClusterNode 28 (j + 22) : ℚ) : ℝ)
        exact_mod_cast monotone_chapterVICubicClusterNode (by norm_num : 0 < 28)
          (by omega : i + 22 ≤ j + 22))
      (by simpa [ChapterVIDPinchingArcPrefixCompiledGrid.prefixEnd,
        ChapterVIDPinchingArcPrefixCompiledGrid.radialIndex] using hprefix)
      (by simpa using s.property.2) with ⟨i, hi, hlo, hup⟩
  exact ⟨⟨i, hi⟩, by simpa [rowStart, radialRow] using hlo,
    by simpa [rowEnd, radialRow] using hup⟩

theorem exists_radial_subcell (row : Fin 6) {s : ℝ}
    (hs : s ∈ Icc (rowStart row : ℝ) (rowEnd row : ℝ)) :
    ∃ radial : Fin 16,
      s ∈ Icc (radialStart row radial : ℝ) (radialEnd row radial : ℝ) := by
  let node : ℕ → ℝ := fun i ↦
    (rowStart row : ℝ) + ((rowEnd row : ℝ) - rowStart row) * i / 16
  have hrow : (rowStart row : ℝ) ≤ rowEnd row := by
    fin_cases row <;> norm_num [rowStart, rowEnd, radialRow, chapterVICubicClusterNode]
  rcases exists_mem_adjacent_node_interval node 16 (by norm_num)
      (by
        intro i j hij
        dsimp [node]
        gcongr)
      (by simpa [node] using hs.1) (by simpa [node] using hs.2) with
    ⟨i, hi, hlo, hup⟩
  exact ⟨⟨i, hi⟩, by
    simpa [radialStart, radialEnd, node] using And.intro hlo hup⟩

theorem exists_angular_cell (side : ChapterVIDPinchingArcSide) (row : Fin 6) (t : I) :
    ∃ angular : Fin (angularCells side row),
      (t : ℝ) ∈ Icc (angularStart side row angular : ℝ)
        (angularEnd side row angular : ℝ) := by
  let cells := angularCells side row
  let node : ℕ → ℝ := fun i ↦ (i : ℝ) ^ 2 / cells ^ 2
  have hcells : 0 < cells := by
    cases side <;> fin_cases row <;> norm_num [cells, angularCells]
  rcases exists_mem_adjacent_node_interval node cells hcells
      (by
        intro i j hij
        dsimp [node]
        gcongr)
      (by simp [node]; exact t.property.1)
      (by simp [node, hcells.ne']; exact t.property.2) with ⟨i, hi, hlo, hup⟩
  exact ⟨⟨i, hi⟩, by simpa [angularStart, angularEnd, node, cells] using And.intro hlo hup⟩

theorem derivative_re_neg
    (side : ChapterVIDPinchingArcSide) (t s : I)
    (hprefix : (ChapterVIDPinchingArcPrefixCompiledGrid.prefixEnd : ℝ) < (s : ℝ))
    (_hpre : (s : ℝ) < 1) :
    (chapterVIDRadialTailActualDerivative side t s).re < 0 := by
  rcases exists_radial_row hprefix.le with ⟨row, hrow⟩
  rcases exists_radial_subcell row hrow with ⟨radial, hs⟩
  rcases exists_angular_cell side row t with ⟨angular, ht⟩
  have hcontains := output_contains_cell side row radial angular t hs ht
  have hupper := all_output_upper_negative side row radial angular
  have hscale := ChapterVISignedDyadicInterval.scale_pos 40
  have hrealUpper := hcontains.1.2
  exact hrealUpper.trans_lt (div_neg_of_neg_of_pos (by exact_mod_cast hupper) hscale)

end ChapterVIDRadialTailCenteredCertificate
end PoincareChapterVI
