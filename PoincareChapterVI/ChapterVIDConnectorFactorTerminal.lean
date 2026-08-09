/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import PoincareChapterVI.ChapterVIDConnectorFactorSecondDerivativeCompiled

/-!
# Calculus join for the terminal connector certificates

The compiled second-derivative campaign covers the last 21 initial cells and the first nine
final cells.  This file turns its cellwise curvature signs into a sign for the first path
derivative, conditional only on the corresponding derivative value at the local endpoint.
The endpoint condition is deliberately isolated: it is the remaining inverse-Morse analytic
obligation and is not smuggled into a compiled receipt.
-/

noncomputable section

open Set
open scoped unitInterval

namespace PoincareChapterVI
namespace ChapterVIDConnectorFactorTerminal

open ChapterVIDConnectorFactorBulkReference
open ChapterVIDConnectorFactorSecondDerivativeReference
open ChapterVIDConnectorSeamCompiledGrid

/-- Closed real interval covered by the terminal curvature campaign. -/
def terminalInterval : ChapterVIDOuterArcSide → Set ℝ
  | .initial => Set.Icc (1003 / 1024 : ℝ) 1
  | .final => Set.Icc 0 (9 / 1024 : ℝ)

theorem convex_terminalInterval (side : ChapterVIDOuterArcSide) :
    Convex ℝ (terminalInterval side) := by
  cases side <;> exact convex_Icc _ _

/-- A real point in the terminal interval, regarded as a unit-interval parameter. -/
def terminalParameter (side : ChapterVIDOuterArcSide)
    (x : ℝ) (hx : x ∈ terminalInterval side) : I :=
  ⟨x, by
    cases side with
    | initial =>
        simpa [terminalInterval] using And.intro (le_trans (by norm_num) hx.1) hx.2
    | final =>
        simpa [terminalInterval] using And.intro hx.1 (le_trans hx.2 (by norm_num))⟩

@[simp] theorem terminalParameter_val (side : ChapterVIDOuterArcSide)
    (x : ℝ) (hx : x ∈ terminalInterval side) :
    (terminalParameter side x hx : ℝ) = x := rfl

/-- Every point of the closed terminal interval belongs to one of the 30 compiled cells. -/
theorem exists_terminal_cell
    (side : ChapterVIDOuterArcSide) (x : ℝ) (hx : x ∈ terminalInterval side) :
    ∃ index : Fin (cells side),
      (0, terminalParameter side x hx) ∈ meshRegion (meshIndex side index) := by
  let t := terminalParameter side x hx
  cases side with
  | initial =>
      let raw := rawMeshIndex t
      have hrawMem := rawMeshIndex_mem t
      have hrawLower : 1003 ≤ raw.val := by
        have hxLower : (1003 : ℝ) / 1024 ≤ x := by
          simpa [terminalInterval] using hx.1
        have hfloor : 1003 ≤ ⌊(1024 : ℝ) * x⌋₊ := by
          apply Nat.le_floor
          calc
            (1003 : ℝ) = 1024 * ((1003 : ℝ) / 1024) := by norm_num
            _ ≤ 1024 * x := mul_le_mul_of_nonneg_left hxLower (by norm_num)
        have hmin : 1003 ≤ min ⌊(1024 : ℝ) * x⌋₊ 1023 := by
          exact le_min hfloor (by norm_num)
        simpa [raw, rawMeshIndex, t, terminalParameter,
          chapterVIUnitGridIndex] using hmin
      let index : Fin (cells (.initial)) := ⟨raw.val - 1003, by
        have hrawLt := raw.isLt
        simp only [cells, meshCells] at hrawLt ⊢
        omega⟩
      refine ⟨index, ?_⟩
      constructor
      · rfl
      · have hindex : meshIndex .initial index = raw := by
          apply Fin.ext
          simp [meshIndex, index, hrawLower]
        rw [hindex]
        exact hrawMem
  | final =>
      by_cases hxUpper : x = (9 / 1024 : ℝ)
      · let index : Fin (cells (.final)) := ⟨8, by norm_num [cells]⟩
        refine ⟨index, ?_⟩
        constructor
        · rfl
        · subst x
          norm_num [meshRegion, meshIndex, chapterVIUnitGridCell,
            terminalParameter, terminalInterval]
      · let raw := rawMeshIndex t
        have hrawMem := rawMeshIndex_mem t
        have hxUpper' : x < (9 / 1024 : ℝ) := lt_of_le_of_ne hx.2 hxUpper
        have hrawLt : raw.val < 9 := by
          rcases hrawMem with ⟨hl, _⟩
          change (raw.val : ℝ) / 1024 ≤ x at hl
          have : (raw.val : ℝ) < 9 := by nlinarith
          exact_mod_cast this
        let index : Fin (cells (.final)) := ⟨raw.val, by
          simpa only [cells] using hrawLt⟩
        refine ⟨index, ?_⟩
        constructor
        · rfl
        · have hindex : meshIndex .final index = raw := by
            apply Fin.ext
            rfl
          simpa [hindex] using hrawMem

/-- The curvature campaign's companion-factor checks cover the whole closed terminal interval,
including the local endpoint. -/
theorem ReferenceCompiledRunVerdict.modelCompanion_re_pos_on_terminal
    {massProduct : ℂ} {b d : ℤ}
    (run : ReferenceCompiledRunVerdict)
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide)
    (x : ℝ) (hx : x ∈ terminalInterval side) :
    0 < (model.rectangleFactorMinus side
      (0, terminalParameter side x hx)).re := by
  obtain ⟨index, hregion⟩ := exists_terminal_cell side x hx
  exact run.modelCompanion_re_pos model side index _ hregion

/-- Imaginary part of the first factor's derivative along the seam connector (`s = 0`). -/
def lineDerivativeImag
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) : ℝ → ℝ :=
  chapterVIDRootCoordinateCollisionFactorPlusLineDerivativeImag
    (model.connectorParameterRoot 0)
    (model.rootModel.connectorSource side (model.criticalValue 0))
    (model.rootModel.connectorTarget side (model.criticalValue 0))

/-- The one analytic datum not supplied by the terminal compiled campaign. -/
structure EndpointDerivativeAnchor
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) : Prop where
  nonneg : 0 ≤ lineDerivativeImag model side (localParameter side : ℝ)

/-- On each point of the terminal interval, the compiled curvature is the derivative of the
actual first-path-derivative function and has the required orientation. -/
theorem ReferenceCompiledRunVerdict.hasDerivAt_lineDerivativeImag_and_oriented
    {massProduct : ℂ} {b d : ℤ}
    (run : ReferenceCompiledRunVerdict)
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide)
    (x : ℝ) (hx : x ∈ terminalInterval side) :
    ∃ curvature : ℝ,
      HasDerivAt (lineDerivativeImag model side) curvature x ∧
        match side with
        | .initial => curvature < 0
        | .final => 0 < curvature := by
  cases side with
  | initial =>
      obtain ⟨index, hregion⟩ := exists_terminal_cell .initial x hx
      have hchecked := run.modelLineDerivativeImag_hasDerivAt_and_oriented
        model .initial index 0 (terminalParameter .initial x hx) hregion
      refine ⟨_, ?_, hchecked.2⟩
      simpa only [lineDerivativeImag, terminalParameter_val] using hchecked.1
  | final =>
      obtain ⟨index, hregion⟩ := exists_terminal_cell .final x hx
      have hchecked := run.modelLineDerivativeImag_hasDerivAt_and_oriented
        model .final index 0 (terminalParameter .final x hx) hregion
      refine ⟨_, ?_, hchecked.2⟩
      simpa only [lineDerivativeImag, terminalParameter_val] using hchecked.1

theorem ReferenceCompiledRunVerdict.continuousOn_lineDerivativeImag
    {massProduct : ℂ} {b d : ℤ}
    (run : ReferenceCompiledRunVerdict)
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) :
    ContinuousOn (lineDerivativeImag model side) (terminalInterval side) := by
  intro x hx
  obtain ⟨curvature, hderiv, _⟩ :=
    ReferenceCompiledRunVerdict.hasDerivAt_lineDerivativeImag_and_oriented
      run model side x hx
  exact hderiv.continuousAt.continuousWithinAt

/-- The initial terminal derivative decreases toward its local endpoint. -/
theorem ReferenceCompiledRunVerdict.strictAntiOn_initial_lineDerivativeImag
    {massProduct : ℂ} {b d : ℤ}
    (run : ReferenceCompiledRunVerdict)
    (model : ChapterVIDPrincipalConnectorModel massProduct b d) :
    StrictAntiOn (lineDerivativeImag model .initial) (terminalInterval .initial) := by
  apply strictAntiOn_of_deriv_neg (convex_terminalInterval .initial)
    (ReferenceCompiledRunVerdict.continuousOn_lineDerivativeImag run model .initial)
  intro x hx
  have hx' : x ∈ terminalInterval .initial := interior_subset hx
  obtain ⟨curvature, hderiv, hneg⟩ :=
    ReferenceCompiledRunVerdict.hasDerivAt_lineDerivativeImag_and_oriented
      run model .initial x hx'
  rw [hderiv.deriv]
  exact hneg

/-- The final terminal derivative increases away from its local endpoint. -/
theorem ReferenceCompiledRunVerdict.strictMonoOn_final_lineDerivativeImag
    {massProduct : ℂ} {b d : ℤ}
    (run : ReferenceCompiledRunVerdict)
    (model : ChapterVIDPrincipalConnectorModel massProduct b d) :
    StrictMonoOn (lineDerivativeImag model .final) (terminalInterval .final) := by
  apply strictMonoOn_of_deriv_pos (convex_terminalInterval .final)
    (ReferenceCompiledRunVerdict.continuousOn_lineDerivativeImag run model .final)
  intro x hx
  have hx' : x ∈ terminalInterval .final := interior_subset hx
  obtain ⟨curvature, hderiv, hpos⟩ :=
    ReferenceCompiledRunVerdict.hasDerivAt_lineDerivativeImag_and_oriented
      run model .final x hx'
  rw [hderiv.deriv]
  exact hpos

/-- Once the inverse-Morse endpoint supplies a nonnegative derivative anchor, all non-endpoint
points in the 30 terminal cells have strictly positive first path derivative. -/
theorem ReferenceCompiledRunVerdict.lineDerivativeImag_pos_of_anchor
    {massProduct : ℂ} {b d : ℤ}
    (run : ReferenceCompiledRunVerdict)
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide)
    (anchor : EndpointDerivativeAnchor model side)
    (x : ℝ) (hx : x ∈ terminalInterval side)
    (hne : x ≠ (localParameter side : ℝ)) :
    0 < lineDerivativeImag model side x := by
  cases side with
  | initial =>
      have hxlt : x < 1 := lt_of_le_of_ne hx.2 hne
      have hend : (1 : ℝ) ∈ terminalInterval (.initial) := by
        norm_num [terminalInterval]
      have hstrict :=
        ReferenceCompiledRunVerdict.strictAntiOn_initial_lineDerivativeImag
          run model hx hend hxlt
      exact anchor.nonneg.trans_lt hstrict
  | final =>
      have hxgt : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hne)
      have hend : (0 : ℝ) ∈ terminalInterval (.final) := by
        norm_num [terminalInterval]
      have hstrict :=
        ReferenceCompiledRunVerdict.strictMonoOn_final_lineDerivativeImag
          run model hend hx hxgt
      exact anchor.nonneg.trans_lt hstrict

end ChapterVIDConnectorFactorTerminal
end PoincareChapterVI
