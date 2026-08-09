/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.ChapterVIDConnectorFactorBulkCompiled
import PoincareChapterVI.ChapterVIDConnectorFactorDerivativeCompiled
import PoincareChapterVI.ChapterVIDEndpointAnchor

/-!
# Joining the compiled connector-factor monotonicity campaigns

The direct factor table leaves a 261-cell endpoint collar on each connector.  The first-order
campaign covers 240 initial and 252 final cells of that collar, while the curvature campaign and
the inverse-Morse endpoint anchors cover the remaining 21 initial and nine final cells.  This file
joins those two finite campaigns into statements about every point of the literal one-dimensional
connector path.
-/

noncomputable section

open Set
open scoped unitInterval

namespace PoincareChapterVI
namespace ChapterVIDConnectorFactorMonotonicity

open ChapterVIDConnectorFactorBulkReference
open ChapterVIDConnectorSeamCompiledGrid

/-- The portion of the endpoint collar covered directly by the first-derivative artifacts. -/
def derivativeInterval : ChapterVIDOuterArcSide → Set ℝ
  | .initial => Set.Ico (763 / 1024 : ℝ) (1003 / 1024 : ℝ)
  | .final => Set.Ioc (9 / 1024 : ℝ) (261 / 1024 : ℝ)

/-- Every point in `derivativeInterval` belongs to one of the 492 first-order compiled cells. -/
theorem exists_derivative_cell
    (side : ChapterVIDOuterArcSide) (t : I)
    (ht : (t : ℝ) ∈ derivativeInterval side) :
    ∃ index : Fin (ChapterVIDConnectorFactorDerivativeReference.cells side),
      (0, t) ∈ meshRegion
        (ChapterVIDConnectorFactorDerivativeReference.meshIndex side index) := by
  let raw := rawMeshIndex t
  have hrawMem := rawMeshIndex_mem t
  cases side with
  | initial =>
      by_cases hendpoint : (t : ℝ) = (763 / 1024 : ℝ)
      · let index : Fin (ChapterVIDConnectorFactorDerivativeReference.cells (.initial)) :=
            ⟨0, by norm_num [ChapterVIDConnectorFactorDerivativeReference.cells]⟩
        refine ⟨index, ?_⟩
        constructor
        · rfl
        · norm_num [meshRegion, ChapterVIDConnectorFactorDerivativeReference.meshIndex,
            chapterVIUnitGridCell, hendpoint]
      · have hlower : 763 ≤ raw.val := by
          rcases hrawMem with ⟨_, hrawUpper⟩
          have hsucc : raw.val + 1 ≤ 1024 := by
            have hi := raw.isLt
            change raw.val < 1024 at hi
            omega
          rw [min_eq_left hsucc] at hrawUpper
          change (t : ℝ) ≤ ((raw.val + 1 : ℕ) : ℝ) / 1024 at hrawUpper
          have htLower : (763 : ℝ) / 1024 < (t : ℝ) := by
            exact lt_of_le_of_ne ht.1 (Ne.symm hendpoint)
          by_contra h
          have hrawReal : ((raw.val + 1 : ℕ) : ℝ) ≤ 763 := by
            exact_mod_cast (show raw.val + 1 ≤ 763 by omega)
          nlinarith
        have hupper : raw.val < 1003 := by
          rcases hrawMem with ⟨hrawLower, _⟩
          change (raw.val : ℝ) / 1024 ≤ (t : ℝ) at hrawLower
          have htUpper : (t : ℝ) < (1003 : ℝ) / 1024 := by
            simpa [derivativeInterval] using ht.2
          by_contra h
          have hrawReal : (1003 : ℝ) ≤ raw.val := by
            exact_mod_cast (show 1003 ≤ raw.val by omega)
          nlinarith
        let index : Fin (ChapterVIDConnectorFactorDerivativeReference.cells (.initial)) :=
            ⟨raw.val - 763, by
          simp only [ChapterVIDConnectorFactorDerivativeReference.cells]
          omega⟩
        refine ⟨index, ?_⟩
        constructor
        · rfl
        · change t ∈ chapterVIUnitGridCell 1023
            ⟨(ChapterVIDConnectorFactorDerivativeReference.meshIndex .initial index).val, _⟩
          convert hrawMem using 1
          congr 1
          apply Fin.ext
          change raw.val - 763 + 763 = raw.val
          omega
  | final =>
      by_cases hendpoint : (t : ℝ) = (261 / 1024 : ℝ)
      · let index : Fin (ChapterVIDConnectorFactorDerivativeReference.cells (.final)) :=
            ⟨251, by
          norm_num [ChapterVIDConnectorFactorDerivativeReference.cells]⟩
        refine ⟨index, ?_⟩
        constructor
        · rfl
        · norm_num [meshRegion, ChapterVIDConnectorFactorDerivativeReference.meshIndex,
            chapterVIUnitGridCell,
            hendpoint]
      · have htUpper : (t : ℝ) < (261 : ℝ) / 1024 := by
          have := ht.2
          simpa [derivativeInterval] using lt_of_le_of_ne this hendpoint
        have hlower : 9 ≤ raw.val := by
          rcases hrawMem with ⟨_, hrawUpper⟩
          have hsucc : raw.val + 1 ≤ 1024 := by
            have hi := raw.isLt
            change raw.val < 1024 at hi
            omega
          rw [min_eq_left hsucc] at hrawUpper
          change (t : ℝ) ≤ ((raw.val + 1 : ℕ) : ℝ) / 1024 at hrawUpper
          have htLower : (9 : ℝ) / 1024 < (t : ℝ) := by
            simpa [derivativeInterval] using ht.1
          by_contra h
          have hrawLe : raw.val ≤ 8 := by omega
          have hrawReal : ((raw.val + 1 : ℕ) : ℝ) ≤ 9 := by exact_mod_cast (show raw.val + 1 ≤ 9 by omega)
          nlinarith
        have hupper : raw.val < 261 := by
          rcases hrawMem with ⟨hrawLower, _⟩
          change (raw.val : ℝ) / 1024 ≤ (t : ℝ) at hrawLower
          by_contra h
          have hrawGe : 261 ≤ raw.val := by omega
          have hrawReal : (261 : ℝ) ≤ raw.val := by exact_mod_cast hrawGe
          nlinarith
        let index : Fin (ChapterVIDConnectorFactorDerivativeReference.cells (.final)) :=
            ⟨raw.val - 9, by
          simp only [ChapterVIDConnectorFactorDerivativeReference.cells]
          omega⟩
        refine ⟨index, ?_⟩
        constructor
        · rfl
        · have hindex : ChapterVIDConnectorFactorDerivativeReference.meshIndex
              .final index = raw := by
            apply Fin.ext
            change raw.val - 9 + 9 = raw.val
            omega
          change t ∈ chapterVIUnitGridCell 1023
            ⟨(ChapterVIDConnectorFactorDerivativeReference.meshIndex .final index).val, _⟩
          convert hrawMem using 1
          congr 1
          apply Fin.ext
          change raw.val - 9 + 9 = raw.val
          omega

/-- A passing first-order campaign gives the literal positive path derivative on its whole
492-cell region. -/
theorem derivativeLineDerivativeImag_pos_on_interval
    {massProduct : ℂ} {b d : ℤ}
    (run : ChapterVIDConnectorFactorDerivativeReference.ReferenceCompiledRunVerdict)
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) (t : I)
    (ht : (t : ℝ) ∈ derivativeInterval side) :
    0 < ChapterVIDConnectorFactorTerminal.lineDerivativeImag model side (t : ℝ) := by
  obtain ⟨index, hregion⟩ := exists_derivative_cell side t ht
  have hchecked := run.modelLineImag_hasDerivAt_and_pos model side index 0 t hregion
  simpa [ChapterVIDConnectorFactorTerminal.lineDerivativeImag,
    chapterVIDRootCoordinateCollisionFactorPlusLineDerivativeImag,
    ChapterVIDPrincipalConnectorModel.rectanglePoint,
    ChapterVIDPrincipalGlobalRootModel.connectorPoint] using hchecked.2

/-- The first-order campaign keeps the actual companion factor in the positive real half-plane
on its whole 492-cell region. -/
theorem derivativeCompanion_re_pos_on_interval
    {massProduct : ℂ} {b d : ℤ}
    (run : ChapterVIDConnectorFactorDerivativeReference.ReferenceCompiledRunVerdict)
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) (t : I)
    (ht : (t : ℝ) ∈ derivativeInterval side) :
    0 < (model.rectangleFactorMinus side (connectorPathPoint model t)).re := by
  obtain ⟨index, hregion⟩ := exists_derivative_cell side t ht
  simpa [connectorPathPoint] using
    run.modelCompanion_re_pos model side index (0, t) hregion

/-- The entire 261-cell collar omitted by the direct factor table. -/
def collarInterval : ChapterVIDOuterArcSide → Set ℝ
  | .initial => Set.Icc (763 / 1024 : ℝ) 1
  | .final => Set.Icc 0 (261 / 1024 : ℝ)

def collarBoundaryParameter : ChapterVIDOuterArcSide → I
  | .initial => ⟨763 / 1024, by norm_num⟩
  | .final => ⟨261 / 1024, by norm_num⟩

def collarBoundaryIndex : ChapterVIDOuterArcSide → Fin meshCells
  | .initial => ⟨763, by norm_num [meshCells]⟩
  | .final => ⟨261, by norm_num [meshCells]⟩

theorem collarBoundary_mem_cell
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) :
    connectorPathPoint model (collarBoundaryParameter side) ∈
      (cell model side (collarBoundaryIndex side)).region := by
  rw [cell_region]
  cases side <;>
    norm_num [collarBoundaryParameter, collarBoundaryIndex, connectorPathPoint,
      retainedMeshIndex, initialLastMeshIndex, finalFirstMeshIndex, meshRegion,
      chapterVIUnitGridCell]

theorem collarBoundary_plus_label (side : ChapterVIDOuterArcSide) :
    plusSeparation side (collarBoundaryIndex side) = outerPlusSeparation side := by
  cases side <;> decide +kernel

theorem terminal_or_derivative
    (side : ChapterVIDOuterArcSide) {x : ℝ}
    (hx : x ∈ collarInterval side) :
    x ∈ ChapterVIDConnectorFactorTerminal.terminalInterval side ∨
      x ∈ derivativeInterval side := by
  cases side with
  | initial =>
      by_cases hterminal : (1003 / 1024 : ℝ) ≤ x
      · left
        simpa [ChapterVIDConnectorFactorTerminal.terminalInterval] using ⟨hterminal, hx.2⟩
      · right
        simpa [derivativeInterval] using ⟨hx.1, lt_of_not_ge hterminal⟩
  | final =>
      by_cases hterminal : x ≤ (9 / 1024 : ℝ)
      · left
        simpa [ChapterVIDConnectorFactorTerminal.terminalInterval] using ⟨hx.1, hterminal⟩
      · right
        simpa [derivativeInterval] using ⟨lt_of_not_ge hterminal, hx.2⟩

/-- The 41 first-order shards, ten curvature shards, and the proved endpoint anchors combine to
give a positive imaginary derivative at every non-endpoint point of the omitted collar. -/
theorem collarLineDerivativeImag_pos
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDAnchoredConnectorModel massProduct b d)
    (derivativeRun :
      ChapterVIDConnectorFactorDerivativeReference.ReferenceCompiledRunVerdict)
    (curvatureRun :
      ChapterVIDConnectorFactorSecondDerivativeReference.ReferenceCompiledRunVerdict)
    (side : ChapterVIDOuterArcSide) (t : I)
    (ht : (t : ℝ) ∈ collarInterval side)
    (hne : t ≠ localParameter side) :
    0 < ChapterVIDConnectorFactorTerminal.lineDerivativeImag
      model.toChapterVIDPrincipalConnectorModel side (t : ℝ) := by
  rcases terminal_or_derivative side ht with hterminal | hderivative
  · apply model.terminalLineDerivativeImag_pos curvatureRun side (t : ℝ) hterminal
    intro heq
    apply hne
    exact Subtype.ext heq
  · exact derivativeLineDerivativeImag_pos_on_interval derivativeRun
      model.toChapterVIDPrincipalConnectorModel side t hderivative

/-- Imaginary part of the vanishing factor along the literal `s = 0` connector path. -/
def lineImag
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) : ℝ → ℝ :=
  chapterVIDRootCoordinateCollisionFactorPlusLineImag
    (model.connectorParameterRoot 0)
    (model.rootModel.connectorSource side (model.criticalValue 0))
    (model.rootModel.connectorTarget side (model.criticalValue 0))

/-- The direct factor campaign supplies the outer-oriented imaginary sign at the boundary where
the monotonicity campaigns begin. -/
theorem collarBoundary_lineImag_oriented
    {massProduct : ℂ} {b d : ℤ}
    (run : ChapterVIDConnectorFactorBulkReference.ReferenceCompiledRunVerdict)
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) :
    match side with
    | .initial => lineImag model side (collarBoundaryParameter side : ℝ) < 0
    | .final => 0 < lineImag model side (collarBoundaryParameter side : ℝ) := by
  have hfacts := run.cell_facts model side (collarBoundaryIndex side)
    (connectorPathPoint model (collarBoundaryParameter side))
    (collarBoundary_mem_cell model side)
  have hplus := hfacts.1
  rw [collarBoundary_plus_label] at hplus
  cases side with
  | initial =>
      have hline : 0 < -(lineImag model .initial
          (collarBoundaryParameter .initial : ℝ)) := by
        simpa [lineImag, chapterVIDRootCoordinateCollisionFactorPlusLineImag,
          connectorPathPoint,
          ChapterVIDPrincipalConnectorModel.rectangleFactorPlus,
          ChapterVIDPrincipalConnectorModel.rectanglePoint,
          ChapterVIDPrincipalGlobalRootModel.connectorPoint,
          outerPlusSeparation, SlitPlaneSeparation.value,
          SlitPlaneSeparation.toZeroSeparation,
          ChapterVIComplexZeroSeparation.value] using hplus
      linarith
  | final =>
      simpa [lineImag, chapterVIDRootCoordinateCollisionFactorPlusLineImag,
        connectorPathPoint,
        ChapterVIDPrincipalConnectorModel.rectangleFactorPlus,
        ChapterVIDPrincipalConnectorModel.rectanglePoint,
        ChapterVIDPrincipalGlobalRootModel.connectorPoint,
        outerPlusSeparation, SlitPlaneSeparation.value,
        SlitPlaneSeparation.toZeroSeparation,
        ChapterVIComplexZeroSeparation.value] using hplus

theorem collarInterval_subset_unit (side : ChapterVIDOuterArcSide) :
    collarInterval side ⊆ Set.Icc (0 : ℝ) 1 := by
  intro x hx
  cases side <;> norm_num [collarInterval] at hx ⊢ <;> constructor <;> linarith

theorem convex_collarInterval (side : ChapterVIDOuterArcSide) :
    Convex ℝ (collarInterval side) := by
  cases side <;> exact convex_Icc _ _

theorem hasDerivAt_lineImag
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    HasDerivAt (lineImag model side)
      (ChapterVIDConnectorFactorTerminal.lineDerivativeImag model side x) x := by
  let t : I := ⟨x, hx⟩
  have hcoordinate := model.rectanglePoint_ne_zero side (0, t)
  have hderiv := hasDerivAt_chapterVIDRootCoordinateCollisionFactorPlusLineImag
    (model.connectorParameterRoot_ne_zero 0)
    (by simpa [ChapterVIDPrincipalConnectorModel.rectanglePoint,
      ChapterVIDPrincipalGlobalRootModel.connectorPoint, t] using hcoordinate)
  simpa [lineImag, ChapterVIDConnectorFactorTerminal.lineDerivativeImag,
    chapterVIDRootCoordinateCollisionFactorPlusLineDerivativeImag] using hderiv

theorem continuousOn_lineImag
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) :
    ContinuousOn (lineImag model side) (collarInterval side) := by
  intro x hx
  exact (hasDerivAt_lineImag model side (collarInterval_subset_unit side hx)).continuousAt.continuousWithinAt

/-- The assembled finite campaigns prove that the vanishing factor's imaginary part is strictly
increasing across the whole formerly-unresolved collar.  In particular it can meet the real axis
at most once there. -/
theorem strictMonoOn_collarLineImag
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDAnchoredConnectorModel massProduct b d)
    (derivativeRun :
      ChapterVIDConnectorFactorDerivativeReference.ReferenceCompiledRunVerdict)
    (curvatureRun :
      ChapterVIDConnectorFactorSecondDerivativeReference.ReferenceCompiledRunVerdict)
    (side : ChapterVIDOuterArcSide) :
    StrictMonoOn (lineImag model.toChapterVIDPrincipalConnectorModel side)
      (collarInterval side) := by
  apply strictMonoOn_of_deriv_pos (convex_collarInterval side)
    (continuousOn_lineImag model.toChapterVIDPrincipalConnectorModel side)
  intro x hx
  have hxCollar : x ∈ collarInterval side := interior_subset hx
  let t : I := ⟨x, collarInterval_subset_unit side hxCollar⟩
  have htNe : t ≠ localParameter side := by
    intro heq
    have hval := congrArg Subtype.val heq
    cases side with
    | initial =>
        have hxOpen : x ∈ Set.Ioo (763 / 1024 : ℝ) 1 := by
          simpa [collarInterval] using hx
        norm_num [localParameter, t] at hval
        exact (ne_of_lt hxOpen.2) hval
    | final =>
        have hxOpen : x ∈ Set.Ioo (0 : ℝ) (261 / 1024 : ℝ) := by
          simpa [collarInterval] using hx
        norm_num [localParameter, t] at hval
        exact (ne_of_gt hxOpen.1) hval
  have hderiv := hasDerivAt_lineImag
    model.toChapterVIDPrincipalConnectorModel side
    (collarInterval_subset_unit side hxCollar)
  rw [hderiv.deriv]
  exact collarLineDerivativeImag_pos model derivativeRun curvatureRun side t hxCollar htNe

/-- Both compiled campaigns keep the companion factor in the positive real half-plane throughout
the complete closed collar. -/
theorem companion_re_pos_on_collar
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (derivativeRun :
      ChapterVIDConnectorFactorDerivativeReference.ReferenceCompiledRunVerdict)
    (curvatureRun :
      ChapterVIDConnectorFactorSecondDerivativeReference.ReferenceCompiledRunVerdict)
    (side : ChapterVIDOuterArcSide) (t : I)
    (ht : (t : ℝ) ∈ collarInterval side) :
    0 < (model.rectangleFactorMinus side (connectorPathPoint model t)).re := by
  rcases terminal_or_derivative side ht with hterminal | hderivative
  · have htEq : ChapterVIDConnectorFactorTerminal.terminalParameter
        side (t : ℝ) hterminal = t := Subtype.ext rfl
    simpa [connectorPathPoint, htEq] using
      ChapterVIDConnectorFactorTerminal.ReferenceCompiledRunVerdict.modelCompanion_re_pos_on_terminal
        curvatureRun model side (t : ℝ) hterminal
  · exact derivativeCompanion_re_pos_on_interval
      derivativeRun model side t hderivative

end ChapterVIDConnectorFactorMonotonicity
end PoincareChapterVI
