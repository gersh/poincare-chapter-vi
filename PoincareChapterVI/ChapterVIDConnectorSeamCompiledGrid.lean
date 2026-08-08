/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.ChapterVIDConnectorCompiledGrid
import PoincareChapterVI.ChapterVILeanCompCertAttestation
import Mathlib.Analysis.RCLike.Sqrt

/-!
# Compiled branch-cut certificates for the D connector seams

Nonvanishing of a connector radicand produces a square-root sheet, but does not determine the
sign with which an outer-normalized sheet reaches the local Morse boundary.  Connectedness
reduces that question to the single path with critical-value parameter `s = 0`.

This file gives a LeanCompCert-facing certificate for that path.  Each interval cell proves one
of three strict signed bounds on the computed radicand rectangle: positive real part, positive
imaginary part, or negative imaginary part.  Their union is the domain on which Mathlib's
principal complex square root is continuous.  Consequently a successful compiled batch proves
that continuation of the outer principal root reaches the positive local Morse root.

The compiled computation checks only signed fixed-point arithmetic and strict integer bounds.
The cell cover, interval-containment bridge, continuity argument, and square-root uniqueness are
ordinary Lean theorems.
-/

noncomputable section

open Set Topology
open scoped unitInterval

namespace PoincareChapterVI

namespace ChapterVIDConnectorSeamCompiledGrid

open ChapterVILeanCompCertBatch
open ChapterVILeanCompCertAttestation
open LeanCompCert.Ports.SignedProductClaims
open ChapterVIDConnectorCompiledGrid

/-- The three rectangle positions that avoid the branch cut of the principal square root. -/
inductive SlitPlaneSeparation
  | realPositive
  | imagPositive
  | imagNegative
  deriving DecidableEq, Repr

namespace SlitPlaneSeparation

def toZeroSeparation : SlitPlaneSeparation → ChapterVIComplexZeroSeparation
  | .realPositive => .realPositive
  | .imagPositive => .imagPositive
  | .imagNegative => .imagNegative

def interval {precision : ℕ}
    (separation : SlitPlaneSeparation)
    (rectangle : ChapterVISignedDyadicComplexRectangle precision) :
    ChapterVISignedDyadicInterval precision :=
  separation.toZeroSeparation.interval rectangle

def value (separation : SlitPlaneSeparation) (z : ℂ) : ℝ :=
  separation.toZeroSeparation.value z

theorem value_pos_of_lower_pos
    {precision : ℕ}
    (separation : SlitPlaneSeparation)
    {rectangle : ChapterVISignedDyadicComplexRectangle precision}
    {z : ℂ} (hz : rectangle.Contains z)
    (hlower : 0 < (separation.interval rectangle).lower) :
    0 < separation.value z := by
  have hcontains := separation.toZeroSeparation.interval_contains_value hz
  have hlowerReal : 0 <
      ((separation.interval rectangle).lower : ℝ) /
        ChapterVISignedDyadicInterval.scale precision :=
    div_pos (by exact_mod_cast hlower)
      (ChapterVISignedDyadicInterval.scale_pos precision)
  exact hlowerReal.trans_le hcontains.1

/-- A passing signed bound is precisely the pointwise hypothesis needed by
`Complex.continuousAt_sqrt`. -/
theorem sqrt_condition_of_lower_pos
    {precision : ℕ}
    (separation : SlitPlaneSeparation)
    {rectangle : ChapterVISignedDyadicComplexRectangle precision}
    {z : ℂ} (hz : rectangle.Contains z)
    (hlower : 0 < (separation.interval rectangle).lower) :
    0 ≤ z.re ∨ z.im ≠ 0 := by
  have hvalue := separation.value_pos_of_lower_pos hz hlower
  cases separation with
  | realPositive =>
      exact Or.inl hvalue.le
  | imagPositive =>
      exact Or.inr (by
        intro hzero
        simp [value, toZeroSeparation, ChapterVIComplexZeroSeparation.value, hzero] at hvalue)
  | imagNegative =>
      exact Or.inr (by
        intro hzero
        simp [value, toZeroSeparation, ChapterVIComplexZeroSeparation.value, hzero] at hvalue)

theorem ne_zero_of_lower_pos
    {precision : ℕ}
    (separation : SlitPlaneSeparation)
    {rectangle : ChapterVISignedDyadicComplexRectangle precision}
    {z : ℂ} (hz : rectangle.Contains z)
    (hlower : 0 < (separation.interval rectangle).lower) :
    z ≠ 0 := by
  have hvalue := separation.value_pos_of_lower_pos hz hlower
  intro hzero
  subst z
  cases separation <;>
    simp [value, toZeroSeparation, ChapterVIComplexZeroSeparation.value] at hvalue

theorem sqrt_condition_of_value_pos
    (separation : SlitPlaneSeparation) {z : ℂ}
    (hvalue : 0 < separation.value z) :
    0 ≤ z.re ∨ z.im ≠ 0 := by
  cases separation with
  | realPositive =>
      exact Or.inl (by
        simpa [value, toZeroSeparation, ChapterVIComplexZeroSeparation.value] using hvalue.le)
  | imagPositive =>
      exact Or.inr (by
        intro hzero
        simp [value, toZeroSeparation, ChapterVIComplexZeroSeparation.value, hzero] at hvalue)
  | imagNegative =>
      exact Or.inr (by
        intro hzero
        simp [value, toZeroSeparation, ChapterVIComplexZeroSeparation.value, hzero] at hvalue)

theorem ne_zero_of_value_pos
    (separation : SlitPlaneSeparation) {z : ℂ}
    (hvalue : 0 < separation.value z) : z ≠ 0 := by
  intro hzero
  subst z
  cases separation <;>
    simp [value, toZeroSeparation, ChapterVIComplexZeroSeparation.value] at hvalue

end SlitPlaneSeparation

/-- Principal square roots multiply without a sign change when the two principal arguments add
inside the principal argument interval. -/
theorem sqrt_mul_of_arg_add_mem
    {x y : ℂ} (hx : x ≠ 0) (hy : y ≠ 0)
    (harg : Complex.arg x + Complex.arg y ∈ Set.Ioc (-Real.pi) Real.pi) :
    Complex.sqrt (x * y) = Complex.sqrt x * Complex.sqrt y := by
  rw [sqrt_eq_exp (mul_ne_zero hx hy), sqrt_eq_exp hx,
    sqrt_eq_exp hy, Complex.log_mul hx hy harg, add_div,
    Complex.exp_add]

/-- Opposite open half-planes force the two arguments to add without crossing the principal
cut. -/
theorem arg_add_mem_Ioc_of_im_neg_pos
    {x y : ℂ} (hx : x.im < 0) (hy : 0 < y.im) :
    Complex.arg x + Complex.arg y ∈ Set.Ioc (-Real.pi) Real.pi := by
  have hxa : Complex.arg x < 0 := Complex.arg_neg_iff.mpr hx
  have hya : 0 ≤ Complex.arg y := Complex.arg_nonneg_iff.mpr hy.le
  exact ⟨by linarith [Complex.neg_pi_lt_arg x],
    by linarith [Complex.arg_le_pi y]⟩

theorem arg_add_mem_Ioc_of_im_pos_neg
    {x y : ℂ} (hx : 0 < x.im) (hy : y.im < 0) :
    Complex.arg x + Complex.arg y ∈ Set.Ioc (-Real.pi) Real.pi := by
  have hxa : 0 ≤ Complex.arg x := Complex.arg_nonneg_iff.mpr hx.le
  have hya : Complex.arg y < 0 := Complex.arg_neg_iff.mpr hy
  exact ⟨by linarith [Complex.neg_pi_lt_arg y],
    by linarith [Complex.arg_le_pi x]⟩

/-- If a product is strictly positive real and the second factor is in the right half-plane,
the principal arguments cancel exactly. -/
theorem arg_add_eq_zero_of_mul_re_pos_im_zero_of_right
    {x y : ℂ} (hprodRe : 0 < (x * y).re) (hprodIm : (x * y).im = 0)
    (hyRe : 0 < y.re) :
    Complex.arg x + Complex.arg y = 0 := by
  have hy : y ≠ 0 := by
    intro hzero
    subst y
    simp at hyRe
  have hprod : x * y = ((x * y).re : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using hprodIm
  have hxEq : x = ((x * y).re : ℂ) * y⁻¹ := by
    calc
      x = (x * y) * y⁻¹ := by field_simp
      _ = ((x * y).re : ℂ) * y⁻¹ := by
        exact congrArg (fun z : ℂ ↦ z * y⁻¹) hprod
  have hyArgNe : Complex.arg y ≠ Real.pi := by
    intro harg
    have hneg := Complex.arg_eq_pi_iff.mp harg
    linarith
  rw [hxEq, Complex.arg_real_mul _ hprodRe, Complex.arg_inv, if_neg hyArgNe]
  ring

theorem arg_add_mem_Ioc_of_mul_re_pos_im_zero_of_right
    {x y : ℂ} (hprodRe : 0 < (x * y).re) (hprodIm : (x * y).im = 0)
    (hyRe : 0 < y.re) :
    Complex.arg x + Complex.arg y ∈ Set.Ioc (-Real.pi) Real.pi := by
  rw [arg_add_eq_zero_of_mul_re_pos_im_zero_of_right hprodRe hprodIm hyRe]
  exact ⟨neg_lt_zero.mpr Real.pi_pos, Real.pi_pos.le⟩

/-- The one signed comparison attached to a seam-path cell. -/
def separationOperation {precision : ℕ}
    (rectangle : ChapterVISignedDyadicComplexRectangle precision)
    (separation : SlitPlaneSeparation) : DyadicOperation precision :=
  .positiveLower (separation.interval rectangle)

/-- Arithmetic for a connector cell followed by its branch-cut separation check. -/
def seamOperations
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide} {precision : ℕ}
    (cell : ChapterVIDConnectorCompiledGrid.Cell model side precision)
    (separation : SlitPlaneSeparation) :
    List (DyadicOperation precision) :=
  cell.coordinateOperations ++ cell.trace.operations ++
    [separationOperation cell.trace.output separation]

/-- The connector path at the single critical-value parameter needed to determine the seam
sign.  Its orientation is left unchanged; the outer endpoint is `0` on the initial connector and
`1` on the final connector. -/
def connectorPathPoint
    {massProduct : ℂ} {b d : ℤ}
    (_model : ChapterVIDPrincipalConnectorModel massProduct b d) (t : I) : I × I :=
  (0, t)

def outerParameter : ChapterVIDOuterArcSide → I
  | .initial => 0
  | .final => 1

def localParameter : ChapterVIDOuterArcSide → I
  | .initial => 1
  | .final => 0

@[simp] theorem connectorPathPoint_outer
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) :
    connectorPathPoint model (outerParameter side) = model.connectorBoundaryPoint side 0 := by
  cases side <;> rfl

@[simp] theorem connectorPathPoint_local
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) :
    connectorPathPoint model (localParameter side) =
      model.connectorLocalBoundaryPoint side 0 := by
  cases side <;> rfl

/-- A finite one-dimensional cover of the `s = 0` connector path. -/
structure SeamData
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) (precision cells : ℕ) where
  cell : Fin cells → ChapterVIDConnectorCompiledGrid.Cell model side precision
  separation : Fin cells → SlitPlaneSeparation
  covers : ∀ t : I, ∃ index, connectorPathPoint model t ∈ (cell index).region
  admissible : Admissible (batchClaims
    ((List.finRange cells).flatMap fun index ↦
      seamOperations (cell index) (separation index)))

def SeamData.operations
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide} {precision cells : ℕ}
    (data : SeamData model side precision cells) : List (DyadicOperation precision) :=
  (List.finRange cells).flatMap fun index ↦
    seamOperations (data.cell index) (data.separation index)

/-- The sole external observation: the CompCert-compiled batch returned zero failed claims. -/
structure SeamRunVerdict
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide} {precision cells : ℕ}
    (name : String) (data : SeamData model side precision cells) : Prop where
  returnsZero : (batchComputation name data.operations).Returns ((0 : Nat) : Int)

/-- Expected half-plane of the first factor at the outer endpoint. -/
def outerPlusSeparation : ChapterVIDOuterArcSide → SlitPlaneSeparation
  | .initial => .imagNegative
  | .final => .imagPositive

/-- Expected opposite half-plane of the companion factor at the outer endpoint. -/
def outerMinusSeparation : ChapterVIDOuterArcSide → SlitPlaneSeparation
  | .initial => .imagPositive
  | .final => .imagNegative

/-- Factor-wise seam data.  Besides the path cover it identifies cells containing the outer and
local endpoints.  Their separation labels are the finite, checkable facts needed to compare the
product of the two principal factor roots with the principal root of the product. -/
structure FactorSeamData
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) (precision cells : ℕ) where
  cell : Fin cells → ChapterVIDConnectorCompiledGrid.Cell model side precision
  plusSeparation : Fin cells → SlitPlaneSeparation
  minusSeparation : Fin cells → SlitPlaneSeparation
  covers : ∀ t : I, ∃ index, connectorPathPoint model t ∈ (cell index).region
  outerIndex : Fin cells
  outer_mem : connectorPathPoint model (outerParameter side) ∈ (cell outerIndex).region
  outer_plus : plusSeparation outerIndex = outerPlusSeparation side
  outer_minus : minusSeparation outerIndex = outerMinusSeparation side
  localIndex : Fin cells
  local_mem : connectorPathPoint model (localParameter side) ∈ (cell localIndex).region
  local_minus : minusSeparation localIndex = .realPositive
  admissible : Admissible (batchClaims
    ((List.finRange cells).flatMap fun index ↦
      (cell index).coordinateOperations ++ (cell index).trace.operations ++
        [separationOperation (cell index).trace.factorPlus (plusSeparation index),
          separationOperation (cell index).trace.factorMinus (minusSeparation index)]))

def FactorSeamData.cellOperations
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide} {precision cells : ℕ}
    (data : FactorSeamData model side precision cells) (index : Fin cells) :
    List (DyadicOperation precision) :=
  (data.cell index).coordinateOperations ++ (data.cell index).trace.operations ++
    [separationOperation (data.cell index).trace.factorPlus (data.plusSeparation index),
      separationOperation (data.cell index).trace.factorMinus (data.minusSeparation index)]

def FactorSeamData.operations
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide} {precision cells : ℕ}
    (data : FactorSeamData model side precision cells) : List (DyadicOperation precision) :=
  (List.finRange cells).flatMap data.cellOperations

structure FactorSeamRunVerdict
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide} {precision cells : ℕ}
    (name : String) (data : FactorSeamData model side precision cells) : Prop where
  returnsZero : (batchComputation name data.operations).Returns ((0 : Nat) : Int)

/-- A one-cell compiled certificate at the exact local endpoint.  Only the companion (`minus`)
factor is separated: the coarse inverse-Morse box contains the collision lift, so asking the
same box to separate the plus factor would be both unnecessary and impossible. -/
structure FactorLocalAnchorData
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) (precision : ℕ) where
  cell : ChapterVIDConnectorCompiledGrid.Cell model side precision
  local_mem : connectorPathPoint model (localParameter side) ∈ cell.region
  admissible : Admissible (batchClaims
    (cell.coordinateOperations ++ cell.trace.operations ++
      [separationOperation cell.trace.factorMinus .realPositive]))

def FactorLocalAnchorData.operations
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide} {precision : ℕ}
    (data : FactorLocalAnchorData model side precision) :
    List (DyadicOperation precision) :=
  data.cell.coordinateOperations ++ data.cell.trace.operations ++
    [separationOperation data.cell.trace.factorMinus .realPositive]

structure FactorLocalAnchorRunVerdict
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide} {precision : ℕ}
    (name : String) (data : FactorLocalAnchorData model side precision) : Prop where
  returnsZero : (batchComputation name data.operations).Returns ((0 : Nat) : Int)

/-- The semantic information recovered from the endpoint batch. -/
theorem factorLocalAnchor_minus_re_pos
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide} {precision : ℕ}
    {name : String} {data : FactorLocalAnchorData model side precision}
    (run : FactorLocalAnchorRunVerdict name data) :
    0 < (model.rectangleFactorMinus side
      (connectorPathPoint model (localParameter side))).re := by
  have hcoordinate : ∀ operation ∈ data.cell.coordinateOperations, operation.Sound := by
    intro operation hoperation
    exact allSound_of_returns_zero name data.operations data.admissible run.returnsZero
      operation (by simp [FactorLocalAnchorData.operations, hoperation])
  have htrace : ∀ operation ∈ data.cell.trace.operations, operation.Sound := by
    intro operation hoperation
    exact allSound_of_returns_zero name data.operations data.admissible run.returnsZero
      operation (by simp [FactorLocalAnchorData.operations, hoperation])
  have hminusSound := allSound_of_returns_zero name data.operations data.admissible
    run.returnsZero (separationOperation data.cell.trace.factorMinus .realPositive)
    (by simp [FactorLocalAnchorData.operations])
  have hcontains := data.cell.factors_contain_of_allSound hcoordinate htrace _ data.local_mem
  exact SlitPlaneSeparation.value_pos_of_lower_pos .realPositive hcontains.2 hminusSound

/-- If a product is positive real and its second factor has positive real part, so does its first
factor.  This elementary identity is the exact bridge that replaces an unprovable interval
separation for the collision-containing endpoint box. -/
theorem first_re_pos_of_mul_re_pos_im_zero_of_second_re_pos
    {x y : ℂ} (hprodRe : 0 < (x * y).re) (hprodIm : (x * y).im = 0)
    (hyRe : 0 < y.re) :
    0 < x.re := by
  have him : x.re * y.im + x.im * y.re = 0 := by
    simpa [Complex.mul_im] using hprodIm
  have hre : 0 < x.re * y.re - x.im * y.im := by
    simpa [Complex.mul_re] using hprodRe
  have hnorm : 0 < y.re ^ 2 + y.im ^ 2 := by
    nlinarith [sq_pos_of_pos hyRe, sq_nonneg y.im]
  have hidentity :
      (x.re * y.re - x.im * y.im) * y.re =
        x.re * (y.re ^ 2 + y.im ^ 2) := by
    calc
      (x.re * y.re - x.im * y.im) * y.re =
          x.re * (y.re ^ 2 + y.im ^ 2) - y.im *
            (x.re * y.im + x.im * y.re) := by ring
      _ = x.re * (y.re ^ 2 + y.im ^ 2) := by rw [him]; ring
  have hleft : 0 < (x.re * y.re - x.im * y.im) * y.re :=
    mul_pos hre hyRe
  by_contra hx
  have hxle : x.re ≤ 0 := le_of_not_gt hx
  have hright : x.re * (y.re ^ 2 + y.im ^ 2) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hxle hnorm.le
  rw [← hidentity] at hright
  exact (not_lt_of_ge hright) hleft

theorem factorLocalAnchor_plus_re_pos
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide} {precision : ℕ}
    {name : String} {data : FactorLocalAnchorData model side precision}
    (run : FactorLocalAnchorRunVerdict name data) :
    0 < (model.rectangleFactorPlus side
      (connectorPathPoint model (localParameter side))).re := by
  let point := connectorPathPoint model (localParameter side)
  let x := model.rectangleFactorPlus side point
  let y := model.rectangleFactorMinus side point
  have hprod : x * y = model.connectorLocalBoundaryRadicand 0 := by
    rw [← model.rectangleRadicand_eq_factor_mul side point]
    simpa [point] using model.rectangleRadicand_connectorLocalBoundaryPoint side 0
  apply first_re_pos_of_mul_re_pos_im_zero_of_second_re_pos
  · rw [hprod]
    exact model.connectorLocalBoundaryRadicand_re_pos 0
  · rw [hprod]
    unfold ChapterVIDPrincipalConnectorModel.connectorLocalBoundaryRadicand
    exact Complex.ofReal_im _
  · exact factorLocalAnchor_minus_re_pos run

/-- A semantic collar on the one-dimensional seam path in which both collision factors lie in
the open right half-plane.  Its endpoint positivity originates in one compiled anchor batch. -/
structure FactorEndpointCollar
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) where
  width : ℝ
  width_pos : 0 < width
  width_le_one : width ≤ 1
  plus_re_pos : ∀ t : I, dist t (localParameter side) < width →
    0 < (model.rectangleFactorPlus side (connectorPathPoint model t)).re
  minus_re_pos : ∀ t : I, dist t (localParameter side) < width →
    0 < (model.rectangleFactorMinus side (connectorPathPoint model t)).re

/-- Continuity turns the checked endpoint margin into a positive-width branch collar.  This
contains no numerical evaluation: all model-specific arithmetic remains in the anchor batch. -/
theorem exists_factorEndpointCollar_of_anchorRun
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide} {precision : ℕ}
    {name : String} {data : FactorLocalAnchorData model side precision}
    (run : FactorLocalAnchorRunVerdict name data) :
    Nonempty (FactorEndpointCollar model side) := by
  let path : I → I × I := connectorPathPoint model
  let plusRe : I → ℝ := fun t ↦ (model.rectangleFactorPlus side (path t)).re
  let minusRe : I → ℝ := fun t ↦ (model.rectangleFactorMinus side (path t)).re
  have hpath : Continuous path := continuous_const.prodMk continuous_id
  have hplusContinuous : Continuous plusRe :=
    Complex.continuous_re.comp
      ((model.continuous_rectangleFactorPlus side).comp hpath)
  have hminusContinuous : Continuous minusRe :=
    Complex.continuous_re.comp
      ((model.continuous_rectangleFactorMinus side).comp hpath)
  have hplusAt : 0 < plusRe (localParameter side) :=
    factorLocalAnchor_plus_re_pos run
  have hminusAt : 0 < minusRe (localParameter side) :=
    factorLocalAnchor_minus_re_pos run
  have hplusEventually : {t : I | 0 < plusRe t} ∈ 𝓝 (localParameter side) :=
    hplusContinuous.continuousAt.eventually (Ioi_mem_nhds hplusAt)
  have hminusEventually : {t : I | 0 < minusRe t} ∈ 𝓝 (localParameter side) :=
    hminusContinuous.continuousAt.eventually (Ioi_mem_nhds hminusAt)
  obtain ⟨δplus, hδplus, hplusBall⟩ := Metric.mem_nhds_iff.mp hplusEventually
  obtain ⟨δminus, hδminus, hminusBall⟩ := Metric.mem_nhds_iff.mp hminusEventually
  refine ⟨{
    width := min (min δplus δminus) 1
    width_pos := lt_min (lt_min hδplus hδminus) zero_lt_one
    width_le_one := min_le_right _ _
    plus_re_pos := ?_
    minus_re_pos := ?_ }⟩
  · intro t ht
    exact hplusBall (by
      rw [Metric.mem_ball]
      exact ht.trans_le ((min_le_left _ _).trans (min_le_left _ _)))
  · intro t ht
    exact hminusBall (by
      rw [Metric.mem_ball]
      exact ht.trans_le ((min_le_left _ _).trans (min_le_right _ _)))

/-- Factor-wise compiled cells outside the endpoint collar.  This is the scalable artifact:
certificate size grows linearly with the one-dimensional mesh, while every arithmetic claim is
checked by the CompCert-compiled batch evaluator. -/
structure FactorBulkData
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) (collar : FactorEndpointCollar model side)
    (precision cells : ℕ) where
  cell : Fin cells → ChapterVIDConnectorCompiledGrid.Cell model side precision
  plusSeparation : Fin cells → SlitPlaneSeparation
  minusSeparation : Fin cells → SlitPlaneSeparation
  covers : ∀ t : I, collar.width ≤ dist t (localParameter side) →
    ∃ index, connectorPathPoint model t ∈ (cell index).region
  outerIndex : Fin cells
  outer_mem : connectorPathPoint model (outerParameter side) ∈ (cell outerIndex).region
  outer_plus : plusSeparation outerIndex = outerPlusSeparation side
  outer_minus : minusSeparation outerIndex = outerMinusSeparation side
  admissible : Admissible (batchClaims
    ((List.finRange cells).flatMap fun index ↦
      (cell index).coordinateOperations ++ (cell index).trace.operations ++
        [separationOperation (cell index).trace.factorPlus (plusSeparation index),
          separationOperation (cell index).trace.factorMinus (minusSeparation index)]))

def FactorBulkData.cellOperations
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide} {collar : FactorEndpointCollar model side}
    {precision cells : ℕ}
    (data : FactorBulkData model side collar precision cells) (index : Fin cells) :
    List (DyadicOperation precision) :=
  (data.cell index).coordinateOperations ++ (data.cell index).trace.operations ++
    [separationOperation (data.cell index).trace.factorPlus (data.plusSeparation index),
      separationOperation (data.cell index).trace.factorMinus (data.minusSeparation index)]

def FactorBulkData.operations
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide} {collar : FactorEndpointCollar model side}
    {precision cells : ℕ}
    (data : FactorBulkData model side collar precision cells) :
    List (DyadicOperation precision) :=
  (List.finRange cells).flatMap data.cellOperations

structure FactorBulkRunVerdict
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide} {collar : FactorEndpointCollar model side}
    {precision cells : ℕ}
    (name : String) (data : FactorBulkData model side collar precision cells) : Prop where
  returnsZero : (batchComputation name data.operations).Returns ((0 : Nat) : Int)

/-- Kernel-side constructor for generated factor batches whose individual interval certificates
have already been reconstructed.  This is also the converse of consuming a compiled zero
verdict: under the word-size admissibility proof, the two formulations are equivalent. -/
theorem FactorBulkRunVerdict.ofAllSound
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide} {collar : FactorEndpointCollar model side}
    {precision cells : ℕ} (name : String)
    (data : FactorBulkData model side collar precision cells)
    (hall : ∀ operation ∈ data.operations, operation.Sound) :
    FactorBulkRunVerdict name data :=
  ⟨returns_zero_of_allSound name data.operations data.admissible hall⟩

theorem factorBulkRunVerdict_iff_allSound
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide} {collar : FactorEndpointCollar model side}
    {precision cells : ℕ} (name : String)
    (data : FactorBulkData model side collar precision cells) :
    FactorBulkRunVerdict name data ↔
      ∀ operation ∈ data.operations, operation.Sound := by
  constructor
  · intro run
    exact allSound_of_returns_zero name data.operations data.admissible run.returnsZero
  · exact FactorBulkRunVerdict.ofAllSound name data

/-- Construct the factor-bulk verdict from a receipt for the exact Lean-derived C artifact. -/
theorem FactorBulkRunVerdict.ofReceipt
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide} {collar : FactorEndpointCollar model side}
    {precision cells : ℕ} (name : String)
    (data : FactorBulkData model side collar precision cells)
    (crypto : LeanCompCert.Attest.ReceiptCrypto)
    (receipt : LeanCompCert.Attest.RunReceipt)
    (kind : LeanCompCert.Attest.AttestationKind) (params nonce : String)
    (bound : LeanCompCert.Attest.receiptBindsProved crypto
      (batchArtifact name data.operations) kind params nonce ((0 : Nat) : Int) receipt = true)
    (admitted : LeanCompCert.Attest.RunAdmission crypto
      (batchArtifact name data.operations) receipt) :
    FactorBulkRunVerdict name data :=
  ⟨returns_zero_of_receipt name data.operations crypto receipt kind params nonce bound admitted⟩

theorem factorBulk_cell_operation_mem
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide} {collar : FactorEndpointCollar model side}
    {precision cells : ℕ}
    (data : FactorBulkData model side collar precision cells) (index : Fin cells)
    (operation : DyadicOperation precision)
    (hoperation : operation ∈ data.cellOperations index) :
    operation ∈ data.operations := by
  rw [FactorBulkData.operations, List.mem_flatMap]
  exact ⟨index, by simp, hoperation⟩

theorem factorBulk_coordinate_operation_mem
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide} {collar : FactorEndpointCollar model side}
    {precision cells : ℕ}
    (data : FactorBulkData model side collar precision cells) (index : Fin cells)
    (operation : DyadicOperation precision)
    (hoperation : operation ∈ (data.cell index).coordinateOperations) :
    operation ∈ data.operations :=
  factorBulk_cell_operation_mem data index operation
    (by simp [FactorBulkData.cellOperations, hoperation])

theorem factorBulk_trace_operation_mem
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide} {collar : FactorEndpointCollar model side}
    {precision cells : ℕ}
    (data : FactorBulkData model side collar precision cells) (index : Fin cells)
    (operation : DyadicOperation precision)
    (hoperation : operation ∈ (data.cell index).trace.operations) :
    operation ∈ data.operations :=
  factorBulk_cell_operation_mem data index operation
    (by simp [FactorBulkData.cellOperations, hoperation])

theorem factorBulk_plus_operation_mem
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide} {collar : FactorEndpointCollar model side}
    {precision cells : ℕ}
    (data : FactorBulkData model side collar precision cells) (index : Fin cells) :
    separationOperation (data.cell index).trace.factorPlus (data.plusSeparation index) ∈
      data.operations := by
  apply factorBulk_cell_operation_mem data index
  simp [FactorBulkData.cellOperations]

theorem factorBulk_minus_operation_mem
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide} {collar : FactorEndpointCollar model side}
    {precision cells : ℕ}
    (data : FactorBulkData model side collar precision cells) (index : Fin cells) :
    separationOperation (data.cell index).trace.factorMinus (data.minusSeparation index) ∈
      data.operations := by
  apply factorBulk_cell_operation_mem data index
  simp [FactorBulkData.cellOperations]

/-- Semantic reconstruction for a cell in the compiled factor bulk. -/
theorem factorBulk_cell_facts
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide} {collar : FactorEndpointCollar model side}
    {precision cells : ℕ}
    {name : String} {data : FactorBulkData model side collar precision cells}
    (run : FactorBulkRunVerdict name data) (index : Fin cells)
    (point : I × I) (hregion : point ∈ (data.cell index).region) :
    (0 < (data.plusSeparation index).value (model.rectangleFactorPlus side point)) ∧
      0 < (data.minusSeparation index).value (model.rectangleFactorMinus side point) := by
  let cell := data.cell index
  have hcoordinate : ∀ operation ∈ cell.coordinateOperations, operation.Sound := by
    intro operation hoperation
    exact allSound_of_returns_zero name data.operations data.admissible run.returnsZero
      operation (factorBulk_coordinate_operation_mem data index operation hoperation)
  have htrace : ∀ operation ∈ cell.trace.operations, operation.Sound := by
    intro operation hoperation
    exact allSound_of_returns_zero name data.operations data.admissible run.returnsZero
      operation (factorBulk_trace_operation_mem data index operation hoperation)
  have hplusSound := allSound_of_returns_zero name data.operations data.admissible
    run.returnsZero
    (separationOperation cell.trace.factorPlus (data.plusSeparation index))
    (factorBulk_plus_operation_mem data index)
  have hminusSound := allSound_of_returns_zero name data.operations data.admissible
    run.returnsZero
    (separationOperation cell.trace.factorMinus (data.minusSeparation index))
    (factorBulk_minus_operation_mem data index)
  have hcontains := cell.factors_contain_of_allSound hcoordinate htrace point hregion
  exact ⟨(data.plusSeparation index).value_pos_of_lower_pos hcontains.1 hplusSound,
    (data.minusSeparation index).value_pos_of_lower_pos hcontains.2 hminusSound⟩

theorem factorHybrid_sqrt_conditions
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide} {collar : FactorEndpointCollar model side}
    {precision cells : ℕ}
    {name : String} {data : FactorBulkData model side collar precision cells}
    (run : FactorBulkRunVerdict name data) (t : I) :
    (0 ≤ (model.rectangleFactorPlus side (connectorPathPoint model t)).re ∨
      (model.rectangleFactorPlus side (connectorPathPoint model t)).im ≠ 0) ∧
    (0 ≤ (model.rectangleFactorMinus side (connectorPathPoint model t)).re ∨
      (model.rectangleFactorMinus side (connectorPathPoint model t)).im ≠ 0) := by
  by_cases hcollar : dist t (localParameter side) < collar.width
  · exact ⟨Or.inl (collar.plus_re_pos t hcollar).le,
      Or.inl (collar.minus_re_pos t hcollar).le⟩
  · obtain ⟨index, hregion⟩ := data.covers t (le_of_not_gt hcollar)
    have hfacts := factorBulk_cell_facts run index _ hregion
    exact ⟨(data.plusSeparation index).sqrt_condition_of_value_pos hfacts.1,
      (data.minusSeparation index).sqrt_condition_of_value_pos hfacts.2⟩

theorem factorHybrid_ne_zero
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide} {collar : FactorEndpointCollar model side}
    {precision cells : ℕ}
    {name : String} {data : FactorBulkData model side collar precision cells}
    (run : FactorBulkRunVerdict name data) (t : I) :
    model.rectangleFactorPlus side (connectorPathPoint model t) ≠ 0 ∧
      model.rectangleFactorMinus side (connectorPathPoint model t) ≠ 0 := by
  by_cases hcollar : dist t (localParameter side) < collar.width
  · constructor
    · intro hzero
      have hpos := collar.plus_re_pos t hcollar
      rw [hzero] at hpos
      simp at hpos
    · intro hzero
      have hpos := collar.minus_re_pos t hcollar
      rw [hzero] at hpos
      simp at hpos
  · obtain ⟨index, hregion⟩ := data.covers t (le_of_not_gt hcollar)
    have hfacts := factorBulk_cell_facts run index _ hregion
    exact ⟨(data.plusSeparation index).ne_zero_of_value_pos hfacts.1,
      (data.minusSeparation index).ne_zero_of_value_pos hfacts.2⟩

theorem factorHybrid_outer_arg_add_mem
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide} {collar : FactorEndpointCollar model side}
    {precision cells : ℕ}
    {name : String} {data : FactorBulkData model side collar precision cells}
    (run : FactorBulkRunVerdict name data) :
    Complex.arg (model.rectangleFactorPlus side
        (connectorPathPoint model (outerParameter side))) +
      Complex.arg (model.rectangleFactorMinus side
        (connectorPathPoint model (outerParameter side))) ∈
      Set.Ioc (-Real.pi) Real.pi := by
  have hfacts := factorBulk_cell_facts run data.outerIndex _ data.outer_mem
  cases side with
  | initial =>
      have hplus := hfacts.1
      have hminus := hfacts.2
      rw [data.outer_plus] at hplus
      rw [data.outer_minus] at hminus
      exact arg_add_mem_Ioc_of_im_neg_pos
        (by simpa [outerPlusSeparation, SlitPlaneSeparation.value,
          SlitPlaneSeparation.toZeroSeparation,
          ChapterVIComplexZeroSeparation.value] using hplus)
        (by simpa [outerMinusSeparation, SlitPlaneSeparation.value,
          SlitPlaneSeparation.toZeroSeparation,
          ChapterVIComplexZeroSeparation.value] using hminus)
  | final =>
      have hplus := hfacts.1
      have hminus := hfacts.2
      rw [data.outer_plus] at hplus
      rw [data.outer_minus] at hminus
      exact arg_add_mem_Ioc_of_im_pos_neg
        (by simpa [outerPlusSeparation, SlitPlaneSeparation.value,
          SlitPlaneSeparation.toZeroSeparation,
          ChapterVIComplexZeroSeparation.value] using hplus)
        (by simpa [outerMinusSeparation, SlitPlaneSeparation.value,
          SlitPlaneSeparation.toZeroSeparation,
          ChapterVIComplexZeroSeparation.value] using hminus)

/-- The hybrid sheet uses ordinary continuity only in the endpoint collar; all bulk branch
choices and all expensive arithmetic come from the compiled factor batch. -/
def factorHybridPathSheet
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide} {collar : FactorEndpointCollar model side}
    {precision cells : ℕ}
    {name : String} {data : FactorBulkData model side collar precision cells}
    (run : FactorBulkRunVerdict name data) :
    ChapterVIContinuousSquareRootSheet
      (fun t : I ↦ model.rectangleRadicand side (connectorPathPoint model t)) where
  root t :=
    Complex.sqrt (model.rectangleFactorPlus side (connectorPathPoint model t)) *
      Complex.sqrt (model.rectangleFactorMinus side (connectorPathPoint model t))
  continuous_root := by
    have hpath : Continuous (connectorPathPoint model) :=
      continuous_const.prodMk continuous_id
    have hplus : Continuous
        (fun t : I ↦ Complex.sqrt
          (model.rectangleFactorPlus side (connectorPathPoint model t))) := by
      rw [continuous_iff_continuousAt]
      intro t
      exact (Complex.continuousAt_sqrt (factorHybrid_sqrt_conditions run t).1).comp_of_eq
        ((model.continuous_rectangleFactorPlus side).comp hpath).continuousAt rfl
    have hminus : Continuous
        (fun t : I ↦ Complex.sqrt
          (model.rectangleFactorMinus side (connectorPathPoint model t))) := by
      rw [continuous_iff_continuousAt]
      intro t
      exact (Complex.continuousAt_sqrt (factorHybrid_sqrt_conditions run t).2).comp_of_eq
        ((model.continuous_rectangleFactorMinus side).comp hpath).continuousAt rfl
    exact hplus.mul hminus
  root_sq t := by
    rw [mul_pow]
    have hplus := Complex.cpow_nat_inv_pow
      (model.rectangleFactorPlus side (connectorPathPoint model t))
      (by norm_num : (2 : ℕ) ≠ 0)
    have hminus := Complex.cpow_nat_inv_pow
      (model.rectangleFactorMinus side (connectorPathPoint model t))
      (by norm_num : (2 : ℕ) ≠ 0)
    change Complex.sqrt
        (model.rectangleFactorPlus side (connectorPathPoint model t)) ^ 2 *
      Complex.sqrt
        (model.rectangleFactorMinus side (connectorPathPoint model t)) ^ 2 = _
    rw [show Complex.sqrt
          (model.rectangleFactorPlus side (connectorPathPoint model t)) ^ 2 =
          model.rectangleFactorPlus side (connectorPathPoint model t) by exact hplus,
      show Complex.sqrt
          (model.rectangleFactorMinus side (connectorPathPoint model t)) ^ 2 =
          model.rectangleFactorMinus side (connectorPathPoint model t) by exact hminus]
    exact (model.rectangleRadicand_eq_factor_mul side _).symm

theorem factorHybridPathSheet_outer
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide} {collar : FactorEndpointCollar model side}
    {precision cells : ℕ}
    {name : String} {data : FactorBulkData model side collar precision cells}
    (run : FactorBulkRunVerdict name data) :
    (factorHybridPathSheet run).root (outerParameter side) =
      Complex.sqrt (model.rectangleRadicand side
        (connectorPathPoint model (outerParameter side))) := by
  have hne := factorHybrid_ne_zero run (outerParameter side)
  have hmul := sqrt_mul_of_arg_add_mem hne.1 hne.2
    (factorHybrid_outer_arg_add_mem run)
  rw [model.rectangleRadicand_eq_factor_mul]
  exact hmul.symm

theorem factorHybridPathSheet_local
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide} {collar : FactorEndpointCollar model side}
    {precision cells : ℕ}
    {name : String} {data : FactorBulkData model side collar precision cells}
    (run : FactorBulkRunVerdict name data) :
    (factorHybridPathSheet run).root (localParameter side) =
      model.connectorLocalBoundaryRoot 0 := by
  let point := connectorPathPoint model (localParameter side)
  let x := model.rectangleFactorPlus side point
  let y := model.rectangleFactorMinus side point
  have hprod : x * y = model.connectorLocalBoundaryRadicand 0 := by
    rw [← model.rectangleRadicand_eq_factor_mul side point]
    simpa [point] using model.rectangleRadicand_connectorLocalBoundaryPoint side 0
  have hprodRe : 0 < (x * y).re := by
    rw [hprod]
    exact model.connectorLocalBoundaryRadicand_re_pos 0
  have hprodIm : (x * y).im = 0 := by
    rw [hprod]
    unfold ChapterVIDPrincipalConnectorModel.connectorLocalBoundaryRadicand
    exact Complex.ofReal_im _
  have hlocalDist : dist (localParameter side) (localParameter side) < collar.width := by
    simpa using collar.width_pos
  have harg := arg_add_mem_Ioc_of_mul_re_pos_im_zero_of_right
    hprodRe hprodIm (collar.minus_re_pos _ hlocalDist)
  have hne := factorHybrid_ne_zero run (localParameter side)
  have hmul := sqrt_mul_of_arg_add_mem hne.1 hne.2 harg
  change Complex.sqrt x * Complex.sqrt y = model.connectorLocalBoundaryRoot 0
  rw [← hmul, hprod]
  rfl

/-- A passing factor-bulk certificate transports an arbitrary outer-normalized connector sheet
to the positive local Morse root. -/
theorem connectorSheet_eq_localBoundaryRoot_zero_of_factorBulkRun
    (outerRun : ChapterVIDOuterArcPolarCompiledGrid.CompiledRunVerdict)
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide} {collar : FactorEndpointCollar model side}
    {precision cells : ℕ}
    {name : String} {data : FactorBulkData model side collar precision cells}
    (run : FactorBulkRunVerdict name data)
    (sheet : ChapterVIContinuousSquareRootSheet (model.rectangleRadicand side))
    (houter : ∀ s : I,
      sheet.root (model.connectorBoundaryPoint side s) =
        model.connectorOuterBoundaryRoot outerRun side s) :
    sheet.root (model.connectorLocalBoundaryPoint side 0) =
      model.connectorLocalBoundaryRoot 0 := by
  let restricted : ChapterVIContinuousSquareRootSheet
      (fun t : I ↦ model.rectangleRadicand side (connectorPathPoint model t)) := {
    root := fun t ↦ sheet.root (connectorPathPoint model t)
    continuous_root := sheet.continuous_root.comp
      (continuous_const.prodMk continuous_id)
    root_sq := fun t ↦ sheet.root_sq _ }
  have hbase : restricted.root (outerParameter side) =
      (factorHybridPathSheet run).root (outerParameter side) := by
    rw [show restricted.root (outerParameter side) =
        sheet.root (model.connectorBoundaryPoint side 0) by simp [restricted]]
    rw [houter 0, factorHybridPathSheet_outer run]
    change Complex.sqrt
        (chapterVIDOuterArcRadicand side (model.connectorOuterBoundaryPoint side 0)) =
      Complex.sqrt
        (model.rectangleRadicand side (connectorPathPoint model (outerParameter side)))
    rw [← model.rectangleRadicand_connectorBoundaryPoint side 0]
    simp
  have hall := restricted.root_eq_of_eq_at (factorHybridPathSheet run)
    (fun t ↦ mul_ne_zero (factorHybrid_ne_zero run t).1
      (factorHybrid_ne_zero run t).2)
    (outerParameter side) hbase
  calc
    sheet.root (model.connectorLocalBoundaryPoint side 0) =
        restricted.root (localParameter side) := by simp [restricted]
    _ = (factorHybridPathSheet run).root (localParameter side) :=
      congrFun hall (localParameter side)
    _ = model.connectorLocalBoundaryRoot 0 := factorHybridPathSheet_local run

def toSeamCompatiblePairOfFactorBulkRuns
    (outerRun : ChapterVIDOuterArcPolarCompiledGrid.CompiledRunVerdict)
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    (pair : ChapterVIDPrincipalConnectorModel.CertifiedConnectorPair outerRun model)
    {initialCollar : FactorEndpointCollar model .initial}
    {finalCollar : FactorEndpointCollar model .final}
    {initialPrecision initialCells finalPrecision finalCells : ℕ}
    {initialName finalName : String}
    {initialData :
      FactorBulkData model .initial initialCollar initialPrecision initialCells}
    {finalData : FactorBulkData model .final finalCollar finalPrecision finalCells}
    (initialRun : FactorBulkRunVerdict initialName initialData)
    (finalRun : FactorBulkRunVerdict finalName finalData) :
    ChapterVIDPrincipalConnectorModel.SeamCompatibleCertifiedConnectorPair outerRun model where
  pair := pair
  initial_local_at_zero :=
    connectorSheet_eq_localBoundaryRoot_zero_of_factorBulkRun outerRun initialRun
      pair.initialSheet pair.initial_outer
  final_local_at_zero :=
    connectorSheet_eq_localBoundaryRoot_zero_of_factorBulkRun outerRun finalRun
      pair.finalSheet pair.final_outer

/-- End-to-end scalable certificate theorem: existing connector nonvanishing certificates create
the two sheets, and linear-size factor batches determine their local signs. -/
theorem exists_seamCompatibleContribution_tendsto_of_factorBulkCertificates
    (outerRun : ChapterVIDOuterArcPolarCompiledGrid.CompiledRunVerdict)
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (initialCertificate : ChapterVIDConnectorCompiledCertificate model .initial)
    (finalCertificate : ChapterVIDConnectorCompiledCertificate model .final)
    {initialCollar : FactorEndpointCollar model .initial}
    {finalCollar : FactorEndpointCollar model .final}
    {initialPrecision initialCells finalPrecision finalCells : ℕ}
    {initialName finalName : String}
    {initialData :
      FactorBulkData model .initial initialCollar initialPrecision initialCells}
    {finalData : FactorBulkData model .final finalCollar finalPrecision finalCells}
    (initialRun : FactorBulkRunVerdict initialName initialData)
    (finalRun : FactorBulkRunVerdict finalName finalData) :
    ∃ compatible :
        ChapterVIDPrincipalConnectorModel.SeamCompatibleCertifiedConnectorPair outerRun model,
      Filter.Tendsto
        (fun k : ℝ ↦ (-Real.log k)⁻¹ • compatible.fivePieceContribution k)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds ((2 * Real.pi * Complex.I : ℂ)⁻¹ *
          chapterVIDPrincipalMorseAmplitude massProduct b d (0, 0))) := by
  obtain ⟨pair⟩ :=
    ChapterVIDPrincipalConnectorModel.exists_certifiedConnectorPair outerRun model
      initialCertificate finalCertificate
  let compatible :=
    toSeamCompatiblePairOfFactorBulkRuns outerRun pair initialRun finalRun
  exact ⟨compatible, compatible.tendsto_fivePiece_inv_neg_log_smul⟩

theorem factor_cell_operation_mem
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide} {precision cells : ℕ}
    (data : FactorSeamData model side precision cells) (index : Fin cells)
    (operation : DyadicOperation precision)
    (hoperation : operation ∈ data.cellOperations index) :
    operation ∈ data.operations := by
  rw [FactorSeamData.operations, List.mem_flatMap]
  exact ⟨index, by simp, hoperation⟩

theorem factor_coordinate_operation_mem
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide} {precision cells : ℕ}
    (data : FactorSeamData model side precision cells) (index : Fin cells)
    (operation : DyadicOperation precision)
    (hoperation : operation ∈ (data.cell index).coordinateOperations) :
    operation ∈ data.operations :=
  factor_cell_operation_mem data index operation
    (by simp [FactorSeamData.cellOperations, hoperation])

theorem factor_trace_operation_mem
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide} {precision cells : ℕ}
    (data : FactorSeamData model side precision cells) (index : Fin cells)
    (operation : DyadicOperation precision)
    (hoperation : operation ∈ (data.cell index).trace.operations) :
    operation ∈ data.operations :=
  factor_cell_operation_mem data index operation
    (by simp [FactorSeamData.cellOperations, hoperation])

theorem factor_plus_operation_mem
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide} {precision cells : ℕ}
    (data : FactorSeamData model side precision cells) (index : Fin cells) :
    separationOperation (data.cell index).trace.factorPlus (data.plusSeparation index) ∈
      data.operations := by
  apply factor_cell_operation_mem data index
  simp [FactorSeamData.cellOperations]

theorem factor_minus_operation_mem
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide} {precision cells : ℕ}
    (data : FactorSeamData model side precision cells) (index : Fin cells) :
    separationOperation (data.cell index).trace.factorMinus (data.minusSeparation index) ∈
      data.operations := by
  apply factor_cell_operation_mem data index
  simp [FactorSeamData.cellOperations]

/-- Semantic reconstruction for any factor cell in a successful compiled run. -/
theorem factor_cell_facts
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide} {precision cells : ℕ}
    {name : String} {data : FactorSeamData model side precision cells}
    (run : FactorSeamRunVerdict name data) (index : Fin cells)
    (point : I × I) (hregion : point ∈ (data.cell index).region) :
    ((data.cell index).trace.factorPlus.Contains (model.rectangleFactorPlus side point) ∧
      0 < (data.plusSeparation index).value (model.rectangleFactorPlus side point)) ∧
    ((data.cell index).trace.factorMinus.Contains (model.rectangleFactorMinus side point) ∧
      0 < (data.minusSeparation index).value (model.rectangleFactorMinus side point)) := by
  let cell := data.cell index
  have hcoordinate : ∀ operation ∈ cell.coordinateOperations, operation.Sound := by
    intro operation hoperation
    exact allSound_of_returns_zero name data.operations data.admissible run.returnsZero
      operation (factor_coordinate_operation_mem data index operation hoperation)
  have htrace : ∀ operation ∈ cell.trace.operations, operation.Sound := by
    intro operation hoperation
    exact allSound_of_returns_zero name data.operations data.admissible run.returnsZero
      operation (factor_trace_operation_mem data index operation hoperation)
  have hplusSound := allSound_of_returns_zero name data.operations data.admissible
    run.returnsZero
    (separationOperation cell.trace.factorPlus (data.plusSeparation index))
    (factor_plus_operation_mem data index)
  have hminusSound := allSound_of_returns_zero name data.operations data.admissible
    run.returnsZero
    (separationOperation cell.trace.factorMinus (data.minusSeparation index))
    (factor_minus_operation_mem data index)
  have hcontains := cell.factors_contain_of_allSound hcoordinate htrace point hregion
  exact ⟨⟨hcontains.1,
      (data.plusSeparation index).value_pos_of_lower_pos hcontains.1 hplusSound⟩,
    ⟨hcontains.2,
      (data.minusSeparation index).value_pos_of_lower_pos hcontains.2 hminusSound⟩⟩

theorem factor_sqrt_conditions
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide} {precision cells : ℕ}
    {name : String} {data : FactorSeamData model side precision cells}
    (run : FactorSeamRunVerdict name data) (t : I) :
    (0 ≤ (model.rectangleFactorPlus side (connectorPathPoint model t)).re ∨
      (model.rectangleFactorPlus side (connectorPathPoint model t)).im ≠ 0) ∧
    (0 ≤ (model.rectangleFactorMinus side (connectorPathPoint model t)).re ∨
      (model.rectangleFactorMinus side (connectorPathPoint model t)).im ≠ 0) := by
  obtain ⟨index, hregion⟩ := data.covers t
  have hfacts := factor_cell_facts run index _ hregion
  exact ⟨(data.plusSeparation index).sqrt_condition_of_lower_pos hfacts.1.1
      (by simpa [separationOperation, DyadicOperation.Sound] using
        (show 0 < ((data.plusSeparation index).interval
          (data.cell index).trace.factorPlus).lower from by
            have hsound := allSound_of_returns_zero name data.operations data.admissible
              run.returnsZero
              (separationOperation (data.cell index).trace.factorPlus
                (data.plusSeparation index))
              (factor_plus_operation_mem data index)
            exact hsound)),
    (data.minusSeparation index).sqrt_condition_of_lower_pos hfacts.2.1
      (by
        have hsound := allSound_of_returns_zero name data.operations data.admissible
          run.returnsZero
          (separationOperation (data.cell index).trace.factorMinus
            (data.minusSeparation index))
          (factor_minus_operation_mem data index)
        exact hsound)⟩

theorem factor_ne_zero
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide} {precision cells : ℕ}
    {name : String} {data : FactorSeamData model side precision cells}
    (run : FactorSeamRunVerdict name data) (t : I) :
    model.rectangleFactorPlus side (connectorPathPoint model t) ≠ 0 ∧
      model.rectangleFactorMinus side (connectorPathPoint model t) ≠ 0 := by
  obtain ⟨index, hregion⟩ := data.covers t
  have hfacts := factor_cell_facts run index _ hregion
  exact ⟨(data.plusSeparation index).ne_zero_of_value_pos hfacts.1.2,
    (data.minusSeparation index).ne_zero_of_value_pos hfacts.2.2⟩

theorem factor_outer_arg_add_mem
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide} {precision cells : ℕ}
    {name : String} {data : FactorSeamData model side precision cells}
    (run : FactorSeamRunVerdict name data) :
    Complex.arg (model.rectangleFactorPlus side
        (connectorPathPoint model (outerParameter side))) +
      Complex.arg (model.rectangleFactorMinus side
        (connectorPathPoint model (outerParameter side))) ∈
      Set.Ioc (-Real.pi) Real.pi := by
  have hfacts := factor_cell_facts run data.outerIndex _ data.outer_mem
  cases side with
  | initial =>
      have hplus := hfacts.1.2
      have hminus := hfacts.2.2
      rw [data.outer_plus] at hplus
      rw [data.outer_minus] at hminus
      exact arg_add_mem_Ioc_of_im_neg_pos
        (by simpa [outerPlusSeparation, SlitPlaneSeparation.value,
          SlitPlaneSeparation.toZeroSeparation,
          ChapterVIComplexZeroSeparation.value] using hplus)
        (by simpa [outerMinusSeparation, SlitPlaneSeparation.value,
          SlitPlaneSeparation.toZeroSeparation,
          ChapterVIComplexZeroSeparation.value] using hminus)
  | final =>
      have hplus := hfacts.1.2
      have hminus := hfacts.2.2
      rw [data.outer_plus] at hplus
      rw [data.outer_minus] at hminus
      exact arg_add_mem_Ioc_of_im_pos_neg
        (by simpa [outerPlusSeparation, SlitPlaneSeparation.value,
          SlitPlaneSeparation.toZeroSeparation,
          ChapterVIComplexZeroSeparation.value] using hplus)
        (by simpa [outerMinusSeparation, SlitPlaneSeparation.value,
          SlitPlaneSeparation.toZeroSeparation,
          ChapterVIComplexZeroSeparation.value] using hminus)

theorem factor_local_minus_re_pos
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide} {precision cells : ℕ}
    {name : String} {data : FactorSeamData model side precision cells}
    (run : FactorSeamRunVerdict name data) :
    0 < (model.rectangleFactorMinus side
      (connectorPathPoint model (localParameter side))).re := by
  have hfacts := factor_cell_facts run data.localIndex _ data.local_mem
  have hminus := hfacts.2.2
  rw [data.local_minus] at hminus
  simpa [SlitPlaneSeparation.value, SlitPlaneSeparation.toZeroSeparation,
    ChapterVIComplexZeroSeparation.value] using hminus

/-- The product of the two principal factor roots is a continuous square-root sheet for the
literal connector radicand. -/
def factorProductPathSheet
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide} {precision cells : ℕ}
    {name : String} {data : FactorSeamData model side precision cells}
    (run : FactorSeamRunVerdict name data) :
    ChapterVIContinuousSquareRootSheet
      (fun t : I ↦ model.rectangleRadicand side (connectorPathPoint model t)) where
  root t :=
    Complex.sqrt (model.rectangleFactorPlus side (connectorPathPoint model t)) *
      Complex.sqrt (model.rectangleFactorMinus side (connectorPathPoint model t))
  continuous_root := by
    have hpath : Continuous (connectorPathPoint model) :=
      continuous_const.prodMk continuous_id
    have hplus : Continuous
        (fun t : I ↦ Complex.sqrt
          (model.rectangleFactorPlus side (connectorPathPoint model t))) := by
      rw [continuous_iff_continuousAt]
      intro t
      exact (Complex.continuousAt_sqrt (factor_sqrt_conditions run t).1).comp_of_eq
        ((model.continuous_rectangleFactorPlus side).comp hpath).continuousAt rfl
    have hminus : Continuous
        (fun t : I ↦ Complex.sqrt
          (model.rectangleFactorMinus side (connectorPathPoint model t))) := by
      rw [continuous_iff_continuousAt]
      intro t
      exact (Complex.continuousAt_sqrt (factor_sqrt_conditions run t).2).comp_of_eq
        ((model.continuous_rectangleFactorMinus side).comp hpath).continuousAt rfl
    exact hplus.mul hminus
  root_sq t := by
    rw [mul_pow]
    have hplus := Complex.cpow_nat_inv_pow
      (model.rectangleFactorPlus side (connectorPathPoint model t))
      (by norm_num : (2 : ℕ) ≠ 0)
    have hminus := Complex.cpow_nat_inv_pow
      (model.rectangleFactorMinus side (connectorPathPoint model t))
      (by norm_num : (2 : ℕ) ≠ 0)
    change Complex.sqrt
        (model.rectangleFactorPlus side (connectorPathPoint model t)) ^ 2 *
      Complex.sqrt
        (model.rectangleFactorMinus side (connectorPathPoint model t)) ^ 2 = _
    rw [show Complex.sqrt
          (model.rectangleFactorPlus side (connectorPathPoint model t)) ^ 2 =
          model.rectangleFactorPlus side (connectorPathPoint model t) by
        exact hplus,
      show Complex.sqrt
          (model.rectangleFactorMinus side (connectorPathPoint model t)) ^ 2 =
          model.rectangleFactorMinus side (connectorPathPoint model t) by
        exact hminus]
    exact (model.rectangleRadicand_eq_factor_mul side _).symm

theorem factorProductPathSheet_outer
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide} {precision cells : ℕ}
    {name : String} {data : FactorSeamData model side precision cells}
    (run : FactorSeamRunVerdict name data) :
    (factorProductPathSheet run).root (outerParameter side) =
      Complex.sqrt (model.rectangleRadicand side
        (connectorPathPoint model (outerParameter side))) := by
  have hne := factor_ne_zero run (outerParameter side)
  have hmul := sqrt_mul_of_arg_add_mem hne.1 hne.2
    (factor_outer_arg_add_mem run)
  rw [model.rectangleRadicand_eq_factor_mul]
  exact hmul.symm

theorem factorProductPathSheet_local
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide} {precision cells : ℕ}
    {name : String} {data : FactorSeamData model side precision cells}
    (run : FactorSeamRunVerdict name data) :
    (factorProductPathSheet run).root (localParameter side) =
      model.connectorLocalBoundaryRoot 0 := by
  let point := connectorPathPoint model (localParameter side)
  let x := model.rectangleFactorPlus side point
  let y := model.rectangleFactorMinus side point
  have hprod : x * y = model.connectorLocalBoundaryRadicand 0 := by
    rw [← model.rectangleRadicand_eq_factor_mul side point]
    simpa [point] using model.rectangleRadicand_connectorLocalBoundaryPoint side 0
  have hprodRe : 0 < (x * y).re := by
    rw [hprod]
    exact model.connectorLocalBoundaryRadicand_re_pos 0
  have hprodIm : (x * y).im = 0 := by
    rw [hprod]
    unfold ChapterVIDPrincipalConnectorModel.connectorLocalBoundaryRadicand
    exact Complex.ofReal_im _
  have harg := arg_add_mem_Ioc_of_mul_re_pos_im_zero_of_right
    hprodRe hprodIm (factor_local_minus_re_pos run)
  have hne := factor_ne_zero run (localParameter side)
  have hmul := sqrt_mul_of_arg_add_mem hne.1 hne.2 harg
  change Complex.sqrt x * Complex.sqrt y = model.connectorLocalBoundaryRoot 0
  rw [← hmul, hprod]
  rfl

/-- The passing factor-wise certificate fixes the local seam sign without ever enclosing the
product rectangle. -/
theorem connectorSheet_eq_localBoundaryRoot_zero_of_factorRun
    (outerRun : ChapterVIDOuterArcPolarCompiledGrid.CompiledRunVerdict)
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide} {precision cells : ℕ}
    {name : String} {data : FactorSeamData model side precision cells}
    (run : FactorSeamRunVerdict name data)
    (sheet : ChapterVIContinuousSquareRootSheet (model.rectangleRadicand side))
    (houter : ∀ s : I,
      sheet.root (model.connectorBoundaryPoint side s) =
        model.connectorOuterBoundaryRoot outerRun side s) :
    sheet.root (model.connectorLocalBoundaryPoint side 0) =
      model.connectorLocalBoundaryRoot 0 := by
  let restricted : ChapterVIContinuousSquareRootSheet
      (fun t : I ↦ model.rectangleRadicand side (connectorPathPoint model t)) := {
    root := fun t ↦ sheet.root (connectorPathPoint model t)
    continuous_root := sheet.continuous_root.comp
      (continuous_const.prodMk continuous_id)
    root_sq := fun t ↦ sheet.root_sq _ }
  have hbase : restricted.root (outerParameter side) =
      (factorProductPathSheet run).root (outerParameter side) := by
    rw [show restricted.root (outerParameter side) =
        sheet.root (model.connectorBoundaryPoint side 0) by simp [restricted]]
    rw [houter 0, factorProductPathSheet_outer run]
    change Complex.sqrt
        (chapterVIDOuterArcRadicand side (model.connectorOuterBoundaryPoint side 0)) =
      Complex.sqrt
        (model.rectangleRadicand side (connectorPathPoint model (outerParameter side)))
    rw [← model.rectangleRadicand_connectorBoundaryPoint side 0]
    simp
  have hall := restricted.root_eq_of_eq_at (factorProductPathSheet run)
    (fun t ↦ mul_ne_zero (factor_ne_zero run t).1 (factor_ne_zero run t).2)
    (outerParameter side) hbase
  calc
    sheet.root (model.connectorLocalBoundaryPoint side 0) =
        restricted.root (localParameter side) := by simp [restricted]
    _ = (factorProductPathSheet run).root (localParameter side) :=
      congrFun hall (localParameter side)
    _ = model.connectorLocalBoundaryRoot 0 := factorProductPathSheet_local run

/-- Two successful factor-wise seam batches upgrade a certificate-selected connector pair to
the fully compatible five-piece contour package.  Unlike `toSeamCompatiblePair`, this route
never asks interval arithmetic to enclose the product of the two collision factors. -/
def toSeamCompatiblePairOfFactorRuns
    (outerRun : ChapterVIDOuterArcPolarCompiledGrid.CompiledRunVerdict)
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    (pair : ChapterVIDPrincipalConnectorModel.CertifiedConnectorPair outerRun model)
    {initialPrecision initialCells finalPrecision finalCells : ℕ}
    {initialName finalName : String}
    {initialData : FactorSeamData model .initial initialPrecision initialCells}
    {finalData : FactorSeamData model .final finalPrecision finalCells}
    (initialRun : FactorSeamRunVerdict initialName initialData)
    (finalRun : FactorSeamRunVerdict finalName finalData) :
    ChapterVIDPrincipalConnectorModel.SeamCompatibleCertifiedConnectorPair outerRun model where
  pair := pair
  initial_local_at_zero :=
    connectorSheet_eq_localBoundaryRoot_zero_of_factorRun outerRun initialRun
      pair.initialSheet pair.initial_outer
  final_local_at_zero :=
    connectorSheet_eq_localBoundaryRoot_zero_of_factorRun outerRun finalRun
      pair.finalSheet pair.final_outer

/-- End-to-end factor-wise seam-selection theorem.  The continuum nonvanishing certificates
construct the outer-normalized sheets, while the compiled factor batches select their signs at
the local Morse boundary. -/
theorem exists_seamCompatiblePair_of_factorCompiledCertificates
    (outerRun : ChapterVIDOuterArcPolarCompiledGrid.CompiledRunVerdict)
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (initialCertificate : ChapterVIDConnectorCompiledCertificate model .initial)
    (finalCertificate : ChapterVIDConnectorCompiledCertificate model .final)
    {initialPrecision initialCells finalPrecision finalCells : ℕ}
    {initialName finalName : String}
    {initialData : FactorSeamData model .initial initialPrecision initialCells}
    {finalData : FactorSeamData model .final finalPrecision finalCells}
    (initialRun : FactorSeamRunVerdict initialName initialData)
    (finalRun : FactorSeamRunVerdict finalName finalData) :
    Nonempty
      (ChapterVIDPrincipalConnectorModel.SeamCompatibleCertifiedConnectorPair outerRun model) := by
  obtain ⟨pair⟩ :=
    ChapterVIDPrincipalConnectorModel.exists_certifiedConnectorPair outerRun model
      initialCertificate finalCertificate
  exact ⟨toSeamCompatiblePairOfFactorRuns outerRun pair initialRun finalRun⟩

/-- The factor-wise compiled route reaches Poincare's logarithmic leading coefficient without a
global symbolic branch-cut normalization. -/
theorem exists_seamCompatibleContribution_tendsto_of_factorCompiledCertificates
    (outerRun : ChapterVIDOuterArcPolarCompiledGrid.CompiledRunVerdict)
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (initialCertificate : ChapterVIDConnectorCompiledCertificate model .initial)
    (finalCertificate : ChapterVIDConnectorCompiledCertificate model .final)
    {initialPrecision initialCells finalPrecision finalCells : ℕ}
    {initialName finalName : String}
    {initialData : FactorSeamData model .initial initialPrecision initialCells}
    {finalData : FactorSeamData model .final finalPrecision finalCells}
    (initialRun : FactorSeamRunVerdict initialName initialData)
    (finalRun : FactorSeamRunVerdict finalName finalData) :
    ∃ compatible :
        ChapterVIDPrincipalConnectorModel.SeamCompatibleCertifiedConnectorPair outerRun model,
      Filter.Tendsto
        (fun k : ℝ ↦ (-Real.log k)⁻¹ • compatible.fivePieceContribution k)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds ((2 * Real.pi * Complex.I : ℂ)⁻¹ *
          chapterVIDPrincipalMorseAmplitude massProduct b d (0, 0))) := by
  obtain ⟨compatible⟩ :=
    exists_seamCompatiblePair_of_factorCompiledCertificates outerRun model
      initialCertificate finalCertificate initialRun finalRun
  exact ⟨compatible, compatible.tendsto_fivePiece_inv_neg_log_smul⟩

theorem cell_operation_mem
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide} {precision cells : ℕ}
    (data : SeamData model side precision cells) (index : Fin cells)
    (operation : DyadicOperation precision)
    (hoperation : operation ∈
      seamOperations (data.cell index) (data.separation index)) :
    operation ∈ data.operations := by
  rw [SeamData.operations, List.mem_flatMap]
  exact ⟨index, by simp, hoperation⟩

theorem coordinate_operation_mem
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide} {precision cells : ℕ}
    (data : SeamData model side precision cells) (index : Fin cells)
    (operation : DyadicOperation precision)
    (hoperation : operation ∈ (data.cell index).coordinateOperations) :
    operation ∈ data.operations :=
  cell_operation_mem data index operation
    (by simp [seamOperations, hoperation])

theorem trace_operation_mem
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide} {precision cells : ℕ}
    (data : SeamData model side precision cells) (index : Fin cells)
    (operation : DyadicOperation precision)
    (hoperation : operation ∈ (data.cell index).trace.operations) :
    operation ∈ data.operations :=
  cell_operation_mem data index operation
    (by simp [seamOperations, hoperation])

theorem separation_operation_mem
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide} {precision cells : ℕ}
    (data : SeamData model side precision cells) (index : Fin cells) :
    separationOperation (data.cell index).trace.output (data.separation index) ∈
      data.operations := by
  apply cell_operation_mem data index
  simp [seamOperations]

theorem output_contains_radicand_of_allSound
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide} {precision : ℕ}
    (cell : ChapterVIDConnectorCompiledGrid.Cell model side precision)
    (hcoordinate : ∀ operation ∈ cell.coordinateOperations, operation.Sound)
    (htrace : ∀ operation ∈ cell.trace.operations, operation.Sound)
    (point : I × I) (hregion : point ∈ cell.region) :
    cell.trace.output.Contains (model.rectangleRadicand side point) := by
  have hcoordinateContains :=
    cell.coordinate_contains_of_allSound hcoordinate point hregion
  exact cell.trace.output_contains_rootCoordinateRadicand_of_allSound htrace
    (cell.zeta_contains point hregion) hcoordinateContains
    cell.exponentialCoefficient_contains cell.inverse10001_contains
    (model.connectorParameterRoot_ne_zero point.1)
    (model.rectanglePoint_ne_zero side point)

/-- A successful path batch puts every radicand value in the continuity domain of the principal
square root. -/
theorem sqrt_condition
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide} {precision cells : ℕ}
    {name : String} {data : SeamData model side precision cells}
    (run : SeamRunVerdict name data) (t : I) :
    0 ≤ (model.rectangleRadicand side (connectorPathPoint model t)).re ∨
      (model.rectangleRadicand side (connectorPathPoint model t)).im ≠ 0 := by
  obtain ⟨index, hregion⟩ := data.covers t
  let cell := data.cell index
  have hcoordinate : ∀ operation ∈ cell.coordinateOperations, operation.Sound := by
    intro operation hoperation
    exact allSound_of_returns_zero name data.operations data.admissible run.returnsZero
      operation (coordinate_operation_mem data index operation hoperation)
  have htrace : ∀ operation ∈ cell.trace.operations, operation.Sound := by
    intro operation hoperation
    exact allSound_of_returns_zero name data.operations data.admissible run.returnsZero
      operation (trace_operation_mem data index operation hoperation)
  have hseparation := allSound_of_returns_zero name data.operations data.admissible
    run.returnsZero
    (separationOperation cell.trace.output (data.separation index))
    (separation_operation_mem data index)
  exact (data.separation index).sqrt_condition_of_lower_pos
    (output_contains_radicand_of_allSound cell hcoordinate htrace _ hregion)
    hseparation

theorem radicand_ne_zero
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide} {precision cells : ℕ}
    {name : String} {data : SeamData model side precision cells}
    (run : SeamRunVerdict name data) (t : I) :
    model.rectangleRadicand side (connectorPathPoint model t) ≠ 0 := by
  obtain ⟨index, hregion⟩ := data.covers t
  let cell := data.cell index
  have hcoordinate : ∀ operation ∈ cell.coordinateOperations, operation.Sound := by
    intro operation hoperation
    exact allSound_of_returns_zero name data.operations data.admissible run.returnsZero
      operation (coordinate_operation_mem data index operation hoperation)
  have htrace : ∀ operation ∈ cell.trace.operations, operation.Sound := by
    intro operation hoperation
    exact allSound_of_returns_zero name data.operations data.admissible run.returnsZero
      operation (trace_operation_mem data index operation hoperation)
  have hseparation := allSound_of_returns_zero name data.operations data.admissible
    run.returnsZero
    (separationOperation cell.trace.output (data.separation index))
    (separation_operation_mem data index)
  exact (data.separation index).ne_zero_of_lower_pos
    (output_contains_radicand_of_allSound cell hcoordinate htrace _ hregion)
    hseparation

/-- The principal square root is a continuous sheet along the certified seam path. -/
def principalPathSheet
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide} {precision cells : ℕ}
    {name : String} {data : SeamData model side precision cells}
    (run : SeamRunVerdict name data) :
    ChapterVIContinuousSquareRootSheet
      (fun t : I ↦ model.rectangleRadicand side (connectorPathPoint model t)) where
  root t := Complex.sqrt (model.rectangleRadicand side (connectorPathPoint model t))
  continuous_root := by
    rw [continuous_iff_continuousAt]
    intro t
    exact (Complex.continuousAt_sqrt (sqrt_condition run t)).comp_of_eq
      ((model.continuous_rectangleRadicand_of_coordinate_ne_zero side
        (model.rectanglePoint_ne_zero side)).continuousAt.comp_of_eq
          (continuous_const.prodMk continuous_id).continuousAt rfl) rfl
  root_sq t := by
    unfold Complex.sqrt
    exact Complex.cpow_nat_inv_pow _ (by norm_num : (2 : ℕ) ≠ 0)

/-- A branch-cut batch fixes the previously ambiguous local sign of any connector sheet already
normalized to the compiled outer principal sheet. -/
theorem connectorSheet_eq_localBoundaryRoot_zero
    (outerRun : ChapterVIDOuterArcPolarCompiledGrid.CompiledRunVerdict)
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide} {precision cells : ℕ}
    {name : String} {data : SeamData model side precision cells}
    (run : SeamRunVerdict name data)
    (sheet : ChapterVIContinuousSquareRootSheet (model.rectangleRadicand side))
    (houter : ∀ s : I,
      sheet.root (model.connectorBoundaryPoint side s) =
        model.connectorOuterBoundaryRoot outerRun side s) :
    sheet.root (model.connectorLocalBoundaryPoint side 0) =
      model.connectorLocalBoundaryRoot 0 := by
  let restricted : ChapterVIContinuousSquareRootSheet
      (fun t : I ↦ model.rectangleRadicand side (connectorPathPoint model t)) := {
    root := fun t ↦ sheet.root (connectorPathPoint model t)
    continuous_root := sheet.continuous_root.comp
      (continuous_const.prodMk continuous_id)
    root_sq := fun t ↦ sheet.root_sq _ }
  have hbase : restricted.root (outerParameter side) =
      (principalPathSheet run).root (outerParameter side) := by
    rw [show restricted.root (outerParameter side) =
        sheet.root (model.connectorBoundaryPoint side 0) by
      simp [restricted]]
    rw [houter 0]
    change Complex.sqrt
        (chapterVIDOuterArcRadicand side (model.connectorOuterBoundaryPoint side 0)) =
      Complex.sqrt
        (model.rectangleRadicand side (connectorPathPoint model (outerParameter side)))
    rw [← model.rectangleRadicand_connectorBoundaryPoint side 0]
    simp
  have hall := restricted.root_eq_of_eq_at (principalPathSheet run)
    (radicand_ne_zero run) (outerParameter side) hbase
  have hlocal := congrFun hall (localParameter side)
  rw [show restricted.root (localParameter side) =
      sheet.root (model.connectorLocalBoundaryPoint side 0) by
    simp [restricted]] at hlocal
  rw [show (principalPathSheet run).root (localParameter side) =
      Complex.sqrt (model.connectorLocalBoundaryRadicand 0) by
    simp [principalPathSheet, model.rectangleRadicand_connectorLocalBoundaryPoint]] at hlocal
  exact hlocal

/-- Two successful seam batches upgrade a certificate-selected connector pair to the fully
compatible five-piece contour package. -/
def toSeamCompatiblePair
    (outerRun : ChapterVIDOuterArcPolarCompiledGrid.CompiledRunVerdict)
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    (pair : ChapterVIDPrincipalConnectorModel.CertifiedConnectorPair outerRun model)
    {initialPrecision initialCells finalPrecision finalCells : ℕ}
    {initialName finalName : String}
    {initialData : SeamData model .initial initialPrecision initialCells}
    {finalData : SeamData model .final finalPrecision finalCells}
    (initialRun : SeamRunVerdict initialName initialData)
    (finalRun : SeamRunVerdict finalName finalData) :
    ChapterVIDPrincipalConnectorModel.SeamCompatibleCertifiedConnectorPair outerRun model where
  pair := pair
  initial_local_at_zero :=
    connectorSheet_eq_localBoundaryRoot_zero outerRun initialRun pair.initialSheet
      pair.initial_outer
  final_local_at_zero :=
    connectorSheet_eq_localBoundaryRoot_zero outerRun finalRun pair.finalSheet
      pair.final_outer

/-- End-to-end seam-selection theorem.  The existing continuum nonvanishing certificates create
the outer-normalized connector sheets; the two compiled branch-cut batches then prove that both
sheets reach the positive local Morse branch. -/
theorem exists_seamCompatiblePair_of_compiledCertificates
    (outerRun : ChapterVIDOuterArcPolarCompiledGrid.CompiledRunVerdict)
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (initialCertificate : ChapterVIDConnectorCompiledCertificate model .initial)
    (finalCertificate : ChapterVIDConnectorCompiledCertificate model .final)
    {initialPrecision initialCells finalPrecision finalCells : ℕ}
    {initialName finalName : String}
    {initialData : SeamData model .initial initialPrecision initialCells}
    {finalData : SeamData model .final finalPrecision finalCells}
    (initialRun : SeamRunVerdict initialName initialData)
    (finalRun : SeamRunVerdict finalName finalData) :
    Nonempty
      (ChapterVIDPrincipalConnectorModel.SeamCompatibleCertifiedConnectorPair outerRun model) := by
  obtain ⟨pair⟩ :=
    ChapterVIDPrincipalConnectorModel.exists_certifiedConnectorPair outerRun model
      initialCertificate finalCertificate
  exact ⟨toSeamCompatiblePair outerRun pair initialRun finalRun⟩

/-- The same compiled inputs produce a genuinely seam-compatible five-piece formal contribution
with Poincare's explicit logarithmic leading coefficient. -/
theorem exists_seamCompatibleContribution_tendsto_of_compiledCertificates
    (outerRun : ChapterVIDOuterArcPolarCompiledGrid.CompiledRunVerdict)
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (initialCertificate : ChapterVIDConnectorCompiledCertificate model .initial)
    (finalCertificate : ChapterVIDConnectorCompiledCertificate model .final)
    {initialPrecision initialCells finalPrecision finalCells : ℕ}
    {initialName finalName : String}
    {initialData : SeamData model .initial initialPrecision initialCells}
    {finalData : SeamData model .final finalPrecision finalCells}
    (initialRun : SeamRunVerdict initialName initialData)
    (finalRun : SeamRunVerdict finalName finalData) :
    ∃ compatible :
        ChapterVIDPrincipalConnectorModel.SeamCompatibleCertifiedConnectorPair outerRun model,
      Filter.Tendsto
        (fun k : ℝ ↦ (-Real.log k)⁻¹ • compatible.fivePieceContribution k)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds ((2 * Real.pi * Complex.I : ℂ)⁻¹ *
          chapterVIDPrincipalMorseAmplitude massProduct b d (0, 0))) := by
  obtain ⟨compatible⟩ := exists_seamCompatiblePair_of_compiledCertificates outerRun model
    initialCertificate finalCertificate initialRun finalRun
  exact ⟨compatible, compatible.tendsto_fivePiece_inv_neg_log_smul⟩

end ChapterVIDConnectorSeamCompiledGrid

end PoincareChapterVI
