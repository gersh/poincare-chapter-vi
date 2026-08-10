/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.ChapterVIDRadialTailBaseConstantTrace
import PoincareChapterVI.ChapterVIDRadialTailBaseCenteredAffineTrace
import PoincareChapterVI.ChapterVINonuniformGrid

/-! # Formally rounded cell inputs for the radial-tail affine table -/

namespace PoincareChapterVI

open ChapterVILeanCompCertBatch

namespace ChapterVIDRadialTailCellInputTrace

open ChapterVIDRadialTailBaseConstants
open ChapterVILeanCompCertAffineTrace

abbrev Interval := ChapterVISignedDyadicInterval 40
abbrev Rectangle := ChapterVISignedDyadicComplexRectangle 40
abbrev Model := ChapterVILeanCompCertAffineTrace.Model 40

def enclose (x : ℚ) : Interval :=
  ⟨⌊x * (2 : ℚ) ^ 40⌋, ⌈x * (2 : ℚ) ^ 40⌉⟩

theorem enclose_contains (x : ℚ) : (enclose x).Contains (x : ℝ) := by
  have hl : ((⌊x * (2 : ℚ) ^ 40⌋ : ℤ) : ℚ) ≤ x * (2 : ℚ) ^ 40 :=
    Int.floor_le _
  have hu : x * (2 : ℚ) ^ 40 ≤ ((⌈x * (2 : ℚ) ^ 40⌉ : ℤ) : ℚ) :=
    Int.le_ceil _
  constructor
  · change ((⌊x * (2 : ℚ) ^ 40⌋ : ℤ) : ℝ) / (2 : ℝ) ^ 40 ≤ (x : ℝ)
    rw [div_le_iff₀ (by positivity)]
    exact_mod_cast hl
  · change (x : ℝ) ≤ ((⌈x * (2 : ℚ) ^ 40⌉ : ℤ) : ℝ) / (2 : ℝ) ^ 40
    rw [le_div_iff₀ (by positivity)]
    exact_mod_cast hu

def zeroRectangle : Rectangle :=
  ChapterVISignedDyadicComplexRectangle.pointInt 40 0

def realRectangle (x : Interval) : Rectangle := ⟨x, zeroInterval⟩

def radialRow (row : Fin 6) : Nat := row.val + 22

def rowStart (row : Fin 6) : ℚ := chapterVICubicClusterNode 28 (radialRow row)
def rowEnd (row : Fin 6) : ℚ := chapterVICubicClusterNode 28 (radialRow row + 1)

def radialStart (row : Fin 6) (index : Fin 16) : ℚ :=
  rowStart row + (rowEnd row - rowStart row) * index.val / 16

def radialEnd (row : Fin 6) (index : Fin 16) : ℚ :=
  rowStart row + (rowEnd row - rowStart row) * (index.val + 1) / 16

def radialCenter (row : Fin 6) (index : Fin 16) : ℚ :=
  (radialStart row index + radialEnd row index) / 2

def radialHalfWidth (row : Fin 6) (index : Fin 16) : ℚ :=
  (radialEnd row index - radialStart row index) / 2

def pCenterData : Array Interval := #[
⟨515126394360, 515126394385⟩,
  ⟨513003050457, 513003050483⟩,
  ⟨510834832022, 510834832048⟩,
  ⟨508619598199, 508619598225⟩,
  ⟨506355046046, 506355046073⟩,
  ⟨504038693513, 504038693541⟩,
  ⟨501667860027, 501667860056⟩,
  ⟨499239644385, 499239644414⟩,
  ⟨496750899482, 496750899511⟩,
  ⟨494198203194, 494198203225⟩,
  ⟨491577824829, 491577824860⟩,
  ⟨488885686285, 488885686316⟩,
  ⟨486117316743, 486117316775⟩,
  ⟨483267799742, 483267799776⟩,
  ⟨480331710820, 480331710855⟩,
  ⟨477303043852, 477303043887⟩,
  ⟨474697849797, 474697849833⟩,
  ⟨472553875865, 472553875902⟩,
  ⟨470360133306, 470360133344⟩,
  ⟨468114007393, 468114007432⟩,
  ⟨465812664890, 465812664930⟩,
  ⟨463453028488, 463453028529⟩,
  ⟨461031747519, 461031747560⟩,
  ⟨458545163921, 458545163964⟩,
  ⟨455989272986, 455989273030⟩,
  ⟨453359677257, 453359677302⟩,
  ⟨450651532532, 450651532578⟩,
  ⟨447859484201, 447859484248⟩,
  ⟨444977591710, 444977591759⟩,
  ⟨441999238200, 441999238251⟩,
  ⟨438917022076, 438917022128⟩,
  ⟨435722625531, 435722625586⟩,
  ⟨433069068779, 433069068835⟩,
  ⟨431010099168, 431010099225⟩,
  ⟨428900742630, 428900742688⟩,
  ⟨426738204044, 426738204104⟩,
  ⟨424519441298, 424519441340⟩,
  ⟨422241134517, 422241134580⟩,
  ⟨419899650818, 419899650883⟩,
  ⟨417491003005, 417491003072⟩,
  ⟨415010800935, 415010801003⟩,
  ⟨412454194641, 412454194711⟩,
  ⟨409815806418, 409815806490⟩,
  ⟨407089650318, 407089650393⟩,
  ⟨404269034815, 404269034892⟩,
  ⟨401346445687, 401346445767⟩,
  ⟨398313402785, 398313402868⟩,
  ⟨395160284079, 395160284165⟩,
  ⟨392687672989, 392687673078⟩,
  ⟨390964399232, 390964399323⟩,
  ⟨389202288037, 389202288129⟩,
  ⟨387399360114, 387399360210⟩,
  ⟨385553475814, 385553475912⟩,
  ⟨383662317026, 383662317126⟩,
  ⟨381723366429, 381723366531⟩,
  ⟨379733883571, 379733883676⟩,
  ⟨377690877385, 377690877493⟩,
  ⟨375591073917, 375591074028⟩,
  ⟨373430879035, 373430879148⟩,
  ⟨371206334500, 371206334617⟩,
  ⟨368913066212, 368913066333⟩,
  ⟨366546222802, 366546222927⟩,
  ⟨364100402353, 364100402481⟩,
  ⟨361569564321, 361569564454⟩,
  ⟨359785488902, 359785489039⟩,
  ⟨358806205244, 358806205383⟩,
  ⟨357813372714, 357813372854⟩,
  ⟨356806571748, 356806571890⟩,
  ⟨355785362695, 355785362839⟩,
  ⟨354749283900, 354749284046⟩,
  ⟨353697850636, 353697850784⟩,
  ⟨352630553164, 352630553314⟩,
  ⟨351546855159, 351546855311⟩,
  ⟨350446191747, 350446191902⟩,
  ⟨349327967360, 349327967518⟩,
  ⟨348191553645, 348191553805⟩,
  ⟨347036286643, 347036286805⟩,
  ⟨345861464234, 345861464400⟩,
  ⟨344666342996, 344666343164⟩,
  ⟨343450135068, 343450135240⟩,
  ⟨342745371882, 342745372055⟩,
  ⟨342568043686, 342568043859⟩,
  ⟨342390255277, 342390255451⟩,
  ⟨342212004134, 342212004308⟩,
  ⟨342033287542, 342033287717⟩,
  ⟨341854102761, 341854102936⟩,
  ⟨341674447199, 341674447375⟩,
  ⟨341494318070, 341494318246⟩,
  ⟨341313712559, 341313712735⟩,
  ⟨341132628003, 341132628180⟩,
  ⟨340951061538, 340951061716⟩,
  ⟨340769010277, 340769010455⟩,
  ⟨340586471479, 340586471658⟩,
  ⟨340403442204, 340403442383⟩,
  ⟨340219919485, 340219919664⟩,
  ⟨340035900502, 340035900682⟩
]

def pCenter (row : Fin 6) (index : Fin 16) : Interval :=
  let raw := pCenterData[row.val * 16 + index.val]'(by
    have hr := row.isLt
    have hi := index.isLt
    have hs : pCenterData.size = 96 := by decide +kernel
    rw [hs]
    omega)
  ⟨raw.lower - 4, raw.upper + 4⟩

def one : Interval := ChapterVISignedDyadicInterval.pointInt 40 1
def qdot : Interval := qD.sub one

def qCenterProduct (row : Fin 6) (index : Fin 16) : Interval :=
  ChapterVILeanCompCertProposals.mul 40 (enclose (radialCenter row index)) qdot

def qCenter (row : Fin 6) (index : Fin 16) : Interval :=
  one.add (qCenterProduct row index)

def pRootTrace (row : Fin 6) (index : Fin 16) :=
  ChapterVILeanCompCertProposals.sixthRootTrace
    (qCenter row index) (pCenter row index)

theorem pRootTrace_valid (row : Fin 6) (index : Fin 16) :
    (pRootTrace row index).Valid := by
  unfold ChapterVILeanCompCertRoots.SixthRootTrace.Valid
  fin_cases row <;> fin_cases index <;>
    decide +kernel

def pSq (row : Fin 6) (index : Fin 16) : Interval :=
  ChapterVILeanCompCertProposals.mul 40 (pCenter row index) (pCenter row index)

def pFourth (row : Fin 6) (index : Fin 16) : Interval :=
  ChapterVILeanCompCertProposals.mul 40 (pSq row index) (pSq row index)

def pFifth (row : Fin 6) (index : Fin 16) : Interval :=
  ChapterVILeanCompCertProposals.mul 40 (pFourth row index) (pCenter row index)

def pFifthInv (row : Fin 6) (index : Fin 16) : Interval :=
  ChapterVILeanCompCertProposals.positiveReciprocal 40 (pFifth row index)

def pDotRaw (row : Fin 6) (index : Fin 16) : Interval :=
  ChapterVILeanCompCertProposals.mul 40 qdot (pFifthInv row index)

def pDot (row : Fin 6) (index : Fin 16) : Interval :=
  ChapterVILeanCompCertProposals.mul 40 (pDotRaw row index) (enclose (1 / 6))

def radialCoefficient (row : Fin 6) (index : Fin 16) : Interval :=
  ChapterVILeanCompCertProposals.mul 40 (pDot row index)
    (enclose (radialHalfWidth row index))

def secondDerivativeBound : Fin 6 → ℕ
  | 0 => 1500
  | 1 => 4400
  | 2 => 14400
  | 3 => 38600
  | 4 => 54700
  | 5 => 78500

def errorBudget (row : Fin 6) (index : Fin 16) : ℤ :=
  (enclose ((secondDerivativeBound row : ℚ) *
    radialHalfWidth row index ^ 2)).upper + 1

def pModel (row : Fin 6) (index : Fin 16) : Model :=
  { center := realRectangle (pCenter row index)
    radial := realRectangle (radialCoefficient row index)
    angular := zeroRectangle
    error := realRectangle ⟨-errorBudget row index, errorBudget row index⟩ }

def pOperations (row : Fin 6) (index : Fin 16) : List (DyadicOperation 40) :=
  [ .mul (enclose (radialCenter row index)) qdot (qCenterProduct row index) ] ++
    (pRootTrace row index).operations ++
    [ .mul (pCenter row index) (pCenter row index) (pSq row index)
    , .mul (pSq row index) (pSq row index) (pFourth row index)
    , .mul (pFourth row index) (pCenter row index) (pFifth row index)
    , .positiveReciprocal (pFifth row index) (pFifthInv row index)
    , .mul qdot (pFifthInv row index) (pDotRaw row index)
    , .mul (pDotRaw row index) (enclose (1 / 6)) (pDot row index)
    , .mul (pDot row index) (enclose (radialHalfWidth row index))
        (radialCoefficient row index) ]

def angularCells (side : ChapterVIDPinchingArcSide) (row : Fin 6) : Nat :=
  match side with
  | .upper => 64
  | .lower => if row.val < 2 then 128 else 64

def angularStart (side : ChapterVIDPinchingArcSide) (row : Fin 6)
    (index : Fin (angularCells side row)) : ℚ :=
  (index.val : ℚ) ^ 2 / angularCells side row ^ 2

def angularEnd (side : ChapterVIDPinchingArcSide) (row : Fin 6)
    (index : Fin (angularCells side row)) : ℚ :=
  ((index.val + 1 : ℕ) : ℚ) ^ 2 / angularCells side row ^ 2

def angularCenter (side : ChapterVIDPinchingArcSide) (row : Fin 6)
    (index : Fin (angularCells side row)) : ℚ :=
  (angularStart side row index + angularEnd side row index) / 2

def angularHalfWidth (side : ChapterVIDPinchingArcSide) (row : Fin 6)
    (index : Fin (angularCells side row)) : ℚ :=
  (angularEnd side row index - angularStart side row index) / 2

def tModel (side : ChapterVIDPinchingArcSide) (row : Fin 6)
    (index : Fin (angularCells side row)) : Model :=
  { center := realRectangle (enclose (angularCenter side row index))
    radial := zeroRectangle
    angular := realRectangle (enclose (angularHalfWidth side row index))
    error := zeroRectangle }

def remainderBudget : ℤ := 2945894

def remainderModel : Model :=
  { center := zeroRectangle, radial := zeroRectangle, angular := zeroRectangle
    error := ⟨⟨-remainderBudget, remainderBudget⟩,
      ⟨-remainderBudget, remainderBudget⟩⟩ }

/-! ## Semantic meaning of the rounded centres and linear coefficients -/

private theorem realRectangle_contains {interval : Interval} {value : ℝ}
    (hvalue : interval.Contains value) : (realRectangle interval).Contains (value : ℂ) := by
  constructor
  · simpa [realRectangle] using hvalue
  · simpa [realRectangle, zeroInterval] using
      ChapterVISignedDyadicInterval.pointInt_contains 40 0

private theorem qdot_contains : qdot.Contains
    (chapterVIDCriticalParameterModulus - 1) := by
  exact ChapterVISignedDyadicInterval.sub_contains
    ChapterVIDRadialTailBaseConstants.qD_contains
    (by simpa [one] using ChapterVISignedDyadicInterval.pointInt_contains 40 1)

theorem qCenter_contains (row : Fin 6) (index : Fin 16) :
    (qCenter row index).Contains
      (chapterVIDCertificateParameterReal (radialCenter row index : ℝ)) := by
  have hproduct := (ChapterVILeanCompCertProposals.mul_sound 40
    (enclose (radialCenter row index)) qdot).contains_mul
      (enclose_contains _) qdot_contains
  have hone := ChapterVISignedDyadicInterval.pointInt_contains 40 1
  have hsum := ChapterVISignedDyadicInterval.add_contains hone hproduct
  simpa [qCenter, qCenterProduct, chapterVIDCertificateParameterReal,
    one, qdot] using hsum

theorem pCenter_contains (row : Fin 6) (index : Fin 16) :
    (pCenter row index).Contains
      (chapterVIDCertificateParameterReal (radialCenter row index : ℝ) ^
        ((6 : ℝ)⁻¹)) := by
  apply (pRootTrace row index).output_contains_of_valid (pRootTrace_valid row index)
  · exact ChapterVILeanCompCertProposals.sixthRootTrace_operations_sound _ _
  · exact (chapterVIDRadialTailRealInputs_pos
      (by
        change 0 ≤ (radialCenter row index : ℝ)
        fin_cases row <;> fin_cases index <;>
          norm_num [radialCenter, radialStart, radialEnd, rowStart, rowEnd,
            radialRow, chapterVICubicClusterNode])
      (by
        change (radialCenter row index : ℝ) ≤ 1
        fin_cases row <;> fin_cases index <;>
          norm_num [radialCenter, radialStart, radialEnd, rowStart, rowEnd,
            radialRow, chapterVICubicClusterNode])).1.le
  · exact qCenter_contains row index

private theorem pFifth_contains (row : Fin 6) (index : Fin 16) :
    (pFifth row index).Contains
      ((chapterVIDCertificateParameterReal (radialCenter row index : ℝ) ^
          ((6 : ℝ)⁻¹)) ^ 5) := by
  let value := chapterVIDCertificateParameterReal (radialCenter row index : ℝ) ^
    ((6 : ℝ)⁻¹)
  have hp : (pCenter row index).Contains value := pCenter_contains row index
  have hsq := (ChapterVILeanCompCertProposals.mul_sound 40
    (pCenter row index) (pCenter row index)).contains_mul hp hp
  have hfourth := (ChapterVILeanCompCertProposals.mul_sound 40
    (pSq row index) (pSq row index)).contains_mul hsq hsq
  have hfifth := (ChapterVILeanCompCertProposals.mul_sound 40
    (pFourth row index) (pCenter row index)).contains_mul hfourth hp
  change (ChapterVILeanCompCertProposals.mul 40
    (ChapterVILeanCompCertProposals.mul 40
      (ChapterVILeanCompCertProposals.mul 40 (pCenter row index) (pCenter row index))
      (ChapterVILeanCompCertProposals.mul 40 (pCenter row index) (pCenter row index)))
    (pCenter row index)).Contains (value ^ 5)
  convert hfifth using 1
  · rfl
  · ring

private theorem pFifthInv_contains (row : Fin 6) (index : Fin 16) :
    (pFifthInv row index).Contains
      ((chapterVIDCertificateParameterReal (radialCenter row index : ℝ) ^
          ((6 : ℝ)⁻¹)) ^ 5)⁻¹ := by
  have hpositive : 0 < (pFifth row index).lower := by
    fin_cases row <;> fin_cases index <;> decide +kernel
  have hwf : (pFifth row index).lower ≤ (pFifth row index).upper :=
    (ChapterVILeanCompCertProposals.mul_sound 40
      (pFourth row index) (pCenter row index)).output_wf
  exact (ChapterVILeanCompCertProposals.positiveReciprocal_sound 40
    (pFifth row index) hpositive hwf).contains_inv (pFifth_contains row index)

theorem radialCoefficient_contains (row : Fin 6) (index : Fin 16) :
    (radialCoefficient row index).Contains
      ((chapterVIDCriticalParameterModulus - 1) /
          (6 * (chapterVIDCertificateParameterReal (radialCenter row index : ℝ) ^
            ((6 : ℝ)⁻¹)) ^ 5) * (radialHalfWidth row index : ℝ)) := by
  let pvalue := chapterVIDCertificateParameterReal (radialCenter row index : ℝ) ^
    ((6 : ℝ)⁻¹)
  have hraw := (ChapterVILeanCompCertProposals.mul_sound 40 qdot
    (pFifthInv row index)).contains_mul qdot_contains (pFifthInv_contains row index)
  have hsixth := enclose_contains (1 / 6)
  have hdot := (ChapterVILeanCompCertProposals.mul_sound 40
    (pDotRaw row index) (enclose (1 / 6))).contains_mul hraw hsixth
  have hhalf := enclose_contains (radialHalfWidth row index)
  have hcoefficient := (ChapterVILeanCompCertProposals.mul_sound 40
    (pDot row index) (enclose (radialHalfWidth row index))).contains_mul hdot hhalf
  change (ChapterVILeanCompCertProposals.mul 40
    (ChapterVILeanCompCertProposals.mul 40
      (ChapterVILeanCompCertProposals.mul 40 qdot (pFifthInv row index))
      (enclose (1 / 6)))
    (enclose (radialHalfWidth row index))).Contains _
  convert hcoefficient using 1
  · simp [pDot, pDotRaw]
  · have hsixCast : ((↑(1 / 6 : ℚ) : ℝ)) = (6 : ℝ)⁻¹ := by norm_num
    rw [div_eq_mul_inv, mul_inv_rev, hsixCast]
    ac_rfl

end ChapterVIDRadialTailCellInputTrace

end PoincareChapterVI
