/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.ChapterVIDConnectorFactorMonotonicity

/-!
# The scale-aware crossing boundary for the D connector seams

The direct factor rectangles prove principal-slit separation away from a 261-cell collar at each
local endpoint.  Inside that collar, the derivative and curvature campaigns prove that the
imaginary part of the first factor is strictly increasing and that the companion factor stays in
the open right half-plane.  The only remaining numerical fact is therefore the sign of the first
factor at its (at most one) real-axis crossing.

`PositiveCrossingCertificate` records precisely that fact.  This file proves that this one
predicate, together with the already compiled campaigns and connector nonvanishing certificate,
determines the seam sign and reaches Poincare's logarithmic leading term.  It is the semantic
target for a dependency-preserving LeanCompCert certificate; no finite computation is hidden in
the assembly below.
-/

noncomputable section

open Set Topology
open scoped unitInterval

namespace PoincareChapterVI
namespace ChapterVIDConnectorFactorCrossing

open ChapterVIDConnectorFactorBulkReference
open ChapterVIDConnectorFactorMonotonicity
open ChapterVIDConnectorSeamCompiledGrid
open ChapterVILeanCompCertBatch
open ChapterVILeanCompCertAttestation

/-- The sole scale-aware finite claim still needed in the endpoint collars. -/
structure PositiveCrossingCertificate
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) : Prop where
  plus_re_nonneg_of_im_eq_zero : ∀ t : I, (t : ℝ) ∈ collarInterval side →
    (model.rectangleFactorPlus side (connectorPathPoint model t)).im = 0 →
    0 ≤ (model.rectangleFactorPlus side (connectorPathPoint model t)).re

/-- A dependency-preserving finite crossing campaign.  The generated data chooses the integer
claims; its semantic bridge proves that soundness of those claims implies the crossing theorem.
This is deliberately more general than rectangular interval arithmetic, which loses the common
endpoint scale and cannot settle the terminal cells. -/
structure CompiledCrossingData
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) (precision : ℕ) where
  operations : List (DyadicOperation precision)
  admissible : LeanCompCert.Ports.SignedProductClaims.Admissible
    (batchClaims operations)
  sound : (∀ operation ∈ operations, operation.Sound) →
    PositiveCrossingCertificate model side

/-- A zero verdict from the exact LeanCompCert computation attached to the crossing data. -/
structure CompiledCrossingRunVerdict
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide} {precision : ℕ}
    (name : String) (data : CompiledCrossingData model side precision) : Prop where
  returnsZero : (batchComputation name data.operations).Returns ((0 : ℕ) : Int)

/-- Kernel reconstruction of the semantic crossing theorem from a successful compiled batch. -/
theorem CompiledCrossingRunVerdict.toPositiveCrossingCertificate
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide} {precision : ℕ}
    {name : String} {data : CompiledCrossingData model side precision}
    (run : CompiledCrossingRunVerdict name data) :
    PositiveCrossingCertificate model side := by
  apply data.sound
  intro operation hoperation
  exact allSound_of_returns_zero name data.operations data.admissible run.returnsZero
    operation hoperation

/-- Receipt ingestion for the exact Lean-derived crossing artifact. -/
theorem CompiledCrossingRunVerdict.ofReceipt
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide} {precision : ℕ}
    (name : String) (data : CompiledCrossingData model side precision)
    (crypto : LeanCompCert.Attest.ReceiptCrypto)
    (receipt : LeanCompCert.Attest.RunReceipt)
    (kind : LeanCompCert.Attest.AttestationKind) (params nonce : String)
    (bound : LeanCompCert.Attest.receiptBindsProved crypto
      (batchArtifact name data.operations) kind params nonce ((0 : ℕ) : Int) receipt = true)
    (admitted : LeanCompCert.Attest.RunAdmission crypto
      (batchArtifact name data.operations) receipt) :
    CompiledCrossingRunVerdict name data :=
  ⟨returns_zero_of_receipt name data.operations crypto receipt kind params nonce
    bound admitted⟩

/-- Outside the endpoint collar, the retained direct-factor mesh covers the path. -/
theorem dist_ge_cutoff_of_not_mem_collar
    (side : ChapterVIDOuterArcSide) (t : I)
    (ht : (t : ℝ) ∉ collarInterval side) :
    (collarCells : ℝ) / meshCells ≤ dist t (localParameter side) := by
  rw [dist_localParameter_eq]
  cases side with
  | initial =>
      simp only [collarInterval, Set.mem_Icc, not_and_or, not_le] at ht
      simp only [collarCells, meshCells]
      rcases ht with ht | ht
      · norm_num at ht ⊢
        linarith
      · exfalso
        exact (not_lt_of_ge t.property.2) ht
  | final =>
      simp only [collarInterval, Set.mem_Icc, not_and_or, not_le] at ht
      simp only [collarCells, meshCells]
      rcases ht with ht | ht
      · exfalso
        exact (not_lt_of_ge t.property.1) ht
      · norm_num at ht ⊢
        exact ht.le

/-- Connector nonvanishing and the exact factorization make both individual factors nonzero. -/
theorem factors_ne_zero
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide}
    (certificate : ChapterVIDConnectorCompiledCertificate model side)
    (t : I) :
    model.rectangleFactorPlus side (connectorPathPoint model t) ≠ 0 ∧
      model.rectangleFactorMinus side (connectorPathPoint model t) ≠ 0 := by
  have hradicand := certificate.radicand.ne_zero (connectorPathPoint model t)
  have hfactor := model.rectangleRadicand_eq_factor_mul side (connectorPathPoint model t)
  constructor
  · intro hzero
    apply hradicand
    rw [hfactor, hzero, zero_mul]
  · intro hzero
    apply hradicand
    rw [hfactor, hzero, mul_zero]

/-- The direct mesh and the one crossing predicate give the principal-sqrt continuity condition
for the first factor; the derivative/curvature campaigns give it for the companion factor. -/
theorem sqrt_conditions
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDAnchoredConnectorModel massProduct b d)
    (bulkRun : ChapterVIDConnectorFactorBulkReference.ReferenceCompiledRunVerdict)
    (derivativeRun :
      ChapterVIDConnectorFactorDerivativeReference.ReferenceCompiledRunVerdict)
    (curvatureRun :
      ChapterVIDConnectorFactorSecondDerivativeReference.ReferenceCompiledRunVerdict)
    (side : ChapterVIDOuterArcSide)
    (crossing : PositiveCrossingCertificate
      model.toChapterVIDPrincipalConnectorModel side)
    (t : I) :
    (0 ≤ (model.rectangleFactorPlus side
        (connectorPathPoint model.toChapterVIDPrincipalConnectorModel t)).re ∨
      (model.rectangleFactorPlus side
        (connectorPathPoint model.toChapterVIDPrincipalConnectorModel t)).im ≠ 0) ∧
    (0 ≤ (model.rectangleFactorMinus side
        (connectorPathPoint model.toChapterVIDPrincipalConnectorModel t)).re ∨
      (model.rectangleFactorMinus side
        (connectorPathPoint model.toChapterVIDPrincipalConnectorModel t)).im ≠ 0) := by
  by_cases hcollar : (t : ℝ) ∈ collarInterval side
  · constructor
    · by_cases him :
          (model.rectangleFactorPlus side
            (connectorPathPoint model.toChapterVIDPrincipalConnectorModel t)).im = 0
      · exact Or.inl (crossing.plus_re_nonneg_of_im_eq_zero t hcollar him)
      · exact Or.inr him
    · exact Or.inl
        (companion_re_pos_on_collar model.toChapterVIDPrincipalConnectorModel
          derivativeRun curvatureRun side t hcollar).le
  · have hbulk := dist_ge_cutoff_of_not_mem_collar side t hcollar
    have hregion := connectorPathPoint_mem_bulkMeshIndex
      model.toChapterVIDPrincipalConnectorModel side t hbulk
    have hregion' : connectorPathPoint model.toChapterVIDPrincipalConnectorModel t ∈
        (cell model.toChapterVIDPrincipalConnectorModel side (bulkMeshIndex side t)).region := by
      rw [cell_region, retainedMeshIndex_bulkMeshIndex]
      exact hregion
    have hfacts := bulkRun.cell_facts model.toChapterVIDPrincipalConnectorModel side
      (bulkMeshIndex side t)
      (connectorPathPoint model.toChapterVIDPrincipalConnectorModel t) hregion'
    exact ⟨(plusSeparation side (bulkMeshIndex side t)).sqrt_condition_of_value_pos hfacts.1,
      (minusSeparation side (bulkMeshIndex side t)).sqrt_condition_of_value_pos hfacts.2⟩

/-- The direct factor campaign fixes the product of principal roots at the outer endpoint. -/
theorem outer_arg_add_mem
    {massProduct : ℂ} {b d : ℤ}
    (bulkRun : ChapterVIDConnectorFactorBulkReference.ReferenceCompiledRunVerdict)
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) :
    Complex.arg (model.rectangleFactorPlus side
        (connectorPathPoint model (outerParameter side))) +
      Complex.arg (model.rectangleFactorMinus side
        (connectorPathPoint model (outerParameter side))) ∈
      Set.Ioc (-Real.pi) Real.pi := by
  have hfacts := bulkRun.cell_facts model side (outerIndex side) _
    (connectorPathPoint_outer_mem model side)
  cases side with
  | initial =>
      have hplus := hfacts.1
      have hminus := hfacts.2
      rw [outer_plus_label] at hplus
      rw [outer_minus_label] at hminus
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
      rw [outer_plus_label] at hplus
      rw [outer_minus_label] at hminus
      exact arg_add_mem_Ioc_of_im_pos_neg
        (by simpa [outerPlusSeparation, SlitPlaneSeparation.value,
          SlitPlaneSeparation.toZeroSeparation,
          ChapterVIComplexZeroSeparation.value] using hplus)
        (by simpa [outerMinusSeparation, SlitPlaneSeparation.value,
          SlitPlaneSeparation.toZeroSeparation,
          ChapterVIComplexZeroSeparation.value] using hminus)

/-- Product of the two principal factor roots along the connector path. -/
def factorPathSheet
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDAnchoredConnectorModel massProduct b d)
    (bulkRun : ChapterVIDConnectorFactorBulkReference.ReferenceCompiledRunVerdict)
    (derivativeRun :
      ChapterVIDConnectorFactorDerivativeReference.ReferenceCompiledRunVerdict)
    (curvatureRun :
      ChapterVIDConnectorFactorSecondDerivativeReference.ReferenceCompiledRunVerdict)
    (side : ChapterVIDOuterArcSide)
    (crossing : PositiveCrossingCertificate
      model.toChapterVIDPrincipalConnectorModel side) :
    ChapterVIContinuousSquareRootSheet
      (fun t : I ↦ model.rectangleRadicand side
        (connectorPathPoint model.toChapterVIDPrincipalConnectorModel t)) where
  root t :=
    Complex.sqrt (model.rectangleFactorPlus side
      (connectorPathPoint model.toChapterVIDPrincipalConnectorModel t)) *
      Complex.sqrt (model.rectangleFactorMinus side
        (connectorPathPoint model.toChapterVIDPrincipalConnectorModel t))
  continuous_root := by
    have hpath : Continuous (connectorPathPoint model.toChapterVIDPrincipalConnectorModel) :=
      continuous_const.prodMk continuous_id
    have hplus : Continuous
        (fun t : I ↦ Complex.sqrt
          (model.rectangleFactorPlus side
            (connectorPathPoint model.toChapterVIDPrincipalConnectorModel t))) := by
      rw [continuous_iff_continuousAt]
      intro t
      exact (Complex.continuousAt_sqrt
        (sqrt_conditions model bulkRun derivativeRun curvatureRun side crossing t).1).comp_of_eq
          ((model.continuous_rectangleFactorPlus side).comp hpath).continuousAt rfl
    have hminus : Continuous
        (fun t : I ↦ Complex.sqrt
          (model.rectangleFactorMinus side
            (connectorPathPoint model.toChapterVIDPrincipalConnectorModel t))) := by
      rw [continuous_iff_continuousAt]
      intro t
      exact (Complex.continuousAt_sqrt
        (sqrt_conditions model bulkRun derivativeRun curvatureRun side crossing t).2).comp_of_eq
          ((model.continuous_rectangleFactorMinus side).comp hpath).continuousAt rfl
    exact hplus.mul hminus
  root_sq t := by
    rw [mul_pow]
    have hplus := Complex.cpow_nat_inv_pow
      (model.rectangleFactorPlus side
        (connectorPathPoint model.toChapterVIDPrincipalConnectorModel t))
      (by norm_num : (2 : ℕ) ≠ 0)
    have hminus := Complex.cpow_nat_inv_pow
      (model.rectangleFactorMinus side
        (connectorPathPoint model.toChapterVIDPrincipalConnectorModel t))
      (by norm_num : (2 : ℕ) ≠ 0)
    change Complex.sqrt
        (model.rectangleFactorPlus side
          (connectorPathPoint model.toChapterVIDPrincipalConnectorModel t)) ^ 2 *
      Complex.sqrt
        (model.rectangleFactorMinus side
          (connectorPathPoint model.toChapterVIDPrincipalConnectorModel t)) ^ 2 = _
    rw [show Complex.sqrt
          (model.rectangleFactorPlus side
            (connectorPathPoint model.toChapterVIDPrincipalConnectorModel t)) ^ 2 =
          model.rectangleFactorPlus side
            (connectorPathPoint model.toChapterVIDPrincipalConnectorModel t) by exact hplus,
      show Complex.sqrt
          (model.rectangleFactorMinus side
            (connectorPathPoint model.toChapterVIDPrincipalConnectorModel t)) ^ 2 =
          model.rectangleFactorMinus side
            (connectorPathPoint model.toChapterVIDPrincipalConnectorModel t) by exact hminus]
    exact (model.rectangleRadicand_eq_factor_mul side _).symm

theorem factorPathSheet_outer
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDAnchoredConnectorModel massProduct b d)
    (bulkRun : ChapterVIDConnectorFactorBulkReference.ReferenceCompiledRunVerdict)
    (derivativeRun :
      ChapterVIDConnectorFactorDerivativeReference.ReferenceCompiledRunVerdict)
    (curvatureRun :
      ChapterVIDConnectorFactorSecondDerivativeReference.ReferenceCompiledRunVerdict)
    (side : ChapterVIDOuterArcSide)
    (crossing : PositiveCrossingCertificate
      model.toChapterVIDPrincipalConnectorModel side)
    (certificate : ChapterVIDConnectorCompiledCertificate
      model.toChapterVIDPrincipalConnectorModel side) :
    (factorPathSheet model bulkRun derivativeRun curvatureRun side crossing).root
        (outerParameter side) =
      Complex.sqrt (model.rectangleRadicand side
        (connectorPathPoint model.toChapterVIDPrincipalConnectorModel
          (outerParameter side))) := by
  have hne := factors_ne_zero certificate (outerParameter side)
  have hmul := sqrt_mul_of_arg_add_mem hne.1 hne.2
    (outer_arg_add_mem bulkRun model.toChapterVIDPrincipalConnectorModel side)
  rw [model.rectangleRadicand_eq_factor_mul]
  exact hmul.symm

theorem factorPathSheet_local
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDAnchoredConnectorModel massProduct b d)
    (bulkRun : ChapterVIDConnectorFactorBulkReference.ReferenceCompiledRunVerdict)
    (derivativeRun :
      ChapterVIDConnectorFactorDerivativeReference.ReferenceCompiledRunVerdict)
    (curvatureRun :
      ChapterVIDConnectorFactorSecondDerivativeReference.ReferenceCompiledRunVerdict)
    (side : ChapterVIDOuterArcSide)
    (crossing : PositiveCrossingCertificate
      model.toChapterVIDPrincipalConnectorModel side)
    (certificate : ChapterVIDConnectorCompiledCertificate
      model.toChapterVIDPrincipalConnectorModel side) :
    (factorPathSheet model bulkRun derivativeRun curvatureRun side crossing).root
        (localParameter side) = model.connectorLocalBoundaryRoot 0 := by
  let point := connectorPathPoint model.toChapterVIDPrincipalConnectorModel (localParameter side)
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
  have hlocal : (localParameter side : ℝ) ∈ collarInterval side := by
    cases side <;> norm_num [localParameter, collarInterval]
  have hyRe : 0 < y.re := by
    change 0 < (model.rectangleFactorMinus side
      (connectorPathPoint model.toChapterVIDPrincipalConnectorModel
        (localParameter side))).re
    exact companion_re_pos_on_collar model.toChapterVIDPrincipalConnectorModel
      derivativeRun curvatureRun side (localParameter side) hlocal
  have harg := arg_add_mem_Ioc_of_mul_re_pos_im_zero_of_right hprodRe hprodIm hyRe
  have hne := factors_ne_zero certificate (localParameter side)
  have hmul := sqrt_mul_of_arg_add_mem hne.1 hne.2 harg
  change Complex.sqrt x * Complex.sqrt y = model.connectorLocalBoundaryRoot 0
  rw [← hmul, hprod]
  rfl

/-- A scale-aware crossing certificate fixes the local sign of any outer-normalized connector
sheet. -/
theorem connectorSheet_eq_localBoundaryRoot_zero
    (outerRun : ChapterVIDOuterArcPolarCompiledGrid.CompiledRunVerdict)
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDAnchoredConnectorModel massProduct b d)
    (bulkRun : ChapterVIDConnectorFactorBulkReference.ReferenceCompiledRunVerdict)
    (derivativeRun :
      ChapterVIDConnectorFactorDerivativeReference.ReferenceCompiledRunVerdict)
    (curvatureRun :
      ChapterVIDConnectorFactorSecondDerivativeReference.ReferenceCompiledRunVerdict)
    (side : ChapterVIDOuterArcSide)
    (crossing : PositiveCrossingCertificate
      model.toChapterVIDPrincipalConnectorModel side)
    (certificate : ChapterVIDConnectorCompiledCertificate
      model.toChapterVIDPrincipalConnectorModel side)
    (sheet : ChapterVIContinuousSquareRootSheet
      (model.toChapterVIDPrincipalConnectorModel.rectangleRadicand side))
    (houter : ∀ s : I,
      sheet.root (model.connectorBoundaryPoint side s) =
        model.connectorOuterBoundaryRoot outerRun side s) :
    sheet.root (model.connectorLocalBoundaryPoint side 0) =
      model.connectorLocalBoundaryRoot 0 := by
  let restricted : ChapterVIContinuousSquareRootSheet
      (fun t : I ↦ model.rectangleRadicand side
        (connectorPathPoint model.toChapterVIDPrincipalConnectorModel t)) := {
    root := fun t ↦ sheet.root
      (connectorPathPoint model.toChapterVIDPrincipalConnectorModel t)
    continuous_root := sheet.continuous_root.comp
      (continuous_const.prodMk continuous_id)
    root_sq := fun t ↦ sheet.root_sq _ }
  have hbase : restricted.root (outerParameter side) =
      (factorPathSheet model bulkRun derivativeRun curvatureRun side crossing).root
        (outerParameter side) := by
    rw [show restricted.root (outerParameter side) =
        sheet.root (model.connectorBoundaryPoint side 0) by simp [restricted]]
    rw [houter 0,
      factorPathSheet_outer model bulkRun derivativeRun curvatureRun side crossing certificate]
    change Complex.sqrt
        (chapterVIDOuterArcRadicand side (model.connectorOuterBoundaryPoint side 0)) =
      Complex.sqrt
        (model.rectangleRadicand side
          (connectorPathPoint model.toChapterVIDPrincipalConnectorModel (outerParameter side)))
    rw [← model.rectangleRadicand_connectorBoundaryPoint side 0]
    simp
  have hall := restricted.root_eq_of_eq_at
    (factorPathSheet model bulkRun derivativeRun curvatureRun side crossing)
    (fun t ↦ by
      have hne := factors_ne_zero certificate t
      exact mul_ne_zero hne.1 hne.2)
    (outerParameter side) hbase
  calc
    sheet.root (model.connectorLocalBoundaryPoint side 0) =
        restricted.root (localParameter side) := by simp [restricted]
    _ = (factorPathSheet model bulkRun derivativeRun curvatureRun side crossing).root
        (localParameter side) := congrFun hall (localParameter side)
    _ = model.connectorLocalBoundaryRoot 0 :=
      factorPathSheet_local model bulkRun derivativeRun curvatureRun side crossing certificate

/-- Both scale-aware crossing verdicts complete the seam-compatible connector pair. -/
theorem exists_seamCompatiblePair
    (outerRun : ChapterVIDOuterArcPolarCompiledGrid.CompiledRunVerdict)
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDAnchoredConnectorModel massProduct b d)
    (bulkRun : ChapterVIDConnectorFactorBulkReference.ReferenceCompiledRunVerdict)
    (derivativeRun :
      ChapterVIDConnectorFactorDerivativeReference.ReferenceCompiledRunVerdict)
    (curvatureRun :
      ChapterVIDConnectorFactorSecondDerivativeReference.ReferenceCompiledRunVerdict)
    (initialCrossing : PositiveCrossingCertificate
      model.toChapterVIDPrincipalConnectorModel .initial)
    (finalCrossing : PositiveCrossingCertificate
      model.toChapterVIDPrincipalConnectorModel .final)
    (initialCertificate : ChapterVIDConnectorCompiledCertificate
      model.toChapterVIDPrincipalConnectorModel .initial)
    (finalCertificate : ChapterVIDConnectorCompiledCertificate
      model.toChapterVIDPrincipalConnectorModel .final) :
    Nonempty (ChapterVIDPrincipalConnectorModel.SeamCompatibleCertifiedConnectorPair
      outerRun model.toChapterVIDPrincipalConnectorModel) := by
  obtain ⟨pair⟩ := ChapterVIDPrincipalConnectorModel.exists_certifiedConnectorPair
    outerRun model.toChapterVIDPrincipalConnectorModel initialCertificate finalCertificate
  exact ⟨{
    pair := pair
    initial_local_at_zero := connectorSheet_eq_localBoundaryRoot_zero outerRun model bulkRun
      derivativeRun curvatureRun .initial initialCrossing initialCertificate
      pair.initialSheet pair.initial_outer
    final_local_at_zero := connectorSheet_eq_localBoundaryRoot_zero outerRun model bulkRun
      derivativeRun curvatureRun .final finalCrossing finalCertificate
      pair.finalSheet pair.final_outer }⟩

/-- End-to-end seam theorem, conditional only on the two scale-aware compiled crossing
verdicts. -/
theorem exists_seamCompatibleContribution_tendsto
    (outerRun : ChapterVIDOuterArcPolarCompiledGrid.CompiledRunVerdict)
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDAnchoredConnectorModel massProduct b d)
    (bulkRun : ChapterVIDConnectorFactorBulkReference.ReferenceCompiledRunVerdict)
    (derivativeRun :
      ChapterVIDConnectorFactorDerivativeReference.ReferenceCompiledRunVerdict)
    (curvatureRun :
      ChapterVIDConnectorFactorSecondDerivativeReference.ReferenceCompiledRunVerdict)
    (initialCrossing : PositiveCrossingCertificate
      model.toChapterVIDPrincipalConnectorModel .initial)
    (finalCrossing : PositiveCrossingCertificate
      model.toChapterVIDPrincipalConnectorModel .final)
    (initialCertificate : ChapterVIDConnectorCompiledCertificate
      model.toChapterVIDPrincipalConnectorModel .initial)
    (finalCertificate : ChapterVIDConnectorCompiledCertificate
      model.toChapterVIDPrincipalConnectorModel .final) :
    ∃ compatible : ChapterVIDPrincipalConnectorModel.SeamCompatibleCertifiedConnectorPair
        outerRun model.toChapterVIDPrincipalConnectorModel,
      Filter.Tendsto
        (fun k : ℝ ↦ (-Real.log k)⁻¹ • compatible.fivePieceContribution k)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds ((2 * Real.pi * Complex.I : ℂ)⁻¹ *
          chapterVIDPrincipalMorseAmplitude massProduct b d (0, 0))) := by
  obtain ⟨compatible⟩ := exists_seamCompatiblePair outerRun model bulkRun derivativeRun
    curvatureRun initialCrossing finalCrossing initialCertificate finalCertificate
  exact ⟨compatible, compatible.tendsto_fivePiece_inv_neg_log_smul⟩

/-- Fully compiled-facing form of the seam theorem.  The two crossing predicates are recovered
from the exact zero-returning LeanCompCert artifacts before the analytic assembly is invoked. -/
theorem exists_seamCompatibleContribution_tendsto_of_compiledCrossingRuns
    (outerRun : ChapterVIDOuterArcPolarCompiledGrid.CompiledRunVerdict)
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDAnchoredConnectorModel massProduct b d)
    (bulkRun : ChapterVIDConnectorFactorBulkReference.ReferenceCompiledRunVerdict)
    (derivativeRun :
      ChapterVIDConnectorFactorDerivativeReference.ReferenceCompiledRunVerdict)
    (curvatureRun :
      ChapterVIDConnectorFactorSecondDerivativeReference.ReferenceCompiledRunVerdict)
    {initialPrecision finalPrecision : ℕ}
    {initialName finalName : String}
    {initialData : CompiledCrossingData
      model.toChapterVIDPrincipalConnectorModel .initial initialPrecision}
    {finalData : CompiledCrossingData
      model.toChapterVIDPrincipalConnectorModel .final finalPrecision}
    (initialRun : CompiledCrossingRunVerdict initialName initialData)
    (finalRun : CompiledCrossingRunVerdict finalName finalData)
    (initialCertificate : ChapterVIDConnectorCompiledCertificate
      model.toChapterVIDPrincipalConnectorModel .initial)
    (finalCertificate : ChapterVIDConnectorCompiledCertificate
      model.toChapterVIDPrincipalConnectorModel .final) :
    ∃ compatible : ChapterVIDPrincipalConnectorModel.SeamCompatibleCertifiedConnectorPair
        outerRun model.toChapterVIDPrincipalConnectorModel,
      Filter.Tendsto
        (fun k : ℝ ↦ (-Real.log k)⁻¹ • compatible.fivePieceContribution k)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds ((2 * Real.pi * Complex.I : ℂ)⁻¹ *
          chapterVIDPrincipalMorseAmplitude massProduct b d (0, 0))) :=
  exists_seamCompatibleContribution_tendsto outerRun model bulkRun derivativeRun curvatureRun
    initialRun.toPositiveCrossingCertificate finalRun.toPositiveCrossingCertificate
    initialCertificate finalCertificate

end ChapterVIDConnectorFactorCrossing
end PoincareChapterVI
