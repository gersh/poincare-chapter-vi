/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.ChapterVIDRadialTailBaseConstants
import PoincareChapterVI.ChapterVILeanCompCertAffineTrace

/-! # Checked derived constants for the radial-tail affine table -/

namespace PoincareChapterVI

open ChapterVILeanCompCertBatch

namespace ChapterVIDRadialTailBaseConstantTrace

open ChapterVIDRadialTailBaseConstants
open ChapterVILeanCompCertAffineTrace

abbrev Model := ChapterVILeanCompCertAffineTrace.Model 40
abbrev Rectangle := ChapterVISignedDyadicComplexRectangle 40

def zeroRectangle : Rectangle :=
  ChapterVISignedDyadicComplexRectangle.pointInt 40 0

def realRectangle (x : Interval) : Rectangle := ⟨x, zeroInterval⟩

def constant (x : Rectangle) : Model :=
  { center := x, radial := zeroRectangle, angular := zeroRectangle, error := zeroRectangle }

def qDModel : Model := constant (realRectangle qD)
def qdot : Model := qDModel.add (ChapterVILeanCompCertAffineTrace.integer 40 (-1))

def collisionModel : Model := constant collision
def collisionInvTrace := ChapterVILeanCompCertAffineTrace.proposeInv collisionModel
def collisionInv : Model := collisionInvTrace.output
def collisionSqTrace := ChapterVILeanCompCertAffineTrace.proposeMul collisionModel collisionModel
def collisionSq : Model := collisionSqTrace.output
def collisionInvSqTrace := ChapterVILeanCompCertAffineTrace.proposeMul collisionInv collisionInv
def collisionInvSq : Model := collisionInvSqTrace.output
def collisionInvCubeTrace := ChapterVILeanCompCertAffineTrace.proposeMul collisionInvSq collisionInv
def collisionInvCube : Model := collisionInvCubeTrace.output
def collisionInvFourthTrace := ChapterVILeanCompCertAffineTrace.proposeMul
  collisionInvCube collisionInv
def collisionInvFourth : Model := collisionInvFourthTrace.output

def qDCubeRoot : Interval := ⟨105102773799, 105102773842⟩
def qDSixthRoot : Interval := ⟨339943704024, 339943704088⟩

def qDCubeRootTrace := ChapterVILeanCompCertProposals.cubicRootTrace qD qDCubeRoot
def qDSixthRootTrace := ChapterVILeanCompCertProposals.sixthRootTrace qD qDSixthRoot

def zetaBase : Model := constant (realRectangle qDCubeRoot)
def pBase : Model := constant (realRectangle qDSixthRoot)
def pBaseInvTrace := ChapterVILeanCompCertAffineTrace.proposeInv pBase
def pBaseInv : Model := pBaseInvTrace.output
def correctionTrace := ChapterVILeanCompCertAffineTrace.proposeMul collisionModel.neg pBaseInv
def correction : Model := correctionTrace.output
def cdot : Model := correction.add (ChapterVILeanCompCertAffineTrace.integer 40 (-1))

def yBase : Model := constant ChapterVIDRadialTailBaseConstants.yBase

def operations : List (DyadicOperation 40) :=
  collisionInvTrace.operations ++ collisionSqTrace.operations ++
    collisionInvSqTrace.operations ++ collisionInvCubeTrace.operations ++
    collisionInvFourthTrace.operations ++ qDCubeRootTrace.operations ++
    qDSixthRootTrace.operations ++ pBaseInvTrace.operations ++ correctionTrace.operations

/-! ## Kernel-checked semantics of the derived constants -/

set_option maxRecDepth 100000

theorem operations_allSound : ∀ operation ∈ operations, operation.Sound := by
  have h1 := proposeInv_operations_sound collisionModel (by decide +kernel) (by decide +kernel)
  have h2 := proposeMul_operations_sound collisionModel collisionModel
  have h3 := proposeMul_operations_sound collisionInv collisionInv
  have h4 := proposeMul_operations_sound collisionInvSq collisionInv
  have h5 := proposeMul_operations_sound collisionInvCube collisionInv
  have h6 := ChapterVILeanCompCertProposals.cubicRootTrace_operations_sound qD qDCubeRoot
  have h7 := ChapterVILeanCompCertProposals.sixthRootTrace_operations_sound qD qDSixthRoot
  have h8 := proposeInv_operations_sound pBase (by decide +kernel) (by decide +kernel)
  have h9 := proposeMul_operations_sound collisionModel.neg pBaseInv
  intro operation hoperation
  change operation ∈ collisionInvTrace.operations ++ collisionSqTrace.operations ++
    collisionInvSqTrace.operations ++ collisionInvCubeTrace.operations ++
    collisionInvFourthTrace.operations ++ qDCubeRootTrace.operations ++
    qDSixthRootTrace.operations ++ pBaseInvTrace.operations ++ correctionTrace.operations
      at hoperation
  rcases List.mem_append.mp hoperation with hoperation | h
  · rcases List.mem_append.mp hoperation with hoperation | h'
    · rcases List.mem_append.mp hoperation with hoperation | h''
      · rcases List.mem_append.mp hoperation with hoperation | h'''
        · rcases List.mem_append.mp hoperation with hoperation | h''''
          · rcases List.mem_append.mp hoperation with hoperation | h'''''
            · rcases List.mem_append.mp hoperation with hoperation | h''''''
              · rcases List.mem_append.mp hoperation with ha | hb
                · exact h1 operation ha
                · exact h2 operation hb
              · exact h3 operation h''''''
            · exact h4 operation h'''''
          · exact h5 operation h''''
        · exact h6 operation h'''
      · exact h7 operation h''
    · exact h8 operation h'
  · exact h9 operation h

theorem qDCubeRootTrace_valid : qDCubeRootTrace.Valid := by
  unfold qDCubeRootTrace qDCubeRoot qD
    ChapterVILeanCompCertProposals.cubicRootTrace
    ChapterVILeanCompCertRoots.CubicRootTrace.Valid
  decide +kernel

theorem qDSixthRootTrace_valid : qDSixthRootTrace.Valid := by
  unfold qDSixthRootTrace qDSixthRoot qD
    ChapterVILeanCompCertProposals.sixthRootTrace
    ChapterVILeanCompCertRoots.SixthRootTrace.Valid
  decide +kernel

private theorem zeroRectangle_contains : zeroRectangle.Contains 0 := by
  simpa [zeroRectangle] using
    ChapterVISignedDyadicComplexRectangle.pointInt_contains 40 0

theorem constant_contains {rectangle : Rectangle} {value : ℂ}
    (hvalue : rectangle.Contains value) (radialParameter angularParameter : ℝ) :
    (constant rectangle).Contains radialParameter angularParameter value := by
  refine ⟨value, 0, 0, 0, hvalue, ?_, ?_, ?_, by ring⟩
  all_goals exact zeroRectangle_contains

theorem qDModel_contains (radialParameter angularParameter : ℝ) :
    qDModel.Contains radialParameter angularParameter
      (chapterVIDCriticalParameterModulus : ℂ) :=
  constant_contains (by
    constructor
    · change qD.Contains chapterVIDCriticalParameterModulus
      exact ChapterVIDRadialTailBaseConstants.qD_contains
    · change zeroInterval.Contains 0
      simpa [ChapterVIDRadialTailBaseConstants.zeroInterval] using
        ChapterVISignedDyadicInterval.pointInt_contains 40 0) _ _

theorem qdot_contains (radialParameter angularParameter : ℝ) :
    qdot.Contains radialParameter angularParameter
      ((chapterVIDCriticalParameterModulus - 1 : ℝ) : ℂ) := by
  simpa [qdot, sub_eq_add_neg] using
    Model.add_contains (qDModel_contains radialParameter angularParameter)
      (integer_contains 40 (-1) radialParameter angularParameter)

theorem collisionModel_contains (radialParameter angularParameter : ℝ) :
    collisionModel.Contains radialParameter angularParameter chapterVIDCollisionLift :=
  constant_contains ChapterVIDRadialTailBaseConstants.collision_contains _ _

theorem yBase_contains (radialParameter angularParameter : ℝ) :
    yBase.Contains radialParameter angularParameter chapterVIDY :=
  constant_contains ChapterVIDRadialTailBaseConstants.yBase_contains _ _

private theorem operations_sound_of_mem {operation : DyadicOperation 40}
    (hoperation : operation ∈ operations) : operation.Sound :=
  operations_allSound operation hoperation

theorem collisionInv_contains (radialParameter angularParameter : ℝ)
    (hradial : |radialParameter| ≤ 1) (hangular : |angularParameter| ≤ 1) :
    collisionInv.Contains radialParameter angularParameter chapterVIDCollisionLift⁻¹ := by
  apply proposeInv_output_contains hradial hangular
  · intro operation hoperation
    apply operations_sound_of_mem
    simp [operations, collisionInvTrace, hoperation]
  · exact collisionModel_contains _ _

theorem collisionSq_contains (radialParameter angularParameter : ℝ)
    (hradial : |radialParameter| ≤ 1) (hangular : |angularParameter| ≤ 1) :
    collisionSq.Contains radialParameter angularParameter (chapterVIDCollisionLift ^ 2) := by
  change (proposeMul collisionModel collisionModel).output.Contains
    radialParameter angularParameter (chapterVIDCollisionLift ^ 2)
  simpa [pow_two] using proposeMul_output_contains hradial hangular
    (x := collisionModel) (y := collisionModel)
    (by
      intro operation hoperation
      apply operations_sound_of_mem
      simp [operations, collisionSqTrace, hoperation])
    (collisionModel_contains _ _) (collisionModel_contains _ _)

theorem collisionInvSq_contains (radialParameter angularParameter : ℝ)
    (hradial : |radialParameter| ≤ 1) (hangular : |angularParameter| ≤ 1) :
    collisionInvSq.Contains radialParameter angularParameter
      (chapterVIDCollisionLift⁻¹ ^ 2) := by
  change (proposeMul collisionInv collisionInv).output.Contains
    radialParameter angularParameter (chapterVIDCollisionLift⁻¹ ^ 2)
  simpa [pow_two] using proposeMul_output_contains hradial hangular
    (x := collisionInv) (y := collisionInv)
    (by
      intro operation hoperation
      apply operations_sound_of_mem
      simp [operations, collisionInvSqTrace, hoperation])
    (collisionInv_contains _ _ hradial hangular)
    (collisionInv_contains _ _ hradial hangular)

theorem collisionInvCube_contains (radialParameter angularParameter : ℝ)
    (hradial : |radialParameter| ≤ 1) (hangular : |angularParameter| ≤ 1) :
    collisionInvCube.Contains radialParameter angularParameter
      (chapterVIDCollisionLift⁻¹ ^ 3) := by
  change (proposeMul collisionInvSq collisionInv).output.Contains
    radialParameter angularParameter (chapterVIDCollisionLift⁻¹ ^ 3)
  have h := proposeMul_output_contains hradial hangular
    (x := collisionInvSq) (y := collisionInv)
    (by
      intro operation hoperation
      apply operations_sound_of_mem
      simp [operations, collisionInvCubeTrace, hoperation])
    (collisionInvSq_contains _ _ hradial hangular)
    (collisionInv_contains _ _ hradial hangular)
  simpa [pow_succ] using h

theorem collisionInvFourth_contains (radialParameter angularParameter : ℝ)
    (hradial : |radialParameter| ≤ 1) (hangular : |angularParameter| ≤ 1) :
    collisionInvFourth.Contains radialParameter angularParameter
      (chapterVIDCollisionLift⁻¹ ^ 4) := by
  change (proposeMul collisionInvCube collisionInv).output.Contains
    radialParameter angularParameter (chapterVIDCollisionLift⁻¹ ^ 4)
  have h := proposeMul_output_contains hradial hangular
    (x := collisionInvCube) (y := collisionInv)
    (by
      intro operation hoperation
      apply operations_sound_of_mem
      simp [operations, collisionInvFourthTrace, hoperation])
    (collisionInvCube_contains _ _ hradial hangular)
    (collisionInv_contains _ _ hradial hangular)
  simpa [pow_succ] using h

theorem zetaBase_contains (radialParameter angularParameter : ℝ) :
    zetaBase.Contains radialParameter angularParameter
      ((chapterVIDCriticalParameterModulus ^ ((3 : ℝ)⁻¹) : ℝ) : ℂ) := by
  apply constant_contains
  constructor
  · apply qDCubeRootTrace.output_contains_of_valid qDCubeRootTrace_valid
    · intro operation hoperation
      apply operations_sound_of_mem
      simp [operations, hoperation]
    · exact chapterVIDCriticalParameterModulus_pos.le
    · exact ChapterVIDRadialTailBaseConstants.qD_contains
  · change zeroInterval.Contains 0
    simpa [ChapterVIDRadialTailBaseConstants.zeroInterval] using
      ChapterVISignedDyadicInterval.pointInt_contains 40 0

theorem pBase_contains (radialParameter angularParameter : ℝ) :
    pBase.Contains radialParameter angularParameter
      ((chapterVIDCriticalParameterSixthRoot : ℝ) : ℂ) := by
  apply constant_contains
  constructor
  · change qDSixthRoot.Contains
      (chapterVIDCriticalParameterModulus ^ ((6 : ℝ)⁻¹))
    apply qDSixthRootTrace.output_contains_of_valid qDSixthRootTrace_valid
    · intro operation hoperation
      apply operations_sound_of_mem
      simp [operations, hoperation]
    · exact chapterVIDCriticalParameterModulus_pos.le
    · exact ChapterVIDRadialTailBaseConstants.qD_contains
  · change zeroInterval.Contains 0
    simpa [ChapterVIDRadialTailBaseConstants.zeroInterval] using
      ChapterVISignedDyadicInterval.pointInt_contains 40 0

theorem pBaseInv_contains (radialParameter angularParameter : ℝ)
    (hradial : |radialParameter| ≤ 1) (hangular : |angularParameter| ≤ 1) :
    pBaseInv.Contains radialParameter angularParameter
      ((chapterVIDCriticalParameterSixthRoot⁻¹ : ℝ) : ℂ) := by
  change (proposeInv pBase).output.Contains radialParameter angularParameter
    ((chapterVIDCriticalParameterSixthRoot⁻¹ : ℝ) : ℂ)
  simpa using proposeInv_output_contains hradial hangular
    (x := pBase)
    (by
      intro operation hoperation
      apply operations_sound_of_mem
      simp [operations, pBaseInvTrace, hoperation])
    (pBase_contains _ _)

theorem correction_contains (radialParameter angularParameter : ℝ)
    (hradial : |radialParameter| ≤ 1) (hangular : |angularParameter| ≤ 1) :
    correction.Contains radialParameter angularParameter
      ((chapterVIDCertificateContourCorrection : ℝ) : ℂ) := by
  change (proposeMul collisionModel.neg pBaseInv).output.Contains
    radialParameter angularParameter
      ((chapterVIDCertificateContourCorrection : ℝ) : ℂ)
  have hneg := Model.neg_contains (collisionModel_contains radialParameter angularParameter)
  have hmul := proposeMul_output_contains hradial hangular
    (x := collisionModel.neg) (y := pBaseInv)
    (by
      intro operation hoperation
      apply operations_sound_of_mem
      simp [operations, correctionTrace, hoperation]) hneg
    (pBaseInv_contains _ _ hradial hangular)
  rw [chapterVIDCertificateContourCorrection, div_eq_mul_inv]
  convert hmul using 1
  rw [chapterVIDCollisionLift_eq_neg_norm]
  simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]

theorem cdot_contains (radialParameter angularParameter : ℝ)
    (hradial : |radialParameter| ≤ 1) (hangular : |angularParameter| ≤ 1) :
    cdot.Contains radialParameter angularParameter
      ((chapterVIDCertificateContourCorrection - 1 : ℝ) : ℂ) := by
  simpa [cdot, sub_eq_add_neg] using Model.add_contains
    (correction_contains radialParameter angularParameter hradial hangular)
    (integer_contains 40 (-1) radialParameter angularParameter)

end ChapterVIDRadialTailBaseConstantTrace

end PoincareChapterVI
