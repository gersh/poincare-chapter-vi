/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.ChapterVISquareRootSheet
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Algebra.Module.LocallyConvex

/-!
# Certificate-backed regular connector arcs

This file isolates the reusable analytic part of the two connector calculation. A connector is
an affine segment between two continuously moving endpoints. A finite nonvanishing certificate
on its parameter rectangle constructs a compatible square-root sheet. The resulting curve
integral is continuous through the collision parameter and hence has an ordinary finite limit.

The concrete Chapter VI work is therefore reduced to supplying the literal numerator and
radicand on each of the two connector rectangles and checking the finite certificates.
-/

noncomputable section

open Filter Topology
open scoped unitInterval

namespace PoincareChapterVI

/-- Continuous extension of a unit-interval coordinate to all real integration parameters. -/
def chapterVIConnectorClamp (t : ℝ) : I :=
  Set.projIcc 0 1 zero_le_one t

theorem continuous_chapterVIConnectorClamp :
    Continuous chapterVIConnectorClamp :=
  continuous_projIcc (h := zero_le_one)

theorem chapterVIConnectorClamp_of_mem {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    chapterVIConnectorClamp t = ⟨t, ht⟩ := by
  exact Set.projIcc_of_mem zero_le_one ht

/-- The straight connector between two parameter-dependent source points. -/
def chapterVIAffineConnectorPoint
    (source target : I → ℂ) (point : I × ℝ) : ℂ :=
  AffineMap.lineMap (source point.1) (target point.1) point.2

theorem continuous_chapterVIAffineConnectorPoint
    {source target : I → ℂ} (hsource : Continuous source)
    (htarget : Continuous target) :
    Continuous (chapterVIAffineConnectorPoint source target) := by
  unfold chapterVIAffineConnectorPoint
  simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
  fun_prop

/-- Constant velocity of an affine connector at a fixed collision parameter. -/
def chapterVIAffineConnectorVelocity
    (source target : I → ℂ) (s : I) : ℂ :=
  target s - source s

theorem continuous_chapterVIAffineConnectorVelocity
    {source target : I → ℂ} (hsource : Continuous source)
    (htarget : Continuous target) :
    Continuous (chapterVIAffineConnectorVelocity source target) := by
  exact htarget.sub hsource

theorem hasDerivAt_chapterVIAffineConnectorPoint
    (source target : I → ℂ) (s : I) (t : ℝ) :
    HasDerivAt (fun τ ↦ chapterVIAffineConnectorPoint source target (s, τ))
      (chapterVIAffineConnectorVelocity source target s) t := by
  unfold chapterVIAffineConnectorPoint chapterVIAffineConnectorVelocity
  simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
  simpa +instances using!
    ((hasDerivAt_id t).smul_const (target s - source s)).const_add (source s)

/-- Extend a square-root sheet on the compact connector rectangle to a real integration
parameter by clamping to `[0,1]`. -/
def chapterVIConnectorSheetRoot
    {radicand : I × I → ℂ}
    (sheet : ChapterVIContinuousSquareRootSheet radicand)
    (point : I × ℝ) : ℂ :=
  sheet.root (point.1, chapterVIConnectorClamp point.2)

theorem continuous_chapterVIConnectorSheetRoot
    {radicand : I × I → ℂ}
    (sheet : ChapterVIContinuousSquareRootSheet radicand) :
    Continuous (chapterVIConnectorSheetRoot sheet) :=
  sheet.continuous_root.comp
    (continuous_fst.prodMk
      (continuous_chapterVIConnectorClamp.comp continuous_snd))

theorem chapterVIConnectorSheetRoot_ne_zero
    {radicand : I × I → ℂ}
    (certificate : ChapterVIFiniteNonvanishingCover radicand)
    (sheet : ChapterVIContinuousSquareRootSheet radicand)
    (point : I × ℝ) :
    chapterVIConnectorSheetRoot sheet point ≠ 0 :=
  sheet.root_ne_zero (certificate.ne_zero _)

/-- The normalized integral on one affine connector. The numerator is already expressed along
the connector; its concrete source identity belongs in the Chapter VI specialization. -/
def chapterVIConnectorIntegral
    (numerator : I × ℝ → ℂ) {radicand : I × I → ℂ}
    (sheet : ChapterVIContinuousSquareRootSheet radicand)
    (source target : I → ℂ) (s : I) : ℂ :=
  (2 * Real.pi * Complex.I : ℂ)⁻¹ *
    ∫ t in (0 : ℝ)..1,
      numerator (s, t) / chapterVIConnectorSheetRoot sheet (s, t) *
        chapterVIAffineConnectorVelocity source target s

/-- Any fixed compatible connector sheet gives a continuous connector integral once the
numerator and moving endpoints are continuous and the radicand is nonzero. -/
theorem continuous_chapterVIConnectorIntegral
    (numerator : I × ℝ → ℂ) {radicand : I × I → ℂ}
    (sheet : ChapterVIContinuousSquareRootSheet radicand)
    (source target : I → ℂ)
    (hnumerator : Continuous numerator)
    (hsource : Continuous source) (htarget : Continuous target)
    (hrad : ∀ point, radicand point ≠ 0) :
    Continuous (chapterVIConnectorIntegral numerator sheet source target) := by
  unfold chapterVIConnectorIntegral
  apply continuous_const.mul
  apply continuous_chapterVIParametricOuterArcIntegral
      (fun s t ↦ numerator (s, t))
      (fun s t ↦ chapterVIConnectorSheetRoot sheet (s, t))
      (fun s _ ↦ chapterVIAffineConnectorVelocity source target s)
  · exact hnumerator
  · exact continuous_chapterVIConnectorSheetRoot sheet
  · exact (continuous_chapterVIAffineConnectorVelocity hsource htarget).comp
      continuous_fst
  · exact fun s t ↦ sheet.root_ne_zero (hrad _)

/-- Pointwise endpoint-limit form of `continuous_chapterVIConnectorIntegral`. -/
theorem tendsto_chapterVIConnectorIntegral
    (numerator : I × ℝ → ℂ) {radicand : I × I → ℂ}
    (sheet : ChapterVIContinuousSquareRootSheet radicand)
    (source target : I → ℂ)
    (hnumerator : Continuous numerator)
    (hsource : Continuous source) (htarget : Continuous target)
    (hrad : ∀ point, radicand point ≠ 0) :
    Tendsto (chapterVIConnectorIntegral numerator sheet source target)
      (𝓝 (1 : I))
      (𝓝 (chapterVIConnectorIntegral numerator sheet source target 1)) :=
  (continuous_chapterVIConnectorIntegral numerator sheet source target
    hnumerator hsource htarget hrad).continuousAt

/-- Pointwise nonvanishing supplies a square-root sheet for an affine connector and makes its
normalized integral continuous on the whole collision-parameter interval. This is the semantic
interface used by both point-sample covers and compiled interval-cell grids. -/
theorem exists_sheet_continuous_chapterVIConnectorIntegral_of_ne_zero
    {radicand : I × I → ℂ} (hradicand : Continuous radicand)
    (hrad : ∀ point, radicand point ≠ 0)
    (numerator : I × ℝ → ℂ) (hnumerator : Continuous numerator)
    (source target : I → ℂ) (hsource : Continuous source)
    (htarget : Continuous target) :
    ∃ sheet : ChapterVIContinuousSquareRootSheet radicand,
      Continuous (chapterVIConnectorIntegral numerator sheet source target) := by
  let : ContractibleSpace I :=
    (convex_Icc (0 : ℝ) 1).contractibleSpace (by simp)
  let : LocallyPathConnectedSpace I :=
    (convex_Icc (0 : ℝ) 1).locallyPathConnectedSpace
  let : LocallyPathConnectedSpace (I × I) := by
    refine LocallyPathConnectedSpace.of_bases
      (p := fun (point : I × I) (sets : Set I × Set I) ↦
        (sets.1 ∈ 𝓝 point.1 ∧ IsPathConnected sets.1) ∧
          (sets.2 ∈ 𝓝 point.2 ∧ IsPathConnected sets.2))
      (s := fun _ sets ↦ sets.1 ×ˢ sets.2) ?_ ?_
    · intro point
      rw [nhds_prod_eq]
      exact (path_connected_basis point.1).prod (path_connected_basis point.2)
    · intro _ sets hsets
      exact hsets.1.2.prod hsets.2.2
  let base : I × I := (0, 0)
  obtain ⟨baseRoot, hbaseRoot⟩ :=
    IsAlgClosed.exists_pow_nat_eq (radicand base) (by norm_num : 0 < (2 : ℕ))
  obtain ⟨sheet, _⟩ := exists_chapterVIContinuousSquareRootSheet
    radicand hradicand hrad base baseRoot hbaseRoot
  refine ⟨sheet, ?_⟩
  unfold chapterVIConnectorIntegral
  apply continuous_const.mul
  apply continuous_chapterVIParametricOuterArcIntegral
      (fun s t ↦ numerator (s, t))
      (fun s t ↦ chapterVIConnectorSheetRoot sheet (s, t))
      (fun s _ ↦ chapterVIAffineConnectorVelocity source target s)
  · exact hnumerator
  · exact continuous_chapterVIConnectorSheetRoot sheet
  · exact (continuous_chapterVIAffineConnectorVelocity hsource htarget).comp
      continuous_fst
  · exact fun _ _ ↦ sheet.root_ne_zero (hrad _)

/-- A finite point-sample cover is one source of the pointwise nonvanishing input. -/
theorem exists_sheet_continuous_chapterVIConnectorIntegral
    {radicand : I × I → ℂ} (hradicand : Continuous radicand)
    (certificate : ChapterVIFiniteNonvanishingCover radicand)
    (numerator : I × ℝ → ℂ) (hnumerator : Continuous numerator)
    (source target : I → ℂ) (hsource : Continuous source)
    (htarget : Continuous target) :
    ∃ sheet : ChapterVIContinuousSquareRootSheet radicand,
      Continuous (chapterVIConnectorIntegral numerator sheet source target) :=
  exists_sheet_continuous_chapterVIConnectorIntegral_of_ne_zero hradicand
    certificate.ne_zero numerator hnumerator source target hsource htarget

/-- Pointwise-nonvanishing form of the finite connector endpoint theorem. -/
theorem exists_sheet_tendsto_chapterVIConnectorIntegral_of_ne_zero
    {radicand : I × I → ℂ} (hradicand : Continuous radicand)
    (hrad : ∀ point, radicand point ≠ 0)
    (numerator : I × ℝ → ℂ) (hnumerator : Continuous numerator)
    (source target : I → ℂ) (hsource : Continuous source)
    (htarget : Continuous target) :
    ∃ sheet : ChapterVIContinuousSquareRootSheet radicand,
      Tendsto (chapterVIConnectorIntegral numerator sheet source target)
        (nhds (1 : I))
        (nhds (chapterVIConnectorIntegral numerator sheet source target 1)) := by
  obtain ⟨sheet, hcontinuous⟩ :=
    exists_sheet_continuous_chapterVIConnectorIntegral_of_ne_zero hradicand hrad
      numerator hnumerator source target hsource htarget
  exact ⟨sheet, hcontinuous.continuousAt⟩

/-- In particular, every certificate-backed connector contribution has a finite endpoint limit
at the collision parameter. -/
theorem exists_sheet_tendsto_chapterVIConnectorIntegral
    {radicand : I × I → ℂ} (hradicand : Continuous radicand)
    (certificate : ChapterVIFiniteNonvanishingCover radicand)
    (numerator : I × ℝ → ℂ) (hnumerator : Continuous numerator)
    (source target : I → ℂ) (hsource : Continuous source)
    (htarget : Continuous target) :
    ∃ sheet : ChapterVIContinuousSquareRootSheet radicand,
      Tendsto (chapterVIConnectorIntegral numerator sheet source target)
        (nhds (1 : I))
        (nhds (chapterVIConnectorIntegral numerator sheet source target 1)) := by
  exact exists_sheet_tendsto_chapterVIConnectorIntegral_of_ne_zero hradicand
    certificate.ne_zero numerator hnumerator source target hsource htarget

end PoincareChapterVI
