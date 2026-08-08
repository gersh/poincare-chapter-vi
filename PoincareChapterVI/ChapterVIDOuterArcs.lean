/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.ChapterVIDCertificateContour
import PoincareChapterVI.ChapterVISquareRootSheet
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Algebra.Module.LocallyConvex

/-!
# Concrete outer arcs for the D pinch

This file fixes the two compact outer quarters of the certificate-friendly radial contour. The first uses
angular time `[0,1/4]`; the second uses `[3/4,1]`.  The collision occurs at time `1/2`, so both
rectangles remain uniformly separated from the local middle arc.

The literal transformed radicand on each rectangle is defined and proved continuous.  The only
remaining datum needed to construct its compatible square-root sheet is an instance of
`ChapterVIDOuterArcNonvanishingCertificate`: this is now the exact concrete target for the
LeanCompCert finite sample computation and the accompanying analytic Lipschitz bound.
-/

noncomputable section

open Complex Real Filter Set
open scoped Topology unitInterval

namespace PoincareChapterVI

/-- The two regular pieces complementary to the middle half of the pinched circle. -/
inductive ChapterVIDOuterArcSide
  | initial
  | final
  deriving DecidableEq

/-- Reparameterization of the unit interval onto `[0,1/4]` or `[3/4,1]`. -/
noncomputable def chapterVIDOuterArcTime
    (side : ChapterVIDOuterArcSide) (t : I) : I :=
  match side with
  | .initial =>
      ⟨(t : ℝ) / 4, by
        constructor <;> nlinarith [t.property.1, t.property.2]⟩
  | .final =>
      ⟨3 / 4 + (t : ℝ) / 4, by
        constructor <;> nlinarith [t.property.1, t.property.2]⟩

theorem continuous_chapterVIDOuterArcTime
    (side : ChapterVIDOuterArcSide) :
    Continuous (chapterVIDOuterArcTime side) := by
  cases side <;> unfold chapterVIDOuterArcTime <;> fun_prop

/-- A point on one of the two outer-arc parameter rectangles.  The first coordinate is the
radial continuation time and the second is the local arc parameter. -/
noncomputable def chapterVIDOuterArcPoint
  (side : ChapterVIDOuterArcSide) (st : I × I) : ℂ :=
  chapterVIDCertificateContourHomotopy (st.1, chapterVIDOuterArcTime side st.2)

theorem continuous_chapterVIDOuterArcPoint
    (side : ChapterVIDOuterArcSide) :
    Continuous (chapterVIDOuterArcPoint side) := by
  exact chapterVIDCertificateContourHomotopy.continuous.comp
    (continuous_fst.prodMk
      ((continuous_chapterVIDOuterArcTime side).comp continuous_snd))

theorem chapterVIDOuterArcPoint_ne_zero
    (side : ChapterVIDOuterArcSide) (st : I × I) :
    chapterVIDOuterArcPoint side st ≠ 0 := by
  intro hzero
  have hnorm := congrArg norm hzero
  rw [chapterVIDOuterArcPoint, chapterVIDCertificateContourHomotopy_norm] at hnorm
  norm_num at hnorm
  exact (chapterVIDCertificateContourRadius_pos st.1).ne' hnorm

theorem chapterVIDCommonParameterRootPath_ne_zero (s : I) :
    chapterVIDCommonParameterRootPath s ≠ 0 := by
  intro hzero
  have hpow := congrArg (fun z : ℂ ↦ z ^ 3) hzero
  rw [chapterVIDCommonParameterRootPath_pow, zero_pow (by norm_num)] at hpow
  have hpos := chapterVIDCurveThreeSmoothParameter_pos
    (chapterVIDInsideXPath_neg s)
  exact (ofReal_ne_zero.mpr hpos.ne') hpow

/-- Poincare's literal transformed source radicand on an explicit outer-arc rectangle. -/
noncomputable def chapterVIDOuterArcRadicand
    (side : ChapterVIDOuterArcSide) (st : I × I) : ℂ :=
  chapterVIDRootCoordinateRadicand
    (chapterVIDCommonParameterRootPath st.1) (chapterVIDOuterArcPoint side st)

theorem continuous_chapterVIDOuterArcRadicand
    (side : ChapterVIDOuterArcSide) :
    Continuous (chapterVIDOuterArcRadicand side) := by
  rw [continuous_iff_continuousAt]
  intro st
  have hpair : ContinuousAt
      (fun st : I × I ↦
        (chapterVIDCommonParameterRootPath st.1,
          chapterVIDOuterArcPoint side st)) st :=
    (chapterVIDCommonParameterRootPath.continuous.comp continuous_fst).continuousAt.prodMk
      (continuous_chapterVIDOuterArcPoint side).continuousAt
  change ContinuousAt
    ((fun p : ℂ × ℂ ↦ chapterVIDRootCoordinateRadicand p.1 p.2) ∘
      fun st : I × I ↦
        (chapterVIDCommonParameterRootPath st.1,
          chapterVIDOuterArcPoint side st)) st
  exact Filter.Tendsto.comp
    (continuousAt_chapterVIDRootCoordinateRadicand
      (chapterVIDCommonParameterRootPath_ne_zero st.1)
      (chapterVIDOuterArcPoint_ne_zero side st)) hpair

/-- The precise finite-certificate type for either concrete D outer arc. -/
abbrev ChapterVIDOuterArcNonvanishingCertificate
    (side : ChapterVIDOuterArcSide) :=
  ChapterVIFiniteNonvanishingCover (chapterVIDOuterArcRadicand side)

/-- Once the finite nonvanishing certificate is supplied, covering-space lifting constructs the
base-normalized square-root sheet on the entire concrete outer-arc rectangle. -/
theorem ChapterVIDOuterArcNonvanishingCertificate.exists_squareRootSheet
    {side : ChapterVIDOuterArcSide}
    (certificate : ChapterVIDOuterArcNonvanishingCertificate side)
    (base : I × I) (baseRoot : ℂ)
    (hbaseRoot : baseRoot ^ 2 = chapterVIDOuterArcRadicand side base) :
    ∃ sheet : ChapterVIContinuousSquareRootSheet
        (chapterVIDOuterArcRadicand side),
      sheet.root base = baseRoot := by
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
  exact certificate.exists_continuousSquareRootSheet
    (continuous_chapterVIDOuterArcRadicand side) base baseRoot hbaseRoot

end PoincareChapterVI
