/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import Mathlib.Analysis.Analytic.Basic
import PoincareChapterVI.ChapterVIWeierstrass

/-!
# From a convergent prepared series to the analytic germ in Chapter VI

The formal Weierstrass preparation theorem in `ChapterVIWeierstrass` produces an identity of
formal power series.  To use that identity in Poincare's contour argument one must additionally
show that the series involved converge to the actual functions.  This file isolates the analytic
identity step from that existence problem.

The main uniqueness lemma says that two functions represented at a point by the same convergent
formal multilinear series agree in a neighbourhood of the point.  The
`ChapterVIConvergentPreparedGerm` structure then records precisely the convergent realization of
Poincare's prepared factors.  Its factorization theorem is a conclusion, not a structure field.

A LeanCompCert computation can certify arbitrarily large finite coefficient comparisons used to
construct such a realization.  It cannot, by itself, turn agreement through one finite cutoff into
convergence or equality of analytic germs; those remain analytic proof obligations.
-/

noncomputable section

open Filter Topology

namespace PoincareChapterVI

/-- Two functions represented by the same convergent formal multilinear series at a point agree
on some neighbourhood of that point.  This is the analytic identity bridge needed after a
coefficient-level preparation argument. -/
theorem eventuallyEq_of_hasFPowerSeriesAt_same
    {𝕜 E F : Type*}
    [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f g : E → F} {series : FormalMultilinearSeries 𝕜 E F} {base : E}
    (hf : HasFPowerSeriesAt f series base)
    (hg : HasFPowerSeriesAt g series base) :
    f =ᶠ[𝓝 base] g := by
  rcases hf with ⟨rf, hf⟩
  rcases hg with ⟨rg, hg⟩
  let radius := min rf rg
  have hradius : 0 < radius := lt_min hf.r_pos hg.r_pos
  have hf' : HasFPowerSeriesOnBall f series base radius :=
    hf.mono hradius inf_le_left
  have hg' : HasFPowerSeriesOnBall g series base radius :=
    hg.mono hradius inf_le_right
  filter_upwards [Metric.eball_mem_nhds base hradius] with point hpoint
  exact hf'.unique hg' hpoint

/-- A convergent analytic realization of Poincare's completed-square normal form near a base
point.  The parameter is the first coordinate and the local integration variable is the second.

The fields `radicandSeries` and `preparedSeries` intentionally have the same value.  Establishing
those two convergence statements from the nested formal power series produced by
`exists_chapterVI_weierstrassNormalForm` is the remaining analytic Weierstrass-preparation
obligation. -/
structure ChapterVIConvergentPreparedGerm
    (radicand : ℂ × ℂ → ℂ) (base : ℂ × ℂ) where
  center : ℂ → ℂ
  kappa : ℂ → ℂ
  unit : ℂ × ℂ → ℂ
  centerSeries : FormalMultilinearSeries ℂ ℂ ℂ
  kappaSeries : FormalMultilinearSeries ℂ ℂ ℂ
  unitSeries : FormalMultilinearSeries ℂ (ℂ × ℂ) ℂ
  commonSeries : FormalMultilinearSeries ℂ (ℂ × ℂ) ℂ
  centerHasFPowerSeries : HasFPowerSeriesAt center centerSeries base.1
  kappaHasFPowerSeries : HasFPowerSeriesAt kappa kappaSeries base.1
  unitHasFPowerSeries : HasFPowerSeriesAt unit unitSeries base
  radicandHasFPowerSeries : HasFPowerSeriesAt radicand commonSeries base
  preparedHasFPowerSeries : HasFPowerSeriesAt
    (fun point : ℂ × ℂ ↦
      (((point.2 - center point.1) ^ 2 + kappa point.1) * unit point))
    commonSeries base
  center_base : center base.1 = base.2
  kappa_base : kappa base.1 = 0
  unit_base_ne_zero : unit base ≠ 0

namespace ChapterVIConvergentPreparedGerm

variable {radicand : ℂ × ℂ → ℂ} {base : ℂ × ℂ}

/-- The completed-square factorization holds as an equality of actual functions near the base
point, once both sides have been identified with the same convergent series. -/
theorem eventually_factorization
    (germ : ChapterVIConvergentPreparedGerm radicand base) :
    radicand =ᶠ[𝓝 base]
      fun point : ℂ × ℂ ↦
        (((point.2 - germ.center point.1) ^ 2 + germ.kappa point.1) * germ.unit point) :=
  eventuallyEq_of_hasFPowerSeriesAt_same
    germ.radicandHasFPowerSeries germ.preparedHasFPowerSeries

/-- The prepared unit is genuinely nonzero on a neighbourhood of the pinch point. -/
theorem eventually_unit_ne_zero
    (germ : ChapterVIConvergentPreparedGerm radicand base) :
    ∀ᶠ point in 𝓝 base, germ.unit point ≠ 0 :=
  germ.unitHasFPowerSeries.continuousAt.eventually_ne germ.unit_base_ne_zero

/-- The three prepared factors are analytic at their relevant base points. -/
theorem analytic_factors
    (germ : ChapterVIConvergentPreparedGerm radicand base) :
    AnalyticAt ℂ germ.center base.1 ∧
      AnalyticAt ℂ germ.kappa base.1 ∧
      AnalyticAt ℂ germ.unit base :=
  ⟨germ.centerHasFPowerSeries.analyticAt,
    germ.kappaHasFPowerSeries.analyticAt,
    germ.unitHasFPowerSeries.analyticAt⟩

end ChapterVIConvergentPreparedGerm

end PoincareChapterVI
