/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.ChapterVISourceCoordinates
import PoincareChapterVI.ConjugationLocalInverse

/-!
# Reality of the selected local source-coordinate branches

The source formulas have real coefficients.  The inverse-function-theorem choices used to invert
integer powers and Kepler's exponential therefore commute locally with conjugation when based at
real points.  These exact identities are analytic input to the compiled orientation certificate;
they are not inferred from floating-point samples.
-/

noncomputable section

open Complex Filter Topology
open scoped ComplexConjugate

namespace PoincareChapterVI

/-- An integer power map commutes with conjugation, including for negative exponents away from
zero. -/
theorem conj_zpow (degree : ℤ) (z : ℂ) :
    conj z ^ degree = conj (z ^ degree) := by
  exact (map_zpow₀ (starRingEnd ℂ) z degree).symm

/-- The canonical inverse branch of an integer power commutes locally with conjugation when its
base point is real. -/
theorem eventually_conj_chapterVIPowerLocalInverse_conj
    (degree : ℤ) (base : ℂ) (hbase : base ≠ 0) (hdegree : degree ≠ 0)
    (hbaseReal : conj base = base) :
    ∀ᶠ y in nhds (base ^ degree),
      conj (chapterVIPowerLocalInverse degree base hbase hdegree (conj y)) =
        chapterVIPowerLocalInverse degree base hbase hdegree y := by
  let hf : AnalyticAt ℂ (fun z : ℂ ↦ z ^ degree) base := analyticAt_id.zpow hbase
  have hderiv : deriv (fun z : ℂ ↦ z ^ degree) base ≠ 0 := by
    rw [deriv_zpow]
    exact mul_ne_zero (Int.cast_ne_zero.mpr hdegree) (zpow_ne_zero _ hbase)
  unfold chapterVIPowerLocalInverse
  exact eventually_conj_localInverse_conj hf.hasStrictDerivAt hderiv hbaseReal
    (Filter.Eventually.of_forall (fun z ↦ conj_zpow degree z))

/-- Equivalent, composition-friendly orientation of the preceding symmetry identity. -/
theorem eventually_chapterVIPowerLocalInverse_conj
    (degree : ℤ) (base : ℂ) (hbase : base ≠ 0) (hdegree : degree ≠ 0)
    (hbaseReal : conj base = base) :
    ∀ᶠ y in nhds (base ^ degree),
      chapterVIPowerLocalInverse degree base hbase hdegree (conj y) =
        conj (chapterVIPowerLocalInverse degree base hbase hdegree y) := by
  filter_upwards [eventually_conj_chapterVIPowerLocalInverse_conj
    degree base hbase hdegree hbaseReal] with y hy
  have := congrArg conj hy
  simpa using this

/-- Kepler's exponential commutes with conjugation when the eccentricity is real. -/
theorem chapterVIKeplerExponential_conj
    {eccentricity : ℂ} (he : conj eccentricity = eccentricity) (z : ℂ) :
    chapterVIKeplerExponential eccentricity (conj z) =
      conj (chapterVIKeplerExponential eccentricity z) := by
  unfold chapterVIKeplerExponential
  rw [map_mul, ← exp_conj]
  congr 1
  rw [map_mul, map_div₀, map_ofNat, map_sub, map_inv₀, he]

/-- The canonical local inverse of Kepler's exponential commutes locally with conjugation when
its eccentricity and base anomaly are real. -/
theorem eventually_conj_chapterVIKeplerLocalInverse_conj
    (eccentricity x : ℂ) (hx : x ≠ 0)
    (hcritical : chapterVIKeplerExponentialDerivative eccentricity x ≠ 0)
    (he : conj eccentricity = eccentricity) (hxReal : conj x = x) :
    ∀ᶠ y in nhds (chapterVIKeplerExponential eccentricity x),
      conj (chapterVIKeplerLocalInverse eccentricity x hx hcritical (conj y)) =
        chapterVIKeplerLocalInverse eccentricity x hx hcritical y := by
  let hf := analyticAt_chapterVIKeplerExponential eccentricity hx
  have hderiv : deriv (chapterVIKeplerExponential eccentricity) x ≠ 0 := by
    rwa [deriv_chapterVIKeplerExponential eccentricity hx]
  unfold chapterVIKeplerLocalInverse
  exact eventually_conj_localInverse_conj hf.hasStrictDerivAt hderiv hxReal
    (Filter.Eventually.of_forall (chapterVIKeplerExponential_conj he))

/-- Equivalent, composition-friendly orientation of the Kepler-inverse symmetry identity. -/
theorem eventually_chapterVIKeplerLocalInverse_conj
    (eccentricity x : ℂ) (hx : x ≠ 0)
    (hcritical : chapterVIKeplerExponentialDerivative eccentricity x ≠ 0)
    (he : conj eccentricity = eccentricity) (hxReal : conj x = x) :
    ∀ᶠ y in nhds (chapterVIKeplerExponential eccentricity x),
      chapterVIKeplerLocalInverse eccentricity x hx hcritical (conj y) =
        conj (chapterVIKeplerLocalInverse eccentricity x hx hcritical y) := by
  filter_upwards [eventually_conj_chapterVIKeplerLocalInverse_conj
    eccentricity x hx hcritical he hxReal] with y hy
  have := congrArg conj hy
  simpa using this

end PoincareChapterVI
