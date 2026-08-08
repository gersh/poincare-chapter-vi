/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.Basic
import PoincareChapterVI.ChapterVISourceCoordinates

/-!
# The exact double-zero interface for Poincaré's radicand

The finite algebra in Chapter VI identifies one collision factor whose value and first
`t`-derivative vanish while its second derivative does not.  The other collision factor is
nonzero.  This file records the analytic theorem that turns precisely those finite facts into
the order-two hypothesis needed by Weierstrass preparation.

The distinction matters for certificate-backed computations: a compiled certificate may prove
the three displayed derivative facts, but analyticity and the passage from those facts to the
order of the complete germ remain kernel-checked theorems.
-/

noncomputable section

open Filter

namespace PoincareChapterVI

/-- An analytic one-variable germ has order exactly two precisely when its value and first
derivative vanish and its second derivative does not. -/
theorem analyticOrderAt_eq_two_iff
    {f : ℂ → ℂ} {x : ℂ} (hf : AnalyticAt ℂ f x) :
    analyticOrderAt f x = 2 ↔
      f x = 0 ∧ deriv f x = 0 ∧ deriv (deriv f) x ≠ 0 := by
  change analyticOrderAt f x = (↑(2 : ℕ) : ℕ∞) ↔ _
  rw [analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero hf]
  constructor
  · rintro ⟨hzero, htwo⟩
    refine ⟨?_, ?_, ?_⟩
    · simpa using hzero 0 (by omega)
    · simpa [iteratedDeriv_one] using hzero 1 (by omega)
    · simpa [iteratedDeriv_succ'] using htwo
  · rintro ⟨hzero, hone, htwo⟩
    constructor
    · intro k hk
      have hk' : k = 0 ∨ k = 1 := by omega
      rcases hk' with rfl | rfl
      · simpa using hzero
      · simpa [iteratedDeriv_one] using hone
    · simpa [iteratedDeriv_succ'] using htwo

/-- If an analytic collision factor has order two and its analytic companion is nonzero, their
product has order two.  This is the exact local algebra behind Poincaré's `ψ = H H₀` step. -/
theorem analyticOrderAt_mul_eq_two_of_left
    {collision companion : ℂ → ℂ} {x : ℂ}
    (hcollision : AnalyticAt ℂ collision x)
    (hcompanion : AnalyticAt ℂ companion x)
    (horder : analyticOrderAt collision x = 2)
    (hcompanion_ne : companion x ≠ 0) :
    analyticOrderAt (collision * companion) x = 2 := by
  rw [analyticOrderAt_mul hcollision hcompanion, horder,
    hcompanion.analyticOrderAt_eq_zero.mpr hcompanion_ne]
  norm_num

/-- Certificate-facing version of `analyticOrderAt_mul_eq_two_of_left`: it asks only for the
value, first derivative, and second derivative checks on the vanishing collision factor. -/
theorem analyticOrderAt_mul_eq_two_of_left_derivatives
    {collision companion : ℂ → ℂ} {x : ℂ}
    (hcollision : AnalyticAt ℂ collision x)
    (hcompanion : AnalyticAt ℂ companion x)
    (hzero : collision x = 0)
    (hfirst : deriv collision x = 0)
    (hsecond : deriv (deriv collision) x ≠ 0)
    (hcompanion_ne : companion x ≠ 0) :
    analyticOrderAt (collision * companion) x = 2 :=
  analyticOrderAt_mul_eq_two_of_left hcollision hcompanion
    ((analyticOrderAt_eq_two_iff hcollision).mpr ⟨hzero, hfirst, hsecond⟩) hcompanion_ne

/-- The exact certificate boundary for the §99 radicand.  Once a selected source point supplies
the four finite checks on `H` and `H₀`, this theorem gives the order-two fiber statement for
Poincaré's actual convergent `ψ(z,t)`, rather than for a truncated Taylor polynomial. -/
theorem analyticOrderAt_chapterVIPoincareRadicand_fiber_eq_two
    (a c : ℤ)
    (firstEccentricity firstComplement secondEccentricity secondComplement beta betaZero : ℂ)
    (base : ℂ × ℂ) (hx : base.1 ≠ 0) (hy : base.2 ≠ 0)
    (hfirstCritical : chapterVIKeplerExponentialDerivative firstEccentricity base.1 ≠ 0)
    (hsecondCritical : chapterVIKeplerExponentialDerivative secondEccentricity base.2 ≠ 0)
    (hc : c ≠ 0) (z t : ℂ)
    (hplusAnalytic : AnalyticAt ℂ
      (fun w ↦ chapterVIPoincareCollisionFactorPlus a c firstEccentricity firstComplement
        secondEccentricity secondComplement beta base hx hy
        hfirstCritical hsecondCritical hc (z, w)) t)
    (hminusAnalytic : AnalyticAt ℂ
      (fun w ↦ chapterVIPoincareCollisionFactorMinus a c firstEccentricity firstComplement
        secondEccentricity secondComplement betaZero base hx hy
        hfirstCritical hsecondCritical hc (z, w)) t)
    (hzero : chapterVIPoincareCollisionFactorPlus a c firstEccentricity firstComplement
      secondEccentricity secondComplement beta base hx hy
      hfirstCritical hsecondCritical hc (z, t) = 0)
    (hfirst : deriv (fun w ↦ chapterVIPoincareCollisionFactorPlus a c
      firstEccentricity firstComplement secondEccentricity secondComplement beta base hx hy
      hfirstCritical hsecondCritical hc (z, w)) t = 0)
    (hsecond : deriv (deriv (fun w ↦ chapterVIPoincareCollisionFactorPlus a c
      firstEccentricity firstComplement secondEccentricity secondComplement beta base hx hy
      hfirstCritical hsecondCritical hc (z, w))) t ≠ 0)
    (hminus_ne : chapterVIPoincareCollisionFactorMinus a c firstEccentricity firstComplement
      secondEccentricity secondComplement betaZero base hx hy
      hfirstCritical hsecondCritical hc (z, t) ≠ 0) :
    analyticOrderAt
      (fun w ↦ chapterVIPoincareRadicand a c firstEccentricity firstComplement
        secondEccentricity secondComplement beta betaZero base hx hy
        hfirstCritical hsecondCritical hc (z, w)) t = 2 := by
  let plus : ℂ → ℂ := fun w ↦
    chapterVIPoincareCollisionFactorPlus a c firstEccentricity firstComplement
      secondEccentricity secondComplement beta base hx hy
      hfirstCritical hsecondCritical hc (z, w)
  let minus : ℂ → ℂ := fun w ↦
    chapterVIPoincareCollisionFactorMinus a c firstEccentricity firstComplement
      secondEccentricity secondComplement betaZero base hx hy
      hfirstCritical hsecondCritical hc (z, w)
  have hproduct :
      (fun w ↦ chapterVIPoincareRadicand a c firstEccentricity firstComplement
        secondEccentricity secondComplement beta betaZero base hx hy
        hfirstCritical hsecondCritical hc (z, w)) = plus * minus := by
    funext w
    exact chapterVIPoincareRadicand_eq_collisionFactors a c firstEccentricity firstComplement
      secondEccentricity secondComplement beta betaZero base hx hy
      hfirstCritical hsecondCritical hc (z, w)
  rw [hproduct]
  exact analyticOrderAt_mul_eq_two_of_left_derivatives hplusAnalytic hminusAnalytic
    hzero hfirst hsecond hminus_ne

/-- Fully source-specialized certificate boundary.  All analytic and coordinate hypotheses are
discharged internally; the remaining four premises are finite equalities/nonvanishing checks at
the selected anomaly pair. -/
theorem analyticOrderAt_chapterVIPoincareRadicand_sourceFiber_eq_two
    (a c : ℤ)
    (firstEccentricity firstComplement secondEccentricity secondComplement beta betaZero : ℂ)
    (base : ℂ × ℂ) (hx : base.1 ≠ 0) (hy : base.2 ≠ 0)
    (hfirstCritical : chapterVIKeplerExponentialDerivative firstEccentricity base.1 ≠ 0)
    (hsecondCritical : chapterVIKeplerExponentialDerivative secondEccentricity base.2 ≠ 0)
    (hc : c ≠ 0) (tBase : ℂ) (htBase : tBase ≠ 0)
    (htPower : tBase ^ c = chapterVIKeplerExponential firstEccentricity base.1)
    (hzero : chapterVIPoincareCollisionFactorPlus a c firstEccentricity firstComplement
      secondEccentricity secondComplement beta base hx hy
      hfirstCritical hsecondCritical hc
      ((chapterVIContourBase a c firstEccentricity secondEccentricity base).1, tBase) = 0)
    (hfirst : deriv (fun w ↦ chapterVIPoincareCollisionFactorPlus a c
      firstEccentricity firstComplement secondEccentricity secondComplement beta base hx hy
      hfirstCritical hsecondCritical hc
      ((chapterVIContourBase a c firstEccentricity secondEccentricity base).1, w)) tBase = 0)
    (hsecond : deriv (deriv (fun w ↦ chapterVIPoincareCollisionFactorPlus a c
      firstEccentricity firstComplement secondEccentricity secondComplement beta base hx hy
      hfirstCritical hsecondCritical hc
      ((chapterVIContourBase a c firstEccentricity secondEccentricity base).1, w))) tBase ≠ 0)
    (hminus_ne : chapterVIPoincareCollisionFactorMinus a c firstEccentricity firstComplement
      secondEccentricity secondComplement betaZero base hx hy
      hfirstCritical hsecondCritical hc
      ((chapterVIContourBase a c firstEccentricity secondEccentricity base).1, tBase) ≠ 0) :
    analyticOrderAt
      (fun w ↦ chapterVIPoincareRadicand a c firstEccentricity firstComplement
        secondEccentricity secondComplement beta betaZero base hx hy
        hfirstCritical hsecondCritical hc
        ((chapterVIContourBase a c firstEccentricity secondEccentricity base).1, w)) tBase = 2 := by
  let fiber : ℂ → ℂ × ℂ := fun w ↦
    ((chapterVIContourBase a c firstEccentricity secondEccentricity base).1, w)
  have hfiber : AnalyticAt ℂ fiber tBase := analyticAt_const.prod analyticAt_id
  have hplusJoint := analyticAt_chapterVIPoincareCollisionFactorPlus a c
    firstEccentricity firstComplement secondEccentricity secondComplement beta base hx hy
    hfirstCritical hsecondCritical hc tBase htBase htPower
  have hminusJoint := analyticAt_chapterVIPoincareCollisionFactorMinus a c
    firstEccentricity firstComplement secondEccentricity secondComplement betaZero base hx hy
    hfirstCritical hsecondCritical hc tBase htBase htPower
  have hplus : AnalyticAt ℂ
      (fun w ↦ chapterVIPoincareCollisionFactorPlus a c firstEccentricity firstComplement
        secondEccentricity secondComplement beta base hx hy
        hfirstCritical hsecondCritical hc (fiber w)) tBase := by
    simpa only [Function.comp_def] using hplusJoint.comp hfiber
  have hminus : AnalyticAt ℂ
      (fun w ↦ chapterVIPoincareCollisionFactorMinus a c firstEccentricity firstComplement
        secondEccentricity secondComplement betaZero base hx hy
        hfirstCritical hsecondCritical hc (fiber w)) tBase := by
    simpa only [Function.comp_def] using hminusJoint.comp hfiber
  exact analyticOrderAt_chapterVIPoincareRadicand_fiber_eq_two a c
    firstEccentricity firstComplement secondEccentricity secondComplement beta betaZero
    base hx hy hfirstCritical hsecondCritical hc
    (chapterVIContourBase a c firstEccentricity secondEccentricity base).1 tBase
    (by simpa only [fiber] using hplus) (by simpa only [fiber] using hminus)
    hzero hfirst hsecond hminus_ne

end PoincareChapterVI
