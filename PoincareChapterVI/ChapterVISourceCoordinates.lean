/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import PoincareChapterVI.ChapterVISingularityAlgebra

/-!
# Poincaré's local complex Kepler coordinates

In §96 Poincaré passes from `x = exp(iu)` to the exponential of the mean anomaly

`exp(il) = x exp(e/2 (x⁻¹ - x))`.

This file proves that map analytic and locally analytically invertible away from the familiar
Kepler critical equation `1 - e (x + x⁻¹) / 2 = 0`.  Applying the two local inverses to the
concrete Laurent radicand from `ChapterVISingularityAlgebra` produces an actual convergent
radicand germ in the two mean-anomaly exponentials.  This closes the coordinate-realization
step before Poincaré's further monomial change to `(z,t)`.
-/

noncomputable section

open Complex Filter Topology

namespace PoincareChapterVI

/-- Exponential form of Kepler's equation, `exp(il)` as a function of `x = exp(iu)`. -/
def chapterVIKeplerExponential (eccentricity x : ℂ) : ℂ :=
  x * exp (eccentricity / 2 * (x⁻¹ - x))

/-- The scalar derivative of `chapterVIKeplerExponential`. -/
def chapterVIKeplerExponentialDerivative (eccentricity x : ℂ) : ℂ :=
  exp (eccentricity / 2 * (x⁻¹ - x)) *
    (1 - eccentricity / 2 * (x + x⁻¹))

theorem hasDerivAt_chapterVIKeplerExponential
    (eccentricity : ℂ) {x : ℂ} (hx : x ≠ 0) :
    HasDerivAt (chapterVIKeplerExponential eccentricity)
      (chapterVIKeplerExponentialDerivative eccentricity x) x := by
  unfold chapterVIKeplerExponential chapterVIKeplerExponentialDerivative
  have h := (hasDerivAt_id x).mul
    (((((hasDerivAt_inv hx).sub (hasDerivAt_id x)).const_mul
      (eccentricity / 2))).cexp)
  convert h using 1
  all_goals try rfl
  simp only [Pi.sub_apply, id_eq, one_mul]
  field_simp [hx]
  ring

theorem deriv_chapterVIKeplerExponential
    (eccentricity : ℂ) {x : ℂ} (hx : x ≠ 0) :
    deriv (chapterVIKeplerExponential eccentricity) x =
      chapterVIKeplerExponentialDerivative eccentricity x :=
  (hasDerivAt_chapterVIKeplerExponential eccentricity hx).deriv

theorem analyticAt_chapterVIKeplerExponential
    (eccentricity : ℂ) {x : ℂ} (hx : x ≠ 0) :
    AnalyticAt ℂ (chapterVIKeplerExponential eccentricity) x := by
  unfold chapterVIKeplerExponential
  exact analyticAt_id.mul
    ((analyticAt_const.mul ((analyticAt_id.inv hx).sub analyticAt_id)).cexp)

theorem chapterVIKeplerExponential_ne_zero
    (eccentricity : ℂ) {x : ℂ} (hx : x ≠ 0) :
    chapterVIKeplerExponential eccentricity x ≠ 0 := by
  unfold chapterVIKeplerExponential
  exact mul_ne_zero hx (exp_ne_zero _)

/-- Poincaré's displayed parameter `z` is the monomial in the two exponentials of the mean
anomalies. -/
theorem chapterVI_singularityParameter_eq_keplerExponential_zpow
    (a c : ℤ) (firstEccentricity secondEccentricity x y : ℂ) :
    chapterVISingularityParameter a c
        ((a : ℂ) * firstEccentricity / 2)
        ((c : ℂ) * secondEccentricity / 2) x y =
      chapterVIKeplerExponential firstEccentricity x ^ a *
        chapterVIKeplerExponential secondEccentricity y ^ c := by
  unfold chapterVISingularityParameter chapterVIKeplerExponential
  rw [mul_zpow, mul_zpow, ← exp_int_mul, ← exp_int_mul]
  rw [show
    (a : ℂ) * firstEccentricity / 2 * (x⁻¹ - x) +
        (c : ℂ) * secondEccentricity / 2 * (y⁻¹ - y) =
      (a : ℂ) * (firstEccentricity / 2 * (x⁻¹ - x)) +
        (c : ℂ) * (secondEccentricity / 2 * (y⁻¹ - y)) by ring,
    exp_add]
  ring

theorem chapterVIKeplerExponentialDerivative_ne_zero_iff
    (eccentricity : ℂ) {x : ℂ} (_hx : x ≠ 0) :
    chapterVIKeplerExponentialDerivative eccentricity x ≠ 0 ↔
      1 - eccentricity / 2 * (x + x⁻¹) ≠ 0 := by
  unfold chapterVIKeplerExponentialDerivative
  constructor
  · intro hproduct hright
    exact hproduct (mul_eq_zero_of_right _ hright)
  · exact mul_ne_zero (exp_ne_zero _)

/-- The canonical local inverse supplied by the analytic inverse-function theorem. -/
noncomputable def chapterVIKeplerLocalInverse
    (eccentricity x : ℂ) (hx : x ≠ 0)
    (hcritical : chapterVIKeplerExponentialDerivative eccentricity x ≠ 0) : ℂ → ℂ :=
  let hf := analyticAt_chapterVIKeplerExponential eccentricity hx
  let hderiv : deriv (chapterVIKeplerExponential eccentricity) x ≠ 0 := by
    rwa [deriv_chapterVIKeplerExponential eccentricity hx]
  hf.hasStrictDerivAt.localInverse (chapterVIKeplerExponential eccentricity)
    (deriv (chapterVIKeplerExponential eccentricity) x) x hderiv

theorem analyticAt_chapterVIKeplerLocalInverse
    (eccentricity x : ℂ) (hx : x ≠ 0)
    (hcritical : chapterVIKeplerExponentialDerivative eccentricity x ≠ 0) :
    AnalyticAt ℂ (chapterVIKeplerLocalInverse eccentricity x hx hcritical)
      (chapterVIKeplerExponential eccentricity x) := by
  let hf := analyticAt_chapterVIKeplerExponential eccentricity hx
  have hderiv : deriv (chapterVIKeplerExponential eccentricity) x ≠ 0 := by
    rwa [deriv_chapterVIKeplerExponential eccentricity hx]
  simpa only [chapterVIKeplerLocalInverse, hf, hderiv] using
    hf.analyticAt_localInverse hderiv

@[simp]
theorem chapterVIKeplerLocalInverse_apply_base
    (eccentricity x : ℂ) (hx : x ≠ 0)
    (hcritical : chapterVIKeplerExponentialDerivative eccentricity x ≠ 0) :
    chapterVIKeplerLocalInverse eccentricity x hx hcritical
      (chapterVIKeplerExponential eccentricity x) = x := by
  unfold chapterVIKeplerLocalInverse
  exact HasStrictFDerivAt.localInverse_apply_image ..

theorem eventually_chapterVIKeplerExponential_localInverse
    (eccentricity x : ℂ) (hx : x ≠ 0)
    (hcritical : chapterVIKeplerExponentialDerivative eccentricity x ≠ 0) :
    (fun mean ↦ chapterVIKeplerExponential eccentricity
      (chapterVIKeplerLocalInverse eccentricity x hx hcritical mean)) =ᶠ[
        𝓝 (chapterVIKeplerExponential eccentricity x)] fun mean ↦ mean := by
  unfold chapterVIKeplerLocalInverse
  exact HasStrictDerivAt.eventually_right_inverse ..

theorem eventually_chapterVIKeplerLocalInverse_exponential
    (eccentricity x : ℂ) (hx : x ≠ 0)
    (hcritical : chapterVIKeplerExponentialDerivative eccentricity x ≠ 0) :
    (fun anomaly ↦ chapterVIKeplerLocalInverse eccentricity x hx hcritical
      (chapterVIKeplerExponential eccentricity anomaly)) =ᶠ[𝓝 x] fun anomaly ↦ anomaly := by
  unfold chapterVIKeplerLocalInverse
  exact HasStrictDerivAt.eventually_left_inverse ..

/-- The canonical local inverse of the integer power map at a nonzero point. -/
noncomputable def chapterVIPowerLocalInverse
    (degree : ℤ) (base : ℂ) (hbase : base ≠ 0) (hdegree : degree ≠ 0) : ℂ → ℂ :=
  let hf : AnalyticAt ℂ (fun z : ℂ ↦ z ^ degree) base := analyticAt_id.zpow hbase
  let hderiv : deriv (fun z : ℂ ↦ z ^ degree) base ≠ 0 := by
    rw [deriv_zpow]
    exact mul_ne_zero (Int.cast_ne_zero.mpr hdegree) (zpow_ne_zero _ hbase)
  hf.hasStrictDerivAt.localInverse (fun z : ℂ ↦ z ^ degree)
    (deriv (fun z : ℂ ↦ z ^ degree) base) base hderiv

theorem analyticAt_chapterVIPowerLocalInverse
    (degree : ℤ) (base : ℂ) (hbase : base ≠ 0) (hdegree : degree ≠ 0) :
    AnalyticAt ℂ (chapterVIPowerLocalInverse degree base hbase hdegree) (base ^ degree) := by
  let hf : AnalyticAt ℂ (fun z : ℂ ↦ z ^ degree) base := analyticAt_id.zpow hbase
  have hderiv : deriv (fun z : ℂ ↦ z ^ degree) base ≠ 0 := by
    rw [deriv_zpow]
    exact mul_ne_zero (Int.cast_ne_zero.mpr hdegree) (zpow_ne_zero _ hbase)
  simpa only [chapterVIPowerLocalInverse, hf, hderiv] using
    hf.analyticAt_localInverse hderiv

@[simp]
theorem chapterVIPowerLocalInverse_apply_base
    (degree : ℤ) (base : ℂ) (hbase : base ≠ 0) (hdegree : degree ≠ 0) :
    chapterVIPowerLocalInverse degree base hbase hdegree (base ^ degree) = base := by
  unfold chapterVIPowerLocalInverse
  exact HasStrictFDerivAt.localInverse_apply_image ..

theorem eventually_chapterVIPowerLocalInverse_zpow
    (degree : ℤ) (base : ℂ) (hbase : base ≠ 0) (hdegree : degree ≠ 0) :
    (fun z : ℂ ↦ chapterVIPowerLocalInverse degree base hbase hdegree (z ^ degree)) =ᶠ[𝓝 base]
      fun z ↦ z := by
  unfold chapterVIPowerLocalInverse
  exact HasStrictDerivAt.eventually_left_inverse ..

/-- Poincaré's monomial change from the two mean-anomaly exponentials `(s,r)` to `(z,s)`,
where `s = exp(il)` and `z = sᵃ rᶜ`.  His contour variable satisfies `s = tᶜ`. -/
def chapterVIMeanToContourMap (a c : ℤ) (mean : ℂ × ℂ) : ℂ × ℂ :=
  (mean.1 ^ a * mean.2 ^ c, mean.1)

theorem chapterVIMeanToContourMap_keplerExponential
    (a c : ℤ) (firstEccentricity secondEccentricity x y : ℂ) :
    chapterVIMeanToContourMap a c
        (chapterVIKeplerExponential firstEccentricity x,
          chapterVIKeplerExponential secondEccentricity y) =
      (chapterVISingularityParameter a c
          ((a : ℂ) * firstEccentricity / 2)
          ((c : ℂ) * secondEccentricity / 2) x y,
        chapterVIKeplerExponential firstEccentricity x) := by
  ext
  · exact (chapterVI_singularityParameter_eq_keplerExponential_zpow
      a c firstEccentricity secondEccentricity x y).symm
  · rfl

theorem analyticAt_chapterVIPlanarKeplerLaurentPlus
    (eccentricity complement : ℂ) {x : ℂ} (hx : x ≠ 0) :
    AnalyticAt ℂ (chapterVIPlanarKeplerLaurentPlus eccentricity complement) x := by
  unfold chapterVIPlanarKeplerLaurentPlus chapterVIPlanarDistanceFactorPlus
  have hnumerator : AnalyticAt ℂ
      (fun x : ℂ ↦ (x ^ 2 + 1) - 2 * x * eccentricity + complement * (x ^ 2 - 1)) x := by
    fun_prop
  have hdenominator : AnalyticAt ℂ (fun x : ℂ ↦ 2 * x) x := by fun_prop
  exact hnumerator.div hdenominator (mul_ne_zero (by norm_num) hx)

theorem analyticAt_chapterVIPlanarKeplerLaurentMinus
    (eccentricity complement : ℂ) {x : ℂ} (hx : x ≠ 0) :
    AnalyticAt ℂ (chapterVIPlanarKeplerLaurentMinus eccentricity complement) x := by
  unfold chapterVIPlanarKeplerLaurentMinus chapterVIPlanarDistanceFactorMinus
  have hnumerator : AnalyticAt ℂ
      (fun x : ℂ ↦ (x ^ 2 + 1) - 2 * x * eccentricity - complement * (x ^ 2 - 1)) x := by
    fun_prop
  have hdenominator : AnalyticAt ℂ (fun x : ℂ ↦ 2 * x) x := by fun_prop
  exact hnumerator.div hdenominator (mul_ne_zero (by norm_num) hx)

/-- Poincaré's concrete source radicand is analytic in `(x,y)` wherever both Laurent
coordinates are nonzero. -/
theorem analyticAt_chapterVIPlanarSourceRadicand
    (firstEccentricity firstComplement secondEccentricity secondComplement beta betaZero : ℂ)
    {point : ℂ × ℂ} (hx : point.1 ≠ 0) (hy : point.2 ≠ 0) :
    AnalyticAt ℂ (fun p : ℂ × ℂ ↦
      chapterVIPlanarSourceRadicand firstEccentricity firstComplement
        secondEccentricity secondComplement beta betaZero p.1 p.2) point := by
  have hfirstPlus := (analyticAt_chapterVIPlanarKeplerLaurentPlus
    firstEccentricity firstComplement hx).comp analyticAt_fst
  have hsecondPlus := (analyticAt_chapterVIPlanarKeplerLaurentPlus
    secondEccentricity secondComplement hy).comp analyticAt_snd
  have hfirstMinus := (analyticAt_chapterVIPlanarKeplerLaurentMinus
    firstEccentricity firstComplement hx).comp analyticAt_fst
  have hsecondMinus := (analyticAt_chapterVIPlanarKeplerLaurentMinus
    secondEccentricity secondComplement hy).comp analyticAt_snd
  exact (hfirstPlus.sub (analyticAt_const.mul hsecondPlus)).mul
    (hfirstMinus.sub (analyticAt_const.mul hsecondMinus))

/-- The source radicand expressed in the two exponentials of the mean anomalies, using the
canonical local inverse branches at a chosen anomaly pair. -/
def chapterVIMeanAnomalyRadicand
    (firstEccentricity firstComplement secondEccentricity secondComplement beta betaZero : ℂ)
    (base : ℂ × ℂ) (hx : base.1 ≠ 0) (hy : base.2 ≠ 0)
    (hfirstCritical : chapterVIKeplerExponentialDerivative firstEccentricity base.1 ≠ 0)
    (hsecondCritical : chapterVIKeplerExponentialDerivative secondEccentricity base.2 ≠ 0)
    (mean : ℂ × ℂ) : ℂ :=
  chapterVIPlanarSourceRadicand firstEccentricity firstComplement
    secondEccentricity secondComplement beta betaZero
    (chapterVIKeplerLocalInverse firstEccentricity base.1 hx hfirstCritical mean.1)
    (chapterVIKeplerLocalInverse secondEccentricity base.2 hy hsecondCritical mean.2)

/-- Poincaré's radicand in the locally equivalent contour coordinates `(z,s)`, with
`z = sᵃrᶜ`.  The inverse of the `c`-th power is the analytic branch based at the second
mean-anomaly exponential. -/
def chapterVIContourRadicand
    (a c : ℤ)
    (firstEccentricity firstComplement secondEccentricity secondComplement beta betaZero : ℂ)
    (base : ℂ × ℂ) (hx : base.1 ≠ 0) (hy : base.2 ≠ 0)
    (hfirstCritical : chapterVIKeplerExponentialDerivative firstEccentricity base.1 ≠ 0)
    (hsecondCritical : chapterVIKeplerExponentialDerivative secondEccentricity base.2 ≠ 0)
    (hc : c ≠ 0) (contour : ℂ × ℂ) : ℂ :=
  let secondMean := chapterVIKeplerExponential secondEccentricity base.2
  let hsecondMean : secondMean ≠ 0 := chapterVIKeplerExponential_ne_zero _ hy
  chapterVIMeanAnomalyRadicand firstEccentricity firstComplement
    secondEccentricity secondComplement beta betaZero base hx hy
    hfirstCritical hsecondCritical
    (contour.2,
      chapterVIPowerLocalInverse c secondMean hsecondMean hc
        (contour.1 / contour.2 ^ a))

/-- The contour-coordinate base corresponding to a chosen anomaly pair. -/
def chapterVIContourBase
    (a c : ℤ) (firstEccentricity secondEccentricity : ℂ) (base : ℂ × ℂ) : ℂ × ℂ :=
  chapterVIMeanToContourMap a c
    (chapterVIKeplerExponential firstEccentricity base.1,
      chapterVIKeplerExponential secondEccentricity base.2)

/-- The literal §99 radicand `ψ(z,t)`, obtained from the `(z,s)` germ by Poincaré's relation
`s = tᶜ`. -/
def chapterVIPoincareRadicand
    (a c : ℤ)
    (firstEccentricity firstComplement secondEccentricity secondComplement beta betaZero : ℂ)
    (base : ℂ × ℂ) (hx : base.1 ≠ 0) (hy : base.2 ≠ 0)
    (hfirstCritical : chapterVIKeplerExponentialDerivative firstEccentricity base.1 ≠ 0)
    (hsecondCritical : chapterVIKeplerExponentialDerivative secondEccentricity base.2 ≠ 0)
    (hc : c ≠ 0) (point : ℂ × ℂ) : ℂ :=
  chapterVIContourRadicand a c firstEccentricity firstComplement
    secondEccentricity secondComplement beta betaZero base hx hy
    hfirstCritical hsecondCritical hc (point.1, point.2 ^ c)

@[simp]
theorem chapterVIContourRadicand_apply_base
    (a c : ℤ)
    (firstEccentricity firstComplement secondEccentricity secondComplement beta betaZero : ℂ)
    (base : ℂ × ℂ) (hx : base.1 ≠ 0) (hy : base.2 ≠ 0)
    (hfirstCritical : chapterVIKeplerExponentialDerivative firstEccentricity base.1 ≠ 0)
    (hsecondCritical : chapterVIKeplerExponentialDerivative secondEccentricity base.2 ≠ 0)
    (hc : c ≠ 0) :
    chapterVIContourRadicand a c firstEccentricity firstComplement
        secondEccentricity secondComplement beta betaZero base hx hy
        hfirstCritical hsecondCritical hc
        (chapterVIContourBase a c firstEccentricity secondEccentricity base) =
      chapterVIMeanAnomalyRadicand firstEccentricity firstComplement
        secondEccentricity secondComplement beta betaZero base hx hy
        hfirstCritical hsecondCritical
        (chapterVIKeplerExponential firstEccentricity base.1,
          chapterVIKeplerExponential secondEccentricity base.2) := by
  have hfirstMean : chapterVIKeplerExponential firstEccentricity base.1 ≠ 0 :=
    chapterVIKeplerExponential_ne_zero _ hx
  have hsecondMean : chapterVIKeplerExponential secondEccentricity base.2 ≠ 0 :=
    chapterVIKeplerExponential_ne_zero _ hy
  unfold chapterVIContourRadicand chapterVIContourBase chapterVIMeanToContourMap
  dsimp only
  rw [mul_div_cancel_left₀ _ (zpow_ne_zero _ hfirstMean)]
  rw [chapterVIPowerLocalInverse_apply_base c _ hsecondMean hc]

@[simp]
theorem chapterVIPoincareRadicand_apply_base
    (a c : ℤ)
    (firstEccentricity firstComplement secondEccentricity secondComplement beta betaZero : ℂ)
    (base : ℂ × ℂ) (hx : base.1 ≠ 0) (hy : base.2 ≠ 0)
    (hfirstCritical : chapterVIKeplerExponentialDerivative firstEccentricity base.1 ≠ 0)
    (hsecondCritical : chapterVIKeplerExponentialDerivative secondEccentricity base.2 ≠ 0)
    (hc : c ≠ 0) (tBase : ℂ)
    (htPower : tBase ^ c = chapterVIKeplerExponential firstEccentricity base.1) :
    chapterVIPoincareRadicand a c firstEccentricity firstComplement
        secondEccentricity secondComplement beta betaZero base hx hy
        hfirstCritical hsecondCritical hc
        ((chapterVIContourBase a c firstEccentricity secondEccentricity base).1, tBase) =
      chapterVIPlanarSourceRadicand firstEccentricity firstComplement
        secondEccentricity secondComplement beta betaZero base.1 base.2 := by
  change chapterVIContourRadicand a c firstEccentricity firstComplement
      secondEccentricity secondComplement beta betaZero base hx hy
      hfirstCritical hsecondCritical hc
      ((chapterVIContourBase a c firstEccentricity secondEccentricity base).1,
        tBase ^ c) = _
  rw [htPower]
  have hpair :
      ((chapterVIContourBase a c firstEccentricity secondEccentricity base).1,
        chapterVIKeplerExponential firstEccentricity base.1) =
      chapterVIContourBase a c firstEccentricity secondEccentricity base := by
    apply Prod.ext
    · rfl
    · rfl
  rw [hpair]
  rw [chapterVIContourRadicand_apply_base]
  simp [chapterVIMeanAnomalyRadicand]

/-- The actual mean-anomaly radicand is a convergent analytic germ. -/
theorem analyticAt_chapterVIMeanAnomalyRadicand
    (firstEccentricity firstComplement secondEccentricity secondComplement beta betaZero : ℂ)
    (base : ℂ × ℂ) (hx : base.1 ≠ 0) (hy : base.2 ≠ 0)
    (hfirstCritical : chapterVIKeplerExponentialDerivative firstEccentricity base.1 ≠ 0)
    (hsecondCritical : chapterVIKeplerExponentialDerivative secondEccentricity base.2 ≠ 0) :
    AnalyticAt ℂ
      (chapterVIMeanAnomalyRadicand firstEccentricity firstComplement
        secondEccentricity secondComplement beta betaZero base hx hy
        hfirstCritical hsecondCritical)
      (chapterVIKeplerExponential firstEccentricity base.1,
        chapterVIKeplerExponential secondEccentricity base.2) := by
  let inversePair : ℂ × ℂ → ℂ × ℂ := fun mean ↦
    (chapterVIKeplerLocalInverse firstEccentricity base.1 hx hfirstCritical mean.1,
      chapterVIKeplerLocalInverse secondEccentricity base.2 hy hsecondCritical mean.2)
  let meanBase : ℂ × ℂ :=
    (chapterVIKeplerExponential firstEccentricity base.1,
      chapterVIKeplerExponential secondEccentricity base.2)
  have hfst : AnalyticAt ℂ (fun mean : ℂ × ℂ ↦ mean.1) meanBase := analyticAt_fst
  have hsnd : AnalyticAt ℂ (fun mean : ℂ × ℂ ↦ mean.2) meanBase := analyticAt_snd
  have hfirstInverse : AnalyticAt ℂ
      (fun mean : ℂ × ℂ ↦
        chapterVIKeplerLocalInverse firstEccentricity base.1 hx hfirstCritical mean.1)
      meanBase := by
    simpa only [meanBase, Function.comp_def] using
      (analyticAt_chapterVIKeplerLocalInverse firstEccentricity base.1 hx
        hfirstCritical).comp_of_eq hfst rfl
  have hsecondInverse : AnalyticAt ℂ
      (fun mean : ℂ × ℂ ↦
        chapterVIKeplerLocalInverse secondEccentricity base.2 hy hsecondCritical mean.2)
      meanBase := by
    simpa only [meanBase, Function.comp_def] using
      (analyticAt_chapterVIKeplerLocalInverse secondEccentricity base.2 hy
        hsecondCritical).comp_of_eq hsnd rfl
  have hinverse : AnalyticAt ℂ inversePair
      meanBase :=
    hfirstInverse.prod hsecondInverse
  have hsource := analyticAt_chapterVIPlanarSourceRadicand
    firstEccentricity firstComplement secondEccentricity secondComplement beta betaZero hx hy
  have hinverseBase : inversePair meanBase = base := by
    apply Prod.ext <;>
      simp [inversePair, meanBase, chapterVIKeplerLocalInverse_apply_base]
  change AnalyticAt ℂ (fun mean : ℂ × ℂ ↦
    chapterVIPlanarSourceRadicand firstEccentricity firstComplement
      secondEccentricity secondComplement beta betaZero
      (chapterVIKeplerLocalInverse firstEccentricity base.1 hx hfirstCritical mean.1)
      (chapterVIKeplerLocalInverse secondEccentricity base.2 hy hsecondCritical mean.2)) meanBase
  simpa only [inversePair, Function.comp_def] using
      hsource.comp_of_eq hinverse hinverseBase

/-- The radicand is a convergent analytic germ in Poincaré's `(z,s)` contour coordinates. -/
theorem analyticAt_chapterVIContourRadicand
    (a c : ℤ)
    (firstEccentricity firstComplement secondEccentricity secondComplement beta betaZero : ℂ)
    (base : ℂ × ℂ) (hx : base.1 ≠ 0) (hy : base.2 ≠ 0)
    (hfirstCritical : chapterVIKeplerExponentialDerivative firstEccentricity base.1 ≠ 0)
    (hsecondCritical : chapterVIKeplerExponentialDerivative secondEccentricity base.2 ≠ 0)
    (hc : c ≠ 0) :
    AnalyticAt ℂ
      (chapterVIContourRadicand a c firstEccentricity firstComplement
        secondEccentricity secondComplement beta betaZero base hx hy
        hfirstCritical hsecondCritical hc)
      (chapterVIContourBase a c firstEccentricity secondEccentricity base) := by
  let firstMean := chapterVIKeplerExponential firstEccentricity base.1
  let secondMean := chapterVIKeplerExponential secondEccentricity base.2
  have hfirstMean : firstMean ≠ 0 := chapterVIKeplerExponential_ne_zero _ hx
  have hsecondMean : secondMean ≠ 0 := chapterVIKeplerExponential_ne_zero _ hy
  let contourBase : ℂ × ℂ := (firstMean ^ a * secondMean ^ c, firstMean)
  have hcontourBase : chapterVIContourBase a c firstEccentricity secondEccentricity base =
      contourBase := rfl
  have hratio : AnalyticAt ℂ (fun contour : ℂ × ℂ ↦ contour.1 / contour.2 ^ a)
      contourBase :=
    analyticAt_fst.div (analyticAt_snd.zpow hfirstMean)
      (zpow_ne_zero _ hfirstMean)
  have hratioBase : contourBase.1 / contourBase.2 ^ a = secondMean ^ c := by
    change (firstMean ^ a * secondMean ^ c) / firstMean ^ a = secondMean ^ c
    exact mul_div_cancel_left₀ _ (zpow_ne_zero _ hfirstMean)
  have hsecondInverse : AnalyticAt ℂ
      (fun contour : ℂ × ℂ ↦
        chapterVIPowerLocalInverse c secondMean hsecondMean hc
          (contour.1 / contour.2 ^ a)) contourBase := by
    simpa only [Function.comp_def] using
      (analyticAt_chapterVIPowerLocalInverse c secondMean hsecondMean hc).comp_of_eq
        hratio hratioBase
  let meanFromContour : ℂ × ℂ → ℂ × ℂ := fun contour ↦
    (contour.2,
      chapterVIPowerLocalInverse c secondMean hsecondMean hc
        (contour.1 / contour.2 ^ a))
  have hmeanFromContour : AnalyticAt ℂ meanFromContour contourBase :=
    analyticAt_snd.prod hsecondInverse
  have hmeanFromContourBase : meanFromContour contourBase = (firstMean, secondMean) := by
    apply Prod.ext
    · rfl
    · simp [meanFromContour, hratioBase, chapterVIPowerLocalInverse_apply_base]
  have hmeanRadicand := analyticAt_chapterVIMeanAnomalyRadicand
    firstEccentricity firstComplement secondEccentricity secondComplement beta betaZero
    base hx hy hfirstCritical hsecondCritical
  rw [hcontourBase]
  change AnalyticAt ℂ (fun contour : ℂ × ℂ ↦
    chapterVIMeanAnomalyRadicand firstEccentricity firstComplement
      secondEccentricity secondComplement beta betaZero base hx hy
      hfirstCritical hsecondCritical (meanFromContour contour)) contourBase
  simpa only [Function.comp_def, firstMean, secondMean] using
    hmeanRadicand.comp_of_eq hmeanFromContour hmeanFromContourBase

/-- The contour-coordinate analytic germ comes with a complete convergent power series. -/
theorem exists_hasFPowerSeriesAt_chapterVIContourRadicand
    (a c : ℤ)
    (firstEccentricity firstComplement secondEccentricity secondComplement beta betaZero : ℂ)
    (base : ℂ × ℂ) (hx : base.1 ≠ 0) (hy : base.2 ≠ 0)
    (hfirstCritical : chapterVIKeplerExponentialDerivative firstEccentricity base.1 ≠ 0)
    (hsecondCritical : chapterVIKeplerExponentialDerivative secondEccentricity base.2 ≠ 0)
    (hc : c ≠ 0) :
    ∃ series : FormalMultilinearSeries ℂ (ℂ × ℂ) ℂ,
      HasFPowerSeriesAt
        (chapterVIContourRadicand a c firstEccentricity firstComplement
          secondEccentricity secondComplement beta betaZero base hx hy
          hfirstCritical hsecondCritical hc)
        series (chapterVIContourBase a c firstEccentricity secondEccentricity base) :=
  analyticAt_chapterVIContourRadicand a c firstEccentricity firstComplement
    secondEccentricity secondComplement beta betaZero base hx hy
    hfirstCritical hsecondCritical hc

/-- Poincaré's literal `ψ(z,t)` is analytic at every chosen local `c`-th root of the first
mean-anomaly exponential. -/
theorem analyticAt_chapterVIPoincareRadicand
    (a c : ℤ)
    (firstEccentricity firstComplement secondEccentricity secondComplement beta betaZero : ℂ)
    (base : ℂ × ℂ) (hx : base.1 ≠ 0) (hy : base.2 ≠ 0)
    (hfirstCritical : chapterVIKeplerExponentialDerivative firstEccentricity base.1 ≠ 0)
    (hsecondCritical : chapterVIKeplerExponentialDerivative secondEccentricity base.2 ≠ 0)
    (hc : c ≠ 0) (tBase : ℂ) (htBase : tBase ≠ 0)
    (htPower : tBase ^ c = chapterVIKeplerExponential firstEccentricity base.1) :
    AnalyticAt ℂ
      (chapterVIPoincareRadicand a c firstEccentricity firstComplement
        secondEccentricity secondComplement beta betaZero base hx hy
        hfirstCritical hsecondCritical hc)
      ((chapterVIContourBase a c firstEccentricity secondEccentricity base).1, tBase) := by
  let poincareBase : ℂ × ℂ :=
    ((chapterVIContourBase a c firstEccentricity secondEccentricity base).1, tBase)
  let toContour : ℂ × ℂ → ℂ × ℂ := fun point ↦ (point.1, point.2 ^ c)
  have htoContour : AnalyticAt ℂ toContour poincareBase :=
    analyticAt_fst.prod (analyticAt_snd.zpow htBase)
  have htoContourBase :
      toContour poincareBase = chapterVIContourBase a c firstEccentricity secondEccentricity base := by
    apply Prod.ext
    · rfl
    · exact htPower
  have hcontour := analyticAt_chapterVIContourRadicand a c firstEccentricity firstComplement
    secondEccentricity secondComplement beta betaZero base hx hy
    hfirstCritical hsecondCritical hc
  change AnalyticAt ℂ (fun point : ℂ × ℂ ↦
    chapterVIContourRadicand a c firstEccentricity firstComplement
      secondEccentricity secondComplement beta betaZero base hx hy
      hfirstCritical hsecondCritical hc (toContour point)) poincareBase
  simpa only [Function.comp_def] using hcontour.comp_of_eq htoContour htoContourBase

/-- The complete convergent series for the exact `ψ(z,t)` used in §99. -/
theorem exists_hasFPowerSeriesAt_chapterVIPoincareRadicand
    (a c : ℤ)
    (firstEccentricity firstComplement secondEccentricity secondComplement beta betaZero : ℂ)
    (base : ℂ × ℂ) (hx : base.1 ≠ 0) (hy : base.2 ≠ 0)
    (hfirstCritical : chapterVIKeplerExponentialDerivative firstEccentricity base.1 ≠ 0)
    (hsecondCritical : chapterVIKeplerExponentialDerivative secondEccentricity base.2 ≠ 0)
    (hc : c ≠ 0) (tBase : ℂ) (htBase : tBase ≠ 0)
    (htPower : tBase ^ c = chapterVIKeplerExponential firstEccentricity base.1) :
    ∃ series : FormalMultilinearSeries ℂ (ℂ × ℂ) ℂ,
      HasFPowerSeriesAt
        (chapterVIPoincareRadicand a c firstEccentricity firstComplement
          secondEccentricity secondComplement beta betaZero base hx hy
          hfirstCritical hsecondCritical hc)
        series
        ((chapterVIContourBase a c firstEccentricity secondEccentricity base).1, tBase) :=
  analyticAt_chapterVIPoincareRadicand a c firstEccentricity firstComplement
    secondEccentricity secondComplement beta betaZero base hx hy
    hfirstCritical hsecondCritical hc tBase htBase htPower

/-- A named convergent power series realizes the source radicand in mean-anomaly coordinates.
Unlike a finite jet certificate, this records convergence of the complete germ. -/
theorem exists_hasFPowerSeriesAt_chapterVIMeanAnomalyRadicand
    (firstEccentricity firstComplement secondEccentricity secondComplement beta betaZero : ℂ)
    (base : ℂ × ℂ) (hx : base.1 ≠ 0) (hy : base.2 ≠ 0)
    (hfirstCritical : chapterVIKeplerExponentialDerivative firstEccentricity base.1 ≠ 0)
    (hsecondCritical : chapterVIKeplerExponentialDerivative secondEccentricity base.2 ≠ 0) :
    ∃ series : FormalMultilinearSeries ℂ (ℂ × ℂ) ℂ,
      HasFPowerSeriesAt
        (chapterVIMeanAnomalyRadicand firstEccentricity firstComplement
          secondEccentricity secondComplement beta betaZero base hx hy
          hfirstCritical hsecondCritical)
        series
        (chapterVIKeplerExponential firstEccentricity base.1,
          chapterVIKeplerExponential secondEccentricity base.2) :=
  analyticAt_chapterVIMeanAnomalyRadicand firstEccentricity firstComplement
    secondEccentricity secondComplement beta betaZero base hx hy
    hfirstCritical hsecondCritical

/-- Pulling the mean-anomaly germ back through the two Kepler maps recovers Poincaré's original
Laurent radicand on a full neighbourhood of the chosen anomaly pair. -/
theorem eventually_chapterVIMeanAnomalyRadicand_comp_keplerExponential
    (firstEccentricity firstComplement secondEccentricity secondComplement beta betaZero : ℂ)
    (base : ℂ × ℂ) (hx : base.1 ≠ 0) (hy : base.2 ≠ 0)
    (hfirstCritical : chapterVIKeplerExponentialDerivative firstEccentricity base.1 ≠ 0)
    (hsecondCritical : chapterVIKeplerExponentialDerivative secondEccentricity base.2 ≠ 0) :
    (fun point : ℂ × ℂ ↦
      chapterVIMeanAnomalyRadicand firstEccentricity firstComplement
        secondEccentricity secondComplement beta betaZero base hx hy
        hfirstCritical hsecondCritical
        (chapterVIKeplerExponential firstEccentricity point.1,
          chapterVIKeplerExponential secondEccentricity point.2)) =ᶠ[𝓝 base]
      (fun point : ℂ × ℂ ↦
        chapterVIPlanarSourceRadicand firstEccentricity firstComplement
          secondEccentricity secondComplement beta betaZero point.1 point.2) := by
  have hfirst := eventually_chapterVIKeplerLocalInverse_exponential
    firstEccentricity base.1 hx hfirstCritical
  have hsecond := eventually_chapterVIKeplerLocalInverse_exponential
    secondEccentricity base.2 hy hsecondCritical
  filter_upwards [continuousAt_fst.eventually hfirst,
    continuousAt_snd.eventually hsecond] with point hpointFirst hpointSecond
  simp only [chapterVIMeanAnomalyRadicand]
  rw [hpointFirst, hpointSecond]

@[simp]
theorem chapterVIMeanAnomalyRadicand_apply_base
    (firstEccentricity firstComplement secondEccentricity secondComplement beta betaZero : ℂ)
    (base : ℂ × ℂ) (hx : base.1 ≠ 0) (hy : base.2 ≠ 0)
    (hfirstCritical : chapterVIKeplerExponentialDerivative firstEccentricity base.1 ≠ 0)
    (hsecondCritical : chapterVIKeplerExponentialDerivative secondEccentricity base.2 ≠ 0) :
    chapterVIMeanAnomalyRadicand firstEccentricity firstComplement
        secondEccentricity secondComplement beta betaZero base hx hy
        hfirstCritical hsecondCritical
        (chapterVIKeplerExponential firstEccentricity base.1,
          chapterVIKeplerExponential secondEccentricity base.2) =
      chapterVIPlanarSourceRadicand firstEccentricity firstComplement
        secondEccentricity secondComplement beta betaZero base.1 base.2 := by
  simp [chapterVIMeanAnomalyRadicand]

end PoincareChapterVI
