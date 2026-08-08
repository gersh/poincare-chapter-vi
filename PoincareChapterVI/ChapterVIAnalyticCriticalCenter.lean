import PoincareChapterVI.ChapterVIDFiberDerivative
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# The analytic motion of Poincaré's critical point

Section 99 begins the local preparation of the radicand by translating the fiber coordinate to
its nearby critical point.  This file constructs that critical center from Mathlib's complex
implicit function theorem.  The input is an actual analytic two-variable germ together with the
first two fiber-derivative conditions; no finite Taylor truncation is substituted for the germ.

The final theorem applies the construction to the exact Chapter VI source radicand at the
certified point D.  The finite LeanCompCert calculation enters upstream through the exact
order-two theorem.  The passage from that finite result to a moving critical point is analytic.
-/

open Filter
open scoped Topology ContDiff

namespace PoincareChapterVI

/-- The derivative in the second coordinate of a two-variable complex function. -/
noncomputable def chapterVIFiberDerivative (f : ℂ × ℂ → ℂ) (point : ℂ × ℂ) : ℂ :=
  fderiv ℂ f point (0, 1)

/-- The fiber derivative of an analytic two-variable germ is itself analytic. -/
theorem analyticAt_chapterVIFiberDerivative
    {f : ℂ × ℂ → ℂ} {point : ℂ × ℂ} (hf : AnalyticAt ℂ f point) :
    AnalyticAt ℂ (chapterVIFiberDerivative f) point := by
  unfold chapterVIFiberDerivative
  have hfd : AnalyticAt ℂ (fderiv ℂ f) point := hf.fderiv
  exact (hfd.contDiffAt.clm_apply contDiffAt_const).analyticAt

/-- On a fixed first-coordinate fiber, the Fréchet partial derivative is the usual derivative. -/
theorem chapterVIFiberDerivative_eq_deriv
    {f : ℂ × ℂ → ℂ} {z t : ℂ} (hf : AnalyticAt ℂ f (z, t)) :
    chapterVIFiberDerivative f (z, t) = deriv (fun w ↦ f (z, w)) t := by
  have hpair : HasDerivAt (fun w : ℂ ↦ (z, w)) (0, 1) t :=
    (hasDerivAt_const t z).prodMk (hasDerivAt_id t)
  have hcomp := hf.differentiableAt.hasFDerivAt.comp_hasDerivAt t hpair
  simpa only [Function.comp_def, chapterVIFiberDerivative] using hcomp.deriv.symm

/-- The identification with the one-variable derivative holds throughout an analytic
neighborhood, so it may itself be differentiated. -/
theorem eventually_chapterVIFiberDerivative_eq_deriv
    {f : ℂ × ℂ → ℂ} {z t : ℂ} (hf : AnalyticAt ℂ f (z, t)) :
    (fun w ↦ chapterVIFiberDerivative f (z, w)) =ᶠ[nhds t]
      (fun w ↦ deriv (fun u ↦ f (z, u)) w) := by
  have hpair : Tendsto (fun w : ℂ ↦ (z, w)) (nhds t) (nhds (z, t)) :=
    continuousAt_const.prodMk continuousAt_id
  filter_upwards [hpair.eventually hf.eventually_analyticAt] with w hw
  exact chapterVIFiberDerivative_eq_deriv hw

/-- The second derivative in the fiber coordinate, expressed as an iterated Fréchet partial
derivative. -/
noncomputable def chapterVISecondFiberDerivative (f : ℂ × ℂ → ℂ) (point : ℂ × ℂ) : ℂ :=
  chapterVIFiberDerivative (chapterVIFiberDerivative f) point

/-- The second fiber derivative of an analytic germ remains analytic. -/
theorem analyticAt_chapterVISecondFiberDerivative
    {f : ℂ × ℂ → ℂ} {point : ℂ × ℂ} (hf : AnalyticAt ℂ f point) :
    AnalyticAt ℂ (chapterVISecondFiberDerivative f) point :=
  analyticAt_chapterVIFiberDerivative (analyticAt_chapterVIFiberDerivative hf)

/-- The iterated Fréchet partial derivative agrees with the ordinary second derivative on a
fixed fiber. -/
theorem chapterVISecondFiberDerivative_eq_deriv_deriv
    {f : ℂ × ℂ → ℂ} {z t : ℂ} (hf : AnalyticAt ℂ f (z, t)) :
    chapterVISecondFiberDerivative f (z, t) =
      deriv (deriv (fun w ↦ f (z, w))) t := by
  unfold chapterVISecondFiberDerivative
  rw [chapterVIFiberDerivative_eq_deriv (analyticAt_chapterVIFiberDerivative hf)]
  exact (eventually_chapterVIFiberDerivative_eq_deriv hf).deriv_eq

/-- A complex continuous linear endomorphism is invertible as soon as its value at `1` is
nonzero. -/
theorem continuousLinearMap_isInvertible_of_apply_one_ne_zero
    (L : ℂ →L[ℂ] ℂ) (hL : L 1 ≠ 0) : L.IsInvertible := by
  let M : ℂ →L[ℂ] ℂ := (1 : ℂ →L[ℂ] ℂ).smulRight (L 1)
  let N : ℂ →L[ℂ] ℂ := (1 : ℂ →L[ℂ] ℂ).smulRight (L 1)⁻¹
  have hLM : L = M := by
    apply ContinuousLinearMap.ext
    intro x
    simpa [M, smul_eq_mul] using L.map_smul x (1 : ℂ)
  rw [hLM]
  apply ContinuousLinearMap.IsInvertible.of_inverse (g := N)
  · apply ContinuousLinearMap.ext
    intro x
    simp [M, N, ContinuousLinearMap.comp_apply, hL, smul_eq_mul]
  · apply ContinuousLinearMap.ext
    intro x
    simp [M, N, ContinuousLinearMap.comp_apply, hL, smul_eq_mul]

/-- A nonzero second fiber derivative is exactly the invertibility premise required by the
implicit function theorem for the fiber-critical equation. -/
theorem chapterVICriticalDerivative_isInvertible
    {f : ℂ × ℂ → ℂ} {z t : ℂ}
    (hf : AnalyticAt ℂ f (z, t))
    (hsecond : deriv (deriv (fun w ↦ f (z, w))) t ≠ 0) :
    (fderiv ℂ (chapterVIFiberDerivative f) (z, t) ∘L
      ContinuousLinearMap.inr ℂ ℂ ℂ).IsInvertible := by
  apply continuousLinearMap_isInvertible_of_apply_one_ne_zero
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]
  have hanalytic := analyticAt_chapterVIFiberDerivative hf
  change chapterVIFiberDerivative (chapterVIFiberDerivative f) (z, t) ≠ 0
  rw [chapterVIFiberDerivative_eq_deriv hanalytic]
  exact (eventually_chapterVIFiberDerivative_eq_deriv hf).deriv_eq ▸ hsecond

/-- An analytic double zero in the fiber variable has an analytic moving critical center.

The last conjunct states Poincaré's critical-point equation in ordinary one-variable derivative
notation, not only as a Fréchet partial derivative. -/
theorem exists_analytic_criticalCenter_of_fiber_double_zero
    {f : ℂ × ℂ → ℂ} {z t : ℂ}
    (hf : AnalyticAt ℂ f (z, t))
    (hfirst : deriv (fun w ↦ f (z, w)) t = 0)
    (hsecond : deriv (deriv (fun w ↦ f (z, w))) t ≠ 0) :
    ∃ center : ℂ → ℂ,
      center z = t ∧
      AnalyticAt ℂ center z ∧
      (∀ᶠ w in nhds z, chapterVIFiberDerivative f (w, center w) = 0) ∧
      (∀ᶠ w in nhds z, deriv (fun u ↦ f (w, u)) (center w) = 0) := by
  let critical : ℂ × ℂ → ℂ := chapterVIFiberDerivative f
  have hcriticalAnalytic : AnalyticAt ℂ critical (z, t) :=
    analyticAt_chapterVIFiberDerivative hf
  let cdf : ContDiffAt ℂ ω critical (z, t) := hcriticalAnalytic.contDiffAt
  have hinvertible :
      (fderiv ℂ critical (z, t) ∘L ContinuousLinearMap.inr ℂ ℂ ℂ).IsInvertible :=
    chapterVICriticalDerivative_isInvertible hf hsecond
  let center : ℂ → ℂ := cdf.implicitFunction (by simp) hinvertible
  have hcenterBase : center z = t := cdf.implicitFunction_apply_self (by simp) hinvertible
  have hcenterAnalytic : AnalyticAt ℂ center z :=
    (cdf.contDiffAt_implicitFunction (by simp) hinvertible).analyticAt
  have hcriticalBase : critical (z, t) = 0 := by
    rw [show critical (z, t) = deriv (fun w ↦ f (z, w)) t from
      chapterVIFiberDerivative_eq_deriv hf]
    exact hfirst
  have hcriticalZero : ∀ᶠ w in nhds z, critical (w, center w) = 0 := by
    filter_upwards [cdf.eventually_apply_implicitFunction (by simp) hinvertible] with w hw
    rw [hw, hcriticalBase]
  have hpairTendsto : Tendsto (fun w ↦ (w, center w)) (nhds z) (nhds (z, t)) := by
    have hpair := continuousAt_id.prodMk hcenterAnalytic.continuousAt
    rw [← hcenterBase]
    change ContinuousAt (fun w ↦ (w, center w)) z
    simpa only [id_eq] using hpair
  have hderivZero : ∀ᶠ w in nhds z, deriv (fun u ↦ f (w, u)) (center w) = 0 := by
    filter_upwards [hcriticalZero, hpairTendsto.eventually hf.eventually_analyticAt]
      with w hw hfw
    rw [← chapterVIFiberDerivative_eq_deriv hfw]
    exact hw
  exact ⟨center, hcenterBase, hcenterAnalytic, hcriticalZero, hderivZero⟩

/-! ## The concrete Chapter VI germ at D -/

/-- The exact convergent two-variable radicand at Poincaré's certified point D. -/
noncomputable def chapterVIDRadicand : ℂ × ℂ → ℂ :=
  chapterVIPoincareRadicand (-1) 3
    chapterVIDEccentricity chapterVIDComplement 0 1 2 2
    (chapterVIDX, chapterVIDY) chapterVIDX_ne_zero chapterVIDY_ne_zero
    chapterVID_firstKeplerCritical chapterVID_secondKeplerCritical (by norm_num)

/-- The first coordinate of D in Poincaré's literal `(z,t)` coordinates. -/
noncomputable def chapterVIDZBase : ℂ :=
  (chapterVIContourBase (-1) 3 chapterVIDEccentricity 0
    (chapterVIDX, chapterVIDY)).1

/-- The source radicand is genuinely analytic as a two-variable germ at D. -/
theorem analyticAt_chapterVIDRadicand :
    AnalyticAt ℂ chapterVIDRadicand (chapterVIDZBase, chapterVIDTBase) := by
  exact analyticAt_chapterVIPoincareRadicand (-1) 3
    chapterVIDEccentricity chapterVIDComplement 0 1 2 2
    (chapterVIDX, chapterVIDY) chapterVIDX_ne_zero chapterVIDY_ne_zero
    chapterVID_firstKeplerCritical chapterVID_secondKeplerCritical (by norm_num)
    chapterVIDTBase chapterVIDTBase_ne_zero chapterVIDTBase_pow

/-- Poincaré's exact radicand has an analytic moving critical center through D.

This closes the analytic-center step that precedes completing the square in §99.  It does not by
itself prove the later convergent Weierstrass factorization or the global admissible contour pinch.
-/
theorem exists_chapterVID_analyticCriticalCenter :
    ∃ center : ℂ → ℂ,
      center chapterVIDZBase = chapterVIDTBase ∧
      AnalyticAt ℂ center chapterVIDZBase ∧
      (∀ᶠ z in nhds chapterVIDZBase,
        chapterVIFiberDerivative chapterVIDRadicand (z, center z) = 0) ∧
      (∀ᶠ z in nhds chapterVIDZBase,
        deriv (fun t ↦ chapterVIDRadicand (z, t)) (center z) = 0) := by
  have hf := analyticAt_chapterVIDRadicand
  have hfiber : AnalyticAt ℂ
      (fun w ↦ chapterVIDRadicand (chapterVIDZBase, w)) chapterVIDTBase :=
    hf.comp (analyticAt_const.prod analyticAt_id)
  have horder : analyticOrderAt
      (fun w ↦ chapterVIDRadicand (chapterVIDZBase, w)) chapterVIDTBase = 2 := by
    exact analyticOrderAt_chapterVIDPoincareRadicand_eq_two
  have hjet := (analyticOrderAt_eq_two_iff hfiber).mp horder
  exact exists_analytic_criticalCenter_of_fiber_double_zero hf hjet.2.1 hjet.2.2

end PoincareChapterVI
