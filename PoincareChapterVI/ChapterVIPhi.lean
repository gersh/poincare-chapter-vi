/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.ChapterVIContour
import PoincareChapterVI.ChapterVIContourTransport

/-!
# Poincaré's one-variable function `Φ`

Section 94 defines

`Φ(z) = (2πi)⁻¹ ∮_{|t|=1} F(z,t) dt`

after the monomial substitution from the two mean anomalies.  This file records that definition
and verifies its finite Fourier-polynomial form.  The exponent of `t` is Poincaré's

`α = c m₁ - a m₂ + a d - b c - 1`.

Consequently the unit-circle integral kills every frequency except `α = -1`; under the usual
coprimality hypothesis those surviving frequencies are exactly the affine ray
`(m₁,m₂) = (a n+b,c n+d)`.  The value `root` below is the selected local `c`-th root of Poincaré's
parameter `z`; keeping it explicit prevents a hidden global branch choice.
-/

noncomputable section

open Complex
open scoped BigOperators Real

namespace PoincareChapterVI

/-- Poincaré's normalized unit-circle integral, before specifying the perturbing integrand. -/
def chapterVIPhi (integrand : ℂ → ℂ → ℂ) (z : ℂ) : ℂ :=
  (2 * Real.pi * Complex.I : ℂ)⁻¹ *
    ∮ t in C(0, 1), integrand z t

/-- The path-integral form of Poincaré's normalized contour construction.  Unlike
`chapterVIPhi`, this definition records the actual continued contour.  It is therefore the
form used in §§95--100, after the unit circle has been deformed on the chosen branch sheet. -/
def chapterVIPhiAlongPath
    {a b : ℂ} (integrand : ℂ → ℂ → ℂ) (z : ℂ) (path : Path a b) : ℂ :=
  (2 * Real.pi * Complex.I : ℂ)⁻¹ *
    ∫ᶜ t in path, chapterVIComplexScalarOneForm (integrand z) t

/-- A checked smooth deformation inside the holomorphic branch domain preserves Poincaré's
normalized contour function.  This is the precise formal replacement for the contour-moving
sentence at the start of §95; constructing the deformation for the physical collision cycle is
a separate source obligation. -/
theorem chapterVIPhiAlongPath_eq_of_smoothContourDeformation
    {a b : ℂ} {integrand : ℂ → ℂ → ℂ} {z : ℂ}
    {initial final : Path a b} {domain : Set ℂ}
    (deformation : ChapterVISmoothContourDeformation
      (chapterVIComplexScalarOneForm (integrand z)) initial final domain) :
    chapterVIPhiAlongPath integrand z initial =
      chapterVIPhiAlongPath integrand z final := by
  unfold chapterVIPhiAlongPath
  rw [deformation.curveIntegral_eq]

/-- Convenient unbundled version: holomorphicity of the scalar integrand and a checked `C²`
homotopy are enough to transport `Φ` between two contours. -/
theorem chapterVIPhiAlongPath_eq_of_holomorphic_homotopy
    {a b : ℂ} {integrand : ℂ → ℂ → ℂ} {z : ℂ}
    {initial final : Path a b} {domain : Set ℂ}
    (homotopy : Path.Homotopy initial final)
    (mapsInterior : ∀ s ∈ Set.Ioo (0 : unitInterval) 1,
      ∀ t ∈ Set.Ioo (0 : unitInterval) 1,
      homotopy (s, t) ∈ domain)
    (hf : DifferentiableOn ℂ (integrand z) domain)
    (hfClosure : ContinuousOn (integrand z) (closure domain))
    (hcontDiff : ContDiffOn ℝ 2
      (fun st : ℝ × ℝ ↦
        Set.IccExtend zero_le_one (homotopy.toHomotopy.extend st.1) st.2)
      (Set.Icc 0 1)) :
    chapterVIPhiAlongPath integrand z initial =
      chapterVIPhiAlongPath integrand z final := by
  unfold chapterVIPhiAlongPath
  rw [chapterVI_curveIntegral_eq_of_holomorphic_homotopy
    homotopy mapsInterior hf hfClosure hcontDiff]

/-- The exponent `α` of the auxiliary contour variable in §94. -/
def chapterVIPhiContourExponent
    (a c b d : ℤ) (frequency : ℤ × ℤ) : ℤ :=
  chapterVIShearExponent a c frequency + a * d - b * c - 1

/-- The finite transformed perturbing integrand in Poincaré's `(z,t)` coordinates.  `root` is a
chosen value of `z^(1/c)`, so all displayed powers remain integer Laurent powers. -/
def chapterVIFinitePhiIntegrand
    (coefficients : ChapterVIFiniteCoefficientTable)
    (a c b d : ℤ) (root t : ℂ) : ℂ :=
  coefficients.sum fun frequency coefficient ↦
    coefficient * root ^ (frequency.2 - d) *
      t ^ chapterVIPhiContourExponent a c b d frequency

/-- The finite version of Poincaré's `Φ`, defined by his normalized `t`-contour. -/
def chapterVIFinitePhi
    (coefficients : ChapterVIFiniteCoefficientTable)
    (a c b d : ℤ) (root : ℂ) : ℂ :=
  chapterVIPhi (fun _ t ↦
    chapterVIFinitePhiIntegrand coefficients a c b d root t) (root ^ c)

theorem chapterVIPhiContourExponent_eq_neg_one_iff
    (a c b d : ℤ) (frequency : ℤ × ℤ) :
    chapterVIPhiContourExponent a c b d frequency = -1 ↔
      chapterVIShearExponent a c frequency = c * b - a * d := by
  unfold chapterVIPhiContourExponent
  ring_nf
  omega

/-- The normalized unit-circle integral keeps precisely the shear level through `(b,d)`. -/
theorem chapterVIFinitePhi_eq_shearLevel
    (coefficients : ChapterVIFiniteCoefficientTable)
    (a c b d : ℤ) (root : ℂ) :
    chapterVIFinitePhi coefficients a c b d root =
      coefficients.sum fun frequency coefficient ↦
        if chapterVIShearExponent a c frequency = c * b - a * d then
          coefficient * root ^ (frequency.2 - d)
        else 0 := by
  classical
  have hnormalization : (2 * Real.pi * Complex.I : ℂ) ≠ 0 :=
    mul_ne_zero
      (mul_ne_zero (by norm_num) (ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
  have hintegral :
      (∮ t in C(0, 1),
        chapterVIFinitePhiIntegrand coefficients a c b d root t) =
      coefficients.sum fun frequency coefficient ↦
        if chapterVIShearExponent a c frequency = c * b - a * d then
          coefficient * root ^ (frequency.2 - d) *
            (2 * Real.pi * Complex.I)
        else 0 := by
    unfold chapterVIFinitePhiIntegrand
    simp only [Finsupp.sum]
    rw [circleIntegral.integral_fun_sum]
    · apply Finset.sum_congr rfl
      intro frequency hfrequency
      rw [circleIntegral.integral_const_mul,
        chapterVI_circleIntegral_zpow _ one_ne_zero]
      simp [chapterVIPhiContourExponent_eq_neg_one_iff]
    · intro frequency hfrequency
      simpa using circleIntegrable_chapterVIFiniteCoefficientMonomial
        (coefficients frequency * root ^ (frequency.2 - d))
        (chapterVIPhiContourExponent a c b d frequency) (-1) one_ne_zero
  unfold chapterVIFinitePhi chapterVIPhi
  rw [hintegral]
  rw [Finsupp.mul_sum]
  apply Finsupp.sum_congr
  intro frequency hfrequency
  split
  · field_simp
  · simp

/-- With Poincaré's coprimality hypothesis, the surviving contour terms are exactly the affine
frequency ray `(a n+b,c n+d)`. -/
theorem chapterVIFinitePhi_eq_affineRay
    (coefficients : ChapterVIFiniteCoefficientTable)
    {a c b d : ℤ} (root : ℂ)
    (ha : a ≠ 0) (hcoprime : Int.gcd a c = 1) :
    (chapterVIFinitePhi coefficients a c b d root =
      coefficients.sum fun frequency coefficient ↦
        if chapterVIShearExponent a c frequency = c * b - a * d then
          coefficient * root ^ (frequency.2 - d)
        else 0) ∧
      ∀ frequency : ℤ × ℤ,
        chapterVIShearExponent a c frequency = c * b - a * d ↔
          ∃ n : ℤ,
            frequency.1 = a * n + b ∧ frequency.2 = c * n + d := by
  exact ⟨chapterVIFinitePhi_eq_shearLevel coefficients a c b d root,
    fun frequency ↦ chapterVIShearExponent_eq_iff_mem_affineRay ha hcoprime⟩

/-- The finite Laurent polynomial on Poincaré's affine frequency ray. -/
def chapterVIFiniteAffineRayLaurentValue
    (coefficients : ChapterVIFiniteCoefficientTable)
    (a c b d : ℤ) (z : ℂ) : ℂ :=
  coefficients.sum fun frequency coefficient ↦
    if chapterVIShearExponent a c frequency = c * b - a * d then
      coefficient * z ^ ((frequency.2 - d) / c)
    else 0

/-- If `root` is the selected `c`-th root of `z`, Poincaré's finite contour function is exactly
the Laurent polynomial whose coefficients lie on `(a n+b,c n+d)`.  This is the displayed
identity `Φ(z)=∑ A_{m₁m₂} zⁿ` in §94, with every branch hypothesis explicit. -/
theorem chapterVIFinitePhi_eq_affineRayLaurentValue
    (coefficients : ChapterVIFiniteCoefficientTable)
    {a c b d : ℤ} {root z : ℂ}
    (ha : a ≠ 0) (hc : c ≠ 0) (hcoprime : Int.gcd a c = 1)
    (hroot : root ^ c = z) :
    chapterVIFinitePhi coefficients a c b d root =
      chapterVIFiniteAffineRayLaurentValue coefficients a c b d z := by
  classical
  rw [chapterVIFinitePhi_eq_shearLevel]
  unfold chapterVIFiniteAffineRayLaurentValue
  apply Finsupp.sum_congr
  intro frequency hfrequency
  by_cases hshear :
      chapterVIShearExponent a c frequency = c * b - a * d
  · rw [if_pos hshear, if_pos hshear]
    obtain ⟨n, hfirst, hsecond⟩ :=
      (chapterVIShearExponent_eq_iff_mem_affineRay ha hcoprime).mp hshear
    have hexponent : frequency.2 - d = c * n := by
      rw [hsecond]
      ring
    have hquotient : (frequency.2 - d) / c = n := by
      rw [hexponent]
      exact Int.mul_ediv_cancel_left n hc
    rw [hquotient, hexponent, zpow_mul, hroot]
  · rw [if_neg hshear, if_neg hshear]

end PoincareChapterVI
