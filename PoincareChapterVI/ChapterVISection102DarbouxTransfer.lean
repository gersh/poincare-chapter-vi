/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.ChapterVIDarbouxTransfer
import PoincareChapterVI.ChapterVISection102

/-!
# Source-facing Darboux transfer for Chapter VI, §§100--102

This file makes the common Darboux normalization radius explicit.  Boundary singularities at
radius `R` contribute unit-circle bases `R z₀⁻¹`; treating those bases as literally `z₀⁻¹` would
silently assume `R = 1`.

The final structure records a finite logarithmic decomposition of the coefficient function and
an analytic remainder on a strictly larger disk.  It is converted, rather than postulated, into
the finite-spectrum asymptotic consumed by the formalized §102--103 contradiction.
-/

noncomputable section

namespace PoincareChapterVI.ChapterVISection102

open AffineIntersectionCount
open MovingAlgebraicBranches
open Filter
open scoped NNReal

private abbrev Orientation := Fin 3 → ℂ
private abbrev Essential := Fin 2 → ℂ
private abbrev FiniteSingularPoint :=
  { point : Fin 2 → ℂ // point ∈ finiteIntersectionPoints }

/-- Equal-modulus §102 data with the common normalization radius made explicit.  The radius is a
function of the two essential coordinates, so it is constant along a direction in their kernel. -/
structure TwoCoordinateScaledUnitSpectrumFactorization (spectrumSize : ℕ)
    (essentialCoordinates : Orientation →L[ℂ] Essential) where
  baseEssential : Essential
  normalizationRadius : FiniteSingularPoint → Essential → ℝ≥0
  normalizationRadius_ne_zero : ∀ point essential,
    normalizationRadius point essential ≠ 0
  normalizedCoefficient : FiniteSingularPoint → Essential → ℕ → ℂ
  spectrumBase : FiniteSingularPoint → Orientation → ℂ → Fin spectrumSize → ℂ
  spectrumWeight : FiniteSingularPoint → Orientation → ℂ → Fin spectrumSize → ℂ
  distinguished : FiniteSingularPoint → Fin spectrumSize
  distinguished_eq : ∀ point rotation γ,
    spectrumBase point rotation γ (distinguished point) =
      (normalizationRadius point
        (baseEssential + γ • essentialCoordinates rotation) : ℂ) *
        (branchSingularityValue rotation point γ)⁻¹
  eventually_base_injective : ∀ point rotation, ∀ᶠ γ in nhds 0,
    Function.Injective (spectrumBase point rotation γ)
  eventually_base_unit : ∀ point rotation, ∀ᶠ γ in nhds 0,
    ∀ i, ‖spectrumBase point rotation γ i‖ = 1
  eventually_weight_ne_zero : ∀ point rotation, ∀ᶠ γ in nhds 0,
    ∀ i, spectrumWeight point rotation γ i ≠ 0
  eventually_asymptotic : ∀ point rotation, ∀ᶠ γ in nhds 0,
    Tendsto
      (normalizedCoefficient point
          (baseEssential + γ • essentialCoordinates rotation) -
        PoincareChapterVI.chapterVIFiniteExponentialMoment
          (spectrumBase point rotation γ) (spectrumWeight point rotation γ))
      atTop (nhds 0)

/-- The normalized finite spectrum is fixed along a direction invisible to the essential
coordinates. -/
theorem TwoCoordinateScaledUnitSpectrumFactorization.eventually_spectrumRange_eq
    (spectrumSize : ℕ) (essentialCoordinates : Orientation →L[ℂ] Essential)
    (factorization :
      TwoCoordinateScaledUnitSpectrumFactorization spectrumSize essentialCoordinates)
    (rotation : Orientation) (hrotation : essentialCoordinates rotation = 0)
    (point : FiniteSingularPoint) :
    ∀ᶠ γ in nhds 0,
      Set.range (factorization.spectrumBase point rotation γ) =
        Set.range (factorization.spectrumBase point rotation 0) := by
  have hbaseZero :=
    (factorization.eventually_base_injective point rotation).self_of_nhds
  have hunitZero :=
    (factorization.eventually_base_unit point rotation).self_of_nhds
  have hweightZero :=
    (factorization.eventually_weight_ne_zero point rotation).self_of_nhds
  have hasymptoticZero :=
    (factorization.eventually_asymptotic point rotation).self_of_nhds
  filter_upwards [factorization.eventually_base_injective point rotation,
    factorization.eventually_base_unit point rotation,
    factorization.eventually_weight_ne_zero point rotation,
    factorization.eventually_asymptotic point rotation] with
      γ hbase hunit hweight hasymptotic
  apply PoincareChapterVI.spectra_eq_of_commonCoefficient_tendsto_finiteExponentialMoments
    hbase hbaseZero hunit hunitZero hweight hweightZero
  · simpa [hrotation] using hasymptotic
  · simpa using hasymptoticZero

/-- Finite-spectrum recovery fixes the scaled distinguished branch.  Because the normalizing
radius depends only on the essential coordinates, its nonzero factor cancels and the actual
singularity branch is locally constant. -/
theorem TwoCoordinateScaledUnitSpectrumFactorization.eventually_branchSingularityValue_eq
    (spectrumSize : ℕ) (essentialCoordinates : Orientation →L[ℂ] Essential)
    (factorization :
      TwoCoordinateScaledUnitSpectrumFactorization spectrumSize essentialCoordinates)
    (rotation : Orientation) (hrotation : essentialCoordinates rotation = 0)
    (point : FiniteSingularPoint) :
    (fun γ ↦ branchSingularityValue rotation point γ) =ᶠ[nhds 0]
      fun _ ↦ branchSingularityValue rotation point 0 := by
  let distinguished := factorization.distinguished point
  let baseAtZero := factorization.spectrumBase point rotation 0
  let radius := factorization.normalizationRadius point factorization.baseEssential
  have hbaseZero : Function.Injective baseAtZero :=
    (factorization.eventually_base_injective point rotation).self_of_nhds
  have hsingularityZero :=
    (eventually_branchSingularityValue_ne_zero rotation point).self_of_nhds
  have hvalue : Tendsto (branchSingularityValue rotation point) (nhds 0)
      (nhds (branchSingularityValue rotation point 0)) :=
    (hasDerivAt_branchSingularityValue rotation point).continuousAt.tendsto
  have hinverse : Tendsto
      (fun γ ↦ (branchSingularityValue rotation point γ)⁻¹) (nhds 0)
      (nhds (branchSingularityValue rotation point 0)⁻¹) :=
    hvalue.inv₀ hsingularityZero
  have hdistinguished : Tendsto
      (fun γ ↦ factorization.spectrumBase point rotation γ distinguished) (nhds 0)
      (nhds (baseAtZero distinguished)) := by
    have hscaled := hinverse.const_mul (radius : ℂ)
    convert hscaled using 1
    · funext γ
      rw [factorization.distinguished_eq]
      simp [radius, hrotation]
    · change nhds (factorization.spectrumBase point rotation 0
          (factorization.distinguished point)) =
        nhds ((radius : ℂ) * (branchSingularityValue rotation point 0)⁻¹)
      rw [factorization.distinguished_eq]
      simp [radius, hrotation]
  have hrange := factorization.eventually_spectrumRange_eq
    spectrumSize essentialCoordinates rotation hrotation point
  have hmem : ∀ᶠ γ in nhds 0,
      factorization.spectrumBase point rotation γ distinguished ∈ Set.range baseAtZero := by
    filter_upwards [hrange] with γ hγ
    rw [← hγ]
    exact ⟨distinguished, rfl⟩
  have hlabel := PoincareChapterVI.eventually_eq_of_tendsto_of_eventually_mem_finiteSpectrum
    hbaseZero distinguished hdistinguished hmem
  have hradius : (radius : ℂ) ≠ 0 := by
    exact_mod_cast factorization.normalizationRadius_ne_zero point factorization.baseEssential
  filter_upwards [hlabel] with γ hγ
  apply inv_injective
  apply mul_left_cancel₀ hradius
  calc
    (radius : ℂ) * (branchSingularityValue rotation point γ)⁻¹ =
        factorization.spectrumBase point rotation γ distinguished := by
      rw [factorization.distinguished_eq]
      simp [radius, hrotation]
    _ = baseAtZero distinguished := hγ
    _ = (radius : ℂ) * (branchSingularityValue rotation point 0)⁻¹ := by
      change factorization.spectrumBase point rotation 0
          (factorization.distinguished point) = _
      rw [factorization.distinguished_eq]
      simp [radius, hrotation]

/-- Package scaled finite-spectrum recovery as the local constancy input consumed by §103. -/
theorem TwoCoordinateScaledUnitSpectrumFactorization.branchConstancy_of_mem_ker
    (spectrumSize : ℕ) (essentialCoordinates : Orientation →L[ℂ] Essential)
    (factorization :
      TwoCoordinateScaledUnitSpectrumFactorization spectrumSize essentialCoordinates)
    (rotation : Orientation) (hrotation : essentialCoordinates rotation = 0) :
    BranchSingularityConstancy rotation where
  eventually_constant := by
    intro point hpoint
    let indexedPoint : FiniteSingularPoint := ⟨point, hpoint⟩
    have hconstant := factorization.eventually_branchSingularityValue_eq
      spectrumSize essentialCoordinates rotation hrotation indexedPoint
    simpa [branchSingularityValue, indexedPoint, movingLocalSystem] using hconstant

/-- The correctly scaled equal-modulus Darboux data contradict the compiled §103 calculation. -/
theorem not_twoCoordinateScaledUnitSpectrumFactorization
    (spectrumSize : ℕ) (essentialCoordinates : Orientation →L[ℂ] Essential)
    (factorization :
      TwoCoordinateScaledUnitSpectrumFactorization spectrumSize essentialCoordinates) : False := by
  apply MovingAlgebraicBranches.not_twoParameter_movingAlgebraicFamily essentialCoordinates
  intro rotation hrotation
  exact factorization.branchConstancy_of_mem_ker
    spectrumSize essentialCoordinates rotation hrotation

/-- Source-facing coefficient data: a finite sum of logarithmic boundary singularities plus a
remainder analytic on a strictly larger disk. -/
structure TwoCoordinateFiniteLogarithmicFactorization (spectrumSize : ℕ)
    (essentialCoordinates : Orientation →L[ℂ] Essential) where
  baseEssential : Essential
  coefficientFunction : FiniteSingularPoint → Essential → ℂ → ℂ
  /-- Full Taylor coefficients, including degree zero.  Darboux normalization below uses degree
  `n + 1`. -/
  coefficient : FiniteSingularPoint → Essential → ℕ → ℂ
  normalizationRadius : FiniteSingularPoint → Essential → ℝ≥0
  normalizationRadius_ne_zero : ∀ point essential,
    normalizationRadius point essential ≠ 0
  analyticRadius : FiniteSingularPoint → Orientation → ℂ → ℝ≥0
  singularityInverse : FiniteSingularPoint → Orientation → ℂ → Fin spectrumSize → ℂ
  amplitude : FiniteSingularPoint → Orientation → ℂ → Fin spectrumSize → ℂ
  remainderCoefficient : FiniteSingularPoint → Orientation → ℂ → ℕ → ℂ
  remainder : FiniteSingularPoint → Orientation → ℂ → ℂ → ℂ
  distinguished : FiniteSingularPoint → Fin spectrumSize
  distinguished_eq : ∀ point rotation γ,
    singularityInverse point rotation γ (distinguished point) =
      (branchSingularityValue rotation point γ)⁻¹
  eventually_coefficient_hasFPowerSeries : ∀ point rotation, ∀ᶠ (γ : ℂ) in nhds 0,
    HasFPowerSeriesAt
      (coefficientFunction point
        (baseEssential + γ • essentialCoordinates rotation))
      (FormalMultilinearSeries.ofScalars ℂ
        (coefficient point
          (baseEssential + γ • essentialCoordinates rotation))) 0
  eventually_function_decomposition : ∀ point rotation, ∀ᶠ (γ : ℂ) in nhds 0,
    coefficientFunction point
        (baseEssential + γ • essentialCoordinates rotation) =ᶠ[nhds 0]
      fun z ↦
        (∑ j, amplitude point rotation γ j *
          Complex.log (1 - z * singularityInverse point rotation γ j)) +
          remainder point rotation γ z
  eventually_radius_lt_analyticRadius : ∀ point rotation, ∀ᶠ γ in nhds 0,
    normalizationRadius point
      (baseEssential + γ • essentialCoordinates rotation) <
        analyticRadius point rotation γ
  eventually_remainder_analytic : ∀ point rotation, ∀ᶠ γ in nhds 0,
    HasFPowerSeriesOnBall (remainder point rotation γ)
      (FormalMultilinearSeries.ofScalars ℂ (remainderCoefficient point rotation γ)) 0
      (analyticRadius point rotation γ)
  eventually_singularityInverse_injective : ∀ point rotation, ∀ᶠ γ in nhds 0,
    Function.Injective (singularityInverse point rotation γ)
  eventually_common_norm : ∀ point rotation, ∀ᶠ γ in nhds 0,
    ∀ i, ‖singularityInverse point rotation γ i‖ =
      (normalizationRadius point
        (baseEssential + γ • essentialCoordinates rotation) : ℝ)⁻¹
  eventually_amplitude_ne_zero : ∀ point rotation, ∀ᶠ γ in nhds 0,
    ∀ i, amplitude point rotation γ i ≠ 0

/-- A genuine finite-logarithm decomposition with a larger-disk analytic remainder supplies the
scaled unit-spectrum interface; the `o(1)` asymptotic is proved by coefficient estimates rather
than retained as a hypothesis. -/
def TwoCoordinateFiniteLogarithmicFactorization.toScaledUnitSpectrumFactorization
    (spectrumSize : ℕ) (essentialCoordinates : Orientation →L[ℂ] Essential)
    (factorization :
      TwoCoordinateFiniteLogarithmicFactorization spectrumSize essentialCoordinates) :
    TwoCoordinateScaledUnitSpectrumFactorization spectrumSize essentialCoordinates where
  baseEssential := factorization.baseEssential
  normalizationRadius := factorization.normalizationRadius
  normalizationRadius_ne_zero := factorization.normalizationRadius_ne_zero
  normalizedCoefficient point essential :=
    PoincareChapterVI.chapterVINormalizedCoefficient
      (factorization.normalizationRadius point essential)
      (fun n ↦ factorization.coefficient point essential (n + 1))
  spectrumBase point rotation γ i :=
    PoincareChapterVI.chapterVIUnitBase
      (factorization.normalizationRadius point
        (factorization.baseEssential + γ • essentialCoordinates rotation))
      (factorization.singularityInverse point rotation γ i)
  spectrumWeight point rotation γ i :=
    PoincareChapterVI.chapterVILogSpectrumWeight
      (factorization.normalizationRadius point
        (factorization.baseEssential + γ • essentialCoordinates rotation))
      (factorization.singularityInverse point rotation γ i)
      (factorization.amplitude point rotation γ i)
  distinguished := factorization.distinguished
  distinguished_eq := by
    intro point rotation γ
    rw [factorization.distinguished_eq]
    rfl
  eventually_base_injective := by
    intro point rotation
    filter_upwards [factorization.eventually_singularityInverse_injective point rotation] with
      γ hinjective
    intro i j hij
    apply hinjective
    apply mul_left_cancel₀
      (show (factorization.normalizationRadius point
        (factorization.baseEssential + γ • essentialCoordinates rotation) : ℂ) ≠ 0 by
          exact_mod_cast factorization.normalizationRadius_ne_zero point
            (factorization.baseEssential + γ • essentialCoordinates rotation))
    exact hij
  eventually_base_unit := by
    intro point rotation
    filter_upwards [factorization.eventually_common_norm point rotation] with γ hnorm
    intro i
    exact PoincareChapterVI.norm_chapterVIUnitBase_eq_one
      (factorization.normalizationRadius_ne_zero point
        (factorization.baseEssential + γ • essentialCoordinates rotation)) (hnorm i)
  eventually_weight_ne_zero := by
    intro point rotation
    filter_upwards [factorization.eventually_common_norm point rotation,
      factorization.eventually_amplitude_ne_zero point rotation] with γ hnorm hamplitude
    intro i
    unfold PoincareChapterVI.chapterVILogSpectrumWeight
    apply mul_ne_zero (neg_ne_zero.mpr (hamplitude i))
    have hbaseNorm := PoincareChapterVI.norm_chapterVIUnitBase_eq_one
      (factorization.normalizationRadius_ne_zero point
        (factorization.baseEssential + γ • essentialCoordinates rotation)) (hnorm i)
    intro hbase
    rw [hbase, norm_zero] at hbaseNorm
    exact zero_ne_one hbaseNorm
  eventually_asymptotic := by
    intro point rotation
    filter_upwards [factorization.eventually_radius_lt_analyticRadius point rotation,
      factorization.eventually_remainder_analytic point rotation,
      factorization.eventually_coefficient_hasFPowerSeries point rotation,
      factorization.eventually_function_decomposition point rotation] with
        γ hradii hremainder hcoefficientSeries hfunctionDecomposition
    let radius := factorization.normalizationRadius point
      (factorization.baseEssential + γ • essentialCoordinates rotation)
    have hcoefficient : (fun n ↦ factorization.coefficient point
        (factorization.baseEssential + γ • essentialCoordinates rotation) (n + 1)) =
        fun n ↦
          (∑ j, factorization.amplitude point rotation γ j *
            PoincareChapterVI.chapterVILogSingularityCoefficient
              (factorization.singularityInverse point rotation γ j) n) +
            factorization.remainderCoefficient point rotation γ (n + 1) := by
      funext n
      have h := PoincareChapterVI.coefficient_eq_finiteLogs_add_analyticRemainder
        (factorization.singularityInverse point rotation γ)
        (factorization.amplitude point rotation γ) hcoefficientSeries
        hremainder.hasFPowerSeriesAt hfunctionDecomposition (n + 1)
      simpa using h
    rw [hcoefficient]
    exact PoincareChapterVI.tendsto_chapterVINormalizedCoefficient_sub_finiteLogSpectrum
      (factorization.normalizationRadius_ne_zero point
        (factorization.baseEssential + γ • essentialCoordinates rotation))
      hradii (factorization.singularityInverse point rotation γ)
      (factorization.amplitude point rotation γ)
      (factorization.remainderCoefficient point rotation γ)
      (factorization.remainder point rotation γ) hremainder

/-- Poincaré's desired finite logarithmic coefficient decomposition, with its analytic remainder
and two-coordinate dependence made explicit, is already incompatible with the formalized §103
calculation. -/
theorem not_twoCoordinateFiniteLogarithmicFactorization
    (spectrumSize : ℕ) (essentialCoordinates : Orientation →L[ℂ] Essential)
    (factorization :
      TwoCoordinateFiniteLogarithmicFactorization spectrumSize essentialCoordinates) : False :=
  not_twoCoordinateScaledUnitSpectrumFactorization spectrumSize essentialCoordinates
    (factorization.toScaledUnitSpectrumFactorization spectrumSize essentialCoordinates)

/-- A more faithful finite Darboux jet interface for Poincaré's
`Φ₂(z) + Φ₃(z) log (z-z₀)`: each analytic logarithmic amplitude is represented by a finite jet in
powers of its vanishing factor.  Positive-order jet terms are no longer required to be absorbed
into the larger-disk analytic remainder. -/
structure TwoCoordinateFiniteLogAmplitudeJetFactorization
    (spectrumSize jetOrder : ℕ)
    (essentialCoordinates : Orientation →L[ℂ] Essential) where
  baseEssential : Essential
  coefficient : FiniteSingularPoint → Essential → ℕ → ℂ
  normalizationRadius : FiniteSingularPoint → Essential → ℝ≥0
  normalizationRadius_ne_zero : ∀ point essential,
    normalizationRadius point essential ≠ 0
  analyticRadius : FiniteSingularPoint → Orientation → ℂ → ℝ≥0
  singularityInverse : FiniteSingularPoint → Orientation → ℂ → Fin spectrumSize → ℂ
  amplitudeJet : FiniteSingularPoint → Orientation → ℂ →
    Fin spectrumSize → Fin (jetOrder + 1) → ℂ
  remainderCoefficient : FiniteSingularPoint → Orientation → ℂ → ℕ → ℂ
  remainder : FiniteSingularPoint → Orientation → ℂ → ℂ → ℂ
  distinguished : FiniteSingularPoint → Fin spectrumSize
  distinguished_eq : ∀ point rotation γ,
    singularityInverse point rotation γ (distinguished point) =
      (branchSingularityValue rotation point γ)⁻¹
  coefficient_decomposition : ∀ point rotation γ n,
    coefficient point (baseEssential + γ • essentialCoordinates rotation) n =
      PoincareChapterVI.chapterVIFiniteLogAmplitudeJetCoefficient
        (singularityInverse point rotation γ) (amplitudeJet point rotation γ) n +
        remainderCoefficient point rotation γ (n + 1)
  eventually_radius_lt_analyticRadius : ∀ point rotation, ∀ᶠ γ in nhds 0,
    normalizationRadius point
      (baseEssential + γ • essentialCoordinates rotation) <
        analyticRadius point rotation γ
  eventually_remainder_analytic : ∀ point rotation, ∀ᶠ γ in nhds 0,
    HasFPowerSeriesOnBall (remainder point rotation γ)
      (FormalMultilinearSeries.ofScalars ℂ (remainderCoefficient point rotation γ)) 0
      (analyticRadius point rotation γ)
  eventually_singularityInverse_injective : ∀ point rotation, ∀ᶠ γ in nhds 0,
    Function.Injective (singularityInverse point rotation γ)
  eventually_common_norm : ∀ point rotation, ∀ᶠ γ in nhds 0,
    ∀ i, ‖singularityInverse point rotation γ i‖ =
      (normalizationRadius point
        (baseEssential + γ • essentialCoordinates rotation) : ℝ)⁻¹
  eventually_leadingAmplitude_ne_zero : ∀ point rotation, ∀ᶠ γ in nhds 0,
    ∀ i, amplitudeJet point rotation γ i 0 ≠ 0

/-- Finite analytic amplitude jets plus a larger-disk analytic remainder produce the correctly
scaled unit spectrum.  The positive-order logarithmic terms are discharged by the finite-jet
Darboux theorem. -/
def TwoCoordinateFiniteLogAmplitudeJetFactorization.toScaledUnitSpectrumFactorization
    (spectrumSize jetOrder : ℕ)
    (essentialCoordinates : Orientation →L[ℂ] Essential)
    (factorization : TwoCoordinateFiniteLogAmplitudeJetFactorization
      spectrumSize jetOrder essentialCoordinates) :
    TwoCoordinateScaledUnitSpectrumFactorization spectrumSize essentialCoordinates where
  baseEssential := factorization.baseEssential
  normalizationRadius := factorization.normalizationRadius
  normalizationRadius_ne_zero := factorization.normalizationRadius_ne_zero
  normalizedCoefficient point essential :=
    PoincareChapterVI.chapterVINormalizedCoefficient
      (factorization.normalizationRadius point essential)
      (factorization.coefficient point essential)
  spectrumBase point rotation γ i :=
    PoincareChapterVI.chapterVIUnitBase
      (factorization.normalizationRadius point
        (factorization.baseEssential + γ • essentialCoordinates rotation))
      (factorization.singularityInverse point rotation γ i)
  spectrumWeight point rotation γ i :=
    PoincareChapterVI.chapterVILogSpectrumWeight
      (factorization.normalizationRadius point
        (factorization.baseEssential + γ • essentialCoordinates rotation))
      (factorization.singularityInverse point rotation γ i)
      (factorization.amplitudeJet point rotation γ i 0)
  distinguished := factorization.distinguished
  distinguished_eq := by
    intro point rotation γ
    rw [factorization.distinguished_eq]
    rfl
  eventually_base_injective := by
    intro point rotation
    filter_upwards [factorization.eventually_singularityInverse_injective point rotation] with
      γ hinjective
    intro i j hij
    apply hinjective
    apply mul_left_cancel₀
      (show (factorization.normalizationRadius point
        (factorization.baseEssential + γ • essentialCoordinates rotation) : ℂ) ≠ 0 by
          exact_mod_cast factorization.normalizationRadius_ne_zero point
            (factorization.baseEssential + γ • essentialCoordinates rotation))
    exact hij
  eventually_base_unit := by
    intro point rotation
    filter_upwards [factorization.eventually_common_norm point rotation] with γ hnorm
    intro i
    exact PoincareChapterVI.norm_chapterVIUnitBase_eq_one
      (factorization.normalizationRadius_ne_zero point
        (factorization.baseEssential + γ • essentialCoordinates rotation)) (hnorm i)
  eventually_weight_ne_zero := by
    intro point rotation
    filter_upwards [factorization.eventually_common_norm point rotation,
      factorization.eventually_leadingAmplitude_ne_zero point rotation] with
        γ hnorm hamplitude
    intro i
    unfold PoincareChapterVI.chapterVILogSpectrumWeight
    apply mul_ne_zero (neg_ne_zero.mpr (hamplitude i))
    have hbaseNorm := PoincareChapterVI.norm_chapterVIUnitBase_eq_one
      (factorization.normalizationRadius_ne_zero point
        (factorization.baseEssential + γ • essentialCoordinates rotation)) (hnorm i)
    intro hbase
    rw [hbase, norm_zero] at hbaseNorm
    exact zero_ne_one hbaseNorm
  eventually_asymptotic := by
    intro point rotation
    filter_upwards [factorization.eventually_radius_lt_analyticRadius point rotation,
      factorization.eventually_remainder_analytic point rotation,
      factorization.eventually_common_norm point rotation] with
        γ hradii hremainder hnorm
    let radius := factorization.normalizationRadius point
      (factorization.baseEssential + γ • essentialCoordinates rotation)
    have hunit : ∀ i, ‖PoincareChapterVI.chapterVIUnitBase radius
        (factorization.singularityInverse point rotation γ i)‖ = 1 := by
      intro i
      exact PoincareChapterVI.norm_chapterVIUnitBase_eq_one
        (factorization.normalizationRadius_ne_zero point
          (factorization.baseEssential + γ • essentialCoordinates rotation)) (hnorm i)
    have hjet :=
      PoincareChapterVI.tendsto_chapterVINormalizedCoefficient_sub_finiteLogAmplitudeJetSpectrum
        (factorization.normalizationRadius_ne_zero point
          (factorization.baseEssential + γ • essentialCoordinates rotation))
        (factorization.singularityInverse point rotation γ)
        (factorization.amplitudeJet point rotation γ) hunit
    have hanalytic := PoincareChapterVI.tendsto_chapterVINormalizedCoefficient_analyticRemainder
      hradii hremainder
    have htotal := hjet.add hanalytic
    convert htotal using 1
    · funext index
      have hdecomposition := factorization.coefficient_decomposition point rotation γ index
      unfold PoincareChapterVI.chapterVINormalizedCoefficient at hdecomposition ⊢
      simp only [Pi.sub_apply]
      rw [hdecomposition]
      ring
    · simp

/-- No two-coordinate family with the stated finite logarithmic amplitude jets and analytic
remainder can exist for the concrete 24-branch family. -/
theorem not_twoCoordinateFiniteLogAmplitudeJetFactorization
    (spectrumSize jetOrder : ℕ)
    (essentialCoordinates : Orientation →L[ℂ] Essential)
    (factorization : TwoCoordinateFiniteLogAmplitudeJetFactorization
      spectrumSize jetOrder essentialCoordinates) : False :=
  not_twoCoordinateScaledUnitSpectrumFactorization spectrumSize essentialCoordinates
    (factorization.toScaledUnitSpectrumFactorization
      spectrumSize jetOrder essentialCoordinates)

/-- The full, nonpolynomial analogue of `TwoCoordinateFiniteLogAmplitudeJetFactorization`.
Each logarithmic amplitude is an infinite series in its local vanishing factor.  The explicit
Tannery data records the uniform summable estimate needed to exchange the amplitude sum with the
large-coefficient limit; deriving that estimate from a concrete analytic germ remains a separate
analytic theorem. -/
structure TwoCoordinateAnalyticLogAmplitudeFactorization
    (spectrumSize : ℕ)
    (essentialCoordinates : Orientation →L[ℂ] Essential) where
  baseEssential : Essential
  coefficient : FiniteSingularPoint → Essential → ℕ → ℂ
  normalizationRadius : FiniteSingularPoint → Essential → ℝ≥0
  normalizationRadius_ne_zero : ∀ point essential,
    normalizationRadius point essential ≠ 0
  analyticRadius : FiniteSingularPoint → Orientation → ℂ → ℝ≥0
  singularityInverse : FiniteSingularPoint → Orientation → ℂ → Fin spectrumSize → ℂ
  amplitudeJet : FiniteSingularPoint → Orientation → ℂ → Fin spectrumSize → ℕ → ℂ
  tailBound : FiniteSingularPoint → Orientation → ℂ → Fin spectrumSize → ℕ → ℝ
  remainderCoefficient : FiniteSingularPoint → Orientation → ℂ → ℕ → ℂ
  remainder : FiniteSingularPoint → Orientation → ℂ → ℂ → ℂ
  distinguished : FiniteSingularPoint → Fin spectrumSize
  distinguished_eq : ∀ point rotation γ,
    singularityInverse point rotation γ (distinguished point) =
      (branchSingularityValue rotation point γ)⁻¹
  coefficient_decomposition : ∀ point rotation γ n,
    coefficient point (baseEssential + γ • essentialCoordinates rotation) n =
      PoincareChapterVI.chapterVIFiniteLogAnalyticAmplitudeCoefficient
        (singularityInverse point rotation γ) (amplitudeJet point rotation γ) n +
        remainderCoefficient point rotation γ (n + 1)
  eventually_radius_lt_analyticRadius : ∀ point rotation, ∀ᶠ γ in nhds 0,
    normalizationRadius point
      (baseEssential + γ • essentialCoordinates rotation) <
        analyticRadius point rotation γ
  eventually_remainder_analytic : ∀ point rotation, ∀ᶠ γ in nhds 0,
    HasFPowerSeriesOnBall (remainder point rotation γ)
      (FormalMultilinearSeries.ofScalars ℂ (remainderCoefficient point rotation γ)) 0
      (analyticRadius point rotation γ)
  eventually_singularityInverse_injective : ∀ point rotation, ∀ᶠ γ in nhds 0,
    Function.Injective (singularityInverse point rotation γ)
  eventually_common_norm : ∀ point rotation, ∀ᶠ γ in nhds 0,
    ∀ i, ‖singularityInverse point rotation γ i‖ =
      (normalizationRadius point
        (baseEssential + γ • essentialCoordinates rotation) : ℝ)⁻¹
  eventually_leadingAmplitude_ne_zero : ∀ point rotation, ∀ᶠ γ in nhds 0,
    ∀ i, amplitudeJet point rotation γ i 0 ≠ 0
  eventually_tail_control : ∀ point rotation, ∀ᶠ γ in nhds 0,
    (∀ j index, Summable fun order : ℕ ↦
      amplitudeJet point rotation γ j (order + 1) *
        PoincareChapterVI.chapterVIHigherVanishingLogCoefficient
          (singularityInverse point rotation γ j) (order + 1) index) ∧
    (∀ j, Summable (tailBound point rotation γ j)) ∧
    (∀ j, ∀ᶠ index : ℕ in atTop, ∀ order : ℕ,
      ‖PoincareChapterVI.chapterVINormalizedCoefficient
        (normalizationRadius point
          (baseEssential + γ • essentialCoordinates rotation))
        (fun n ↦ amplitudeJet point rotation γ j (order + 1) *
          PoincareChapterVI.chapterVIHigherVanishingLogCoefficient
            (singularityInverse point rotation γ j) (order + 1) n) index‖ ≤
        tailBound point rotation γ j order)

/-- Infinite analytic amplitude series satisfying the explicit Tannery estimate produce the
same scaled unit spectrum as their values at the logarithmic singularities. -/
def TwoCoordinateAnalyticLogAmplitudeFactorization.toScaledUnitSpectrumFactorization
    (spectrumSize : ℕ)
    (essentialCoordinates : Orientation →L[ℂ] Essential)
    (factorization : TwoCoordinateAnalyticLogAmplitudeFactorization
      spectrumSize essentialCoordinates) :
    TwoCoordinateScaledUnitSpectrumFactorization spectrumSize essentialCoordinates where
  baseEssential := factorization.baseEssential
  normalizationRadius := factorization.normalizationRadius
  normalizationRadius_ne_zero := factorization.normalizationRadius_ne_zero
  normalizedCoefficient point essential :=
    PoincareChapterVI.chapterVINormalizedCoefficient
      (factorization.normalizationRadius point essential)
      (factorization.coefficient point essential)
  spectrumBase point rotation γ i :=
    PoincareChapterVI.chapterVIUnitBase
      (factorization.normalizationRadius point
        (factorization.baseEssential + γ • essentialCoordinates rotation))
      (factorization.singularityInverse point rotation γ i)
  spectrumWeight point rotation γ i :=
    PoincareChapterVI.chapterVILogSpectrumWeight
      (factorization.normalizationRadius point
        (factorization.baseEssential + γ • essentialCoordinates rotation))
      (factorization.singularityInverse point rotation γ i)
      (factorization.amplitudeJet point rotation γ i 0)
  distinguished := factorization.distinguished
  distinguished_eq := by
    intro point rotation γ
    rw [factorization.distinguished_eq]
    rfl
  eventually_base_injective := by
    intro point rotation
    filter_upwards [factorization.eventually_singularityInverse_injective point rotation] with
      γ hinjective
    intro i j hij
    apply hinjective
    apply mul_left_cancel₀
      (show (factorization.normalizationRadius point
        (factorization.baseEssential + γ • essentialCoordinates rotation) : ℂ) ≠ 0 by
          exact_mod_cast factorization.normalizationRadius_ne_zero point
            (factorization.baseEssential + γ • essentialCoordinates rotation))
    exact hij
  eventually_base_unit := by
    intro point rotation
    filter_upwards [factorization.eventually_common_norm point rotation] with γ hnorm
    intro i
    exact PoincareChapterVI.norm_chapterVIUnitBase_eq_one
      (factorization.normalizationRadius_ne_zero point
        (factorization.baseEssential + γ • essentialCoordinates rotation)) (hnorm i)
  eventually_weight_ne_zero := by
    intro point rotation
    filter_upwards [factorization.eventually_common_norm point rotation,
      factorization.eventually_leadingAmplitude_ne_zero point rotation] with
        γ hnorm hamplitude
    intro i
    unfold PoincareChapterVI.chapterVILogSpectrumWeight
    apply mul_ne_zero (neg_ne_zero.mpr (hamplitude i))
    have hbaseNorm := PoincareChapterVI.norm_chapterVIUnitBase_eq_one
      (factorization.normalizationRadius_ne_zero point
        (factorization.baseEssential + γ • essentialCoordinates rotation)) (hnorm i)
    intro hbase
    rw [hbase, norm_zero] at hbaseNorm
    exact zero_ne_one hbaseNorm
  eventually_asymptotic := by
    intro point rotation
    filter_upwards [factorization.eventually_radius_lt_analyticRadius point rotation,
      factorization.eventually_remainder_analytic point rotation,
      factorization.eventually_common_norm point rotation,
      factorization.eventually_tail_control point rotation] with
        γ hradii hremainder hnorm htail
    let radius := factorization.normalizationRadius point
      (factorization.baseEssential + γ • essentialCoordinates rotation)
    have hunit : ∀ i, ‖PoincareChapterVI.chapterVIUnitBase radius
        (factorization.singularityInverse point rotation γ i)‖ = 1 := by
      intro i
      exact PoincareChapterVI.norm_chapterVIUnitBase_eq_one
        (factorization.normalizationRadius_ne_zero point
          (factorization.baseEssential + γ • essentialCoordinates rotation)) (hnorm i)
    have hjet :=
      PoincareChapterVI.tendsto_chapterVINormalizedCoefficient_sub_finiteLogAnalyticAmplitudeSpectrum
        (factorization.normalizationRadius_ne_zero point
          (factorization.baseEssential + γ • essentialCoordinates rotation))
        (factorization.singularityInverse point rotation γ)
        (factorization.amplitudeJet point rotation γ)
        (factorization.tailBound point rotation γ) hunit htail.1 htail.2.1 htail.2.2
    have hanalytic := PoincareChapterVI.tendsto_chapterVINormalizedCoefficient_analyticRemainder
      hradii hremainder
    have htotal := hjet.add hanalytic
    convert htotal using 1
    · funext index
      have hdecomposition := factorization.coefficient_decomposition point rotation γ index
      unfold PoincareChapterVI.chapterVINormalizedCoefficient at hdecomposition ⊢
      simp only [Pi.sub_apply]
      rw [hdecomposition]
      ring
    · simp

/-- Poincaré's §102 contradiction follows for full analytic logarithmic amplitudes once their
local series satisfy the recorded Tannery bound. -/
theorem not_twoCoordinateAnalyticLogAmplitudeFactorization
    (spectrumSize : ℕ)
    (essentialCoordinates : Orientation →L[ℂ] Essential)
    (factorization : TwoCoordinateAnalyticLogAmplitudeFactorization
      spectrumSize essentialCoordinates) : False :=
  not_twoCoordinateScaledUnitSpectrumFactorization spectrumSize essentialCoordinates
    (factorization.toScaledUnitSpectrumFactorization spectrumSize essentialCoordinates)

/-- A source-faithful varying-amplitude interface that avoids expanding the amplitude about the
singular point all the way back to the origin.  For each logarithmic singularity it records
`G(z) = G(z₀) + (1-z/z₀) H(z)`, with the regular factor `H` analytic on a disk larger than the
common boundary circle. -/
structure TwoCoordinateRegularAnalyticLogAmplitudeFactorization
    (spectrumSize : ℕ)
    (essentialCoordinates : Orientation →L[ℂ] Essential) where
  baseEssential : Essential
  coefficient : FiniteSingularPoint → Essential → ℕ → ℂ
  normalizationRadius : FiniteSingularPoint → Essential → ℝ≥0
  normalizationRadius_ne_zero : ∀ point essential,
    normalizationRadius point essential ≠ 0
  singularityInverse : FiniteSingularPoint → Orientation → ℂ → Fin spectrumSize → ℂ
  leadingAmplitude : FiniteSingularPoint → Orientation → ℂ → Fin spectrumSize → ℂ
  regularAmplitudeCoefficient : FiniteSingularPoint → Orientation → ℂ →
    Fin spectrumSize → ℕ → ℂ
  regularAmplitude : FiniteSingularPoint → Orientation → ℂ →
    Fin spectrumSize → ℂ → ℂ
  regularAmplitudeRadius : FiniteSingularPoint → Orientation → ℂ →
    Fin spectrumSize → ℝ≥0
  remainderCoefficient : FiniteSingularPoint → Orientation → ℂ → ℕ → ℂ
  remainder : FiniteSingularPoint → Orientation → ℂ → ℂ → ℂ
  remainderRadius : FiniteSingularPoint → Orientation → ℂ → ℝ≥0
  distinguished : FiniteSingularPoint → Fin spectrumSize
  distinguished_eq : ∀ point rotation γ,
    singularityInverse point rotation γ (distinguished point) =
      (branchSingularityValue rotation point γ)⁻¹
  coefficient_decomposition : ∀ point rotation γ n,
    coefficient point (baseEssential + γ • essentialCoordinates rotation) n =
      PoincareChapterVI.chapterVIFiniteRegularAnalyticLogAmplitudeCoefficient
        (singularityInverse point rotation γ) (leadingAmplitude point rotation γ)
        (regularAmplitudeCoefficient point rotation γ) n +
      remainderCoefficient point rotation γ (n + 1)
  eventually_radius_lt_regularAmplitudeRadius : ∀ point rotation, ∀ᶠ γ in nhds 0,
    ∀ j, normalizationRadius point
      (baseEssential + γ • essentialCoordinates rotation) <
        regularAmplitudeRadius point rotation γ j
  eventually_regularAmplitude_analytic : ∀ point rotation, ∀ᶠ γ in nhds 0,
    ∀ j, HasFPowerSeriesOnBall (regularAmplitude point rotation γ j)
      (FormalMultilinearSeries.ofScalars ℂ
        (regularAmplitudeCoefficient point rotation γ j)) 0
      (regularAmplitudeRadius point rotation γ j)
  eventually_radius_lt_remainderRadius : ∀ point rotation, ∀ᶠ γ in nhds 0,
    normalizationRadius point
      (baseEssential + γ • essentialCoordinates rotation) <
        remainderRadius point rotation γ
  eventually_remainder_analytic : ∀ point rotation, ∀ᶠ γ in nhds 0,
    HasFPowerSeriesOnBall (remainder point rotation γ)
      (FormalMultilinearSeries.ofScalars ℂ (remainderCoefficient point rotation γ)) 0
      (remainderRadius point rotation γ)
  eventually_singularityInverse_injective : ∀ point rotation, ∀ᶠ γ in nhds 0,
    Function.Injective (singularityInverse point rotation γ)
  eventually_common_norm : ∀ point rotation, ∀ᶠ γ in nhds 0,
    ∀ i, ‖singularityInverse point rotation γ i‖ =
      (normalizationRadius point
        (baseEssential + γ • essentialCoordinates rotation) : ℝ)⁻¹
  eventually_leadingAmplitude_ne_zero : ∀ point rotation, ∀ᶠ γ in nhds 0,
    ∀ i, leadingAmplitude point rotation γ i ≠ 0

/-- The regular-factor analytic interface supplies the scaled unit spectrum without any
separately postulated Tannery bound: larger-disk analyticity proves the required weighted
summability internally. -/
def TwoCoordinateRegularAnalyticLogAmplitudeFactorization.toScaledUnitSpectrumFactorization
    (spectrumSize : ℕ)
    (essentialCoordinates : Orientation →L[ℂ] Essential)
    (factorization : TwoCoordinateRegularAnalyticLogAmplitudeFactorization
      spectrumSize essentialCoordinates) :
    TwoCoordinateScaledUnitSpectrumFactorization spectrumSize essentialCoordinates where
  baseEssential := factorization.baseEssential
  normalizationRadius := factorization.normalizationRadius
  normalizationRadius_ne_zero := factorization.normalizationRadius_ne_zero
  normalizedCoefficient point essential :=
    PoincareChapterVI.chapterVINormalizedCoefficient
      (factorization.normalizationRadius point essential)
      (factorization.coefficient point essential)
  spectrumBase point rotation γ i :=
    PoincareChapterVI.chapterVIUnitBase
      (factorization.normalizationRadius point
        (factorization.baseEssential + γ • essentialCoordinates rotation))
      (factorization.singularityInverse point rotation γ i)
  spectrumWeight point rotation γ i :=
    PoincareChapterVI.chapterVILogSpectrumWeight
      (factorization.normalizationRadius point
        (factorization.baseEssential + γ • essentialCoordinates rotation))
      (factorization.singularityInverse point rotation γ i)
      (factorization.leadingAmplitude point rotation γ i)
  distinguished := factorization.distinguished
  distinguished_eq := by
    intro point rotation γ
    rw [factorization.distinguished_eq]
    rfl
  eventually_base_injective := by
    intro point rotation
    filter_upwards [factorization.eventually_singularityInverse_injective point rotation] with
      γ hinjective
    intro i j hij
    apply hinjective
    apply mul_left_cancel₀
      (show (factorization.normalizationRadius point
        (factorization.baseEssential + γ • essentialCoordinates rotation) : ℂ) ≠ 0 by
          exact_mod_cast factorization.normalizationRadius_ne_zero point
            (factorization.baseEssential + γ • essentialCoordinates rotation))
    exact hij
  eventually_base_unit := by
    intro point rotation
    filter_upwards [factorization.eventually_common_norm point rotation] with γ hnorm
    intro i
    exact PoincareChapterVI.norm_chapterVIUnitBase_eq_one
      (factorization.normalizationRadius_ne_zero point
        (factorization.baseEssential + γ • essentialCoordinates rotation)) (hnorm i)
  eventually_weight_ne_zero := by
    intro point rotation
    filter_upwards [factorization.eventually_common_norm point rotation,
      factorization.eventually_leadingAmplitude_ne_zero point rotation] with
        γ hnorm hamplitude
    intro i
    unfold PoincareChapterVI.chapterVILogSpectrumWeight
    apply mul_ne_zero (neg_ne_zero.mpr (hamplitude i))
    have hbaseNorm := PoincareChapterVI.norm_chapterVIUnitBase_eq_one
      (factorization.normalizationRadius_ne_zero point
        (factorization.baseEssential + γ • essentialCoordinates rotation)) (hnorm i)
    intro hbase
    rw [hbase, norm_zero] at hbaseNorm
    exact zero_ne_one hbaseNorm
  eventually_asymptotic := by
    intro point rotation
    filter_upwards [factorization.eventually_radius_lt_regularAmplitudeRadius point rotation,
      factorization.eventually_regularAmplitude_analytic point rotation,
      factorization.eventually_radius_lt_remainderRadius point rotation,
      factorization.eventually_remainder_analytic point rotation,
      factorization.eventually_common_norm point rotation] with
        γ hregularRadii hregularAnalytic hremainderRadius hremainder hnorm
    let radius := factorization.normalizationRadius point
      (factorization.baseEssential + γ • essentialCoordinates rotation)
    have hunit : ∀ i, ‖PoincareChapterVI.chapterVIUnitBase radius
        (factorization.singularityInverse point rotation γ i)‖ = 1 := by
      intro i
      exact PoincareChapterVI.norm_chapterVIUnitBase_eq_one
        (factorization.normalizationRadius_ne_zero point
          (factorization.baseEssential + γ • essentialCoordinates rotation)) (hnorm i)
    have hlog :=
      PoincareChapterVI.tendsto_chapterVINormalizedCoefficient_sub_finiteRegularAnalyticLogAmplitudeSpectrum
        (factorization.normalizationRadius_ne_zero point
          (factorization.baseEssential + γ • essentialCoordinates rotation))
        (factorization.singularityInverse point rotation γ)
        (factorization.leadingAmplitude point rotation γ)
        (factorization.regularAmplitudeCoefficient point rotation γ)
        (factorization.regularAmplitude point rotation γ)
        (factorization.regularAmplitudeRadius point rotation γ)
        hunit hregularRadii hregularAnalytic
    have hanalytic := PoincareChapterVI.tendsto_chapterVINormalizedCoefficient_analyticRemainder
      hremainderRadius hremainder
    have htotal := hlog.add hanalytic
    convert htotal using 1
    · funext index
      have hdecomposition := factorization.coefficient_decomposition point rotation γ index
      unfold PoincareChapterVI.chapterVINormalizedCoefficient at hdecomposition ⊢
      simp only [Pi.sub_apply]
      rw [hdecomposition]
      ring
    · simp

/-- The regular-factor form of Poincaré's varying logarithmic amplitudes is incompatible with a
two-essential-coordinate coefficient family for the concrete 24-branch system. -/
theorem not_twoCoordinateRegularAnalyticLogAmplitudeFactorization
    (spectrumSize : ℕ)
    (essentialCoordinates : Orientation →L[ℂ] Essential)
    (factorization : TwoCoordinateRegularAnalyticLogAmplitudeFactorization
      spectrumSize essentialCoordinates) : False :=
  not_twoCoordinateScaledUnitSpectrumFactorization spectrumSize essentialCoordinates
    (factorization.toScaledUnitSpectrumFactorization spectrumSize essentialCoordinates)

/-- The most source-facing §100--102 interface: the coefficient-generating function is given,
as an analytic germ at the origin, by actual varying analytic amplitudes multiplying logarithms
plus a larger-disk analytic remainder.  All Cauchy-product coefficients, removable factors, and
Darboux tail bounds are derived rather than included as fields. -/
structure TwoCoordinateAnalyticLogGermFactorization
    (spectrumSize : ℕ)
    (essentialCoordinates : Orientation →L[ℂ] Essential) where
  baseEssential : Essential
  coefficientFunction : FiniteSingularPoint → Essential → ℂ → ℂ
  coefficient : FiniteSingularPoint → Essential → ℕ → ℂ
  normalizationRadius : FiniteSingularPoint → Essential → ℝ≥0
  normalizationRadius_ne_zero : ∀ point essential,
    normalizationRadius point essential ≠ 0
  singularity : FiniteSingularPoint → Orientation → ℂ → Fin spectrumSize → ℂ
  amplitude : FiniteSingularPoint → Orientation → ℂ → Fin spectrumSize → ℂ → ℂ
  amplitudeCoefficient : FiniteSingularPoint → Orientation → ℂ →
    Fin spectrumSize → ℕ → ℂ
  amplitudeRadius : FiniteSingularPoint → Orientation → ℂ →
    Fin spectrumSize → ℝ≥0
  remainder : FiniteSingularPoint → Orientation → ℂ → ℂ → ℂ
  remainderCoefficient : FiniteSingularPoint → Orientation → ℂ → ℕ → ℂ
  remainderRadius : FiniteSingularPoint → Orientation → ℂ → ℝ≥0
  distinguished : FiniteSingularPoint → Fin spectrumSize
  distinguished_eq : ∀ point rotation γ,
    singularity point rotation γ (distinguished point) =
      branchSingularityValue rotation point γ
  eventually_coefficient_hasFPowerSeries : ∀ point rotation, ∀ᶠ (γ : ℂ) in nhds 0,
    HasFPowerSeriesAt
      (coefficientFunction point
        (baseEssential + γ • essentialCoordinates rotation))
      (FormalMultilinearSeries.ofScalars ℂ
        (coefficient point
          (baseEssential + γ • essentialCoordinates rotation))) 0
  eventually_function_decomposition : ∀ point rotation, ∀ᶠ γ in nhds 0,
    coefficientFunction point
        (baseEssential + γ • essentialCoordinates rotation) =ᶠ[nhds 0]
      fun z ↦ (∑ j, amplitude point rotation γ j z *
        Complex.log (1 - z * (singularity point rotation γ j)⁻¹)) +
        remainder point rotation γ z
  eventually_radius_lt_amplitudeRadius : ∀ point rotation, ∀ᶠ γ in nhds 0,
    ∀ j, normalizationRadius point
      (baseEssential + γ • essentialCoordinates rotation) <
        amplitudeRadius point rotation γ j
  eventually_amplitude_analytic : ∀ point rotation, ∀ᶠ γ in nhds 0,
    ∀ j, HasFPowerSeriesOnBall (amplitude point rotation γ j)
      (FormalMultilinearSeries.ofScalars ℂ
        (amplitudeCoefficient point rotation γ j)) 0
      (amplitudeRadius point rotation γ j)
  eventually_radius_lt_remainderRadius : ∀ point rotation, ∀ᶠ γ in nhds 0,
    normalizationRadius point
      (baseEssential + γ • essentialCoordinates rotation) <
        remainderRadius point rotation γ
  eventually_remainder_analytic : ∀ point rotation, ∀ᶠ γ in nhds 0,
    HasFPowerSeriesOnBall (remainder point rotation γ)
      (FormalMultilinearSeries.ofScalars ℂ (remainderCoefficient point rotation γ)) 0
      (remainderRadius point rotation γ)
  eventually_singularity_injective : ∀ point rotation, ∀ᶠ γ in nhds 0,
    Function.Injective (singularity point rotation γ)
  eventually_common_norm : ∀ point rotation, ∀ᶠ γ in nhds 0,
    ∀ j, ‖singularity point rotation γ j‖ =
      normalizationRadius point
        (baseEssential + γ • essentialCoordinates rotation)
  eventually_leadingAmplitude_ne_zero : ∀ point rotation, ∀ᶠ γ in nhds 0,
    ∀ j, amplitude point rotation γ j (singularity point rotation γ j) ≠ 0

/-- The actual analytic-log germ decomposition supplies the entire scaled spectrum interface. -/
def TwoCoordinateAnalyticLogGermFactorization.toScaledUnitSpectrumFactorization
    (spectrumSize : ℕ)
    (essentialCoordinates : Orientation →L[ℂ] Essential)
    (factorization : TwoCoordinateAnalyticLogGermFactorization
      spectrumSize essentialCoordinates) :
    TwoCoordinateScaledUnitSpectrumFactorization spectrumSize essentialCoordinates where
  baseEssential := factorization.baseEssential
  normalizationRadius := factorization.normalizationRadius
  normalizationRadius_ne_zero := factorization.normalizationRadius_ne_zero
  normalizedCoefficient point essential :=
    PoincareChapterVI.chapterVINormalizedCoefficient
      (factorization.normalizationRadius point essential)
      (fun index ↦ factorization.coefficient point essential (index + 1))
  spectrumBase point rotation γ j :=
    PoincareChapterVI.chapterVIUnitBase
      (factorization.normalizationRadius point
        (factorization.baseEssential + γ • essentialCoordinates rotation))
      (factorization.singularity point rotation γ j)⁻¹
  spectrumWeight point rotation γ j :=
    PoincareChapterVI.chapterVILogSpectrumWeight
      (factorization.normalizationRadius point
        (factorization.baseEssential + γ • essentialCoordinates rotation))
      (factorization.singularity point rotation γ j)⁻¹
      (factorization.amplitude point rotation γ j
        (factorization.singularity point rotation γ j))
  distinguished := factorization.distinguished
  distinguished_eq := by
    intro point rotation γ
    rw [factorization.distinguished_eq]
    rfl
  eventually_base_injective := by
    intro point rotation
    filter_upwards [factorization.eventually_singularity_injective point rotation,
      factorization.eventually_common_norm point rotation] with γ hinjective hnorm
    intro i j hij
    apply hinjective
    apply inv_injective
    apply mul_left_cancel₀
      (show (factorization.normalizationRadius point
        (factorization.baseEssential + γ • essentialCoordinates rotation) : ℂ) ≠ 0 by
          exact_mod_cast factorization.normalizationRadius_ne_zero point
            (factorization.baseEssential + γ • essentialCoordinates rotation))
    exact hij
  eventually_base_unit := by
    intro point rotation
    filter_upwards [factorization.eventually_common_norm point rotation] with γ hnorm
    intro j
    apply PoincareChapterVI.norm_chapterVIUnitBase_eq_one
      (factorization.normalizationRadius_ne_zero point
        (factorization.baseEssential + γ • essentialCoordinates rotation))
    rw [norm_inv, hnorm j]
  eventually_weight_ne_zero := by
    intro point rotation
    filter_upwards [factorization.eventually_common_norm point rotation,
      factorization.eventually_leadingAmplitude_ne_zero point rotation] with
        γ hnorm hamplitude
    intro j
    unfold PoincareChapterVI.chapterVILogSpectrumWeight
    apply mul_ne_zero (neg_ne_zero.mpr (hamplitude j))
    have hbaseNorm := PoincareChapterVI.norm_chapterVIUnitBase_eq_one
      (factorization.normalizationRadius_ne_zero point
        (factorization.baseEssential + γ • essentialCoordinates rotation))
      (by rw [norm_inv, hnorm j])
    intro hbase
    rw [hbase, norm_zero] at hbaseNorm
    exact zero_ne_one hbaseNorm
  eventually_asymptotic := by
    intro point rotation
    filter_upwards [factorization.eventually_coefficient_hasFPowerSeries point rotation,
      factorization.eventually_function_decomposition point rotation,
      factorization.eventually_radius_lt_amplitudeRadius point rotation,
      factorization.eventually_amplitude_analytic point rotation,
      factorization.eventually_radius_lt_remainderRadius point rotation,
      factorization.eventually_remainder_analytic point rotation,
      factorization.eventually_common_norm point rotation] with
        γ hcoefficient hdecomposition hamplitudeRadii hamplitude
          hremainderRadius hremainder hnorm
    let radius := factorization.normalizationRadius point
      (factorization.baseEssential + γ • essentialCoordinates rotation)
    have hsingularity : ∀ j, factorization.singularity point rotation γ j ≠ 0 := by
      intro j hzero
      have := hnorm j
      rw [hzero, norm_zero] at this
      exact factorization.normalizationRadius_ne_zero point
        (factorization.baseEssential + γ • essentialCoordinates rotation)
        (NNReal.coe_eq_zero.mp this.symm)
    have hlog :=
      PoincareChapterVI.tendsto_chapterVINormalizedCoefficient_sub_finiteAnalyticLogProductSpectrum
        (factorization.normalizationRadius_ne_zero point
          (factorization.baseEssential + γ • essentialCoordinates rotation))
        (factorization.singularity point rotation γ) hsingularity hnorm
        (factorization.amplitudeCoefficient point rotation γ)
        (factorization.amplitude point rotation γ)
        (factorization.amplitudeRadius point rotation γ) hamplitudeRadii hamplitude
    have hanalytic := PoincareChapterVI.tendsto_chapterVINormalizedCoefficient_analyticRemainder
      hremainderRadius hremainder
    have htotal := hlog.add hanalytic
    convert htotal using 1
    · funext index
      have hcoefficientDecomposition :=
        PoincareChapterVI.coefficient_eq_finiteAnalyticLogs_add_analyticRemainder
          (fun j ↦ (factorization.singularity point rotation γ j)⁻¹)
          (factorization.amplitude point rotation γ)
          (factorization.amplitudeCoefficient point rotation γ)
          hcoefficient (show HasFPowerSeriesAt (factorization.remainder point rotation γ)
            (FormalMultilinearSeries.ofScalars ℂ
              (factorization.remainderCoefficient point rotation γ)) 0 from
                ⟨factorization.remainderRadius point rotation γ, hremainder⟩)
          (fun j ↦ ⟨factorization.amplitudeRadius point rotation γ j, hamplitude j⟩)
          hdecomposition (index + 1)
      have hcoefficientDecomposition' :
          factorization.coefficient point
              (factorization.baseEssential + γ • essentialCoordinates rotation) (index + 1) =
            PoincareChapterVI.chapterVIFiniteAnalyticLogProductCoefficient
              (factorization.singularity point rotation γ)
              (factorization.amplitudeCoefficient point rotation γ) index +
            factorization.remainderCoefficient point rotation γ (index + 1) := by
        simpa [PoincareChapterVI.chapterVIFiniteAnalyticLogProductCoefficient] using
          hcoefficientDecomposition
      unfold PoincareChapterVI.chapterVINormalizedCoefficient at hcoefficientDecomposition ⊢
      simp only [Pi.sub_apply]
      rw [hcoefficientDecomposition']
      ring
    · simp

/-- Poincaré's function-level analytic-log germ data already contradicts the compiled §103
calculation; no independent coefficient or tail estimate remains in this interface. -/
theorem not_twoCoordinateAnalyticLogGermFactorization
    (spectrumSize : ℕ)
    (essentialCoordinates : Orientation →L[ℂ] Essential)
    (factorization : TwoCoordinateAnalyticLogGermFactorization
      spectrumSize essentialCoordinates) : False :=
  not_twoCoordinateScaledUnitSpectrumFactorization spectrumSize essentialCoordinates
    (factorization.toScaledUnitSpectrumFactorization spectrumSize essentialCoordinates)

end PoincareChapterVI.ChapterVISection102
