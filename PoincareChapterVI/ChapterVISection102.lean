/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import Mathlib.LinearAlgebra.Determinant
import PoincareChapterVI.ChapterVIDarboux
import PoincareChapterVI.ChapterVIDarbouxSpectrum
import PoincareChapterVI.Section103.MovingAlgebraicBranches

/-!
# Poincaré's two-essential-coordinate argument in Chapter VI, §102

On pp. 328--329 Poincaré argues that, if the additional uniform integral existed, the singular
roots would depend on only two of the three orientation parameters.  Consequently the Jacobian
of any three roots with respect to inclination and the two perihelion longitudes would vanish.

The following formulation records exactly the differential consequence used in §103.  It is
deliberately weaker than requiring the roots to be locally constant on a straight parameter line:
their differentials merely factor through a two-dimensional space.  Rank--nullity then supplies
one nonzero orientation direction in which every singular root is stationary.  The concrete
moving-curve formalization turns that stationarity into Poincaré's equation (2), and its
LeanCompCert certificate gives the contradiction.

The file now derives that rank conclusion from `TwoCoordinateDarbouxFactorization`: isolated
coefficient sequences factor through two essential coordinates and have Poincaré's stated
Darboux leading term.  Constructing that data from the putative uniform integral in Chapter V,
the contour integral, and the singularity classification in §§93--100 remains the historical
analytic input.
-/

noncomputable section

namespace PoincareChapterVI.ChapterVISection102

open AffineIntersectionCount
open MovingAlgebraicBranches
open Asymptotics Filter

private abbrev Orientation := Fin 3 → ℂ
private abbrev Essential := Fin 2 → ℂ
private abbrev FiniteSingularPoint :=
  { point : Fin 2 → ℂ // point ∈ finiteIntersectionPoints }

/-- If a linear root differential kills every direction killed by a two-coordinate map, then
its rank is at most two.  This is the intrinsic rank form of Poincaré's parameter count. -/
theorem finrank_range_le_two_of_ker_le_essentialKernel
    {RootValues : Type*} [AddCommGroup RootValues] [Module ℂ RootValues]
    (rootDifferential : Orientation →ₗ[ℂ] RootValues)
    (essentialCoordinates : Orientation →ₗ[ℂ] Essential)
    (hker : LinearMap.ker essentialCoordinates ≤ LinearMap.ker rootDifferential) :
    Module.finrank ℂ rootDifferential.range ≤ 2 := by
  have hkerDimension : Module.finrank ℂ (LinearMap.ker essentialCoordinates) ≤
      Module.finrank ℂ (LinearMap.ker rootDifferential) :=
    Submodule.finrank_mono hker
  have hroot := LinearMap.finrank_range_add_finrank_ker rootDifferential
  have hessential := LinearMap.finrank_range_add_finrank_ker essentialCoordinates
  have hessentialRange : Module.finrank ℂ essentialCoordinates.range ≤ 2 := by
    simpa using (LinearMap.range essentialCoordinates).finrank_le
  have horientation : Module.finrank ℂ Orientation = 3 := by simp
  rw [horientation] at hroot hessential
  omega

/-- The block-triangular determinant reduction on p. 329.  The first-kind parameters `τ,τ'`
depend separately and nontrivially on the two eccentricities, so vanishing of the full five-by-five
Jacobian forces vanishing of the three-by-three orientation Jacobian of any three second-kind
roots.  The lower-left block is unrestricted because those roots may also depend on eccentricity. -/
theorem orientationJacobian_det_eq_zero_of_fullJacobian_det_eq_zero
    (dτ dτ' : ℂ) (hdτ : dτ ≠ 0) (hdτ' : dτ' ≠ 0)
    (eccentricityDerivative : Matrix (Fin 3) (Fin 2) ℂ)
    (orientationDerivative : Matrix (Fin 3) (Fin 3) ℂ)
    (hfull : (Matrix.fromBlocks (Matrix.diagonal ![dτ, dτ']) 0
      eccentricityDerivative orientationDerivative).det = 0) :
    orientationDerivative.det = 0 := by
  rw [Matrix.det_fromBlocks_zero₁₂] at hfull
  have hdiagonal : (Matrix.diagonal ![dτ, dτ'] : Matrix (Fin 2) (Fin 2) ℂ).det =
      dτ * dτ' := by
    simp [Fin.prod_univ_succ]
  rw [hdiagonal] at hfull
  exact (mul_eq_zero.mp hfull).resolve_left (mul_ne_zero hdτ hdτ')

/-- Intrinsic differential-rank formulation of the last sentence of §102: with eccentricities
fixed, the complete collection of second-kind singular roots has rank at most two as a function
of the three orientation parameters. -/
structure SecondKindRootDifferential where
  differential : Orientation →L[ℂ] (FiniteSingularPoint → ℂ)
  agrees : ∀ (rotation : Orientation) (point : FiniteSingularPoint),
    branchSingularityParameterDerivative rotation point.1 point.2 =
      differential rotation point
  rank_le_two : Module.finrank ℂ differential.toLinearMap.range ≤ 2

/-- The root differential is not additional data: it is canonically assembled from the exact
directional derivatives of the 24 moving algebraic IFT branches. -/
def concreteSecondKindRootDifferential :
    Orientation →L[ℂ] (FiniteSingularPoint → ℂ) :=
  ContinuousLinearMap.pi fun point ↦
    branchSingularityDifferential point.1 point.2

@[simp] theorem concreteSecondKindRootDifferential_apply
    (rotation : Orientation) (point : FiniteSingularPoint) :
    concreteSecondKindRootDifferential rotation point =
      branchSingularityParameterDerivative rotation point.1 point.2 := by
  exact branchSingularityDifferential_apply rotation point.1 point.2

/-- The singularity value along the concrete one-parameter IFT branch in a chosen infinitesimal
orientation direction. -/
def branchSingularityValue (rotation : Orientation)
    (point : FiniteSingularPoint) (γ : ℂ) : ℂ :=
  SingularityParameterTangent.halfAngleSingularityParameter (-2) 3 (1 / 3) (1 / 5)
    ((movingLocalSystem rotation point.1 point.2).branch γ).1
    ((movingLocalSystem rotation point.1 point.2).branch γ).2

@[simp] theorem branchSingularityValue_zero
    (rotation : Orientation) (point : FiniteSingularPoint) :
    branchSingularityValue rotation point 0 =
      SingularityParameterTangent.halfAngleSingularityParameter
        (-2) 3 (1 / 3) (1 / 5) (point.1 0) (point.1 1) := by
  simp [branchSingularityValue, movingLocalSystem]

/-- The branch singularity value has the derivative already computed by the concrete IFT
construction. -/
theorem hasDerivAt_branchSingularityValue
    (rotation : Orientation) (point : FiniteSingularPoint) :
    HasDerivAt (branchSingularityValue rotation point)
      (branchSingularityParameterDerivative rotation point.1 point.2) 0 := by
  change HasDerivAt
    (fun γ ↦ SingularityParameterTangent.halfAngleSingularityParameter
      (-2) 3 (1 / 3) (1 / 5)
      ((movingLocalSystem rotation point.1 point.2).branch γ).1
      ((movingLocalSystem rotation point.1 point.2).branch γ).2)
    (branchSingularityParameterDerivative rotation point.1 point.2) 0
  exact MovingAlgebraicBranches.hasDerivAt_branchSingularityParameter
    rotation point.1 point.2

/-- The concrete IFT branch stays away from the coordinate axes near its certified base point,
so Poincaré's exponential singularity parameter remains nonzero. -/
theorem eventually_branchSingularityValue_ne_zero
    (rotation : Orientation) (point : FiniteSingularPoint) :
    ∀ᶠ γ in nhds 0, branchSingularityValue rotation point γ ≠ 0 := by
  let data := movingLocalSystem rotation point.1 point.2
  have hcoordinates :=
    ReducedCurveTangent.finiteIntersectionPoint_coordinates_ne_zero point.1 point.2
  have hx : Tendsto (fun γ ↦ (data.branch γ).1) (nhds 0) (nhds (point.1 0)) := by
    simpa [data, movingLocalSystem] using data.timeBranch_hasDerivAt.continuousAt.tendsto
  have hy : Tendsto (fun γ ↦ (data.branch γ).2) (nhds 0) (nhds (point.1 1)) := by
    simpa [data, movingLocalSystem] using
      data.singularValueBranch_hasDerivAt.continuousAt.tendsto
  filter_upwards [hx.eventually_ne hcoordinates.1, hy.eventually_ne hcoordinates.2] with
      γ hxγ hyγ
  exact SingularityParameterTangent.halfAngleSingularityParameter_ne_zero
    (-2) 3 (1 / 3) (1 / 5) hxγ hyγ

/-- The exact coefficient-to-singularity input behind Poincaré's §102 dependency argument.

For each isolated second-kind singular branch, `coefficient` is the corresponding coefficient
sequence after the competing singular contributions have been separated.  Along a direction
that fixes the two essential coordinates, this sequence is locally constant.  Darboux's formula
identifies its leading exponential base with the inverse singularity value.  The nonvanishing
condition excludes a missing leading term; nonvanishing of the concrete singularity value is
proved from the IFT branch and the certified nonzero base coordinates.

Deriving this structure from Poincaré's actual contour integral remains the analytic work of
§§93--100; unlike a direct rank assumption, these fields state the coefficient asymptotics that
his printed §102 argument invokes. -/
structure DarbouxCoefficientRecovery
    (essentialCoordinates : Orientation →L[ℂ] Essential) where
  coefficient : FiniteSingularPoint → Orientation → ℂ → ℕ → ℂ
  leadingCoefficient : FiniteSingularPoint → Orientation → ℂ → ℂ
  coefficient_eventually_constant : ∀ rotation,
    essentialCoordinates rotation = 0 → ∀ point,
      (fun γ ↦ coefficient point rotation γ) =ᶠ[nhds 0]
        fun _ ↦ coefficient point rotation 0
  eventually_asymptotic : ∀ rotation point, ∀ᶠ γ in nhds 0,
    coefficient point rotation γ ~[atTop]
      PoincareChapterVI.chapterVILeadingDarbouxModel
        (branchSingularityValue rotation point γ)⁻¹
        (leadingCoefficient point rotation γ)
  eventually_leadingCoefficient_ne_zero : ∀ rotation point, ∀ᶠ γ in nhds 0,
    leadingCoefficient point rotation γ ≠ 0

/-- A direct formulation of Poincaré's claim that the isolated coefficient data depend on only
two essential orientation coordinates.  The scalar `γ` moves along the image of an orientation
direction, starting at `baseEssential`. -/
structure TwoCoordinateDarbouxFactorization
    (essentialCoordinates : Orientation →L[ℂ] Essential) where
  baseEssential : Essential
  coefficient : FiniteSingularPoint → Essential → ℕ → ℂ
  leadingCoefficient : FiniteSingularPoint → Orientation → ℂ → ℂ
  eventually_asymptotic : ∀ rotation point, ∀ᶠ γ in nhds 0,
    coefficient point (baseEssential + γ • essentialCoordinates rotation) ~[atTop]
      PoincareChapterVI.chapterVILeadingDarbouxModel
        (branchSingularityValue rotation point γ)⁻¹
        (leadingCoefficient point rotation γ)
  eventually_leadingCoefficient_ne_zero : ∀ rotation point, ∀ᶠ γ in nhds 0,
    leadingCoefficient point rotation γ ≠ 0

/-- Equal-modulus version of the §102 coefficient input.  Instead of isolating one singularity,
the normalized coefficient sequence is approximated by a finite exponential spectrum on the unit
circle.  `distinguished` identifies the concrete IFT branch within that spectrum.

This structure makes the competing-singularity obligations explicit: local uniform asymptotics,
distinct bases, nonzero leading weights, a common unit-modulus normalization, and dependence of
the normalized coefficients through two essential coordinates. -/
structure TwoCoordinateUnitSpectrumFactorization (spectrumSize : ℕ)
    (essentialCoordinates : Orientation →L[ℂ] Essential) where
  baseEssential : Essential
  normalizedCoefficient : FiniteSingularPoint → Essential → ℕ → ℂ
  spectrumBase : FiniteSingularPoint → Orientation → ℂ → Fin spectrumSize → ℂ
  spectrumWeight : FiniteSingularPoint → Orientation → ℂ → Fin spectrumSize → ℂ
  distinguished : FiniteSingularPoint → Fin spectrumSize
  distinguished_eq : ∀ point rotation γ,
    spectrumBase point rotation γ (distinguished point) =
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

/-- Along a direction invisible to the essential coordinates, the normalized coefficient
sequence is unchanged.  Finite-spectrum Darboux uniqueness therefore fixes the complete set of
equally dominant inverse singularities, even when no consecutive-coefficient ratio converges. -/
theorem TwoCoordinateUnitSpectrumFactorization.eventually_spectrumRange_eq
    (spectrumSize : ℕ) (essentialCoordinates : Orientation →L[ℂ] Essential)
    (factorization : TwoCoordinateUnitSpectrumFactorization spectrumSize essentialCoordinates)
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

/-- Continuity of the concrete IFT branch prevents a locally fixed finite spectrum from
permuting its labels.  Hence finite-spectrum Darboux recovery gives the same local branch
constancy as the isolated-singularity argument. -/
theorem TwoCoordinateUnitSpectrumFactorization.eventually_branchSingularityValue_eq
    (spectrumSize : ℕ) (essentialCoordinates : Orientation →L[ℂ] Essential)
    (factorization : TwoCoordinateUnitSpectrumFactorization spectrumSize essentialCoordinates)
    (rotation : Orientation) (hrotation : essentialCoordinates rotation = 0)
    (point : FiniteSingularPoint) :
    (fun γ ↦ branchSingularityValue rotation point γ) =ᶠ[nhds 0]
      fun _ ↦ branchSingularityValue rotation point 0 := by
  let distinguished := factorization.distinguished point
  let baseAtZero := factorization.spectrumBase point rotation 0
  have hbaseZero : Function.Injective baseAtZero := by
    exact (factorization.eventually_base_injective point rotation).self_of_nhds
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
    convert hinverse using 1
    · funext γ
      exact factorization.distinguished_eq point rotation γ
    · exact congrArg nhds (factorization.distinguished_eq point rotation 0)
  have hrange := factorization.eventually_spectrumRange_eq
    spectrumSize essentialCoordinates rotation hrotation point
  have hmem : ∀ᶠ γ in nhds 0,
      factorization.spectrumBase point rotation γ distinguished ∈ Set.range baseAtZero := by
    filter_upwards [hrange] with γ hγ
    rw [← hγ]
    exact ⟨distinguished, rfl⟩
  have hlabel := PoincareChapterVI.eventually_eq_of_tendsto_of_eventually_mem_finiteSpectrum
    hbaseZero distinguished hdistinguished hmem
  filter_upwards [hlabel] with γ hγ
  apply inv_injective
  rw [← factorization.distinguished_eq point rotation γ,
    ← factorization.distinguished_eq point rotation 0]
  exact hγ

/-- Package finite-spectrum recovery as the concrete local constancy input consumed by §103. -/
theorem TwoCoordinateUnitSpectrumFactorization.branchConstancy_of_mem_ker
    (spectrumSize : ℕ) (essentialCoordinates : Orientation →L[ℂ] Essential)
    (factorization : TwoCoordinateUnitSpectrumFactorization spectrumSize essentialCoordinates)
    (rotation : Orientation) (hrotation : essentialCoordinates rotation = 0) :
    BranchSingularityConstancy rotation where
  eventually_constant := by
    intro point hpoint
    let indexedPoint : FiniteSingularPoint := ⟨point, hpoint⟩
    have hconstant := factorization.eventually_branchSingularityValue_eq
      spectrumSize essentialCoordinates rotation hrotation indexedPoint
    simpa [branchSingularityValue, indexedPoint, movingLocalSystem] using hconstant

/-- Explicit dependence through two coordinates supplies the coefficient-constancy form needed
by Darboux uniqueness. -/
def TwoCoordinateDarbouxFactorization.toCoefficientRecovery
    (essentialCoordinates : Orientation →L[ℂ] Essential)
    (factorization : TwoCoordinateDarbouxFactorization essentialCoordinates) :
    DarbouxCoefficientRecovery essentialCoordinates where
  coefficient point rotation γ :=
    factorization.coefficient point
      (factorization.baseEssential + γ • essentialCoordinates rotation)
  leadingCoefficient := factorization.leadingCoefficient
  coefficient_eventually_constant := by
    intro rotation hrotation point
    filter_upwards with γ
    simp [hrotation]
  eventually_asymptotic := factorization.eventually_asymptotic
  eventually_leadingCoefficient_ne_zero :=
    factorization.eventually_leadingCoefficient_ne_zero

/-- Darboux uniqueness upgrades coefficient constancy to constancy of the corresponding isolated
singularity branch. -/
theorem DarbouxCoefficientRecovery.eventually_branchSingularityValue_eq
    (essentialCoordinates : Orientation →L[ℂ] Essential)
    (recovery : DarbouxCoefficientRecovery essentialCoordinates)
    (rotation : Orientation) (hrotation : essentialCoordinates rotation = 0)
    (point : FiniteSingularPoint) :
    (fun γ ↦ branchSingularityValue rotation point γ) =ᶠ[nhds 0]
      fun _ ↦ branchSingularityValue rotation point 0 := by
  have hasymptoticZero :=
    (recovery.eventually_asymptotic rotation point).self_of_nhds
  have hsingularityZero :=
    (eventually_branchSingularityValue_ne_zero rotation point).self_of_nhds
  have hleadingZero :=
    (recovery.eventually_leadingCoefficient_ne_zero rotation point).self_of_nhds
  filter_upwards [recovery.coefficient_eventually_constant rotation hrotation point,
    recovery.eventually_asymptotic rotation point,
    eventually_branchSingularityValue_ne_zero rotation point,
    recovery.eventually_leadingCoefficient_ne_zero rotation point] with
      γ hcoefficient hasymptotic hsingularity hleading
  have hasymptoticZero' : recovery.coefficient point rotation γ ~[atTop]
      PoincareChapterVI.chapterVILeadingDarbouxModel
        (branchSingularityValue rotation point 0)⁻¹
        (recovery.leadingCoefficient point rotation 0) := by
    rw [hcoefficient]
    exact hasymptoticZero
  apply inv_injective
  exact PoincareChapterVI.chapterVI_darbouxSingularityInverse_unique
    (inv_ne_zero hsingularity) hleading
    (inv_ne_zero hsingularityZero) hleadingZero
    hasymptotic hasymptoticZero'

/-- The coefficient-recovery hypotheses imply the local branch constancy that is sufficient for
the §103 tangent calculation. -/
theorem DarbouxCoefficientRecovery.branchConstancy_of_mem_ker
    (essentialCoordinates : Orientation →L[ℂ] Essential)
    (recovery : DarbouxCoefficientRecovery essentialCoordinates)
    (rotation : Orientation) (hrotation : essentialCoordinates rotation = 0) :
    BranchSingularityConstancy rotation where
  eventually_constant := by
    intro point hpoint
    let indexedPoint : FiniteSingularPoint := ⟨point, hpoint⟩
    have hconstant := recovery.eventually_branchSingularityValue_eq
      essentialCoordinates rotation hrotation indexedPoint
    simpa [branchSingularityValue, indexedPoint, movingLocalSystem] using hconstant

/-- Every direction invisible to the two essential coordinates is also killed by the canonical
differential of all 24 singular roots. -/
theorem DarbouxCoefficientRecovery.essentialKernel_le_concreteDifferentialKernel
    (essentialCoordinates : Orientation →L[ℂ] Essential)
    (recovery : DarbouxCoefficientRecovery essentialCoordinates) :
    LinearMap.ker essentialCoordinates.toLinearMap ≤
      LinearMap.ker concreteSecondKindRootDifferential.toLinearMap := by
  intro rotation hrotation
  have hcoordinates : essentialCoordinates rotation = 0 := hrotation
  have hstationary :=
    (recovery.branchConstancy_of_mem_ker essentialCoordinates rotation hcoordinates).toStationarity
  change concreteSecondKindRootDifferential rotation = 0
  funext point
  rw [concreteSecondKindRootDifferential_apply]
  exact hstationary.derivative_eq_zero point.1 point.2

/-- Poincaré's coefficient-dependence and Darboux-recovery premises imply the exact §102 rank
bound, without assuming that rank bound separately. -/
theorem DarbouxCoefficientRecovery.concreteDifferential_rank_le_two
    (essentialCoordinates : Orientation →L[ℂ] Essential)
    (recovery : DarbouxCoefficientRecovery essentialCoordinates) :
    Module.finrank ℂ concreteSecondKindRootDifferential.toLinearMap.range ≤ 2 := by
  apply finrank_range_le_two_of_ker_le_essentialKernel
    concreteSecondKindRootDifferential.toLinearMap essentialCoordinates.toLinearMap
  exact recovery.essentialKernel_le_concreteDifferentialKernel essentialCoordinates

/-- Package the canonical differential once the sole §102 rank bound is known. -/
def concreteSecondKindRootDifferentialData
    (hrank : Module.finrank ℂ
      concreteSecondKindRootDifferential.toLinearMap.range ≤ 2) :
    SecondKindRootDifferential where
  differential := concreteSecondKindRootDifferential
  agrees := fun rotation point ↦
    (concreteSecondKindRootDifferential_apply rotation point).symm
  rank_le_two := hrank

/-- A rank-at-most-two differential on the three orientation parameters has a nonzero common
stationary direction for all twenty-four roots. -/
theorem exists_nonzero_stationary_direction (roots : SecondKindRootDifferential) :
    ∃ rotation : Orientation, rotation ≠ 0 ∧ BranchSingularityStationarity rotation := by
  have hkernel : LinearMap.ker roots.differential.toLinearMap ≠ ⊥ := by
    intro hbot
    have hinjective : Function.Injective roots.differential :=
      LinearMap.ker_eq_bot.mp hbot
    have hrange : Module.finrank ℂ roots.differential.toLinearMap.range =
        Module.finrank ℂ Orientation :=
      LinearMap.finrank_range_of_inj hinjective
    have : Module.finrank ℂ Orientation ≤ 2 := hrange ▸ roots.rank_le_two
    norm_num at this
  obtain ⟨rotation, hrotationKernel, hrotationNonzero⟩ :=
    (LinearMap.ker roots.differential.toLinearMap).ne_bot_iff.mp hkernel
  refine ⟨rotation, hrotationNonzero, ⟨?_⟩⟩
  intro point hpoint
  let indexedPoint : FiniteSingularPoint := ⟨point, hpoint⟩
  have hzero : roots.differential rotation = 0 := hrotationKernel
  rw [roots.agrees rotation indexedPoint]
  exact congrFun hzero indexedPoint

/-- Poincaré's §102 rank conclusion contradicts the fully formalized §103 calculation. -/
theorem not_rankAtMostTwo_secondKindRootDifferential
    (roots : SecondKindRootDifferential) : False := by
  obtain ⟨rotation, hrotationNonzero, hstationary⟩ :=
    exists_nonzero_stationary_direction roots
  exact hrotationNonzero
    (rotation_eq_zero_of_branchSingularityStationarity rotation hstationary)

/-- The remaining §102 statement in its minimal form: the exact, already-constructed root
differential cannot have rank at most two.  Thus deriving Poincaré's asserted rank bound from a
putative uniform integral immediately finishes the §102--103 contradiction. -/
theorem not_concreteSecondKindRootDifferential_rank_le_two
    (hrank : Module.finrank ℂ
      concreteSecondKindRootDifferential.toLinearMap.range ≤ 2) :
    False :=
  not_rankAtMostTwo_secondKindRootDifferential
    (concreteSecondKindRootDifferentialData hrank)

/-- Source-facing §102--103 contradiction: no two-coordinate coefficient family satisfying the
isolated Darboux recovery hypotheses can produce the 24 concrete second-kind branches. -/
theorem not_darbouxCoefficientRecovery
    (essentialCoordinates : Orientation →L[ℂ] Essential)
    (recovery : DarbouxCoefficientRecovery essentialCoordinates) : False :=
  not_concreteSecondKindRootDifferential_rank_le_two
    (recovery.concreteDifferential_rank_le_two essentialCoordinates)

/-- Poincaré's asserted two-coordinate coefficient factorization, together with isolated Darboux
asymptotics, directly contradicts the certified §103 family. -/
theorem not_twoCoordinateDarbouxFactorization
    (essentialCoordinates : Orientation →L[ℂ] Essential)
    (factorization : TwoCoordinateDarbouxFactorization essentialCoordinates) : False :=
  not_darbouxCoefficientRecovery essentialCoordinates
    (factorization.toCoefficientRecovery essentialCoordinates)

/-- Equal-modulus source-facing contradiction.  A locally uniform finite Darboux spectrum may
contain several competing singularities, but Vandermonde recovery fixes its set of bases and
continuity fixes the label of every concrete branch.  The compiled §103 restriction certificate
then rules out the asserted two-coordinate dependence. -/
theorem not_twoCoordinateUnitSpectrumFactorization
    (spectrumSize : ℕ) (essentialCoordinates : Orientation →L[ℂ] Essential)
    (factorization : TwoCoordinateUnitSpectrumFactorization spectrumSize essentialCoordinates) :
    False := by
  apply MovingAlgebraicBranches.not_twoParameter_movingAlgebraicFamily essentialCoordinates
  intro rotation hrotation
  exact factorization.branchConstancy_of_mem_ker
    spectrumSize essentialCoordinates rotation hrotation

/-- Differential form of Poincaré's assertion that all second-kind singular roots depend on only
two essential coordinates.  Each root has a covector on the two-dimensional essential-coordinate
space, and its derivative in an orientation direction is the pullback of that covector. -/
structure TwoCoordinateDifferentialFactorization
    (essentialCoordinates : Orientation →L[ℂ] Essential) where
  singularityDifferential :
    (point : Fin 2 → ℂ) → point ∈ finiteIntersectionPoints → Essential →L[ℂ] ℂ
  factors : ∀ (rotation : Orientation) (point : Fin 2 → ℂ)
      (hpoint : point ∈ finiteIntersectionPoints),
    branchSingularityParameterDerivative rotation point hpoint =
      singularityDifferential point hpoint (essentialCoordinates rotation)

/-- A direction in the kernel of the two essential coordinates makes every concrete singular
branch stationary to first order. -/
theorem stationarity_of_mem_ker
    (essentialCoordinates : Orientation →L[ℂ] Essential)
    (factorization : TwoCoordinateDifferentialFactorization essentialCoordinates)
    (rotation : Orientation) (hrotation : essentialCoordinates rotation = 0) :
    BranchSingularityStationarity rotation where
  derivative_eq_zero := by
    intro point hpoint
    rw [factorization.factors rotation point hpoint, hrotation]
    exact map_zero _

/-- Differential of any three selected singular roots.  Poincaré writes the determinant of a
coordinate matrix for this map on p. 329. -/
def threeRootDifferential
    (essentialCoordinates : Orientation →L[ℂ] Essential)
    (factorization : TwoCoordinateDifferentialFactorization essentialCoordinates)
    (point : Fin 3 → Fin 2 → ℂ)
    (hpoint : ∀ i, point i ∈ finiteIntersectionPoints) : Orientation →L[ℂ] Orientation :=
  (ContinuousLinearMap.pi fun i ↦
    factorization.singularityDifferential (point i) (hpoint i)).comp essentialCoordinates

/-- The three-root Jacobian in §102 vanishes because its differential factors through a
two-dimensional space. -/
theorem threeRootDifferential_det_eq_zero
    (essentialCoordinates : Orientation →L[ℂ] Essential)
    (factorization : TwoCoordinateDifferentialFactorization essentialCoordinates)
    (point : Fin 3 → Fin 2 → ℂ)
    (hpoint : ∀ i, point i ∈ finiteIntersectionPoints) :
    (threeRootDifferential essentialCoordinates factorization point hpoint).toLinearMap.det = 0 := by
  rw [LinearMap.det_eq_zero_iff_ker_ne_bot]
  have hdimension : Module.finrank ℂ Essential < Module.finrank ℂ Orientation := by
    simp
  have hkernel : LinearMap.ker essentialCoordinates.toLinearMap ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt hdimension
  obtain ⟨rotation, hrotationKernel, hrotationNonzero⟩ :=
    (LinearMap.ker essentialCoordinates.toLinearMap).ne_bot_iff.mp hkernel
  apply (LinearMap.ker
    (threeRootDifferential essentialCoordinates factorization point hpoint).toLinearMap).ne_bot_iff.mpr
  refine ⟨rotation, ?_, hrotationNonzero⟩
  have hrotationZero : essentialCoordinates rotation = 0 := hrotationKernel
  change threeRootDifferential essentialCoordinates factorization point hpoint rotation = 0
  ext i
  simp [threeRootDifferential, hrotationZero]

/-- Source-faithful §102--103 contradiction at the differential level.  A common factorization
of the singular-root differentials through two coordinates supplies a nonzero stationary
rotation; the concrete §103 branch calculation and finite certificate force it to be zero. -/
theorem not_twoCoordinateDifferentialFactorization
    (essentialCoordinates : Orientation →L[ℂ] Essential)
    (factorization : TwoCoordinateDifferentialFactorization essentialCoordinates) :
    False := by
  have hdimension : Module.finrank ℂ Essential < Module.finrank ℂ Orientation := by
    simp
  have hkernel : LinearMap.ker essentialCoordinates.toLinearMap ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt hdimension
  obtain ⟨rotation, hrotationKernel, hrotationNonzero⟩ :=
    (LinearMap.ker essentialCoordinates.toLinearMap).ne_bot_iff.mp hkernel
  have hcoordinates : essentialCoordinates rotation = 0 := hrotationKernel
  have hrotationZero : rotation = 0 :=
    rotation_eq_zero_of_branchSingularityStationarity rotation
      (stationarity_of_mem_ker essentialCoordinates factorization rotation hcoordinates)
  exact hrotationNonzero hrotationZero

end PoincareChapterVI.ChapterVISection102
