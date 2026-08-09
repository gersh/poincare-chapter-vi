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
Darboux leading term.  It also records the exact differential content of Chapter V, no. 85,
equation (13 bis): one nonzero characteristic direction annihilates every selected `D_λ`
differential, so rank--nullity bounds the six coefficients by five parameters.  Constructing the
characteristic equation from the putative uniform integral and identifying its `D_λ` with the
contour coefficients remain the historical analytic input.

-/

noncomputable section

namespace PoincareChapterVI.ChapterVISection102

open AffineIntersectionCount
open MovingAlgebraicBranches
open Asymptotics Filter

private abbrev Orientation := Fin 3 → ℂ
private abbrev Essential := Fin 2 → ℂ
private abbrev Eccentricity := Fin 2 → ℂ
private abbrev FiveOrbitalParameters := Eccentricity × Orientation
private abbrev FourRatioParameters := Fin 4 → ℂ
private abbrev FiveRatioValues := Fin 5 → ℂ
private abbrev SixScaledSingularityValues := ℂ × FiveRatioValues
private abbrev FiniteSingularPoint :=
  { point : Fin 2 → ℂ // point ∈ finiteIntersectionPoints }

/-! ## Poincare's five-to-four-to-two rank reduction -/

/-- Infinitesimal passage from six singularity values to the five ratios with the first value
as denominator.  In logarithmic coordinates this is simply subtraction of the common first
coordinate.  It is the differential of Poincare's passage from
`(λα₀, λα₁, ..., λα₅)` to `(α₁/α₀, ..., α₅/α₀)` on p. 327. -/
def singularityRatioDifferential :
    SixScaledSingularityValues →ₗ[ℂ] FiveRatioValues where
  toFun value := fun i ↦ value.2 i - value.1
  map_add' left right := by
    ext i
    simp
    ring
  map_smul' scalar value := by
    ext i
    simp
    ring

/-- The common logarithmic scale direction of all six singularities. -/
def commonSingularityScaleDirection : SixScaledSingularityValues :=
  (1, fun _ ↦ 1)

@[simp] theorem singularityRatioDifferential_commonScale :
    singularityRatioDifferential commonSingularityScaleDirection = 0 := by
  ext i
  simp [singularityRatioDifferential, commonSingularityScaleDirection]

theorem commonSingularityScaleDirection_ne_zero :
    commonSingularityScaleDirection ≠ 0 := by
  intro h
  have := congrArg Prod.fst h
  norm_num [commonSingularityScaleDirection] at this

/-- Differential form of Poincaré's Chapter V, no. 85, equation (13 bis).  The displayed
first-order equation says that the same characteristic direction

`(H, ∂Φ0/∂uᵢ, -∂Φ0/∂zᵢ)`

annihilates every coefficient `D_λ`.  The alternative in which this direction vanishes is the
case Poincaré excludes by independence of the putative uniform integral.  Unlike an output-side
relation among six coefficient values, this is the literal domain-kernel statement printed in
(13 bis). -/
structure ChapterVNo85CharacteristicEquation
    (coefficientDifferential :
      (ℂ × FiveOrbitalParameters) →ₗ[ℂ] SixScaledSingularityValues) where
  characteristicDirection : ℂ × FiveOrbitalParameters
  characteristicDirection_ne_zero : characteristicDirection ≠ 0
  equation13bis : coefficientDifferential characteristicDirection = 0

/-! ### The no. 85 Fourier calculation and the printed normalization error

For a resonant Fourier mode `(m₁,m₂) = λ(p,q)`, equation (13) on p. 247 says

`dBλ(XΦ) = λ Bλ S`,

where `S = p ∂Φ₀/∂x₁ + q ∂Φ₀/∂x₂` and
`XΦ = (∂Φ₀/∂uᵢ, -∂Φ₀/∂zᵢ)`.  If
`Dλ = Bλ ζ^λ`, its differential in the `(ζ,z,u)` variables is the map below.

There is a genuine typographical normalization error in the 1892 text.  The displayed
definition `-ζ H = S` does not imply (13 bis).  Direct substitution requires `H = -ζ S`.
The two following theorems make both the repaired cancellation and the failure of the printed
normalization kernel-checkable rather than silently correcting the source.
-/

/-- Differential of one rescaled Fourier coefficient `Dλ = Bλ ζ^λ`, with the derivative of
`Bλ` supplied as a linear map on the five fixed-axis orbital variables.  Natural exponents are
enough for the six positive coefficients used in §102. -/
def chapterVNo85CoefficientDifferential
    (modeIndex : ℕ) (ζ B : ℂ) (dB : FiveOrbitalParameters →ₗ[ℂ] ℂ) :
    (ℂ × FiveOrbitalParameters) →ₗ[ℂ] ℂ where
  toFun direction :=
    (modeIndex : ℂ) * B * ζ ^ (modeIndex - 1) * direction.1 +
      ζ ^ modeIndex * dB direction.2
  map_add' left right := by
    simp only [Prod.fst_add, Prod.snd_add, map_add]
    ring
  map_smul' scalar direction := by
    simp only [Prod.smul_fst, Prod.smul_snd, RingHom.id_apply, map_smul]
    ring

/-- The six selected `Dλ` differentials, packaged in the output coordinates already used by
the §102 rank chain. -/
def chapterVNo85SixCoefficientDifferential
    (headIndex : ℕ) (tailIndex : Fin 5 → ℕ) (ζ headCoefficient : ℂ)
    (tailCoefficient : Fin 5 → ℂ)
    (headDerivative : FiveOrbitalParameters →ₗ[ℂ] ℂ)
    (tailDerivative : Fin 5 → FiveOrbitalParameters →ₗ[ℂ] ℂ) :
    (ℂ × FiveOrbitalParameters) →ₗ[ℂ] SixScaledSingularityValues where
  toFun direction :=
    (chapterVNo85CoefficientDifferential headIndex ζ headCoefficient headDerivative direction,
      fun i ↦ chapterVNo85CoefficientDifferential (tailIndex i) ζ
        (tailCoefficient i) (tailDerivative i) direction)
  map_add' left right := by
    ext i <;> simp [chapterVNo85CoefficientDifferential] <;> ring
  map_smul' scalar direction := by
    ext i <;> simp [chapterVNo85CoefficientDifferential]

private theorem chapterVNo85CoefficientDifferential_corrected_direction
    (modeIndex : ℕ) (ζ B S : ℂ) (dB : FiveOrbitalParameters →ₗ[ℂ] ℂ)
    (secularDirection : FiveOrbitalParameters)
    (equation13 : dB secularDirection = (modeIndex : ℂ) * B * S) :
    chapterVNo85CoefficientDifferential modeIndex ζ B dB
      (-ζ * S, secularDirection) = 0 := by
  cases modeIndex with
  | zero => simpa [chapterVNo85CoefficientDifferential] using equation13
  | succ index =>
      change ((index + 1 : ℕ) : ℂ) * B * ζ ^ index * (-ζ * S) +
        ζ ^ (index + 1) * dB secularDirection = 0
      rw [equation13, pow_succ]
      push_cast
      ring

/-- Source-corrected derivation of equation (13 bis) from the six resonant first-order Fourier
coefficient identities.  The only extra premise is exactly Poincaré's exclusion of his first
alternative: the characteristic vector must not vanish. -/
def chapterVNo85CharacteristicEquation_of_firstOrderFourierIdentities
    (headIndex : ℕ) (tailIndex : Fin 5 → ℕ) (ζ S headCoefficient : ℂ)
    (tailCoefficient : Fin 5 → ℂ)
    (headDerivative : FiveOrbitalParameters →ₗ[ℂ] ℂ)
    (tailDerivative : Fin 5 → FiveOrbitalParameters →ₗ[ℂ] ℂ)
    (secularDirection : FiveOrbitalParameters)
    (headEquation13 :
      headDerivative secularDirection = (headIndex : ℂ) * headCoefficient * S)
    (tailEquation13 : ∀ i,
      tailDerivative i secularDirection = (tailIndex i : ℂ) * tailCoefficient i * S)
    (characteristicDirection_ne_zero :
      (-ζ * S, secularDirection) ≠ (0 : ℂ × FiveOrbitalParameters)) :
    ChapterVNo85CharacteristicEquation
      (chapterVNo85SixCoefficientDifferential headIndex tailIndex ζ headCoefficient
        tailCoefficient headDerivative tailDerivative) where
  characteristicDirection := (-ζ * S, secularDirection)
  characteristicDirection_ne_zero := characteristicDirection_ne_zero
  equation13bis := by
    ext i
    · exact chapterVNo85CoefficientDifferential_corrected_direction
        headIndex ζ headCoefficient S headDerivative secularDirection headEquation13
    · exact chapterVNo85CoefficientDifferential_corrected_direction
        (tailIndex i) ζ (tailCoefficient i) S (tailDerivative i) secularDirection
        (tailEquation13 i)

/-- A rational counterexample to the normalization printed on p. 247.  Here `λ=1`, `ζ=2`,
`B=S=1`, and the secular derivative is the first-coordinate projection evaluated on its unit
vector. Equation (13) holds, but the printed direction `H=-S/ζ` gives residual `3/2`, not zero.
This proves that the displayed definition `-ζH=S` cannot literally yield (13 bis). -/
theorem chapterVNo85_printed_normalization_counterexample :
    let dB : FiveOrbitalParameters →ₗ[ℂ] ℂ :=
      { toFun := fun parameter ↦ parameter.1 0
        map_add' := by intro left right; simp
        map_smul' := by intro scalar parameter; simp }
    let secularDirection : FiveOrbitalParameters := (fun _ ↦ 1, fun _ ↦ 0)
    dB secularDirection = 1 ∧
      chapterVNo85CoefficientDifferential 1 2 1 dB (-(1 / 2), secularDirection) ≠ 0 := by
  dsimp
  constructor
  · simp
  · norm_num [chapterVNo85CoefficientDifferential]

/-- The source-facing finite algebra extracted from the first-order Poisson equation on
pp. 246--247.  Before imposing resonance, the coefficient of the Fourier mode
`λ(p y₁ + q y₂)` is

`-Bλ λ S + Cλ λ T + dBλ(XΦ) = 0`.

Here `T = p ∂F₀/∂x₁ + q ∂F₀/∂x₂`; equation (12 bis) is `T=0`.  The last field is the pointwise
independence condition excluding Poincaré's first alternative.  It is stated as
`S ≠ 0 ∨ XΦ ≠ 0`, which, together with `ζ ≠ 0`, makes the corrected characteristic direction
nonzero. -/
structure ChapterVNo85ResonantFirstOrderData where
  headIndex : ℕ
  tailIndex : Fin 5 → ℕ
  ζ : ℂ
  ζ_ne_zero : ζ ≠ 0
  S : ℂ
  T : ℂ
  headCoefficient : ℂ
  tailCoefficient : Fin 5 → ℂ
  headIntegralCoefficient : ℂ
  tailIntegralCoefficient : Fin 5 → ℂ
  headDerivative : FiveOrbitalParameters →ₗ[ℂ] ℂ
  tailDerivative : Fin 5 → FiveOrbitalParameters →ₗ[ℂ] ℂ
  secularDirection : FiveOrbitalParameters
  headFirstOrderCoefficient :
    -headCoefficient * (headIndex : ℂ) * S +
        headIntegralCoefficient * (headIndex : ℂ) * T +
        headDerivative secularDirection = 0
  tailFirstOrderCoefficient : ∀ i,
    -tailCoefficient i * (tailIndex i : ℂ) * S +
        tailIntegralCoefficient i * (tailIndex i : ℂ) * T +
        tailDerivative i secularDirection = 0
  resonance12bis : T = 0
  independentAtResonance : S ≠ 0 ∨ secularDirection ≠ 0

namespace ChapterVNo85ResonantFirstOrderData

theorem headEquation13 (data : ChapterVNo85ResonantFirstOrderData) :
    data.headDerivative data.secularDirection =
      (data.headIndex : ℂ) * data.headCoefficient * data.S := by
  have h := data.headFirstOrderCoefficient
  rw [data.resonance12bis] at h
  simp only [mul_zero] at h
  linear_combination h

theorem tailEquation13 (data : ChapterVNo85ResonantFirstOrderData) (i : Fin 5) :
    data.tailDerivative i data.secularDirection =
      (data.tailIndex i : ℂ) * data.tailCoefficient i * data.S := by
  have h := data.tailFirstOrderCoefficient i
  rw [data.resonance12bis] at h
  simp only [mul_zero] at h
  linear_combination h

theorem correctedCharacteristicDirection_ne_zero
    (data : ChapterVNo85ResonantFirstOrderData) :
    (-data.ζ * data.S, data.secularDirection) ≠
      (0 : ℂ × FiveOrbitalParameters) := by
  rintro hzero
  have hfirst : -data.ζ * data.S = 0 := congrArg Prod.fst hzero
  have hsecond : data.secularDirection = 0 := congrArg Prod.snd hzero
  rcases data.independentAtResonance with hS | hX
  · exact hS (by
      apply (mul_eq_zero.mp hfirst).resolve_left
      exact neg_ne_zero.mpr data.ζ_ne_zero)
  · exact hX hsecond

/-- Complete algebraic passage from the first-order uniform-integral Fourier identity and the
resonance equation to the corrected common-kernel form of (13 bis). -/
def characteristicEquation (data : ChapterVNo85ResonantFirstOrderData) :
    ChapterVNo85CharacteristicEquation
      (chapterVNo85SixCoefficientDifferential data.headIndex data.tailIndex data.ζ
        data.headCoefficient data.tailCoefficient data.headDerivative data.tailDerivative) :=
  chapterVNo85CharacteristicEquation_of_firstOrderFourierIdentities
    data.headIndex data.tailIndex data.ζ data.S data.headCoefficient data.tailCoefficient
    data.headDerivative data.tailDerivative data.secularDirection data.headEquation13
    data.tailEquation13 data.correctedCharacteristicDirection_ne_zero

end ChapterVNo85ResonantFirstOrderData

/-- Poincaré's no. 85 statement in its equivalent parameter-count form: after the two angular
momenta have been fixed, the six selected coefficient observables factor infinitesimally through
five independent variables.  This formulation does not assume a chosen equation among the six
outputs. -/
structure ChapterVNo85FiveVariableFactorization
    (coefficientDifferential :
      (ℂ × FiveOrbitalParameters) →ₗ[ℂ] SixScaledSingularityValues) where
  fiveVariableDifferential :
    (ℂ × FiveOrbitalParameters) →ₗ[ℂ] (Fin 5 → ℂ)
  coefficientFromFiveVariables :
    (Fin 5 → ℂ) →ₗ[ℂ] SixScaledSingularityValues
  factors : coefficientDifferential =
    coefficientFromFiveVariables.comp fiveVariableDifferential

/-- Factoring the six Chapter-V observables through five variables gives the rank-five
conclusion directly, without first choosing a defining relation or a regular point of it. -/
theorem scaled_rank_le_five_of_chapterVNo85_fiveVariableFactorization
    (coefficientDifferential :
      (ℂ × FiveOrbitalParameters) →ₗ[ℂ] SixScaledSingularityValues)
    (factorization :
      ChapterVNo85FiveVariableFactorization coefficientDifferential) :
    Module.finrank ℂ coefficientDifferential.range ≤ 5 := by
  have hrange : coefficientDifferential.range ≤
      factorization.coefficientFromFiveVariables.range := by
    rintro value ⟨parameter, rfl⟩
    have hfactor := LinearMap.congr_fun factorization.factors parameter
    rw [hfactor]
    exact ⟨factorization.fiveVariableDifferential parameter, rfl⟩
  calc
    Module.finrank ℂ coefficientDifferential.range ≤
        Module.finrank ℂ factorization.coefficientFromFiveVariables.range :=
      Submodule.finrank_mono hrange
    _ ≤ Module.finrank ℂ (Fin 5 → ℂ) :=
      LinearMap.finrank_range_le _
    _ = 5 := by simp

/-- The common nonzero characteristic direction from equation (13 bis) makes the joint
differential of the six `D_λ` have rank at most five.  This is the source-faithful no. 85 to
rank-five step: it uses the kernel in the six-dimensional parameter space, not an unrelated
regular-value equation in the output space. -/
theorem scaled_rank_le_five_of_chapterVNo85_characteristicEquation
    (coefficientDifferential :
      (ℂ × FiveOrbitalParameters) →ₗ[ℂ] SixScaledSingularityValues)
    (equation : ChapterVNo85CharacteristicEquation coefficientDifferential) :
    Module.finrank ℂ coefficientDifferential.range ≤ 5 := by
  have hdirectionKernel : equation.characteristicDirection ∈
      LinearMap.ker coefficientDifferential := equation.equation13bis
  have hspan : Submodule.span ℂ {equation.characteristicDirection} ≤
      LinearMap.ker coefficientDifferential := by
    rw [Submodule.span_le]
    simpa using hdirectionKernel
  have hkernelPositive :
      1 ≤ Module.finrank ℂ (LinearMap.ker coefficientDifferential) := by
    have hspanRank : Module.finrank ℂ
        (Submodule.span ℂ {equation.characteristicDirection}) = 1 := by
      rw [finrank_span_singleton equation.characteristicDirection_ne_zero]
    rw [← hspanRank]
    exact Submodule.finrank_mono hspan
  have hrankNullity :=
    LinearMap.finrank_range_add_finrank_ker coefficientDifferential
  have hdomain : Module.finrank ℂ (ℂ × FiveOrbitalParameters) = 6 := by simp
  omega

/-- The source-facing no. 85-to-§102 result with no separate characteristic-equation premise:
the pre-resonance first-order Fourier equations, resonance (12 bis), and pointwise independence
produce the rank-five bound for the six selected rescaled coefficients. -/
theorem scaled_rank_le_five_of_chapterVNo85_resonantFirstOrderData
    (data : ChapterVNo85ResonantFirstOrderData) :
    Module.finrank ℂ
      (chapterVNo85SixCoefficientDifferential data.headIndex data.tailIndex data.ζ
        data.headCoefficient data.tailCoefficient data.headDerivative
        data.tailDerivative).range ≤ 5 :=
  scaled_rank_le_five_of_chapterVNo85_characteristicEquation _
    data.characteristicEquation

/-- Coordinate-free form of the scale-quotient argument.  It is useful when `ScaledValues`
contains the complete finite family of collision branches rather than only five selected
values. -/
theorem projectivized_rank_le_four_of_scaled_rank_le_five
    {ScaledValues RatioValues : Type*}
    [AddCommGroup ScaledValues] [Module ℂ ScaledValues]
    [AddCommGroup RatioValues] [Module ℂ RatioValues]
    (differential : (ℂ × FiveOrbitalParameters) →ₗ[ℂ] ScaledValues)
    (projectivization : ScaledValues →ₗ[ℂ] RatioValues)
    (scaleDirection : ScaledValues)
    (hscale : differential (1, 0) = scaleDirection)
    (hprojectivization : projectivization scaleDirection = 0)
    (hscaleNonzero : scaleDirection ≠ 0)
    (hrank : Module.finrank ℂ differential.range ≤ 5) :
    Module.finrank ℂ
      (projectivization.comp
        (differential.comp (LinearMap.inr ℂ ℂ FiveOrbitalParameters))).range ≤ 4 := by
  let restrictedProjectivization : differential.range →ₗ[ℂ] RatioValues :=
    projectivization.domRestrict differential.range
  let scaleInRange : differential.range :=
    ⟨scaleDirection, ⟨(1, 0), hscale⟩⟩
  have hscaleKernel :
      scaleInRange ∈ LinearMap.ker restrictedProjectivization := by
    exact hprojectivization
  have hscaleRangeNe : scaleInRange ≠ 0 := by
    intro h
    apply hscaleNonzero
    exact congrArg Subtype.val h
  have hkernelPositive :
      1 ≤ Module.finrank ℂ (LinearMap.ker restrictedProjectivization) := by
    have hspan : Submodule.span ℂ {scaleInRange} ≤
        LinearMap.ker restrictedProjectivization := by
      rw [Submodule.span_le]
      simpa using hscaleKernel
    have hspanRank : Module.finrank ℂ (Submodule.span ℂ {scaleInRange}) = 1 := by
      rw [finrank_span_singleton hscaleRangeNe]
    rw [← hspanRank]
    exact Submodule.finrank_mono hspan
  have hrankRestricted :=
    LinearMap.finrank_range_add_finrank_ker restrictedProjectivization
  have hrangeRestricted :
      Module.finrank ℂ restrictedProjectivization.range ≤ 4 := by
    omega
  refine (Submodule.finrank_mono ?_).trans hrangeRestricted
  rintro value ⟨parameter, rfl⟩
  refine ⟨⟨differential (0, parameter), ⟨(0, parameter), rfl⟩⟩, ?_⟩
  rfl

/-- Exact linear-algebra content of the first parameter reduction on pp. 326--327.  Chapter V
gives rank at most five for the six scaled singularities.  If the independent scale parameter
moves all six singularities by the same nonzero logarithmic amount, quotienting by that common
scale leaves rank at most four for the five singularity ratios.

No choice of singularity labels or analyticity claim is hidden here: `differential` is the full
six-value differential, `hscale` is Poincare's displayed `λαᵢ` scaling law, and `hrank` is the
precise differential form of the Chapter V relation among any six `Dₙ`. -/
theorem ratio_rank_le_four_of_scaled_rank_le_five
    (differential : (ℂ × FiveOrbitalParameters) →ₗ[ℂ]
      SixScaledSingularityValues)
    (hscale : differential (1, 0) = commonSingularityScaleDirection)
    (hrank : Module.finrank ℂ differential.range ≤ 5) :
    Module.finrank ℂ
      (singularityRatioDifferential.comp
        (differential.comp (LinearMap.inr ℂ ℂ FiveOrbitalParameters))).range ≤ 4 := by
  exact projectivized_rank_le_four_of_scaled_rank_le_five differential
    singularityRatioDifferential commonSingularityScaleDirection hscale
    singularityRatioDifferential_commonScale commonSingularityScaleDirection_ne_zero hrank

/-- Differential of the five ratios on p. 327, split into the two elementary first-kind
coordinates and an arbitrary family of second-kind collision roots.  The latter may also vary
with eccentricity, exactly as in Poincare's block-triangular Jacobian on p. 329. -/
def combinedRatioDifferential
    {RootValues : Type*} [AddCommGroup RootValues] [Module ℂ RootValues]
    (firstKind : Eccentricity →ₗ[ℂ] Eccentricity)
    (collisionEccentricity : Eccentricity →ₗ[ℂ] RootValues)
    (collisionOrientation : Orientation →ₗ[ℂ] RootValues) :
    FiveOrbitalParameters →ₗ[ℂ] (Eccentricity × RootValues) where
  toFun parameter :=
    (firstKind parameter.1,
      collisionEccentricity parameter.1 + collisionOrientation parameter.2)
  map_add' left right := by
    ext <;> simp <;> abel
  map_smul' scalar parameter := by simp [smul_add]

/-- Poincare's complete parameter count on pp. 327--329.  If the five singularity ratios have
differential rank at most four, while the two first-kind ratios independently recover the two
eccentricities, then the differential of *all* second-kind roots with eccentricities fixed has
rank at most two in the three orientation variables.

This theorem supplies the exact intermediate implication that was previously encoded only by
the stronger assumption `TwoCoordinateDifferentialFactorization`. -/
theorem collisionOrientation_rank_le_two_of_ratio_rank_le_four
    {RootValues : Type*} [AddCommGroup RootValues] [Module ℂ RootValues]
    [Module.Finite ℂ RootValues]
    (firstKind : Eccentricity →ₗ[ℂ] Eccentricity)
    (collisionEccentricity : Eccentricity →ₗ[ℂ] RootValues)
    (collisionOrientation : Orientation →ₗ[ℂ] RootValues)
    (hfirstKind : Function.Injective firstKind)
    (hratio : Module.finrank ℂ
      (combinedRatioDifferential firstKind collisionEccentricity
        collisionOrientation).range ≤ 4) :
    Module.finrank ℂ collisionOrientation.range ≤ 2 := by
  let combined := combinedRatioDifferential firstKind collisionEccentricity
    collisionOrientation
  have hfirst_eq_zero (parameter : LinearMap.ker combined) : parameter.1.1 = 0 := by
    have hzero := parameter.2
    have hfst := congrArg Prod.fst hzero
    change firstKind parameter.1.1 = 0 at hfst
    exact hfirstKind (hfst.trans (map_zero firstKind).symm)
  let orientationProjection : LinearMap.ker combined →ₗ[ℂ] Orientation :=
    (LinearMap.snd ℂ Eccentricity Orientation).comp
      (LinearMap.ker combined).subtype
  have horientation_mem (parameter : LinearMap.ker combined) :
      orientationProjection parameter ∈ LinearMap.ker collisionOrientation := by
    have hzero := parameter.2
    have hsnd := congrArg Prod.snd hzero
    change collisionEccentricity parameter.1.1 +
      collisionOrientation parameter.1.2 = 0 at hsnd
    rw [hfirst_eq_zero parameter, map_zero, zero_add] at hsnd
    exact hsnd
  let kernelProjection : LinearMap.ker combined →ₗ[ℂ]
      LinearMap.ker collisionOrientation :=
    LinearMap.codRestrict (LinearMap.ker collisionOrientation)
      orientationProjection horientation_mem
  have hprojection : Function.Injective kernelProjection := by
    intro left right heq
    apply Subtype.ext
    apply Prod.ext
    · rw [hfirst_eq_zero left, hfirst_eq_zero right]
    · exact congrArg (fun point : LinearMap.ker collisionOrientation ↦ point.1) heq
  have hker_le : Module.finrank ℂ (LinearMap.ker combined) ≤
      Module.finrank ℂ (LinearMap.ker collisionOrientation) :=
    kernelProjection.finrank_le_finrank_of_injective hprojection
  have hcombined := LinearMap.finrank_range_add_finrank_ker combined
  have horientation := LinearMap.finrank_range_add_finrank_ker collisionOrientation
  have hdomain : Module.finrank ℂ FiveOrbitalParameters = 5 := by simp
  have horientationDomain : Module.finrank ℂ Orientation = 3 := by simp
  change Module.finrank ℂ combined.range ≤ 4 at hratio
  rw [hdomain] at hcombined
  rw [horientationDomain] at horientation
  omega

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

/-- Exact pp. 327--329 interface to the certified §103 contradiction.  It is enough to prove
Poincare's preceding claim that the differential of the five singularity ratios has rank at
most four.  The two first-kind ratios must recover the eccentricities injectively; arbitrary
eccentricity dependence of the collision roots is allowed.  The theorem above then derives,
rather than assumes, the rank-at-most-two conclusion for all 24 concrete collision branches. -/
theorem not_ratioRankAtMostFour_of_firstKindRecovery
    (firstKind : Eccentricity →ₗ[ℂ] Eccentricity)
    (collisionEccentricity : Eccentricity →ₗ[ℂ]
      (FiniteSingularPoint → ℂ))
    (hfirstKind : Function.Injective firstKind)
    (hratio : Module.finrank ℂ
      (combinedRatioDifferential firstKind collisionEccentricity
        concreteSecondKindRootDifferential.toLinearMap).range ≤ 4) :
    False :=
  not_concreteSecondKindRootDifferential_rank_le_two
    (collisionOrientation_rank_le_two_of_ratio_rank_le_four
      firstKind collisionEccentricity
      concreteSecondKindRootDifferential.toLinearMap hfirstKind hratio)

/-- Complete differential chain from Poincare's Chapter V conclusion to the certified §103
contradiction.  The hypotheses spell out exactly the three assertions made on pp. 326--327:

* the six scaled singularities have differential rank at most five;
* changing `λ` alone moves all six values in one common nonzero scale direction;
* quotienting by that direction gives the two first-kind ratios and all concrete second-kind
  collision-root ratios.

The theorem proves both subsequent losses of dimension (five to four, then four to two); neither
is retained as a separate assumption. -/
theorem not_scaledSingularityRankAtMostFive_of_firstKindRecovery
    {ScaledValues : Type*} [AddCommGroup ScaledValues] [Module ℂ ScaledValues]
    (firstKind : Eccentricity →ₗ[ℂ] Eccentricity)
    (collisionEccentricity : Eccentricity →ₗ[ℂ]
      (FiniteSingularPoint → ℂ))
    (scaledDifferential : (ℂ × FiveOrbitalParameters) →ₗ[ℂ] ScaledValues)
    (projectivization : ScaledValues →ₗ[ℂ]
      (Eccentricity × (FiniteSingularPoint → ℂ)))
    (scaleDirection : ScaledValues)
    (hfirstKind : Function.Injective firstKind)
    (hscale : scaledDifferential (1, 0) = scaleDirection)
    (hprojectivization : projectivization scaleDirection = 0)
    (hscaleNonzero : scaleDirection ≠ 0)
    (hrank : Module.finrank ℂ scaledDifferential.range ≤ 5)
    (hratios :
      projectivization.comp
          (scaledDifferential.comp
            (LinearMap.inr ℂ ℂ FiveOrbitalParameters)) =
        combinedRatioDifferential firstKind collisionEccentricity
          concreteSecondKindRootDifferential.toLinearMap) :
    False := by
  apply not_ratioRankAtMostFour_of_firstKindRecovery
    firstKind collisionEccentricity hfirstKind
  rw [← hratios]
  exact projectivized_rank_le_four_of_scaled_rank_le_five
    scaledDifferential projectivization scaleDirection hscale
    hprojectivization hscaleNonzero hrank

/-- Source-faithful no. 85 form: equation (13 bis) supplies a common nonzero characteristic
direction annihilating the six Chapter-V coefficient observables.  Rank--nullity supplies the
rank-five premise, after which Poincaré's common-scale quotient and the certified §103 calculation
give the contradiction. -/
theorem not_chapterVNo85CharacteristicEquation_of_firstKindRecovery
    (firstKind : Eccentricity →ₗ[ℂ] Eccentricity)
    (collisionEccentricity : Eccentricity →ₗ[ℂ]
      (FiniteSingularPoint → ℂ))
    (scaledDifferential : (ℂ × FiveOrbitalParameters) →ₗ[ℂ]
      SixScaledSingularityValues)
    (equation : ChapterVNo85CharacteristicEquation scaledDifferential)
    (projectivization : SixScaledSingularityValues →ₗ[ℂ]
      (Eccentricity × (FiniteSingularPoint → ℂ)))
    (hfirstKind : Function.Injective firstKind)
    (hscale : scaledDifferential (1, 0) = commonSingularityScaleDirection)
    (hprojectivization :
      projectivization commonSingularityScaleDirection = 0)
    (hratios :
      projectivization.comp
          (scaledDifferential.comp
            (LinearMap.inr ℂ ℂ FiveOrbitalParameters)) =
        combinedRatioDifferential firstKind collisionEccentricity
          concreteSecondKindRootDifferential.toLinearMap) :
    False := by
  exact not_scaledSingularityRankAtMostFive_of_firstKindRecovery
    firstKind collisionEccentricity scaledDifferential projectivization
    commonSingularityScaleDirection hfirstKind hscale hprojectivization
    commonSingularityScaleDirection_ne_zero
    (scaled_rank_le_five_of_chapterVNo85_characteristicEquation
      scaledDifferential equation)
    hratios

/-- The complete §102--§103 contradiction starting with the source-facing, pre-resonance
first-order Fourier data.  Thus the corrected finite algebra no longer enters the endgame through
an independently assumed instance of equation (13 bis). -/
theorem not_chapterVNo85ResonantFirstOrderData_of_firstKindRecovery
    (data : ChapterVNo85ResonantFirstOrderData)
    (firstKind : Eccentricity →ₗ[ℂ] Eccentricity)
    (collisionEccentricity : Eccentricity →ₗ[ℂ]
      (FiniteSingularPoint → ℂ))
    (projectivization : SixScaledSingularityValues →ₗ[ℂ]
      (Eccentricity × (FiniteSingularPoint → ℂ)))
    (hfirstKind : Function.Injective firstKind)
    (hscale :
      chapterVNo85SixCoefficientDifferential data.headIndex data.tailIndex data.ζ
          data.headCoefficient data.tailCoefficient data.headDerivative data.tailDerivative
          (1, 0) =
        commonSingularityScaleDirection)
    (hprojectivization :
      projectivization commonSingularityScaleDirection = 0)
    (hratios :
      projectivization.comp
          ((chapterVNo85SixCoefficientDifferential data.headIndex data.tailIndex data.ζ
              data.headCoefficient data.tailCoefficient data.headDerivative
              data.tailDerivative).comp
            (LinearMap.inr ℂ ℂ FiveOrbitalParameters)) =
        combinedRatioDifferential firstKind collisionEccentricity
          concreteSecondKindRootDifferential.toLinearMap) :
    False := by
  exact not_chapterVNo85CharacteristicEquation_of_firstKindRecovery
    firstKind collisionEccentricity
    (chapterVNo85SixCoefficientDifferential data.headIndex data.tailIndex data.ζ
      data.headCoefficient data.tailCoefficient data.headDerivative data.tailDerivative)
    data.characteristicEquation projectivization hfirstKind hscale hprojectivization hratios

/-- Literal five-variable no. 85 form of the complete differential contradiction.  The sole
source-facing premise is now exactly Poincaré's claim that the six coefficient observables depend
on five variables; the five-to-four-to-two losses and the section 103 contradiction are theorems. -/
theorem not_chapterVNo85FiveVariableFactorization_of_firstKindRecovery
    (firstKind : Eccentricity →ₗ[ℂ] Eccentricity)
    (collisionEccentricity : Eccentricity →ₗ[ℂ]
      (FiniteSingularPoint → ℂ))
    (scaledDifferential : (ℂ × FiveOrbitalParameters) →ₗ[ℂ]
      SixScaledSingularityValues)
    (factorization :
      ChapterVNo85FiveVariableFactorization scaledDifferential)
    (projectivization : SixScaledSingularityValues →ₗ[ℂ]
      (Eccentricity × (FiniteSingularPoint → ℂ)))
    (hfirstKind : Function.Injective firstKind)
    (hscale : scaledDifferential (1, 0) = commonSingularityScaleDirection)
    (hprojectivization :
      projectivization commonSingularityScaleDirection = 0)
    (hratios :
      projectivization.comp
          (scaledDifferential.comp
            (LinearMap.inr ℂ ℂ FiveOrbitalParameters)) =
        combinedRatioDifferential firstKind collisionEccentricity
          concreteSecondKindRootDifferential.toLinearMap) :
    False := by
  exact not_scaledSingularityRankAtMostFive_of_firstKindRecovery
    firstKind collisionEccentricity scaledDifferential projectivization
    commonSingularityScaleDirection hfirstKind hscale hprojectivization
    commonSingularityScaleDirection_ne_zero
    (scaled_rank_le_five_of_chapterVNo85_fiveVariableFactorization
      scaledDifferential factorization)
    hratios

/-- Literal “depend on four variables” form of the preceding theorem.  A factorization of the
five ratio differentials through a four-dimensional coordinate space automatically has rank at
most four, so it is incompatible with the certified §103 collision family once the two
eccentricities are recovered by the first-kind ratios. -/
theorem not_fourParameterRatioFactorization
    (firstKind : Eccentricity →ₗ[ℂ] Eccentricity)
    (collisionEccentricity : Eccentricity →ₗ[ℂ]
      (FiniteSingularPoint → ℂ))
    (ratioCoordinates : FiveOrbitalParameters →ₗ[ℂ] FourRatioParameters)
    (ratioRecovery : FourRatioParameters →ₗ[ℂ]
      (Eccentricity × (FiniteSingularPoint → ℂ)))
    (hfirstKind : Function.Injective firstKind)
    (hfactor :
      combinedRatioDifferential firstKind collisionEccentricity
          concreteSecondKindRootDifferential.toLinearMap =
        ratioRecovery.comp ratioCoordinates) :
    False := by
  apply not_ratioRankAtMostFour_of_firstKindRecovery firstKind
    collisionEccentricity hfirstKind
  rw [hfactor]
  calc
    Module.finrank ℂ (ratioRecovery.comp ratioCoordinates).range ≤
        Module.finrank ℂ ratioRecovery.range :=
      Submodule.finrank_mono
        (LinearMap.range_comp_le_range ratioCoordinates ratioRecovery)
    _ ≤ Module.finrank ℂ FourRatioParameters :=
      LinearMap.finrank_range_le ratioRecovery
    _ = 4 := by simp

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
