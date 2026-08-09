/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import Mathlib.Analysis.Fourier.AddCircleMulti
import PoincareChapterVI.ChapterVISection102

/-!
# Chapter V no. 85: extraction of the first-order Fourier equations

Poincare's equation (13) is obtained by applying a Fourier-coefficient functional to one
function-level first-order Poisson equation.  This file carries out that analytic extraction on
the genuine two-dimensional unit additive torus using Mathlib's `UnitAddTorus.mFourierCoeff`.

The source-facing model records the three standard differentiation/interchange statements:
the resonant angle derivative multiplies the selected coefficient by its mode index, and the
orbital directional derivative commutes with coefficient extraction.  From one pointwise
homological identity Lean derives all six pre-resonance equations and constructs the
`ChapterVNo85ResonantFirstOrderData` consumed by the rank argument.  Thus the six equations are
no longer independent hypotheses.
-/

noncomputable section

open MeasureTheory

namespace PoincareChapterVI.ChapterVNo85FourierExtraction

open ChapterVISection102

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

private abbrev TwoTorus := UnitAddTorus (Fin 2)
private abbrev TorusFunction := TwoTorus → ℂ
private abbrev Mode := Fin 2 → ℤ
private abbrev FiveOrbitalParameters := (Fin 2 → ℂ) × (Fin 3 → ℂ)

private theorem integrable_mFourier_mul
    (mode : Mode) {f : TorusFunction} (hf : Integrable f) :
    Integrable (fun point ↦ UnitAddTorus.mFourier (-mode) point * f point) := by
  apply hf.bdd_mul (c := 1)
  · exact (UnitAddTorus.mFourier (-mode)).continuous.aestronglyMeasurable
  · filter_upwards with point
    simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, norm_prod,
      fourier_apply, Circle.norm_coe, Finset.prod_const_one, le_refl]

/-- Fourier coefficient extraction is linear on integrable two-torus functions.  This is the
analytic step used to pass from the function-level Poisson equation to one mode equation. -/
theorem mFourierCoeff_linear_combination
    (mode : Mode) (S T : ℂ)
    (anglePerturbation angleIntegral orbitalDerivative : TorusFunction)
    (hPerturbation : Integrable anglePerturbation)
    (hIntegral : Integrable angleIntegral)
    (hOrbital : Integrable orbitalDerivative) :
    UnitAddTorus.mFourierCoeff
        (fun point ↦ -S * anglePerturbation point +
          T * angleIntegral point + orbitalDerivative point) mode =
      -S * UnitAddTorus.mFourierCoeff anglePerturbation mode +
        T * UnitAddTorus.mFourierCoeff angleIntegral mode +
        UnitAddTorus.mFourierCoeff orbitalDerivative mode := by
  unfold UnitAddTorus.mFourierCoeff
  simp only [smul_eq_mul, mul_add]
  let A : TorusFunction := fun point ↦
    -S * (UnitAddTorus.mFourier (-mode) point * anglePerturbation point)
  let B : TorusFunction := fun point ↦
    T * (UnitAddTorus.mFourier (-mode) point * angleIntegral point)
  let C : TorusFunction := fun point ↦
    UnitAddTorus.mFourier (-mode) point * orbitalDerivative point
  have hA : Integrable A :=
    (integrable_mFourier_mul mode hPerturbation).const_mul (-S)
  have hB : Integrable B :=
    (integrable_mFourier_mul mode hIntegral).const_mul T
  have hC : Integrable C := integrable_mFourier_mul mode hOrbital
  calc
    (∫ point, UnitAddTorus.mFourier (-mode) point * (-S * anglePerturbation point) +
        UnitAddTorus.mFourier (-mode) point * (T * angleIntegral point) +
        UnitAddTorus.mFourier (-mode) point * orbitalDerivative point) =
        ∫ point, (A point + B point) + C point := by
          apply integral_congr_ae
          filter_upwards with point
          dsimp [A, B, C]
          ring
    _ = (∫ point, A point + B point) + ∫ point, C point :=
      integral_add (hA.add hB) hC
    _ = ((∫ point, A point) + ∫ point, B point) + ∫ point, C point := by
      rw [integral_add hA hB]
    _ = ((-S * ∫ point, UnitAddTorus.mFourier (-mode) point * anglePerturbation point) +
        T * ∫ point, UnitAddTorus.mFourier (-mode) point * angleIntegral point) +
        ∫ point, UnitAddTorus.mFourier (-mode) point * orbitalDerivative point := by
      dsimp [A, B, C]
      rw [integral_const_mul, integral_const_mul]

/-- Applying the actual multivariate Fourier coefficient to a pointwise first-order equation
gives the corresponding coefficient equation. -/
theorem mFourierCoeff_firstOrderEquation
    (mode : Mode) (S T : ℂ)
    (anglePerturbation angleIntegral orbitalDerivative : TorusFunction)
    (hPerturbation : Integrable anglePerturbation)
    (hIntegral : Integrable angleIntegral)
    (hOrbital : Integrable orbitalDerivative)
    (hequation : ∀ point,
      -S * anglePerturbation point + T * angleIntegral point +
        orbitalDerivative point = 0) :
    -S * UnitAddTorus.mFourierCoeff anglePerturbation mode +
        T * UnitAddTorus.mFourierCoeff angleIntegral mode +
        UnitAddTorus.mFourierCoeff orbitalDerivative mode = 0 := by
  rw [← mFourierCoeff_linear_combination mode S T anglePerturbation angleIntegral
    orbitalDerivative hPerturbation hIntegral hOrbital]
  have hzero : (fun point ↦ -S * anglePerturbation point +
      T * angleIntegral point + orbitalDerivative point) = fun _ ↦ 0 := by
    funext point
    exact hequation point
  rw [hzero]
  simp [UnitAddTorus.mFourierCoeff]

/-- The analytic Chapter V input before selecting Fourier modes.  There is one pointwise
first-order equation.  The multiplier fields are precisely the usual Fourier rules for the
resonant angle derivative and differentiation under the orbital-parameter integral. -/
structure UniformIntegralFirstOrderTorusModel where
  headIndex : ℕ
  tailIndex : Fin 5 → ℕ
  headMode : Mode
  tailMode : Fin 5 → Mode
  ζ : ℂ
  ζ_ne_zero : ζ ≠ 0
  S : ℂ
  T : ℂ
  perturbation : TorusFunction
  integralFirstOrder : TorusFunction
  resonantAngleDerivativePerturbation : TorusFunction
  resonantAngleDerivativeIntegral : TorusFunction
  orbitalDirectionalDerivative : TorusFunction
  integrable_perturbation : Integrable perturbation
  integrable_integralFirstOrder : Integrable integralFirstOrder
  integrable_anglePerturbation : Integrable resonantAngleDerivativePerturbation
  integrable_angleIntegral : Integrable resonantAngleDerivativeIntegral
  integrable_orbitalDerivative : Integrable orbitalDirectionalDerivative
  firstOrderPoissonEquation : ∀ point,
    -S * resonantAngleDerivativePerturbation point +
      T * resonantAngleDerivativeIntegral point +
      orbitalDirectionalDerivative point = 0
  headDerivative : FiveOrbitalParameters →ₗ[ℂ] ℂ
  tailDerivative : Fin 5 → FiveOrbitalParameters →ₗ[ℂ] ℂ
  secularDirection : FiveOrbitalParameters
  head_perturbation_multiplier :
    UnitAddTorus.mFourierCoeff resonantAngleDerivativePerturbation headMode =
      (headIndex : ℂ) * UnitAddTorus.mFourierCoeff perturbation headMode
  tail_perturbation_multiplier : ∀ i,
    UnitAddTorus.mFourierCoeff resonantAngleDerivativePerturbation (tailMode i) =
      (tailIndex i : ℂ) * UnitAddTorus.mFourierCoeff perturbation (tailMode i)
  head_integral_multiplier :
    UnitAddTorus.mFourierCoeff resonantAngleDerivativeIntegral headMode =
      (headIndex : ℂ) * UnitAddTorus.mFourierCoeff integralFirstOrder headMode
  tail_integral_multiplier : ∀ i,
    UnitAddTorus.mFourierCoeff resonantAngleDerivativeIntegral (tailMode i) =
      (tailIndex i : ℂ) * UnitAddTorus.mFourierCoeff integralFirstOrder (tailMode i)
  head_orbital_interchange :
    UnitAddTorus.mFourierCoeff orbitalDirectionalDerivative headMode =
      headDerivative secularDirection
  tail_orbital_interchange : ∀ i,
    UnitAddTorus.mFourierCoeff orbitalDirectionalDerivative (tailMode i) =
      tailDerivative i secularDirection
  resonance12bis : T = 0
  independentAtResonance : S ≠ 0 ∨ secularDirection ≠ 0

namespace UniformIntegralFirstOrderTorusModel

def headCoefficient (model : UniformIntegralFirstOrderTorusModel) : ℂ :=
  UnitAddTorus.mFourierCoeff model.perturbation model.headMode

def tailCoefficient (model : UniformIntegralFirstOrderTorusModel) (i : Fin 5) : ℂ :=
  UnitAddTorus.mFourierCoeff model.perturbation (model.tailMode i)

def headIntegralCoefficient (model : UniformIntegralFirstOrderTorusModel) : ℂ :=
  UnitAddTorus.mFourierCoeff model.integralFirstOrder model.headMode

def tailIntegralCoefficient
    (model : UniformIntegralFirstOrderTorusModel) (i : Fin 5) : ℂ :=
  UnitAddTorus.mFourierCoeff model.integralFirstOrder (model.tailMode i)

theorem headFirstOrderCoefficient (model : UniformIntegralFirstOrderTorusModel) :
    -model.headCoefficient * (model.headIndex : ℂ) * model.S +
        model.headIntegralCoefficient * (model.headIndex : ℂ) * model.T +
        model.headDerivative model.secularDirection = 0 := by
  have h := mFourierCoeff_firstOrderEquation model.headMode model.S model.T
    model.resonantAngleDerivativePerturbation
    model.resonantAngleDerivativeIntegral model.orbitalDirectionalDerivative
    model.integrable_anglePerturbation model.integrable_angleIntegral
    model.integrable_orbitalDerivative model.firstOrderPoissonEquation
  rw [model.head_perturbation_multiplier, model.head_integral_multiplier,
    model.head_orbital_interchange] at h
  unfold headCoefficient headIntegralCoefficient
  linear_combination h

theorem tailFirstOrderCoefficient
    (model : UniformIntegralFirstOrderTorusModel) (i : Fin 5) :
    -model.tailCoefficient i * (model.tailIndex i : ℂ) * model.S +
        model.tailIntegralCoefficient i * (model.tailIndex i : ℂ) * model.T +
        model.tailDerivative i model.secularDirection = 0 := by
  have h := mFourierCoeff_firstOrderEquation (model.tailMode i) model.S model.T
    model.resonantAngleDerivativePerturbation
    model.resonantAngleDerivativeIntegral model.orbitalDirectionalDerivative
    model.integrable_anglePerturbation model.integrable_angleIntegral
    model.integrable_orbitalDerivative model.firstOrderPoissonEquation
  rw [model.tail_perturbation_multiplier i, model.tail_integral_multiplier i,
    model.tail_orbital_interchange i] at h
  unfold tailCoefficient tailIntegralCoefficient
  linear_combination h

/-- One full torus-level uniform-integral model constructs the exact finite first-order data used
in §102.  In particular, the head and five tail equations are consequences of one Poisson
identity and actual Fourier integration. -/
def toResonantFirstOrderData (model : UniformIntegralFirstOrderTorusModel) :
    ChapterVNo85ResonantFirstOrderData where
  headIndex := model.headIndex
  tailIndex := model.tailIndex
  ζ := model.ζ
  ζ_ne_zero := model.ζ_ne_zero
  S := model.S
  T := model.T
  headCoefficient := model.headCoefficient
  tailCoefficient := model.tailCoefficient
  headIntegralCoefficient := model.headIntegralCoefficient
  tailIntegralCoefficient := model.tailIntegralCoefficient
  headDerivative := model.headDerivative
  tailDerivative := model.tailDerivative
  secularDirection := model.secularDirection
  headFirstOrderCoefficient := model.headFirstOrderCoefficient
  tailFirstOrderCoefficient := model.tailFirstOrderCoefficient
  resonance12bis := model.resonance12bis
  independentAtResonance := model.independentAtResonance

def characteristicEquation (model : UniformIntegralFirstOrderTorusModel) :
    ChapterVNo85CharacteristicEquation
      (chapterVNo85SixCoefficientDifferential model.headIndex model.tailIndex model.ζ
        model.headCoefficient model.tailCoefficient model.headDerivative
        model.tailDerivative) :=
  model.toResonantFirstOrderData.characteristicEquation

theorem scaled_rank_le_five (model : UniformIntegralFirstOrderTorusModel) :
    Module.finrank ℂ (LinearMap.range
      (chapterVNo85SixCoefficientDifferential model.headIndex model.tailIndex model.ζ
        model.headCoefficient model.tailCoefficient model.headDerivative
        model.tailDerivative)) ≤ 5 :=
  scaled_rank_le_five_of_chapterVNo85_resonantFirstOrderData
    model.toResonantFirstOrderData

end UniformIntegralFirstOrderTorusModel

end PoincareChapterVI.ChapterVNo85FourierExtraction
