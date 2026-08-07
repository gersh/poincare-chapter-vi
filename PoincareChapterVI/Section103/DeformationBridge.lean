/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import PoincareChapterVI.Section103.RotationSource

/-!
# The differential step in Poincaré's Chapter VI, §103

Poincaré fixes two local parameters and varies a third one, denoted `γ₃`.  Under the
hypothesis inherited from §102, each singular value `z` is constant along this variation.  If
`t` denotes the corresponding point on the parametrized ellipse, differentiating

`Δ (t(γ₃), z(γ₃), γ₃) = 0`

gives his equation (2).  At a singular value the `t`-derivative of `Δ` is zero, while the
`z`-velocity is zero because `z` is constant.  The derivative in the `γ₃` direction therefore
vanishes.

This file proves that chain-rule step and packages the remaining source correspondence needed
to apply it simultaneously at the twenty-four certified intersections.  The final theorem then
uses the exact Section 103 certificate to show that the infinitesimal rotation is zero.
-/

noncomputable section

namespace PoincareChapterVI.DeformationBridge

open scoped Topology
open Filter
open AffineIntersectionCount
open RotationSource

private abbrev State := Fin 3 → ℂ
private abbrev Bivar := MvPolynomial (Fin 2) ℂ

/-- Velocity in the `t` coordinate, with `z` and `γ₃` fixed. -/
def timeVelocity (dt : ℂ) : State := ![dt, 0, 0]

/-- Unit velocity in Poincaré's varying parameter `γ₃`. -/
def parameterVelocity : State := ![0, 0, 1]

/-- The velocity of `(t(γ₃), z(γ₃), γ₃)` when the singular value `z` is fixed. -/
def fixedSingularValueVelocity (dt : ℂ) : State := ![dt, 0, 1]

theorem fixedSingularValueVelocity_eq (dt : ℂ) :
    fixedSingularValueVelocity dt = timeVelocity dt + parameterVelocity := by
  funext i
  fin_cases i <;> simp [fixedSingularValueVelocity, timeVelocity, parameterVelocity]

/-- Poincaré's differential equation (2): persistence of a singular zero, constancy of its
`z`-value, and stationarity in `t` force the parameter-direction derivative to vanish. -/
theorem parameterDerivative_eq_zero
    (delta : State → ℂ) (state : ℂ → State)
    (dDelta : State →L[ℂ] ℂ) (dt : ℂ)
    (hDelta : HasFDerivAt delta dDelta (state 0))
    (hstate : HasDerivAt state (fixedSingularValueVelocity dt) 0)
    (hpersistent : (fun γ ↦ delta (state γ)) =ᶠ[𝓝 0] (fun _ ↦ 0))
    (hstationary : dDelta (timeVelocity dt) = 0) :
    dDelta parameterVelocity = 0 := by
  have hcomposition :
      HasDerivAt (delta ∘ state) (dDelta (fixedSingularValueVelocity dt)) 0 :=
    hDelta.comp_hasDerivAt 0 hstate
  have hpersistent' :
      (delta ∘ state) =ᶠ[𝓝 0] (fun _ : ℂ ↦ (0 : ℂ)) := by
    simpa [Function.comp_def] using hpersistent
  have hzero : HasDerivAt (delta ∘ state) 0 0 :=
    (hasDerivAt_const (0 : ℂ) (0 : ℂ)).congr_of_eventuallyEq hpersistent'
  have htotal : dDelta (fixedSingularValueVelocity dt) = 0 :=
    hcomposition.unique hzero
  rw [fixedSingularValueVelocity_eq, map_add, hstationary, zero_add] at htotal
  exact htotal

/-- Data expressing Poincaré's local deformation argument at every certified finite
intersection.  There is one common variation polynomial.  At each point, `delta` is the local
distance equation, `state` follows the persistent singular point, and the last equality
identifies its `γ₃` derivative with evaluation of the variation polynomial.

The fields deliberately expose the two analytic inputs that are not consequences of the finite
certificate: persistence of each singular value and the local source-coordinate derivative.
-/
structure PersistentSingularDeformation (variation : Bivar) where
  delta : (point : Fin 2 → ℂ) → State → ℂ
  state : (point : Fin 2 → ℂ) → ℂ → State
  dDelta : (point : Fin 2 → ℂ) → State →L[ℂ] ℂ
  timeDerivative : (point : Fin 2 → ℂ) → ℂ
  delta_hasFDerivAt : ∀ point ∈ finiteIntersectionPoints,
    HasFDerivAt (delta point) (dDelta point) (state point 0)
  state_hasDerivAt : ∀ point ∈ finiteIntersectionPoints,
    HasDerivAt (state point) (fixedSingularValueVelocity (timeDerivative point)) 0
  persistent_zero : ∀ point ∈ finiteIntersectionPoints,
    (fun γ ↦ delta point (state point γ)) =ᶠ[𝓝 0] (fun _ ↦ 0)
  stationary_in_time : ∀ point ∈ finiteIntersectionPoints,
    dDelta point (timeVelocity (timeDerivative point)) = 0
  parameterDerivative_eq_eval : ∀ point ∈ finiteIntersectionPoints,
    dDelta point parameterVelocity = MvPolynomial.eval point variation

/-- Poincaré's equation (2), simultaneously at the twenty-four certified singular points. -/
theorem eval_eq_zero_of_persistentSingularDeformation
    {variation : Bivar} (deformation : PersistentSingularDeformation variation)
    (point : Fin 2 → ℂ) (hpoint : point ∈ finiteIntersectionPoints) :
    MvPolynomial.eval point variation = 0 := by
  rw [← deformation.parameterDerivative_eq_eval point hpoint]
  exact parameterDerivative_eq_zero
    (deformation.delta point) (deformation.state point) (deformation.dDelta point)
    (deformation.timeDerivative point)
    (deformation.delta_hasFDerivAt point hpoint)
    (deformation.state_hasDerivAt point hpoint)
    (deformation.persistent_zero point hpoint)
    (deformation.stationary_in_time point hpoint)

/-- The certified algebraic conclusion of the §103 deformation argument.  Once the local
analytic deformation data realizes the derivative of the physical rotation family, that
rotation must be zero. -/
theorem rotation_eq_zero_of_persistentSingularDeformation
    (rotation : Fin 3 → ℂ)
    (deformation : PersistentSingularDeformation
      (∑ axis, rotation axis • affineDirectionalPolynomial axis)) :
    rotation = 0 := by
  apply rotation_eq_zero_of_source_vanishes rotation
  intro point hpoint
  exact eval_eq_zero_of_persistentSingularDeformation deformation point hpoint

/-- The §102 dimension count joined to the §103 finite certificate.  The map
`essentialCoordinates` represents Poincaré's assertion that, after fixing the eccentricities,
the singular values depend on only two local coordinates.  Every direction in its kernel is
assumed to lift to the persistent singular deformation constructed above.  Such data are
impossible: a map from the three rotation parameters to two coordinates has a nonzero kernel,
whereas the §103 certificate forces every lifted kernel direction to be zero.

This theorem isolates precisely what remains to be supplied by the analytic singular-locus
argument: the function `deformation_of_kernel`. -/
theorem not_twoParameter_persistentSingularFamily
    (essentialCoordinates : (Fin 3 → ℂ) →L[ℂ] (Fin 2 → ℂ))
    (deformation_of_kernel : ∀ rotation,
      essentialCoordinates rotation = 0 →
        PersistentSingularDeformation
          (∑ axis, rotation axis • affineDirectionalPolynomial axis)) :
    False := by
  have hdimension :
      Module.finrank ℂ (Fin 2 → ℂ) < Module.finrank ℂ (Fin 3 → ℂ) := by
    simp
  have hkernel : LinearMap.ker essentialCoordinates.toLinearMap ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt hdimension
  obtain ⟨rotation, hrotationKernel, hrotationNonzero⟩ :=
    (LinearMap.ker essentialCoordinates.toLinearMap).ne_bot_iff.mp hkernel
  have hcoordinates : essentialCoordinates rotation = 0 := by
    exact hrotationKernel
  have hrotationZero : rotation = 0 :=
    rotation_eq_zero_of_persistentSingularDeformation rotation
      (deformation_of_kernel rotation hcoordinates)
  exact hrotationNonzero hrotationZero

end PoincareChapterVI.DeformationBridge
