/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.Section103.SingularBranches
import PoincareChapterVI.Section103.DeformationBridge

/-!
# Constructing Poincaré's §103 deformation from the singular equations

`DeformationBridge` formalizes Poincaré's differentiated equation once a persistent local
singular branch has been supplied.  This file removes that branch as an input: it constructs the
branch of `(Δ, ∂Δ/∂t) = (0,0)` by the complex implicit-function theorem in
`SingularBranches` and packages it as the physical deformation required by the certified
Section 103 contradiction.

The remaining §102 input is explicit: the singular-value component of the branch derivative
must vanish in a direction that fixes Poincaré's two alleged essential coordinates.
-/

noncomputable section

namespace PoincareChapterVI.ImplicitDeformation

open Filter
open scoped Topology
open AffineIntersectionCount
open RotationFamily
open SingularBranches
open DeformationBridge

private abbrev State := Fin 3 → ℂ

-- Keep the overlapping complex calculus instances coherent on Lean 4.33-rc2.
@[reducible] local instance (priority := 20000) complexNormedAddCommGroupForCalculus :
    NormedAddCommGroup ℂ :=
  { Complex.instNormedAddCommGroup with
    toAddCommGroup :=
      DenselyNormedField.toNontriviallyNormedField.toDivisionRing.toAddCommGroup }

@[reducible] local instance (priority := 20000) complexAddCommGroupForCalculus :
    AddCommGroup ℂ :=
  complexNormedAddCommGroupForCalculus.toAddCommGroup

attribute [local instance 20000] NormedAlgebra.toNormedSpace NormedSpace.toModule

private theorem complexAddCommGroupForCalculus_eq_field :
    complexAddCommGroupForCalculus =
      DenselyNormedField.toNontriviallyNormedField.toDivisionRing.toAddCommGroup := by
  rfl

/-- The `(t(γ₃), z(γ₃), γ₃)` state obtained from the implicit singular branch. -/
def branchState (system : LocalSingularSystem) (γ : ℂ) : State :=
  ![(system.branch γ).1, (system.branch γ).2, γ]

@[simp] theorem branchState_zero (system : LocalSingularSystem) :
    branchState system 0 = ![system.base.1, system.base.2, 0] := by
  simp [branchState]

theorem timeVelocity_eq_smul (dt : ℂ) :
    timeVelocity dt = dt • timeVelocity 1 := by
  funext i
  fin_cases i <;> simp [timeVelocity]

/-- If §102 makes the singular value stationary, the IFT branch has precisely the velocity used
in Poincaré's differential equation (2). -/
theorem branchState_hasDerivAt_of_singularValueDerivative_eq_zero
    (system : LocalSingularSystem)
    (hz : (system.branchFDeriv 1).2 = 0) :
    HasDerivAt (branchState system)
      (fixedSingularValueVelocity (system.branchFDeriv 1).1) 0 := by
  rw [hasDerivAt_pi]
  intro i
  fin_cases i
  · simpa [branchState, fixedSingularValueVelocity] using system.timeBranch_hasDerivAt
  · simpa [branchState, fixedSingularValueVelocity, hz] using
      system.singularValueBranch_hasDerivAt
  · have h := hasDerivAt_id (𝕜 := ℂ) (0 : ℂ)
    convert h using 1
    · exact complexAddCommGroupForCalculus_eq_field
    · rfl
    · funext x
      rfl
    · rfl

/-- Physical local singular systems at all twenty-four certified points.

Compared with `PhysicalPersistentSingularDeformation`, neither a branch nor persistence of its
zero is assumed.  Those are consequences of `localSystem`.  The fields here identify the first
equation with `Δ`, the second base equation with the `t` derivative of `Δ`, and the straight
parameter slice with the genuine moving-ellipse squared distance.

`singularValue_is_constant` is exactly the conclusion to be supplied by the §102
two-essential-coordinate hypothesis; its zero derivative is proved rather than assumed. -/
structure ImplicitPhysicalSingularDeformation (rotation : Fin 3 → ℂ) where
  localSystem : (point : Fin 2 → ℂ) → LocalSingularSystem
  delta : (point : Fin 2 → ℂ) → State → ℂ
  dDelta : (point : Fin 2 → ℂ) → State →L[ℂ] ℂ
  delta_hasFDerivAt : ∀ point ∈ finiteIntersectionPoints,
    HasFDerivAt (delta point) (dDelta point) (branchState (localSystem point) 0)
  firstEquation_eq_delta : ∀ point ∈ finiteIntersectionPoints,
    ∀ (γ : ℂ) (fiber : Fiber),
    ((localSystem point).system γ fiber).1 =
      delta point ![fiber.1, fiber.2, γ]
  secondEquation_eq_timeDerivative : ∀ point ∈ finiteIntersectionPoints,
    ((localSystem point).system 0 (localSystem point).base).2 =
      dDelta point (timeVelocity 1)
  singularValue_is_constant : ∀ point ∈ finiteIntersectionPoints,
    (fun γ ↦ ((localSystem point).branch γ).2) =ᶠ[𝓝 0]
      (fun _ ↦ (localSystem point).base.2)
  parameter_slice_agrees : ∀ point ∈ finiteIntersectionPoints,
    (fun γ ↦ delta point (parameterLine (branchState (localSystem point) 0) γ)) =ᶠ[𝓝 0]
      (fun γ ↦ movingAffineDistance rotation γ point)

namespace ImplicitPhysicalSingularDeformation

/-- The implicit-function construction supplies the stronger physical persistence object used
by the endgame theorem. -/
def toPhysical (rotation : Fin 3 → ℂ)
    (deformation : ImplicitPhysicalSingularDeformation rotation) :
    PhysicalPersistentSingularDeformation rotation where
  delta := deformation.delta
  state := fun point ↦ branchState (deformation.localSystem point)
  dDelta := deformation.dDelta
  timeDerivative := fun point ↦
    ((deformation.localSystem point).branchFDeriv 1).1
  delta_hasFDerivAt := deformation.delta_hasFDerivAt
  state_hasDerivAt := by
    intro point hpoint
    exact branchState_hasDerivAt_of_singularValueDerivative_eq_zero
      (deformation.localSystem point)
      ((deformation.localSystem point)
        |>.singularValueBranch_derivative_eq_zero_of_eventually_constant
          (deformation.singularValue_is_constant point hpoint))
  persistent_zero := by
    intro point hpoint
    filter_upwards [(deformation.localSystem point).eventually_firstEquation_eq_zero]
      with γ hγ
    change deformation.delta point
      ![((deformation.localSystem point).branch γ).1,
        ((deformation.localSystem point).branch γ).2, γ] = 0
    rw [← deformation.firstEquation_eq_delta point hpoint γ
      ((deformation.localSystem point).branch γ)]
    exact hγ
  stationary_in_time := by
    intro point hpoint
    let dt := ((deformation.localSystem point).branchFDeriv 1).1
    have hbase : ((deformation.localSystem point).system 0
        (deformation.localSystem point).base).2 = 0 := by
      rw [(deformation.localSystem point).base_is_singular]
      rfl
    have hone : deformation.dDelta point (timeVelocity 1) = 0 := by
      rw [← deformation.secondEquation_eq_timeDerivative point hpoint]
      exact hbase
    rw [timeVelocity_eq_smul dt, map_smul, hone, smul_zero]
  parameter_slice_agrees := deformation.parameter_slice_agrees

/-- Source-faithful §103 conclusion with the local branches constructed, rather than supplied.
Every rotation direction compatible with the §102 constancy claim is zero. -/
theorem rotation_eq_zero (rotation : Fin 3 → ℂ)
    (deformation : ImplicitPhysicalSingularDeformation rotation) :
    rotation = 0 :=
  rotation_eq_zero_of_physicalPersistentSingularDeformation rotation
    (deformation.toPhysical rotation)

end ImplicitPhysicalSingularDeformation

end PoincareChapterVI.ImplicitDeformation
