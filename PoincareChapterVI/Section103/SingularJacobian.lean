/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import Mathlib.Analysis.Normed.Module.FiniteDimension
import PoincareChapterVI.Section103.SingularBranches

/-!
# Nondegeneracy of Poincaré's singular-equation Jacobian

At a solution of `Δ = 0` and `Δₜ = 0`, the derivative of

`(t,z) ↦ (Δ, Δₜ)`

has matrix

```
[  0    Δ_z  ]
[ Δ_tt  Δ_tz ] .
```

This file proves directly that the corresponding continuous linear map is invertible whenever
`Δ_z` and `Δ_tt` are nonzero.  Thus the abstract invertibility hypothesis used by
`LocalSingularSystem` reduces to Poincaré's two standard scalar nondegeneracy conditions.
-/

noncomputable section

namespace PoincareChapterVI.SingularJacobian

open SingularBranches

/-- The fiber Jacobian of `(Δ, Δₜ)` at a stationary root `Δₜ = 0`. -/
def singularFiberJacobian (deltaZ deltaTT deltaTZ : ℂ) : Fiber →L[ℂ] Equation :=
  ({ toFun := fun velocity ↦
        (deltaZ * velocity.2, deltaTT * velocity.1 + deltaTZ * velocity.2)
     map_add' := by
       intro left right
       ext <;> simp [mul_add, add_assoc, add_left_comm]
     map_smul' := by
       intro scalar velocity
       ext <;> dsimp <;> ring } : Fiber →ₗ[ℂ] Equation).toContinuousLinearMap

@[simp] theorem singularFiberJacobian_apply (deltaZ deltaTT deltaTZ : ℂ)
    (velocity : Fiber) :
    singularFiberJacobian deltaZ deltaTT deltaTZ velocity =
      (deltaZ * velocity.2, deltaTT * velocity.1 + deltaTZ * velocity.2) :=
  rfl

/-- Explicit inverse formula for the stationary singular-equation Jacobian. -/
def singularFiberJacobianEquiv (deltaZ deltaTT deltaTZ : ℂ)
    (hdeltaZ : deltaZ ≠ 0) (hdeltaTT : deltaTT ≠ 0) : Fiber ≃ₗ[ℂ] Equation where
  toFun velocity :=
    (deltaZ * velocity.2, deltaTT * velocity.1 + deltaTZ * velocity.2)
  invFun value :=
    ((value.2 - deltaTZ * (value.1 / deltaZ)) / deltaTT, value.1 / deltaZ)
  left_inv velocity := by
    ext <;> simp [hdeltaZ, hdeltaTT]
  right_inv value := by
    ext <;> dsimp
    · field_simp
    · field_simp
      ring
  map_add' left right := by
    ext <;> simp [mul_add, add_assoc, add_left_comm]
  map_smul' scalar velocity := by
    ext <;> dsimp <;> ring

/-- Nonvanishing of `Δ_z` and `Δ_tt` is sufficient for the IFT hypothesis. -/
theorem singularFiberJacobian_isInvertible (deltaZ deltaTT deltaTZ : ℂ)
    (hdeltaZ : deltaZ ≠ 0) (hdeltaTT : deltaTT ≠ 0) :
    (singularFiberJacobian deltaZ deltaTT deltaTZ).IsInvertible := by
  refine ⟨(singularFiberJacobianEquiv deltaZ deltaTT deltaTZ hdeltaZ hdeltaTT)
    |>.toContinuousLinearEquiv, ?_⟩
  apply ContinuousLinearMap.ext
  intro velocity
  rfl

end PoincareChapterVI.SingularJacobian
