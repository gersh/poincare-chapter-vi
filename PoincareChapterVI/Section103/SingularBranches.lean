/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.ImplicitFunction.Bivariate
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Local branches of the Section 103 singular equations

In §§102--103 Poincaré follows a root of

`Δ = 0,    ∂Δ/∂t = 0`

while a third orbital parameter varies.  The differentiation in §103 is justified only after
such a root has been shown to lie on a local branch.  This file supplies that step using the
complex implicit-function theorem.

The fiber is the pair `(t,z)`, the value is the pair `(Δ, ∂Δ/∂t)`, and the external variable is
Poincaré's `γ₃`.  The sole local nondegeneracy assumption is invertibility of the fiber
Jacobian.  At a singular point its determinant has the familiar form
`-(∂Δ/∂z) * (∂²Δ/∂t²)`; identifying and proving those two scalar factors nonzero for the
physical equations is kept separate from the general analytic theorem proved here.
-/

noncomputable section

namespace PoincareChapterVI.SingularBranches

open Filter
open scoped Topology

/-- The two unknowns in Poincaré's singular equations: time `t` and singular value `z`. -/
abbrev Fiber := ℂ × ℂ

/-- The two equations `(Δ, ∂Δ/∂t)`. -/
abbrev Equation := ℂ × ℂ

/-- Local differentiability data for the coupled singular equations.

The hypotheses are stated on a neighbourhood, rather than merely at the base point, because
that is the exact regularity needed by Mathlib's implicit-function theorem. -/
structure LocalSingularSystem where
  system : ℂ → Fiber → Equation
  base : Fiber
  parameterDerivative : ℂ → Fiber → ℂ →L[ℂ] Equation
  fiberDerivative : ℂ → Fiber → Fiber →L[ℂ] Equation
  hasFDerivAt_parameter :
    ∀ᶠ point in 𝓝 ((0 : ℂ), base),
      HasFDerivAt (system · point.2)
        (parameterDerivative point.1 point.2) point.1
  hasFDerivAt_fiber :
    ∀ᶠ point in 𝓝 ((0 : ℂ), base),
      HasFDerivAt (system point.1 ·)
        (fiberDerivative point.1 point.2) point.2
  continuousAt_parameterDerivative :
    ContinuousAt (Function.uncurry parameterDerivative) (0, base)
  continuousAt_fiberDerivative :
    ContinuousAt (Function.uncurry fiberDerivative) (0, base)
  fiberDerivative_isInvertible : (fiberDerivative 0 base).IsInvertible
  base_is_singular : system 0 base = 0

namespace LocalSingularSystem

/-- The branch selected by the implicit-function theorem. -/
def branch (data : LocalSingularSystem) : ℂ → Fiber :=
  implicitFunctionOfBivariate
    data.hasFDerivAt_parameter data.hasFDerivAt_fiber
    data.continuousAt_parameterDerivative data.continuousAt_fiberDerivative
    data.fiberDerivative_isInvertible

/-- The derivative prescribed by the implicit-function theorem. -/
def branchFDeriv (data : LocalSingularSystem) : ℂ →L[ℂ] Fiber :=
  -(data.fiberDerivative 0 data.base).inverse ∘L
    data.parameterDerivative 0 data.base

/-- The constructed branch passes through the specified singular point. -/
@[simp] theorem branch_zero (data : LocalSingularSystem) :
    data.branch 0 = data.base := by
  have h := eventually_apply_eq_iff_implicitFunctionOfBivariate
    data.hasFDerivAt_parameter data.hasFDerivAt_fiber
    data.continuousAt_parameterDerivative data.continuousAt_fiberDerivative
    data.fiberDerivative_isInvertible
  exact (h.self_of_nhds.mp rfl)

/-- Both equations persist along the branch on a neighbourhood of `γ₃ = 0`. -/
theorem eventually_system_branch_eq_zero (data : LocalSingularSystem) :
    (fun γ ↦ data.system γ (data.branch γ)) =ᶠ[𝓝 0] (fun _ ↦ 0) := by
  have h := eventually_apply_implicitFunctionOfBivariate
    data.hasFDerivAt_parameter data.hasFDerivAt_fiber
    data.continuousAt_parameterDerivative data.continuousAt_fiberDerivative
    data.fiberDerivative_isInvertible
  change ∀ᶠ γ in 𝓝 0, data.system γ (data.branch γ) = 0
  simpa only [branch, data.base_is_singular] using h

/-- Strict derivative of the whole `(t,z)` branch. -/
theorem branch_hasStrictFDerivAt (data : LocalSingularSystem) :
    HasStrictFDerivAt data.branch data.branchFDeriv 0 := by
  simpa [branch, branchFDeriv] using
    hasStrictFDerivAt_implicitFunctionOfBivariate
      data.hasFDerivAt_parameter data.hasFDerivAt_fiber
      data.continuousAt_parameterDerivative data.continuousAt_fiberDerivative
      data.fiberDerivative_isInvertible

/-- Ordinary one-variable derivative of the whole `(t,z)` branch. -/
theorem branch_hasDerivAt (data : LocalSingularSystem) :
    HasDerivAt data.branch (data.branchFDeriv 1) 0 :=
  data.branch_hasStrictFDerivAt.hasFDerivAt.hasDerivAt

/-- The time component of the branch has the first component of the IFT derivative. -/
theorem timeBranch_hasDerivAt (data : LocalSingularSystem) :
    HasDerivAt (fun γ ↦ (data.branch γ).1) (data.branchFDeriv 1).1 0 :=
  data.branch_hasDerivAt.fst

/-- The singular-value component of the branch has the second component of the IFT derivative. -/
theorem singularValueBranch_hasDerivAt (data : LocalSingularSystem) :
    HasDerivAt (fun γ ↦ (data.branch γ).2) (data.branchFDeriv 1).2 0 :=
  data.branch_hasDerivAt.snd

/-- Poincaré's §102 assertion that the singular value does not vary implies that the
singular-value component of the IFT derivative is zero. -/
theorem singularValueBranch_derivative_eq_zero_of_eventually_constant
    (data : LocalSingularSystem)
    (hconstant : (fun γ ↦ (data.branch γ).2) =ᶠ[𝓝 0]
      (fun _ ↦ data.base.2)) :
    (data.branchFDeriv 1).2 = 0 := by
  have hzero : HasDerivAt (fun _ : ℂ ↦ data.base.2) 0 0 :=
    hasDerivAt_const (0 : ℂ) data.base.2
  exact data.singularValueBranch_hasDerivAt.unique
    (hzero.congr_of_eventuallyEq hconstant)

/-- The first equation `Δ = 0` persists along the constructed branch. -/
theorem eventually_firstEquation_eq_zero (data : LocalSingularSystem) :
    (fun γ ↦ (data.system γ (data.branch γ)).1) =ᶠ[𝓝 0] (fun _ ↦ 0) := by
  filter_upwards [data.eventually_system_branch_eq_zero] with γ hγ
  rw [hγ]
  rfl

/-- The second equation `∂Δ/∂t = 0` persists along the constructed branch. -/
theorem eventually_secondEquation_eq_zero (data : LocalSingularSystem) :
    (fun γ ↦ (data.system γ (data.branch γ)).2) =ᶠ[𝓝 0] (fun _ ↦ 0) := by
  filter_upwards [data.eventually_system_branch_eq_zero] with γ hγ
  rw [hγ]
  rfl

end LocalSingularSystem

end PoincareChapterVI.SingularBranches
