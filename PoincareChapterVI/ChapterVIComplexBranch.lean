/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import Mathlib.Analysis.Complex.SqrtDeriv
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Analytic.ChangeOrigin

/-!
# Compatible square-root branches for Poincaré's prepared pinch

In Chapter VI, §99, Poincaré writes the local radicand as

`((t-h)²+k) ψ₁`.

A formal factorization alone is insufficient: the contour integrand needs a compatible analytic
square-root branch.  This file supplies the local branch construction on any domain where both
the quadratic factor and the analytic unit take values in `Complex.slitPlane`.  On such a domain,
the product of the two principal square roots is holomorphic, squares to the prepared radicand,
and has a holomorphic inverse.

`ChapterVIAnalyticPreparation.lean` applies these constructions to a convergent prepared germ and
proves correctness for its actual radicand.  The remaining source work is geometric: construct a
neighborhood of Poincaré's transported cycle on which the actual quadratic factor satisfies the
slit-plane hypothesis.
-/

noncomputable section

open Set Topology

namespace PoincareChapterVI

/-- The principal complex square root really squares to its input on the slit plane. -/
theorem Complex.sq_sqrt_of_mem_slitPlane {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    Complex.sqrt z ^ 2 = z := by
  have hz0 : z ≠ 0 := Complex.slitPlane_ne_zero hz
  rw [sqrt_eq_exp hz0, pow_two, ← Complex.exp_add]
  convert Complex.exp_log hz0 using 1
  ring_nf

/-- Consequently, the principal square root does not vanish on the slit plane. -/
theorem Complex.sqrt_ne_zero_of_mem_slitPlane {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    Complex.sqrt z ≠ 0 := by
  intro hsqrt
  have := Complex.sq_sqrt_of_mem_slitPlane hz
  rw [hsqrt, zero_pow (by norm_num)] at this
  exact Complex.slitPlane_ne_zero hz this.symm

/-- The compatible square-root branch of a prepared radicand `quadratic * unit`. -/
def chapterVIPreparedSquareRoot
    {X : Type*} (quadratic unit : X → ℂ) (x : X) : ℂ :=
  Complex.sqrt (quadratic x) * Complex.sqrt (unit x)

/-- The inverse branch occurring in the prepared local contour integrand. -/
def chapterVIPreparedInverseSquareRoot
    {X : Type*} (quadratic unit : X → ℂ) (x : X) : ℂ :=
  (chapterVIPreparedSquareRoot quadratic unit x)⁻¹

/-- Pointwise correctness of the compatible prepared square-root branch. -/
theorem chapterVIPreparedSquareRoot_sq
    {X : Type*} {quadratic unit : X → ℂ} {x : X}
    (hquadratic : quadratic x ∈ Complex.slitPlane)
    (hunit : unit x ∈ Complex.slitPlane) :
    chapterVIPreparedSquareRoot quadratic unit x ^ 2 = quadratic x * unit x := by
  rw [chapterVIPreparedSquareRoot, mul_pow,
    Complex.sq_sqrt_of_mem_slitPlane hquadratic,
    Complex.sq_sqrt_of_mem_slitPlane hunit]

/-- The prepared square-root branch is nonzero wherever both factors lie in the slit plane. -/
theorem chapterVIPreparedSquareRoot_ne_zero
    {X : Type*} {quadratic unit : X → ℂ} {x : X}
    (hquadratic : quadratic x ∈ Complex.slitPlane)
    (hunit : unit x ∈ Complex.slitPlane) :
    chapterVIPreparedSquareRoot quadratic unit x ≠ 0 := by
  exact mul_ne_zero
    (Complex.sqrt_ne_zero_of_mem_slitPlane hquadratic)
    (Complex.sqrt_ne_zero_of_mem_slitPlane hunit)

/-- The inverse branch is the product of the two inverse principal branches. -/
theorem chapterVIPreparedInverseSquareRoot_eq
    {X : Type*} (quadratic unit : X → ℂ) (x : X) :
    chapterVIPreparedInverseSquareRoot quadratic unit x =
      (Complex.sqrt (quadratic x))⁻¹ * (Complex.sqrt (unit x))⁻¹ := by
  simp [chapterVIPreparedInverseSquareRoot, chapterVIPreparedSquareRoot, mul_comm]

/-- Algebraic correctness of the inverse square-root branch. -/
theorem chapterVIPreparedInverseSquareRoot_sq_mul
    {X : Type*} {quadratic unit : X → ℂ} {x : X}
    (hquadratic : quadratic x ∈ Complex.slitPlane)
    (hunit : unit x ∈ Complex.slitPlane) :
    chapterVIPreparedInverseSquareRoot quadratic unit x ^ 2 *
        (quadratic x * unit x) = 1 := by
  rw [← chapterVIPreparedSquareRoot_sq hquadratic hunit]
  have hbranch := chapterVIPreparedSquareRoot_ne_zero hquadratic hunit
  simp [chapterVIPreparedInverseSquareRoot, hbranch]

/-- Holomorphicity of the compatible square-root branch on a common slit-plane chart. -/
theorem differentiableOn_chapterVIPreparedSquareRoot
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    {quadratic unit : X → ℂ} {s : Set X}
    (hquadratic : DifferentiableOn ℂ quadratic s)
    (hunit : DifferentiableOn ℂ unit s)
    (hquadraticMap : MapsTo quadratic s Complex.slitPlane)
    (hunitMap : MapsTo unit s Complex.slitPlane) :
    DifferentiableOn ℂ (chapterVIPreparedSquareRoot quadratic unit) s := by
  exact (Complex.differentiableOn_sqrt.fun_comp hquadratic hquadraticMap).mul
    (Complex.differentiableOn_sqrt.fun_comp hunit hunitMap)

/-- Holomorphicity of the inverse branch used by the local contour integrand. -/
theorem differentiableOn_chapterVIPreparedInverseSquareRoot
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    {quadratic unit : X → ℂ} {s : Set X}
    (hquadratic : DifferentiableOn ℂ quadratic s)
    (hunit : DifferentiableOn ℂ unit s)
    (hquadraticMap : MapsTo quadratic s Complex.slitPlane)
    (hunitMap : MapsTo unit s Complex.slitPlane) :
    DifferentiableOn ℂ (chapterVIPreparedInverseSquareRoot quadratic unit) s := by
  apply (differentiableOn_chapterVIPreparedSquareRoot
    hquadratic hunit hquadraticMap hunitMap).inv
  intro z hz
  exact chapterVIPreparedSquareRoot_ne_zero (hquadraticMap hz) (hunitMap hz)

/-- An open common branch chart for the two factors of a prepared radicand.  The protected set
may be a point, a contour, or a joint parameter-contour family. -/
structure ChapterVIPreparedBranchChart
    {X : Type*} [TopologicalSpace X]
    (quadratic unit : X → ℂ) (carrier : Set X) where
  domain : Set X
  isOpen_domain : IsOpen domain
  carrier_subset : carrier ⊆ domain
  quadratic_mapsTo : MapsTo quadratic domain Complex.slitPlane
  unit_mapsTo : MapsTo unit domain Complex.slitPlane

/-- Continuity promotes slit-plane values on the protected cycle to an open common branch chart.
No compactness assumption is needed: the intersection of the two slit-plane preimages already is
an open neighborhood of the entire protected set. -/
def ChapterVIPreparedBranchChart.of_continuous
    {X : Type*} [TopologicalSpace X]
    {quadratic unit : X → ℂ} {carrier : Set X}
    (hquadratic : Continuous quadratic) (hunit : Continuous unit)
    (hquadraticCarrier : MapsTo quadratic carrier Complex.slitPlane)
    (hunitCarrier : MapsTo unit carrier Complex.slitPlane) :
    ChapterVIPreparedBranchChart quadratic unit carrier where
  domain := quadratic ⁻¹' Complex.slitPlane ∩ unit ⁻¹' Complex.slitPlane
  isOpen_domain :=
    (Complex.isOpen_slitPlane.preimage hquadratic).inter
      (Complex.isOpen_slitPlane.preimage hunit)
  carrier_subset := fun _ hx ↦
    ⟨hquadraticCarrier hx, hunitCarrier hx⟩
  quadratic_mapsTo := fun _ hx ↦ hx.1
  unit_mapsTo := fun _ hx ↦ hx.2

/-- The inverse prepared branch is holomorphic on the automatically constructed joint chart. -/
theorem ChapterVIPreparedBranchChart.differentiableOn_inverseSquareRoot
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    {quadratic unit : X → ℂ} {carrier : Set X}
    (chart : ChapterVIPreparedBranchChart quadratic unit carrier)
    (hquadratic : Differentiable ℂ quadratic)
    (hunit : Differentiable ℂ unit) :
    DifferentiableOn ℂ (chapterVIPreparedInverseSquareRoot quadratic unit) chart.domain := by
  exact differentiableOn_chapterVIPreparedInverseSquareRoot
    hquadratic.differentiableOn hunit.differentiableOn
    chart.quadratic_mapsTo chart.unit_mapsTo

/-- Pointwise correctness of the inverse branch everywhere on a common branch chart. -/
theorem ChapterVIPreparedBranchChart.inverseSquareRoot_sq_mul
    {X : Type*} [TopologicalSpace X]
    {quadratic unit : X → ℂ} {carrier : Set X}
    (chart : ChapterVIPreparedBranchChart quadratic unit carrier)
    {x : X} (hx : x ∈ chart.domain) :
    chapterVIPreparedInverseSquareRoot quadratic unit x ^ 2 *
        (quadratic x * unit x) = 1 :=
  chapterVIPreparedInverseSquareRoot_sq_mul
    (chart.quadratic_mapsTo hx) (chart.unit_mapsTo hx)

/-- A local holomorphic square-root germ of a nonvanishing analytic unit.  The root is not forced
to be the principal square root: when the value at the base point lies on the excluded negative
ray, the construction rotates by `-1` and compensates with a factor of `I`. -/
structure ChapterVIHolomorphicSquareRootGerm
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (unit : X → ℂ) (base : X) where
  domain : Set X
  isOpen_domain : IsOpen domain
  base_mem : base ∈ domain
  root : X → ℂ
  differentiableOn_root : DifferentiableOn ℂ root domain
  root_sq : ∀ x ∈ domain, root x ^ 2 = unit x
  root_ne_zero : ∀ x ∈ domain, root x ≠ 0

/-- Every nonzero value of a globally holomorphic function admits a local holomorphic square-root
germ. -/
noncomputable def ChapterVIHolomorphicSquareRootGerm.of_differentiable
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    {unit : X → ℂ} {base : X}
    (hunit : Differentiable ℂ unit) (hbase : unit base ≠ 0) :
    ChapterVIHolomorphicSquareRootGerm unit base := by
  classical
  by_cases hprincipal : unit base ∈ Complex.slitPlane
  · exact
      { domain := unit ⁻¹' Complex.slitPlane
        isOpen_domain := Complex.isOpen_slitPlane.preimage hunit.continuous
        base_mem := hprincipal
        root := fun x ↦ Complex.sqrt (unit x)
        differentiableOn_root :=
          Complex.differentiableOn_sqrt.fun_comp hunit.differentiableOn
            (fun _ hx ↦ hx)
        root_sq := fun _ hx ↦ Complex.sq_sqrt_of_mem_slitPlane hx
        root_ne_zero := fun _ hx ↦ Complex.sqrt_ne_zero_of_mem_slitPlane hx }
  · have hrotated : -unit base ∈ Complex.slitPlane :=
      (Complex.mem_slitPlane_or_neg_mem_slitPlane hbase).resolve_left hprincipal
    exact
      { domain := (fun x ↦ -unit x) ⁻¹' Complex.slitPlane
        isOpen_domain := Complex.isOpen_slitPlane.preimage hunit.continuous.neg
        base_mem := hrotated
        root := fun x ↦ Complex.I * Complex.sqrt (-unit x)
        differentiableOn_root := by
          exact (Complex.differentiableOn_sqrt.fun_comp
            hunit.neg.differentiableOn (fun _ hx ↦ hx)).const_mul Complex.I
        root_sq := by
          intro x hx
          rw [mul_pow, Complex.I_sq,
            Complex.sq_sqrt_of_mem_slitPlane hx]
          ring
        root_ne_zero := by
          intro x hx
          exact mul_ne_zero Complex.I_ne_zero
            (Complex.sqrt_ne_zero_of_mem_slitPlane hx) }

/-- Every analytic unit germ that is nonzero at its base point admits a local holomorphic square
root.  Unlike `of_differentiable`, this constructor makes no global regularity assumption.  Its
domain is cut down to the open analytic locus and the interior of the appropriate slit-plane
preimage. -/
noncomputable def ChapterVIHolomorphicSquareRootGerm.of_analyticAt
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    {unit : X → ℂ} {base : X}
    (hunit : AnalyticAt ℂ unit base) (hbase : unit base ≠ 0) :
    ChapterVIHolomorphicSquareRootGerm unit base := by
  classical
  let analyticLocus : Set X := {x | AnalyticAt ℂ unit x}
  have hopenAnalytic : IsOpen analyticLocus := isOpen_analyticAt ℂ unit
  have hbaseAnalytic : base ∈ analyticLocus := hunit
  by_cases hprincipal : unit base ∈ Complex.slitPlane
  · have hpreimage : unit ⁻¹' Complex.slitPlane ∈ 𝓝 base :=
      hunit.continuousAt
        (Complex.isOpen_slitPlane.mem_nhds hprincipal)
    have hbaseInterior : base ∈ interior (unit ⁻¹' Complex.slitPlane) :=
      mem_interior_iff_mem_nhds.mpr hpreimage
    have hinterior : interior (unit ⁻¹' Complex.slitPlane) ⊆
        unit ⁻¹' Complex.slitPlane := interior_subset
    exact
      { domain := analyticLocus ∩ interior (unit ⁻¹' Complex.slitPlane)
        isOpen_domain := hopenAnalytic.inter isOpen_interior
        base_mem := ⟨hbaseAnalytic, hbaseInterior⟩
        root := fun x ↦ Complex.sqrt (unit x)
        differentiableOn_root := by
          apply Complex.differentiableOn_sqrt.fun_comp
          · intro x hx
            exact hx.1.differentiableAt.differentiableWithinAt
          · intro x hx
            exact hinterior hx.2
        root_sq := fun _ hx ↦
          Complex.sq_sqrt_of_mem_slitPlane (hinterior hx.2)
        root_ne_zero := fun _ hx ↦
          Complex.sqrt_ne_zero_of_mem_slitPlane (hinterior hx.2) }
  · have hrotated : -unit base ∈ Complex.slitPlane :=
      (Complex.mem_slitPlane_or_neg_mem_slitPlane hbase).resolve_left hprincipal
    have hnegativeAnalytic : AnalyticAt ℂ (fun x ↦ -unit x) base := hunit.neg
    have hpreimage : (fun x ↦ -unit x) ⁻¹' Complex.slitPlane ∈ 𝓝 base :=
      hnegativeAnalytic.continuousAt
        (Complex.isOpen_slitPlane.mem_nhds hrotated)
    have hbaseInterior : base ∈
        interior ((fun x ↦ -unit x) ⁻¹' Complex.slitPlane) :=
      mem_interior_iff_mem_nhds.mpr hpreimage
    have hinterior : interior ((fun x ↦ -unit x) ⁻¹' Complex.slitPlane) ⊆
        (fun x ↦ -unit x) ⁻¹' Complex.slitPlane := interior_subset
    exact
      { domain := analyticLocus ∩
          interior ((fun x ↦ -unit x) ⁻¹' Complex.slitPlane)
        isOpen_domain := hopenAnalytic.inter isOpen_interior
        base_mem := ⟨hbaseAnalytic, hbaseInterior⟩
        root := fun x ↦ Complex.I * Complex.sqrt (-unit x)
        differentiableOn_root := by
          apply DifferentiableOn.const_mul
          apply Complex.differentiableOn_sqrt.fun_comp
          · intro x hx
            exact hx.1.differentiableAt.neg.differentiableWithinAt
          · intro x hx
            exact hinterior hx.2
        root_sq := by
          intro x hx
          rw [mul_pow, Complex.I_sq,
            Complex.sq_sqrt_of_mem_slitPlane (hinterior hx.2)]
          ring
        root_ne_zero := by
          intro x hx
          exact mul_ne_zero Complex.I_ne_zero
            (Complex.sqrt_ne_zero_of_mem_slitPlane (hinterior hx.2)) }

/-- Combine the principal branch of the quadratic factor with an arbitrary local holomorphic
square-root germ of the analytic unit. -/
def chapterVIPreparedSquareRootFromUnitGerm
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    {unit : X → ℂ} {base : X}
    (quadratic : X → ℂ)
    (unitGerm : ChapterVIHolomorphicSquareRootGerm unit base) (x : X) : ℂ :=
  Complex.sqrt (quadratic x) * unitGerm.root x

/-- The corresponding prepared inverse square-root branch. -/
def chapterVIPreparedInverseSquareRootFromUnitGerm
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    {unit : X → ℂ} {base : X}
    (quadratic : X → ℂ)
    (unitGerm : ChapterVIHolomorphicSquareRootGerm unit base) (x : X) : ℂ :=
  (chapterVIPreparedSquareRootFromUnitGerm quadratic unitGerm x)⁻¹

/-- Correctness of the prepared branch with an arbitrary analytic-unit square-root germ. -/
theorem chapterVIPreparedSquareRootFromUnitGerm_sq
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    {quadratic unit : X → ℂ} {base x : X}
    (unitGerm : ChapterVIHolomorphicSquareRootGerm unit base)
    (hquadratic : quadratic x ∈ Complex.slitPlane)
    (hunit : x ∈ unitGerm.domain) :
    chapterVIPreparedSquareRootFromUnitGerm quadratic unitGerm x ^ 2 =
      quadratic x * unit x := by
  rw [chapterVIPreparedSquareRootFromUnitGerm, mul_pow,
    Complex.sq_sqrt_of_mem_slitPlane hquadratic,
    unitGerm.root_sq x hunit]

/-- The combined branch is nonzero on its natural domain. -/
theorem chapterVIPreparedSquareRootFromUnitGerm_ne_zero
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    {quadratic unit : X → ℂ} {base x : X}
    (unitGerm : ChapterVIHolomorphicSquareRootGerm unit base)
    (hquadratic : quadratic x ∈ Complex.slitPlane)
    (hunit : x ∈ unitGerm.domain) :
    chapterVIPreparedSquareRootFromUnitGerm quadratic unitGerm x ≠ 0 :=
  mul_ne_zero (Complex.sqrt_ne_zero_of_mem_slitPlane hquadratic)
    (unitGerm.root_ne_zero x hunit)

/-- Holomorphicity of the prepared branch on the intersection of the quadratic chart and the
automatically constructed unit-root germ. -/
theorem differentiableOn_chapterVIPreparedSquareRootFromUnitGerm
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    {quadratic unit : X → ℂ} {base : X}
    (unitGerm : ChapterVIHolomorphicSquareRootGerm unit base)
    (hquadratic : Differentiable ℂ quadratic) :
    DifferentiableOn ℂ
      (chapterVIPreparedSquareRootFromUnitGerm quadratic unitGerm)
      (quadratic ⁻¹' Complex.slitPlane ∩ unitGerm.domain) := by
  exact (Complex.differentiableOn_sqrt.fun_comp hquadratic.differentiableOn
    (fun _ hx ↦ hx.1)).mul
      (unitGerm.differentiableOn_root.mono inter_subset_right)

/-- Holomorphicity of the inverse prepared branch with an arbitrary nonvanishing analytic unit. -/
theorem differentiableOn_chapterVIPreparedInverseSquareRootFromUnitGerm
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    {quadratic unit : X → ℂ} {base : X}
    (unitGerm : ChapterVIHolomorphicSquareRootGerm unit base)
    (hquadratic : Differentiable ℂ quadratic) :
    DifferentiableOn ℂ
      (chapterVIPreparedInverseSquareRootFromUnitGerm quadratic unitGerm)
      (quadratic ⁻¹' Complex.slitPlane ∩ unitGerm.domain) := by
  apply (differentiableOn_chapterVIPreparedSquareRootFromUnitGerm
    unitGerm hquadratic).inv
  intro x hx
  exact chapterVIPreparedSquareRootFromUnitGerm_ne_zero unitGerm hx.1 hx.2

/-- Algebraic correctness of the inverse branch constructed from the arbitrary unit germ. -/
theorem chapterVIPreparedInverseSquareRootFromUnitGerm_sq_mul
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    {quadratic unit : X → ℂ} {base x : X}
    (unitGerm : ChapterVIHolomorphicSquareRootGerm unit base)
    (hquadratic : quadratic x ∈ Complex.slitPlane)
    (hunit : x ∈ unitGerm.domain) :
    chapterVIPreparedInverseSquareRootFromUnitGerm quadratic unitGerm x ^ 2 *
        (quadratic x * unit x) = 1 := by
  rw [← chapterVIPreparedSquareRootFromUnitGerm_sq unitGerm hquadratic hunit]
  have hne := chapterVIPreparedSquareRootFromUnitGerm_ne_zero
    unitGerm hquadratic hunit
  simp [chapterVIPreparedInverseSquareRootFromUnitGerm, hne]

end PoincareChapterVI
