/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import Mathlib.Analysis.Analytic.Basic
import PoincareChapterVI.ChapterVIComplexBranch
import PoincareChapterVI.ChapterVIContourTransport
import PoincareChapterVI.ChapterVIWeierstrass

/-!
# From a convergent prepared series to the analytic germ in Chapter VI

The formal Weierstrass preparation theorem in `ChapterVIWeierstrass` produces an identity of
formal power series.  To use that identity in Poincare's contour argument one must additionally
show that the series involved converge to the actual functions.  This file isolates the analytic
identity step from that existence problem.

The main uniqueness lemma says that two functions represented at a point by the same convergent
formal multilinear series agree in a neighbourhood of the point.  The
`ChapterVIConvergentPreparedGerm` structure then records precisely the convergent realization of
Poincare's prepared factors.  Its factorization theorem is a conclusion, not a structure field.

A LeanCompCert computation can certify arbitrarily large finite coefficient comparisons used to
construct such a realization.  It cannot, by itself, turn agreement through one finite cutoff into
convergence or equality of analytic germs; those remain analytic proof obligations.
-/

noncomputable section

open Filter Set Topology
open scoped unitInterval

namespace PoincareChapterVI

/-- Two functions represented by the same convergent formal multilinear series at a point agree
on some neighbourhood of that point.  This is the analytic identity bridge needed after a
coefficient-level preparation argument. -/
theorem eventuallyEq_of_hasFPowerSeriesAt_same
    {𝕜 E F : Type*}
    [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f g : E → F} {series : FormalMultilinearSeries 𝕜 E F} {base : E}
    (hf : HasFPowerSeriesAt f series base)
    (hg : HasFPowerSeriesAt g series base) :
    f =ᶠ[𝓝 base] g := by
  rcases hf with ⟨rf, hf⟩
  rcases hg with ⟨rg, hg⟩
  let radius := min rf rg
  have hradius : 0 < radius := lt_min hf.r_pos hg.r_pos
  have hf' : HasFPowerSeriesOnBall f series base radius :=
    hf.mono hradius inf_le_left
  have hg' : HasFPowerSeriesOnBall g series base radius :=
    hg.mono hradius inf_le_right
  filter_upwards [Metric.eball_mem_nhds base hradius] with point hpoint
  exact hf'.unique hg' hpoint

/-- A convergent analytic realization of Poincare's completed-square normal form near a base
point.  The parameter is the first coordinate and the local integration variable is the second.

The fields `radicandSeries` and `preparedSeries` intentionally have the same value.  Establishing
those two convergence statements from the nested formal power series produced by
`exists_chapterVI_weierstrassNormalForm` is the remaining analytic Weierstrass-preparation
obligation. -/
structure ChapterVIConvergentPreparedGerm
    (radicand : ℂ × ℂ → ℂ) (base : ℂ × ℂ) where
  center : ℂ → ℂ
  kappa : ℂ → ℂ
  unit : ℂ × ℂ → ℂ
  centerSeries : FormalMultilinearSeries ℂ ℂ ℂ
  kappaSeries : FormalMultilinearSeries ℂ ℂ ℂ
  unitSeries : FormalMultilinearSeries ℂ (ℂ × ℂ) ℂ
  commonSeries : FormalMultilinearSeries ℂ (ℂ × ℂ) ℂ
  centerHasFPowerSeries : HasFPowerSeriesAt center centerSeries base.1
  kappaHasFPowerSeries : HasFPowerSeriesAt kappa kappaSeries base.1
  unitHasFPowerSeries : HasFPowerSeriesAt unit unitSeries base
  radicandHasFPowerSeries : HasFPowerSeriesAt radicand commonSeries base
  preparedHasFPowerSeries : HasFPowerSeriesAt
    (fun point : ℂ × ℂ ↦
      (((point.2 - center point.1) ^ 2 + kappa point.1) * unit point))
    commonSeries base
  center_base : center base.1 = base.2
  kappa_base : kappa base.1 = 0
  unit_base_ne_zero : unit base ≠ 0

namespace ChapterVIConvergentPreparedGerm

variable {radicand : ℂ × ℂ → ℂ} {base : ℂ × ℂ}

/-- The completed-square quadratic factor of a convergent prepared germ. -/
def quadratic (germ : ChapterVIConvergentPreparedGerm radicand base) :
    ℂ × ℂ → ℂ :=
  fun point ↦ (point.2 - germ.center point.1) ^ 2 + germ.kappa point.1

/-- The completed-square factorization holds as an equality of actual functions near the base
point, once both sides have been identified with the same convergent series. -/
theorem eventually_factorization
    (germ : ChapterVIConvergentPreparedGerm radicand base) :
    radicand =ᶠ[𝓝 base]
      fun point : ℂ × ℂ ↦
        (((point.2 - germ.center point.1) ^ 2 + germ.kappa point.1) * germ.unit point) :=
  eventuallyEq_of_hasFPowerSeriesAt_same
    germ.radicandHasFPowerSeries germ.preparedHasFPowerSeries

/-- The prepared unit is genuinely nonzero on a neighbourhood of the pinch point. -/
theorem eventually_unit_ne_zero
    (germ : ChapterVIConvergentPreparedGerm radicand base) :
    ∀ᶠ point in 𝓝 base, germ.unit point ≠ 0 :=
  germ.unitHasFPowerSeries.continuousAt.eventually_ne germ.unit_base_ne_zero

/-- The factorization and nonvanishing of the prepared unit hold together on one actual open
neighbourhood of the pinch point. -/
theorem exists_open_factorization_neighborhood
    (germ : ChapterVIConvergentPreparedGerm radicand base) :
    ∃ neighborhood : Set (ℂ × ℂ),
      IsOpen neighborhood ∧ base ∈ neighborhood ∧
      ∀ point ∈ neighborhood,
        radicand point = germ.quadratic point * germ.unit point ∧
          germ.unit point ≠ 0 := by
  have heventually : ∀ᶠ point in 𝓝 base,
      radicand point = germ.quadratic point * germ.unit point ∧
        germ.unit point ≠ 0 := by
    filter_upwards [germ.eventually_factorization, germ.eventually_unit_ne_zero]
      with point hfactor hunit
    exact ⟨hfactor, hunit⟩
  rcases eventually_nhds_iff.mp heventually with
    ⟨neighborhood, hall, hopen, hbase⟩
  exact ⟨neighborhood, hopen, hbase, hall⟩

/-- The canonical open neighbourhood on which the actual radicand equals its prepared
factorization. -/
def factorizationDomain
    (germ : ChapterVIConvergentPreparedGerm radicand base) : Set (ℂ × ℂ) :=
  interior {point | radicand point = germ.quadratic point * germ.unit point}

theorem isOpen_factorizationDomain
    (germ : ChapterVIConvergentPreparedGerm radicand base) :
    IsOpen germ.factorizationDomain :=
  isOpen_interior

theorem base_mem_factorizationDomain
    (germ : ChapterVIConvergentPreparedGerm radicand base) :
    base ∈ germ.factorizationDomain := by
  apply mem_interior_iff_mem_nhds.mpr
  change radicand =ᶠ[𝓝 base]
    fun point : ℂ × ℂ ↦ germ.quadratic point * germ.unit point
  simpa only [quadratic] using germ.eventually_factorization

theorem factorization_of_mem_factorizationDomain
    (germ : ChapterVIConvergentPreparedGerm radicand base)
    {point : ℂ × ℂ} (hpoint : point ∈ germ.factorizationDomain) :
    radicand point = germ.quadratic point * germ.unit point := by
  have hinterior :
      interior {x | radicand x = germ.quadratic x * germ.unit x} ⊆
        {x | radicand x = germ.quadratic x * germ.unit x} := interior_subset
  exact hinterior hpoint

/-- The three prepared factors are analytic at their relevant base points. -/
theorem analytic_factors
    (germ : ChapterVIConvergentPreparedGerm radicand base) :
    AnalyticAt ℂ germ.center base.1 ∧
      AnalyticAt ℂ germ.kappa base.1 ∧
      AnalyticAt ℂ germ.unit base :=
  ⟨germ.centerHasFPowerSeries.analyticAt,
    germ.kappaHasFPowerSeries.analyticAt,
    germ.unitHasFPowerSeries.analyticAt⟩

/-- The automatically selected local holomorphic square root of the prepared unit.  This uses
only the unit's convergent germ, not a global holomorphic extension. -/
noncomputable def unitRootGerm
    (germ : ChapterVIConvergentPreparedGerm radicand base) :
    ChapterVIHolomorphicSquareRootGerm germ.unit base :=
  ChapterVIHolomorphicSquareRootGerm.of_analyticAt
    germ.unitHasFPowerSeries.analyticAt germ.unit_base_ne_zero

/-- The square-root branch obtained by combining the principal quadratic branch with the local
unit-root germ. -/
noncomputable def squareRoot
    (germ : ChapterVIConvergentPreparedGerm radicand base) : ℂ × ℂ → ℂ :=
  chapterVIPreparedSquareRootFromUnitGerm germ.quadratic germ.unitRootGerm

/-- The inverse square root appearing in Poincare's prepared contour integrand. -/
noncomputable def inverseSquareRoot
    (germ : ChapterVIConvergentPreparedGerm radicand base) : ℂ × ℂ → ℂ :=
  chapterVIPreparedInverseSquareRootFromUnitGerm germ.quadratic germ.unitRootGerm

/-- The open locus on which the parameter factors `center` and `kappa` are analytic.  Convergence
at the base point ensures that this locus contains the base point. -/
def analyticFactorDomain
    (germ : ChapterVIConvergentPreparedGerm radicand base) : Set (ℂ × ℂ) :=
  {point | AnalyticAt ℂ germ.center point.1} ∩
    {point | AnalyticAt ℂ germ.kappa point.1}

theorem isOpen_analyticFactorDomain
    (germ : ChapterVIConvergentPreparedGerm radicand base) :
    IsOpen germ.analyticFactorDomain := by
  exact ((isOpen_analyticAt ℂ germ.center).preimage continuous_fst).inter
    ((isOpen_analyticAt ℂ germ.kappa).preimage continuous_fst)

theorem base_mem_analyticFactorDomain
    (germ : ChapterVIConvergentPreparedGerm radicand base) :
    base ∈ germ.analyticFactorDomain :=
  ⟨germ.centerHasFPowerSeries.analyticAt,
    germ.kappaHasFPowerSeries.analyticAt⟩

/-- The completed-square quadratic is holomorphic on the local analytic-factor locus. -/
theorem differentiableOn_quadratic
    (germ : ChapterVIConvergentPreparedGerm radicand base) :
    DifferentiableOn ℂ germ.quadratic germ.analyticFactorDomain := by
  intro point hpoint
  have hcenter : DifferentiableAt ℂ
      (fun x : ℂ × ℂ ↦ germ.center x.1) point :=
    hpoint.1.differentiableAt.comp point (by fun_prop)
  have hkappa : DifferentiableAt ℂ
      (fun x : ℂ × ℂ ↦ germ.kappa x.1) point :=
    hpoint.2.differentiableAt.comp point (by fun_prop)
  have hcoordinate : DifferentiableAt ℂ (fun x : ℂ × ℂ ↦ x.2) point := by
    fun_prop
  exact (((hcoordinate.sub hcenter).pow 2).add hkappa).differentiableWithinAt

/-- The natural open punctured chart for the prepared inverse square root.  The interior is used
because the quadratic factor vanishes at the pinch itself, while its chosen square-root branch is
defined on a slit neighbourhood away from that zero. -/
def branchDomain
    (germ : ChapterVIConvergentPreparedGerm radicand base) : Set (ℂ × ℂ) :=
  (germ.analyticFactorDomain ∩
    interior (germ.quadratic ⁻¹' Complex.slitPlane)) ∩
      germ.unitRootGerm.domain

theorem isOpen_branchDomain
    (germ : ChapterVIConvergentPreparedGerm radicand base) :
    IsOpen germ.branchDomain :=
  (germ.isOpen_analyticFactorDomain.inter isOpen_interior).inter
    germ.unitRootGerm.isOpen_domain

/-- The constructed inverse square root is holomorphic on its natural local punctured chart. -/
theorem differentiableOn_inverseSquareRoot
    (germ : ChapterVIConvergentPreparedGerm radicand base) :
    DifferentiableOn ℂ germ.inverseSquareRoot germ.branchDomain := by
  have hquadratic : DifferentiableOn ℂ germ.quadratic germ.branchDomain :=
    germ.differentiableOn_quadratic.mono fun _ hx ↦ hx.1.1
  have hquadraticMap : MapsTo germ.quadratic germ.branchDomain Complex.slitPlane := by
    have hinterior : interior (germ.quadratic ⁻¹' Complex.slitPlane) ⊆
        germ.quadratic ⁻¹' Complex.slitPlane := interior_subset
    intro point hpoint
    exact hinterior hpoint.1.2
  have hroot : DifferentiableOn ℂ germ.unitRootGerm.root germ.branchDomain :=
    germ.unitRootGerm.differentiableOn_root.mono fun _ hx ↦ hx.2
  have hbranch : DifferentiableOn ℂ germ.squareRoot germ.branchDomain := by
    exact (Complex.differentiableOn_sqrt.fun_comp hquadratic hquadraticMap).mul hroot
  apply hbranch.inv
  intro point hpoint
  exact chapterVIPreparedSquareRootFromUnitGerm_ne_zero
    germ.unitRootGerm (hquadraticMap hpoint) hpoint.2

/-- The open chart on which the inverse branch is both holomorphic and certified to be the
inverse square root of the original radicand. -/
def actualBranchDomain
    (germ : ChapterVIConvergentPreparedGerm radicand base) : Set (ℂ × ℂ) :=
  germ.factorizationDomain ∩ germ.branchDomain

theorem isOpen_actualBranchDomain
    (germ : ChapterVIConvergentPreparedGerm radicand base) :
    IsOpen germ.actualBranchDomain :=
  germ.isOpen_factorizationDomain.inter germ.isOpen_branchDomain

theorem differentiableOn_inverseSquareRoot_actualBranchDomain
    (germ : ChapterVIConvergentPreparedGerm radicand base) :
    DifferentiableOn ℂ germ.inverseSquareRoot germ.actualBranchDomain :=
  germ.differentiableOn_inverseSquareRoot.mono inter_subset_right

/-- On the local factorization neighbourhood and the quadratic slit chart, the constructed
square root squares to the *actual* radicand, rather than merely to the prepared expression. -/
theorem squareRoot_sq_eq_radicand
    (germ : ChapterVIConvergentPreparedGerm radicand base)
    {point : ℂ × ℂ}
    (hfactorization :
      radicand point = germ.quadratic point * germ.unit point)
    (hquadratic : germ.quadratic point ∈ Complex.slitPlane)
    (hunit : point ∈ germ.unitRootGerm.domain) :
    germ.squareRoot point ^ 2 = radicand point := by
  rw [hfactorization]
  exact chapterVIPreparedSquareRootFromUnitGerm_sq
    germ.unitRootGerm hquadratic hunit

/-- Algebraic correctness of the constructed inverse branch for the actual radicand. -/
theorem inverseSquareRoot_sq_mul_radicand
    (germ : ChapterVIConvergentPreparedGerm radicand base)
    {point : ℂ × ℂ}
    (hfactorization :
      radicand point = germ.quadratic point * germ.unit point)
    (hquadratic : germ.quadratic point ∈ Complex.slitPlane)
    (hunit : point ∈ germ.unitRootGerm.domain) :
    germ.inverseSquareRoot point ^ 2 * radicand point = 1 := by
  rw [hfactorization]
  exact chapterVIPreparedInverseSquareRootFromUnitGerm_sq_mul
    germ.unitRootGerm hquadratic hunit

/-- Membership in the natural branch domain supplies both branch hypotheses automatically. -/
theorem inverseSquareRoot_sq_mul_radicand_of_mem_branchDomain
    (germ : ChapterVIConvergentPreparedGerm radicand base)
    {point : ℂ × ℂ}
    (hfactorization :
      radicand point = germ.quadratic point * germ.unit point)
    (hpoint : point ∈ germ.branchDomain) :
    germ.inverseSquareRoot point ^ 2 * radicand point = 1 := by
  have hinterior : interior (germ.quadratic ⁻¹' Complex.slitPlane) ⊆
      germ.quadratic ⁻¹' Complex.slitPlane := interior_subset
  exact germ.inverseSquareRoot_sq_mul_radicand hfactorization
    (hinterior hpoint.1.2) hpoint.2

/-- Pointwise correctness is automatic throughout the actual branch domain. -/
theorem inverseSquareRoot_sq_mul_radicand_of_mem_actualBranchDomain
    (germ : ChapterVIConvergentPreparedGerm radicand base)
    {point : ℂ × ℂ} (hpoint : point ∈ germ.actualBranchDomain) :
    germ.inverseSquareRoot point ^ 2 * radicand point = 1 :=
  germ.inverseSquareRoot_sq_mul_radicand_of_mem_branchDomain
    (germ.factorization_of_mem_factorizationDomain hpoint.1) hpoint.2

/-- There is one open neighbourhood of the pinch on whose punctured branch chart the constructed
holomorphic inverse branch is an actual inverse square root of the original radicand. -/
theorem exists_open_inverseSquareRoot_neighborhood
    (germ : ChapterVIConvergentPreparedGerm radicand base) :
    ∃ neighborhood : Set (ℂ × ℂ),
      IsOpen neighborhood ∧ base ∈ neighborhood ∧
      ∀ point ∈ neighborhood ∩ germ.branchDomain,
        germ.inverseSquareRoot point ^ 2 * radicand point = 1 := by
  rcases germ.exists_open_factorization_neighborhood with
    ⟨neighborhood, hopen, hbase, hfactorization⟩
  refine ⟨neighborhood, hopen, hbase, ?_⟩
  intro point hpoint
  exact germ.inverseSquareRoot_sq_mul_radicand_of_mem_branchDomain
    (hfactorization point hpoint.1).1 hpoint.2

/-- Near the pinch, every point lying in the quadratic slit chart and the automatically chosen
unit-root chart satisfies the inverse-square-root equation for the actual radicand. -/
theorem eventually_inverseSquareRoot_sq_mul_radicand
    (germ : ChapterVIConvergentPreparedGerm radicand base) :
    ∀ᶠ point in 𝓝 base,
      germ.quadratic point ∈ Complex.slitPlane →
      point ∈ germ.unitRootGerm.domain →
      germ.inverseSquareRoot point ^ 2 * radicand point = 1 := by
  filter_upwards [germ.eventually_factorization] with point hfactorization
  intro hquadratic hunit
  exact germ.inverseSquareRoot_sq_mul_radicand
    hfactorization hquadratic hunit

/-- Restrict the two-variable inverse branch to one fixed parameter value, as required by the
one-variable contour integral in §§99--100. -/
noncomputable def sliceInverseSquareRoot
    (germ : ChapterVIConvergentPreparedGerm radicand base)
    (parameter : ℂ) : ℂ → ℂ :=
  fun coordinate ↦ germ.inverseSquareRoot (parameter, coordinate)

/-- The corresponding slice of the open two-variable branch domain. -/
def sliceBranchDomain
    (germ : ChapterVIConvergentPreparedGerm radicand base)
    (parameter : ℂ) : Set ℂ :=
  {coordinate | (parameter, coordinate) ∈ germ.actualBranchDomain}

theorem isOpen_sliceBranchDomain
    (germ : ChapterVIConvergentPreparedGerm radicand base)
    (parameter : ℂ) :
    IsOpen (germ.sliceBranchDomain parameter) := by
  exact germ.isOpen_actualBranchDomain.preimage (continuous_const.prodMk continuous_id)

/-- Holomorphicity of every fixed-parameter inverse branch on its sliced chart. -/
theorem differentiableOn_sliceInverseSquareRoot
    (germ : ChapterVIConvergentPreparedGerm radicand base)
    (parameter : ℂ) :
    DifferentiableOn ℂ (germ.sliceInverseSquareRoot parameter)
      (germ.sliceBranchDomain parameter) := by
  have hembedding : Differentiable ℂ (fun coordinate : ℂ ↦ (parameter, coordinate)) := by
    fun_prop
  change DifferentiableOn ℂ
    (germ.inverseSquareRoot ∘ fun coordinate : ℂ ↦ (parameter, coordinate))
    ((fun coordinate : ℂ ↦ (parameter, coordinate)) ⁻¹' germ.actualBranchDomain)
  exact germ.differentiableOn_inverseSquareRoot_actualBranchDomain.comp
    hembedding.differentiableOn (fun _ hpoint ↦ hpoint)

/-- On every fixed-parameter actual branch chart, the slice is pointwise an inverse square root
of the corresponding slice of the original radicand. -/
theorem sliceInverseSquareRoot_sq_mul_radicand
    (germ : ChapterVIConvergentPreparedGerm radicand base)
    (parameter coordinate : ℂ)
    (hcoordinate : coordinate ∈ germ.sliceBranchDomain parameter) :
    germ.sliceInverseSquareRoot parameter coordinate ^ 2 *
        radicand (parameter, coordinate) = 1 :=
  germ.inverseSquareRoot_sq_mul_radicand_of_mem_actualBranchDomain hcoordinate

/-- Direct contour transport for the inverse square root of the actual convergent radicand.
The deformation may use any domain whose closure stays inside the fixed-parameter branch chart;
this closure condition automatically supplies the continuity premise required by Stokes' theorem.
-/
theorem sliceInverseSquareRoot_curveIntegral_eq_of_holomorphic_homotopy
    (germ : ChapterVIConvergentPreparedGerm radicand base)
    (parameter : ℂ)
    {a b : ℂ} {initial final : Path a b} {domain : Set ℂ}
    (homotopy : Path.Homotopy initial final)
    (mapsInterior : ∀ s ∈ Ioo (0 : I) 1, ∀ t ∈ Ioo (0 : I) 1,
      homotopy (s, t) ∈ domain)
    (hclosure : closure domain ⊆ germ.sliceBranchDomain parameter)
    (hcontDiff : ContDiffOn ℝ 2
      (fun st : ℝ × ℝ ↦
        Set.IccExtend zero_le_one (homotopy.toHomotopy.extend st.1) st.2)
      (Icc 0 1)) :
    (∫ᶜ z in initial,
      chapterVIComplexScalarOneForm (germ.sliceInverseSquareRoot parameter) z) =
      ∫ᶜ z in final,
        chapterVIComplexScalarOneForm (germ.sliceInverseSquareRoot parameter) z := by
  have hdomain : domain ⊆ germ.sliceBranchDomain parameter :=
    subset_closure.trans hclosure
  exact chapterVI_curveIntegral_eq_of_holomorphic_homotopy
    homotopy mapsInterior
    ((germ.differentiableOn_sliceInverseSquareRoot parameter).mono hdomain)
    ((germ.differentiableOn_sliceInverseSquareRoot parameter).continuousOn.mono hclosure)
    hcontDiff

end ChapterVIConvergentPreparedGerm

end PoincareChapterVI
