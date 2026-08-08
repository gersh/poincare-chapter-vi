/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import PoincareChapterVI.ChapterVIComplexBranch

/-!
# Smooth contour transport for Poincaré's Chapter VI pinch

Poincaré deforms the coefficient contour to a local cycle through a region where the chosen
inverse square-root branch is analytic.  This file packages Mathlib's formalized Poincaré/Stokes
theorem into the exact relative-endpoint contour-transport statement required in §§95--100.

The data deliberately distinguish:

* a mere reparameterization or affine center translation;
* a genuine `C²` homotopy of complex paths;
* the analytic branch domain in which the homotopy is allowed to move.

The remaining source obligation is to construct this data for Poincaré's actual collision cycle.
-/

noncomputable section

open AffineMap Filter Function MeasureTheory Set
open scoped Interval Topology unitInterval

namespace PoincareChapterVI

/-- Turn a complex scalar integrand `f(z)` into the complex-linear one-form `f(z) dz`. -/
def chapterVIComplexScalarOneForm (f : ℂ → ℂ) (z : ℂ) : ℂ →L[ℂ] ℂ :=
  (ContinuousLinearMap.smulRightL ℂ ℂ ℂ 1) (f z)

@[simp]
theorem chapterVIComplexScalarOneForm_apply (f : ℂ → ℂ) (z v : ℂ) :
    chapterVIComplexScalarOneForm f z v = v * f z := by
  simp [chapterVIComplexScalarOneForm]

/-- The real Fréchet derivative of the complex one-form `f(z) dz`, expressed using the complex
Fréchet derivative of `f`. -/
def chapterVIComplexScalarOneFormDerivative (f : ℂ → ℂ) (s : Set ℂ) (z : ℂ) :
    ℂ →L[ℝ] ℂ →L[ℂ] ℂ :=
  ((ContinuousLinearMap.smulRightL ℂ ℂ ℂ 1).comp
    (fderivWithin ℂ f s z)).restrictScalars ℝ

@[simp]
theorem chapterVIComplexScalarOneFormDerivative_apply
    (f : ℂ → ℂ) (s : Set ℂ) (z u v : ℂ) :
    chapterVIComplexScalarOneFormDerivative f s z u v =
      v * fderivWithin ℂ f s z u := by
  simp [chapterVIComplexScalarOneFormDerivative]

/-- Holomorphicity of `f` supplies the required real derivative of `f(z) dz`. -/
theorem hasFDerivWithinAt_chapterVIComplexScalarOneForm
    {f : ℂ → ℂ} {s : Set ℂ} {z : ℂ}
    (hf : DifferentiableWithinAt ℂ f s z) :
    HasFDerivWithinAt (chapterVIComplexScalarOneForm f)
      (chapterVIComplexScalarOneFormDerivative f s z) s z := by
  have hcompose := (ContinuousLinearMap.smulRightL ℂ ℂ ℂ 1).hasFDerivAt
    |>.comp_hasFDerivWithinAt z hf.hasFDerivWithinAt
    |>.restrictScalars ℝ
  change HasFDerivWithinAt (fun x ↦ ContinuousLinearMap.smulRight 1 (f x))
    (chapterVIComplexScalarOneFormDerivative f s z) s z
  exact hcompose

/-- The derivative of a holomorphic scalar one-form is symmetric as a real bilinear map. -/
theorem chapterVIComplexScalarOneFormDerivative_symmetric
    (f : ℂ → ℂ) (s : Set ℂ) (z u v : ℂ) :
    chapterVIComplexScalarOneFormDerivative f s z u v =
      chapterVIComplexScalarOneFormDerivative f s z v u := by
  let D := fderivWithin ℂ f s z
  have hu : D u = u * D 1 := by
    calc
      D u = D (u • (1 : ℂ)) := by simp
      _ = u • D 1 := by rw [map_smul]
      _ = u * D 1 := by simp
  have hv : D v = v * D 1 := by
    calc
      D v = D (v • (1 : ℂ)) := by simp
      _ = v • D 1 := by rw [map_smul]
      _ = v * D 1 := by simp
  simp only [chapterVIComplexScalarOneFormDerivative_apply]
  rw [hu, hv]
  ring

/-- The pointwise affine homotopy between two complex paths with the same endpoints, regarded as
a path homotopy relative to `{0,1}`. -/
def chapterVIAffinePathHomotopy
    {a b : ℂ} (initial final : Path a b) : Path.Homotopy initial final where
  toHomotopy := ContinuousMap.Homotopy.affine
    (initial : C(I, ℂ)) (final : C(I, ℂ))
  prop' := by
    intro t x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · simp [initial.source, final.source]
    · simp [initial.target, final.target]

@[simp]
theorem chapterVIAffinePathHomotopy_apply
    {a b : ℂ} (initial final : Path a b) (s t : I) :
    chapterVIAffinePathHomotopy initial final (s, t) =
      AffineMap.lineMap (initial t) (final t) (s : ℝ) :=
  rfl

/-- `C²` regularity of the two extended paths implies `C²` regularity of their canonical affine
homotopy on the closed unit square. -/
theorem contDiffOn_two_chapterVIAffinePathHomotopy
    {a b : ℂ} {initial final : Path a b}
    (hinitial : ContDiff ℝ 2 initial.extend)
    (hfinal : ContDiff ℝ 2 final.extend) :
    ContDiffOn ℝ 2
      (fun st : ℝ × ℝ ↦ Set.IccExtend zero_le_one
        ((chapterVIAffinePathHomotopy initial final).toHomotopy.extend st.1) st.2)
      (Icc 0 1) := by
  let model : ℝ × ℝ → ℂ := fun st ↦
    AffineMap.lineMap (initial.extend st.2) (final.extend st.2) st.1
  have hmodel : ContDiff ℝ 2 model := by
    dsimp only [model, AffineMap.lineMap_apply]
    simp only [vsub_eq_sub, vadd_eq_add]
    fun_prop
  apply hmodel.contDiffOn.congr
  rintro ⟨s, t⟩ hst
  rw [Icc_prod_eq] at hst
  simp only [model, ContinuousMap.Homotopy.extend_of_mem_I _ hst.1,
    Set.IccExtend_of_mem zero_le_one _ hst.2]
  change AffineMap.lineMap (initial ⟨t, hst.2⟩) (final ⟨t, hst.2⟩) s = _
  rw [Path.extend_apply, Path.extend_apply]

/-- The complete checked data for transporting a complex contour through a branch domain while
fixing its two endpoints.  Symmetry of `dω` is the closed-one-form condition used by Stokes'
theorem. -/
structure ChapterVISmoothContourDeformation
    {a b : ℂ} (ω : ℂ → ℂ →L[ℂ] ℂ)
    (initial final : Path a b) (domain : Set ℂ) where
  homotopy : Path.Homotopy initial final
  dω : ℂ → ℂ →L[ℝ] ℂ →L[ℂ] ℂ
  mapsInterior : ∀ s ∈ Ioo (0 : I) 1, ∀ t ∈ Ioo (0 : I) 1,
    homotopy (s, t) ∈ domain
  hasFDerivWithinAt : ∀ z ∈ domain,
    HasFDerivWithinAt ω (dω z) domain z
  continuousOnClosure : ContinuousOn ω (closure domain)
  derivative_symmetric : ∀ z ∈ domain,
    ∀ u ∈ tangentConeAt ℝ domain z, ∀ v ∈ tangentConeAt ℝ domain z,
      dω z u v = dω z v u
  contDiff_homotopy : ContDiffOn ℝ 2
    (fun st : ℝ × ℝ ↦
      Set.IccExtend zero_le_one (homotopy.toHomotopy.extend st.1) st.2)
    (Icc 0 1)

/-- Construct the closed-one-form data automatically from a holomorphic scalar integrand. -/
def ChapterVISmoothContourDeformation.of_holomorphicScalar
    {a b : ℂ} {f : ℂ → ℂ} {initial final : Path a b} {domain : Set ℂ}
    (homotopy : Path.Homotopy initial final)
    (mapsInterior : ∀ s ∈ Ioo (0 : I) 1, ∀ t ∈ Ioo (0 : I) 1,
      homotopy (s, t) ∈ domain)
    (hf : DifferentiableOn ℂ f domain)
    (hfClosure : ContinuousOn f (closure domain))
    (hcontDiff : ContDiffOn ℝ 2
      (fun st : ℝ × ℝ ↦
        Set.IccExtend zero_le_one (homotopy.toHomotopy.extend st.1) st.2)
      (Icc 0 1)) :
    ChapterVISmoothContourDeformation
      (chapterVIComplexScalarOneForm f) initial final domain where
  homotopy := homotopy
  dω := chapterVIComplexScalarOneFormDerivative f domain
  mapsInterior := mapsInterior
  hasFDerivWithinAt := fun z hz ↦
    hasFDerivWithinAt_chapterVIComplexScalarOneForm (hf z hz)
  continuousOnClosure := by
    change ContinuousOn (fun z ↦ ContinuousLinearMap.smulRight 1 (f z)) (closure domain)
    exact (ContinuousLinearMap.smulRightL ℂ ℂ ℂ 1).continuous.comp_continuousOn hfClosure
  derivative_symmetric := fun z _ u _ v _ ↦
    chapterVIComplexScalarOneFormDerivative_symmetric f domain z u v
  contDiff_homotopy := hcontDiff

/-- A checked smooth deformation with fixed endpoint boundaries preserves the contour integral
exactly. -/
theorem ChapterVISmoothContourDeformation.curveIntegral_eq
    {a b : ℂ} {ω : ℂ → ℂ →L[ℂ] ℂ}
    {initial final : Path a b} {domain : Set ℂ}
    (deformation : ChapterVISmoothContourDeformation ω initial final domain) :
    (∫ᶜ z in initial, ω z) = ∫ᶜ z in final, ω z := by
  let φ := deformation.homotopy.toHomotopy
  have hlower : φ.evalAt 0 =
      (Path.refl a).cast initial.source final.source := by
    ext t
    exact deformation.homotopy.source t
  have hupper : φ.evalAt 1 =
      (Path.refl b).cast initial.target final.target := by
    ext t
    exact deformation.homotopy.target t
  have hlowerIntegral : (∫ᶜ z in φ.evalAt 0, ω z) = 0 := by
    rw [hlower, curveIntegral_cast, curveIntegral_refl]
  have hupperIntegral : (∫ᶜ z in φ.evalAt 1, ω z) = 0 := by
    rw [hupper, curveIntegral_cast, curveIntegral_refl]
  have hboundary :=
    φ.curveIntegral_add_curveIntegral_eq_of_hasFDerivWithinAt
      deformation.mapsInterior deformation.hasFDerivWithinAt
      deformation.continuousOnClosure deformation.derivative_symmetric
      deformation.contDiff_homotopy
  rw [hlowerIntegral, hupperIntegral, add_zero] at hboundary
  simpa using hboundary

/-- Specialization to the one-form associated with a scalar complex integrand. -/
theorem ChapterVISmoothContourDeformation.scalar_curveIntegral_eq
    {a b : ℂ} {f : ℂ → ℂ}
    {initial final : Path a b} {domain : Set ℂ}
    (deformation : ChapterVISmoothContourDeformation
      (chapterVIComplexScalarOneForm f) initial final domain) :
    (∫ᶜ z in initial, chapterVIComplexScalarOneForm f z) =
      ∫ᶜ z in final, chapterVIComplexScalarOneForm f z :=
  deformation.curveIntegral_eq

/-- Fundamental theorem for a complex scalar one-form on a straight contour segment.  This is
the exact integration step used in §100 once the prepared inverse branch has been identified as
the derivative of a logarithmic primitive. -/
theorem chapterVI_curveIntegral_segment_eq_sub_of_primitive
    {f primitive : ℂ → ℂ} {start direction : ℂ}
    (hcont : ContinuousOn
      (fun t : ℝ ↦ f (start + t • direction)) (Icc 0 1))
    (hderiv : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt primitive (f (start + t • direction))
        (start + t • direction)) :
    (∫ᶜ z in Path.segment start (start + direction),
      chapterVIComplexScalarOneForm f z) =
      primitive (start + direction) - primitive start := by
  rw [curveIntegral_segment]
  have hfundamental :=
    intervalIntegral.integral_unitInterval_deriv_eq_sub hcont hderiv
  simpa [chapterVIComplexScalarOneForm_apply, AffineMap.lineMap_apply, add_comm] using hfundamental

/-- A holomorphic scalar integrand has equal contour integrals along any two paths connected by
a checked `C²` homotopy relative to their endpoints inside its domain. -/
theorem chapterVI_curveIntegral_eq_of_holomorphic_homotopy
    {a b : ℂ} {f : ℂ → ℂ} {initial final : Path a b} {domain : Set ℂ}
    (homotopy : Path.Homotopy initial final)
    (mapsInterior : ∀ s ∈ Ioo (0 : I) 1, ∀ t ∈ Ioo (0 : I) 1,
      homotopy (s, t) ∈ domain)
    (hf : DifferentiableOn ℂ f domain)
    (hfClosure : ContinuousOn f (closure domain))
    (hcontDiff : ContDiffOn ℝ 2
      (fun st : ℝ × ℝ ↦
        Set.IccExtend zero_le_one (homotopy.toHomotopy.extend st.1) st.2)
      (Icc 0 1)) :
    (∫ᶜ z in initial, chapterVIComplexScalarOneForm f z) =
      ∫ᶜ z in final, chapterVIComplexScalarOneForm f z :=
  (ChapterVISmoothContourDeformation.of_holomorphicScalar
    homotopy mapsInterior hf hfClosure hcontDiff).curveIntegral_eq

/-- Direct contour-transport theorem for the prepared inverse square-root branch constructed in
`ChapterVIComplexBranch`. -/
theorem chapterVI_preparedInverseSquareRoot_curveIntegral_eq
    {a b : ℂ} {quadratic unit : ℂ → ℂ} {carrier : Set ℂ}
    (chart : ChapterVIPreparedBranchChart quadratic unit carrier)
    (hquadratic : Differentiable ℂ quadratic) (hunit : Differentiable ℂ unit)
    {initial final : Path a b}
    (homotopy : Path.Homotopy initial final)
    (mapsInterior : ∀ s ∈ Ioo (0 : I) 1, ∀ t ∈ Ioo (0 : I) 1,
      homotopy (s, t) ∈ chart.domain)
    (hclosure : ContinuousOn
      (chapterVIPreparedInverseSquareRoot quadratic unit) (closure chart.domain))
    (hcontDiff : ContDiffOn ℝ 2
      (fun st : ℝ × ℝ ↦
        Set.IccExtend zero_le_one (homotopy.toHomotopy.extend st.1) st.2)
      (Icc 0 1)) :
    (∫ᶜ z in initial,
      chapterVIComplexScalarOneForm
        (chapterVIPreparedInverseSquareRoot quadratic unit) z) =
    ∫ᶜ z in final,
      chapterVIComplexScalarOneForm
        (chapterVIPreparedInverseSquareRoot quadratic unit) z := by
  exact chapterVI_curveIntegral_eq_of_holomorphic_homotopy
    homotopy mapsInterior
    (chart.differentiableOn_inverseSquareRoot hquadratic hunit)
    hclosure hcontDiff

/-- On a convex branch domain, the canonical pointwise affine homotopy stays in the domain.
Consequently two sufficiently smooth paths with the same endpoints have equal integrals of a
holomorphic scalar one-form. -/
theorem chapterVI_curveIntegral_eq_of_holomorphic_affineHomotopy
    {a b : ℂ} {f : ℂ → ℂ} {initial final : Path a b} {domain : Set ℂ}
    (hconvex : Convex ℝ domain)
    (hinitial : ∀ t, initial t ∈ domain)
    (hfinal : ∀ t, final t ∈ domain)
    (hf : DifferentiableOn ℂ f domain)
    (hfClosure : ContinuousOn f (closure domain))
    (hcontDiff : ContDiffOn ℝ 2
      (fun st : ℝ × ℝ ↦ Set.IccExtend zero_le_one
        ((chapterVIAffinePathHomotopy initial final).toHomotopy.extend st.1) st.2)
      (Icc 0 1)) :
    (∫ᶜ z in initial, chapterVIComplexScalarOneForm f z) =
      ∫ᶜ z in final, chapterVIComplexScalarOneForm f z := by
  apply chapterVI_curveIntegral_eq_of_holomorphic_homotopy
    (chapterVIAffinePathHomotopy initial final) ?_ hf hfClosure hcontDiff
  intro s _ t _
  rw [chapterVIAffinePathHomotopy_apply]
  exact hconvex.lineMap_mem (hinitial t) (hfinal t) s.2

/-- Fully automatic affine transport from `C²` regularity of the two extended paths. -/
theorem chapterVI_curveIntegral_eq_of_holomorphic_convex
    {a b : ℂ} {f : ℂ → ℂ} {initial final : Path a b} {domain : Set ℂ}
    (hconvex : Convex ℝ domain)
    (hinitial : ∀ t, initial t ∈ domain)
    (hfinal : ∀ t, final t ∈ domain)
    (hinitialC2 : ContDiff ℝ 2 initial.extend)
    (hfinalC2 : ContDiff ℝ 2 final.extend)
    (hf : DifferentiableOn ℂ f domain)
    (hfClosure : ContinuousOn f (closure domain)) :
    (∫ᶜ z in initial, chapterVIComplexScalarOneForm f z) =
      ∫ᶜ z in final, chapterVIComplexScalarOneForm f z :=
  chapterVI_curveIntegral_eq_of_holomorphic_affineHomotopy
    hconvex hinitial hfinal hf hfClosure
    (contDiffOn_two_chapterVIAffinePathHomotopy hinitialC2 hfinalC2)

/-- Direct convex-domain transport for Poincaré's prepared inverse square-root branch. -/
theorem chapterVI_preparedInverseSquareRoot_curveIntegral_eq_of_convex
    {a b : ℂ} {quadratic unit : ℂ → ℂ} {carrier : Set ℂ}
    (chart : ChapterVIPreparedBranchChart quadratic unit carrier)
    (hconvex : Convex ℝ chart.domain)
    (hquadratic : Differentiable ℂ quadratic) (hunit : Differentiable ℂ unit)
    {initial final : Path a b}
    (hinitial : ∀ t, initial t ∈ chart.domain)
    (hfinal : ∀ t, final t ∈ chart.domain)
    (hinitialC2 : ContDiff ℝ 2 initial.extend)
    (hfinalC2 : ContDiff ℝ 2 final.extend)
    (hclosure : ContinuousOn
      (chapterVIPreparedInverseSquareRoot quadratic unit) (closure chart.domain)) :
    (∫ᶜ z in initial,
      chapterVIComplexScalarOneForm
        (chapterVIPreparedInverseSquareRoot quadratic unit) z) =
    ∫ᶜ z in final,
      chapterVIComplexScalarOneForm
        (chapterVIPreparedInverseSquareRoot quadratic unit) z := by
  exact chapterVI_curveIntegral_eq_of_holomorphic_convex
    hconvex hinitial hfinal hinitialC2 hfinalC2
    (chart.differentiableOn_inverseSquareRoot hquadratic hunit) hclosure

/-- Convex-domain contour transport using the automatically constructed square-root germ of an
arbitrary nonvanishing analytic unit. -/
theorem chapterVI_preparedUnitGerm_curveIntegral_eq_of_convex
    {a b : ℂ} {quadratic unit : ℂ → ℂ} {base : ℂ}
    (unitGerm : ChapterVIHolomorphicSquareRootGerm unit base)
    (hquadratic : Differentiable ℂ quadratic)
    {initial final : Path a b}
    (hconvex : Convex ℝ (quadratic ⁻¹' Complex.slitPlane ∩ unitGerm.domain))
    (hinitial : ∀ t,
      initial t ∈ quadratic ⁻¹' Complex.slitPlane ∩ unitGerm.domain)
    (hfinal : ∀ t,
      final t ∈ quadratic ⁻¹' Complex.slitPlane ∩ unitGerm.domain)
    (hinitialC2 : ContDiff ℝ 2 initial.extend)
    (hfinalC2 : ContDiff ℝ 2 final.extend)
    (hclosure : ContinuousOn
      (chapterVIPreparedInverseSquareRootFromUnitGerm quadratic unitGerm)
      (closure (quadratic ⁻¹' Complex.slitPlane ∩ unitGerm.domain))) :
    (∫ᶜ z in initial,
      chapterVIComplexScalarOneForm
        (chapterVIPreparedInverseSquareRootFromUnitGerm quadratic unitGerm) z) =
    ∫ᶜ z in final,
      chapterVIComplexScalarOneForm
        (chapterVIPreparedInverseSquareRootFromUnitGerm quadratic unitGerm) z := by
  exact chapterVI_curveIntegral_eq_of_holomorphic_convex
    hconvex hinitial hfinal hinitialC2 hfinalC2
    (differentiableOn_chapterVIPreparedInverseSquareRootFromUnitGerm
      unitGerm hquadratic) hclosure

end PoincareChapterVI
