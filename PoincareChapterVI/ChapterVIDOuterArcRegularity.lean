/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.ChapterVIDOuterArcPolarAdmissibility
import PoincareChapterVI.ChapterVIPrincipalIntegrand

/-!
# Finite limits of the certified regular arcs at D

The compiled polar certificate constructs a nonvanishing square-root sheet on each of the two
closed outer-arc rectangles.  This file pulls Poincare's literal principal numerator and the
contour differential back through his `u = x^(1/3)` coordinate and proves that the resulting
outer integrals vary continuously all the way to the collision parameter.

The exact source contour coordinate is

`t(u) = u exp((100/30003) (u^(-3) - u^3))`,

not `u^3`.  The algebraically expected derivative is included explicitly in the pulled-back
velocity.  The theorem below proves the finite-limit statement for that explicit transformed
integrand, conditional only on the compiled run verdict and a choice of square-root sheet.  The
chain rule and equality with the original curve integral are proved below under explicit branch
agreement.  Identifying the outer choices with the sheet used by the middle Morse chart remains
the separate gluing obligation.
-/

noncomputable section

open Complex Filter Set Topology
open scoped Interval Topology unitInterval

namespace PoincareChapterVI

namespace ChapterVIDOuterArcRegularity

/-- Clamp a real integration parameter to the unit interval.  This provides continuous
extensions to all of `R`, as required by Mathlib's parametric interval-integral theorem. -/
def clampUnit (t : ℝ) : I :=
  Set.projIcc 0 1 zero_le_one t

theorem continuous_clampUnit : Continuous clampUnit :=
  continuous_projIcc (h := zero_le_one)

@[simp]
theorem clampUnit_of_mem {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    clampUnit t = ⟨t, ht⟩ := by
  exact Set.projIcc_of_mem zero_le_one ht

/-- The point `u` on one of the certified outer rectangles, continuously extended in the
integration variable. -/
def rootCoordinate
    (side : ChapterVIDOuterArcSide) (point : I × ℝ) : ℂ :=
  chapterVIDOuterArcPoint side (point.1, clampUnit point.2)

theorem continuous_rootCoordinate (side : ChapterVIDOuterArcSide) :
    Continuous (rootCoordinate side) := by
  exact (continuous_chapterVIDOuterArcPoint side).comp
    (continuous_fst.prodMk (continuous_clampUnit.comp continuous_snd))

theorem rootCoordinate_ne_zero
    (side : ChapterVIDOuterArcSide) (point : I × ℝ) :
    rootCoordinate side point ≠ 0 :=
  chapterVIDOuterArcPoint_ne_zero side (point.1, clampUnit point.2)

/-- The selected positive cubic root `zeta = z^(1/3)` of Poincare's source parameter. -/
def parameterRoot (point : I × ℝ) : ℂ :=
  chapterVIDCommonParameterRootPath point.1

theorem continuous_parameterRoot : Continuous parameterRoot :=
  chapterVIDCommonParameterRootPath.continuous.comp continuous_fst

theorem parameterRoot_ne_zero (point : I × ℝ) :
    parameterRoot point ≠ 0 :=
  chapterVIDCommonParameterRootPath_ne_zero point.1

/-- The exact original contour coordinate `t` obtained from the root coordinate `u`. -/
def sourceContour
    (side : ChapterVIDOuterArcSide) (point : I × ℝ) : ℂ :=
  chapterVIDRootToOriginalContour (rootCoordinate side point)

theorem continuous_sourceContour (side : ChapterVIDOuterArcSide) :
    Continuous (sourceContour side) := by
  rw [continuous_iff_continuousAt]
  intro point
  exact (analyticAt_chapterVIDRootToOriginalContour
      (rootCoordinate_ne_zero side point)).continuousAt.comp_of_eq
    (continuous_rootCoordinate side).continuousAt rfl

theorem sourceContour_ne_zero
    (side : ChapterVIDOuterArcSide) (point : I × ℝ) :
    sourceContour side point ≠ 0 :=
  chapterVIDRootToOriginalContour_ne_zero (rootCoordinate_ne_zero side point)

/-- The literal principal numerator after `z = zeta^3` and
`t = t(u)`.  For `a=-1`, `c=3`, its first exponent is `-d-3b-1`. -/
def sourceNumerator
    (massProduct : ℂ) (b d : ℤ) (side : ChapterVIDOuterArcSide)
    (point : I × ℝ) : ℂ :=
  massProduct * sourceContour side point ^ ((-1) * d - b * 3 - 1) *
    parameterRoot point ^ (-d)

theorem continuous_sourceNumerator
    (massProduct : ℂ) (b d : ℤ) (side : ChapterVIDOuterArcSide) :
    Continuous (sourceNumerator massProduct b d side) := by
  unfold sourceNumerator
  exact (continuous_const.mul
      ((continuous_sourceContour side).zpow₀ _
        (fun point ↦ Or.inl (sourceContour_ne_zero side point)))).mul
    (continuous_parameterRoot.zpow₀ _
      (fun point ↦ Or.inl (parameterRoot_ne_zero point)))

/-- Pointwise correspondence with the numerator from the literal source-coordinate definition.
The hypothesis says that the local `z^(1/3)` branch agrees with the selected global lift at this
source point. -/
theorem sourceNumerator_eq_principalSourceNumerator
    (massProduct : ℂ) (b d : ℤ) (zRoot : ℂ → ℂ)
    (side : ChapterVIDOuterArcSide) (point : I × ℝ)
    (hroot : zRoot (parameterRoot point ^ 3) = parameterRoot point) :
    sourceNumerator massProduct b d side point =
      chapterVIPrincipalSourceNumerator massProduct (-1) b 3 d zRoot
        (parameterRoot point ^ 3, sourceContour side point) := by
  simp [sourceNumerator, chapterVIPrincipalSourceNumerator, hroot]

/-- Derivative of Poincare's exact `u -> t` coordinate change. -/
def rootToSourceDerivative (u : ℂ) : ℂ :=
  Complex.exp (chapterVIDRootExponentialArgument u) *
    (1 - (100 / 10001 : ℂ) * (u ^ (-3 : ℤ) + u ^ 3))

/-- The displayed formula is the actual complex derivative of Poincare's coordinate change. -/
theorem hasDerivAt_rootToOriginalContour
    {u : ℂ} (hu : u ≠ 0) :
    HasDerivAt chapterVIDRootToOriginalContour (rootToSourceDerivative u) u := by
  change HasDerivAt
    (fun w : ℂ ↦ w * Complex.exp
      ((100 / 30003 : ℂ) * ((w ^ 3)⁻¹ - w ^ 3)))
    (rootToSourceDerivative u) u
  have h := (hasDerivAt_id u).mul
    ((((((hasDerivAt_id u).pow 3).inv (pow_ne_zero 3 hu)).sub
      ((hasDerivAt_id u).pow 3)).const_mul (100 / 30003 : ℂ)).cexp)
  have heq : rootToSourceDerivative u =
      Complex.exp ((100 / 30003 : ℂ) * ((u ^ 3)⁻¹ - u ^ 3)) +
        u * (Complex.exp ((100 / 30003 : ℂ) * ((u ^ 3)⁻¹ - u ^ 3)) *
          ((100 / 30003 : ℂ) * (-(3 * u ^ 2) / (u ^ 3) ^ 2 - 3 * u ^ 2))) := by
    unfold rootToSourceDerivative chapterVIDRootExponentialArgument
    field_simp [hu]
    ring
  rw [heq]
  simpa +instances [Pi.sub_apply, Pi.pow_apply] using! h

theorem continuous_rootToSourceDerivative_comp
    {X : Type*} [TopologicalSpace X] (u : X → ℂ)
    (hu : Continuous u) (hu0 : ∀ x, u x ≠ 0) :
    Continuous (fun x ↦ rootToSourceDerivative (u x)) := by
  unfold rootToSourceDerivative chapterVIDRootExponentialArgument
  have huneg : Continuous (fun x ↦ u x ^ (-3 : ℤ)) :=
    hu.zpow₀ (-3) (fun x ↦ Or.inl (hu0 x))
  have hupos : Continuous (fun x ↦ u x ^ (3 : ℕ)) := hu.pow 3
  have hargument : Continuous (fun x ↦
      (100 / 30003 : ℂ) * (u x ^ (-3 : ℤ) - u x ^ (3 : ℕ))) :=
    continuous_const.mul (huneg.sub hupos)
  exact (Complex.continuous_exp.comp hargument).mul
    (continuous_const.sub
      (continuous_const.mul (huneg.add hupos)))

/-- The derivative of the rational quarter-circle parametrization with respect to its real
parameter. -/
def rationalUnitQuarterVelocity (t : ℝ) : ℂ :=
  ((-4 * (t : ℂ)) + 2 * (1 - (t : ℂ) ^ 2) * Complex.I) /
    (1 + (t : ℂ) ^ 2) ^ 2

/-- The same rational quarter as a function on all real parameters. -/
def rationalUnitQuarterReal (t : ℝ) : ℂ :=
  (1 - (t : ℂ) ^ 2) / (1 + (t : ℂ) ^ 2) +
    (2 * (t : ℂ) / (1 + (t : ℂ) ^ 2)) * Complex.I

theorem rationalUnitQuarter_denominator_ne_zero (t : ℝ) :
    (1 + (t : ℂ) ^ 2) ≠ 0 := by
  exact_mod_cast (ne_of_gt (by positivity : 0 < 1 + t ^ 2))

/-- The rational velocity is exactly the real derivative of the extended quarter path. -/
theorem hasDerivAt_rationalUnitQuarterReal (t : ℝ) :
    HasDerivAt rationalUnitQuarterReal (rationalUnitQuarterVelocity t) t := by
  change HasDerivAt
    (fun t : ℝ ↦
      (1 - (t : ℂ) ^ 2) / (1 + (t : ℂ) ^ 2) +
        (2 * (t : ℂ) / (1 + (t : ℂ) ^ 2)) * Complex.I)
    (rationalUnitQuarterVelocity t) t
  have ht := (hasDerivAt_id t).ofReal_comp
  have hden := (hasDerivAt_const t (1 : ℂ)).add (ht.pow 2)
  have h := ((hasDerivAt_const t (1 : ℂ)).sub (ht.pow 2)).div hden
      (rationalUnitQuarter_denominator_ne_zero t) |>.add
    (((ht.const_mul (2 : ℂ)).div hden
      (rationalUnitQuarter_denominator_ne_zero t)).mul_const Complex.I)
  have heq : rationalUnitQuarterVelocity t =
      (-(2 * (t : ℂ) * (1 + (t : ℂ) ^ 2)) -
        (1 - (t : ℂ) ^ 2) * (2 * (t : ℂ))) /
          (1 + (t : ℂ) ^ 2) ^ 2 +
      (2 * (1 + (t : ℂ) ^ 2) -
        2 * (t : ℂ) * (2 * (t : ℂ))) /
          (1 + (t : ℂ) ^ 2) ^ 2 * Complex.I := by
    unfold rationalUnitQuarterVelocity
    field_simp [rationalUnitQuarter_denominator_ne_zero t]
    ring
  rw [heq]
  simpa +instances [Pi.add_apply, Pi.sub_apply, Pi.pow_apply] using! h

theorem rationalUnitQuarterReal_eq
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    rationalUnitQuarterReal t = chapterVIDRationalUnitQuarter ⟨t, ht⟩ := by
  simp [rationalUnitQuarterReal, chapterVIDRationalUnitQuarter]

theorem continuous_rationalUnitQuarterVelocity :
    Continuous rationalUnitQuarterVelocity := by
  unfold rationalUnitQuarterVelocity
  have ht : Continuous (fun t : ℝ ↦ (t : ℂ)) := Complex.ofRealCLM.continuous
  have hnumerator : Continuous (fun t : ℝ ↦
      (-4 * (t : ℂ)) + 2 * (1 - (t : ℂ) ^ 2) * Complex.I) := by
    fun_prop
  have hdenominator : Continuous (fun t : ℝ ↦ (1 + (t : ℂ) ^ 2) ^ 2) := by
    fun_prop
  exact hnumerator.div hdenominator
    (fun t ↦ pow_ne_zero 2 (rationalUnitQuarter_denominator_ne_zero t))

/-- Velocity of either oriented rational unit-circle quarter. -/
def rationalOuterArcUnitVelocity
    (side : ChapterVIDOuterArcSide) (t : ℝ) : ℂ :=
  match side with
  | .initial => rationalUnitQuarterVelocity t
  | .final => -Complex.I * rationalUnitQuarterVelocity t

/-- The corresponding real-parameter extension of either oriented outer quarter. -/
def rationalOuterArcUnitReal
    (side : ChapterVIDOuterArcSide) (t : ℝ) : ℂ :=
  match side with
  | .initial => rationalUnitQuarterReal t
  | .final => -Complex.I * rationalUnitQuarterReal t

theorem hasDerivAt_rationalOuterArcUnitReal
    (side : ChapterVIDOuterArcSide) (t : ℝ) :
    HasDerivAt (rationalOuterArcUnitReal side)
      (rationalOuterArcUnitVelocity side t) t := by
  cases side
  · exact hasDerivAt_rationalUnitQuarterReal t
  · change HasDerivAt (fun t ↦ -Complex.I * rationalUnitQuarterReal t)
      (-Complex.I * rationalUnitQuarterVelocity t) t
    simpa +instances using!
      (hasDerivAt_rationalUnitQuarterReal t).const_mul (-Complex.I)

theorem rationalOuterArcUnitReal_eq
    (side : ChapterVIDOuterArcSide) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    rationalOuterArcUnitReal side t =
      chapterVIDRationalOuterArcUnit side ⟨t, ht⟩ := by
  cases side
  · exact rationalUnitQuarterReal_eq ht
  · simp only [rationalOuterArcUnitReal, chapterVIDRationalOuterArcUnit]
    rw [rationalUnitQuarterReal_eq ht]

theorem continuous_rationalOuterArcUnitVelocity
    (side : ChapterVIDOuterArcSide) :
    Continuous (rationalOuterArcUnitVelocity side) := by
  cases side
  · change Continuous rationalUnitQuarterVelocity
    exact continuous_rationalUnitQuarterVelocity
  · change Continuous (fun t ↦ -Complex.I * rationalUnitQuarterVelocity t)
    exact continuous_const.mul continuous_rationalUnitQuarterVelocity

/-- The complete Jacobian `dt/dtau`: first differentiate `t(u)`, then the radial rational
quarter `u(tau)`.  The clamp affects only the continuous extension outside `[0,1]`; on the
interval of integration it is the identity. -/
def sourceVelocity
    (side : ChapterVIDOuterArcSide) (point : I × ℝ) : ℂ :=
  rootToSourceDerivative (rootCoordinate side point) *
    (chapterVIDCertificateContourRadius point.1 : ℂ) *
      rationalOuterArcUnitVelocity side point.2

/-- The unclamped root-coordinate path used to state the chain-rule theorem. -/
def rootCoordinateReal
    (side : ChapterVIDOuterArcSide) (s : I) (t : ℝ) : ℂ :=
  (chapterVIDCertificateContourRadius s : ℂ) *
    rationalOuterArcUnitReal side t

theorem hasDerivAt_rootCoordinateReal
    (side : ChapterVIDOuterArcSide) (s : I) (t : ℝ) :
    HasDerivAt (rootCoordinateReal side s)
      ((chapterVIDCertificateContourRadius s : ℂ) *
        rationalOuterArcUnitVelocity side t) t := by
  simpa +instances [rootCoordinateReal] using!
    (hasDerivAt_rationalOuterArcUnitReal side t).const_mul
      (chapterVIDCertificateContourRadius s : ℂ)

theorem rootCoordinateReal_eq
    (side : ChapterVIDOuterArcSide) (s : I) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    rootCoordinateReal side s t = rootCoordinate side (s, t) := by
  rw [rootCoordinate, chapterVIDOuterArcPoint, clampUnit_of_mem ht,
    rootCoordinateReal, rationalOuterArcUnitReal_eq side ht]

/-- On the interval of integration, `sourceVelocity` is exactly the derivative of the pulled-back
source contour. -/
theorem hasDerivAt_sourceContourReal
    (side : ChapterVIDOuterArcSide) (s : I) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    HasDerivAt
      (fun τ ↦ chapterVIDRootToOriginalContour (rootCoordinateReal side s τ))
      (sourceVelocity side (s, t)) t := by
  have hu : rootCoordinateReal side s t ≠ 0 := by
    rw [rootCoordinateReal_eq side s ht]
    exact rootCoordinate_ne_zero side (s, t)
  have hchain := (hasDerivAt_rootToOriginalContour hu).comp t
    (hasDerivAt_rootCoordinateReal side s t)
  have hvelocity : sourceVelocity side (s, t) =
      rootToSourceDerivative (rootCoordinateReal side s t) *
        ((chapterVIDCertificateContourRadius s : ℂ) *
          rationalOuterArcUnitVelocity side t) := by
    unfold sourceVelocity
    rw [rootCoordinateReal_eq side s ht]
    ring
  rw [hvelocity]
  simpa +instances only [Function.comp_apply] using! hchain

theorem continuous_sourceVelocity (side : ChapterVIDOuterArcSide) :
    Continuous (sourceVelocity side) := by
  unfold sourceVelocity
  exact ((continuous_rootToSourceDerivative_comp (rootCoordinate side)
      (continuous_rootCoordinate side) (rootCoordinate_ne_zero side)).mul
    (Complex.ofRealCLM.continuous.comp
      (continuous_chapterVIDCertificateContourRadius.comp continuous_fst))).mul
    ((continuous_rationalOuterArcUnitVelocity side).comp continuous_snd)

/-- The actual path in Poincare's original contour coordinate obtained from one root-coordinate
outer quarter. -/
def sourcePath (side : ChapterVIDOuterArcSide) (s : I) :
    Path (sourceContour side (s, 0)) (sourceContour side (s, 1)) where
  toFun τ := sourceContour side (s, τ)
  continuous_toFun := (continuous_sourceContour side).comp
    (continuous_const.prodMk continuous_subtype_val)
  source' := rfl
  target' := rfl

@[simp]
theorem sourcePath_apply
    (side : ChapterVIDOuterArcSide) (s τ : I) :
    sourcePath side s τ = sourceContour side (s, τ) :=
  rfl

theorem sourcePath_eq_rootCoordinateReal
    (side : ChapterVIDOuterArcSide) (s : I) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    sourcePath side s ⟨t, ht⟩ =
      chapterVIDRootToOriginalContour (rootCoordinateReal side s t) := by
  rw [sourcePath_apply, sourceContour, rootCoordinateReal_eq side s ht]

/-- Extend a certified square-root sheet from `I x I` to the real integration parameter. -/
def sheetRoot
    {side : ChapterVIDOuterArcSide}
    (sheet : ChapterVIContinuousSquareRootSheet (chapterVIDOuterArcRadicand side))
    (point : I × ℝ) : ℂ :=
  sheet.root (point.1, clampUnit point.2)

theorem continuous_sheetRoot
    {side : ChapterVIDOuterArcSide}
    (sheet : ChapterVIContinuousSquareRootSheet (chapterVIDOuterArcRadicand side)) :
    Continuous (sheetRoot sheet) :=
  sheet.continuous_root.comp
    (continuous_fst.prodMk (continuous_clampUnit.comp continuous_snd))

theorem sheetRoot_ne_zero_of_run
    (run : ChapterVIDOuterArcPolarCompiledGrid.CompiledRunVerdict)
    {side : ChapterVIDOuterArcSide}
    (sheet : ChapterVIContinuousSquareRootSheet (chapterVIDOuterArcRadicand side))
    (point : I × ℝ) :
    sheetRoot sheet point ≠ 0 :=
  sheet.root_ne_zero
    (ChapterVIDOuterArcPolarCompiledGrid.radicand_ne_zero_of_run run side
      (point.1, clampUnit point.2))

/-- Poincare's unnormalized principal contribution on one certified outer quarter. -/
def integral
    (massProduct : ℂ) (b d : ℤ) (side : ChapterVIDOuterArcSide)
    (sheet : ChapterVIContinuousSquareRootSheet (chapterVIDOuterArcRadicand side))
    (s : I) : ℂ :=
  ∫ τ in (0 : ℝ)..1,
    sourceNumerator massProduct b d side (s, τ) /
      sheetRoot sheet (s, τ) * sourceVelocity side (s, τ)

/-- Under explicit cubic-root and square-root branch agreement, the interval integral above is
literally the curve integral of Poincare's principal source integrand along `sourcePath`.  These
two compatibility hypotheses are exactly what the later global sheet-gluing theorem must
construct. -/
theorem integral_eq_curveIntegral
    (massProduct : ℂ) (b d : ℤ) (side : ChapterVIDOuterArcSide)
    (sheet : ChapterVIContinuousSquareRootSheet (chapterVIDOuterArcRadicand side))
    (zRoot : ℂ → ℂ) (sourceRoot : ℂ × ℂ → ℂ) (s : I)
    (hzRoot : zRoot (chapterVIDCommonParameterRootPath s ^ 3) =
      chapterVIDCommonParameterRootPath s)
    (hsourceRoot : ∀ τ : I,
      sourceRoot (chapterVIDCommonParameterRootPath s ^ 3, sourcePath side s τ) =
        sheet.root (s, τ)) :
    integral massProduct b d side sheet s =
      ∫ᶜ t in sourcePath side s,
        chapterVIComplexScalarOneForm
          (fun t ↦ chapterVIPrincipalSourceNumerator
              massProduct (-1) b 3 d zRoot
                (chapterVIDCommonParameterRootPath s ^ 3, t) /
            sourceRoot (chapterVIDCommonParameterRootPath s ^ 3, t)) t := by
  rw [integral, curveIntegral_def]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [Set.uIcc_of_le zero_le_one] at ht
  let rawPath : ℝ → ℂ := fun τ ↦
    chapterVIDRootToOriginalContour (rootCoordinateReal side s τ)
  have heq : Set.EqOn (sourcePath side s).extend rawPath (Set.Icc 0 1) := by
    intro τ hτ
    rw [Path.extend_apply (sourcePath side s) hτ]
    exact sourcePath_eq_rootCoordinateReal side s hτ
  rw [curveIntegralFun_def, derivWithin_congr heq (heq ht), heq ht]
  have hderiv := hasDerivAt_sourceContourReal side s ht
  change HasDerivAt rawPath (sourceVelocity side (s, t)) t at hderiv
  rw [hderiv.hasDerivWithinAt.derivWithin
    (uniqueDiffOn_Icc_zero_one t ht)]
  rw [chapterVIComplexScalarOneForm_apply]
  have hraw : rawPath t = sourceContour side (s, t) := by
    dsimp only [rawPath]
    rw [rootCoordinateReal_eq side s ht]
    rfl
  rw [hraw]
  have hnumerator : sourceNumerator massProduct b d side (s, t) =
      chapterVIPrincipalSourceNumerator massProduct (-1) b 3 d zRoot
        (chapterVIDCommonParameterRootPath s ^ 3, sourceContour side (s, t)) := by
    simpa [parameterRoot] using sourceNumerator_eq_principalSourceNumerator
      massProduct b d zRoot side (s, t) (by simpa [parameterRoot] using hzRoot)
  have hroot : sourceRoot
      (chapterVIDCommonParameterRootPath s ^ 3, sourceContour side (s, t)) =
      sheetRoot sheet (s, t) := by
    simpa [sourcePath_apply, sheetRoot, clampUnit_of_mem ht] using
      hsourceRoot ⟨t, ht⟩
  rw [← hnumerator, hroot]
  ring

/-- The entire outer-quarter integral is continuous up to and including Poincare's collision
parameter. -/
theorem continuous_integral_of_run
    (run : ChapterVIDOuterArcPolarCompiledGrid.CompiledRunVerdict)
    (massProduct : ℂ) (b d : ℤ) (side : ChapterVIDOuterArcSide)
    (sheet : ChapterVIContinuousSquareRootSheet (chapterVIDOuterArcRadicand side)) :
    Continuous (integral massProduct b d side sheet) := by
  apply continuous_chapterVIParametricOuterArcIntegral
    (fun s τ ↦ sourceNumerator massProduct b d side (s, τ))
    (fun s τ ↦ sheetRoot sheet (s, τ))
    (fun s τ ↦ sourceVelocity side (s, τ))
  · exact continuous_sourceNumerator massProduct b d side
  · exact continuous_sheetRoot sheet
  · exact continuous_sourceVelocity side
  · exact fun s τ ↦ sheetRoot_ne_zero_of_run run sheet (s, τ)

/-- In particular, the regular arc has an ordinary finite endpoint limit at D. -/
theorem tendsto_integral_collision_of_run
    (run : ChapterVIDOuterArcPolarCompiledGrid.CompiledRunVerdict)
    (massProduct : ℂ) (b d : ℤ) (side : ChapterVIDOuterArcSide)
    (sheet : ChapterVIContinuousSquareRootSheet (chapterVIDOuterArcRadicand side)) :
    Tendsto (integral massProduct b d side sheet) (nhds (1 : I))
      (nhds (integral massProduct b d side sheet 1)) :=
  (continuous_integral_of_run run massProduct b d side sheet).continuousAt

/-- The compiled verdict supplies a sheet for each outer quarter and hence a certified finite
endpoint limit.  The returned sheet is intentionally visible, because its sign must later be
matched to the middle local branch. -/
theorem exists_sheet_tendsto_integral_collision_of_run
    (run : ChapterVIDOuterArcPolarCompiledGrid.CompiledRunVerdict)
    (massProduct : ℂ) (b d : ℤ) (side : ChapterVIDOuterArcSide) :
    ∃ sheet : ChapterVIContinuousSquareRootSheet (chapterVIDOuterArcRadicand side),
      Tendsto (integral massProduct b d side sheet) (nhds (1 : I))
        (nhds (integral massProduct b d side sheet 1)) := by
  let base : I × I := (0, 0)
  obtain ⟨baseRoot, hbaseRoot⟩ :=
    IsAlgClosed.exists_pow_nat_eq (chapterVIDOuterArcRadicand side base)
      (by norm_num : 0 < (2 : ℕ))
  obtain ⟨sheet, _⟩ :=
    ChapterVIDOuterArcPolarCompiledGrid.exists_squareRootSheet_of_run
      run side base baseRoot hbaseRoot
  exact ⟨sheet, tendsto_integral_collision_of_run run massProduct b d side sheet⟩

/-- The normalized sum of the two pieces complementary to Poincare's pinched middle arc. -/
def regularContribution
    (massProduct : ℂ) (b d : ℤ)
    (initialSheet : ChapterVIContinuousSquareRootSheet
      (chapterVIDOuterArcRadicand .initial))
    (finalSheet : ChapterVIContinuousSquareRootSheet
      (chapterVIDOuterArcRadicand .final))
    (s : I) : ℂ :=
  (2 * Real.pi * Complex.I : ℂ)⁻¹ *
    (integral massProduct b d .initial initialSheet s +
      integral massProduct b d .final finalSheet s)

theorem continuous_regularContribution_of_run
    (run : ChapterVIDOuterArcPolarCompiledGrid.CompiledRunVerdict)
    (massProduct : ℂ) (b d : ℤ)
    (initialSheet : ChapterVIContinuousSquareRootSheet
      (chapterVIDOuterArcRadicand .initial))
    (finalSheet : ChapterVIContinuousSquareRootSheet
      (chapterVIDOuterArcRadicand .final)) :
    Continuous (regularContribution massProduct b d initialSheet finalSheet) := by
  unfold regularContribution
  exact continuous_const.mul
    ((continuous_integral_of_run run massProduct b d .initial initialSheet).add
      (continuous_integral_of_run run massProduct b d .final finalSheet))

/-- The complete certified regular contribution has a finite limit at D. -/
theorem tendsto_regularContribution_collision_of_run
    (run : ChapterVIDOuterArcPolarCompiledGrid.CompiledRunVerdict)
    (massProduct : ℂ) (b d : ℤ)
    (initialSheet : ChapterVIContinuousSquareRootSheet
      (chapterVIDOuterArcRadicand .initial))
    (finalSheet : ChapterVIContinuousSquareRootSheet
      (chapterVIDOuterArcRadicand .final)) :
    Tendsto (regularContribution massProduct b d initialSheet finalSheet)
      (nhds (1 : I))
      (nhds (regularContribution massProduct b d initialSheet finalSheet 1)) :=
  (continuous_regularContribution_of_run run massProduct b d
    initialSheet finalSheet).continuousAt

/-- A compiled run supplies some square-root sheet on each outer rectangle and proves that their
normalized sum has a finite limit.  Compatibility of their two signs with the middle sheet is
not asserted by this existential theorem. -/
theorem exists_sheets_tendsto_regularContribution_collision_of_run
    (run : ChapterVIDOuterArcPolarCompiledGrid.CompiledRunVerdict)
    (massProduct : ℂ) (b d : ℤ) :
    ∃ (initialSheet : ChapterVIContinuousSquareRootSheet
        (chapterVIDOuterArcRadicand .initial))
      (finalSheet : ChapterVIContinuousSquareRootSheet
        (chapterVIDOuterArcRadicand .final)),
      Tendsto (regularContribution massProduct b d initialSheet finalSheet)
        (nhds (1 : I))
        (nhds (regularContribution massProduct b d initialSheet finalSheet 1)) := by
  obtain ⟨initialSheet, _⟩ :=
    exists_sheet_tendsto_integral_collision_of_run run massProduct b d .initial
  obtain ⟨finalSheet, _⟩ :=
    exists_sheet_tendsto_integral_collision_of_run run massProduct b d .final
  exact ⟨initialSheet, finalSheet,
    tendsto_regularContribution_collision_of_run run massProduct b d
      initialSheet finalSheet⟩

end ChapterVIDOuterArcRegularity

end PoincareChapterVI
