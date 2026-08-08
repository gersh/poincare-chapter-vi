/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.ChapterVIDTransversality
import PoincareChapterVI.ChapterVICycleDecomposition
import PoincareChapterVI.ChapterVIDRootCoordinates

/-!
# The principal §94 integrand at Poincaré's point D

Poincaré defines

`F(z,t) = F₁⁰(z,t) t^(ad-bc-1) z^(-d/c)`.

For the principal mutual-distance term, `F₁⁰` is a nonzero mass factor divided by the square root
of the collision radicand.  The radicand and its local square-root sheet are handled elsewhere;
this file formalizes the previously implicit analytic numerator

`massProduct * t^(ad-bc-1) * (z^(1/c))^(-d)`.

At the concrete point D one has `a=-1` and `c=3`.  We construct a local cubic-root branch of
`z` and prove that the complete numerator is analytic and nonzero there.  Thus the nonvanishing
of Poincaré's logarithmic amplitude is not left as an arbitrary-numerator assumption.
-/

noncomputable section

open Filter Topology

namespace PoincareChapterVI

/-- The analytic numerator multiplying the inverse collision root in Poincaré's §94 integrand.
The function `zRoot` records the locally selected determination of `z^(1/c)`. -/
def chapterVIPrincipalSourceNumerator
    (massProduct : ℂ) (a b c d : ℤ) (zRoot : ℂ → ℂ) (point : ℂ × ℂ) : ℂ :=
  massProduct * point.2 ^ (a * d - b * c - 1) * zRoot point.1 ^ (-d)

/-- Analyticity of the §94 numerator on any chosen nonzero local root sheet. -/
theorem analyticAt_chapterVIPrincipalSourceNumerator
    {massProduct : ℂ} {a b c d : ℤ} {zRoot : ℂ → ℂ} {point : ℂ × ℂ}
    (ht : point.2 ≠ 0)
    (hroot : AnalyticAt ℂ zRoot point.1)
    (hroot_ne : zRoot point.1 ≠ 0) :
    AnalyticAt ℂ
      (chapterVIPrincipalSourceNumerator massProduct a b c d zRoot) point := by
  unfold chapterVIPrincipalSourceNumerator
  exact (analyticAt_const.mul (analyticAt_snd.zpow ht)).mul
    ((hroot.comp analyticAt_fst).zpow hroot_ne)

/-- The §94 numerator cannot cancel the pinch when the physical mass factor and both monomial
bases are nonzero. -/
theorem chapterVIPrincipalSourceNumerator_ne_zero
    {massProduct : ℂ} {a b c d : ℤ} {zRoot : ℂ → ℂ} {point : ℂ × ℂ}
    (hmass : massProduct ≠ 0) (ht : point.2 ≠ 0) (hroot : zRoot point.1 ≠ 0) :
    chapterVIPrincipalSourceNumerator massProduct a b c d zRoot point ≠ 0 := by
  unfold chapterVIPrincipalSourceNumerator
  exact mul_ne_zero (mul_ne_zero hmass (zpow_ne_zero _ ht)) (zpow_ne_zero _ hroot)

/-- Poincaré's external parameter at D is nonzero. -/
theorem chapterVIDZBase_ne_zero : chapterVIDZBase ≠ 0 := by
  unfold chapterVIDZBase chapterVIContourBase chapterVIMeanToContourMap
  exact mul_ne_zero
    (zpow_ne_zero _
      (chapterVIKeplerExponential_ne_zero chapterVIDEccentricity chapterVIDX_ne_zero))
    (zpow_ne_zero _ (chapterVIKeplerExponential_ne_zero 0 chapterVIDY_ne_zero))

/-- The source `z` coordinate at D is exactly the positive real critical parameter used by the
global root-coordinate path.  Placing this theorem before the local root choice lets the local
germ use the same determination as the global continuation. -/
theorem chapterVIDZBase_eq_criticalParameter :
    chapterVIDZBase = (chapterVIDCriticalParameterModulus : ℂ) := by
  have hsource := chapterVI_singularityParameter_eq_keplerExponential_zpow
    (-1) 3 chapterVIDEccentricity 0 chapterVIDX chapterVIDY
  have hcurve := chapterVID_singularityParameter_curveThree_eq_smooth
    chapterVIDRoot_lt_zero
  rw [chapterVIDCurveThreeY_at_root] at hcurve
  unfold chapterVIDZBase chapterVIContourBase chapterVIMeanToContourMap
  change chapterVIKeplerExponential chapterVIDEccentricity chapterVIDX ^ (-1 : ℤ) *
      chapterVIKeplerExponential 0 chapterVIDY ^ (3 : ℤ) = _
  rw [← hsource]
  have hscale : -chapterVIDEccentricity / 2 = (-100 / 10001 : ℂ) := by
    norm_num [chapterVIDEccentricity]
  norm_num only [Int.cast_negSucc, Int.cast_ofNat, neg_mul, one_mul, mul_zero,
    zero_div]
  rw [hscale]
  simpa [chapterVIDX, chapterVIDCriticalParameterModulus] using hcurve

/-- The local determination of `z_D^(1/3)` is the positive real root selected by the global
parameter path, rather than an arbitrary algebraic cube root. -/
noncomputable def chapterVIDZRootBase : ℂ :=
  chapterVIPositiveRealCubicLift chapterVIDCriticalParameterModulus

@[simp]
theorem chapterVIDZRootBase_pow : chapterVIDZRootBase ^ (3 : ℤ) = chapterVIDZBase := by
  rw [zpow_ofNat, chapterVIDZRootBase,
    chapterVIPositiveRealCubicLift_pow chapterVIDCriticalParameterModulus_pos.le,
    chapterVIDZBase_eq_criticalParameter]

/-- The canonical base is, in particular, a cube root of the source parameter. -/
theorem exists_chapterVIDZRootBase : ∃ root : ℂ, root ^ 3 = chapterVIDZBase := by
  exact ⟨chapterVIDZRootBase, by simpa only [zpow_ofNat] using chapterVIDZRootBase_pow⟩

/-- The local and global cubic-root choices agree exactly at D. -/
theorem chapterVIDZRootBase_eq_commonParameterRootPath_one :
    chapterVIDZRootBase = chapterVIDCommonParameterRootPath 1 := by
  unfold chapterVIDZRootBase chapterVIDCommonParameterRootPath
  simp [Path.segment, AffineMap.lineMap_apply]

theorem chapterVIDZRootBase_ne_zero : chapterVIDZRootBase ≠ 0 := by
  intro hzero
  apply chapterVIDZBase_ne_zero
  rw [← chapterVIDZRootBase_pow, hzero]
  norm_num

/-- The local analytic determination of `z^(1/3)` based at D. -/
def chapterVIDZRoot : ℂ → ℂ :=
  chapterVIPowerLocalInverse 3 chapterVIDZRootBase chapterVIDZRootBase_ne_zero
    (by norm_num)

@[simp]
theorem chapterVIDZRoot_base : chapterVIDZRoot chapterVIDZBase = chapterVIDZRootBase := by
  unfold chapterVIDZRoot
  rw [← chapterVIDZRootBase_pow]
  exact chapterVIPowerLocalInverse_apply_base 3 chapterVIDZRootBase
    chapterVIDZRootBase_ne_zero (by norm_num)

theorem analyticAt_chapterVIDZRoot : AnalyticAt ℂ chapterVIDZRoot chapterVIDZBase := by
  unfold chapterVIDZRoot
  rw [← chapterVIDZRootBase_pow]
  exact analyticAt_chapterVIPowerLocalInverse 3 chapterVIDZRootBase
    chapterVIDZRootBase_ne_zero (by norm_num)

/-- The selected determination really cubes back to `z` near D. -/
theorem eventually_chapterVIDZRoot_pow :
    (fun z : ℂ ↦ chapterVIDZRoot z ^ (3 : ℤ)) =ᶠ[𝓝 chapterVIDZBase] fun z ↦ z := by
  unfold chapterVIDZRoot
  rw [← chapterVIDZRootBase_pow]
  exact eventually_zpow_chapterVIPowerLocalInverse 3 chapterVIDZRootBase
    chapterVIDZRootBase_ne_zero (by norm_num)

/-- Near D, the local analytic cubic-root germ is literally the restriction of the global
positive-real root path. -/
theorem eventually_chapterVIDZRoot_commonParameterRootPath :
    (fun s : unitInterval ↦
      chapterVIDZRoot (chapterVIDCommonParameterRootPath s ^ (3 : ℤ))) =ᶠ[
      nhds (1 : unitInterval)] chapterVIDCommonParameterRootPath := by
  have hlocal := eventually_chapterVIPowerLocalInverse_zpow
    3 chapterVIDZRootBase chapterVIDZRootBase_ne_zero (by norm_num)
  have htend : Tendsto chapterVIDCommonParameterRootPath (nhds (1 : unitInterval))
      (nhds chapterVIDZRootBase) := by
    rw [chapterVIDZRootBase_eq_commonParameterRootPath_one]
    exact chapterVIDCommonParameterRootPath.continuous.continuousAt
  unfold chapterVIDZRoot
  convert hlocal.comp_tendsto htend using 1 <;> rfl

/-- The literal numerator in the principal §94 integrand, specialized to D's ray direction
`(a,c)=(-1,3)` while retaining the finite offsets `(b,d)`. -/
def chapterVIDPrincipalSourceNumerator
    (massProduct : ℂ) (b d : ℤ) : ℂ × ℂ → ℂ :=
  chapterVIPrincipalSourceNumerator massProduct (-1) b 3 d chapterVIDZRoot

/-- Poincaré's literal principal contour integrand on an explicitly selected square-root sheet.
The sheet is an argument because the collision root has no single global determination. -/
def chapterVIDPrincipalPhiIntegrand
    (massProduct : ℂ) (b d : ℤ) (sourceRoot : ℂ × ℂ → ℂ)
    (z t : ℂ) : ℂ :=
  chapterVIDPrincipalSourceNumerator massProduct b d (z, t) / sourceRoot (z, t)

/-- The §94 unit-circle `Φ` for the actual principal mutual-distance term and a selected root
sheet.  Later contour deformation must certify that the same sheet continues along the path. -/
def chapterVIDPrincipalPhi
    (massProduct : ℂ) (b d : ℤ) (sourceRoot : ℂ × ℂ → ℂ) (z : ℂ) : ℂ :=
  chapterVIPhi (chapterVIDPrincipalPhiIntegrand massProduct b d sourceRoot) z

theorem analyticAt_chapterVIDPrincipalSourceNumerator
    (massProduct : ℂ) (b d : ℤ) :
    AnalyticAt ℂ (chapterVIDPrincipalSourceNumerator massProduct b d)
      (chapterVIDZBase, chapterVIDTBase) := by
  exact analyticAt_chapterVIPrincipalSourceNumerator chapterVIDTBase_ne_zero
    analyticAt_chapterVIDZRoot (by simpa using chapterVIDZRootBase_ne_zero)

theorem chapterVIDPrincipalSourceNumerator_base_ne_zero
    {massProduct : ℂ} (b d : ℤ) (hmass : massProduct ≠ 0) :
    chapterVIDPrincipalSourceNumerator massProduct b d
        (chapterVIDZBase, chapterVIDTBase) ≠ 0 := by
  exact chapterVIPrincipalSourceNumerator_ne_zero hmass chapterVIDTBase_ne_zero
    (by simpa using chapterVIDZRootBase_ne_zero)

/-- The actual Morse-coordinate amplitude for Poincaré's principal integrand. -/
def chapterVIDPrincipalMorseAmplitude
    (massProduct : ℂ) (b d : ℤ) : ℂ × ℂ → ℂ :=
  chapterVIDCriticalMorseAmplitudeAtD
    (chapterVIDPrincipalSourceNumerator massProduct b d)

theorem analyticAt_chapterVIDPrincipalMorseAmplitude
    (massProduct : ℂ) (b d : ℤ) :
    AnalyticAt ℂ (chapterVIDPrincipalMorseAmplitude massProduct b d) (0, 0) :=
  analyticAt_chapterVIDCriticalMorseAmplitudeAtD
    (analyticAt_chapterVIDPrincipalSourceNumerator massProduct b d)

/-- The exact leading amplitude corresponding to Poincaré's displayed identity on p. 323.  In
particular, the prepared quadratic factor contributes the inverse Morse root, not the second
derivative itself. -/
theorem chapterVIDPrincipalMorseAmplitude_base
    (massProduct : ℂ) (b d : ℤ) :
    chapterVIDPrincipalMorseAmplitude massProduct b d (0, 0) =
      chapterVIDPrincipalSourceNumerator massProduct b d
          (chapterVIDZBase, chapterVIDTBase) * chapterVIDMorseRootBase⁻¹ := by
  exact chapterVIDCriticalMorseAmplitude_base
    deriv_chapterVIDCriticalValue_ne_zero
    (chapterVIDPrincipalSourceNumerator massProduct b d)

/-- For nonzero masses, the actual principal amplitude at the pinch is nonzero. -/
theorem chapterVIDPrincipalMorseAmplitude_base_ne_zero
    {massProduct : ℂ} (b d : ℤ) (hmass : massProduct ≠ 0) :
    chapterVIDPrincipalMorseAmplitude massProduct b d (0, 0) ≠ 0 := by
  rw [chapterVIDPrincipalMorseAmplitude_base]
  exact mul_ne_zero
    (chapterVIDPrincipalSourceNumerator_base_ne_zero b d hmass)
    (inv_ne_zero chapterVIDMorseRootBase_ne_zero)

end PoincareChapterVI
