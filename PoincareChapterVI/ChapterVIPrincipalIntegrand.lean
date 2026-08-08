/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.ChapterVIDTransversality
import PoincareChapterVI.ChapterVICycleDecomposition

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

/-- Choose the determination of `z_D^(1/3)` through which the local §94 integrand is continued. -/
theorem exists_chapterVIDZRootBase : ∃ root : ℂ, root ^ 3 = chapterVIDZBase :=
  IsAlgClosed.exists_pow_nat_eq chapterVIDZBase (by norm_num)

noncomputable def chapterVIDZRootBase : ℂ :=
  Classical.choose exists_chapterVIDZRootBase

@[simp]
theorem chapterVIDZRootBase_pow : chapterVIDZRootBase ^ (3 : ℤ) = chapterVIDZBase := by
  unfold chapterVIDZRootBase
  simpa only [zpow_ofNat] using Classical.choose_spec exists_chapterVIDZRootBase

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
