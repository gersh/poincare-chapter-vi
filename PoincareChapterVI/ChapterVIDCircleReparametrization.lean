/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.ChapterVIDGlobalLiftedPrefix
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Topology.Order.MonotoneContinuity

/-!
# The exact root-to-source circle reparametrization

On the root-coordinate unit circle, Poincare's exact change of contour variable changes only
the angular parameter.  Its real angular lift is

`theta |-> theta - (200 / 30003) sin (3 theta)`.

The derivative is uniformly positive.  Consequently the image of the root-coordinate circle is
the literal source circle with an orientation-preserving reparametrization, rather than merely a
homotopic loop with the same norm.
-/

noncomputable section

open Complex Real Set Topology
open scoped unitInterval

namespace PoincareChapterVI

/-- The real angular lift of Poincare's exact `u -> t` coordinate change on `|u|=1`. -/
def chapterVIDCircleAngularWarp (theta : ℝ) : ℝ :=
  theta - (200 / 30003 : ℝ) * Real.sin (3 * theta)

theorem hasDerivAt_chapterVIDCircleAngularWarp (theta : ℝ) :
    HasDerivAt chapterVIDCircleAngularWarp
      (1 - (600 / 30003 : ℝ) * Real.cos (3 * theta)) theta := by
  have hinner : HasDerivAt (fun x : ℝ ↦ 3 * x) 3 theta :=
    hasDerivAt_const_mul 3
  have hsin : HasDerivAt (fun x : ℝ ↦ Real.sin (3 * x))
      (Real.cos (3 * theta) * 3) theta :=
    (Real.hasDerivAt_sin (3 * theta)).comp theta hinner
  have hscaled : HasDerivAt
      (fun x : ℝ ↦ (200 / 30003 : ℝ) * Real.sin (3 * x))
      ((200 / 30003 : ℝ) * (Real.cos (3 * theta) * 3)) theta :=
    hsin.const_mul (200 / 30003 : ℝ)
  have hcoef :
      (1 - (600 / 30003 : ℝ) * Real.cos (3 * theta)) =
        1 - (200 / 30003 : ℝ) * (Real.cos (3 * theta) * 3) := by
    ring
  rw [hcoef]
  exact (hasDerivAt_id theta).sub hscaled

theorem chapterVIDCircleAngularWarp_deriv_pos (theta : ℝ) :
    0 < deriv chapterVIDCircleAngularWarp theta := by
  rw [(hasDerivAt_chapterVIDCircleAngularWarp theta).deriv]
  have hcos := Real.cos_le_one (3 * theta)
  nlinarith

theorem strictMono_chapterVIDCircleAngularWarp :
    StrictMono chapterVIDCircleAngularWarp :=
  strictMono_of_deriv_pos chapterVIDCircleAngularWarp_deriv_pos

theorem continuous_chapterVIDCircleAngularWarp :
    Continuous chapterVIDCircleAngularWarp := by
  exact continuous_id.sub
    (continuous_const.mul (Real.continuous_sin.comp (continuous_const.mul continuous_id)))

@[simp] theorem chapterVIDCircleAngularWarp_zero :
    chapterVIDCircleAngularWarp 0 = 0 := by
  simp [chapterVIDCircleAngularWarp]

@[simp] theorem chapterVIDCircleAngularWarp_two_pi :
    chapterVIDCircleAngularWarp (2 * Real.pi) = 2 * Real.pi := by
  unfold chapterVIDCircleAngularWarp
  rw [show 3 * (2 * Real.pi) = (6 : ℕ) * Real.pi by ring,
    Real.sin_nat_mul_pi]
  ring

/-- The induced increasing self-map of the unit interval. -/
def chapterVIDCircleTimeWarp (s : I) : I := by
  let theta := 2 * Real.pi * (s : ℝ)
  have htheta0 : 0 ≤ theta :=
    mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) s.property.1
  have htheta1 : theta ≤ 2 * Real.pi := by
    dsimp [theta]
    exact mul_le_of_le_one_right
      (mul_nonneg (by norm_num) Real.pi_pos.le) s.property.2
  have hwarp0 : 0 ≤ chapterVIDCircleAngularWarp theta := by
    rw [← chapterVIDCircleAngularWarp_zero]
    exact strictMono_chapterVIDCircleAngularWarp.monotone htheta0
  have hwarp1 : chapterVIDCircleAngularWarp theta ≤ 2 * Real.pi := by
    rw [← chapterVIDCircleAngularWarp_two_pi]
    exact strictMono_chapterVIDCircleAngularWarp.monotone htheta1
  exact ⟨chapterVIDCircleAngularWarp theta / (2 * Real.pi),
    div_nonneg hwarp0 (mul_nonneg (by norm_num) Real.pi_pos.le),
    (div_le_one (mul_pos (by norm_num) Real.pi_pos)).mpr hwarp1⟩

theorem continuous_chapterVIDCircleTimeWarp :
    Continuous chapterVIDCircleTimeWarp := by
  apply Continuous.subtype_mk
  change Continuous (fun s : I ↦
    chapterVIDCircleAngularWarp (2 * Real.pi * (s : ℝ)) / (2 * Real.pi))
  exact (continuous_chapterVIDCircleAngularWarp.comp
    (continuous_const.mul continuous_subtype_val)).div_const _

@[simp] theorem chapterVIDCircleTimeWarp_zero :
    chapterVIDCircleTimeWarp 0 = 0 := by
  apply Subtype.ext
  simp [chapterVIDCircleTimeWarp]

@[simp] theorem chapterVIDCircleTimeWarp_one :
    chapterVIDCircleTimeWarp 1 = 1 := by
  apply Subtype.ext
  simp [chapterVIDCircleTimeWarp]

/-- The time warp is orientation preserving, not merely endpoint preserving. -/
theorem strictMono_chapterVIDCircleTimeWarp :
    StrictMono chapterVIDCircleTimeWarp := by
  intro a b hab
  change chapterVIDCircleAngularWarp (2 * Real.pi * (a : ℝ)) / (2 * Real.pi) <
    chapterVIDCircleAngularWarp (2 * Real.pi * (b : ℝ)) / (2 * Real.pi)
  apply div_lt_div_of_pos_right _ (mul_pos (by norm_num) Real.pi_pos)
  apply strictMono_chapterVIDCircleAngularWarp
  exact mul_lt_mul_of_pos_left hab (mul_pos (by norm_num) Real.pi_pos)

/-- The endpoint-preserving continuous time warp covers the complete unit interval. -/
theorem surjective_chapterVIDCircleTimeWarp :
    Function.Surjective chapterVIDCircleTimeWarp := by
  intro t
  have hcontinuous : Continuous (Set.IccExtend (zero_le_one' ℝ)
      chapterVIDCircleTimeWarp) :=
    continuous_chapterVIDCircleTimeWarp.Icc_extend'
  have hintermediate := intermediate_value_Icc (zero_le_one' ℝ)
    hcontinuous.continuousOn
  rw [Set.IccExtend_left, Set.IccExtend_right, Icc.mk_zero, Icc.mk_one,
    chapterVIDCircleTimeWarp_zero, chapterVIDCircleTimeWarp_one] at hintermediate
  rcases hintermediate t.2 with ⟨s, hs, hst⟩
  rw [Set.IccExtend_of_mem _ _ hs] at hst
  exact ⟨⟨s, hs⟩, hst⟩

/-- The circle time warp as an order isomorphism.  Its inverse is the exact parameter needed
to pull the historical source-circle sheet back to the root circle. -/
noncomputable def chapterVIDCircleTimeOrderIso : I ≃o I :=
  StrictMono.orderIsoOfSurjective chapterVIDCircleTimeWarp
    strictMono_chapterVIDCircleTimeWarp surjective_chapterVIDCircleTimeWarp

/-- Source-circle time as a function of root-circle time, inverted. -/
noncomputable def chapterVIDCircleSourceToRootTime (s : I) : I :=
  chapterVIDCircleTimeOrderIso.symm s

theorem continuous_chapterVIDCircleSourceToRootTime :
    Continuous chapterVIDCircleSourceToRootTime :=
  chapterVIDCircleTimeOrderIso.symm.continuous

@[simp] theorem chapterVIDCircleSourceToRootTime_timeWarp (s : I) :
    chapterVIDCircleSourceToRootTime (chapterVIDCircleTimeWarp s) = s :=
  chapterVIDCircleTimeOrderIso.symm_apply_apply s

@[simp] theorem chapterVIDCircleTimeWarp_sourceToRootTime (s : I) :
    chapterVIDCircleTimeWarp (chapterVIDCircleSourceToRootTime s) = s :=
  chapterVIDCircleTimeOrderIso.apply_symm_apply s

/-- On `|u|=1`, the transcendental exponent is the displayed purely imaginary angular
correction. -/
theorem chapterVIDRootExponentialArgument_circleMap (theta : ℝ) :
    chapterVIDRootExponentialArgument (circleMap 0 1 theta) =
      ((-(200 / 30003 : ℝ) * Real.sin (3 * theta) : ℝ) : ℂ) * Complex.I := by
  unfold chapterVIDRootExponentialArgument
  rw [circleMap_zero_pow, circleMap_zero_inv]
  norm_num only [one_pow, inv_one]
  have hexp (x : ℝ) :
      Complex.exp ((-x : ℝ) * Complex.I) -
          Complex.exp (x * Complex.I) =
        ((-2 * Real.sin x : ℝ) : ℂ) * Complex.I := by
    rw [Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I]
    rw [Real.cos_neg, Real.sin_neg]
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring
  rw [circleMap_zero, circleMap_zero]
  norm_num only [Complex.ofReal_one, one_mul]
  rw [hexp (3 * theta)]
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

/-- The exact coordinate change on the unit circle is the angular warp above. -/
theorem chapterVIDRootToOriginalContour_circleMap (theta : ℝ) :
    chapterVIDRootToOriginalContour (circleMap 0 1 theta) =
      circleMap 0 1 (chapterVIDCircleAngularWarp theta) := by
  rw [chapterVIDRootToOriginalContour, chapterVIDRootExponentialArgument_circleMap]
  simp only [circleMap_zero, one_mul, Complex.ofReal_neg, Complex.ofReal_mul,
    Complex.ofReal_div, Complex.ofReal_ofNat]
  calc
    (1 : ℂ) * Complex.exp ((theta : ℂ) * Complex.I) *
        Complex.exp ((-(200 / 30003 : ℂ) *
          (Real.sin (3 * theta) : ℂ)) * Complex.I) =
      Complex.exp (((theta : ℂ) * Complex.I) +
        ((-(200 / 30003 : ℂ) *
          (Real.sin (3 * theta) : ℂ)) * Complex.I)) := by
        simp only [one_mul]
        rw [Complex.exp_add]
    _ = (1 : ℂ) *
        Complex.exp ((chapterVIDCircleAngularWarp theta : ℂ) * Complex.I) := by
      rw [one_mul]
      congr 1
      rw [show (chapterVIDCircleAngularWarp theta : ℂ) =
        (theta : ℂ) - (200 / 30003 : ℂ) *
          (Real.sin (3 * theta) : ℂ) by
            norm_num [chapterVIDCircleAngularWarp]]
      ring

/-- Pointwise, the source image of the root-coordinate unit circle is the standard circle
reparametrized by `chapterVIDCircleTimeWarp`. -/
theorem chapterVIDRootMappedUnitCirclePath_eq_reparam_apply (s : I) :
    chapterVIDRootMappedUnitCirclePath s =
      chapterVIUnitCirclePath (chapterVIDCircleTimeWarp s) := by
  rw [chapterVIDRootMappedUnitCirclePath_apply]
  change chapterVIDRootToOriginalContour
      (circleMap 0 1 (AffineMap.lineMap 0 (2 * Real.pi) (s : ℝ))) = _
  rw [chapterVIDRootToOriginalContour_circleMap]
  change circleMap 0 1
      (chapterVIDCircleAngularWarp (AffineMap.lineMap 0 (2 * Real.pi) (s : ℝ))) =
    circleMap 0 1
      (AffineMap.lineMap 0 (2 * Real.pi) (chapterVIDCircleTimeWarp s : ℝ))
  congr 1
  simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, smul_eq_mul,
    sub_zero, mul_zero]
  simp only [add_zero]
  rw [show (chapterVIDCircleTimeWarp s : ℝ) =
      chapterVIDCircleAngularWarp (2 * Real.pi * (s : ℝ)) /
        (2 * Real.pi) by rfl]
  rw [mul_comm (s : ℝ) (2 * Real.pi)]
  field_simp [show (2 * Real.pi : ℝ) ≠ 0 by positivity]

/-- The mapped root circle is exactly a reparametrization of the literal source circle. -/
theorem chapterVIDRootMappedUnitCirclePath_eq_reparam :
    chapterVIDRootMappedUnitCirclePath =
      chapterVIUnitCirclePath.reparam chapterVIDCircleTimeWarp
        continuous_chapterVIDCircleTimeWarp
        chapterVIDCircleTimeWarp_zero chapterVIDCircleTimeWarp_one := by
  ext s
  exact chapterVIDRootMappedUnitCirclePath_eq_reparam_apply s

/-- In particular, the mapped root circle and the historical source circle have exactly the
same image.  The preceding strict-monotonicity theorem records that their orientations agree. -/
theorem chapterVIDRootMappedUnitCirclePath_range :
    Set.range chapterVIDRootMappedUnitCirclePath =
      Set.range chapterVIUnitCirclePath := by
  rw [chapterVIDRootMappedUnitCirclePath_eq_reparam]
  exact Path.range_reparam chapterVIUnitCirclePath
    continuous_chapterVIDCircleTimeWarp
    chapterVIDCircleTimeWarp_zero chapterVIDCircleTimeWarp_one

/-! ## Exact transport of the initial square-root sheet -/

/-- The initial source-circle radicand, with the root coordinate recovered by the exact inverse
time warp.  Its contour point is the literal historical unit circle by the next theorem. -/
def chapterVIDInitialSourceCircleRadicand (s : I) : ℂ :=
  ChapterVIDGlobalLiftedPrefix.standardRadicand 0
    (chapterVIDCircleSourceToRootTime s)

theorem chapterVIDRootToOriginalContour_sourceToRootTime (s : I) :
    chapterVIDRootToOriginalContour
        (chapterVIUnitCirclePath (chapterVIDCircleSourceToRootTime s)) =
      chapterVIUnitCirclePath s := by
  rw [← chapterVIDRootMappedUnitCirclePath_apply,
    chapterVIDRootMappedUnitCirclePath_eq_reparam_apply,
    chapterVIDCircleTimeWarp_sourceToRootTime]

theorem continuous_chapterVIDInitialSourceCircleRadicand :
    Continuous chapterVIDInitialSourceCircleRadicand := by
  unfold chapterVIDInitialSourceCircleRadicand
  change Continuous
    ((fun st : I × I ↦ ChapterVIDGlobalLiftedPrefix.standardRadicand st.1 st.2) ∘
      fun s : I ↦ (0, chapterVIDCircleSourceToRootTime s))
  exact ChapterVIDGlobalLiftedPrefix.continuous_standardRadicand.comp
    (continuous_const.prodMk continuous_chapterVIDCircleSourceToRootTime)

theorem chapterVIDInitialSourceCircleRadicand_reparam (s : I) :
    chapterVIDInitialSourceCircleRadicand (chapterVIDCircleTimeWarp s) =
      ChapterVIDGlobalLiftedPrefix.standardRadicand 0 s := by
  simp [chapterVIDInitialSourceCircleRadicand]

/-- The principal sheet already certified on the initial root circle, transported exactly to
Poincare's historical source-circle parametrization. -/
def chapterVIDInitialSourceCirclePrincipalSheet :
    ChapterVIContinuousSquareRootSheet chapterVIDInitialSourceCircleRadicand where
  root s := ChapterVIDGlobalLiftedPrefix.standardPrincipalSheet.root
    (0, chapterVIDCircleSourceToRootTime s)
  continuous_root :=
    ChapterVIDGlobalLiftedPrefix.standardPrincipalSheet.continuous_root.comp
      (continuous_const.prodMk continuous_chapterVIDCircleSourceToRootTime)
  root_sq s := by
    exact ChapterVIDGlobalLiftedPrefix.standardPrincipalSheet.root_sq
      (0, chapterVIDCircleSourceToRootTime s)

/-- Pulling the transported source sheet back along the orientation-preserving warp recovers
the certified initial root-circle sheet pointwise, including its sign. -/
theorem chapterVIDInitialSourceCirclePrincipalSheet_reparam (s : I) :
    chapterVIDInitialSourceCirclePrincipalSheet.root
        (chapterVIDCircleTimeWarp s) =
      ChapterVIDGlobalLiftedPrefix.standardPrincipalSheet.root (0, s) := by
  simp [chapterVIDInitialSourceCirclePrincipalSheet]

end PoincareChapterVI
