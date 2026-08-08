/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import PoincareChapterVI.ChapterVIJointPreparation

/-!
# Parametric holomorphic Morse coordinate at Poincaré's pinch

The jointly divided centered germ satisfies

`ψ(z,h(z)+u) - ψ(z,h(z)) = u² U(z,u)`

with `U(D,0) ≠ 0`.  Choosing the already-constructed holomorphic square root `S²=U` suggests the
fiber coordinate `v=uS(z,u)`.  Its derivative at `(D,0)` is invertible.  A local inverse therefore
turns the *unsubtracted* translated source radicand into the exact parametric Morse normal form

`ψ(z,h(z)+u(z,v)) = ψ(z,h(z)) + v²`.

This is the convergent analytic replacement for the formal Weierstrass-preparation gap.  It keeps
Poincaré's quadratic pinch route but records the necessary local change of integration coordinate.
-/

noncomputable section

open Filter Set
open scoped Topology

namespace PoincareChapterVI

/-- Analyticity at the pinch of the selected square root of the joint Hadamard quotient. -/
theorem analyticAt_chapterVIDCenteredPreparedUnitRoot :
    AnalyticAt ℂ
      chapterVIDCenteredConvergentPreparedGerm.unitRootGerm.root
      (chapterVIDZBase, (0 : ℂ)) := by
  unfold ChapterVIConvergentPreparedGerm.unitRootGerm
  exact ChapterVIHolomorphicSquareRootGerm.analyticAt_root_of_analyticAt
    chapterVIDCenteredConvergentPreparedGerm.unitHasFPowerSeries.analyticAt
    chapterVIDCenteredConvergentPreparedGerm.unit_base_ne_zero

/-- The nonzero fiber derivative of the Morse coordinate. -/
def chapterVIDMorseRootBase : ℂ :=
  chapterVIDCenteredConvergentPreparedGerm.unitRootGerm.root
    (chapterVIDZBase, (0 : ℂ))

theorem chapterVIDMorseRootBase_ne_zero : chapterVIDMorseRootBase ≠ 0 := by
  exact chapterVIDCenteredConvergentPreparedGerm.unitRootGerm.root_ne_zero _
    chapterVIDCenteredConvergentPreparedGerm.unitRootGerm.base_mem

/-- The forward parametric Morse coordinate `(z,u) ↦ (z,uS(z,u))`. -/
def chapterVIDMorseMap (point : ℂ × ℂ) : ℂ × ℂ :=
  (point.1, point.2 *
    chapterVIDCenteredConvergentPreparedGerm.unitRootGerm.root point)

@[simp]
theorem chapterVIDMorseMap_base :
    chapterVIDMorseMap (chapterVIDZBase, (0 : ℂ)) =
      (chapterVIDZBase, (0 : ℂ)) := by
  simp [chapterVIDMorseMap]

/-- The derivative of the Morse map at the pinch, as a continuous linear equivalence. -/
def chapterVIDMorseLinearEquiv :
    (ℂ × ℂ) ≃L[ℂ] (ℂ × ℂ) :=
  (ContinuousLinearEquiv.refl ℂ ℂ).prodCongr
    (ContinuousLinearEquiv.unitsEquivAut ℂ
      (Units.mk0 chapterVIDMorseRootBase chapterVIDMorseRootBase_ne_zero))

@[simp]
theorem chapterVIDMorseLinearEquiv_apply (direction : ℂ × ℂ) :
    chapterVIDMorseLinearEquiv direction =
      (direction.1, direction.2 * chapterVIDMorseRootBase) := by
  simp [chapterVIDMorseLinearEquiv, ContinuousLinearEquiv.unitsEquivAut_apply]

set_option backward.isDefEq.respectTransparency.types false in
/-- The forward Morse coordinate has the asserted invertible derivative at the pinch. -/
theorem hasFDerivAt_chapterVIDMorseMap :
    HasFDerivAt chapterVIDMorseMap
      (chapterVIDMorseLinearEquiv : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ))
      (chapterVIDZBase, (0 : ℂ)) := by
  have hroot :=
    analyticAt_chapterVIDCenteredPreparedUnitRoot.hasStrictFDerivAt.hasFDerivAt
  have hproduct :=
    (hasFDerivAt_snd (𝕜 := ℂ) (p := (chapterVIDZBase, (0 : ℂ)))).mul hroot
  have hderivative :
      (ContinuousLinearMap.fst ℂ ℂ ℂ).prod
        (((chapterVIDZBase, (0 : ℂ)).2 •
            fderiv ℂ chapterVIDCenteredConvergentPreparedGerm.unitRootGerm.root
              (chapterVIDZBase, (0 : ℂ))) +
          chapterVIDCenteredConvergentPreparedGerm.unitRootGerm.root
              (chapterVIDZBase, (0 : ℂ)) • ContinuousLinearMap.snd ℂ ℂ ℂ) =
        (chapterVIDMorseLinearEquiv : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) := by
    apply ContinuousLinearMap.ext
    intro direction
    apply Prod.ext <;>
      simp [chapterVIDMorseLinearEquiv_apply, chapterVIDMorseRootBase, mul_comm]
  change HasFDerivAt
    (fun point : ℂ × ℂ ↦
      (point.1, point.2 *
        chapterVIDCenteredConvergentPreparedGerm.unitRootGerm.root point))
    (chapterVIDMorseLinearEquiv : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ))
    (chapterVIDZBase, (0 : ℂ))
  rw [← hderivative]
  exact (hasFDerivAt_fst (𝕜 := ℂ)
    (p := (chapterVIDZBase, (0 : ℂ)))).prodMk hproduct

/-- The Morse coordinate is analytic at the pinch. -/
theorem analyticAt_chapterVIDMorseMap :
    AnalyticAt ℂ chapterVIDMorseMap (chapterVIDZBase, (0 : ℂ)) := by
  exact analyticAt_fst.prod
    (analyticAt_snd.mul analyticAt_chapterVIDCenteredPreparedUnitRoot)

set_option backward.isDefEq.respectTransparency.types false in
/-- Analyticity upgrades the invertible derivative to the strict derivative required by the
inverse function theorem. -/
theorem hasStrictFDerivAt_chapterVIDMorseMap :
    HasStrictFDerivAt chapterVIDMorseMap
      (chapterVIDMorseLinearEquiv : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ))
      (chapterVIDZBase, (0 : ℂ)) := by
  have hstrict := analyticAt_chapterVIDMorseMap.hasStrictFDerivAt
  have hfderiv := hasFDerivAt_chapterVIDMorseMap.fderiv
  exact hstrict.congr_fderiv hfderiv

/-- The local inverse `(z,v) ↦ (z,u)` supplied by the complex inverse function theorem. -/
def chapterVIDMorseInverse : ℂ × ℂ → ℂ × ℂ :=
  hasStrictFDerivAt_chapterVIDMorseMap.localInverse chapterVIDMorseMap
    chapterVIDMorseLinearEquiv (chapterVIDZBase, (0 : ℂ))

@[simp]
theorem chapterVIDMorseInverse_base :
    chapterVIDMorseInverse (chapterVIDZBase, (0 : ℂ)) =
      (chapterVIDZBase, (0 : ℂ)) := by
  unfold chapterVIDMorseInverse
  have hbase := hasStrictFDerivAt_chapterVIDMorseMap.localInverse_apply_image
  rw [chapterVIDMorseMap_base] at hbase
  exact hbase

theorem eventually_chapterVIDMorseInverse_left :
    ∀ᶠ point in 𝓝 (chapterVIDZBase, (0 : ℂ)),
      chapterVIDMorseInverse (chapterVIDMorseMap point) = point :=
  hasStrictFDerivAt_chapterVIDMorseMap.eventually_left_inverse

theorem eventually_chapterVIDMorseInverse_right :
    ∀ᶠ point in 𝓝 (chapterVIDZBase, (0 : ℂ)),
      chapterVIDMorseMap (chapterVIDMorseInverse point) = point := by
  simpa only [chapterVIDMorseInverse, chapterVIDMorseMap_base] using
    hasStrictFDerivAt_chapterVIDMorseMap.eventually_right_inverse

theorem tendsto_chapterVIDMorseInverse :
    Tendsto chapterVIDMorseInverse
      (𝓝 (chapterVIDZBase, (0 : ℂ)))
      (𝓝 (chapterVIDZBase, (0 : ℂ))) := by
  simpa only [chapterVIDMorseInverse, chapterVIDMorseMap_base] using
    hasStrictFDerivAt_chapterVIDMorseMap.localInverse_tendsto

/-- The local inverse is analytic; this is needed to transport the contour differential, not
only its point set. -/
theorem analyticAt_chapterVIDMorseInverse :
    AnalyticAt ℂ chapterVIDMorseInverse (chapterVIDZBase, (0 : ℂ)) := by
  let localHomeomorph :=
    hasStrictFDerivAt_chapterVIDMorseMap.toOpenPartialHomeomorph chapterVIDMorseMap
  have hbase : (chapterVIDZBase, (0 : ℂ)) ∈ localHomeomorph.source :=
    hasStrictFDerivAt_chapterVIDMorseMap.mem_toOpenPartialHomeomorph_source
  obtain ⟨series, hseriesMap⟩ := analyticAt_chapterVIDMorseMap
  have hseriesLocal : HasFPowerSeriesAt
      (localHomeomorph : ℂ × ℂ → ℂ × ℂ) series
      (chapterVIDZBase, (0 : ℂ)) := by
    apply hseriesMap.congr
    filter_upwards [localHomeomorph.open_source.mem_nhds hbase] with point hpoint
    simp [localHomeomorph]
  have hlinear : series 1 =
      (continuousMultilinearCurryFin1 ℂ (ℂ × ℂ) (ℂ × ℂ)).symm
        chapterVIDMorseLinearEquiv := by
    apply (continuousMultilinearCurryFin1 ℂ (ℂ × ℂ) (ℂ × ℂ)).injective
    exact hseriesMap.fderiv_eq.symm.trans hasFDerivAt_chapterVIDMorseMap.fderiv
  have hseries := localHomeomorph.hasFPowerSeriesAt_symm hbase hseriesLocal hlinear
  have hanalytic := hseries.analyticAt
  have hlocalBase : localHomeomorph (chapterVIDZBase, (0 : ℂ)) =
      (chapterVIDZBase, (0 : ℂ)) := by
    change chapterVIDMorseMap (chapterVIDZBase, (0 : ℂ)) = _
    exact chapterVIDMorseMap_base
  rw [hlocalBase] at hanalytic
  simpa only [chapterVIDMorseInverse, localHomeomorph,
    HasStrictFDerivAt.localInverse_def] using hanalytic

/-- The original source radicand after translating only by the analytic critical center, without
subtracting its varying critical value. -/
def chapterVIDTranslatedRadicand (point : ℂ × ℂ) : ℂ :=
  chapterVIDRadicand
    (point.1, chapterVIDCriticalCenter point.1 + point.2)

theorem chapterVIDTranslatedRadicand_eq_critical_add_centered
    (point : ℂ × ℂ) :
    chapterVIDTranslatedRadicand point =
      chapterVIDCriticalValue point.1 + chapterVIDCenteredRadicand point := by
  simp [chapterVIDTranslatedRadicand, chapterVIDCenteredRadicand,
    chapterVIDCriticalValue]

/-- In the forward Morse coordinate, the unsubtracted translated radicand is exactly its varying
critical value plus a square. -/
theorem eventually_chapterVIDTranslatedRadicand_eq_critical_add_morse_sq :
    ∀ᶠ point in 𝓝 (chapterVIDZBase, (0 : ℂ)),
      chapterVIDTranslatedRadicand point =
        chapterVIDCriticalValue point.1 + (chapterVIDMorseMap point).2 ^ 2 := by
  have hfactor := chapterVIDCenteredConvergentPreparedGerm.eventually_factorization
  have hrootDomain : chapterVIDCenteredConvergentPreparedGerm.unitRootGerm.domain ∈
      𝓝 (chapterVIDZBase, (0 : ℂ)) :=
    chapterVIDCenteredConvergentPreparedGerm.unitRootGerm.isOpen_domain.mem_nhds
      chapterVIDCenteredConvergentPreparedGerm.unitRootGerm.base_mem
  filter_upwards [hfactor, hrootDomain] with point hfactorPoint hdomain
  rw [chapterVIDTranslatedRadicand_eq_critical_add_centered, hfactorPoint]
  rw [chapterVIDCenteredConvergentPreparedGerm_center,
    chapterVIDCenteredConvergentPreparedGerm_kappa]
  simp only [Pi.zero_apply, sub_zero, add_zero]
  rw [← chapterVIDCenteredConvergentPreparedGerm.unitRootGerm.root_sq point hdomain]
  simp [chapterVIDMorseMap]
  ring

/-- Pulling the preceding identity through the analytic local inverse gives the exact
parameter-dependent holomorphic Morse normal form for Poincaré's original radicand. -/
theorem eventually_chapterVIDTranslatedRadicand_comp_morseInverse_eq :
    ∀ᶠ point in 𝓝 (chapterVIDZBase, (0 : ℂ)),
      chapterVIDTranslatedRadicand (chapterVIDMorseInverse point) =
        chapterVIDCriticalValue point.1 + point.2 ^ 2 := by
  have hnormal := tendsto_chapterVIDMorseInverse.eventually
    eventually_chapterVIDTranslatedRadicand_eq_critical_add_morse_sq
  filter_upwards [hnormal, eventually_chapterVIDMorseInverse_right]
    with point hnormalPoint hinverse
  have hfirst := congrArg Prod.fst hinverse
  simp only [chapterVIDMorseMap] at hfirst
  rw [hnormalPoint, hfirst, hinverse]

end PoincareChapterVI
