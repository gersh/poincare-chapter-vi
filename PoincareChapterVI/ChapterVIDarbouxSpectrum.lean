/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Finite spectra of equally dominant Darboux singularities

When several singularities have the same modulus, consecutive coefficient ratios need not
converge.  The leading normalized coefficients instead form a finite exponential sum

`sₙ = ∑ⱼ Eⱼ λⱼⁿ`.

This file proves the finite-spectrum replacement for the single-singularity ratio argument:

* the polynomial `∏ⱼ (X - λⱼ)` annihilates `sₙ` by a linear recurrence;
* distinct bases are recovered from exact chapterVIFiniteExponentialMoment data by Vandermonde invertibility;
* if all bases lie on the unit circle, a finite exponential sum tending to zero has all weights
  zero;
* consequently two nondegenerate unit-circle spectra whose moments differ by `o(1)` have the same
  set of bases.

The last theorem is the algebraic/limit core needed to separate equally dominant singularities in
Poincaré's Darboux calculation.  Applying it to the actual contour coefficients still requires
the uniform asymptotic expansion and a common normalization radius.
-/

noncomputable section

open scoped BigOperators
open Polynomial
open Filter

namespace PoincareChapterVI

def chapterVIFiniteExponentialMoment {r : ℕ} (base weight : Fin r → ℂ) (n : ℕ) : ℂ :=
  ∑ j, weight j * base j ^ n

def chapterVIShiftApply (p : ℂ[X]) (sequence : ℕ → ℂ) (n : ℕ) : ℂ :=
  p.sum fun k coefficient ↦ coefficient * sequence (n + k)

theorem chapterVIShiftApply_finiteExponentialMoment {r : ℕ} (p : ℂ[X])
    (base weight : Fin r → ℂ) (n : ℕ) :
    chapterVIShiftApply p (chapterVIFiniteExponentialMoment base weight) n =
      ∑ j, weight j * base j ^ n * p.eval (base j) := by
  classical
  unfold chapterVIShiftApply chapterVIFiniteExponentialMoment
  rw [Polynomial.sum_def]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [pow_add]
  ring

def chapterVIExponentialAnnihilator {r : ℕ} (base : Fin r → ℂ) : ℂ[X] :=
  ∏ j, (Polynomial.X - Polynomial.C (base j))

theorem chapterVIExponentialAnnihilator_eval {r : ℕ} (base : Fin r → ℂ) (j : Fin r) :
    (chapterVIExponentialAnnihilator base).eval (base j) = 0 := by
  classical
  unfold chapterVIExponentialAnnihilator
  rw [Polynomial.eval_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ j)
  simp

theorem chapterVIExponentialAnnihilator_eval_eq_zero_iff {r : ℕ} (base : Fin r → ℂ) (z : ℂ) :
    (chapterVIExponentialAnnihilator base).eval z = 0 ↔ ∃ j, base j = z := by
  classical
  unfold chapterVIExponentialAnnihilator
  rw [Polynomial.eval_prod, Finset.prod_eq_zero_iff]
  simp only [Finset.mem_univ, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
    true_and]
  constructor
  · rintro ⟨j, hj⟩
    exact ⟨j, (sub_eq_zero.mp hj).symm⟩
  · rintro ⟨j, hj⟩
    exact ⟨j, sub_eq_zero.mpr hj.symm⟩

theorem chapterVIExponentialAnnihilator_recurrence {r : ℕ} (base weight : Fin r → ℂ) (n : ℕ) :
    chapterVIShiftApply (chapterVIExponentialAnnihilator base) (chapterVIFiniteExponentialMoment base weight) n = 0 := by
  rw [chapterVIShiftApply_finiteExponentialMoment]
  apply Finset.sum_eq_zero
  intro j hj
  rw [chapterVIExponentialAnnihilator_eval]
  ring

theorem weights_zero_of_finiteExponentialMoments {r : ℕ} {base weight : Fin r → ℂ}
    (hbase : Function.Injective base)
    (hmoments : ∀ n : Fin r, chapterVIFiniteExponentialMoment base weight n = 0) :
    weight = 0 := by
  apply Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hbase
  intro n
  simpa [chapterVIFiniteExponentialMoment] using hmoments n

theorem spectrum_mem_of_finiteExponentialMoment_eq
    {r s : ℕ} {firstBase : Fin r → ℂ} {firstWeight : Fin r → ℂ}
    {secondBase : Fin s → ℂ} {secondWeight : Fin s → ℂ}
    (hfirstBase : Function.Injective firstBase)
    (hfirstWeight : ∀ i, firstWeight i ≠ 0)
    (hmoment : chapterVIFiniteExponentialMoment firstBase firstWeight = chapterVIFiniteExponentialMoment secondBase secondWeight)
    (i : Fin r) : ∃ j, secondBase j = firstBase i := by
  let p := chapterVIExponentialAnnihilator secondBase
  have hrecurrence (n : ℕ) : chapterVIShiftApply p (chapterVIFiniteExponentialMoment firstBase firstWeight) n = 0 := by
    rw [hmoment]
    exact chapterVIExponentialAnnihilator_recurrence secondBase secondWeight n
  have hvanish : (fun j ↦ firstWeight j * p.eval (firstBase j)) = 0 := by
    apply Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hfirstBase
    intro n
    have h := hrecurrence n
    rw [chapterVIShiftApply_finiteExponentialMoment] at h
    simpa only [mul_assoc, mul_comm (firstBase _ ^ (n : ℕ)),
      mul_left_comm (firstBase _ ^ (n : ℕ))] using h
  have hi : firstWeight i * p.eval (firstBase i) = 0 := congrFun hvanish i
  have hp : p.eval (firstBase i) = 0 :=
    (mul_eq_zero.mp hi).resolve_left (hfirstWeight i)
  exact (chapterVIExponentialAnnihilator_eval_eq_zero_iff secondBase (firstBase i)).mp hp

theorem spectra_eq_of_finiteExponentialMoment_eq
    {r s : ℕ} {firstBase : Fin r → ℂ} {firstWeight : Fin r → ℂ}
    {secondBase : Fin s → ℂ} {secondWeight : Fin s → ℂ}
    (hfirstBase : Function.Injective firstBase)
    (hsecondBase : Function.Injective secondBase)
    (hfirstWeight : ∀ i, firstWeight i ≠ 0)
    (hsecondWeight : ∀ i, secondWeight i ≠ 0)
    (hmoment : chapterVIFiniteExponentialMoment firstBase firstWeight = chapterVIFiniteExponentialMoment secondBase secondWeight) :
    (Set.range firstBase : Set ℂ) = Set.range secondBase := by
  ext z
  constructor
  · rintro ⟨i, rfl⟩
    exact spectrum_mem_of_finiteExponentialMoment_eq hfirstBase hfirstWeight hmoment i
  · rintro ⟨j, rfl⟩
    exact spectrum_mem_of_finiteExponentialMoment_eq hsecondBase hsecondWeight hmoment.symm j

def chapterVIFiniteExponentialMomentCLM {r : ℕ} (base : Fin r → ℂ) :
    (Fin r → ℂ) →L[ℂ] (Fin r → ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun weight n ↦ chapterVIFiniteExponentialMoment base weight n
      map_add' := by
        intro left right
        funext n
        simp [chapterVIFiniteExponentialMoment, add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro scalar weight
        funext n
        simp [chapterVIFiniteExponentialMoment, mul_assoc, Finset.mul_sum] }

theorem chapterVIFiniteExponentialMomentCLM_injective {r : ℕ} {base : Fin r → ℂ}
    (hbase : Function.Injective base) : Function.Injective (chapterVIFiniteExponentialMomentCLM base) := by
  intro left right heq
  apply sub_eq_zero.mp
  apply weights_zero_of_finiteExponentialMoments hbase
  intro n
  have hn := congrFun heq n
  change chapterVIFiniteExponentialMoment base left n = chapterVIFiniteExponentialMoment base right n at hn
  simpa [chapterVIFiniteExponentialMoment, sub_mul, Finset.sum_sub_distrib] using sub_eq_zero.mpr hn

noncomputable def chapterVIFiniteExponentialMomentCLE {r : ℕ} (base : Fin r → ℂ)
    (hbase : Function.Injective base) :
    (Fin r → ℂ) ≃L[ℂ] (Fin r → ℂ) := by
  let map := chapterVIFiniteExponentialMomentCLM base
  have hinjective : Function.Injective map := chapterVIFiniteExponentialMomentCLM_injective hbase
  have hsurjective : Function.Surjective map :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp hinjective
  exact ContinuousLinearEquiv.ofBijective map
    (LinearMap.ker_eq_bot.mpr hinjective) (LinearMap.range_eq_top.mpr hsurjective)

theorem tendsto_weightedPowers_zero_of_finiteExponentialMoment_tendsto_zero
    {r : ℕ} {base weight : Fin r → ℂ}
    (hbase : Function.Injective base)
    (hmoment : Filter.Tendsto (chapterVIFiniteExponentialMoment base weight) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n : ℕ ↦ fun j ↦ weight j * base j ^ n)
      Filter.atTop (nhds 0) := by
  let shiftedWeight : ℕ → (Fin r → ℂ) :=
    fun n j ↦ weight j * base j ^ n
  have hshiftedMoments : Filter.Tendsto
      (fun n : ℕ ↦ fun k : Fin r ↦ chapterVIFiniteExponentialMoment base weight (n + k))
      Filter.atTop (nhds 0) := by
    rw [tendsto_pi_nhds]
    intro k
    simpa [Function.comp_def] using
      hmoment.comp (Filter.tendsto_add_atTop_nat (k : ℕ))
  have heq (n : ℕ) : chapterVIFiniteExponentialMomentCLM base (shiftedWeight n) =
      fun k : Fin r ↦ chapterVIFiniteExponentialMoment base weight (n + k) := by
    funext k
    simp [chapterVIFiniteExponentialMomentCLM, shiftedWeight, chapterVIFiniteExponentialMoment, pow_add, mul_assoc]
  have hforward : Filter.Tendsto (fun n ↦ chapterVIFiniteExponentialMomentCLM base (shiftedWeight n))
      Filter.atTop (nhds 0) := by
    simpa only [heq] using hshiftedMoments
  let equivalence := chapterVIFiniteExponentialMomentCLE base hbase
  have hinverse := equivalence.symm.continuous.continuousAt.tendsto.comp hforward
  have heventual :
      (fun n ↦ equivalence.symm (chapterVIFiniteExponentialMomentCLM base (shiftedWeight n))) =ᶠ[atTop]
        shiftedWeight := by
    filter_upwards with n
    exact equivalence.symm_apply_apply (shiftedWeight n)
  exact (tendsto_congr' heventual).mp (by simpa [Function.comp_def] using hinverse)

theorem weights_zero_of_finiteExponentialMoment_tendsto_zero_unitSpectrum
    {r : ℕ} {base weight : Fin r → ℂ}
    (hbase : Function.Injective base)
    (hunit : ∀ j, ‖base j‖ = 1)
    (hmoment : Filter.Tendsto (chapterVIFiniteExponentialMoment base weight) Filter.atTop (nhds 0)) :
    weight = 0 := by
  have hweighted := tendsto_weightedPowers_zero_of_finiteExponentialMoment_tendsto_zero hbase hmoment
  funext j
  have hj : Filter.Tendsto (fun n : ℕ ↦ weight j * base j ^ n)
      Filter.atTop (nhds 0) := by
    exact (tendsto_pi_nhds.mp hweighted) j
  have hnorm := hj.norm
  have hconstant : (fun n : ℕ ↦ ‖weight j * base j ^ n‖) =
      fun _ ↦ ‖weight j‖ := by
    funext n
    simp [norm_pow, hunit]
  rw [hconstant] at hnorm
  simp only [norm_zero] at hnorm
  have hconst : Tendsto (fun _ : ℕ ↦ ‖weight j‖) atTop (nhds ‖weight j‖) :=
    tendsto_const_nhds
  have : ‖weight j‖ = 0 := tendsto_nhds_unique hconst hnorm
  exact norm_eq_zero.mp this

theorem tendsto_chapterVIShiftApply_zero (p : ℂ[X]) {sequence : ℕ → ℂ}
    (hsequence : Tendsto sequence atTop (nhds 0)) :
    Tendsto (fun n ↦ chapterVIShiftApply p sequence n) atTop (nhds 0) := by
  classical
  unfold chapterVIShiftApply Polynomial.sum
  simpa using tendsto_finsetSum p.support (fun k hk ↦
    tendsto_const_nhds.mul
      (hsequence.comp (Filter.tendsto_add_atTop_nat k)))

theorem chapterVIShiftApply_sub (p : ℂ[X]) (first second : ℕ → ℂ) (n : ℕ) :
    chapterVIShiftApply p (first - second) n =
      chapterVIShiftApply p first n - chapterVIShiftApply p second n := by
  classical
  simp [chapterVIShiftApply, Polynomial.sum_def, mul_sub, Finset.sum_sub_distrib]

theorem spectrum_mem_of_finiteExponentialMoment_sub_tendsto_zero
    {r s : ℕ} {firstBase : Fin r → ℂ} {firstWeight : Fin r → ℂ}
    {secondBase : Fin s → ℂ} {secondWeight : Fin s → ℂ}
    (hfirstBase : Function.Injective firstBase)
    (hfirstUnit : ∀ i, ‖firstBase i‖ = 1)
    (hfirstWeight : ∀ i, firstWeight i ≠ 0)
    (hdifference : Tendsto
      (chapterVIFiniteExponentialMoment firstBase firstWeight - chapterVIFiniteExponentialMoment secondBase secondWeight)
      atTop (nhds 0)) (i : Fin r) :
    ∃ j, secondBase j = firstBase i := by
  let p := chapterVIExponentialAnnihilator secondBase
  have hshiftDifference := tendsto_chapterVIShiftApply_zero p hdifference
  have hshiftFirst : Tendsto
      (fun n ↦ chapterVIShiftApply p (chapterVIFiniteExponentialMoment firstBase firstWeight) n) atTop (nhds 0) := by
    convert hshiftDifference using 1
    funext n
    rw [chapterVIShiftApply_sub, chapterVIExponentialAnnihilator_recurrence]
    simp
  let modifiedWeight : Fin r → ℂ :=
    fun j ↦ firstWeight j * p.eval (firstBase j)
  have hmodifiedMoment : (fun n ↦ chapterVIShiftApply p (chapterVIFiniteExponentialMoment firstBase firstWeight) n) =
      chapterVIFiniteExponentialMoment firstBase modifiedWeight := by
    funext n
    rw [chapterVIShiftApply_finiteExponentialMoment]
    simp only [chapterVIFiniteExponentialMoment, modifiedWeight]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hmodifiedMoment] at hshiftFirst
  have hmodifiedZero :=
    weights_zero_of_finiteExponentialMoment_tendsto_zero_unitSpectrum hfirstBase hfirstUnit hshiftFirst
  have hi : firstWeight i * p.eval (firstBase i) = 0 := congrFun hmodifiedZero i
  have hp : p.eval (firstBase i) = 0 :=
    (mul_eq_zero.mp hi).resolve_left (hfirstWeight i)
  exact (chapterVIExponentialAnnihilator_eval_eq_zero_iff secondBase (firstBase i)).mp hp

theorem spectra_eq_of_finiteExponentialMoment_sub_tendsto_zero_unitSpectra
    {r s : ℕ} {firstBase : Fin r → ℂ} {firstWeight : Fin r → ℂ}
    {secondBase : Fin s → ℂ} {secondWeight : Fin s → ℂ}
    (hfirstBase : Function.Injective firstBase)
    (hsecondBase : Function.Injective secondBase)
    (hfirstUnit : ∀ i, ‖firstBase i‖ = 1)
    (hsecondUnit : ∀ i, ‖secondBase i‖ = 1)
    (hfirstWeight : ∀ i, firstWeight i ≠ 0)
    (hsecondWeight : ∀ i, secondWeight i ≠ 0)
    (hdifference : Tendsto
      (chapterVIFiniteExponentialMoment firstBase firstWeight - chapterVIFiniteExponentialMoment secondBase secondWeight)
      atTop (nhds 0)) :
    (Set.range firstBase : Set ℂ) = Set.range secondBase := by
  ext z
  constructor
  · rintro ⟨i, rfl⟩
    exact spectrum_mem_of_finiteExponentialMoment_sub_tendsto_zero hfirstBase hfirstUnit hfirstWeight
      hdifference i
  · rintro ⟨j, rfl⟩
    have hreverse : Tendsto
        (chapterVIFiniteExponentialMoment secondBase secondWeight - chapterVIFiniteExponentialMoment firstBase firstWeight)
        atTop (nhds 0) := by
      convert hdifference.neg using 1
      · funext n
        simp
      · simp
    apply spectrum_mem_of_finiteExponentialMoment_sub_tendsto_zero hsecondBase hsecondUnit hsecondWeight
      (secondBase := firstBase) (secondWeight := firstWeight)
    exact hreverse

/-- Two nondegenerate unit-circle spectra approximating the same normalized coefficient sequence
up to a term tending to zero have the same set of exponential bases.  This is the finite-spectrum
replacement for consecutive-ratio recovery when equally dominant singularities coexist. -/
theorem spectra_eq_of_commonCoefficient_tendsto_finiteExponentialMoments
    {r s : ℕ} {coefficient : ℕ → ℂ}
    {firstBase : Fin r → ℂ} {firstWeight : Fin r → ℂ}
    {secondBase : Fin s → ℂ} {secondWeight : Fin s → ℂ}
    (hfirstBase : Function.Injective firstBase)
    (hsecondBase : Function.Injective secondBase)
    (hfirstUnit : ∀ i, ‖firstBase i‖ = 1)
    (hsecondUnit : ∀ i, ‖secondBase i‖ = 1)
    (hfirstWeight : ∀ i, firstWeight i ≠ 0)
    (hsecondWeight : ∀ i, secondWeight i ≠ 0)
    (hfirst : Tendsto
      (coefficient - chapterVIFiniteExponentialMoment firstBase firstWeight)
      atTop (nhds 0))
    (hsecond : Tendsto
      (coefficient - chapterVIFiniteExponentialMoment secondBase secondWeight)
      atTop (nhds 0)) :
    (Set.range firstBase : Set ℂ) = Set.range secondBase := by
  apply spectra_eq_of_finiteExponentialMoment_sub_tendsto_zero_unitSpectra
    hfirstBase hsecondBase hfirstUnit hsecondUnit hfirstWeight hsecondWeight
  have hdifference := hfirst.neg.add hsecond
  convert hdifference using 1
  · funext n
    simp
  · simp

/-- A continuous labeling of a finite injective spectrum cannot permute locally.  If a branch
tends to one labeled base and is eventually contained in the unchanged finite spectrum, then it
is eventually equal to that same base. -/
theorem eventually_eq_of_tendsto_of_eventually_mem_finiteSpectrum
    {α : Type*} {l : Filter α} {r : ℕ} {base : Fin r → ℂ}
    (hbase : Function.Injective base) {branch : α → ℂ} (i : Fin r)
    (hbranch : Tendsto branch l (nhds (base i)))
    (hmem : ∀ᶠ parameter in l, branch parameter ∈ Set.range base) :
    branch =ᶠ[l] fun _ ↦ base i := by
  have havoid : ∀ᶠ parameter in l, ∀ j : Fin r, j ≠ i → branch parameter ≠ base j := by
    rw [Filter.eventually_all]
    intro j
    by_cases hji : j = i
    · exact Eventually.of_forall fun _ hj ↦ (hj hji).elim
    · filter_upwards [hbranch.eventually_ne (hbase.ne (Ne.symm hji))] with parameter hne
      intro _
      exact hne
  filter_upwards [hmem, havoid] with parameter hparameter hparameterAvoids
  obtain ⟨j, hj⟩ := hparameter
  have hji : j = i := by
    by_contra hne
    exact hparameterAvoids j hne hj.symm
  subst j
  exact hj.symm

end PoincareChapterVI
