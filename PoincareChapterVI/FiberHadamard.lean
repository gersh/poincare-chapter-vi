/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Operator.Prod

/-!
# Analytic Hadamard division in a fiber coordinate

This file develops the power-series operation needed to divide an analytic function on
`ℂ × ℂ` by the second coordinate when it vanishes on the first-coordinate axis.

For a homogeneous multilinear term `p (n+1)`, the quotient coefficient is the telescoping sum
obtained by changing its arguments one at a time from `(z,u)` to `(z,0)`.  The fundamental
coefficient identity is proved below.  Convergence and reconstruction of the analytic quotient
are developed separately from this finite multilinear algebra.
-/

noncomputable section

open scoped BigOperators Topology

namespace PoincareChapterVI

/-- Projection of a parameter-fiber pair onto the parameter axis. -/
def chapterVIFiberHorizontal : ℂ × ℂ →L[ℂ] ℂ × ℂ :=
  (ContinuousLinearMap.fst ℂ ℂ ℂ).prod 0

@[simp]
theorem chapterVIFiberHorizontal_apply (point : ℂ × ℂ) :
    chapterVIFiberHorizontal point = (point.1, 0) :=
  rfl

/-- The unit vector in the fiber direction. -/
def chapterVIFiberVerticalOne : ℂ × ℂ := (0, 1)

/-- One summand in the homogeneous Hadamard quotient. Arguments before the distinguished slot
remain unchanged, the distinguished slot is the unit fiber vector, and later arguments are
projected to the parameter axis. -/
def chapterVIFiberHadamardTerm
    (p : FormalMultilinearSeries ℂ (ℂ × ℂ) ℂ)
    (n : ℕ) (i : Fin (n + 1)) : (ℂ × ℂ) [×n]→L[ℂ] ℂ :=
  ((p (n + 1)).curryMid i chapterVIFiberVerticalOne).compContinuousLinearMap
    (fun j ↦ if i.succAbove j < i then ContinuousLinearMap.id ℂ (ℂ × ℂ)
      else chapterVIFiberHorizontal)

/-- The formal multilinear series obtained by one Hadamard division in the fiber coordinate. -/
def chapterVIFiberHadamardSeries
    (p : FormalMultilinearSeries ℂ (ℂ × ℂ) ℂ) :
    FormalMultilinearSeries ℂ (ℂ × ℂ) ℂ :=
  fun n ↦ ∑ i : Fin (n + 1), chapterVIFiberHadamardTerm p n i

@[simp]
theorem chapterVIFiberVerticalOne_smul (point : ℂ × ℂ) :
    point.2 • chapterVIFiberVerticalOne = point - chapterVIFiberHorizontal point := by
  ext <;> simp [chapterVIFiberVerticalOne, chapterVIFiberHorizontal]

@[simp]
theorem chapterVIFiberHadamardTerm_apply_diagonal
    (p : FormalMultilinearSeries ℂ (ℂ × ℂ) ℂ)
    (n : ℕ) (i : Fin (n + 1)) (point : ℂ × ℂ) :
    chapterVIFiberHadamardTerm p n i (fun _ ↦ point) =
      p (n + 1) (i.insertNth chapterVIFiberVerticalOne
        (fun j ↦ if i.succAbove j < i then point else chapterVIFiberHorizontal point)) := by
  simp only [chapterVIFiberHadamardTerm,
    ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.curryMid_apply]
  congr 2
  funext j
  split <;> simp_all

/-- The coefficient-level Hadamard identity: multiplying the quotient coefficient by the fiber
coordinate recovers the difference between the original homogeneous term and its restriction to
the parameter axis. -/
theorem chapterVIFiber_smul_hadamardSeries_apply_diagonal
    (p : FormalMultilinearSeries ℂ (ℂ × ℂ) ℂ)
    (n : ℕ) (point : ℂ × ℂ) :
    point.2 * (chapterVIFiberHadamardSeries p n (fun _ ↦ point) : ℂ) =
      (p (n + 1) (fun _ ↦ point) : ℂ) -
        (p (n + 1) (fun _ ↦ chapterVIFiberHorizontal point) : ℂ) := by
  rw [chapterVIFiberHadamardSeries]
  rw [show
    ((∑ i : Fin (n + 1), chapterVIFiberHadamardTerm p n i)
        (fun _ ↦ point) : ℂ) =
      ∑ i : Fin (n + 1), chapterVIFiberHadamardTerm p n i (fun _ ↦ point) by
        simp]
  rw [Finset.mul_sum]
  have htel := (p (n + 1)).toMultilinearMap.map_sub_map_piecewise
    (fun _ ↦ point) (fun _ ↦ chapterVIFiberHorizontal point) Finset.univ
  rw [Finset.piecewise_univ] at htel
  change
    p (n + 1) (fun _ ↦ point) -
      p (n + 1) (fun _ ↦ chapterVIFiberHorizontal point) = _ at htel
  rw [htel]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Finset.mem_univ, true_implies,
    chapterVIFiberHadamardTerm_apply_diagonal]
  change _ = p (n + 1) (fun j ↦
    if j < i then point
    else if i = j then point - chapterVIFiberHorizontal point
    else chapterVIFiberHorizontal point)
  rw [← smul_eq_mul]
  change
    ((point.2 • ((p (n + 1)).curryMid i chapterVIFiberVerticalOne) :
        (ℂ × ℂ) [×n]→L[ℂ] ℂ)
      (fun j ↦ if i.succAbove j < i then point else chapterVIFiberHorizontal point)) = _
  have hsmul :
      point.2 • ((p (n + 1)).curryMid i chapterVIFiberVerticalOne) =
        (p (n + 1)).curryMid i (point.2 • chapterVIFiberVerticalOne) :=
    (ContinuousLinearMap.map_smul ((p (n + 1)).curryMid i)
      point.2 chapterVIFiberVerticalOne).symm
  rw [hsmul]
  simp only [ContinuousMultilinearMap.curryMid_apply]
  congr 1
  funext j
  rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨k, rfl⟩
  · simp
  · simp

/-- Each telescoping summand has operator norm no larger than its source homogeneous term. -/
theorem norm_chapterVIFiberHadamardTerm_le
    (p : FormalMultilinearSeries ℂ (ℂ × ℂ) ℂ)
    (n : ℕ) (i : Fin (n + 1)) :
    ‖chapterVIFiberHadamardTerm p n i‖ ≤ ‖p (n + 1)‖ := by
  unfold chapterVIFiberHadamardTerm
  have hcenter :
      ‖(p (n + 1)).curryMid i chapterVIFiberVerticalOne‖ ≤ ‖p (n + 1)‖ := by
    calc
      ‖(p (n + 1)).curryMid i chapterVIFiberVerticalOne‖ ≤
          ‖(p (n + 1)).curryMid i‖ * ‖chapterVIFiberVerticalOne‖ :=
        ((p (n + 1)).curryMid i).le_opNorm chapterVIFiberVerticalOne
      _ = ‖p (n + 1)‖ := by
        simp [chapterVIFiberVerticalOne]
  have hmaps (j : Fin n) :
      ‖if i.succAbove j < i then ContinuousLinearMap.id ℂ (ℂ × ℂ)
        else chapterVIFiberHorizontal‖ ≤ 1 := by
    split
    · simp
    · simp [chapterVIFiberHorizontal]
  have hprod :
      ∏ j : Fin n,
        ‖if i.succAbove j < i then ContinuousLinearMap.id ℂ (ℂ × ℂ)
          else chapterVIFiberHorizontal‖ ≤ 1 := by
    apply Finset.prod_le_one
    · intro j hj
      positivity
    · intro j hj
      exact hmaps j
  calc
    ‖((p (n + 1)).curryMid i chapterVIFiberVerticalOne).compContinuousLinearMap
        (fun j ↦ if i.succAbove j < i then ContinuousLinearMap.id ℂ (ℂ × ℂ)
          else chapterVIFiberHorizontal)‖ ≤
        ‖(p (n + 1)).curryMid i chapterVIFiberVerticalOne‖ *
          ∏ j : Fin n,
            ‖if i.succAbove j < i then ContinuousLinearMap.id ℂ (ℂ × ℂ)
              else chapterVIFiberHorizontal‖ :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ ‖p (n + 1)‖ * 1 := mul_le_mul hcenter hprod (by positivity) (norm_nonneg _)
    _ = ‖p (n + 1)‖ := mul_one _

/-- The quotient coefficient grows by at most the linear factor `n+1`. -/
theorem norm_chapterVIFiberHadamardSeries_le
    (p : FormalMultilinearSeries ℂ (ℂ × ℂ) ℂ) (n : ℕ) :
    ‖chapterVIFiberHadamardSeries p n‖ ≤ (n + 1) * ‖p (n + 1)‖ := by
  calc
    ‖chapterVIFiberHadamardSeries p n‖ ≤
        ∑ i : Fin (n + 1), ‖chapterVIFiberHadamardTerm p n i‖ := by
      exact norm_sum_le _ _
    _ ≤ ∑ _i : Fin (n + 1), ‖p (n + 1)‖ := by
      exact Finset.sum_le_sum fun i _ ↦ norm_chapterVIFiberHadamardTerm_le p n i
    _ = (n + 1) * ‖p (n + 1)‖ := by simp

/-- One Hadamard division preserves a positive radius of convergence.  The proof only loses an
irrelevant constant factor in the radius and uses the linear coefficient bound above. -/
theorem chapterVIFiberHadamardSeries_radius_pos
    (p : FormalMultilinearSeries ℂ (ℂ × ℂ) ℂ)
    (hp : 0 < p.radius) :
    0 < (chapterVIFiberHadamardSeries p).radius := by
  obtain ⟨C, growth, hC, hgrowth, hpbound⟩ := p.le_mul_pow_of_radius_pos hp
  let quotientRadius : NNReal := ⟨(2 * growth)⁻¹, by positivity⟩
  have hquotientRadius : 0 < quotientRadius := by
    change 0 < (2 * growth)⁻¹
    positivity
  have hmajorant : Summable (fun n : ℕ ↦
      (C * growth) * ((n + 1 : ℝ) * (1 / 2 : ℝ) ^ n)) := by
    have hgeom := summable_descFactorial_mul_geometric_of_norm_lt_one
      (R := ℝ) 1 (r := (1 / 2 : ℝ)) (by norm_num)
    simpa [Nat.descFactorial_one] using hgeom.mul_left (C * growth)
  have hsummable : Summable (fun n : ℕ ↦
      ‖chapterVIFiberHadamardSeries p n‖ * (quotientRadius : ℝ) ^ n) := by
    apply Summable.of_nonneg_of_le (fun n ↦ by positivity) ?_ hmajorant
    intro n
    calc
      ‖chapterVIFiberHadamardSeries p n‖ * (quotientRadius : ℝ) ^ n ≤
          ((n + 1 : ℝ) * ‖p (n + 1)‖) * (quotientRadius : ℝ) ^ n := by
        gcongr
        exact norm_chapterVIFiberHadamardSeries_le p n
      _ ≤ ((n + 1 : ℝ) * (C * growth ^ (n + 1))) *
          (quotientRadius : ℝ) ^ n := by
        gcongr
        exact hpbound (n + 1)
      _ = (C * growth) * ((n + 1 : ℝ) * (1 / 2 : ℝ) ^ n) := by
        simp only [quotientRadius]
        change ((n + 1 : ℝ) * (C * growth ^ (n + 1))) *
          ((2 * growth)⁻¹ : ℝ) ^ n =
            (C * growth) * ((n + 1 : ℝ) * (1 / 2 : ℝ) ^ n)
        rw [pow_succ]
        rw [inv_pow]
        field_simp [hgrowth.ne']
        rw [← mul_pow]
        congr 1
        ring
  have hradius : (quotientRadius : ENNReal) ≤
      (chapterVIFiberHadamardSeries p).radius :=
    FormalMultilinearSeries.le_radius_of_summable_norm _ hsummable
  exact (ENNReal.coe_pos.mpr hquotientRadius).trans_le hradius

/-- Summing the coefficient identity reconstructs the difference between a power series and its
restriction to the parameter axis.  This lemma isolates the only reindexing needed in analytic
Hadamard division. -/
theorem chapterVIFiberHadamard_hasSum_identity
    (p : FormalMultilinearSeries ℂ (ℂ × ℂ) ℂ) (point : ℂ × ℂ)
    {source horizontalSource quotient : ℂ}
    (hsource : HasSum (fun n : ℕ ↦ p n (fun _ ↦ point)) source)
    (hhorizontal : HasSum
      (fun n : ℕ ↦ p n (fun _ ↦ chapterVIFiberHorizontal point)) horizontalSource)
    (hquotient : HasSum
      (fun n : ℕ ↦ chapterVIFiberHadamardSeries p n (fun _ ↦ point)) quotient) :
    point.2 * quotient = source - horizontalSource := by
  have hdifference : HasSum
      (fun n : ℕ ↦ p n (fun _ ↦ point) -
        p n (fun _ ↦ chapterVIFiberHorizontal point))
      (source - horizontalSource) :=
    hsource.sub hhorizontal
  have htail : HasSum
      (fun n : ℕ ↦ p (n + 1) (fun _ ↦ point) -
        p (n + 1) (fun _ ↦ chapterVIFiberHorizontal point))
      (source - horizontalSource) := by
    have hzero : p 0 (fun _ ↦ point) -
        p 0 (fun _ ↦ chapterVIFiberHorizontal point) = 0 := by
      have heval : p 0 (fun _ ↦ point) =
          p 0 (fun _ ↦ chapterVIFiberHorizontal point) :=
        congrArg (fun v ↦ p 0 v) (Subsingleton.elim _ _)
      rw [heval, sub_self]
    have hshift := (hasSum_nat_add_iff' 1).mpr hdifference
    rw [Finset.sum_range_one, hzero, sub_zero] at hshift
    exact hshift
  have hscaled : HasSum
      (fun n : ℕ ↦ point.2 *
        chapterVIFiberHadamardSeries p n (fun _ ↦ point))
      (point.2 * quotient) :=
    hquotient.mul_left point.2
  exact hscaled.unique <| htail.congr_fun fun n ↦
    chapterVIFiber_smul_hadamardSeries_apply_diagonal p n point

/-- Analytic Hadamard division in the second coordinate.  If an analytic function vanishes on
the local parameter axis through a base point whose second coordinate is zero, it is locally the
fiber coordinate times an analytic quotient.  The quotient is represented by
`chapterVIFiberHadamardSeries`. -/
theorem exists_hasFPowerSeriesAt_fiberHadamard
    (f : ℂ × ℂ → ℂ) (p : FormalMultilinearSeries ℂ (ℂ × ℂ) ℂ)
    (base : ℂ × ℂ) (hbase : base.2 = 0)
    (hf : HasFPowerSeriesAt f p base)
    (haxis : ∀ᶠ z in 𝓝 base.1, f (z, 0) = 0) :
    ∃ quotient : ℂ × ℂ → ℂ,
      HasFPowerSeriesAt quotient (chapterVIFiberHadamardSeries p) base ∧
      ∀ᶠ point in 𝓝 base,
        f point = (point.2 - base.2) * quotient point := by
  let qseries := chapterVIFiberHadamardSeries p
  let quotient : ℂ × ℂ → ℂ := fun point ↦ qseries.sum (point - base)
  have hqradius : 0 < qseries.radius := by
    exact chapterVIFiberHadamardSeries_radius_pos p hf.radius_pos
  have hqzero : HasFPowerSeriesAt qseries.sum qseries 0 :=
    (qseries.hasFPowerSeriesOnBall hqradius).hasFPowerSeriesAt
  have hquotient : HasFPowerSeriesAt quotient qseries base := by
    simpa [quotient] using hqzero.comp_sub base
  refine ⟨quotient, hquotient, ?_⟩
  have hhorizontalMap : ContinuousAt
      (fun point : ℂ × ℂ ↦ chapterVIFiberHorizontal (point - base)) base := by
    fun_prop
  have hhorizontalMapZero : Filter.Tendsto
      (fun point : ℂ × ℂ ↦ chapterVIFiberHorizontal (point - base))
      (𝓝 base) (𝓝 0) := by
    have hvalue : chapterVIFiberHorizontal (base - base) = (0 : ℂ × ℂ) := by
      simp
    rw [← hvalue]
    exact hhorizontalMap
  have hhorizontal : ∀ᶠ point in 𝓝 base,
      HasSum
        (fun n : ℕ ↦ p n
          (fun _ ↦ chapterVIFiberHorizontal (point - base)))
        (f (base + chapterVIFiberHorizontal (point - base))) := by
    have hpulled := hhorizontalMapZero.eventually hf.eventually_hasSum
    simpa using hpulled
  have haxisPoint : ∀ᶠ point : ℂ × ℂ in 𝓝 base,
      f (point.1, 0) = 0 :=
    continuousAt_fst.eventually haxis
  filter_upwards [hf.eventually_hasSum_sub, hhorizontal,
    hquotient.eventually_hasSum_sub, haxisPoint]
      with point hsource hhorizontalSource hquotientSum haxisZero
  have hid := chapterVIFiberHadamard_hasSum_identity p (point - base)
    hsource hhorizontalSource hquotientSum
  have hhorizontalPoint :
      base + chapterVIFiberHorizontal (point - base) = (point.1, 0) := by
    ext <;> simp [chapterVIFiberHorizontal, hbase]
  rw [hhorizontalPoint, haxisZero, sub_zero] at hid
  simpa using hid.symm

/-- In a local factorization `f(z,u) = u q(z,u)`, the quotient on the axis is the first fiber
derivative of `f`.  This supplies the vanishing hypothesis needed to apply Hadamard division a
second time. -/
theorem eventually_fiberHadamard_quotient_axis_eq_deriv
    (f quotient : ℂ × ℂ → ℂ) (base : ℂ × ℂ) (hbase : base.2 = 0)
    (hf : AnalyticAt ℂ f base)
    (hquotient : AnalyticAt ℂ quotient base)
    (hfactor : ∀ᶠ point in 𝓝 base,
      f point = (point.2 - base.2) * quotient point) :
    ∀ᶠ z in 𝓝 base.1,
      quotient (z, 0) = deriv (fun u ↦ f (z, u)) 0 := by
  have haxisMap : Filter.Tendsto (fun z : ℂ ↦ (z, (0 : ℂ)))
      (𝓝 base.1) (𝓝 base) := by
    have hmap : ContinuousAt (fun z : ℂ ↦ (z, (0 : ℂ))) base.1 :=
      continuousAt_id.prodMk continuousAt_const
    have hvalue : (base.1, (0 : ℂ)) = base := by
      ext <;> simp [hbase]
    rw [← hvalue]
    exact hmap
  have hanalyticAxis : ∀ᶠ z in 𝓝 base.1,
      AnalyticAt ℂ quotient (z, 0) :=
    haxisMap.eventually hquotient.eventually_analyticAt
  have hfAnalyticAxis : ∀ᶠ z in 𝓝 base.1,
      AnalyticAt ℂ f (z, 0) :=
    haxisMap.eventually hf.eventually_analyticAt
  have hfactorLocalAxis : ∀ᶠ z in 𝓝 base.1,
      ∀ᶠ point in 𝓝 (z, (0 : ℂ)),
        f point = (point.2 - base.2) * quotient point :=
    haxisMap.eventually hfactor.eventually_nhds
  filter_upwards [hanalyticAxis, hfAnalyticAxis, hfactorLocalAxis]
      with z hzAnalytic hzFAnalytic hzFactor
  have hfiberMap : Filter.Tendsto (fun u : ℂ ↦ (z, u))
      (𝓝 0) (𝓝 (z, (0 : ℂ))) :=
    continuousAt_const.prodMk continuousAt_id
  have hzFactorFiber : (fun u : ℂ ↦ f (z, u)) =ᶠ[𝓝 0]
      (fun u : ℂ ↦ u • quotient (z, u)) := by
    filter_upwards [hfiberMap.eventually hzFactor] with u hu
    simpa [hbase, smul_eq_mul] using hu
  have hquotientFiber : AnalyticAt ℂ (fun u : ℂ ↦ quotient (z, u)) 0 :=
    hzAnalytic.curry_right
  have hfFiber : AnalyticAt ℂ (fun u : ℂ ↦ f (z, u)) 0 :=
    hzFAnalytic.curry_right
  have hfactorZero : f (z, 0) = 0 := by
    have := hzFactorFiber.self_of_nhds
    simpa using this
  have hpunctured : dslope (fun u : ℂ ↦ f (z, u)) 0 =ᶠ[𝓝[≠] 0]
      (fun u : ℂ ↦ quotient (z, u)) := by
    filter_upwards [hzFactorFiber.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with u huFactor hu
    have hu_ne : u ≠ 0 := hu
    rw [dslope_of_ne _ hu]
    simp [slope, hfactorZero, huFactor, hu_ne]
  have hdslopeContinuous : ContinuousAt
      (dslope (fun u : ℂ ↦ f (z, u)) 0) 0 :=
    continuousAt_dslope_same.mpr hfFiber.differentiableAt
  have hfull :=
    (hdslopeContinuous.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
      hquotientFiber.continuousAt).mp hpunctured
  have hatZero := hfull.self_of_nhds
  simpa using hatZero.symm

end PoincareChapterVI
