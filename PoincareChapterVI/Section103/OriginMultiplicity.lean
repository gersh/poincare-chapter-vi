/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.Section103.LocalAlgebra
import Mathlib.RingTheory.DualNumber
import Mathlib.RingTheory.MvPolynomial.Ideal

/-!
# The affine-origin certificate in Poincaré's Section 103

This file makes the tangent calculation at the affine origin exact.  Both Section 103
polynomials are expressed in the local coordinates `x²` and `y + αx`; the determinant of the
change-of-generators matrix is then proved nonzero at the origin.  Consequently their localized
intersection ideal is exactly `(x², y + αx)`.
-/

noncomputable section

open scoped BigOperators
open scoped DualNumber

namespace PoincareChapterVI

private abbrev BivarC := MvPolynomial (Fin 2) ℂ
private def ox : BivarC := MvPolynomial.X 0
private def oy : BivarC := MvPolynomial.X 1

def originAlpha : ℂ :=
  (6564100 : ℂ) / 6194669 + (672000 / 6194669 : ℂ) * Complex.I

def originLine : BivarC := oy + MvPolynomial.C originAlpha * ox

def powerDiffQuotient (v w : BivarC) (n : Nat) : BivarC :=
  ∑ k ∈ Finset.range n, v ^ (n - 1 - k) * w ^ k

theorem line_mul_powerDiffQuotient (n : Fin 5) :
    originLine * powerDiffQuotient oy (-MvPolynomial.C originAlpha * ox) n.val =
      oy ^ n.val - (-MvPolynomial.C originAlpha * ox) ^ n.val := by
  fin_cases n <;>
    norm_num [powerDiffQuotient, Finset.sum_range_succ, originLine] <;> ring

def originP_c : BivarC :=
  ∑ a : Fin 5, ∑ b : Fin 5,
    MvPolynomial.C (chapterVISection103AffineGaussianCoefficient a b : ℂ) *
      MvPolynomial.C ((-originAlpha) ^ b.val) * ox ^ (a.val + b.val - 2)

def originP_u : BivarC :=
  ∑ a : Fin 5, ∑ b : Fin 5,
    MvPolynomial.C (chapterVISection103AffineGaussianCoefficient a b : ℂ) *
      ox ^ a.val * powerDiffQuotient oy (-MvPolynomial.C originAlpha * ox) b.val

def originRResidualCoefficient (a b : Fin 5) : ℂ :=
  (chapterVISection103ReducedGaussianCoefficient a b : ℂ) -
    if a.val = 1 ∧ b.val = 0 then 106500 - 96000 * Complex.I
    else if a.val = 0 ∧ b.val = 1 then 90285 - 99840 * Complex.I
    else 0

def originR_t : BivarC :=
  ∑ a : Fin 5, ∑ b : Fin 5,
    MvPolynomial.C (originRResidualCoefficient a b) *
      MvPolynomial.C ((-originAlpha) ^ b.val) * ox ^ (a.val + b.val - 2)

def originR_s0 : BivarC :=
  ∑ a : Fin 5, ∑ b : Fin 5,
    MvPolynomial.C (originRResidualCoefficient a b) *
      ox ^ a.val * powerDiffQuotient oy (-MvPolynomial.C originAlpha * ox) b.val

def originR_s : BivarC :=
  MvPolynomial.C (90285 - 99840 * Complex.I) + originR_s0

def originRawTangent : BivarC :=
  MvPolynomial.C (106500 - 96000 * Complex.I) * ox +
    MvPolynomial.C (90285 - 99840 * Complex.I) * oy

theorem originP_factorization :
    chapterVISection103AffinePolynomial =
      ox ^ 2 * originP_c + originLine * originP_u := by
  change (∑ a : Fin 5, ∑ b : Fin 5,
    MvPolynomial.monomial
      (Finsupp.single 0 a.val + Finsupp.single 1 b.val)
      (chapterVISection103AffineGaussianCoefficient a b : ℂ)) = _
  simp [originP_c, originP_u, Fin.sum_univ_succ, ox, oy,
    MvPolynomial.monomial_eq, Finsupp.prod_fintype, Fin.prod_univ_succ,
    powerDiffQuotient, Finset.sum_range_succ, originLine,
    chapterVISection103AffineGaussianCoefficient, GaussianInt.toComplex_def]
  ring

theorem originR_factorization :
    chapterVISection103ReducedAffinePolynomial =
      ox ^ 2 * originR_t + originLine * originR_s := by
  have halpha : (90285 - 99840 * Complex.I) * originAlpha =
      (106500 - 96000 * Complex.I) := by
    apply Complex.ext <;>
      norm_num [originAlpha, Complex.mul_re, Complex.mul_im]
  have hraw : originRawTangent =
      MvPolynomial.C (90285 - 99840 * Complex.I) * originLine := by
    unfold originRawTangent originLine
    rw [mul_add, ← mul_assoc, ← map_mul, halpha]
    ring
  have hres :
      chapterVISection103ReducedAffinePolynomial - originRawTangent =
        ox ^ 2 * originR_t + originLine * originR_s0 := by
    change (∑ a : Fin 5, ∑ b : Fin 5,
      MvPolynomial.monomial
        (Finsupp.single 0 a.val + Finsupp.single 1 b.val)
        (chapterVISection103ReducedGaussianCoefficient a b : ℂ)) - _ = _
    simp [originRawTangent, originR_t, originR_s0, originRResidualCoefficient,
      Fin.sum_univ_succ, ox, oy,
      MvPolynomial.monomial_eq, Finsupp.prod_fintype, Fin.prod_univ_succ,
      powerDiffQuotient, Finset.sum_range_succ, originLine,
      chapterVISection103ReducedGaussianCoefficient, GaussianInt.toComplex_def]
    norm_num [originAlpha]
    simp only [map_ofNat]
    ring
  calc
    chapterVISection103ReducedAffinePolynomial =
        (chapterVISection103ReducedAffinePolynomial - originRawTangent) +
          originRawTangent := by ring
    _ = (ox ^ 2 * originR_t + originLine * originR_s0) +
          MvPolynomial.C (90285 - 99840 * Complex.I) * originLine := by
      rw [hres, hraw]
    _ = ox ^ 2 * originR_t + originLine * originR_s := by
      simp only [originR_s]
      ring

theorem origin_det_nonzero :
    MvPolynomial.eval (0 : Fin 2 → ℂ)
      (originP_c * originR_s - originP_u * originR_t) ≠ 0 := by
  have hc : MvPolynomial.eval (0 : Fin 2 → ℂ) originP_c =
      4563 * originAlpha ^ 2 - (21320 - 33280 * Complex.I) * originAlpha + 7500 := by
    simp only [originP_c, ox, map_sum, map_mul, map_pow, MvPolynomial.eval_C,
      MvPolynomial.eval_X, Pi.zero_apply]
    norm_num [originAlpha, Fin.sum_univ_succ,
      chapterVISection103AffineGaussianCoefficient, GaussianInt.toComplex_def]
    ring
  have hs : MvPolynomial.eval (0 : Fin 2 → ℂ) originR_s =
      90285 - 99840 * Complex.I := by
    simp only [originR_s, originR_s0, ox, oy, map_add, map_sum, map_mul, map_pow,
      MvPolynomial.eval_C, MvPolynomial.eval_X, Pi.zero_apply]
    norm_num [originRResidualCoefficient, powerDiffQuotient,
      Finset.sum_range_succ, Fin.sum_univ_succ,
      chapterVISection103ReducedGaussianCoefficient,
      GaussianInt.toComplex_def]
  have hu : MvPolynomial.eval (0 : Fin 2 → ℂ) originP_u = 0 := by
    simp only [originP_u, ox, oy, map_sum, map_mul, map_pow, MvPolynomial.eval_C,
      MvPolynomial.eval_X, Pi.zero_apply]
    norm_num [powerDiffQuotient, Finset.sum_range_succ, Fin.sum_univ_succ,
      chapterVISection103AffineGaussianCoefficient,
      GaussianInt.toComplex_def]
  rw [map_sub, map_mul, map_mul, hc, hs, hu, zero_mul, sub_zero]
  apply mul_ne_zero
  · intro h
    have hr := congrArg Complex.re h
    norm_num [originAlpha, pow_two, Complex.div_re, Complex.div_im, Complex.mul_re,
      Complex.mul_im, Complex.normSq_apply] at hr
  · norm_num [Complex.ext_iff]

/-- The two Section 103 germs at the affine origin generate exactly the curvilinear double-point
ideal `(x², y + αx)` in the local ring. -/
theorem chapterVI_origin_localIntersectionIdeal_eq :
    localIntersectionIdeal ℂ 0 chapterVISection103AffinePolynomial
        chapterVISection103ReducedAffinePolynomial =
      Ideal.span {
        algebraMap (PlanePolynomial ℂ) (PlaneLocalRing ℂ 0) (ox ^ 2),
        algebraMap (PlanePolynomial ℂ) (PlaneLocalRing ℂ 0) originLine} :=
  localIntersectionIdeal_eq_of_matrixFactorization ℂ 0
    chapterVISection103AffinePolynomial chapterVISection103ReducedAffinePolynomial
    (ox ^ 2) originLine originP_c originP_u originR_t originR_s
    originP_factorization originR_factorization origin_det_nonzero

/-! ## The local length -/

private theorem orderIso_map_covBy {α β : Type*} [PartialOrder α] [PartialOrder β]
    (e : α ≃o β) {a b : α} (h : a ⋖ b) : e a ⋖ e b := by
  rw [covBy_iff_lt_and_eq_or_eq] at h ⊢
  refine ⟨e.lt_iff_lt.mpr h.1, ?_⟩
  intro c hac hcb
  have hac' : a ≤ e.symm c := by simpa using e.symm.monotone hac
  have hcb' : e.symm c ≤ b := by simpa using e.symm.monotone hcb
  rcases h.2 (e.symm c) hac' hcb' with hc | hc
  · left
    simpa using congrArg e hc
  · right
    simpa using congrArg e hc

/-- In a local ring whose maximal ideal is `(x,l)`, the ideal `(x²,l)` is immediately below the
maximal ideal as soon as the class of `x` is nonzero modulo `(x²,l)`. -/
theorem span_sq_line_covBy_span_line
    (A : Type*) [CommRing A] [IsLocalRing A] (x l : A)
    (hm : IsLocalRing.maximalIdeal A = Ideal.span {x, l})
    (hx : x ∉ Ideal.span {x ^ 2, l}) :
    Ideal.span {x ^ 2, l} ⋖ IsLocalRing.maximalIdeal A := by
  let J : Ideal A := Ideal.span {x ^ 2, l}
  let m : Ideal A := IsLocalRing.maximalIdeal A
  have hx_m : x ∈ m := by
    change x ∈ IsLocalRing.maximalIdeal A
    rw [hm]
    exact Ideal.subset_span (Set.mem_insert _ _)
  have hl_m : l ∈ m := by
    change l ∈ IsLocalRing.maximalIdeal A
    rw [hm]
    exact Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hJm : J ≤ m := by
    refine Ideal.span_le.2 ?_
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact m.pow_mem_of_mem hx_m 2 (by omega)
    · exact hl_m
  rw [SetLike.covBy_iff]
  refine ⟨lt_of_le_of_ne hJm ?_, ?_⟩
  · intro h
    apply hx
    rw [h]
    exact hx_m
  · intro I z hJI hIm hzJ hzI
    have hz_m : z ∈ Ideal.span {x, l} := by
      rw [← hm]
      exact hIm hzI
    obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.mp hz_m
    have hl_J : l ∈ J := Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    have haxI : a * x ∈ I := by
      have hzI' := hzI
      rw [← hab] at hzI'
      simpa only [add_sub_cancel_right] using
        I.sub_mem hzI' (hJI (J.mul_mem_left b hl_J))
    have ha_unit : IsUnit a := by
      by_contra ha
      have ha_m : a ∈ m := by
        change a ∈ IsLocalRing.maximalIdeal A
        rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
        exact ha
      change a ∈ IsLocalRing.maximalIdeal A at ha_m
      rw [hm] at ha_m
      obtain ⟨c, d, hcd⟩ := Ideal.mem_span_pair.mp ha_m
      have haxJ : a * x ∈ J := by
        have heq : a * x = c * x ^ 2 + (d * x) * l := by
          rw [← hcd]
          ring
        rw [heq]
        exact J.add_mem (J.mul_mem_left c
          (Ideal.subset_span (Set.mem_insert _ _)))
          (J.mul_mem_left (d * x) hl_J)
      apply hzJ
      rw [← hab]
      exact J.add_mem haxJ (J.mul_mem_left b hl_J)
    apply le_antisymm hIm
    rw [hm]
    refine Ideal.span_le.2 ?_
    intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl
    · exact (Ideal.unit_mul_mem_iff_mem I ha_unit).1 haxI
    · exact hJI hl_J

/-- Two covering relations from an ideal to the top give the quotient a composition series of
length two. -/
theorem length_quotient_eq_two_of_covBy
    (A : Type*) [CommRing A] (J m : Ideal A)
    (hJm : J ⋖ m) (hm : m ⋖ (⊤ : Ideal A)) :
    Module.length A (A ⧸ J) = 2 := by
  let e := Submodule.comapMkQRelIso J
  let N0 : Submodule A (A ⧸ J) := e.symm ⟨J, show J ≤ J from le_rfl⟩
  let N : Submodule A (A ⧸ J) := e.symm ⟨m, hJm.le⟩
  let N2 : Submodule A (A ⧸ J) :=
    e.symm ⟨⊤, show J ≤ (⊤ : Ideal A) from le_top⟩
  have subtypeCovBy {a b : Ideal A} (ha : J ≤ a) (h : a ⋖ b) :
      (⟨a, ha⟩ : Set.Ici J) ⋖ ⟨b, ha.trans h.le⟩ := by
    rw [covBy_iff_lt_and_eq_or_eq] at h ⊢
    refine ⟨h.1, ?_⟩
    intro c hac hcb
    rcases h.2 c.1 hac hcb with hc | hc
    · exact Or.inl (Subtype.ext hc)
    · exact Or.inr (Subtype.ext hc)
  have hN0N : N0 ⋖ N :=
    orderIso_map_covBy e.symm (subtypeCovBy le_rfl hJm)
  have hNN2 : N ⋖ N2 :=
    orderIso_map_covBy e.symm (subtypeCovBy hJm.le hm)
  have hN0 : N0 = ⊥ := by
    change Submodule.map J.mkQ J = ⊥
    apply le_antisymm
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := hy
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hx
    · exact bot_le
  have hN2 : N2 = ⊤ := by
    change Submodule.map J.mkQ ⊤ = ⊤
    rw [Submodule.map_top, LinearMap.range_eq_top]
    exact Ideal.Quotient.mk_surjective
  let s : CompositionSeries (Submodule A (A ⧸ J)) := {
    length := 2
    toFun := ![N0, N, N2]
    step := by
      intro i
      fin_cases i
      · exact hN0N
      · exact hNN2
  }
  rw [← Module.length_compositionSeries s (by exact hN0) (by exact hN2)]
  rfl

theorem mem_idealOfVars_iff_constantCoeff_eq_zero
    {σ K : Type*} [Field K] (f : MvPolynomial σ K) :
    f ∈ MvPolynomial.idealOfVars σ K ↔ MvPolynomial.constantCoeff f = 0 := by
  rw [MvPolynomial.idealOfVars, ← Set.image_univ,
    MvPolynomial.mem_ideal_span_X_image]
  constructor
  · intro h
    by_contra h0
    have hs : (0 : σ →₀ ℕ) ∈ f.support := MvPolynomial.mem_support_iff.mpr h0
    obtain ⟨i, -, hi⟩ := h 0 hs
    exact hi rfl
  · intro h m hm
    by_cases hm0 : m = 0
    · subst m
      exact (MvPolynomial.mem_support_iff.mp hm h).elim
    · obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hm0
      exact ⟨i, Set.mem_univ i, hi⟩

theorem affinePointIdeal_zero_eq_idealOfVars :
    affinePointIdeal ℂ 0 = MvPolynomial.idealOfVars (Fin 2) ℂ := by
  ext f
  rw [mem_idealOfVars_iff_constantCoeff_eq_zero]
  simp only [affinePointIdeal, RingHom.mem_ker, MvPolynomial.eval_zero]

theorem finTwo_idealOfVars_eq_span_originLine :
    MvPolynomial.idealOfVars (Fin 2) ℂ = Ideal.span {ox, originLine} := by
  have hrange : Set.range (MvPolynomial.X : Fin 2 → BivarC) = {ox, oy} := by
    ext f
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp [ox, oy]
    · intro h
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
      rcases h with rfl | rfl
      · exact ⟨0, by simp [ox]⟩
      · exact ⟨1, by simp [oy]⟩
  rw [MvPolynomial.idealOfVars, hrange]
  apply le_antisymm
  · refine Ideal.span_le.2 ?_
    intro f hf
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hf
    rcases hf with rfl | rfl
    · exact Ideal.subset_span (Set.mem_insert _ _)
    · have hx : ox ∈ Ideal.span {ox, originLine} :=
        Ideal.subset_span (Set.mem_insert _ _)
      have hl : originLine ∈ Ideal.span {ox, originLine} :=
        Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
      have := (Ideal.span {ox, originLine}).sub_mem hl
        ((Ideal.span {ox, originLine}).mul_mem_left (MvPolynomial.C originAlpha) hx)
      simpa [originLine] using this
  · refine Ideal.span_le.2 ?_
    intro f hf
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hf
    rcases hf with rfl | rfl
    · exact Ideal.subset_span (Set.mem_insert _ _)
    · exact (Ideal.span {ox, oy}).add_mem
        (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
        ((Ideal.span {ox, oy}).mul_mem_left (MvPolynomial.C originAlpha)
          (Ideal.subset_span (Set.mem_insert _ _)))

local instance originPointIdeal_isPrime : (affinePointIdeal ℂ 0).IsPrime :=
  affinePointIdeal_isPrime ℂ 0

local instance originPlaneLocalRing_isLocalRing : IsLocalRing (PlaneLocalRing ℂ 0) := by
  infer_instance

theorem origin_maximalIdeal_eq_span :
    IsLocalRing.maximalIdeal (PlaneLocalRing ℂ 0) =
      Ideal.span {
        algebraMap (PlanePolynomial ℂ) (PlaneLocalRing ℂ 0) ox,
        algebraMap (PlanePolynomial ℂ) (PlaneLocalRing ℂ 0) originLine} := by
  rw [← Localization.AtPrime.map_eq_maximalIdeal]
  have hglobal : affinePointIdeal ℂ 0 = Ideal.span {ox, originLine} :=
    affinePointIdeal_zero_eq_idealOfVars.trans finTwo_idealOfVars_eq_span_originLine
  let φ : PlanePolynomial ℂ →+* PlaneLocalRing ℂ 0 := algebraMap _ _
  calc
    Ideal.map φ (affinePointIdeal ℂ 0) =
        Ideal.map φ (Ideal.span {ox, originLine}) :=
      congrArg (Ideal.map φ) hglobal
    _ = Ideal.span (φ '' {ox, originLine}) := Ideal.map_span φ _
    _ = Ideal.span {φ ox, φ originLine} := by
      congr 1
      ext f
      simp [eq_comm]

private def originDualAssignment (i : Fin 2) : ℂ[ε] :=
  ![(ε : ℂ[ε]), -originAlpha • (ε : ℂ[ε])] i

private def originDualPolynomialHom : PlanePolynomial ℂ →+* ℂ[ε] :=
  (MvPolynomial.aeval originDualAssignment).toRingHom

private theorem originDualPolynomialHom_fst (f : PlanePolynomial ℂ) :
    (originDualPolynomialHom f).fst = MvPolynomial.eval 0 f := by
  let lhs : PlanePolynomial ℂ →ₐ[ℂ] ℂ :=
    (TrivSqZeroExt.fstHom ℂ ℂ ℂ).comp (MvPolynomial.aeval originDualAssignment)
  let rhs : PlanePolynomial ℂ →ₐ[ℂ] ℂ := MvPolynomial.aeval 0
  have h : lhs = rhs := by
    ext i
    fin_cases i <;> simp [lhs, rhs, originDualAssignment]
  exact DFunLike.congr_fun h f

private theorem originDualPolynomialHom_unit
    (s : affinePointComplement ℂ 0) : IsUnit (originDualPolynomialHom s) := by
  rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, originDualPolynomialHom_fst]
  rw [isUnit_iff_ne_zero]
  simpa [affinePointComplement, affinePointIdeal, Ideal.primeCompl,
    RingHom.mem_ker] using s.property

private def originLocalToDual : PlaneLocalRing ℂ 0 →+* ℂ[ε] :=
  IsLocalization.lift originDualPolynomialHom_unit

private theorem originLocalToDual_algebraMap (f : PlanePolynomial ℂ) :
    originLocalToDual (algebraMap (PlanePolynomial ℂ) (PlaneLocalRing ℂ 0) f) =
      originDualPolynomialHom f :=
  IsLocalization.lift_eq originDualPolynomialHom_unit f

theorem origin_x_not_mem_modelIdeal :
    algebraMap (PlanePolynomial ℂ) (PlaneLocalRing ℂ 0) ox ∉
      Ideal.span {
        (algebraMap (PlanePolynomial ℂ) (PlaneLocalRing ℂ 0) ox) ^ 2,
        algebraMap (PlanePolynomial ℂ) (PlaneLocalRing ℂ 0) originLine} := by
  let x : PlaneLocalRing ℂ 0 := algebraMap _ _ ox
  let l : PlaneLocalRing ℂ 0 := algebraMap _ _ originLine
  let J : Ideal (PlaneLocalRing ℂ 0) := Ideal.span {x ^ 2, l}
  have hxmap : originLocalToDual x = (ε : ℂ[ε]) := by
    rw [originLocalToDual_algebraMap]
    simp [originDualPolynomialHom, originDualAssignment, ox]
  have hlmap : originLocalToDual l = 0 := by
    rw [originLocalToDual_algebraMap]
    simp [originDualPolynomialHom, originDualAssignment, originLine, ox, oy,
      Algebra.smul_def]
  have hJker : J ≤ RingHom.ker originLocalToDual := by
    refine Ideal.span_le.2 ?_
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · simp [RingHom.mem_ker, hxmap]
    · simpa [RingHom.mem_ker] using hlmap
  intro hx
  have hzero : originLocalToDual x = 0 := hJker hx
  rw [hxmap] at hzero
  have heps : (ε : ℂ[ε]) ≠ 0 := by
    intro h
    have := congrArg TrivSqZeroExt.snd h
    norm_num at this
  exact heps hzero

/-- The affine-origin contribution in Poincaré's Section 103 is intrinsically equal to two. -/
theorem chapterVIOriginLocalIntersectionMultiplicity_eq_two :
    chapterVIOriginLocalIntersectionMultiplicity = 2 := by
  let x : PlaneLocalRing ℂ 0 := algebraMap _ _ ox
  let l : PlaneLocalRing ℂ 0 := algebraMap _ _ originLine
  let J : Ideal (PlaneLocalRing ℂ 0) := Ideal.span {x ^ 2, l}
  have hJm : J ⋖ IsLocalRing.maximalIdeal (PlaneLocalRing ℂ 0) :=
    span_sq_line_covBy_span_line (PlaneLocalRing ℂ 0) x l
      origin_maximalIdeal_eq_span origin_x_not_mem_modelIdeal
  have hm : IsLocalRing.maximalIdeal (PlaneLocalRing ℂ 0) ⋖
      (⊤ : Ideal (PlaneLocalRing ℂ 0)) :=
    (Ideal.isMaximal_def.mp
      (inferInstance : (IsLocalRing.maximalIdeal (PlaneLocalRing ℂ 0)).IsMaximal)).covBy_top
  have hIdeal :
      localIntersectionIdeal ℂ 0 chapterVISection103AffinePolynomial
          chapterVISection103ReducedAffinePolynomial = J := by
    rw [chapterVI_origin_localIntersectionIdeal_eq]
    simp only [map_pow]
    change J = J
    rfl
  unfold chapterVIOriginLocalIntersectionMultiplicity localIntersectionMultiplicity
  change Module.length (PlaneLocalRing ℂ 0)
    ((PlaneLocalRing ℂ 0) ⧸ localIntersectionIdeal ℂ 0
      chapterVISection103AffinePolynomial chapterVISection103ReducedAffinePolynomial) = 2
  let F := fun I : Ideal (PlaneLocalRing ℂ 0) =>
    Module.length (PlaneLocalRing ℂ 0) ((PlaneLocalRing ℂ 0) ⧸ I) = 2
  exact Eq.mpr (congrArg F hIdeal)
    (length_quotient_eq_two_of_covBy (PlaneLocalRing ℂ 0) J
      (IsLocalRing.maximalIdeal (PlaneLocalRing ℂ 0)) hJm hm)

end PoincareChapterVI
