/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import Mathlib.RingTheory.Length
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import PoincareChapterVI.Section103.LocalIntersection

/-!
# Intrinsic local intersection multiplicity for Section 103

The local intersection multiplicity of two plane curves at a point is the module length of their
scheme-theoretic intersection in the local ring at that point.  This file installs that intrinsic
definition over an arbitrary field and specializes it to the three exceptional points in
Poincaré's §103 count.

The definitions deliberately use local-algebra length, not the order of an elimination
resultant.  Relating the order-eight resultants to these lengths requires a separate fiberwise
resultant theorem with isolation and leading-coefficient hypotheses.
-/

noncomputable section

namespace PoincareChapterVI

abbrev PlanePolynomial (K : Type*) [CommRing K] := MvPolynomial (Fin 2) K

def affinePointIdeal (K : Type*) [Field K] (p : Fin 2 → K) : Ideal (PlanePolynomial K) :=
  RingHom.ker (MvPolynomial.eval p)

theorem affinePointIdeal_isPrime (K : Type*) [Field K] (p : Fin 2 → K) :
    (affinePointIdeal K p).IsPrime :=
  RingHom.ker_isPrime (MvPolynomial.eval p)

abbrev affinePointComplement (K : Type*) [Field K] (p : Fin 2 → K) :
    Submonoid (PlanePolynomial K) :=
  @Ideal.primeCompl _ _ (affinePointIdeal K p) (affinePointIdeal_isPrime K p)

theorem affinePointComplement_eq_primeCompl (K : Type*) [Field K] (p : Fin 2 → K) :
    affinePointComplement K p =
      @Ideal.primeCompl _ _ (affinePointIdeal K p) (affinePointIdeal_isPrime K p) := by
  rfl

abbrev PlaneLocalRing (K : Type*) [Field K] (p : Fin 2 → K) :=
  Localization (affinePointComplement K p)

instance (K : Type*) [Field K] (p : Fin 2 → K) :
    CommRing (PlaneLocalRing K p) := inferInstance

instance (K : Type*) [Field K] (p : Fin 2 → K) :
    Algebra (PlanePolynomial K) (PlaneLocalRing K p) := inferInstance

def localIntersectionIdeal (K : Type*) [Field K] (p : Fin 2 → K)
    (f g : PlanePolynomial K) : Ideal (PlaneLocalRing K p) :=
  Ideal.span {algebraMap (PlanePolynomial K) (PlaneLocalRing K p) f,
    algebraMap (PlanePolynomial K) (PlaneLocalRing K p) g}

abbrev LocalIntersectionAlgebra (K : Type*) [Field K] (p : Fin 2 → K)
    (f g : PlanePolynomial K) :=
  PlaneLocalRing K p ⧸ localIntersectionIdeal K p f g

def localIntersectionMultiplicity (K : Type*) [Field K] (p : Fin 2 → K)
    (f g : PlanePolynomial K) : ℕ∞ :=
  Module.length (PlaneLocalRing K p) (LocalIntersectionAlgebra K p f g)

theorem localIntersectionIdeal_comm (K : Type*) [Field K] (p : Fin 2 → K)
    (f g : PlanePolynomial K) :
    localIntersectionIdeal K p f g = localIntersectionIdeal K p g f := by
  unfold localIntersectionIdeal
  congr 1
  ext x
  simp [or_comm]

theorem localIntersectionMultiplicity_comm (K : Type*) [Field K] (p : Fin 2 → K)
    (f g : PlanePolynomial K) :
    localIntersectionMultiplicity K p f g = localIntersectionMultiplicity K p g f := by
  unfold localIntersectionMultiplicity LocalIntersectionAlgebra
  rw [localIntersectionIdeal_comm K p f g]

/-- A two-by-two local change of generators.  If

`f = x₂ * c + l * u` and `g = x₂ * t + l * s`,

and the determinant `c * s - u * t` does not vanish at the point, then `(f,g)` and
`(x₂,l)` generate the same ideal in the local ring.  This is the exact algebraic core of the
smooth-tangent-line calculation at the affine origin. -/
theorem localIntersectionIdeal_eq_of_matrixFactorization
    (K : Type*) [Field K] (p : Fin 2 → K)
    (f g x₂ l c u t s : PlanePolynomial K)
    (hf : f = x₂ * c + l * u) (hg : g = x₂ * t + l * s)
    (hdet : MvPolynomial.eval p (c * s - u * t) ≠ 0) :
    localIntersectionIdeal K p f g =
      Ideal.span {
        algebraMap (PlanePolynomial K) (PlaneLocalRing K p) x₂,
        algebraMap (PlanePolynomial K) (PlaneLocalRing K p) l} := by
  let φ : PlanePolynomial K →+* PlaneLocalRing K p := algebraMap _ _
  let Δ : PlanePolynomial K := c * s - u * t
  have hΔmem : Δ ∈ affinePointComplement K p := by
    simpa [Δ, affinePointComplement, affinePointIdeal, Ideal.primeCompl,
      RingHom.mem_ker] using hdet
  have hΔunit : IsUnit (φ Δ) :=
    IsLocalization.map_units (PlaneLocalRing K p) ⟨Δ, hΔmem⟩
  apply le_antisymm
  · rw [localIntersectionIdeal]
    refine Ideal.span_le.2 ?_
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · rw [hf, map_add, map_mul, map_mul]
      exact (Ideal.mem_span_pair.2 ⟨φ c, φ u, by ring⟩)
    · rw [hg, map_add, map_mul, map_mul]
      exact (Ideal.mem_span_pair.2 ⟨φ t, φ s, by ring⟩)
  · refine Ideal.span_le.2 ?_
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    have hfmem : φ f ∈ localIntersectionIdeal K p f g :=
      Ideal.subset_span (Set.mem_insert _ _)
    have hgmem : φ g ∈ localIntersectionIdeal K p f g :=
      Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    rcases hz with rfl | rfl
    · apply (Ideal.unit_mul_mem_iff_mem _ hΔunit).1
      have hcomb : φ Δ * φ x₂ = φ s * φ f - φ u * φ g := by
        rw [hf, hg]
        simp only [map_add, map_mul, Δ]
        rw [map_sub, map_mul, map_mul]
        ring
      rw [hcomb]
      exact (localIntersectionIdeal K p f g).sub_mem
        ((localIntersectionIdeal K p f g).mul_mem_left _ hfmem)
        ((localIntersectionIdeal K p f g).mul_mem_left _ hgmem)
    · apply (Ideal.unit_mul_mem_iff_mem _ hΔunit).1
      have hcomb : φ Δ * φ l = -φ t * φ f + φ c * φ g := by
        rw [hf, hg]
        simp only [map_add, map_mul, Δ]
        rw [map_sub, map_mul, map_mul]
        ring
      rw [hcomb]
      exact (localIntersectionIdeal K p f g).add_mem
        ((localIntersectionIdeal K p f g).mul_mem_left _ hfmem)
        ((localIntersectionIdeal K p f g).mul_mem_left _ hgmem)

/-- The intrinsic local-algebra length for the affine-origin contribution in §103. -/
def chapterVIOriginLocalIntersectionMultiplicity : ℕ∞ :=
  localIntersectionMultiplicity ℂ 0 chapterVISection103AffinePolynomial
    chapterVISection103ReducedAffinePolynomial

/-- The intrinsic local-algebra length at `(1 : 0 : 0)` in its `(y,z)` chart. -/
def chapterVIXInfinityLocalIntersectionMultiplicity : ℕ∞ :=
  localIntersectionMultiplicity ℂ 0 chapterVISection103XInfinitySextic
    chapterVISection103XInfinityReduced

/-- The intrinsic local-algebra length at `(0 : 1 : 0)` in its `(x,z)` chart. -/
def chapterVIYInfinityLocalIntersectionMultiplicity : ℕ∞ :=
  localIntersectionMultiplicity ℂ 0 chapterVISection103YInfinitySextic
    chapterVISection103YInfinityReduced

end PoincareChapterVI
