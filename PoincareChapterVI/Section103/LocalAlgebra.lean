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

def affinePointComplement (K : Type*) [Field K] (p : Fin 2 → K) :
    Submonoid (PlanePolynomial K) where
  carrier := {f | MvPolynomial.eval p f ≠ 0}
  one_mem' := by simp
  mul_mem' := by
    intro f g hf hg
    simpa using mul_ne_zero hf hg

theorem affinePointComplement_eq_primeCompl (K : Type*) [Field K] (p : Fin 2 → K) :
    affinePointComplement K p =
      @Ideal.primeCompl _ _ (affinePointIdeal K p) (affinePointIdeal_isPrime K p) := by
  ext f
  simp [affinePointComplement, affinePointIdeal, Ideal.primeCompl]

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
