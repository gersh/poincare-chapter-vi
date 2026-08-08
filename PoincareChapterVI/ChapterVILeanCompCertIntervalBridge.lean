/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import LeanCompCert.Ports.SignedProductClaims
import PoincareChapterVI.ChapterVIIntervalCertificate

/-!
# LeanCompCert bridge for Chapter VI signed dyadic intervals

This file translates the integer side conditions of the Chapter VI interval operations into
LeanCompCert's compiled signed-product claims.  Consequently, a zero result returned by the
compiled checker constructs the semantic multiplication or positive-reciprocal certificate used
by the real and complex interval proofs.
-/

namespace PoincareChapterVI.ChapterVILeanCompCertIntervalBridge

open LeanCompCert.Ports.SignedProductClaims

/-- Canonical sign-magnitude representation of a mathematical integer. -/
def signedWordOfInt : ℤ → SignedWord
  | .ofNat n => ⟨false, n⟩
  | .negSucc n => ⟨true, n + 1⟩

@[simp] theorem signedWordOfInt_val (z : ℤ) : (signedWordOfInt z).val = z := by
  cases z <;> simp [signedWordOfInt, SignedWord.val, Int.negSucc_eq]

/-- A signed product inequality in the form consumed by the compiled checker. -/
def productClaim (leftA leftB rightA rightB : ℤ) : Claim where
  leftA := signedWordOfInt leftA
  leftB := signedWordOfInt leftB
  rightA := signedWordOfInt rightA
  rightB := signedWordOfInt rightB

@[simp] theorem productClaim_holds_iff (leftA leftB rightA rightB : ℤ) :
    (productClaim leftA leftB rightA rightB).Holds ↔
      leftA * leftB ≤ rightA * rightB := by
  simp [productClaim, Claim.Holds]

/-- The well-formedness comparison and eight corner comparisons for one dyadic product. -/
def mulClaims {precision : ℕ}
    (x y output : ChapterVISignedDyadicInterval precision) : List Claim :=
  let scale : ℤ := 2 ^ precision
  [ productClaim output.lower 1 output.upper 1
  , productClaim output.lower scale x.lower y.lower
  , productClaim output.lower scale x.lower y.upper
  , productClaim output.lower scale x.upper y.lower
  , productClaim output.lower scale x.upper y.upper
  , productClaim x.lower y.lower output.upper scale
  , productClaim x.lower y.upper output.upper scale
  , productClaim x.upper y.lower output.upper scale
  , productClaim x.upper y.upper output.upper scale ]

/-- Every compiled product claim holding reconstructs the mathematical dyadic certificate. -/
theorem mulCertificate_of_allHold {precision : ℕ}
    (x y output : ChapterVISignedDyadicInterval precision)
    (hall : ∀ claim ∈ mulClaims x y output, claim.Holds) :
    ChapterVISignedDyadicInterval.MulCertificate x y output where
  output_wf := by
    have h := hall (productClaim output.lower 1 output.upper 1) (by simp [mulClaims])
    simpa using h
  lower_ll := by
    simpa only [productClaim_holds_iff] using
      hall (productClaim output.lower (2 ^ precision) x.lower y.lower)
        (by simp [mulClaims])
  lower_lu := by
    simpa only [productClaim_holds_iff] using
      hall (productClaim output.lower (2 ^ precision) x.lower y.upper)
        (by simp [mulClaims])
  lower_ul := by
    simpa only [productClaim_holds_iff] using
      hall (productClaim output.lower (2 ^ precision) x.upper y.lower)
        (by simp [mulClaims])
  lower_uu := by
    simpa only [productClaim_holds_iff] using
      hall (productClaim output.lower (2 ^ precision) x.upper y.upper)
        (by simp [mulClaims])
  upper_ll := by
    simpa only [productClaim_holds_iff] using
      hall (productClaim x.lower y.lower output.upper (2 ^ precision))
        (by simp [mulClaims])
  upper_lu := by
    simpa only [productClaim_holds_iff] using
      hall (productClaim x.lower y.upper output.upper (2 ^ precision))
        (by simp [mulClaims])
  upper_ul := by
    simpa only [productClaim_holds_iff] using
      hall (productClaim x.upper y.lower output.upper (2 ^ precision))
        (by simp [mulClaims])
  upper_uu := by
    simpa only [productClaim_holds_iff] using
      hall (productClaim x.upper y.upper output.upper (2 ^ precision))
        (by simp [mulClaims])

/-- A successful compiled run proves a signed-dyadic multiplication certificate. -/
theorem mulCertificate_of_compiled {precision : ℕ} (name : String)
    (x y output : ChapterVISignedDyadicInterval precision)
    (hadmissible : Admissible (mulClaims x y output))
    (hrun : (claimComputation name (mulClaims x y output)).Returns ((0 : Nat) : Int)) :
    ChapterVISignedDyadicInterval.MulCertificate x y output :=
  mulCertificate_of_allHold x y output
    (allHold_of_returns_zero name (mulClaims x y output) hadmissible hrun)

/-- Consumer-facing semantic form of the compiled multiplication theorem. -/
theorem mul_contains_of_compiled {precision : ℕ} (name : String)
    (x y output : ChapterVISignedDyadicInterval precision)
    (hadmissible : Admissible (mulClaims x y output))
    (hrun : (claimComputation name (mulClaims x y output)).Returns ((0 : Nat) : Int))
    {a b : ℝ} (ha : x.Contains a) (hb : y.Contains b) :
    output.Contains (a * b) :=
  (mulCertificate_of_compiled name x y output hadmissible hrun).contains_mul ha hb

/-- Positivity, well-formedness, nonnegativity, and the two cross-multiplied reciprocal bounds. -/
def positiveReciprocalClaims {precision : ℕ}
    (input output : ChapterVISignedDyadicInterval precision) : List Claim :=
  let scale : ℤ := 2 ^ precision
  [ productClaim 1 1 input.lower 1
  , productClaim output.lower 1 output.upper 1
  , productClaim 0 1 output.lower 1
  , productClaim output.lower input.upper scale scale
  , productClaim scale scale output.upper input.lower ]

/-- Every compiled reciprocal claim holding reconstructs the mathematical certificate. -/
theorem positiveReciprocalCertificate_of_allHold {precision : ℕ}
    (input output : ChapterVISignedDyadicInterval precision)
    (hall : ∀ claim ∈ positiveReciprocalClaims input output, claim.Holds) :
    ChapterVISignedDyadicInterval.PositiveReciprocalCertificate input output where
  input_lower_pos := by
    have h := hall (productClaim 1 1 input.lower 1) (by simp [positiveReciprocalClaims])
    simp only [productClaim_holds_iff, mul_one] at h
    omega
  output_wf := by
    have h := hall (productClaim output.lower 1 output.upper 1)
      (by simp [positiveReciprocalClaims])
    simpa using h
  output_lower_nonneg := by
    have h := hall (productClaim 0 1 output.lower 1) (by simp [positiveReciprocalClaims])
    simpa using h
  lower_cross := by
    simpa only [productClaim_holds_iff, pow_two] using
      hall (productClaim output.lower input.upper (2 ^ precision) (2 ^ precision))
        (by simp [positiveReciprocalClaims])
  upper_cross := by
    simpa only [productClaim_holds_iff, pow_two] using
      hall (productClaim (2 ^ precision) (2 ^ precision) output.upper input.lower)
        (by simp [positiveReciprocalClaims])

/-- A successful compiled run proves a positive signed-dyadic reciprocal certificate. -/
theorem positiveReciprocalCertificate_of_compiled {precision : ℕ} (name : String)
    (input output : ChapterVISignedDyadicInterval precision)
    (hadmissible : Admissible (positiveReciprocalClaims input output))
    (hrun : (claimComputation name (positiveReciprocalClaims input output)).Returns
      ((0 : Nat) : Int)) :
    ChapterVISignedDyadicInterval.PositiveReciprocalCertificate input output :=
  positiveReciprocalCertificate_of_allHold input output
    (allHold_of_returns_zero name (positiveReciprocalClaims input output) hadmissible hrun)

/-- Consumer-facing semantic form of the compiled positive-reciprocal theorem. -/
theorem inv_contains_of_compiled {precision : ℕ} (name : String)
    (input output : ChapterVISignedDyadicInterval precision)
    (hadmissible : Admissible (positiveReciprocalClaims input output))
    (hrun : (claimComputation name (positiveReciprocalClaims input output)).Returns
      ((0 : Nat) : Int))
    {value : ℝ} (hvalue : input.Contains value) :
    output.Contains value⁻¹ :=
  (positiveReciprocalCertificate_of_compiled name input output hadmissible hrun).contains_inv
    hvalue

end PoincareChapterVI.ChapterVILeanCompCertIntervalBridge
