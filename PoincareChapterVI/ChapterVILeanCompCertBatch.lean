/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.ChapterVILeanCompCertIntervalBridge

/-!
# One compiled verdict for a Chapter VI interval campaign

A realistic outer-arc table contains many signed-dyadic multiplications and reciprocals.  Running
one compiled artifact per operation would obscure what was checked and would not scale.  This file
flattens every operation's signed-product conditions into one claim list and proves that a zero
failure count reconstructs every individual semantic interval certificate.
-/

namespace PoincareChapterVI.ChapterVILeanCompCertBatch

open LeanCompCert.Ports.SignedProductClaims
open ChapterVILeanCompCertIntervalBridge

/-- The two rounded interval operations needed by the sparse outer-arc evaluator. -/
inductive DyadicOperation (precision : ℕ)
  | mul (x y output : ChapterVISignedDyadicInterval precision)
  | positiveReciprocal (input output : ChapterVISignedDyadicInterval precision)
  | positiveLower (input : ChapterVISignedDyadicInterval precision)
  | rawClaim (claim : Claim)

namespace DyadicOperation

def claims {precision : ℕ} : DyadicOperation precision → List Claim
  | .mul x y output => mulClaims x y output
  | .positiveReciprocal input output => positiveReciprocalClaims input output
  | .positiveLower input => [productClaim 1 1 input.lower 1]
  | .rawClaim claim => [claim]

/-- Mathematical meaning reconstructed after the corresponding claims pass. -/
def Sound {precision : ℕ} : DyadicOperation precision → Prop
  | .mul x y output => ChapterVISignedDyadicInterval.MulCertificate x y output
  | .positiveReciprocal input output =>
      ChapterVISignedDyadicInterval.PositiveReciprocalCertificate input output
  | .positiveLower input => 0 < input.lower
  | .rawClaim claim => claim.Holds

theorem sound_of_allHold {precision : ℕ} (operation : DyadicOperation precision)
    (hall : ∀ claim ∈ operation.claims, claim.Holds) : operation.Sound := by
  cases operation with
  | mul x y output => exact mulCertificate_of_allHold x y output hall
  | positiveReciprocal input output =>
      exact positiveReciprocalCertificate_of_allHold input output hall
  | positiveLower input =>
      have h := hall (productClaim 1 1 input.lower 1) (by simp [claims])
      simp only [productClaim_holds_iff, mul_one] at h
      exact Int.zero_lt_one.trans_le h
  | rawClaim claim => exact hall claim (by simp [claims])

end DyadicOperation

/-- Concatenated machine input for an entire interval campaign. -/
def batchClaims {precision : ℕ}
    (operations : List (DyadicOperation precision)) : List Claim :=
  operations.flatMap DyadicOperation.claims

def batchComputation {precision : ℕ} (name : String)
    (operations : List (DyadicOperation precision)) : LeanCompCert.Verified.Computation :=
  claimComputation name (batchClaims operations)

/-- One zero verdict reconstructs every operation certificate in the batch. -/
theorem allSound_of_returns_zero {precision : ℕ} (name : String)
    (operations : List (DyadicOperation precision))
    (hadmissible : Admissible (batchClaims operations))
    (hrun : (batchComputation name operations).Returns ((0 : Nat) : Int)) :
    ∀ operation ∈ operations, operation.Sound := by
  have hall := allHold_of_returns_zero name (batchClaims operations) hadmissible hrun
  intro operation hoperation
  apply operation.sound_of_allHold
  intro claim hclaim
  apply hall claim
  rw [batchClaims, List.mem_flatMap]
  exact ⟨operation, hoperation, hclaim⟩

/-- Consumer form for a multiplication appearing anywhere in the checked campaign. -/
theorem mul_contains_of_batch {precision : ℕ} (name : String)
    (operations : List (DyadicOperation precision))
    (x y output : ChapterVISignedDyadicInterval precision)
    (hoperation : DyadicOperation.mul x y output ∈ operations)
    (hadmissible : Admissible (batchClaims operations))
    (hrun : (batchComputation name operations).Returns ((0 : Nat) : Int))
    {a b : ℝ} (ha : x.Contains a) (hb : y.Contains b) :
    output.Contains (a * b) := by
  have certificate :=
    allSound_of_returns_zero name operations hadmissible hrun
      (.mul x y output) hoperation
  exact certificate.contains_mul ha hb

/-- Consumer form for a positive reciprocal appearing anywhere in the checked campaign. -/
theorem inv_contains_of_batch {precision : ℕ} (name : String)
    (operations : List (DyadicOperation precision))
    (input output : ChapterVISignedDyadicInterval precision)
    (hoperation : DyadicOperation.positiveReciprocal input output ∈ operations)
    (hadmissible : Admissible (batchClaims operations))
    (hrun : (batchComputation name operations).Returns ((0 : Nat) : Int))
    {value : ℝ} (hvalue : input.Contains value) :
    output.Contains value⁻¹ := by
  have certificate :=
    allSound_of_returns_zero name operations hadmissible hrun
      (.positiveReciprocal input output) hoperation
  exact certificate.contains_inv hvalue

end PoincareChapterVI.ChapterVILeanCompCertBatch
