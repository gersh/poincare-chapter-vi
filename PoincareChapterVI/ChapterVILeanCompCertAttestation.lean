/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import LeanCompCert.Attest
import PoincareChapterVI.ChapterVILeanCompCertBatch

/-!
# Attested compiled artifacts for Chapter VI interval batches

The interval bridge consumes a `Computation.Returns 0` theorem.  Small batches can establish that
theorem by kernel evaluation.  Large connector campaigns instead use LeanCompCert's compiled-run
receipt route.  This file derives the exact C artifact and its self-checking `main` from the same
batch computation used by the mathematical theorem, then transports a hash-bound admitted receipt
back to `Computation.Returns 0`.

No run is admitted here.  `RunAdmission` remains an explicit hypothesis, so downstream axiom
audits identify whether a local signed run or a hardware-attested run discharged it.
-/

namespace PoincareChapterVI.ChapterVILeanCompCertAttestation

open ChapterVILeanCompCertBatch
open LeanCompCert
open LeanCompCert.Attest

/-- The exact straight-line C artifact for one Chapter VI batch.  Both the emitted function name
and the expected zero verdict are derived rather than supplied independently. -/
def batchArtifact {precision : ℕ} (name : String)
    (operations : List (DyadicOperation precision)) : Artifact where
  body := .straightLine (batchComputation name operations)
  mainC := selfCheckMain (ABI.mangle name) 0

@[simp] theorem batchArtifact_route {precision : ℕ} (name : String)
    (operations : List (DyadicOperation precision)) :
    (batchArtifact name operations).route = .provedStraightLine := rfl

@[simp] theorem batchArtifact_covered {precision : ℕ} (name : String)
    (operations : List (DyadicOperation precision)) :
    (batchArtifact name operations).coveredByProvedChain = true := rfl

/-- A receipt bound to the Lean-derived artifact, together with the explicitly named empirical
run premise, yields exactly the zero verdict consumed by the interval checker. -/
theorem returns_zero_of_receipt {precision : ℕ}
    (name : String) (operations : List (DyadicOperation precision))
    (crypto : ReceiptCrypto) (receipt : RunReceipt)
    (kind : AttestationKind) (params nonce : String)
    (bound : receiptBindsProved crypto (batchArtifact name operations) kind params nonce
      ((0 : Nat) : Int) receipt = true)
    (admitted : RunAdmission crypto (batchArtifact name operations) receipt) :
    (batchComputation name operations).Returns ((0 : Nat) : Int) := by
  exact returns_of_receipt_proved bound admitted

end PoincareChapterVI.ChapterVILeanCompCertAttestation
