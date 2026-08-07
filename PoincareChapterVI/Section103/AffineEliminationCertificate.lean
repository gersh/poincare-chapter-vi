/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import LeanCompCert.Verified.Decide
import PoincareChapterVI.Section103.AffineEliminationData
import Std.Data.TreeMap

/-!
# Exact affine-elimination certificate for Section 103

The sparse checker verifies that the two cleared affine source curves generate the lexicographic
shape basis `x + h(y), y² q(y)`.  It is deliberately independent of the SymPy generator.
-/

namespace PoincareChapterVI.AffineEliminationCertificate

open AffineEliminationData

def add (left right : Sparse) : Sparse := left ++ right

def mulExp (left right : Exp) : Exp :=
  ⟨left.x + right.x, left.y + right.y⟩

def mul (left right : Sparse) : Sparse :=
  left.flatMap fun leftTerm => right.map fun rightTerm =>
    ⟨mulExp leftTerm.exp rightTerm.exp, leftTerm.coeff * rightTerm.coeff⟩

def coefficient : Sparse → Exp → QI
  | [], _ => 0
  | term :: terms, exponent =>
      (if term.exp = exponent then term.coeff else 0) + coefficient terms exponent

def expKey (exponent : Exp) : ℕ := Nat.pair exponent.x exponent.y

def insertTerm (terms : Std.TreeMap ℕ QI) (term : Term) : Std.TreeMap ℕ QI :=
  terms.alter (expKey term.exp) fun previous =>
    let value := previous.getD 0 + term.coeff
    if value = 0 then none else some value

def accumulate : Sparse → Std.TreeMap ℕ QI → Std.TreeMap ℕ QI
  | [], terms => terms
  | term :: rest, terms => accumulate rest (insertTerm terms term)

def normalMap (polynomial : Sparse) : Std.TreeMap ℕ QI := accumulate polynomial {}

def variableX : Sparse := [⟨⟨1, 0⟩, 1⟩]

def variableYSquared : Sparse := [⟨⟨0, 2⟩, 1⟩]

def shapeFromTail : Sparse := add variableX shapeTail

def eliminantFromResidual : Sparse := mul variableYSquared residualPolynomial

def shapeMembershipLeft : Sparse :=
  add (mul shapeLeft affineSextic) (mul shapeRight affineSeptic)

def eliminantMembershipLeft : Sparse :=
  add (mul eliminantLeft affineSextic) (mul eliminantRight affineSeptic)

def sexticReconstructionLeft : Sparse :=
  add (mul sexticQuotientShape shapePolynomial)
    (mul sexticQuotientEliminant eliminant)

def septicReconstructionLeft : Sparse :=
  add (mul septicQuotientShape shapePolynomial)
    (mul septicQuotientEliminant eliminant)

end PoincareChapterVI.AffineEliminationCertificate
