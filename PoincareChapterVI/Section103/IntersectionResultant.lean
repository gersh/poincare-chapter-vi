/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import LeanCompCert.Verified.Decide
import PoincareChapterVI.Section103.LocalIntersection

/-!
# Finite Sylvester certificates at the two points at infinity

The two local chart pairs in `LocalIntersection` have degree four in the coordinate eliminated
by Poincaré's resultants.  This file constructs their `8 × 8` Sylvester matrices over sparse
Gaussian polynomials in the remaining coordinate.  A 256-state subset determinant avoids the
factorial duplication of a Laplace expansion.  LeanCompCert verifies that coefficients below
degree eight vanish and that the degree-eight coefficient is nonzero in both charts.

The sparse operations discard terms above degree eight; this is sound for the reported low
coefficients because exponents are nonnegative.  The generic semantic bridge identifying the
subset determinant with `Polynomial.resultant` remains a separate local-algebra infrastructure
task.  Accordingly, the theorems below are named as finite Sylvester certificates rather than
as completed local intersection-multiplicity theorems.
-/

namespace PoincareChapterVI.Section103Resultant

open PoincareChapterVI.Section103Source

abbrev QI := PoincareChapterVI.Section103Source.QI

structure ZTerm where
  exp : Nat
  coeff : QI
deriving DecidableEq

abbrev ZSparse := List ZTerm

def zmonomial (n : Nat) (q : QI) : ZSparse :=
  if q = 0 then [] else [⟨n, q⟩]

def zconstant (q : QI) : ZSparse := zmonomial 0 q
def zneg (p : ZSparse) : ZSparse := p.map fun t => ⟨t.exp, -t.coeff⟩
def zadd (p q : ZSparse) : ZSparse := p ++ q

def zmul (p q : ZSparse) : ZSparse :=
  p.flatMap fun s ↦ q.filterMap fun t ↦
    if s.exp + t.exp ≤ 8 then
      let c := s.coeff * t.coeff
      if c = 0 then none else some ⟨s.exp + t.exp, c⟩
    else none

def zsum (p : List ZSparse) : ZSparse := p.flatten
def zproduct (p : List ZSparse) : ZSparse := p.foldl zmul (zconstant 1)

def zcoefficient : ZSparse → Nat → QI
  | [], _ => 0
  | t :: p, n => (if t.exp = n then t.coeff else 0) + zcoefficient p n

def sexticCoefficient : Fin 5 → Fin 5 → QI :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨4563, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩],
    ![⟨0, 0⟩, ⟨21320, -33280⟩, ⟨-56420, 20800⟩,
      ⟨46280, -20800⟩, ⟨0, 0⟩],
    ![⟨7500, 0⟩, ⟨-118560, 7488⟩, ⟨308826, 0⟩,
      ⟨-118560, -7488⟩, ⟨7500, 0⟩],
    ![⟨0, 0⟩, ⟨46280, 20800⟩, ⟨-56420, -20800⟩,
      ⟨21320, 33280⟩, ⟨0, 0⟩],
    ![⟨0, 0⟩, ⟨0, 0⟩, ⟨4563, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

def xSexticCoefficient (b : Fin 5) : ZSparse :=
  zsum (List.ofFn fun a : Fin 5 ↦
    zmonomial (6 - a.val - b.val) (sexticCoefficient a b))

def xReducedCoefficient (b : Fin 5) : ZSparse :=
  zsum (List.ofFn fun a : Fin 5 ↦
    zmonomial (7 - a.val - b.val) (reducedCoefficient a b))

def ySexticCoefficient (a : Fin 5) : ZSparse :=
  zsum (List.ofFn fun b : Fin 5 ↦
    zmonomial (6 - a.val - b.val) (sexticCoefficient a b))

def yReducedCoefficient (a : Fin 5) : ZSparse :=
  zsum (List.ofFn fun b : Fin 5 ↦
    zmonomial (7 - a.val - b.val) (reducedCoefficient a b))

abbrev Eight := Fin 8

def coeffAt (p : Fin 5 → ZSparse) (n : Nat) : ZSparse :=
  if h : n < 5 then p ⟨n, h⟩ else []

def sylvester (p q : Fin 5 → ZSparse) : Eight → Eight → ZSparse := fun i j ↦
  if _hj : j.val < 4 then
    if j.val ≤ i.val ∧ i.val ≤ j.val + 4 then coeffAt q (i.val - j.val) else []
  else
    let k := j.val - 4
    if k ≤ i.val ∧ i.val ≤ k + 4 then coeffAt p (i.val - k) else []

def columns : List Eight := List.ofFn id

def bitSet (mask : Nat) (j : Eight) : Bool :=
  (mask / 2 ^ j.val) % 2 = 1

def bitCount (mask : Nat) : Nat :=
  columns.foldl (fun count j ↦ if bitSet mask j then count + 1 else count) 0

def greaterBitCount (mask : Nat) (j : Eight) : Nat :=
  columns.foldl
    (fun count k ↦ if j.val < k.val && bitSet mask k then count + 1 else count) 0

def determinantStep (M : Eight → Eight → ZSparse) (mask : Nat)
    (hk : bitCount mask < 8) (values : Array ZSparse) (j : Eight) : Array ZSparse :=
  if bitSet mask j then values
  else
    let next := mask + 2 ^ j.val
    let term := zmul (values.getD mask []) (M ⟨bitCount mask, hk⟩ j)
    let signed := if greaterBitCount mask j % 2 = 0 then term else zneg term
    values.set! next (zadd (values.getD next []) signed)

def determinant (M : Eight → Eight → ZSparse) : ZSparse :=
  let initial := (Array.replicate 256 ([] : ZSparse)).set! 0 (zconstant 1)
  let values := (List.range 256).foldl (fun values mask ↦
    if hk : bitCount mask < 8 then
      columns.foldl (determinantStep M mask hk) values
    else values) initial
  values.getD 255 []

def xResultant : ZSparse := determinant (sylvester xSexticCoefficient xReducedCoefficient)
def yResultant : ZSparse := determinant (sylvester ySexticCoefficient yReducedCoefficient)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
theorem chapterVI_xInfinitySylvester_coeff_below_eight :
    ∀ n : Fin 8, zcoefficient xResultant n.val = 0 := by
  verified_decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
theorem chapterVI_xInfinitySylvester_coeff_eight : zcoefficient xResultant 8 =
    ⟨4818158998095220357263684627656250000,
      10850659278679505837928529530000000000⟩ := by
  verified_decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
theorem chapterVI_yInfinitySylvester_coeff_below_eight :
    ∀ n : Fin 8, zcoefficient yResultant n.val = 0 := by
  verified_decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
theorem chapterVI_yInfinitySylvester_coeff_eight : zcoefficient yResultant 8 =
    ⟨-4598471310720574147795898437500000000,
      -31742888552352893718562500000000000000⟩ := by
  verified_decide

end PoincareChapterVI.Section103Resultant
