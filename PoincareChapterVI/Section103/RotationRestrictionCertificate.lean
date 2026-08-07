/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.Section103.AffineEliminationCertificate
import PoincareChapterVI.Section103.RotationRestrictionData

/-! Sparse identities for restricting the three rotation derivatives to the 24-point algebra. -/

namespace PoincareChapterVI.RotationRestrictionCertificate

open AffineEliminationData
open AffineEliminationCertificate
open RotationRestrictionData

def scaleNat (scalar : ℕ) (polynomial : Sparse) : Sparse :=
  polynomial.map fun term => ⟨term.exp, (scalar : QI) * term.coeff⟩

def reducedShapeRight : Sparse :=
  add shapePolynomial (mul reducedShapeQuotient residualPolynomial)

def directionLeft (axis : Fin 3) : Sparse :=
  scaleNat (remainderScale axis) (direction axis)

def directionRight (axis : Fin 3) : Sparse :=
  add (mul (directionShapeQuotient axis) reducedShape)
    (add (mul (directionResidualQuotient axis) residualPolynomial)
      (directionRemainder axis))

def remainderHasNoX (axis : Fin 3) : Bool :=
  (directionRemainder axis).all fun term => term.exp.x == 0

def residualHasNoX : Bool :=
  residualPolynomial.all fun term => term.exp.x == 0

def gaussianToQI (value : GaussianInt) : QI :=
  ⟨value.re, value.im⟩

def directionRemainderCoefficient (axis row : Fin 3) : QI :=
  ((directionRemainder axis).reverse.map Term.coeff).getD row.val 0

private abbrev F53 := ZMod 53

private instance : Fact (Nat.Prime 53) := ⟨by decide⟩

def gaussianMod53 : GaussianInt →+* F53 :=
  Zsqrtd.lift ⟨23, by decide⟩

def modularMinorZMod : Matrix (Fin 3) (Fin 3) F53 := fun row column ↦
  RotationRestrictionData.modularMinor row column

def modularInverseZMod : Matrix (Fin 3) (Fin 3) F53 := fun row column ↦
  RotationRestrictionData.modularInverse row column

private abbrev Vec3QI := Fin 3 → QI
private abbrev Exp3 := Fin 3 → ℕ

def qiI : QI := ⟨0, 1⟩

def secondMajorAxisQI : Vec3QI := ![-2 / 3, 2 / 3, 1 / 3]

def secondMinorAxisQI : Vec3QI := ![2 / 15, -1 / 3, 14 / 15]

def rotationGeneratorQI : Fin 3 → Matrix (Fin 3) (Fin 3) QI :=
  ![!![0, 0, 0; 0, 0, -1; 0, 1, 0],
    !![0, 0, 1; 0, 0, 0; -1, 0, 0],
    !![0, -1, 0; 1, 0, 0; 0, 0, 0]]

def cubicExponentQI : Fin 5 → Exp3 :=
  ![![2, 1, 0], ![1, 2, 0], ![1, 1, 1], ![1, 0, 2], ![0, 1, 2]]

def cubicCoefficientDerivativeQI (axis : Fin 3) : Fin 5 → Vec3QI :=
  let majorDerivative := (rotationGeneratorQI axis).mulVec secondMajorAxisQI
  let minorDerivative := (rotationGeneratorQI axis).mulVec secondMinorAxisQI
  ![fun _ ↦ 0,
    fun coordinate ↦ -2 *
      (majorDerivative coordinate / 2 -
        qiI * (12 / 13 : QI) * minorDerivative coordinate / 2),
    fun coordinate ↦ 2 * (5 / 13 : QI) * majorDerivative coordinate,
    fun coordinate ↦ -2 *
      (majorDerivative coordinate / 2 +
        qiI * (12 / 13 : QI) * minorDerivative coordinate / 2),
    fun _ ↦ 0]

def exponentsAddToQI (left right : Fin 5) (target : Exp3) : Bool :=
  cubicExponentQI left 0 + cubicExponentQI right 0 == target 0 &&
    cubicExponentQI left 1 + cubicExponentQI right 1 == target 1 &&
    cubicExponentQI left 2 + cubicExponentQI right 2 == target 2

def directionalCoefficientQI (target : Exp3) (axis : Fin 3) : QI :=
  2 * ∑ coordinate : Fin 3, ∑ left : Fin 5, ∑ right : Fin 5,
    if exponentsAddToQI left right target then
      Section103Source.cubicCoefficient left coordinate *
        cubicCoefficientDerivativeQI axis right coordinate
    else 0

def sourceDirectionSparse (axis : Fin 3) : Sparse :=
  (List.ofFn fun a : Fin 5 ↦
    List.ofFn fun b : Fin 5 ↦
      ⟨⟨a.val, b.val⟩,
        directionalCoefficientQI ![a.val, b.val, 6 - a.val - b.val] axis⟩).flatten

def scaledSourceDirection (axis : Fin 3) : Sparse :=
  scaleNat directionScale (sourceDirectionSparse axis)

end PoincareChapterVI.RotationRestrictionCertificate
