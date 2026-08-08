/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.ChapterVILeanCompCertBatch

/-!
# Complex signed-dyadic traces for the Chapter VI checker

The sparse outer-arc formula is complex-valued, while the compiled kernel checks signed real
products.  These trace structures reduce complex multiplication and inversion to finite lists of
the primitive operations already handled by the batch checker and prove their rectangular complex
semantics once.
-/

namespace PoincareChapterVI

/-- A complex rectangle whose endpoints share one signed binary scale. -/
structure ChapterVISignedDyadicComplexRectangle (precision : ℕ) where
  real : ChapterVISignedDyadicInterval precision
  imag : ChapterVISignedDyadicInterval precision

namespace ChapterVISignedDyadicComplexRectangle

open ChapterVILeanCompCertBatch
open scoped ComplexConjugate

def Contains {precision : ℕ}
    (rectangle : ChapterVISignedDyadicComplexRectangle precision) (value : ℂ) : Prop :=
  rectangle.real.Contains value.re ∧ rectangle.imag.Contains value.im

/-- A rational `L¹` enclosure turns component rectangles into a dyadic interval containing the
Euclidean complex norm. The budgets are signed integers at the common fixed-point scale, so all
fields are exact kernel-checkable comparisons. -/
structure L1NormBound {precision : ℕ}
    (rectangle : ChapterVISignedDyadicComplexRectangle precision)
    (output : ChapterVISignedDyadicInterval precision) where
  realBudget : ℤ
  imagBudget : ℤ
  realBudget_nonneg : 0 ≤ realBudget
  imagBudget_nonneg : 0 ≤ imagBudget
  real_lower : -realBudget ≤ rectangle.real.lower
  real_upper : rectangle.real.upper ≤ realBudget
  imag_lower : -imagBudget ≤ rectangle.imag.lower
  imag_upper : rectangle.imag.upper ≤ imagBudget
  output_lower_nonpos : output.lower ≤ 0
  budget_le_output : realBudget + imagBudget ≤ output.upper

theorem L1NormBound.contains_norm {precision : ℕ}
    {rectangle : ChapterVISignedDyadicComplexRectangle precision}
    {output : ChapterVISignedDyadicInterval precision}
    (bound : L1NormBound rectangle output)
    {z : ℂ} (hz : rectangle.Contains z) : output.Contains ‖z‖ := by
  have hscale : 0 < ChapterVISignedDyadicInterval.scale precision :=
    ChapterVISignedDyadicInterval.scale_pos precision
  have hreLower : -((bound.realBudget : ℝ) /
      ChapterVISignedDyadicInterval.scale precision) ≤ z.re := by
    apply le_trans _ hz.1.1
    change -((bound.realBudget : ℝ) /
        ChapterVISignedDyadicInterval.scale precision) ≤
      (rectangle.real.lower : ℝ) / ChapterVISignedDyadicInterval.scale precision
    rw [← neg_div]
    exact (div_le_div_iff_of_pos_right hscale).mpr (by exact_mod_cast bound.real_lower)
  have hreUpper : z.re ≤ (bound.realBudget : ℝ) /
      ChapterVISignedDyadicInterval.scale precision := by
    apply hz.1.2.trans
    exact (div_le_div_iff_of_pos_right hscale).mpr (by exact_mod_cast bound.real_upper)
  have himLower : -((bound.imagBudget : ℝ) /
      ChapterVISignedDyadicInterval.scale precision) ≤ z.im := by
    apply le_trans _ hz.2.1
    change -((bound.imagBudget : ℝ) /
        ChapterVISignedDyadicInterval.scale precision) ≤
      (rectangle.imag.lower : ℝ) / ChapterVISignedDyadicInterval.scale precision
    rw [← neg_div]
    exact (div_le_div_iff_of_pos_right hscale).mpr (by exact_mod_cast bound.imag_lower)
  have himUpper : z.im ≤ (bound.imagBudget : ℝ) /
      ChapterVISignedDyadicInterval.scale precision := by
    apply hz.2.2.trans
    exact (div_le_div_iff_of_pos_right hscale).mpr (by exact_mod_cast bound.imag_upper)
  have hreAbs : |z.re| ≤ (bound.realBudget : ℝ) /
      ChapterVISignedDyadicInterval.scale precision :=
    abs_le.mpr ⟨hreLower, hreUpper⟩
  have himAbs : |z.im| ≤ (bound.imagBudget : ℝ) /
      ChapterVISignedDyadicInterval.scale precision :=
    abs_le.mpr ⟨himLower, himUpper⟩
  have hnorm : ‖z‖ ≤ |z.re| + |z.im| := by
    calc
      ‖z‖ = ‖(z.re : ℂ) + (z.im : ℂ) * Complex.I‖ := by
        congr 1
        apply Complex.ext <;> simp
      _ ≤ ‖(z.re : ℂ)‖ + ‖(z.im : ℂ) * Complex.I‖ := norm_add_le _ _
      _ = |z.re| + |z.im| := by simp [Real.norm_eq_abs]
  constructor
  · exact (by
      have : (output.lower : ℝ) ≤ 0 := by exact_mod_cast bound.output_lower_nonpos
      exact (div_nonpos_of_nonpos_of_nonneg this hscale.le).trans (norm_nonneg z))
  · calc
      ‖z‖ ≤ |z.re| + |z.im| := hnorm
      _ ≤ (bound.realBudget : ℝ) /
            ChapterVISignedDyadicInterval.scale precision +
          (bound.imagBudget : ℝ) /
            ChapterVISignedDyadicInterval.scale precision := add_le_add hreAbs himAbs
      _ = ((bound.realBudget + bound.imagBudget : ℤ) : ℝ) /
            ChapterVISignedDyadicInterval.scale precision := by push_cast; ring
      _ ≤ (output.upper : ℝ) / ChapterVISignedDyadicInterval.scale precision :=
        (div_le_div_iff_of_pos_right hscale).mpr (by exact_mod_cast bound.budget_le_output)

noncomputable def toComplexRectangle {precision : ℕ}
    (rectangle : ChapterVISignedDyadicComplexRectangle precision) :
    ChapterVIComplexRectangle :=
  ⟨rectangle.real.toRealInterval, rectangle.imag.toRealInterval⟩

def add {precision : ℕ}
    (x y : ChapterVISignedDyadicComplexRectangle precision) :
    ChapterVISignedDyadicComplexRectangle precision :=
  ⟨x.real.add y.real, x.imag.add y.imag⟩

def neg {precision : ℕ}
    (x : ChapterVISignedDyadicComplexRectangle precision) :
    ChapterVISignedDyadicComplexRectangle precision :=
  ⟨x.real.neg, x.imag.neg⟩

def sub {precision : ℕ}
    (x y : ChapterVISignedDyadicComplexRectangle precision) :
    ChapterVISignedDyadicComplexRectangle precision :=
  x.add y.neg

/-- Exact rectangular complex conjugation at a fixed dyadic scale. -/
def conjugate {precision : ℕ}
    (x : ChapterVISignedDyadicComplexRectangle precision) :
    ChapterVISignedDyadicComplexRectangle precision :=
  ⟨x.real, x.imag.neg⟩

/-- Exact multiplication of both rectangle coordinates by a natural number. -/
def nsmul {precision : ℕ} (n : ℕ)
    (x : ChapterVISignedDyadicComplexRectangle precision) :
    ChapterVISignedDyadicComplexRectangle precision :=
  ⟨⟨n * x.real.lower, n * x.real.upper⟩,
    ⟨n * x.imag.lower, n * x.imag.upper⟩⟩

/-- An exactly represented real integer, viewed as a complex rectangle. -/
def pointInt (precision : ℕ) (value : ℤ) :
    ChapterVISignedDyadicComplexRectangle precision :=
  ⟨ChapterVISignedDyadicInterval.pointInt precision value,
    ChapterVISignedDyadicInterval.pointInt precision 0⟩

/-- Exact dyadic widening by the upper endpoint of a nonnegative error interval. -/
def widenUpper {precision : ℕ}
    (x : ChapterVISignedDyadicComplexRectangle precision)
    (error : ChapterVISignedDyadicInterval precision) :
    ChapterVISignedDyadicComplexRectangle precision :=
  ⟨⟨x.real.lower - error.upper, x.real.upper + error.upper⟩,
    ⟨x.imag.lower - error.upper, x.imag.upper + error.upper⟩⟩

theorem add_contains {precision : ℕ}
    {x y : ChapterVISignedDyadicComplexRectangle precision} {a b : ℂ}
    (ha : x.Contains a) (hb : y.Contains b) :
    (x.add y).Contains (a + b) :=
  ⟨ChapterVISignedDyadicInterval.add_contains ha.1 hb.1,
    ChapterVISignedDyadicInterval.add_contains ha.2 hb.2⟩

theorem neg_contains {precision : ℕ}
    {x : ChapterVISignedDyadicComplexRectangle precision} {a : ℂ}
    (ha : x.Contains a) : x.neg.Contains (-a) :=
  ⟨ChapterVISignedDyadicInterval.neg_contains ha.1,
    ChapterVISignedDyadicInterval.neg_contains ha.2⟩

theorem sub_contains {precision : ℕ}
    {x y : ChapterVISignedDyadicComplexRectangle precision} {a b : ℂ}
    (ha : x.Contains a) (hb : y.Contains b) :
    (x.sub y).Contains (a - b) := by
  simpa [sub, sub_eq_add_neg] using add_contains ha (neg_contains hb)

theorem conjugate_contains {precision : ℕ}
    {x : ChapterVISignedDyadicComplexRectangle precision} {a : ℂ}
    (ha : x.Contains a) : x.conjugate.Contains (conj a) := by
  constructor
  · simpa [conjugate] using ha.1
  · simpa [conjugate] using ChapterVISignedDyadicInterval.neg_contains ha.2

theorem conjugate_contains_inv_of_norm_one {precision : ℕ}
    {x : ChapterVISignedDyadicComplexRectangle precision} {a : ℂ}
    (ha : x.Contains a) (hnorm : ‖a‖ = 1) : x.conjugate.Contains a⁻¹ := by
  rw [Complex.inv_eq_conj hnorm]
  exact conjugate_contains ha

theorem nsmul_contains {precision : ℕ} (n : ℕ)
    {x : ChapterVISignedDyadicComplexRectangle precision} {a : ℂ}
    (ha : x.Contains a) : (x.nsmul n).Contains (n * a) := by
  constructor
  · change ((n : ℤ) * x.real.lower : ℤ) / ChapterVISignedDyadicInterval.scale precision ≤
      (n * a).re ∧
      (n * a).re ≤
        ((n : ℤ) * x.real.upper : ℤ) / ChapterVISignedDyadicInterval.scale precision
    simpa [Complex.mul_re, ChapterVISignedDyadicInterval.Contains,
      ChapterVISignedDyadicInterval.toRealInterval, nsmul,
      div_eq_mul_inv, mul_assoc] using
      ⟨mul_le_mul_of_nonneg_left ha.1.1 (Nat.cast_nonneg n),
        mul_le_mul_of_nonneg_left ha.1.2 (Nat.cast_nonneg n)⟩
  · change ((n : ℤ) * x.imag.lower : ℤ) / ChapterVISignedDyadicInterval.scale precision ≤
      (n * a).im ∧
      (n * a).im ≤
        ((n : ℤ) * x.imag.upper : ℤ) / ChapterVISignedDyadicInterval.scale precision
    simpa [Complex.mul_im, ChapterVISignedDyadicInterval.Contains,
      ChapterVISignedDyadicInterval.toRealInterval, nsmul,
      div_eq_mul_inv, mul_assoc] using
      ⟨mul_le_mul_of_nonneg_left ha.2.1 (Nat.cast_nonneg n),
        mul_le_mul_of_nonneg_left ha.2.2 (Nat.cast_nonneg n)⟩

theorem pointInt_contains (precision : ℕ) (value : ℤ) :
    (pointInt precision value).Contains (value : ℂ) := by
  constructor
  · simpa [pointInt] using ChapterVISignedDyadicInterval.pointInt_contains precision value
  · simpa [pointInt] using ChapterVISignedDyadicInterval.pointInt_contains precision 0

theorem widenUpper_contains_of_norm_sub_le {precision : ℕ}
    {x : ChapterVISignedDyadicComplexRectangle precision}
    {error : ChapterVISignedDyadicInterval precision} {approximation value : ℂ}
    (happroximation : x.Contains approximation)
    (herror : ‖value - approximation‖ ≤
      (error.upper : ℝ) / ChapterVISignedDyadicInterval.scale precision) :
    (x.widenUpper error).Contains value := by
  have hwiden := ChapterVIComplexRectangle.widen_contains_of_norm_sub_le
    (rectangle := x.toComplexRectangle) happroximation herror
  constructor <;> constructor
  · change ((x.real.lower - error.upper : ℤ) : ℝ) /
      ChapterVISignedDyadicInterval.scale precision ≤ value.re
    convert hwiden.1.1 using 1 <;>
      simp only [toComplexRectangle, ChapterVIComplexRectangle.widen,
        ChapterVISignedDyadicInterval.toRealInterval] <;> push_cast <;> ring
  · change value.re ≤ ((x.real.upper + error.upper : ℤ) : ℝ) /
      ChapterVISignedDyadicInterval.scale precision
    convert hwiden.1.2 using 1 <;>
      simp only [toComplexRectangle, ChapterVIComplexRectangle.widen,
        ChapterVISignedDyadicInterval.toRealInterval] <;> push_cast <;> ring
  · change ((x.imag.lower - error.upper : ℤ) : ℝ) /
      ChapterVISignedDyadicInterval.scale precision ≤ value.im
    convert hwiden.2.1 using 1 <;>
      simp only [toComplexRectangle, ChapterVIComplexRectangle.widen,
        ChapterVISignedDyadicInterval.toRealInterval] <;> push_cast <;> ring
  · change value.im ≤ ((x.imag.upper + error.upper : ℤ) : ℝ) /
      ChapterVISignedDyadicInterval.scale precision
    convert hwiden.2.2 using 1 <;>
      simp only [toComplexRectangle, ChapterVIComplexRectangle.widen,
        ChapterVISignedDyadicInterval.toRealInterval] <;> push_cast <;> ring

/-- Two rounded real products scale a complex rectangle by a real interval. -/
structure RealMulTrace {precision : ℕ}
    (scalar : ChapterVISignedDyadicInterval precision)
    (input : ChapterVISignedDyadicComplexRectangle precision) where
  realOut : ChapterVISignedDyadicInterval precision
  imagOut : ChapterVISignedDyadicInterval precision

def RealMulTrace.operations {precision : ℕ}
    {scalar : ChapterVISignedDyadicInterval precision}
    {input : ChapterVISignedDyadicComplexRectangle precision}
    (trace : RealMulTrace scalar input) : List (DyadicOperation precision) :=
  [ .mul scalar input.real trace.realOut
  , .mul scalar input.imag trace.imagOut ]

def RealMulTrace.output {precision : ℕ}
    {scalar : ChapterVISignedDyadicInterval precision}
    {input : ChapterVISignedDyadicComplexRectangle precision}
    (trace : RealMulTrace scalar input) :
    ChapterVISignedDyadicComplexRectangle precision :=
  ⟨trace.realOut, trace.imagOut⟩

theorem RealMulTrace.output_contains_of_allSound {precision : ℕ}
    {scalar : ChapterVISignedDyadicInterval precision}
    {input : ChapterVISignedDyadicComplexRectangle precision}
    (trace : RealMulTrace scalar input)
    (hall : ∀ operation ∈ trace.operations, operation.Sound)
    {r : ℝ} {z : ℂ} (hr : scalar.Contains r) (hz : input.Contains z) :
    trace.output.Contains ((r : ℂ) * z) := by
  have hre : ChapterVISignedDyadicInterval.MulCertificate
      scalar input.real trace.realOut :=
    hall (.mul scalar input.real trace.realOut) (by simp [RealMulTrace.operations])
  have him : ChapterVISignedDyadicInterval.MulCertificate
      scalar input.imag trace.imagOut :=
    hall (.mul scalar input.imag trace.imagOut) (by simp [RealMulTrace.operations])
  constructor
  · simpa [RealMulTrace.output] using hre.contains_mul hr hz.1
  · simpa [RealMulTrace.output] using him.contains_mul hr hz.2

/-- Four real rounded products implementing one complex multiplication. -/
structure MulTrace {precision : ℕ}
    (x y : ChapterVISignedDyadicComplexRectangle precision) where
  realReal : ChapterVISignedDyadicInterval precision
  imagImag : ChapterVISignedDyadicInterval precision
  realImag : ChapterVISignedDyadicInterval precision
  imagReal : ChapterVISignedDyadicInterval precision

def MulTrace.operations {precision : ℕ}
    {x y : ChapterVISignedDyadicComplexRectangle precision}
    (trace : MulTrace x y) : List (DyadicOperation precision) :=
  [ .mul x.real y.real trace.realReal
  , .mul x.imag y.imag trace.imagImag
  , .mul x.real y.imag trace.realImag
  , .mul x.imag y.real trace.imagReal ]

def MulTrace.output {precision : ℕ}
    {x y : ChapterVISignedDyadicComplexRectangle precision}
    (trace : MulTrace x y) : ChapterVISignedDyadicComplexRectangle precision :=
  ⟨trace.realReal.sub trace.imagImag,
    trace.realImag.add trace.imagReal⟩

theorem MulTrace.output_contains_mul_of_allSound {precision : ℕ}
    {x y : ChapterVISignedDyadicComplexRectangle precision}
    (trace : MulTrace x y)
    (hall : ∀ operation ∈ trace.operations, operation.Sound)
    {a b : ℂ} (ha : x.Contains a) (hb : y.Contains b) :
    trace.output.Contains (a * b) := by
  have hrr : ChapterVISignedDyadicInterval.MulCertificate
      x.real y.real trace.realReal :=
    hall (.mul x.real y.real trace.realReal) (by simp [MulTrace.operations])
  have hii : ChapterVISignedDyadicInterval.MulCertificate
      x.imag y.imag trace.imagImag :=
    hall (.mul x.imag y.imag trace.imagImag) (by simp [MulTrace.operations])
  have hri : ChapterVISignedDyadicInterval.MulCertificate
      x.real y.imag trace.realImag :=
    hall (.mul x.real y.imag trace.realImag) (by simp [MulTrace.operations])
  have hir : ChapterVISignedDyadicInterval.MulCertificate
      x.imag y.real trace.imagReal :=
    hall (.mul x.imag y.real trace.imagReal) (by simp [MulTrace.operations])
  have hrrValue := hrr.contains_mul ha.1 hb.1
  have hiiValue := hii.contains_mul ha.2 hb.2
  have hriValue := hri.contains_mul ha.1 hb.2
  have hirValue := hir.contains_mul ha.2 hb.1
  constructor
  · simpa [MulTrace.output, ChapterVISignedDyadicInterval.sub,
      ChapterVISignedDyadicInterval.neg, ChapterVISignedDyadicInterval.add,
      Complex.mul_re, sub_eq_add_neg] using ChapterVISignedDyadicInterval.add_contains
        hrrValue (ChapterVISignedDyadicInterval.neg_contains hiiValue)
  · simpa [MulTrace.output, Complex.mul_im] using
      ChapterVISignedDyadicInterval.add_contains hriValue hirValue

theorem MulTrace.output_contains_mul_of_batch {precision : ℕ}
    {x y : ChapterVISignedDyadicComplexRectangle precision}
    (trace : MulTrace x y) (name : String)
    (operations : List (DyadicOperation precision))
    (hoperations : ∀ operation ∈ trace.operations, operation ∈ operations)
    (hadmissible : LeanCompCert.Ports.SignedProductClaims.Admissible
      (batchClaims operations))
    (hrun : (batchComputation name operations).Returns ((0 : Nat) : Int))
    {a b : ℂ} (ha : x.Contains a) (hb : y.Contains b) :
    trace.output.Contains (a * b) := by
  apply trace.output_contains_mul_of_allSound
  · intro operation hoperation
    exact allSound_of_returns_zero name operations hadmissible hrun operation
      (hoperations operation hoperation)
  · exact ha
  · exact hb

/-- Two complex multiplication traces computing a cube. -/
structure CubeTrace {precision : ℕ}
    (input : ChapterVISignedDyadicComplexRectangle precision) where
  square : MulTrace input input
  cube : MulTrace square.output input

def CubeTrace.operations {precision : ℕ}
    {input : ChapterVISignedDyadicComplexRectangle precision}
    (trace : CubeTrace input) : List (DyadicOperation precision) :=
  trace.square.operations ++ trace.cube.operations

def CubeTrace.output {precision : ℕ}
    {input : ChapterVISignedDyadicComplexRectangle precision}
    (trace : CubeTrace input) : ChapterVISignedDyadicComplexRectangle precision :=
  trace.cube.output

theorem CubeTrace.output_contains_cube_of_allSound {precision : ℕ}
    {input : ChapterVISignedDyadicComplexRectangle precision}
    (trace : CubeTrace input)
    (hall : ∀ operation ∈ trace.operations, operation.Sound)
    {value : ℂ} (hvalue : input.Contains value) :
    trace.output.Contains (value ^ 3) := by
  have hsquareSound : ∀ operation ∈ trace.square.operations, operation.Sound := by
    intro operation hoperation
    exact hall operation (by simp [CubeTrace.operations, hoperation])
  have hcubeSound : ∀ operation ∈ trace.cube.operations, operation.Sound := by
    intro operation hoperation
    exact hall operation (by simp [CubeTrace.operations, hoperation])
  have hsquare := trace.square.output_contains_mul_of_allSound
    hsquareSound hvalue hvalue
  have hcube := trace.cube.output_contains_mul_of_allSound hcubeSound hsquare hvalue
  simpa [CubeTrace.output, pow_succ, pow_two, mul_assoc] using hcube

/-- Five primitive operations implementing complex inversion through
`conj(z) / (re(z)^2 + im(z)^2)`. -/
structure InvTrace {precision : ℕ}
    (input : ChapterVISignedDyadicComplexRectangle precision) where
  realSq : ChapterVISignedDyadicInterval precision
  imagSq : ChapterVISignedDyadicInterval precision
  normInv : ChapterVISignedDyadicInterval precision
  realOut : ChapterVISignedDyadicInterval precision
  imagOut : ChapterVISignedDyadicInterval precision

def InvTrace.normSq {precision : ℕ}
    {input : ChapterVISignedDyadicComplexRectangle precision}
    (trace : InvTrace input) : ChapterVISignedDyadicInterval precision :=
  trace.realSq.add trace.imagSq

def InvTrace.operations {precision : ℕ}
    {input : ChapterVISignedDyadicComplexRectangle precision}
    (trace : InvTrace input) : List (DyadicOperation precision) :=
  [ .mul input.real input.real trace.realSq
  , .mul input.imag input.imag trace.imagSq
  , .positiveReciprocal trace.normSq trace.normInv
  , .mul input.real trace.normInv trace.realOut
  , .mul input.imag.neg trace.normInv trace.imagOut ]

def InvTrace.output {precision : ℕ}
    {input : ChapterVISignedDyadicComplexRectangle precision}
    (trace : InvTrace input) : ChapterVISignedDyadicComplexRectangle precision :=
  ⟨trace.realOut, trace.imagOut⟩

theorem InvTrace.output_contains_inv_of_allSound {precision : ℕ}
    {input : ChapterVISignedDyadicComplexRectangle precision}
    (trace : InvTrace input)
    (hall : ∀ operation ∈ trace.operations, operation.Sound)
    {value : ℂ} (hvalue : input.Contains value) :
    trace.output.Contains value⁻¹ := by
  have hreSq : ChapterVISignedDyadicInterval.MulCertificate
      input.real input.real trace.realSq :=
    hall (.mul input.real input.real trace.realSq) (by simp [InvTrace.operations])
  have himSq : ChapterVISignedDyadicInterval.MulCertificate
      input.imag input.imag trace.imagSq :=
    hall (.mul input.imag input.imag trace.imagSq) (by simp [InvTrace.operations])
  have hrecip : ChapterVISignedDyadicInterval.PositiveReciprocalCertificate
      trace.normSq trace.normInv :=
    hall (.positiveReciprocal trace.normSq trace.normInv) (by simp [InvTrace.operations])
  have hreOut : ChapterVISignedDyadicInterval.MulCertificate
      input.real trace.normInv trace.realOut :=
    hall (.mul input.real trace.normInv trace.realOut) (by simp [InvTrace.operations])
  have himOut : ChapterVISignedDyadicInterval.MulCertificate
      input.imag.neg trace.normInv trace.imagOut :=
    hall (.mul input.imag.neg trace.normInv trace.imagOut)
      (by simp [InvTrace.operations])
  have hreSqValue := hreSq.contains_mul hvalue.1 hvalue.1
  have himSqValue := himSq.contains_mul hvalue.2 hvalue.2
  have hnormSq : trace.normSq.Contains (Complex.normSq value) := by
    rw [Complex.normSq_apply]
    exact ChapterVISignedDyadicInterval.add_contains hreSqValue himSqValue
  have hnormInv := hrecip.contains_inv hnormSq
  have hreValue := hreOut.contains_mul hvalue.1 hnormInv
  have himValue := himOut.contains_mul
    (ChapterVISignedDyadicInterval.neg_contains hvalue.2) hnormInv
  change trace.realOut.Contains value⁻¹.re ∧ trace.imagOut.Contains value⁻¹.im
  constructor
  · rw [Complex.inv_re, div_eq_mul_inv]
    exact hreValue
  · rw [Complex.inv_im, div_eq_mul_inv]
    exact himValue

theorem InvTrace.output_contains_inv_of_batch {precision : ℕ}
    {input : ChapterVISignedDyadicComplexRectangle precision}
    (trace : InvTrace input) (name : String)
    (operations : List (DyadicOperation precision))
    (hoperations : ∀ operation ∈ trace.operations, operation ∈ operations)
    (hadmissible : LeanCompCert.Ports.SignedProductClaims.Admissible
      (batchClaims operations))
    (hrun : (batchComputation name operations).Returns ((0 : Nat) : Int))
    {value : ℂ} (hvalue : input.Contains value) :
    trace.output.Contains value⁻¹ := by
  apply trace.output_contains_inv_of_allSound
  · intro operation hoperation
    exact allSound_of_returns_zero name operations hadmissible hrun operation
      (hoperations operation hoperation)
  · exact hvalue

end ChapterVISignedDyadicComplexRectangle

end PoincareChapterVI
