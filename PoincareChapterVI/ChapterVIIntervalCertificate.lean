/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import Mathlib

/-!
# Certificate semantics for the compiled Chapter VI interval sweep

The outer-arc computation is intentionally certificate-driven.  A compiled program checks
integer inequalities describing interval operations; Lean only proves once that those finite
comparisons have the advertised real and complex meaning.

This file is independent of a particular fixed-point encoding.  The later LeanCompCert bridge
maps signed dyadic endpoints and its checked comparisons into these predicates.
-/

namespace PoincareChapterVI

/-- A closed real interval.  Well-formedness is kept explicit so a compiled certificate must
also check that an alleged output interval is nonempty. -/
structure ChapterVIRealInterval where
  lower : ℝ
  upper : ℝ

namespace ChapterVIRealInterval

def WF (x : ChapterVIRealInterval) : Prop := x.lower ≤ x.upper

def Contains (x : ChapterVIRealInterval) (value : ℝ) : Prop :=
  x.lower ≤ value ∧ value ≤ x.upper

def point (value : ℝ) : ChapterVIRealInterval := ⟨value, value⟩

def add (x y : ChapterVIRealInterval) : ChapterVIRealInterval :=
  ⟨x.lower + y.lower, x.upper + y.upper⟩

def neg (x : ChapterVIRealInterval) : ChapterVIRealInterval :=
  ⟨-x.upper, -x.lower⟩

def sub (x y : ChapterVIRealInterval) : ChapterVIRealInterval :=
  x.add y.neg

theorem point_contains (value : ℝ) : (point value).Contains value :=
  ⟨le_rfl, le_rfl⟩

theorem add_contains {x y : ChapterVIRealInterval} {a b : ℝ}
    (ha : x.Contains a) (hb : y.Contains b) :
    (x.add y).Contains (a + b) :=
  ⟨add_le_add ha.1 hb.1, add_le_add ha.2 hb.2⟩

theorem neg_contains {x : ChapterVIRealInterval} {a : ℝ}
    (ha : x.Contains a) : x.neg.Contains (-a) :=
  ⟨neg_le_neg ha.2, neg_le_neg ha.1⟩

theorem sub_contains {x y : ChapterVIRealInterval} {a b : ℝ}
    (ha : x.Contains a) (hb : y.Contains b) :
    (x.sub y).Contains (a - b) := by
  simpa [sub, sub_eq_add_neg] using add_contains ha (neg_contains hb)

/-- The certificate for a product interval consists solely of comparisons against the four
corner products.  This is convenient for a signed fixed-point checker: no sign branch appears
in the certificate format. -/
structure MulCertificate
    (x y output : ChapterVIRealInterval) : Prop where
  output_wf : output.WF
  lower_ll : output.lower ≤ x.lower * y.lower
  lower_lu : output.lower ≤ x.lower * y.upper
  lower_ul : output.lower ≤ x.upper * y.lower
  lower_uu : output.lower ≤ x.upper * y.upper
  upper_ll : x.lower * y.lower ≤ output.upper
  upper_lu : x.lower * y.upper ≤ output.upper
  upper_ul : x.upper * y.lower ≤ output.upper
  upper_uu : x.upper * y.upper ≤ output.upper

private theorem lower_mul_of_corner_bounds
    {xl xh yl yh a b lower : ℝ}
    (ha : xl ≤ a ∧ a ≤ xh) (hb : yl ≤ b ∧ b ≤ yh)
    (hll : lower ≤ xl * yl) (hlu : lower ≤ xl * yh)
    (hul : lower ≤ xh * yl) (huu : lower ≤ xh * yh) :
    lower ≤ a * b := by
  rcases le_total 0 b with hb0 | hb0
  · have hxb : xl * b ≤ a * b := mul_le_mul_of_nonneg_right ha.1 hb0
    have hlower : lower ≤ xl * b := by
      rcases le_total 0 xl with hxl | hxl
      · exact hll.trans (mul_le_mul_of_nonneg_left hb.1 hxl)
      · exact hlu.trans (mul_le_mul_of_nonpos_left hb.2 hxl)
    exact hlower.trans hxb
  · have hxb : xh * b ≤ a * b := mul_le_mul_of_nonpos_right ha.2 hb0
    have hlower : lower ≤ xh * b := by
      rcases le_total 0 xh with hxh | hxh
      · exact hul.trans (mul_le_mul_of_nonneg_left hb.1 hxh)
      · exact huu.trans (mul_le_mul_of_nonpos_left hb.2 hxh)
    exact hlower.trans hxb

private theorem upper_mul_of_corner_bounds
    {xl xh yl yh a b upper : ℝ}
    (ha : xl ≤ a ∧ a ≤ xh) (hb : yl ≤ b ∧ b ≤ yh)
    (hll : xl * yl ≤ upper) (hlu : xl * yh ≤ upper)
    (hul : xh * yl ≤ upper) (huu : xh * yh ≤ upper) :
    a * b ≤ upper := by
  rcases le_total 0 b with hb0 | hb0
  · have hxb : a * b ≤ xh * b := mul_le_mul_of_nonneg_right ha.2 hb0
    exact hxb.trans (by
      rcases le_total 0 xh with hxh | hxh
      · exact (mul_le_mul_of_nonneg_left hb.2 hxh).trans huu
      · exact (mul_le_mul_of_nonpos_left hb.1 hxh).trans hul)
  · have hxb : a * b ≤ xl * b := mul_le_mul_of_nonpos_right ha.1 hb0
    exact hxb.trans (by
      rcases le_total 0 xl with hxl | hxl
      · exact (mul_le_mul_of_nonneg_left hb.2 hxl).trans hlu
      · exact (mul_le_mul_of_nonpos_left hb.1 hxl).trans hll)

theorem MulCertificate.contains_mul
    {x y output : ChapterVIRealInterval} (certificate : MulCertificate x y output)
    {a b : ℝ} (ha : x.Contains a) (hb : y.Contains b) :
    output.Contains (a * b) :=
  ⟨lower_mul_of_corner_bounds ha hb certificate.lower_ll certificate.lower_lu
      certificate.lower_ul certificate.lower_uu,
    upper_mul_of_corner_bounds ha hb certificate.upper_ll certificate.upper_lu
      certificate.upper_ul certificate.upper_uu⟩

/-- Certificate for the reciprocal of a strictly positive interval.  Both inequalities are
cross-multiplied, exactly as they will be checked over signed dyadic integers. -/
structure PositiveReciprocalCertificate
    (input output : ChapterVIRealInterval) : Prop where
  input_lower_pos : 0 < input.lower
  output_wf : output.WF
  output_lower_nonneg : 0 ≤ output.lower
  lower_cross : output.lower * input.upper ≤ 1
  upper_cross : 1 ≤ output.upper * input.lower

theorem PositiveReciprocalCertificate.contains_inv
    {input output : ChapterVIRealInterval}
    (certificate : PositiveReciprocalCertificate input output)
    {value : ℝ} (hvalue : input.Contains value) :
    output.Contains value⁻¹ := by
  have hvaluePos := certificate.input_lower_pos.trans_le hvalue.1
  have houtputUpper : 0 ≤ output.upper := by
    by_contra hnegative
    have hproduct : output.upper * input.lower < 0 :=
      mul_neg_of_neg_of_pos (lt_of_not_ge hnegative) certificate.input_lower_pos
    exact (not_lt_of_ge certificate.upper_cross) (hproduct.trans zero_lt_one)
  constructor
  · rw [← one_div]
    rw [le_div_iff₀ hvaluePos]
    exact (mul_le_mul_of_nonneg_left hvalue.2 certificate.output_lower_nonneg).trans
      certificate.lower_cross
  · rw [inv_le_iff_one_le_mul₀ hvaluePos]
    exact certificate.upper_cross.trans
      (mul_le_mul_of_nonneg_left hvalue.1 houtputUpper)

end ChapterVIRealInterval

/-! ## Signed dyadic encoding checked by LeanCompCert -/

/-- Fixed-point endpoints at scale `2^precision`.  These are mathematical integers here; the
compiled program represents them by LeanCompCert's proved sign-magnitude limb layer. -/
structure ChapterVISignedDyadicInterval (precision : ℕ) where
  lower : ℤ
  upper : ℤ

namespace ChapterVISignedDyadicInterval

noncomputable section

def scale (precision : ℕ) : ℝ := (2 : ℝ) ^ precision

theorem scale_pos (precision : ℕ) : 0 < scale precision := by
  unfold scale
  positivity

def toRealInterval {precision : ℕ}
    (x : ChapterVISignedDyadicInterval precision) : ChapterVIRealInterval where
  lower := (x.lower : ℝ) / scale precision
  upper := (x.upper : ℝ) / scale precision

def Contains {precision : ℕ}
    (x : ChapterVISignedDyadicInterval precision) (value : ℝ) : Prop :=
  x.toRealInterval.Contains value

def add {precision : ℕ}
    (x y : ChapterVISignedDyadicInterval precision) :
    ChapterVISignedDyadicInterval precision :=
  ⟨x.lower + y.lower, x.upper + y.upper⟩

theorem add_contains {precision : ℕ}
    {x y : ChapterVISignedDyadicInterval precision} {a b : ℝ}
    (ha : x.Contains a) (hb : y.Contains b) :
    (x.add y).Contains (a + b) := by
  simpa [Contains, toRealInterval, add, ChapterVIRealInterval.add, scale,
    add_div] using ChapterVIRealInterval.add_contains ha hb

/-- The exact integer comparisons checked for an outward-rounded signed dyadic product. -/
structure MulCertificate {precision : ℕ}
    (x y output : ChapterVISignedDyadicInterval precision) : Prop where
  output_wf : output.lower ≤ output.upper
  lower_ll : output.lower * (2 ^ precision : ℤ) ≤ x.lower * y.lower
  lower_lu : output.lower * (2 ^ precision : ℤ) ≤ x.lower * y.upper
  lower_ul : output.lower * (2 ^ precision : ℤ) ≤ x.upper * y.lower
  lower_uu : output.lower * (2 ^ precision : ℤ) ≤ x.upper * y.upper
  upper_ll : x.lower * y.lower ≤ output.upper * (2 ^ precision : ℤ)
  upper_lu : x.lower * y.upper ≤ output.upper * (2 ^ precision : ℤ)
  upper_ul : x.upper * y.lower ≤ output.upper * (2 ^ precision : ℤ)
  upper_uu : x.upper * y.upper ≤ output.upper * (2 ^ precision : ℤ)

private theorem lower_product_meaning {precision : ℕ} {output x y : ℤ}
    (h : output * (2 ^ precision : ℤ) ≤ x * y) :
    (output : ℝ) / scale precision ≤
      ((x : ℝ) / scale precision) * ((y : ℝ) / scale precision) := by
  have hscale : 0 < scale precision := scale_pos precision
  have hreal : (output : ℝ) * scale precision ≤ (x : ℝ) * y := by
    have hcast : ((output * (2 ^ precision : ℤ) : ℤ) : ℝ) ≤
        ((x * y : ℤ) : ℝ) := by exact_mod_cast h
    simpa [scale] using hcast
  rw [show ((x : ℝ) / scale precision) * ((y : ℝ) / scale precision) =
      ((x : ℝ) * y) / (scale precision * scale precision) by ring]
  rw [div_le_div_iff₀ hscale (mul_pos hscale hscale)]
  simpa [mul_assoc] using mul_le_mul_of_nonneg_right hreal hscale.le

private theorem upper_product_meaning {precision : ℕ} {output x y : ℤ}
    (h : x * y ≤ output * (2 ^ precision : ℤ)) :
    ((x : ℝ) / scale precision) * ((y : ℝ) / scale precision) ≤
      (output : ℝ) / scale precision := by
  have hscale : 0 < scale precision := scale_pos precision
  have hreal : (x : ℝ) * y ≤ (output : ℝ) * scale precision := by
    have hcast : ((x * y : ℤ) : ℝ) ≤
        ((output * (2 ^ precision : ℤ) : ℤ) : ℝ) := by exact_mod_cast h
    simpa [scale] using hcast
  rw [show ((x : ℝ) / scale precision) * ((y : ℝ) / scale precision) =
      ((x : ℝ) * y) / (scale precision * scale precision) by ring]
  rw [div_le_div_iff₀ (mul_pos hscale hscale) hscale]
  simpa [mul_assoc] using mul_le_mul_of_nonneg_right hreal hscale.le

/-- Integer product checks imply the real four-corner certificate. -/
theorem MulCertificate.toRealCertificate
    {precision : ℕ} {x y output : ChapterVISignedDyadicInterval precision}
    (certificate : MulCertificate x y output) :
    ChapterVIRealInterval.MulCertificate x.toRealInterval y.toRealInterval
      output.toRealInterval where
  output_wf := by
    exact (div_le_div_iff_of_pos_right (scale_pos precision)).2
      (by exact_mod_cast certificate.output_wf)
  lower_ll := lower_product_meaning certificate.lower_ll
  lower_lu := lower_product_meaning certificate.lower_lu
  lower_ul := lower_product_meaning certificate.lower_ul
  lower_uu := lower_product_meaning certificate.lower_uu
  upper_ll := upper_product_meaning certificate.upper_ll
  upper_lu := upper_product_meaning certificate.upper_lu
  upper_ul := upper_product_meaning certificate.upper_ul
  upper_uu := upper_product_meaning certificate.upper_uu

theorem MulCertificate.contains_mul
    {precision : ℕ} {x y output : ChapterVISignedDyadicInterval precision}
    (certificate : MulCertificate x y output) {a b : ℝ}
    (ha : x.Contains a) (hb : y.Contains b) :
    output.Contains (a * b) :=
  certificate.toRealCertificate.contains_mul ha hb

/-- Integer checks for the reciprocal of a positive signed dyadic interval. -/
structure PositiveReciprocalCertificate {precision : ℕ}
    (input output : ChapterVISignedDyadicInterval precision) : Prop where
  input_lower_pos : 0 < input.lower
  output_wf : output.lower ≤ output.upper
  output_lower_nonneg : 0 ≤ output.lower
  lower_cross : output.lower * input.upper ≤ (2 ^ precision : ℤ) ^ 2
  upper_cross : (2 ^ precision : ℤ) ^ 2 ≤ output.upper * input.lower

private theorem product_le_one_meaning {precision : ℕ} {x y : ℤ}
    (h : x * y ≤ (2 ^ precision : ℤ) ^ 2) :
    ((x : ℝ) / scale precision) * ((y : ℝ) / scale precision) ≤ 1 := by
  have hscale : 0 < scale precision := scale_pos precision
  have hcast : (((x * y : ℤ) : ℝ)) ≤
      (((2 ^ precision : ℤ) ^ 2 : ℤ) : ℝ) := by exact_mod_cast h
  have hreal : (x : ℝ) * y ≤ scale precision ^ 2 := by
    simpa [scale] using hcast
  rw [show ((x : ℝ) / scale precision) * ((y : ℝ) / scale precision) =
      ((x : ℝ) * y) / (scale precision ^ 2) by ring]
  exact (div_le_one₀ (sq_pos_of_pos hscale)).2 hreal

private theorem one_le_product_meaning {precision : ℕ} {x y : ℤ}
    (h : (2 ^ precision : ℤ) ^ 2 ≤ x * y) :
    1 ≤ ((x : ℝ) / scale precision) * ((y : ℝ) / scale precision) := by
  have hscale : 0 < scale precision := scale_pos precision
  have hcast : ((((2 ^ precision : ℤ) ^ 2 : ℤ) : ℝ)) ≤
      (((x * y : ℤ) : ℝ)) := by exact_mod_cast h
  have hreal : scale precision ^ 2 ≤ (x : ℝ) * y := by
    simpa [scale] using hcast
  rw [show ((x : ℝ) / scale precision) * ((y : ℝ) / scale precision) =
      ((x : ℝ) * y) / (scale precision ^ 2) by ring]
  exact (one_le_div₀ (sq_pos_of_pos hscale)).2 hreal

theorem PositiveReciprocalCertificate.toRealCertificate
    {precision : ℕ} {input output : ChapterVISignedDyadicInterval precision}
    (certificate : PositiveReciprocalCertificate input output) :
    ChapterVIRealInterval.PositiveReciprocalCertificate input.toRealInterval
      output.toRealInterval where
  input_lower_pos := div_pos (by exact_mod_cast certificate.input_lower_pos)
    (scale_pos precision)
  output_wf := (div_le_div_iff_of_pos_right (scale_pos precision)).2
    (by exact_mod_cast certificate.output_wf)
  output_lower_nonneg := div_nonneg (by exact_mod_cast certificate.output_lower_nonneg)
    (scale_pos precision).le
  lower_cross := product_le_one_meaning certificate.lower_cross
  upper_cross := one_le_product_meaning certificate.upper_cross

theorem PositiveReciprocalCertificate.contains_inv
    {precision : ℕ} {input output : ChapterVISignedDyadicInterval precision}
    (certificate : PositiveReciprocalCertificate input output) {value : ℝ}
    (hvalue : input.Contains value) : output.Contains value⁻¹ :=
  certificate.toRealCertificate.contains_inv hvalue

end

end ChapterVISignedDyadicInterval

/-- A rectangular complex interval, represented by independent real and imaginary intervals. -/
structure ChapterVIComplexRectangle where
  real : ChapterVIRealInterval
  imag : ChapterVIRealInterval

namespace ChapterVIComplexRectangle

def Contains (rectangle : ChapterVIComplexRectangle) (value : ℂ) : Prop :=
  rectangle.real.Contains value.re ∧ rectangle.imag.Contains value.im

def add (x y : ChapterVIComplexRectangle) : ChapterVIComplexRectangle where
  real := x.real.add y.real
  imag := x.imag.add y.imag

def neg (x : ChapterVIComplexRectangle) : ChapterVIComplexRectangle where
  real := x.real.neg
  imag := x.imag.neg

def sub (x y : ChapterVIComplexRectangle) : ChapterVIComplexRectangle :=
  x.add y.neg

theorem add_contains {x y : ChapterVIComplexRectangle} {a b : ℂ}
    (ha : x.Contains a) (hb : y.Contains b) :
    (x.add y).Contains (a + b) :=
  ⟨ChapterVIRealInterval.add_contains ha.1 hb.1,
    ChapterVIRealInterval.add_contains ha.2 hb.2⟩

theorem neg_contains {x : ChapterVIComplexRectangle} {a : ℂ}
    (ha : x.Contains a) : x.neg.Contains (-a) :=
  ⟨ChapterVIRealInterval.neg_contains ha.1,
    ChapterVIRealInterval.neg_contains ha.2⟩

theorem sub_contains {x y : ChapterVIComplexRectangle} {a b : ℂ}
    (ha : x.Contains a) (hb : y.Contains b) :
    (x.sub y).Contains (a - b) := by
  simpa [sub, sub_eq_add_neg] using add_contains ha (neg_contains hb)

/-- Four real product certificates are sufficient for a rectangular complex product. -/
structure MulCertificate (x y : ChapterVIComplexRectangle) where
  realReal : ChapterVIRealInterval
  imagImag : ChapterVIRealInterval
  realImag : ChapterVIRealInterval
  imagReal : ChapterVIRealInterval
  realReal_sound : ChapterVIRealInterval.MulCertificate x.real y.real realReal
  imagImag_sound : ChapterVIRealInterval.MulCertificate x.imag y.imag imagImag
  realImag_sound : ChapterVIRealInterval.MulCertificate x.real y.imag realImag
  imagReal_sound : ChapterVIRealInterval.MulCertificate x.imag y.real imagReal

def MulCertificate.output {x y : ChapterVIComplexRectangle}
    (certificate : MulCertificate x y) : ChapterVIComplexRectangle where
  real := certificate.realReal.sub certificate.imagImag
  imag := certificate.realImag.add certificate.imagReal

theorem MulCertificate.output_contains_mul
    {x y : ChapterVIComplexRectangle} (certificate : MulCertificate x y)
    {a b : ℂ} (ha : x.Contains a) (hb : y.Contains b) :
    certificate.output.Contains (a * b) := by
  have hrr := certificate.realReal_sound.contains_mul ha.1 hb.1
  have hii := certificate.imagImag_sound.contains_mul ha.2 hb.2
  have hri := certificate.realImag_sound.contains_mul ha.1 hb.2
  have hir := certificate.imagReal_sound.contains_mul ha.2 hb.1
  exact ⟨ChapterVIRealInterval.sub_contains hrr hii,
    ChapterVIRealInterval.add_contains hri hir⟩

/-- A norm error widens both Cartesian components by the same amount. -/
def widen (rectangle : ChapterVIComplexRectangle) (error : ℝ) :
    ChapterVIComplexRectangle where
  real := ⟨rectangle.real.lower - error, rectangle.real.upper + error⟩
  imag := ⟨rectangle.imag.lower - error, rectangle.imag.upper + error⟩

theorem widen_contains_of_norm_sub_le
    {rectangle : ChapterVIComplexRectangle} {approximation value : ℂ} {error : ℝ}
    (happroximation : rectangle.Contains approximation)
    (herror : ‖value - approximation‖ ≤ error) :
    (rectangle.widen error).Contains value := by
  have hre : |value.re - approximation.re| ≤ error := by
    exact (Complex.abs_re_le_norm (value - approximation)).trans herror
  have him : |value.im - approximation.im| ≤ error := by
    exact (Complex.abs_im_le_norm (value - approximation)).trans herror
  rw [abs_le] at hre him
  constructor <;> constructor <;> dsimp [widen]
  · linarith [happroximation.1.1]
  · linarith [happroximation.1.2]
  · linarith [happroximation.2.1]
  · linarith [happroximation.2.2]

end ChapterVIComplexRectangle

end PoincareChapterVI
