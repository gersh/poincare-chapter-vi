/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import LeanCompCert.Verified.ExpFixed
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Real-number meaning of LeanCompCert fixed-point power certificates

`LeanCompCert.Verified.ExpFixed.rpow_bracket` is deliberately stated using only natural-number
powers.  That is the form a compiled fixed-width checker can verify.  The Chapter VI contour,
however, uses `Real.rpow`.  This file closes that encoding gap: the integer bracket implies the
expected outward-rounded real interval for `n ^ (Y / 2^T)`.

No compiled run appears in this theorem.  A later contour certificate supplies the checked
integer inequalities; this kernel proof says exactly what those inequalities mean analytically.
-/

namespace PoincareChapterVI

open LeanCompCert.Verified.ExpFixed

/-- Raising the fixed-point target to its positive denominator recovers the all-integer middle
term used by `ExpFixed.rpow_bracket`. -/
private theorem fixedPointRpow_pow_denominator (P T n Y : ℕ) :
    (((2 : ℝ) ^ P *
        (n : ℝ) ^ ((Y : ℝ) / ((2 ^ T : ℕ) : ℝ))) ^ (2 ^ T : ℕ)) =
      (2 : ℝ) ^ (P * 2 ^ T) * (n : ℝ) ^ Y := by
  rw [mul_pow, ← pow_mul]
  have hden : (((2 ^ T : ℕ) : ℝ)) ≠ 0 := by positivity
  have hexponent :
      (Y : ℝ) / ((2 ^ T : ℕ) : ℝ) * ((2 ^ T : ℕ) : ℝ) = (Y : ℝ) := by
    field_simp
  rw [← Real.rpow_mul_natCast (Nat.cast_nonneg n), hexponent,
    Real.rpow_natCast]

/-- The real interval represented by LeanCompCert's integer `rpow` bracket.  The scale is
`2^P`; both endpoints are outward rounded. -/
theorem leanCompCert_rpow_real_bracket (P S T n Y : ℕ)
    (hS : LeanCompCert.Verified.LogFixed.errB S ≤
      LeanCompCert.Verified.LogFixed.B62)
    (h1 : 1 ≤ n) (h2 : n < LeanCompCert.Verified.LogFixed.B63) :
    (rpowLo P S T n Y : ℝ) / (2 : ℝ) ^ P ≤
        (n : ℝ) ^ ((Y : ℝ) / ((2 ^ T : ℕ) : ℝ)) ∧
      (n : ℝ) ^ ((Y : ℝ) / ((2 ^ T : ℕ) : ℝ)) ≤
        (rpowHi P S T n Y : ℝ) / (2 : ℝ) ^ P := by
  obtain ⟨hlower, hupper⟩ := rpow_bracket P S T n Y hS h1 h2
  have hlowerReal :
      (rpowLo P S T n Y : ℝ) ^ (2 ^ T : ℕ) ≤
        (2 : ℝ) ^ (P * 2 ^ T) * (n : ℝ) ^ Y := by
    exact_mod_cast hlower
  have hupperReal :
      (2 : ℝ) ^ (P * 2 ^ T) * (n : ℝ) ^ Y ≤
        (rpowHi P S T n Y : ℝ) ^ (2 ^ T : ℕ) := by
    exact_mod_cast hupper
  have hpowne : (2 ^ T : ℕ) ≠ 0 := by positivity
  have htargetNonneg :
      0 ≤ (2 : ℝ) ^ P *
        (n : ℝ) ^ ((Y : ℝ) / ((2 ^ T : ℕ) : ℝ)) := by positivity
  have hlowerScaled :
      (rpowLo P S T n Y : ℝ) ≤
        (2 : ℝ) ^ P *
          (n : ℝ) ^ ((Y : ℝ) / ((2 ^ T : ℕ) : ℝ)) := by
    apply le_of_pow_le_pow_left₀ hpowne htargetNonneg
    rw [fixedPointRpow_pow_denominator]
    exact hlowerReal
  have hupperScaled :
      (2 : ℝ) ^ P *
          (n : ℝ) ^ ((Y : ℝ) / ((2 ^ T : ℕ) : ℝ)) ≤
        (rpowHi P S T n Y : ℝ) := by
    apply le_of_pow_le_pow_left₀ hpowne (by positivity)
    rw [fixedPointRpow_pow_denominator]
    exact hupperReal
  constructor
  · exact (div_le_iff₀' (by positivity)).2 hlowerScaled
  · exact (le_div_iff₀' (by positivity)).2 (by simpa [mul_comm] using hupperScaled)

/-- A machine-checkable sum-of-squares bound on scaled component magnitudes gives the
corresponding lower bound on the complex norm.  This is the final algebraic step expected for
each row of the compiled outer-arc sample table.

The interval evaluator supplies `hre` and `him`; the compiled checker only has to verify `hsq`,
an inequality of natural numbers. -/
theorem leanCompCert_complex_norm_lower_of_scaled_components
    (scale margin reLower imLower : ℕ) (z : ℂ)
    (hscale : 0 < scale)
    (hre : (reLower : ℝ) ≤ (scale : ℝ) * |z.re|)
    (him : (imLower : ℝ) ≤ (scale : ℝ) * |z.im|)
    (hsq : margin ^ 2 ≤ reLower ^ 2 + imLower ^ 2) :
    (margin : ℝ) / scale ≤ ‖z‖ := by
  have hreSq : (reLower : ℝ) ^ 2 ≤ ((scale : ℝ) * |z.re|) ^ 2 :=
    pow_le_pow_left₀ (Nat.cast_nonneg reLower) hre 2
  have himSq : (imLower : ℝ) ^ 2 ≤ ((scale : ℝ) * |z.im|) ^ 2 :=
    pow_le_pow_left₀ (Nat.cast_nonneg imLower) him 2
  have hsqReal : (margin : ℝ) ^ 2 ≤
      (reLower : ℝ) ^ 2 + (imLower : ℝ) ^ 2 := by
    exact_mod_cast hsq
  rw [mul_pow, sq_abs] at hreSq himSq
  have hscaledSq : (margin : ℝ) ^ 2 ≤
      ((scale : ℝ) * ‖z‖) ^ 2 := by
    rw [mul_pow, Complex.sq_norm, Complex.normSq_apply]
    nlinarith
  have hscaled : (margin : ℝ) ≤ (scale : ℝ) * ‖z‖ :=
    le_of_pow_le_pow_left₀ (by norm_num) (mul_nonneg (Nat.cast_nonneg scale) (norm_nonneg z))
      hscaledSq
  exact (div_le_iff₀' (Nat.cast_pos.mpr hscale)).2 hscaled

end PoincareChapterVI
