/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.ChapterVILeanCompCertBatch

/-!
# Compiled cubic- and sixth-root interval traces

The certificate contour needs `q^(1/3)` and `q^(1/6)`. Rather than approximate logarithms or a
non-dyadic exponent, the compiled checker raises proposed dyadic endpoints to the third or sixth
power with outward rounding. Kernel mathematics then uses monotonicity on the nonnegative reals to
turn those power comparisons into root enclosures.
-/

namespace PoincareChapterVI.ChapterVILeanCompCertRoots

open PoincareChapterVI
open ChapterVILeanCompCertBatch

/-- A degenerate dyadic interval at one encoded endpoint. -/
def endpoint {precision : ℕ} (value : ℤ) : ChapterVISignedDyadicInterval precision :=
  ⟨value, value⟩

/-- Two rounded products computing a cube. -/
structure PowThreeTrace {precision : ℕ}
    (input : ChapterVISignedDyadicInterval precision) where
  square : ChapterVISignedDyadicInterval precision
  cube : ChapterVISignedDyadicInterval precision

def PowThreeTrace.operations {precision : ℕ}
    {input : ChapterVISignedDyadicInterval precision}
    (trace : PowThreeTrace input) : List (DyadicOperation precision) :=
  [ .mul input input trace.square
  , .mul trace.square input trace.cube ]

theorem PowThreeTrace.cube_contains_of_allSound {precision : ℕ}
    {input : ChapterVISignedDyadicInterval precision}
    (trace : PowThreeTrace input)
    (hall : ∀ operation ∈ trace.operations, operation.Sound)
    {value : ℝ} (hvalue : input.Contains value) :
    trace.cube.Contains (value ^ 3) := by
  have hsquare : ChapterVISignedDyadicInterval.MulCertificate
      input input trace.square :=
    hall (.mul input input trace.square) (by simp [PowThreeTrace.operations])
  have hcube : ChapterVISignedDyadicInterval.MulCertificate
      trace.square input trace.cube :=
    hall (.mul trace.square input trace.cube) (by simp [PowThreeTrace.operations])
  have hsquareValue := hsquare.contains_mul hvalue hvalue
  simpa [pow_succ, pow_two, mul_assoc] using hcube.contains_mul hsquareValue hvalue

/-- Three rounded products computing a sixth power as `x²`, `x³`, then `(x³)²`. -/
structure PowSixTrace {precision : ℕ}
    (input : ChapterVISignedDyadicInterval precision) where
  square : ChapterVISignedDyadicInterval precision
  cube : ChapterVISignedDyadicInterval precision
  sixth : ChapterVISignedDyadicInterval precision

def PowSixTrace.operations {precision : ℕ}
    {input : ChapterVISignedDyadicInterval precision}
    (trace : PowSixTrace input) : List (DyadicOperation precision) :=
  [ .mul input input trace.square
  , .mul trace.square input trace.cube
  , .mul trace.cube trace.cube trace.sixth ]

theorem PowSixTrace.sixth_contains_of_allSound {precision : ℕ}
    {input : ChapterVISignedDyadicInterval precision}
    (trace : PowSixTrace input)
    (hall : ∀ operation ∈ trace.operations, operation.Sound)
    {value : ℝ} (hvalue : input.Contains value) :
    trace.sixth.Contains (value ^ 6) := by
  have hsquare : ChapterVISignedDyadicInterval.MulCertificate
      input input trace.square :=
    hall (.mul input input trace.square) (by simp [PowSixTrace.operations])
  have hcube : ChapterVISignedDyadicInterval.MulCertificate
      trace.square input trace.cube :=
    hall (.mul trace.square input trace.cube) (by simp [PowSixTrace.operations])
  have hsixth : ChapterVISignedDyadicInterval.MulCertificate
      trace.cube trace.cube trace.sixth :=
    hall (.mul trace.cube trace.cube trace.sixth) (by simp [PowSixTrace.operations])
  have hsquareValue := hsquare.contains_mul hvalue hvalue
  have hcubeValue := hcube.contains_mul hsquareValue hvalue
  have hsixthValue := hsixth.contains_mul hcubeValue hcubeValue
  simpa [pow_succ, pow_two, mul_assoc] using hsixthValue

/-- Monotonicity bridge shared by the cubic and sixth-root traces. -/
theorem rpow_inv_natCast_mem_of_power_bounds {precision n : ℕ}
    (hn : n ≠ 0) (input output : ChapterVISignedDyadicInterval precision)
    {value : ℝ} (hvalueNonneg : 0 ≤ value) (hvalue : input.Contains value)
    (houtputUpperNonneg : 0 ≤ (output.upper : ℝ) /
      ChapterVISignedDyadicInterval.scale precision)
    (hlowerPower :
      ((output.lower : ℝ) / ChapterVISignedDyadicInterval.scale precision) ^ n ≤
        (input.lower : ℝ) / ChapterVISignedDyadicInterval.scale precision)
    (hupperPower :
      (input.upper : ℝ) / ChapterVISignedDyadicInterval.scale precision ≤
        ((output.upper : ℝ) / ChapterVISignedDyadicInterval.scale precision) ^ n) :
    output.Contains (value ^ ((n : ℝ)⁻¹)) := by
  let root := value ^ ((n : ℝ)⁻¹)
  have hrootNonneg : 0 ≤ root := Real.rpow_nonneg hvalueNonneg _
  have hrootPow : root ^ n = value :=
    Real.rpow_inv_natCast_pow hvalueNonneg hn
  constructor
  · apply le_of_pow_le_pow_left₀ hn hrootNonneg
    rw [hrootPow]
    exact hlowerPower.trans hvalue.1
  · apply le_of_pow_le_pow_left₀ hn houtputUpperNonneg
    rw [hrootPow]
    exact hvalue.2.trans hupperPower

/-- Endpoint power traces certifying a cubic-root enclosure. -/
structure CubicRootTrace {precision : ℕ}
    (input output : ChapterVISignedDyadicInterval precision) where
  lowerPower : PowThreeTrace (endpoint (precision := precision) output.lower)
  upperPower : PowThreeTrace (endpoint (precision := precision) output.upper)

def CubicRootTrace.operations {precision : ℕ}
    {input output : ChapterVISignedDyadicInterval precision}
    (trace : CubicRootTrace input output) : List (DyadicOperation precision) :=
  trace.lowerPower.operations ++ trace.upperPower.operations

theorem CubicRootTrace.output_contains_of_allSound {precision : ℕ}
    {input output : ChapterVISignedDyadicInterval precision}
    (trace : CubicRootTrace input output)
    (hall : ∀ operation ∈ trace.operations, operation.Sound)
    {value : ℝ} (hvalueNonneg : 0 ≤ value) (hvalue : input.Contains value)
    (houtputUpperNonneg : 0 ≤ output.upper)
    (hlower : trace.lowerPower.cube.upper ≤ input.lower)
    (hupper : input.upper ≤ trace.upperPower.cube.lower) :
    output.Contains (value ^ ((3 : ℝ)⁻¹)) := by
  have hlowerSound : ∀ operation ∈ trace.lowerPower.operations, operation.Sound := by
    intro operation hoperation
    exact hall operation (by simp [CubicRootTrace.operations, hoperation])
  have hupperSound : ∀ operation ∈ trace.upperPower.operations, operation.Sound := by
    intro operation hoperation
    exact hall operation (by simp [CubicRootTrace.operations, hoperation])
  have hlowerPoint : (endpoint (precision := precision) output.lower).Contains
      ((output.lower : ℝ) / ChapterVISignedDyadicInterval.scale precision) :=
    ⟨le_rfl, le_rfl⟩
  have hupperPoint : (endpoint (precision := precision) output.upper).Contains
      ((output.upper : ℝ) / ChapterVISignedDyadicInterval.scale precision) :=
    ⟨le_rfl, le_rfl⟩
  have hlowerPow := trace.lowerPower.cube_contains_of_allSound hlowerSound hlowerPoint
  have hupperPow := trace.upperPower.cube_contains_of_allSound hupperSound hupperPoint
  apply rpow_inv_natCast_mem_of_power_bounds (by norm_num) input output
      hvalueNonneg hvalue
  · exact div_nonneg (by exact_mod_cast houtputUpperNonneg)
      (ChapterVISignedDyadicInterval.scale_pos precision).le
  · exact hlowerPow.2.trans ((div_le_div_iff_of_pos_right
      (ChapterVISignedDyadicInterval.scale_pos precision)).2 (by exact_mod_cast hlower))
  · exact ((div_le_div_iff_of_pos_right
      (ChapterVISignedDyadicInterval.scale_pos precision)).2 (by exact_mod_cast hupper)).trans
      hupperPow.1

/-- Endpoint power traces certifying a sixth-root enclosure. -/
structure SixthRootTrace {precision : ℕ}
    (input output : ChapterVISignedDyadicInterval precision) where
  lowerPower : PowSixTrace (endpoint (precision := precision) output.lower)
  upperPower : PowSixTrace (endpoint (precision := precision) output.upper)

def SixthRootTrace.operations {precision : ℕ}
    {input output : ChapterVISignedDyadicInterval precision}
    (trace : SixthRootTrace input output) : List (DyadicOperation precision) :=
  trace.lowerPower.operations ++ trace.upperPower.operations

theorem SixthRootTrace.output_contains_of_allSound {precision : ℕ}
    {input output : ChapterVISignedDyadicInterval precision}
    (trace : SixthRootTrace input output)
    (hall : ∀ operation ∈ trace.operations, operation.Sound)
    {value : ℝ} (hvalueNonneg : 0 ≤ value) (hvalue : input.Contains value)
    (houtputUpperNonneg : 0 ≤ output.upper)
    (hlower : trace.lowerPower.sixth.upper ≤ input.lower)
    (hupper : input.upper ≤ trace.upperPower.sixth.lower) :
    output.Contains (value ^ ((6 : ℝ)⁻¹)) := by
  have hlowerSound : ∀ operation ∈ trace.lowerPower.operations, operation.Sound := by
    intro operation hoperation
    exact hall operation (by simp [SixthRootTrace.operations, hoperation])
  have hupperSound : ∀ operation ∈ trace.upperPower.operations, operation.Sound := by
    intro operation hoperation
    exact hall operation (by simp [SixthRootTrace.operations, hoperation])
  have hlowerPoint : (endpoint (precision := precision) output.lower).Contains
      ((output.lower : ℝ) / ChapterVISignedDyadicInterval.scale precision) :=
    ⟨le_rfl, le_rfl⟩
  have hupperPoint : (endpoint (precision := precision) output.upper).Contains
      ((output.upper : ℝ) / ChapterVISignedDyadicInterval.scale precision) :=
    ⟨le_rfl, le_rfl⟩
  have hlowerPow := trace.lowerPower.sixth_contains_of_allSound hlowerSound hlowerPoint
  have hupperPow := trace.upperPower.sixth_contains_of_allSound hupperSound hupperPoint
  apply rpow_inv_natCast_mem_of_power_bounds (by norm_num) input output
      hvalueNonneg hvalue
  · exact div_nonneg (by exact_mod_cast houtputUpperNonneg)
      (ChapterVISignedDyadicInterval.scale_pos precision).le
  · exact hlowerPow.2.trans ((div_le_div_iff_of_pos_right
      (ChapterVISignedDyadicInterval.scale_pos precision)).2 (by exact_mod_cast hlower))
  · exact ((div_le_div_iff_of_pos_right
      (ChapterVISignedDyadicInterval.scale_pos precision)).2 (by exact_mod_cast hupper)).trans
      hupperPow.1

end PoincareChapterVI.ChapterVILeanCompCertRoots
