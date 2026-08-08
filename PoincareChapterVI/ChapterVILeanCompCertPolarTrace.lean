/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.ChapterVILeanCompCertComplexTrace

/-!
# Dependency-preserving polar traces

Generic rectangular inversion loses the identity `v⁻¹ = conj v` on the unit circle.  Near the D
collision this dependency loss is large enough to swamp the positive radicand margin.  This trace
keeps a point in the form `u = r*v`, certifies the real powers of the positive radius, and uses
exact conjugation for the unit factor.  Thus `u³` and `u⁻³` remain sharp without adding any trusted
operation to the compiled checker.
-/

namespace PoincareChapterVI

open ChapterVILeanCompCertBatch

namespace ChapterVILeanCompCertPolarTrace

open scoped ComplexConjugate

abbrev Interval (precision : ℕ) := ChapterVISignedDyadicInterval precision
abbrev Rectangle (precision : ℕ) := ChapterVISignedDyadicComplexRectangle precision

/-- A compiled trace for `u`, `u³`, and `u⁻³` from `u=r*v`, with `r>0` and `‖v‖=1`. -/
structure Trace {precision : ℕ}
    (radius : Interval precision) (unit : Rectangle precision) where
  radiusInv : Interval precision
  radiusSq : Interval precision
  radiusCube : Interval precision
  radiusCubeInv : Interval precision
  unitCube : ChapterVISignedDyadicComplexRectangle.CubeTrace unit
  u : ChapterVISignedDyadicComplexRectangle.RealMulTrace radius unit
  uInv : ChapterVISignedDyadicComplexRectangle.RealMulTrace radiusInv unit.conjugate
  uCube : ChapterVISignedDyadicComplexRectangle.RealMulTrace radiusCube unitCube.output
  uCubeInv : ChapterVISignedDyadicComplexRectangle.RealMulTrace
    radiusCubeInv unitCube.output.conjugate

def Trace.operations {precision : ℕ}
    {radius : Interval precision} {unit : Rectangle precision}
    (trace : Trace radius unit) : List (DyadicOperation precision) :=
  [ .positiveReciprocal radius trace.radiusInv
  , .mul radius radius trace.radiusSq
  , .mul trace.radiusSq radius trace.radiusCube
  , .positiveReciprocal trace.radiusCube trace.radiusCubeInv ] ++
    trace.unitCube.operations ++ trace.u.operations ++ trace.uInv.operations ++ trace.uCube.operations ++
      trace.uCubeInv.operations

theorem Trace.radial_outputs_contain_of_allSound {precision : ℕ}
    {radius : Interval precision} {unit : Rectangle precision}
    (trace : Trace radius unit)
    (hall : ∀ operation ∈ trace.operations, operation.Sound)
    {r : ℝ} (hr : radius.Contains r) :
    trace.radiusInv.Contains r⁻¹ ∧
      trace.radiusCube.Contains (r ^ 3) ∧
        trace.radiusCubeInv.Contains (r ^ 3)⁻¹ := by
  have hradiusInvCert : ChapterVISignedDyadicInterval.PositiveReciprocalCertificate
      radius trace.radiusInv :=
    hall (.positiveReciprocal radius trace.radiusInv) (by simp [Trace.operations])
  have hrSqCert : ChapterVISignedDyadicInterval.MulCertificate
      radius radius trace.radiusSq :=
    hall (.mul radius radius trace.radiusSq) (by simp [Trace.operations])
  have hrCubeCert : ChapterVISignedDyadicInterval.MulCertificate
      trace.radiusSq radius trace.radiusCube :=
    hall (.mul trace.radiusSq radius trace.radiusCube) (by simp [Trace.operations])
  have hrInvCert : ChapterVISignedDyadicInterval.PositiveReciprocalCertificate
      trace.radiusCube trace.radiusCubeInv :=
    hall (.positiveReciprocal trace.radiusCube trace.radiusCubeInv)
      (by simp [Trace.operations])
  have hrSq := hrSqCert.contains_mul hr hr
  have hrCube := hrCubeCert.contains_mul hrSq hr
  refine ⟨hradiusInvCert.contains_inv hr, ?_, ?_⟩
  · simpa [pow_succ, pow_two, mul_assoc] using hrCube
  · simpa [pow_succ, pow_two, mul_assoc] using hrInvCert.contains_inv hrCube

theorem Trace.outputs_contain_of_allSound {precision : ℕ}
    {radius : Interval precision} {unit : Rectangle precision}
    (trace : Trace radius unit)
    (hall : ∀ operation ∈ trace.operations, operation.Sound)
    {r : ℝ} {v : ℂ} (hr : radius.Contains r)
    (hv : unit.Contains v) (hvNorm : ‖v‖ = 1) :
    trace.u.output.Contains ((r : ℂ) * v) ∧
      trace.uInv.output.Contains (((r : ℂ) * v)⁻¹) ∧
      trace.uCube.output.Contains (((r : ℂ) * v) ^ 3) ∧
        trace.uCubeInv.output.Contains ((((r : ℂ) * v) ^ 3)⁻¹) := by
  have hradiusInvCert : ChapterVISignedDyadicInterval.PositiveReciprocalCertificate
      radius trace.radiusInv :=
    hall (.positiveReciprocal radius trace.radiusInv) (by simp [Trace.operations])
  have hrSqCert : ChapterVISignedDyadicInterval.MulCertificate
      radius radius trace.radiusSq :=
    hall (.mul radius radius trace.radiusSq) (by simp [Trace.operations])
  have hrCubeCert : ChapterVISignedDyadicInterval.MulCertificate
      trace.radiusSq radius trace.radiusCube :=
    hall (.mul trace.radiusSq radius trace.radiusCube) (by simp [Trace.operations])
  have hrInvCert : ChapterVISignedDyadicInterval.PositiveReciprocalCertificate
      trace.radiusCube trace.radiusCubeInv :=
    hall (.positiveReciprocal trace.radiusCube trace.radiusCubeInv)
      (by simp [Trace.operations])
  have hunitSound : ∀ operation ∈ trace.unitCube.operations, operation.Sound := by
    intro operation hoperation
    exact hall operation (by simp [Trace.operations, hoperation])
  have huSound : ∀ operation ∈ trace.u.operations, operation.Sound := by
    intro operation hoperation
    exact hall operation (by simp [Trace.operations, hoperation])
  have huInvUnitSound : ∀ operation ∈ trace.uInv.operations, operation.Sound := by
    intro operation hoperation
    exact hall operation (by simp [Trace.operations, hoperation])
  have huCubeSound : ∀ operation ∈ trace.uCube.operations, operation.Sound := by
    intro operation hoperation
    exact hall operation (by simp [Trace.operations, hoperation])
  have huInvSound : ∀ operation ∈ trace.uCubeInv.operations, operation.Sound := by
    intro operation hoperation
    exact hall operation (by simp [Trace.operations, hoperation])
  have hrSq := hrSqCert.contains_mul hr hr
  have hrInv := hradiusInvCert.contains_inv hr
  have hrCube := hrCubeCert.contains_mul hrSq hr
  have hrCubeInv := hrInvCert.contains_inv hrCube
  have hunitCube := trace.unitCube.output_contains_cube_of_allSound hunitSound hv
  have hunitInv :=
    ChapterVISignedDyadicComplexRectangle.conjugate_contains_inv_of_norm_one hv hvNorm
  have hunitCubeNorm : ‖v ^ 3‖ = 1 := by simp [norm_pow, hvNorm]
  have hunitCubeInv :=
    ChapterVISignedDyadicComplexRectangle.conjugate_contains_inv_of_norm_one
    hunitCube hunitCubeNorm
  have hu := trace.u.output_contains_of_allSound huSound hr hv
  have huInv := trace.uInv.output_contains_of_allSound huInvUnitSound hrInv hunitInv
  have huCubeScaled := trace.uCube.output_contains_of_allSound
    huCubeSound hrCube hunitCube
  have huInvScaled := trace.uCubeInv.output_contains_of_allSound
    huInvSound hrCubeInv hunitCubeInv
  refine ⟨hu, ?_, ?_, ?_⟩
  · simpa [mul_inv_rev, mul_comm] using huInv
  · convert huCubeScaled using 1
    push_cast
    ring
  · simpa [mul_pow, pow_succ, pow_two, mul_assoc, mul_comm, mul_left_comm]
      using huInvScaled

end ChapterVILeanCompCertPolarTrace

end PoincareChapterVI
