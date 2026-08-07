/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import LeanCompCert.Verified.Decide
import PoincareChapterVI.Section103.RotationRestrictionCertificate

/-! Kernel-checked sparse identities for the §103 rotation restrictions. -/

namespace PoincareChapterVI.RotationRestrictionCertificate

open AffineEliminationCertificate

set_option maxRecDepth 100000 in
theorem reduced_shape_certificate :
    normalMap RotationRestrictionData.reducedShape == normalMap reducedShapeRight := by
  verified_decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem direction_zero_certificate :
    normalMap (directionLeft 0) == normalMap (directionRight 0) := by
  verified_decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem direction_one_certificate :
    normalMap (directionLeft 1) == normalMap (directionRight 1) := by
  verified_decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem direction_two_certificate :
    normalMap (directionLeft 2) == normalMap (directionRight 2) := by
  verified_decide

set_option maxRecDepth 100000 in
theorem remainder_has_no_x_certificate :
    ∀ axis, remainderHasNoX axis = true := by
  verified_decide

set_option maxRecDepth 100000 in
theorem residual_has_no_x_certificate : residualHasNoX = true := by
  verified_decide

set_option maxRecDepth 100000 in
theorem restriction_minor_coefficient_certificate :
    ∀ row axis,
      directionRemainderCoefficient axis row =
        gaussianToQI (RotationRestrictionData.restrictionMinor row axis) := by
  verified_decide

set_option maxRecDepth 100000 in
theorem restriction_minor_mod53_certificate :
    RotationRestrictionData.restrictionMinor.map gaussianMod53 = modularMinorZMod := by
  verified_decide

set_option maxRecDepth 100000 in
theorem modular_inverse_mul_minor_certificate :
    modularInverseZMod * modularMinorZMod = 1 := by
  verified_decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem source_direction_certificate :
    ∀ axis,
      normalMap (RotationRestrictionData.direction axis) ==
        normalMap (scaledSourceDirection axis) := by
  verified_decide

end PoincareChapterVI.RotationRestrictionCertificate
