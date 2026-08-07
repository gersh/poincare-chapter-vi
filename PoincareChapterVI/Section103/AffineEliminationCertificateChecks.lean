/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.Section103.AffineEliminationCertificate

/-! Kernel-checked identities for the Section 103 affine shape basis. -/

namespace PoincareChapterVI.AffineEliminationCertificate

open AffineEliminationData

set_option maxRecDepth 100000 in
theorem shape_from_tail_certificate :
    normalMap shapePolynomial == normalMap shapeFromTail := by
  verified_decide

set_option maxRecDepth 100000 in
theorem eliminant_from_residual_certificate :
    normalMap eliminant == normalMap eliminantFromResidual := by
  verified_decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem shape_membership_certificate :
    normalMap shapeMembershipLeft == normalMap shapePolynomial := by
  verified_decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem eliminant_membership_certificate :
    normalMap eliminantMembershipLeft == normalMap eliminant := by
  verified_decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem sextic_reconstruction_certificate :
    normalMap sexticReconstructionLeft == normalMap affineSextic := by
  verified_decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem septic_reconstruction_certificate :
    normalMap septicReconstructionLeft == normalMap affineSeptic := by
  verified_decide

end PoincareChapterVI.AffineEliminationCertificate
