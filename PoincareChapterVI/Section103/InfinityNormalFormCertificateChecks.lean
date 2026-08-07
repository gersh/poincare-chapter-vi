/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.Section103.InfinityNormalFormCertificate

/-! Kernel-checked normalized identities for the Section 103 infinity normal forms. -/

namespace PoincareChapterVI.InfinityNormalFormCertificate

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
theorem x_localized_first_certificate :
    normalMap xLocalizedFirstLeft == normalMap xLocalizedFirstRight := by
  verified_decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
theorem x_localized_second_certificate :
    normalMap xLocalizedSecondLeft == normalMap xLocalizedSecondRight := by
  verified_decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
theorem x_localized_third_certificate :
    normalMap xLocalizedThirdLeft == normalMap xLocalizedThirdRight := by
  verified_decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
theorem y_localized_first_certificate :
    normalMap yLocalizedFirstLeft == normalMap yLocalizedFirstRight := by
  verified_decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
theorem y_localized_second_certificate :
    normalMap yLocalizedSecondLeft == normalMap yLocalizedSecondRight := by
  verified_decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
theorem y_localized_third_certificate :
    normalMap yLocalizedThirdLeft == normalMap yLocalizedThirdRight := by
  verified_decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
theorem x_chart_first_certificate :
    normalMap xChartFirstLeft == normalMap xChartFirstRight := by
  verified_decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
theorem x_chart_second_certificate :
    normalMap xChartSecondLeft == normalMap xChartSecondRight := by
  verified_decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
theorem y_chart_first_certificate :
    normalMap yChartFirstLeft == normalMap yChartFirstRight := by
  verified_decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
theorem y_chart_second_certificate :
    normalMap yChartSecondLeft == normalMap yChartSecondRight := by
  verified_decide

end PoincareChapterVI.InfinityNormalFormCertificate
