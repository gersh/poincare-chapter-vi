/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.ChapterVIDRadialTailEndpointCertificate

/-! # Completed radial-tail monotonicity certificate

This file joins the endpoint table and its convex collision collars to the previously certified
centered derivative grid.  It is the unconditional finite certificate requested by
`ChapterVIDRadialTailReduction`.
-/

noncomputable section

open scoped unitInterval

namespace PoincareChapterVI

/-- The complete, kernel-checked monotonicity certificate on the final `27/2744` radial strip. -/
theorem chapterVIDRadialTailMonotonicityCertificate :
    ChapterVIDRadialTailMonotonicityCertificate :=
  chapterVIDRadialTailMonotonicityCertificate_of_tables
    ChapterVIDRadialTailEndpointTrace.chapterVIDRadialTail_endpoint_nonneg
    ChapterVIDRadialTailCenteredCertificate.derivative_re_neg

/-- The prefix and repaired radial tail cover every pre-collision pinching-arc point. -/
theorem chapterVID_full_precollision_radicand_re_pos
    (side : ChapterVIDPinchingArcSide) (s t : I) (hpre : (s : ℝ) < 1) :
    0 < (chapterVIDPinchingArcRadicand side (s, t)).re :=
  chapterVIDRadialTailMonotonicityCertificate.full_precollision_radicand_re_pos
    side s t hpre

/-- The corresponding ordinary angular circle has positive real radicand before collision. -/
theorem chapterVID_fullStandardRadicand_re_pos
    (s t : I) (hpre : (s : ℝ) < 1) :
    0 < (ChapterVIDRadialTailMonotonicityCertificate.fullStandardRadicand s t).re :=
  chapterVIDRadialTailMonotonicityCertificate.fullStandardRadicand_re_pos s t hpre

/-- The repaired full pre-collision family therefore has its canonical principal square-root
sheet, with no remaining certificate hypothesis or execution receipt. -/
noncomputable def chapterVIDFullStandardPrincipalSheet :
    ChapterVIContinuousSquareRootSheet
      ChapterVIDRadialTailMonotonicityCertificate.fullStandardPrecollisionRadicand :=
  chapterVIDRadialTailMonotonicityCertificate.fullStandardPrincipalSheet

end PoincareChapterVI
