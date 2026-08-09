/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.ChapterVIDConnectorIntegral

/-!
# From compiled connector certificates to the global placement package

This file removes the remaining abstract connector-limit field from the compiled three-arc
continuation. Two concrete connector certificates select sheets compatible with the compiled
outer quarters, record their constant signs on the local Morse seams, and produce the actual
finite connector contribution required by `ChapterVIDCompiledPrincipalThreeArcPlacement`.

After this construction, the only non-certificate input to the placement package is the genuine
five-piece source-sheet deformation identity.
-/

noncomputable section

open Filter Set Topology
open scoped unitInterval

namespace PoincareChapterVI

namespace ChapterVIDPrincipalConnectorModel

/-- Convert a small positive critical value back to the compact connector parameter. -/
def connectorParameter
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d) (k : ℝ) : I :=
  Set.projIcc 0 1 zero_le_one (1 - k / model.κ)

@[simp]
theorem connectorParameter_zero
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d) :
    model.connectorParameter 0 = 1 := by
  simp [connectorParameter]

theorem continuous_connectorParameter
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d) :
    Continuous model.connectorParameter := by
  unfold connectorParameter
  exact (continuous_projIcc (h := zero_le_one)).comp
    (continuous_const.sub (continuous_id.div_const model.κ))

theorem tendsto_connectorParameter_zero
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d) :
    Tendsto model.connectorParameter (𝓝[>] (0 : ℝ)) (𝓝 (1 : I)) := by
  rw [← model.connectorParameter_zero]
  exact model.continuous_connectorParameter.continuousAt.tendsto.mono_left
    nhdsWithin_le_nhds

/-- On the certified critical-value interval, the inverse affine parameter is exact. -/
theorem criticalValue_connectorParameter
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    {k : ℝ} (hk : k ∈ Set.Icc 0 model.κ) :
    model.criticalValue (model.connectorParameter k) = k := by
  have hκ : model.κ ≠ 0 := model.κ_pos.ne'
  have hraw : 1 - k / model.κ ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · rw [sub_nonneg, div_le_one model.κ_pos]
      exact hk.2
    · exact sub_le_self 1 (div_nonneg hk.1 model.κ_pos.le)
  unfold connectorParameter ChapterVIDPrincipalConnectorModel.criticalValue
  rw [Set.projIcc_of_mem zero_le_one hraw]
  field_simp
  ring

theorem eventually_criticalValue_connectorParameter
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d) :
    ∀ᶠ k : ℝ in 𝓝[>] 0,
      model.criticalValue (model.connectorParameter k) = k := by
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds model.κ_pos).filter_mono nhdsWithin_le_nhds]
    with k hkpos hkκ
  exact model.criticalValue_connectorParameter ⟨hkpos.le, hkκ.le⟩

/-- The two certificate-selected connector sheets, including every seam compatibility needed
later by the five-piece source-sheet deformation. -/
structure CertifiedConnectorPair
    (run : ChapterVIDOuterArcPolarCompiledGrid.CompiledRunVerdict)
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d) where
  initialSheet : ChapterVIContinuousSquareRootSheet
    (model.rectangleRadicand .initial)
  finalSheet : ChapterVIContinuousSquareRootSheet
    (model.rectangleRadicand .final)
  initial_outer : ∀ s : I,
    initialSheet.root (model.connectorBoundaryPoint .initial s) =
      model.connectorOuterBoundaryRoot run .initial s
  final_outer : ∀ s : I,
    finalSheet.root (model.connectorBoundaryPoint .final s) =
      model.connectorOuterBoundaryRoot run .final s
  initial_local_sign :
    (∀ s : I,
      initialSheet.root (model.connectorLocalBoundaryPoint .initial s) =
        model.connectorLocalBoundaryRoot s) ∨
    (∀ s : I,
      initialSheet.root (model.connectorLocalBoundaryPoint .initial s) =
        -model.connectorLocalBoundaryRoot s)
  final_local_sign :
    (∀ s : I,
      finalSheet.root (model.connectorLocalBoundaryPoint .final s) =
        model.connectorLocalBoundaryRoot s) ∨
    (∀ s : I,
      finalSheet.root (model.connectorLocalBoundaryPoint .final s) =
        -model.connectorLocalBoundaryRoot s)
  initial_tendsto : Tendsto (model.connectorIntegral .initial initialSheet)
    (𝓝 (1 : I)) (𝓝 (model.connectorIntegral .initial initialSheet 1))
  final_tendsto : Tendsto (model.connectorIntegral .final finalSheet)
    (𝓝 (1 : I)) (𝓝 (model.connectorIntegral .final finalSheet 1))

/-- The actual normalized sum of the two transformed connector integrals. -/
def CertifiedConnectorPair.connectorContribution
    {run : ChapterVIDOuterArcPolarCompiledGrid.CompiledRunVerdict}
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    (pair : CertifiedConnectorPair run model) (k : ℝ) : ℂ :=
  model.connectorIntegral .initial pair.initialSheet (model.connectorParameter k) +
    model.connectorIntegral .final pair.finalSheet (model.connectorParameter k)

/-- Its collision value is an ordinary finite complex number. -/
def CertifiedConnectorPair.connectorLimit
    {run : ChapterVIDOuterArcPolarCompiledGrid.CompiledRunVerdict}
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    (pair : CertifiedConnectorPair run model) : ℂ :=
  model.connectorIntegral .initial pair.initialSheet 1 +
    model.connectorIntegral .final pair.finalSheet 1

theorem CertifiedConnectorPair.connector_tendsto
    {run : ChapterVIDOuterArcPolarCompiledGrid.CompiledRunVerdict}
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    (pair : CertifiedConnectorPair run model) :
    Tendsto pair.connectorContribution (𝓝[>] (0 : ℝ))
      (𝓝 pair.connectorLimit) := by
  unfold connectorContribution connectorLimit
  exact (pair.initial_tendsto.comp model.tendsto_connectorParameter_zero).add
    (pair.final_tendsto.comp model.tendsto_connectorParameter_zero)

/-- Two compiled certificates construct the complete connector pair. -/
theorem exists_certifiedConnectorPair
    (run : ChapterVIDOuterArcPolarCompiledGrid.CompiledRunVerdict)
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (initialCertificate : ChapterVIDConnectorCompiledCertificate model .initial)
    (finalCertificate : ChapterVIDConnectorCompiledCertificate model .final) :
    Nonempty (CertifiedConnectorPair run model) := by
  obtain ⟨initialSheet, initialOuter, initialLocal, initialTendsto⟩ :=
    model.exists_sheet_outer_boundary_local_sign_tendsto_connectorIntegral
      run .initial initialCertificate
  obtain ⟨finalSheet, finalOuter, finalLocal, finalTendsto⟩ :=
    model.exists_sheet_outer_boundary_local_sign_tendsto_connectorIntegral
      run .final finalCertificate
  exact ⟨{
    initialSheet := initialSheet
    finalSheet := finalSheet
    initial_outer := initialOuter
    final_outer := finalOuter
    initial_local_sign := initialLocal
    final_local_sign := finalLocal
    initial_tendsto := initialTendsto
    final_tendsto := finalTendsto }⟩

/-- A connector pair whose two outer-normalized sheets both meet the positive local Morse sheet.
By connectedness, one equality at each local seam fixes the branch along that entire seam. -/
structure SeamCompatibleCertifiedConnectorPair
    (run : ChapterVIDOuterArcPolarCompiledGrid.CompiledRunVerdict)
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d) where
  pair : CertifiedConnectorPair run model
  initial_local_at_zero :
    pair.initialSheet.root (model.connectorLocalBoundaryPoint .initial 0) =
      model.connectorLocalBoundaryRoot 0
  final_local_at_zero :
    pair.finalSheet.root (model.connectorLocalBoundaryPoint .final 0) =
      model.connectorLocalBoundaryRoot 0

theorem SeamCompatibleCertifiedConnectorPair.initial_local
    {run : ChapterVIDOuterArcPolarCompiledGrid.CompiledRunVerdict}
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    (compatible : SeamCompatibleCertifiedConnectorPair run model) (s : I) :
    compatible.pair.initialSheet.root
        (model.connectorLocalBoundaryPoint .initial s) =
      model.connectorLocalBoundaryRoot s :=
  model.connectorSheet_eq_localBoundary_of_eq_at .initial
    compatible.pair.initialSheet 0 compatible.initial_local_at_zero s

theorem SeamCompatibleCertifiedConnectorPair.final_local
    {run : ChapterVIDOuterArcPolarCompiledGrid.CompiledRunVerdict}
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    (compatible : SeamCompatibleCertifiedConnectorPair run model) (s : I) :
    compatible.pair.finalSheet.root
        (model.connectorLocalBoundaryPoint .final s) =
      model.connectorLocalBoundaryRoot s :=
  model.connectorSheet_eq_localBoundary_of_eq_at .final
    compatible.pair.finalSheet 0 compatible.final_local_at_zero s

/-- All four seams of the five-piece contour now carry explicitly compatible square roots: the
outer equalities come from the compiled normalization and the local equalities from the two
single-point checks above. -/
theorem SeamCompatibleCertifiedConnectorPair.all_seams
    {run : ChapterVIDOuterArcPolarCompiledGrid.CompiledRunVerdict}
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    (compatible : SeamCompatibleCertifiedConnectorPair run model) :
    (∀ s : I,
      compatible.pair.initialSheet.root
          (model.connectorBoundaryPoint .initial s) =
        model.connectorOuterBoundaryRoot run .initial s) ∧
    (∀ s : I,
      compatible.pair.initialSheet.root
          (model.connectorLocalBoundaryPoint .initial s) =
        model.connectorLocalBoundaryRoot s) ∧
    (∀ s : I,
      compatible.pair.finalSheet.root
          (model.connectorLocalBoundaryPoint .final s) =
        model.connectorLocalBoundaryRoot s) ∧
    (∀ s : I,
      compatible.pair.finalSheet.root
          (model.connectorBoundaryPoint .final s) =
        model.connectorOuterBoundaryRoot run .final s) :=
  ⟨compatible.pair.initial_outer, compatible.initial_local,
    compatible.final_local, compatible.pair.final_outer⟩

/-- Assemble a certificate-selected connector pair into the global three-arc placement.
The caller supplies only the actual source-sheet contribution and the five-piece contour
decomposition; the connector contribution and its finite collision limit are no longer
abstract inputs. -/
def CertifiedConnectorPair.toCompiledPrincipalThreeArcPlacement
    {run : ChapterVIDOuterArcPolarCompiledGrid.CompiledRunVerdict}
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    (pair : CertifiedConnectorPair run model)
    (fullContribution : ℝ → ℂ)
    (decomposition : ∀ᶠ k in 𝓝[>] (0 : ℝ),
      fullContribution k =
        (ChapterVIDOuterArcRegularity.principalRegularContribution
            run massProduct b d (chapterVIDCriticalToGlobalParameter k) +
          pair.connectorContribution k) +
        chapterVIDPrincipalLocalPhiContribution
          massProduct b d model.rootModel.L k) :
    ChapterVIDCompiledPrincipalThreeArcPlacement
      run massProduct b d model.rootModel.toChapterVIDPrincipalLocalSourceModel where
  fullContribution := fullContribution
  connectorContribution := pair.connectorContribution
  connectorLimit := pair.connectorLimit
  connector_tendsto := pair.connector_tendsto
  decomposition := decomposition

/-- Once the genuine five-piece deformation identity is known, the certificate-selected
connectors give Poincare's nonzero logarithmic asymptotic without any further regularity
hypothesis. -/
theorem CertifiedConnectorPair.tendsto_full_inv_neg_log_smul
    {run : ChapterVIDOuterArcPolarCompiledGrid.CompiledRunVerdict}
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    (pair : CertifiedConnectorPair run model)
    (fullContribution : ℝ → ℂ)
    (decomposition : ∀ᶠ k in 𝓝[>] (0 : ℝ),
      fullContribution k =
        (ChapterVIDOuterArcRegularity.principalRegularContribution
            run massProduct b d (chapterVIDCriticalToGlobalParameter k) +
          pair.connectorContribution k) +
        chapterVIDPrincipalLocalPhiContribution
          massProduct b d model.rootModel.L k) :
    Tendsto
      (fun k : ℝ ↦ (-Real.log k)⁻¹ • fullContribution k)
      (𝓝[>] 0)
      (𝓝 ((2 * Real.pi * Complex.I : ℂ)⁻¹ *
        chapterVIDPrincipalMorseAmplitude massProduct b d (0, 0))) := by
  exact ChapterVIDCompiledPrincipalThreeArcPlacement.tendsto_full_inv_neg_log_smul
    (pair.toCompiledPrincipalThreeArcPlacement fullContribution decomposition)

/-- The normalized formal sum of the compiled outer quarters, the two certificate-selected
connectors, and the positive local Morse segment. It becomes the analytic contribution of one
five-piece source-sheet contour once the two connector sheets are proved to meet that positive
local sheet; that seam compatibility is intentionally not hidden in this definition. -/
def CertifiedConnectorPair.fivePieceContribution
    {run : ChapterVIDOuterArcPolarCompiledGrid.CompiledRunVerdict}
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    (pair : CertifiedConnectorPair run model) (k : ℝ) : ℂ :=
  (ChapterVIDOuterArcRegularity.principalRegularContribution
      run massProduct b d (chapterVIDCriticalToGlobalParameter k) +
    pair.connectorContribution k) +
  chapterVIDPrincipalLocalPhiContribution massProduct b d model.rootModel.L k

/-- The canonical five-term sum satisfies the global placement interface by definition. Thus no
separate algebraic decomposition hypothesis is needed; identifying the sum with one seamless
source contour remains a geometric theorem. -/
def CertifiedConnectorPair.toFivePiecePlacement
    {run : ChapterVIDOuterArcPolarCompiledGrid.CompiledRunVerdict}
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    (pair : CertifiedConnectorPair run model) :
    ChapterVIDCompiledPrincipalThreeArcPlacement
      run massProduct b d model.rootModel.toChapterVIDPrincipalLocalSourceModel :=
  pair.toCompiledPrincipalThreeArcPlacement pair.fivePieceContribution
    (Filter.Eventually.of_forall fun _ ↦ rfl)

/-- Conditional only on the connector certificates, the canonical five-term sum has Poincare's
explicit nonzero logarithmic leading term. To call this the continued source contour one must
still prove local-seam compatibility and deformation from the original unit circle. -/
theorem CertifiedConnectorPair.tendsto_fivePiece_inv_neg_log_smul
    {run : ChapterVIDOuterArcPolarCompiledGrid.CompiledRunVerdict}
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    (pair : CertifiedConnectorPair run model) :
    Tendsto
      (fun k : ℝ ↦ (-Real.log k)⁻¹ • pair.fivePieceContribution k)
      (𝓝[>] 0)
      (𝓝 ((2 * Real.pi * Complex.I : ℂ)⁻¹ *
      chapterVIDPrincipalMorseAmplitude massProduct b d (0, 0))) :=
  pair.toFivePiecePlacement.tendsto_full_inv_neg_log_smul

def SeamCompatibleCertifiedConnectorPair.fivePieceContribution
    {run : ChapterVIDOuterArcPolarCompiledGrid.CompiledRunVerdict}
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    (compatible : SeamCompatibleCertifiedConnectorPair run model) : ℝ → ℂ :=
  compatible.pair.fivePieceContribution

/-- Poincare's literal §94 unit-circle function, evaluated along the positive critical-value
coordinate approaching D.  Naming this function prevents the abstract `fullContribution` field
of the general three-arc interface from being mistaken for the source contour integral. -/
def principalPhiAlongCriticalValue
    (massProduct : ℂ) (b d : ℤ) (sourceRoot : ℂ × ℂ → ℂ) (k : ℝ) : ℂ :=
  chapterVIDPrincipalPhi massProduct b d sourceRoot
    (chapterVIDCriticalParameterInverseAtD (k : ℂ))

/-- A seam-compatible pair inherits the logarithmic limit, now with the branch equalities needed
to interpret all five summands as one continued square-root sheet. -/
theorem SeamCompatibleCertifiedConnectorPair.tendsto_fivePiece_inv_neg_log_smul
    {run : ChapterVIDOuterArcPolarCompiledGrid.CompiledRunVerdict}
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    (compatible : SeamCompatibleCertifiedConnectorPair run model) :
    Tendsto
      (fun k : ℝ ↦ (-Real.log k)⁻¹ • compatible.fivePieceContribution k)
      (𝓝[>] 0)
      (𝓝 ((2 * Real.pi * Complex.I : ℂ)⁻¹ *
        chapterVIDPrincipalMorseAmplitude massProduct b d (0, 0))) :=
  compatible.pair.tendsto_fivePiece_inv_neg_log_smul

/-- Source-exact end of the §94--100 argument.  If a single square-root sheet on Poincare's
literal source contour is transported from the unit circle to the five certified pieces, the
actual `chapterVIDPrincipalPhi` has the computed nonzero logarithmic coefficient.  The sole
hypothesis is now an equality whose left side is the literal §94 definition, rather than an
unconstrained placeholder function. -/
theorem SeamCompatibleCertifiedConnectorPair.tendsto_principalPhiAlongCriticalValue
    {run : ChapterVIDOuterArcPolarCompiledGrid.CompiledRunVerdict}
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    (compatible : SeamCompatibleCertifiedConnectorPair run model)
    (sourceRoot : ℂ × ℂ → ℂ)
    (hdeformation : ∀ᶠ k : ℝ in 𝓝[>] 0,
      principalPhiAlongCriticalValue massProduct b d sourceRoot k =
        compatible.fivePieceContribution k) :
    Tendsto
      (fun k : ℝ ↦ (-Real.log k)⁻¹ •
        principalPhiAlongCriticalValue massProduct b d sourceRoot k)
      (𝓝[>] 0)
      (𝓝 ((2 * Real.pi * Complex.I : ℂ)⁻¹ *
        chapterVIDPrincipalMorseAmplitude massProduct b d (0, 0))) := by
  apply Filter.Tendsto.congr' _
    compatible.tendsto_fivePiece_inv_neg_log_smul
  filter_upwards [hdeformation] with k hk
  rw [hk]

/-- End-to-end certified-connector statement: nonvanishing witnesses for the coordinate and
radicand on each side, together with the already compiled outer run, produce a five-piece
contribution with the exact logarithmic asymptotic. -/
theorem exists_fivePieceContribution_tendsto_of_compiledCertificates
    (run : ChapterVIDOuterArcPolarCompiledGrid.CompiledRunVerdict)
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (initialCertificate : ChapterVIDConnectorCompiledCertificate model .initial)
    (finalCertificate : ChapterVIDConnectorCompiledCertificate model .final) :
    ∃ pair : CertifiedConnectorPair run model,
      Tendsto
        (fun k : ℝ ↦ (-Real.log k)⁻¹ • pair.fivePieceContribution k)
        (𝓝[>] 0)
        (𝓝 ((2 * Real.pi * Complex.I : ℂ)⁻¹ *
          chapterVIDPrincipalMorseAmplitude massProduct b d (0, 0))) := by
  obtain ⟨pair⟩ := exists_certifiedConnectorPair run model
    initialCertificate finalCertificate
  exact ⟨pair, pair.tendsto_fivePiece_inv_neg_log_smul⟩

end ChapterVIDPrincipalConnectorModel

end PoincareChapterVI
