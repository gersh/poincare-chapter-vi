/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.ChapterVIDConnectorFactorMonotonicity

/-!
# The scale-aware crossing boundary for the D connector seams

The direct factor rectangles prove principal-slit separation away from a 261-cell collar at each
local endpoint.  Inside that collar, the derivative and curvature campaigns prove that the
imaginary part of the first factor is strictly increasing and that the companion factor stays in
the open right half-plane.  The only remaining numerical fact is therefore the sign of the first
factor at its (at most one) real-axis crossing.

`PositiveCrossingCertificate` records precisely that fact.  This file proves that this one
predicate, together with the already compiled campaigns and connector nonvanishing certificate,
determines the seam sign and reaches Poincare's logarithmic leading term.  It is the semantic
target for a dependency-preserving LeanCompCert certificate; no finite computation is hidden in
the assembly below.
-/

noncomputable section

open Set Topology
open scoped unitInterval

namespace PoincareChapterVI
namespace ChapterVIDConnectorFactorCrossing

open ChapterVIDConnectorFactorBulkReference
open ChapterVIDConnectorFactorMonotonicity
open ChapterVIDConnectorSeamCompiledGrid
open ChapterVILeanCompCertBatch
open ChapterVILeanCompCertAttestation

/-- The sole scale-aware finite claim still needed in the endpoint collars. -/
structure PositiveCrossingCertificate
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) : Prop where
  plus_re_nonneg_of_im_eq_zero : ∀ t : I, (t : ℝ) ∈ collarInterval side →
    (model.rectangleFactorPlus side (connectorPathPoint model t)).im = 0 →
    0 ≤ (model.rectangleFactorPlus side (connectorPathPoint model t)).re

/-- Real part of the vanishing factor along the literal connector line. -/
def lineReal
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) : ℝ → ℝ := fun t ↦
  (chapterVIDRootCoordinateCollisionFactorPlus
    (model.connectorParameterRoot 0)
    (AffineMap.lineMap
      (model.rootModel.connectorSource side (model.criticalValue 0))
      (model.rootModel.connectorTarget side (model.criticalValue 0)) (t : ℂ))).re

/-- Real part of the literal path derivative. -/
def lineDerivativeReal
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) : ℝ → ℝ := fun t ↦
  (chapterVIDRootCoordinateCollisionFactorPlusDerivative
      (model.connectorParameterRoot 0)
      (AffineMap.lineMap
        (model.rootModel.connectorSource side (model.criticalValue 0))
        (model.rootModel.connectorTarget side (model.criticalValue 0)) (t : ℂ)) *
    (model.rootModel.connectorTarget side (model.criticalValue 0) -
      model.rootModel.connectorSource side (model.criticalValue 0))).re

/-- Real curvature of the first collision factor along the literal affine connector. -/
def lineCurvatureReal
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) : ℝ → ℝ := fun t ↦
  (chapterVIDRootCoordinateCollisionFactorPlusSecondDerivative
      (model.connectorParameterRoot 0)
      (AffineMap.lineMap
        (model.rootModel.connectorSource side (model.criticalValue 0))
        (model.rootModel.connectorTarget side (model.criticalValue 0)) (t : ℂ)) *
    (model.rootModel.connectorTarget side (model.criticalValue 0) -
      model.rootModel.connectorSource side (model.criticalValue 0)) ^ 2).re

theorem hasDerivAt_lineReal
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    HasDerivAt (lineReal model side) (lineDerivativeReal model side x) x := by
  let t : I := ⟨x, hx⟩
  have hcoordinate := model.rectanglePoint_ne_zero side (0, t)
  have hfactor : HasDerivAt
      (chapterVIDRootCoordinateCollisionFactorPlus (model.connectorParameterRoot 0))
      (chapterVIDRootCoordinateCollisionFactorPlusDerivative
        (model.connectorParameterRoot 0)
        (AffineMap.lineMap
          (model.rootModel.connectorSource side (model.criticalValue 0))
          (model.rootModel.connectorTarget side (model.criticalValue 0)) (x : ℂ)))
      (AffineMap.lineMap
        (model.rootModel.connectorSource side (model.criticalValue 0))
        (model.rootModel.connectorTarget side (model.criticalValue 0)) (x : ℂ)) :=
    hasDerivAt_chapterVIDRootCoordinateCollisionFactorPlus
      (model.connectorParameterRoot_ne_zero 0)
      (by simpa [ChapterVIDPrincipalConnectorModel.rectanglePoint,
        ChapterVIDPrincipalGlobalRootModel.connectorPoint, t,
        AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, smul_eq_mul,
        mul_comm] using hcoordinate)
  have hline : HasDerivAt
      (fun w : ℂ ↦ AffineMap.lineMap
        (model.rootModel.connectorSource side (model.criticalValue 0))
        (model.rootModel.connectorTarget side (model.criticalValue 0)) w)
      (model.rootModel.connectorTarget side (model.criticalValue 0) -
        model.rootModel.connectorSource side (model.criticalValue 0)) (x : ℂ) := by
    simpa [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, smul_eq_mul,
      mul_comm] using
      (((hasDerivAt_id (x : ℂ)).const_mul
        (model.rootModel.connectorTarget side (model.criticalValue 0) -
          model.rootModel.connectorSource side (model.criticalValue 0))).add_const
            (model.rootModel.connectorSource side (model.criticalValue 0)))
  have hcomp := hfactor.comp (x : ℂ) hline
  unfold lineReal lineDerivativeReal
  simpa [Function.comp_apply] using hcomp.real_of_complex

theorem continuousOn_lineReal
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) :
    ContinuousOn (lineReal model side) (collarInterval side) := by
  intro x hx
  exact (hasDerivAt_lineReal model side
    (collarInterval_subset_unit side hx)).continuousAt.continuousWithinAt

theorem hasDerivAt_lineDerivativeReal
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    HasDerivAt (lineDerivativeReal model side) (lineCurvatureReal model side x) x := by
  let t : I := ⟨x, hx⟩
  let source := model.rootModel.connectorSource side (model.criticalValue 0)
  let target := model.rootModel.connectorTarget side (model.criticalValue 0)
  let coordinate := AffineMap.lineMap source target (x : ℂ)
  let direction := target - source
  have hcoordinate : coordinate ≠ 0 := by
    simpa [coordinate, source, target, ChapterVIDPrincipalConnectorModel.rectanglePoint,
      ChapterVIDPrincipalGlobalRootModel.connectorPoint, t,
      AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, smul_eq_mul,
      mul_comm] using model.rectanglePoint_ne_zero side (0, t)
  have hfactor : HasDerivAt
      (chapterVIDRootCoordinateCollisionFactorPlusDerivative
        (model.connectorParameterRoot 0))
      (chapterVIDRootCoordinateCollisionFactorPlusSecondDerivative
        (model.connectorParameterRoot 0) coordinate) coordinate :=
    hasDerivAt_chapterVIDRootCoordinateCollisionFactorPlusDerivative hcoordinate
  have hline : HasDerivAt
      (fun w : ℂ ↦ AffineMap.lineMap source target w) direction (x : ℂ) := by
    simpa [source, target, direction, AffineMap.lineMap_apply, vsub_eq_sub,
      vadd_eq_add, smul_eq_mul, mul_comm] using
      (((hasDerivAt_id (x : ℂ)).const_mul direction).add_const source)
  have hcomp := hfactor.comp (x : ℂ) hline
  have hproduct := hcomp.mul_const direction
  unfold lineDerivativeReal lineCurvatureReal
  simpa [source, target, coordinate, direction, Function.comp_apply, pow_two,
    mul_assoc] using hproduct.real_of_complex

theorem continuousOn_lineDerivativeReal
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) :
    ContinuousOn (lineDerivativeReal model side) (collarInterval side) := by
  intro x hx
  exact (hasDerivAt_lineDerivativeReal model side
    (collarInterval_subset_unit side hx)).continuousAt.continuousWithinAt

/-- The selected inverse-Morse endpoint has a strict real derivative margin with the required
orientation. -/
theorem lineDerivativeReal_local_strictly_oriented
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDAnchoredConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) :
    match side with
    | .initial => lineDerivativeReal model.toChapterVIDPrincipalConnectorModel side 1 < 0
    | .final => 0 < lineDerivativeReal model.toChapterVIDPrincipalConnectorModel side 0 := by
  have hk : model.κ ∈ Set.Icc 0 model.κ := ⟨model.κ_pos.le, le_rfl⟩
  have hroot := model.parameterRoot_eq_global model.κ hk
  cases side with
  | initial =>
      simpa [lineDerivativeReal, chapterVIDEndpointRealDerivativeValue,
        ChapterVIDPrincipalConnectorModel.connectorParameterRoot,
        ChapterVIDPrincipalConnectorModel.criticalValue_zero, hroot,
        ChapterVIDPrincipalGlobalRootModel.connectorSource,
        ChapterVIDPrincipalGlobalRootModel.connectorTarget,
        ChapterVIDPrincipalGlobalRootModel.localConnectorEndpoint,
        ChapterVIDPrincipalGlobalRootModel.outerConnectorEndpoint,
        AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, smul_eq_mul] using
        model.initialRealAnchor
  | final =>
      simpa [lineDerivativeReal, chapterVIDEndpointRealDerivativeValue,
        ChapterVIDPrincipalConnectorModel.connectorParameterRoot,
        ChapterVIDPrincipalConnectorModel.criticalValue_zero, hroot,
        ChapterVIDPrincipalGlobalRootModel.connectorSource,
        ChapterVIDPrincipalGlobalRootModel.connectorTarget,
        ChapterVIDPrincipalGlobalRootModel.localConnectorEndpoint,
        ChapterVIDPrincipalGlobalRootModel.outerConnectorEndpoint,
        AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, smul_eq_mul] using
        model.finalRealAnchor

theorem lineDerivativeReal_local_oriented
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDAnchoredConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) :
    match side with
    | .initial => lineDerivativeReal model.toChapterVIDPrincipalConnectorModel side 1 ≤ 0
    | .final => 0 ≤ lineDerivativeReal model.toChapterVIDPrincipalConnectorModel side 0 := by
  cases side with
  | initial => exact (lineDerivativeReal_local_strictly_oriented model .initial).le
  | final => exact (lineDerivativeReal_local_strictly_oriented model .final).le

/-- Auxiliary sufficient target: if a campaign proves nonnegative real curvature, the exact
inverse-Morse endpoint signs orient the first derivative everywhere. This is a sound calculus
interface, but the actual endpoint curvature is scale-sensitive, so no concrete campaign of this
shape is claimed below. -/
structure NonnegativeRealCurvatureCertificate
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) : Prop where
  nonnegative : ∀ t : I, (t : ℝ) ∈ collarInterval side →
    0 ≤ lineCurvatureReal model side (t : ℝ)

/-- A scale-aware derivative campaign may equivalently orient the real derivative throughout
the collar.  This form is particularly convenient for interval compilation: it compares the
crossing value with the already positive exact Morse endpoint. -/
structure OrientedRealDerivativeCertificate
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) : Prop where
  oriented : ∀ t : I, (t : ℝ) ∈ collarInterval side →
    match side with
    | .initial => lineDerivativeReal model side (t : ℝ) ≤ 0
    | .final => 0 ≤ lineDerivativeReal model side (t : ℝ)

/-- Distance from the local inverse-Morse endpoint, in the affine line parameter. -/
def localEndpointDistance (side : ChapterVIDOuterArcSide) (t : ℝ) : ℝ :=
  match side with
  | .initial => 1 - t
  | .final => t

/-- Put the two required derivative orientations into one nonnegative quantity. -/
def orientedLineDerivative
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) (t : ℝ) : ℝ :=
  match side with
  | .initial => -lineDerivativeReal model side t
  | .final => lineDerivativeReal model side t

/-- The scale retained by the terminal certificate.  The endpoint contribution is first order in
the selected inverse-Morse length `L`, while the collapsed connector contribution is second order
in the distance from the local endpoint.  Their sum is therefore the natural nonvanishing
denominator for a dependency-preserving interval campaign. -/
def realDerivativeScale
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDAnchoredConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) (t : ℝ) : ℝ :=
  model.toChapterVIDPrincipalConnectorModel.rootModel.L + localEndpointDistance side t ^ 2

theorem realDerivativeScale_pos
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDAnchoredConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) (t : ℝ) :
    0 < realDerivativeScale model side t := by
  exact add_pos_of_pos_of_nonneg
    model.toChapterVIDPrincipalConnectorModel.rootModel.L_pos (sq_nonneg _)

/-- Scale-normalized quantity that the concrete LeanCompCert table must enclose.  Unlike a raw
Cartesian rectangle for the derivative, this expression does not discard the common `L` and
endpoint-distance factors responsible for the terminal cancellation. -/
def normalizedOrientedLineDerivative
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDAnchoredConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) (t : ℝ) : ℝ :=
  orientedLineDerivative model.toChapterVIDPrincipalConnectorModel side t /
    realDerivativeScale model side t

/-- The exact semantic target of the dependency-preserving compiled campaign. -/
structure NormalizedRealDerivativeCertificate
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDAnchoredConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) : Prop where
  nonnegative : ∀ t : I, (t : ℝ) ∈ collarInterval side →
    0 ≤ normalizedOrientedLineDerivative model side (t : ℝ)

/-- Positivity of `L + distance²` turns the normalized finite certificate into precisely the
oriented derivative statement consumed by the seam proof. -/
theorem NormalizedRealDerivativeCertificate.toOrientedRealDerivativeCertificate
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDAnchoredConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide)
    (certificate : NormalizedRealDerivativeCertificate model side) :
    OrientedRealDerivativeCertificate
      model.toChapterVIDPrincipalConnectorModel side := by
  refine ⟨?_⟩
  intro t ht
  have hscale := realDerivativeScale_pos model side (t : ℝ)
  have hnormalized := certificate.nonnegative t ht
  have horiented :
      0 ≤ orientedLineDerivative model.toChapterVIDPrincipalConnectorModel side (t : ℝ) := by
    rw [normalizedOrientedLineDerivative, div_nonneg_iff] at hnormalized
    rcases hnormalized with hpositive | hnegative
    · exact hpositive.1
    · exact (not_le_of_gt hscale hnegative.2).elim
  cases side with
  | initial => simpa [orientedLineDerivative] using horiented
  | final => simpa [orientedLineDerivative] using horiented

/-- Nonnegative compiled real curvature plus the exact Morse endpoint anchor proves the former
scale-sensitive first-derivative obligation. -/
theorem NonnegativeRealCurvatureCertificate.toOrientedRealDerivativeCertificate
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDAnchoredConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide)
    (certificate : NonnegativeRealCurvatureCertificate
      model.toChapterVIDPrincipalConnectorModel side) :
    OrientedRealDerivativeCertificate
      model.toChapterVIDPrincipalConnectorModel side := by
  have hmono : MonotoneOn
      (lineDerivativeReal model.toChapterVIDPrincipalConnectorModel side)
      (collarInterval side) := by
    apply monotoneOn_of_deriv_nonneg (convex_collarInterval side)
      (continuousOn_lineDerivativeReal
        model.toChapterVIDPrincipalConnectorModel side)
    · intro x hx
      have hx' : x ∈ collarInterval side := interior_subset hx
      exact (hasDerivAt_lineDerivativeReal
        model.toChapterVIDPrincipalConnectorModel side
        (collarInterval_subset_unit side hx')).differentiableAt.differentiableWithinAt
    · intro x hx
      have hx' : x ∈ collarInterval side := interior_subset hx
      let tx : I := ⟨x, collarInterval_subset_unit side hx'⟩
      have hderiv := hasDerivAt_lineDerivativeReal
        model.toChapterVIDPrincipalConnectorModel side
        (collarInterval_subset_unit side hx')
      rw [hderiv.deriv]
      exact certificate.nonnegative tx hx'
  refine ⟨?_⟩
  intro t ht
  have hanchor := lineDerivativeReal_local_oriented model side
  cases side with
  | initial =>
      have hlocalMem : (1 : ℝ) ∈ collarInterval .initial := by
        norm_num [collarInterval]
      exact (hmono ht hlocalMem t.property.2).trans hanchor
  | final =>
      have hlocalMem : (0 : ℝ) ∈ collarInterval .final := by
        norm_num [collarInterval]
      exact hanchor.trans (hmono hlocalMem ht t.property.1)

/-- A dependency-preserving finite crossing campaign.  The generated data chooses the integer
claims; its semantic bridge proves that soundness of those claims implies the crossing theorem.
This is deliberately more general than rectangular interval arithmetic, which loses the common
endpoint scale and cannot settle the terminal cells. -/
structure CompiledCrossingData
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) (precision : ℕ) where
  operations : List (DyadicOperation precision)
  admissible : LeanCompCert.Ports.SignedProductClaims.Admissible
    (batchClaims operations)
  sound : (∀ operation ∈ operations, operation.Sound) →
    PositiveCrossingCertificate model side

/-- A zero verdict from the exact LeanCompCert computation attached to the crossing data. -/
structure CompiledCrossingRunVerdict
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide} {precision : ℕ}
    (name : String) (data : CompiledCrossingData model side precision) : Prop where
  returnsZero : (batchComputation name data.operations).Returns ((0 : ℕ) : Int)

/-- Kernel reconstruction of the semantic crossing theorem from a successful compiled batch. -/
theorem CompiledCrossingRunVerdict.toPositiveCrossingCertificate
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide} {precision : ℕ}
    {name : String} {data : CompiledCrossingData model side precision}
    (run : CompiledCrossingRunVerdict name data) :
    PositiveCrossingCertificate model side := by
  apply data.sound
  intro operation hoperation
  exact allSound_of_returns_zero name data.operations data.admissible run.returnsZero
    operation hoperation

/-- Receipt ingestion for the exact Lean-derived crossing artifact. -/
theorem CompiledCrossingRunVerdict.ofReceipt
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide} {precision : ℕ}
    (name : String) (data : CompiledCrossingData model side precision)
    (crypto : LeanCompCert.Attest.ReceiptCrypto)
    (receipt : LeanCompCert.Attest.RunReceipt)
    (kind : LeanCompCert.Attest.AttestationKind) (params nonce : String)
    (bound : LeanCompCert.Attest.receiptBindsProved crypto
      (batchArtifact name data.operations) kind params nonce ((0 : ℕ) : Int) receipt = true)
    (admitted : LeanCompCert.Attest.RunAdmission crypto
      (batchArtifact name data.operations) receipt) :
    CompiledCrossingRunVerdict name data :=
  ⟨returns_zero_of_receipt name data.operations crypto receipt kind params nonce
    bound admitted⟩

/-- Optional artifact shape for the sufficient nonnegative-curvature condition above. The
interface is sound, but no concrete passing campaign is claimed for Poincare's endpoint geometry. -/
structure CompiledRealCurvatureData
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) (precision : ℕ) where
  operations : List (DyadicOperation precision)
  admissible : LeanCompCert.Ports.SignedProductClaims.Admissible
    (batchClaims operations)
  sound : (∀ operation ∈ operations, operation.Sound) →
    NonnegativeRealCurvatureCertificate model side

structure CompiledRealCurvatureRunVerdict
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide} {precision : ℕ}
    (name : String) (data : CompiledRealCurvatureData model side precision) : Prop where
  returnsZero : (batchComputation name data.operations).Returns ((0 : ℕ) : Int)

theorem CompiledRealCurvatureRunVerdict.toNonnegativeRealCurvatureCertificate
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide} {precision : ℕ}
    {name : String} {data : CompiledRealCurvatureData model side precision}
    (run : CompiledRealCurvatureRunVerdict name data) :
    NonnegativeRealCurvatureCertificate model side := by
  apply data.sound
  intro operation hoperation
  exact allSound_of_returns_zero name data.operations data.admissible run.returnsZero
    operation hoperation

theorem CompiledRealCurvatureRunVerdict.ofReceipt
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide} {precision : ℕ}
    (name : String) (data : CompiledRealCurvatureData model side precision)
    (crypto : LeanCompCert.Attest.ReceiptCrypto)
    (receipt : LeanCompCert.Attest.RunReceipt)
    (kind : LeanCompCert.Attest.AttestationKind) (params nonce : String)
    (bound : LeanCompCert.Attest.receiptBindsProved crypto
      (batchArtifact name data.operations) kind params nonce ((0 : ℕ) : Int) receipt = true)
    (admitted : LeanCompCert.Attest.RunAdmission crypto
      (batchArtifact name data.operations) receipt) :
    CompiledRealCurvatureRunVerdict name data :=
  ⟨returns_zero_of_receipt name data.operations crypto receipt kind params nonce
    bound admitted⟩

/-- Alternative artifact shape: certify the unnormalized oriented real derivative directly on
the full collar.  This interface is sound, but raw Cartesian boxes lose the shared endpoint scale;
the normalized artifact below is the concrete route. -/
structure CompiledRealDerivativeData
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) (precision : ℕ) where
  operations : List (DyadicOperation precision)
  admissible : LeanCompCert.Ports.SignedProductClaims.Admissible
    (batchClaims operations)
  sound : (∀ operation ∈ operations, operation.Sound) →
    OrientedRealDerivativeCertificate model side

structure CompiledRealDerivativeRunVerdict
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide} {precision : ℕ}
    (name : String) (data : CompiledRealDerivativeData model side precision) : Prop where
  returnsZero : (batchComputation name data.operations).Returns ((0 : ℕ) : Int)

theorem CompiledRealDerivativeRunVerdict.toOrientedRealDerivativeCertificate
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide} {precision : ℕ}
    {name : String} {data : CompiledRealDerivativeData model side precision}
    (run : CompiledRealDerivativeRunVerdict name data) :
    OrientedRealDerivativeCertificate model side := by
  apply data.sound
  intro operation hoperation
  exact allSound_of_returns_zero name data.operations data.admissible run.returnsZero
    operation hoperation

theorem CompiledRealDerivativeRunVerdict.ofReceipt
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide} {precision : ℕ}
    (name : String) (data : CompiledRealDerivativeData model side precision)
    (crypto : LeanCompCert.Attest.ReceiptCrypto)
    (receipt : LeanCompCert.Attest.RunReceipt)
    (kind : LeanCompCert.Attest.AttestationKind) (params nonce : String)
    (bound : LeanCompCert.Attest.receiptBindsProved crypto
      (batchArtifact name data.operations) kind params nonce ((0 : ℕ) : Int) receipt = true)
    (admitted : LeanCompCert.Attest.RunAdmission crypto
      (batchArtifact name data.operations) receipt) :
    CompiledRealDerivativeRunVerdict name data :=
  ⟨returns_zero_of_receipt name data.operations crypto receipt kind params nonce
    bound admitted⟩

/-- Preferred compiled artifact: integer operations certify the scale-normalized derivative.
The semantic bridge supplied by a concrete table must reconstruct the literal normalized
expression from those operations; the generic ingestion layer only handles compilation and
receipt plumbing. -/
structure CompiledNormalizedRealDerivativeData
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDAnchoredConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) (precision : ℕ) where
  operations : List (DyadicOperation precision)
  admissible : LeanCompCert.Ports.SignedProductClaims.Admissible
    (batchClaims operations)
  sound : (∀ operation ∈ operations, operation.Sound) →
    NormalizedRealDerivativeCertificate model side

structure CompiledNormalizedRealDerivativeRunVerdict
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDAnchoredConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide} {precision : ℕ}
    (name : String) (data : CompiledNormalizedRealDerivativeData model side precision) : Prop where
  returnsZero : (batchComputation name data.operations).Returns ((0 : ℕ) : Int)

theorem CompiledNormalizedRealDerivativeRunVerdict.toNormalizedRealDerivativeCertificate
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDAnchoredConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide} {precision : ℕ}
    {name : String} {data : CompiledNormalizedRealDerivativeData model side precision}
    (run : CompiledNormalizedRealDerivativeRunVerdict name data) :
    NormalizedRealDerivativeCertificate model side := by
  apply data.sound
  intro operation hoperation
  exact allSound_of_returns_zero name data.operations data.admissible run.returnsZero
    operation hoperation

theorem CompiledNormalizedRealDerivativeRunVerdict.ofReceipt
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDAnchoredConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide} {precision : ℕ}
    (name : String) (data : CompiledNormalizedRealDerivativeData model side precision)
    (crypto : LeanCompCert.Attest.ReceiptCrypto)
    (receipt : LeanCompCert.Attest.RunReceipt)
    (kind : LeanCompCert.Attest.AttestationKind) (params nonce : String)
    (bound : LeanCompCert.Attest.receiptBindsProved crypto
      (batchArtifact name data.operations) kind params nonce ((0 : ℕ) : Int) receipt = true)
    (admitted : LeanCompCert.Attest.RunAdmission crypto
      (batchArtifact name data.operations) receipt) :
    CompiledNormalizedRealDerivativeRunVerdict name data :=
  ⟨returns_zero_of_receipt name data.operations crypto receipt kind params nonce
    bound admitted⟩

/-- Outside the endpoint collar, the retained direct-factor mesh covers the path. -/
theorem dist_ge_cutoff_of_not_mem_collar
    (side : ChapterVIDOuterArcSide) (t : I)
    (ht : (t : ℝ) ∉ collarInterval side) :
    (collarCells : ℝ) / meshCells ≤ dist t (localParameter side) := by
  rw [dist_localParameter_eq]
  cases side with
  | initial =>
      simp only [collarInterval, Set.mem_Icc, not_and_or, not_le] at ht
      simp only [collarCells, meshCells]
      rcases ht with ht | ht
      · norm_num at ht ⊢
        linarith
      · exfalso
        exact (not_lt_of_ge t.property.2) ht
  | final =>
      simp only [collarInterval, Set.mem_Icc, not_and_or, not_le] at ht
      simp only [collarCells, meshCells]
      rcases ht with ht | ht
      · exfalso
        exact (not_lt_of_ge t.property.1) ht
      · norm_num at ht ⊢
        exact ht.le

/-- Connector nonvanishing and the exact factorization make both individual factors nonzero. -/
theorem factors_ne_zero
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide}
    (certificate : ChapterVIDConnectorCompiledCertificate model side)
    (t : I) :
    model.rectangleFactorPlus side (connectorPathPoint model t) ≠ 0 ∧
      model.rectangleFactorMinus side (connectorPathPoint model t) ≠ 0 := by
  have hradicand := certificate.radicand.ne_zero (connectorPathPoint model t)
  have hfactor := model.rectangleRadicand_eq_factor_mul side (connectorPathPoint model t)
  constructor
  · intro hzero
    apply hradicand
    rw [hfactor, hzero, zero_mul]
  · intro hzero
    apply hradicand
    rw [hfactor, hzero, mul_zero]

/-- The exact Morse endpoint product and the compiled companion-factor sign make the vanishing
factor positive real at the local endpoint. -/
theorem local_plus_re_pos
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDAnchoredConnectorModel massProduct b d)
    (derivativeRun :
      ChapterVIDConnectorFactorDerivativeReference.ReferenceCompiledRunVerdict)
    (curvatureRun :
      ChapterVIDConnectorFactorSecondDerivativeReference.ReferenceCompiledRunVerdict)
    (side : ChapterVIDOuterArcSide) :
    0 < (model.rectangleFactorPlus side
      (connectorPathPoint model.toChapterVIDPrincipalConnectorModel
        (localParameter side))).re := by
  let point := connectorPathPoint model.toChapterVIDPrincipalConnectorModel
    (localParameter side)
  let x := model.rectangleFactorPlus side point
  let y := model.rectangleFactorMinus side point
  have hprod : x * y = model.connectorLocalBoundaryRadicand 0 := by
    rw [← model.rectangleRadicand_eq_factor_mul side point]
    simpa [point] using model.rectangleRadicand_connectorLocalBoundaryPoint side 0
  have hprodRe : 0 < (x * y).re := by
    rw [hprod]
    exact model.connectorLocalBoundaryRadicand_re_pos 0
  have hprodIm : (x * y).im = 0 := by
    rw [hprod]
    unfold ChapterVIDPrincipalConnectorModel.connectorLocalBoundaryRadicand
    exact Complex.ofReal_im _
  have hlocal : (localParameter side : ℝ) ∈ collarInterval side := by
    cases side <;> norm_num [localParameter, collarInterval]
  have hyRe : 0 < y.re := by
    change 0 < (model.rectangleFactorMinus side
      (connectorPathPoint model.toChapterVIDPrincipalConnectorModel
        (localParameter side))).re
    exact companion_re_pos_on_collar model.toChapterVIDPrincipalConnectorModel
      derivativeRun curvatureRun side (localParameter side) hlocal
  exact first_re_pos_of_mul_re_pos_im_zero_of_second_re_pos hprodRe hprodIm hyRe

/-- An oriented real-derivative certificate is stronger than the crossing predicate: the first
factor's real part is positive on the entire collar. -/
theorem OrientedRealDerivativeCertificate.toPositiveCrossingCertificate
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDAnchoredConnectorModel massProduct b d)
    (derivativeRun :
      ChapterVIDConnectorFactorDerivativeReference.ReferenceCompiledRunVerdict)
    (curvatureRun :
      ChapterVIDConnectorFactorSecondDerivativeReference.ReferenceCompiledRunVerdict)
    (side : ChapterVIDOuterArcSide)
    (certificate : OrientedRealDerivativeCertificate
      model.toChapterVIDPrincipalConnectorModel side) :
    PositiveCrossingCertificate model.toChapterVIDPrincipalConnectorModel side where
  plus_re_nonneg_of_im_eq_zero := by
    intro t ht _
    have hlocal := local_plus_re_pos model derivativeRun curvatureRun side
    have hvalue : lineReal model.toChapterVIDPrincipalConnectorModel side (t : ℝ) =
        (model.rectangleFactorPlus side
          (connectorPathPoint model.toChapterVIDPrincipalConnectorModel t)).re := by
      rfl
    rw [← hvalue]
    cases side with
    | initial =>
        have hanti : AntitoneOn
            (lineReal model.toChapterVIDPrincipalConnectorModel .initial)
            (collarInterval .initial) := by
          apply antitoneOn_of_deriv_nonpos (convex_collarInterval .initial)
            (continuousOn_lineReal model.toChapterVIDPrincipalConnectorModel .initial)
          · intro x hx
            have hx' : x ∈ collarInterval .initial := interior_subset hx
            exact (hasDerivAt_lineReal model.toChapterVIDPrincipalConnectorModel .initial
              (collarInterval_subset_unit .initial hx')).differentiableAt.differentiableWithinAt
          · intro x hx
            have hx' : x ∈ collarInterval .initial := interior_subset hx
            let tx : I := ⟨x, collarInterval_subset_unit .initial hx'⟩
            have hderiv := hasDerivAt_lineReal
              model.toChapterVIDPrincipalConnectorModel .initial
              (collarInterval_subset_unit .initial hx')
            rw [hderiv.deriv]
            exact certificate.oriented tx hx'
        have hlocalMem : (1 : ℝ) ∈ collarInterval .initial := by
          norm_num [collarInterval]
        have hcompare := hanti ht hlocalMem t.property.2
        change 0 < lineReal model.toChapterVIDPrincipalConnectorModel .initial 1 at hlocal
        exact hlocal.le.trans hcompare
    | final =>
        have hmono : MonotoneOn
            (lineReal model.toChapterVIDPrincipalConnectorModel .final)
            (collarInterval .final) := by
          apply monotoneOn_of_deriv_nonneg (convex_collarInterval .final)
            (continuousOn_lineReal model.toChapterVIDPrincipalConnectorModel .final)
          · intro x hx
            have hx' : x ∈ collarInterval .final := interior_subset hx
            exact (hasDerivAt_lineReal model.toChapterVIDPrincipalConnectorModel .final
              (collarInterval_subset_unit .final hx')).differentiableAt.differentiableWithinAt
          · intro x hx
            have hx' : x ∈ collarInterval .final := interior_subset hx
            let tx : I := ⟨x, collarInterval_subset_unit .final hx'⟩
            have hderiv := hasDerivAt_lineReal
              model.toChapterVIDPrincipalConnectorModel .final
              (collarInterval_subset_unit .final hx')
            rw [hderiv.deriv]
            exact certificate.oriented tx hx'
        have hlocalMem : (0 : ℝ) ∈ collarInterval .final := by
          norm_num [collarInterval]
        have hcompare := hmono hlocalMem ht t.property.1
        change 0 < lineReal model.toChapterVIDPrincipalConnectorModel .final 0 at hlocal
        exact hlocal.le.trans hcompare

/-- The direct mesh and the one crossing predicate give the principal-sqrt continuity condition
for the first factor; the derivative/curvature campaigns give it for the companion factor. -/
theorem sqrt_conditions
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDAnchoredConnectorModel massProduct b d)
    (bulkRun : ChapterVIDConnectorFactorBulkReference.ReferenceCompiledRunVerdict)
    (derivativeRun :
      ChapterVIDConnectorFactorDerivativeReference.ReferenceCompiledRunVerdict)
    (curvatureRun :
      ChapterVIDConnectorFactorSecondDerivativeReference.ReferenceCompiledRunVerdict)
    (side : ChapterVIDOuterArcSide)
    (crossing : PositiveCrossingCertificate
      model.toChapterVIDPrincipalConnectorModel side)
    (t : I) :
    (0 ≤ (model.rectangleFactorPlus side
        (connectorPathPoint model.toChapterVIDPrincipalConnectorModel t)).re ∨
      (model.rectangleFactorPlus side
        (connectorPathPoint model.toChapterVIDPrincipalConnectorModel t)).im ≠ 0) ∧
    (0 ≤ (model.rectangleFactorMinus side
        (connectorPathPoint model.toChapterVIDPrincipalConnectorModel t)).re ∨
      (model.rectangleFactorMinus side
        (connectorPathPoint model.toChapterVIDPrincipalConnectorModel t)).im ≠ 0) := by
  by_cases hcollar : (t : ℝ) ∈ collarInterval side
  · constructor
    · by_cases him :
          (model.rectangleFactorPlus side
            (connectorPathPoint model.toChapterVIDPrincipalConnectorModel t)).im = 0
      · exact Or.inl (crossing.plus_re_nonneg_of_im_eq_zero t hcollar him)
      · exact Or.inr him
    · exact Or.inl
        (companion_re_pos_on_collar model.toChapterVIDPrincipalConnectorModel
          derivativeRun curvatureRun side t hcollar).le
  · have hbulk := dist_ge_cutoff_of_not_mem_collar side t hcollar
    have hregion := connectorPathPoint_mem_bulkMeshIndex
      model.toChapterVIDPrincipalConnectorModel side t hbulk
    have hregion' : connectorPathPoint model.toChapterVIDPrincipalConnectorModel t ∈
        (cell model.toChapterVIDPrincipalConnectorModel side (bulkMeshIndex side t)).region := by
      rw [cell_region, retainedMeshIndex_bulkMeshIndex]
      exact hregion
    have hfacts := bulkRun.cell_facts model.toChapterVIDPrincipalConnectorModel side
      (bulkMeshIndex side t)
      (connectorPathPoint model.toChapterVIDPrincipalConnectorModel t) hregion'
    exact ⟨(plusSeparation side (bulkMeshIndex side t)).sqrt_condition_of_value_pos hfacts.1,
      (minusSeparation side (bulkMeshIndex side t)).sqrt_condition_of_value_pos hfacts.2⟩

/-- The direct factor campaign fixes the product of principal roots at the outer endpoint. -/
theorem outer_arg_add_mem
    {massProduct : ℂ} {b d : ℤ}
    (bulkRun : ChapterVIDConnectorFactorBulkReference.ReferenceCompiledRunVerdict)
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) :
    Complex.arg (model.rectangleFactorPlus side
        (connectorPathPoint model (outerParameter side))) +
      Complex.arg (model.rectangleFactorMinus side
        (connectorPathPoint model (outerParameter side))) ∈
      Set.Ioc (-Real.pi) Real.pi := by
  have hfacts := bulkRun.cell_facts model side (outerIndex side) _
    (connectorPathPoint_outer_mem model side)
  cases side with
  | initial =>
      have hplus := hfacts.1
      have hminus := hfacts.2
      rw [outer_plus_label] at hplus
      rw [outer_minus_label] at hminus
      exact arg_add_mem_Ioc_of_im_neg_pos
        (by simpa [outerPlusSeparation, SlitPlaneSeparation.value,
          SlitPlaneSeparation.toZeroSeparation,
          ChapterVIComplexZeroSeparation.value] using hplus)
        (by simpa [outerMinusSeparation, SlitPlaneSeparation.value,
          SlitPlaneSeparation.toZeroSeparation,
          ChapterVIComplexZeroSeparation.value] using hminus)
  | final =>
      have hplus := hfacts.1
      have hminus := hfacts.2
      rw [outer_plus_label] at hplus
      rw [outer_minus_label] at hminus
      exact arg_add_mem_Ioc_of_im_pos_neg
        (by simpa [outerPlusSeparation, SlitPlaneSeparation.value,
          SlitPlaneSeparation.toZeroSeparation,
          ChapterVIComplexZeroSeparation.value] using hplus)
        (by simpa [outerMinusSeparation, SlitPlaneSeparation.value,
          SlitPlaneSeparation.toZeroSeparation,
          ChapterVIComplexZeroSeparation.value] using hminus)

/-- Product of the two principal factor roots along the connector path. -/
def factorPathSheet
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDAnchoredConnectorModel massProduct b d)
    (bulkRun : ChapterVIDConnectorFactorBulkReference.ReferenceCompiledRunVerdict)
    (derivativeRun :
      ChapterVIDConnectorFactorDerivativeReference.ReferenceCompiledRunVerdict)
    (curvatureRun :
      ChapterVIDConnectorFactorSecondDerivativeReference.ReferenceCompiledRunVerdict)
    (side : ChapterVIDOuterArcSide)
    (crossing : PositiveCrossingCertificate
      model.toChapterVIDPrincipalConnectorModel side) :
    ChapterVIContinuousSquareRootSheet
      (fun t : I ↦ model.rectangleRadicand side
        (connectorPathPoint model.toChapterVIDPrincipalConnectorModel t)) where
  root t :=
    Complex.sqrt (model.rectangleFactorPlus side
      (connectorPathPoint model.toChapterVIDPrincipalConnectorModel t)) *
      Complex.sqrt (model.rectangleFactorMinus side
        (connectorPathPoint model.toChapterVIDPrincipalConnectorModel t))
  continuous_root := by
    have hpath : Continuous (connectorPathPoint model.toChapterVIDPrincipalConnectorModel) :=
      continuous_const.prodMk continuous_id
    have hplus : Continuous
        (fun t : I ↦ Complex.sqrt
          (model.rectangleFactorPlus side
            (connectorPathPoint model.toChapterVIDPrincipalConnectorModel t))) := by
      rw [continuous_iff_continuousAt]
      intro t
      exact (Complex.continuousAt_sqrt
        (sqrt_conditions model bulkRun derivativeRun curvatureRun side crossing t).1).comp_of_eq
          ((model.continuous_rectangleFactorPlus side).comp hpath).continuousAt rfl
    have hminus : Continuous
        (fun t : I ↦ Complex.sqrt
          (model.rectangleFactorMinus side
            (connectorPathPoint model.toChapterVIDPrincipalConnectorModel t))) := by
      rw [continuous_iff_continuousAt]
      intro t
      exact (Complex.continuousAt_sqrt
        (sqrt_conditions model bulkRun derivativeRun curvatureRun side crossing t).2).comp_of_eq
          ((model.continuous_rectangleFactorMinus side).comp hpath).continuousAt rfl
    exact hplus.mul hminus
  root_sq t := by
    rw [mul_pow]
    have hplus := Complex.cpow_nat_inv_pow
      (model.rectangleFactorPlus side
        (connectorPathPoint model.toChapterVIDPrincipalConnectorModel t))
      (by norm_num : (2 : ℕ) ≠ 0)
    have hminus := Complex.cpow_nat_inv_pow
      (model.rectangleFactorMinus side
        (connectorPathPoint model.toChapterVIDPrincipalConnectorModel t))
      (by norm_num : (2 : ℕ) ≠ 0)
    change Complex.sqrt
        (model.rectangleFactorPlus side
          (connectorPathPoint model.toChapterVIDPrincipalConnectorModel t)) ^ 2 *
      Complex.sqrt
        (model.rectangleFactorMinus side
          (connectorPathPoint model.toChapterVIDPrincipalConnectorModel t)) ^ 2 = _
    rw [show Complex.sqrt
          (model.rectangleFactorPlus side
            (connectorPathPoint model.toChapterVIDPrincipalConnectorModel t)) ^ 2 =
          model.rectangleFactorPlus side
            (connectorPathPoint model.toChapterVIDPrincipalConnectorModel t) by exact hplus,
      show Complex.sqrt
          (model.rectangleFactorMinus side
            (connectorPathPoint model.toChapterVIDPrincipalConnectorModel t)) ^ 2 =
          model.rectangleFactorMinus side
            (connectorPathPoint model.toChapterVIDPrincipalConnectorModel t) by exact hminus]
    exact (model.rectangleRadicand_eq_factor_mul side _).symm

theorem factorPathSheet_outer
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDAnchoredConnectorModel massProduct b d)
    (bulkRun : ChapterVIDConnectorFactorBulkReference.ReferenceCompiledRunVerdict)
    (derivativeRun :
      ChapterVIDConnectorFactorDerivativeReference.ReferenceCompiledRunVerdict)
    (curvatureRun :
      ChapterVIDConnectorFactorSecondDerivativeReference.ReferenceCompiledRunVerdict)
    (side : ChapterVIDOuterArcSide)
    (crossing : PositiveCrossingCertificate
      model.toChapterVIDPrincipalConnectorModel side)
    (certificate : ChapterVIDConnectorCompiledCertificate
      model.toChapterVIDPrincipalConnectorModel side) :
    (factorPathSheet model bulkRun derivativeRun curvatureRun side crossing).root
        (outerParameter side) =
      Complex.sqrt (model.rectangleRadicand side
        (connectorPathPoint model.toChapterVIDPrincipalConnectorModel
          (outerParameter side))) := by
  have hne := factors_ne_zero certificate (outerParameter side)
  have hmul := sqrt_mul_of_arg_add_mem hne.1 hne.2
    (outer_arg_add_mem bulkRun model.toChapterVIDPrincipalConnectorModel side)
  rw [model.rectangleRadicand_eq_factor_mul]
  exact hmul.symm

theorem factorPathSheet_local
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDAnchoredConnectorModel massProduct b d)
    (bulkRun : ChapterVIDConnectorFactorBulkReference.ReferenceCompiledRunVerdict)
    (derivativeRun :
      ChapterVIDConnectorFactorDerivativeReference.ReferenceCompiledRunVerdict)
    (curvatureRun :
      ChapterVIDConnectorFactorSecondDerivativeReference.ReferenceCompiledRunVerdict)
    (side : ChapterVIDOuterArcSide)
    (crossing : PositiveCrossingCertificate
      model.toChapterVIDPrincipalConnectorModel side)
    (certificate : ChapterVIDConnectorCompiledCertificate
      model.toChapterVIDPrincipalConnectorModel side) :
    (factorPathSheet model bulkRun derivativeRun curvatureRun side crossing).root
        (localParameter side) = model.connectorLocalBoundaryRoot 0 := by
  let point := connectorPathPoint model.toChapterVIDPrincipalConnectorModel (localParameter side)
  let x := model.rectangleFactorPlus side point
  let y := model.rectangleFactorMinus side point
  have hprod : x * y = model.connectorLocalBoundaryRadicand 0 := by
    rw [← model.rectangleRadicand_eq_factor_mul side point]
    simpa [point] using model.rectangleRadicand_connectorLocalBoundaryPoint side 0
  have hprodRe : 0 < (x * y).re := by
    rw [hprod]
    exact model.connectorLocalBoundaryRadicand_re_pos 0
  have hprodIm : (x * y).im = 0 := by
    rw [hprod]
    unfold ChapterVIDPrincipalConnectorModel.connectorLocalBoundaryRadicand
    exact Complex.ofReal_im _
  have hlocal : (localParameter side : ℝ) ∈ collarInterval side := by
    cases side <;> norm_num [localParameter, collarInterval]
  have hyRe : 0 < y.re := by
    change 0 < (model.rectangleFactorMinus side
      (connectorPathPoint model.toChapterVIDPrincipalConnectorModel
        (localParameter side))).re
    exact companion_re_pos_on_collar model.toChapterVIDPrincipalConnectorModel
      derivativeRun curvatureRun side (localParameter side) hlocal
  have harg := arg_add_mem_Ioc_of_mul_re_pos_im_zero_of_right hprodRe hprodIm hyRe
  have hne := factors_ne_zero certificate (localParameter side)
  have hmul := sqrt_mul_of_arg_add_mem hne.1 hne.2 harg
  change Complex.sqrt x * Complex.sqrt y = model.connectorLocalBoundaryRoot 0
  rw [← hmul, hprod]
  rfl

/-- A scale-aware crossing certificate fixes the local sign of any outer-normalized connector
sheet. -/
theorem connectorSheet_eq_localBoundaryRoot_zero
    (outerRun : ChapterVIDOuterArcPolarCompiledGrid.CompiledRunVerdict)
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDAnchoredConnectorModel massProduct b d)
    (bulkRun : ChapterVIDConnectorFactorBulkReference.ReferenceCompiledRunVerdict)
    (derivativeRun :
      ChapterVIDConnectorFactorDerivativeReference.ReferenceCompiledRunVerdict)
    (curvatureRun :
      ChapterVIDConnectorFactorSecondDerivativeReference.ReferenceCompiledRunVerdict)
    (side : ChapterVIDOuterArcSide)
    (crossing : PositiveCrossingCertificate
      model.toChapterVIDPrincipalConnectorModel side)
    (certificate : ChapterVIDConnectorCompiledCertificate
      model.toChapterVIDPrincipalConnectorModel side)
    (sheet : ChapterVIContinuousSquareRootSheet
      (model.toChapterVIDPrincipalConnectorModel.rectangleRadicand side))
    (houter : ∀ s : I,
      sheet.root (model.connectorBoundaryPoint side s) =
        model.connectorOuterBoundaryRoot outerRun side s) :
    sheet.root (model.connectorLocalBoundaryPoint side 0) =
      model.connectorLocalBoundaryRoot 0 := by
  let restricted : ChapterVIContinuousSquareRootSheet
      (fun t : I ↦ model.rectangleRadicand side
        (connectorPathPoint model.toChapterVIDPrincipalConnectorModel t)) := {
    root := fun t ↦ sheet.root
      (connectorPathPoint model.toChapterVIDPrincipalConnectorModel t)
    continuous_root := sheet.continuous_root.comp
      (continuous_const.prodMk continuous_id)
    root_sq := fun t ↦ sheet.root_sq _ }
  have hbase : restricted.root (outerParameter side) =
      (factorPathSheet model bulkRun derivativeRun curvatureRun side crossing).root
        (outerParameter side) := by
    rw [show restricted.root (outerParameter side) =
        sheet.root (model.connectorBoundaryPoint side 0) by simp [restricted]]
    rw [houter 0,
      factorPathSheet_outer model bulkRun derivativeRun curvatureRun side crossing certificate]
    change Complex.sqrt
        (chapterVIDOuterArcRadicand side (model.connectorOuterBoundaryPoint side 0)) =
      Complex.sqrt
        (model.rectangleRadicand side
          (connectorPathPoint model.toChapterVIDPrincipalConnectorModel (outerParameter side)))
    rw [← model.rectangleRadicand_connectorBoundaryPoint side 0]
    simp
  have hall := restricted.root_eq_of_eq_at
    (factorPathSheet model bulkRun derivativeRun curvatureRun side crossing)
    (fun t ↦ by
      have hne := factors_ne_zero certificate t
      exact mul_ne_zero hne.1 hne.2)
    (outerParameter side) hbase
  calc
    sheet.root (model.connectorLocalBoundaryPoint side 0) =
        restricted.root (localParameter side) := by simp [restricted]
    _ = (factorPathSheet model bulkRun derivativeRun curvatureRun side crossing).root
        (localParameter side) := congrFun hall (localParameter side)
    _ = model.connectorLocalBoundaryRoot 0 :=
      factorPathSheet_local model bulkRun derivativeRun curvatureRun side crossing certificate

/-- Both scale-aware crossing verdicts complete the seam-compatible connector pair. -/
theorem exists_seamCompatiblePair
    (outerRun : ChapterVIDOuterArcPolarCompiledGrid.CompiledRunVerdict)
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDAnchoredConnectorModel massProduct b d)
    (bulkRun : ChapterVIDConnectorFactorBulkReference.ReferenceCompiledRunVerdict)
    (derivativeRun :
      ChapterVIDConnectorFactorDerivativeReference.ReferenceCompiledRunVerdict)
    (curvatureRun :
      ChapterVIDConnectorFactorSecondDerivativeReference.ReferenceCompiledRunVerdict)
    (initialCrossing : PositiveCrossingCertificate
      model.toChapterVIDPrincipalConnectorModel .initial)
    (finalCrossing : PositiveCrossingCertificate
      model.toChapterVIDPrincipalConnectorModel .final)
    (initialCertificate : ChapterVIDConnectorCompiledCertificate
      model.toChapterVIDPrincipalConnectorModel .initial)
    (finalCertificate : ChapterVIDConnectorCompiledCertificate
      model.toChapterVIDPrincipalConnectorModel .final) :
    Nonempty (ChapterVIDPrincipalConnectorModel.SeamCompatibleCertifiedConnectorPair
      outerRun model.toChapterVIDPrincipalConnectorModel) := by
  obtain ⟨pair⟩ := ChapterVIDPrincipalConnectorModel.exists_certifiedConnectorPair
    outerRun model.toChapterVIDPrincipalConnectorModel initialCertificate finalCertificate
  exact ⟨{
    pair := pair
    initial_local_at_zero := connectorSheet_eq_localBoundaryRoot_zero outerRun model bulkRun
      derivativeRun curvatureRun .initial initialCrossing initialCertificate
      pair.initialSheet pair.initial_outer
    final_local_at_zero := connectorSheet_eq_localBoundaryRoot_zero outerRun model bulkRun
      derivativeRun curvatureRun .final finalCrossing finalCertificate
      pair.finalSheet pair.final_outer }⟩

/-- End-to-end seam theorem, conditional only on the two scale-aware compiled crossing
verdicts. -/
theorem exists_seamCompatibleContribution_tendsto
    (outerRun : ChapterVIDOuterArcPolarCompiledGrid.CompiledRunVerdict)
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDAnchoredConnectorModel massProduct b d)
    (bulkRun : ChapterVIDConnectorFactorBulkReference.ReferenceCompiledRunVerdict)
    (derivativeRun :
      ChapterVIDConnectorFactorDerivativeReference.ReferenceCompiledRunVerdict)
    (curvatureRun :
      ChapterVIDConnectorFactorSecondDerivativeReference.ReferenceCompiledRunVerdict)
    (initialCrossing : PositiveCrossingCertificate
      model.toChapterVIDPrincipalConnectorModel .initial)
    (finalCrossing : PositiveCrossingCertificate
      model.toChapterVIDPrincipalConnectorModel .final)
    (initialCertificate : ChapterVIDConnectorCompiledCertificate
      model.toChapterVIDPrincipalConnectorModel .initial)
    (finalCertificate : ChapterVIDConnectorCompiledCertificate
      model.toChapterVIDPrincipalConnectorModel .final) :
    ∃ compatible : ChapterVIDPrincipalConnectorModel.SeamCompatibleCertifiedConnectorPair
        outerRun model.toChapterVIDPrincipalConnectorModel,
      Filter.Tendsto
        (fun k : ℝ ↦ (-Real.log k)⁻¹ • compatible.fivePieceContribution k)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds ((2 * Real.pi * Complex.I : ℂ)⁻¹ *
          chapterVIDPrincipalMorseAmplitude massProduct b d (0, 0))) := by
  obtain ⟨compatible⟩ := exists_seamCompatiblePair outerRun model bulkRun derivativeRun
    curvatureRun initialCrossing finalCrossing initialCertificate finalCertificate
  exact ⟨compatible, compatible.tendsto_fivePiece_inv_neg_log_smul⟩

/-- Fully compiled-facing form of the seam theorem.  The two crossing predicates are recovered
from the exact zero-returning LeanCompCert artifacts before the analytic assembly is invoked. -/
theorem exists_seamCompatibleContribution_tendsto_of_compiledCrossingRuns
    (outerRun : ChapterVIDOuterArcPolarCompiledGrid.CompiledRunVerdict)
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDAnchoredConnectorModel massProduct b d)
    (bulkRun : ChapterVIDConnectorFactorBulkReference.ReferenceCompiledRunVerdict)
    (derivativeRun :
      ChapterVIDConnectorFactorDerivativeReference.ReferenceCompiledRunVerdict)
    (curvatureRun :
      ChapterVIDConnectorFactorSecondDerivativeReference.ReferenceCompiledRunVerdict)
    {initialPrecision finalPrecision : ℕ}
    {initialName finalName : String}
    {initialData : CompiledCrossingData
      model.toChapterVIDPrincipalConnectorModel .initial initialPrecision}
    {finalData : CompiledCrossingData
      model.toChapterVIDPrincipalConnectorModel .final finalPrecision}
    (initialRun : CompiledCrossingRunVerdict initialName initialData)
    (finalRun : CompiledCrossingRunVerdict finalName finalData)
    (initialCertificate : ChapterVIDConnectorCompiledCertificate
      model.toChapterVIDPrincipalConnectorModel .initial)
    (finalCertificate : ChapterVIDConnectorCompiledCertificate
      model.toChapterVIDPrincipalConnectorModel .final) :
    ∃ compatible : ChapterVIDPrincipalConnectorModel.SeamCompatibleCertifiedConnectorPair
        outerRun model.toChapterVIDPrincipalConnectorModel,
      Filter.Tendsto
        (fun k : ℝ ↦ (-Real.log k)⁻¹ • compatible.fivePieceContribution k)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds ((2 * Real.pi * Complex.I : ℂ)⁻¹ *
          chapterVIDPrincipalMorseAmplitude massProduct b d (0, 0))) :=
  exists_seamCompatibleContribution_tendsto outerRun model bulkRun derivativeRun curvatureRun
    initialRun.toPositiveCrossingCertificate finalRun.toPositiveCrossingCertificate
    initialCertificate finalCertificate

/-- Preferred end-to-end compiled route: the artifacts certify oriented real derivatives, and
ordinary Lean calculus converts those signs to the two crossing verdicts before assembling the
seams. -/
theorem exists_seamCompatibleContribution_tendsto_of_compiledRealDerivativeRuns
    (outerRun : ChapterVIDOuterArcPolarCompiledGrid.CompiledRunVerdict)
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDAnchoredConnectorModel massProduct b d)
    (bulkRun : ChapterVIDConnectorFactorBulkReference.ReferenceCompiledRunVerdict)
    (derivativeRun :
      ChapterVIDConnectorFactorDerivativeReference.ReferenceCompiledRunVerdict)
    (curvatureRun :
      ChapterVIDConnectorFactorSecondDerivativeReference.ReferenceCompiledRunVerdict)
    {initialPrecision finalPrecision : ℕ}
    {initialName finalName : String}
    {initialData : CompiledRealDerivativeData
      model.toChapterVIDPrincipalConnectorModel .initial initialPrecision}
    {finalData : CompiledRealDerivativeData
      model.toChapterVIDPrincipalConnectorModel .final finalPrecision}
    (initialRun : CompiledRealDerivativeRunVerdict initialName initialData)
    (finalRun : CompiledRealDerivativeRunVerdict finalName finalData)
    (initialCertificate : ChapterVIDConnectorCompiledCertificate
      model.toChapterVIDPrincipalConnectorModel .initial)
    (finalCertificate : ChapterVIDConnectorCompiledCertificate
      model.toChapterVIDPrincipalConnectorModel .final) :
    ∃ compatible : ChapterVIDPrincipalConnectorModel.SeamCompatibleCertifiedConnectorPair
        outerRun model.toChapterVIDPrincipalConnectorModel,
      Filter.Tendsto
        (fun k : ℝ ↦ (-Real.log k)⁻¹ • compatible.fivePieceContribution k)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds ((2 * Real.pi * Complex.I : ℂ)⁻¹ *
          chapterVIDPrincipalMorseAmplitude massProduct b d (0, 0))) :=
  exists_seamCompatibleContribution_tendsto outerRun model bulkRun derivativeRun curvatureRun
    (initialRun.toOrientedRealDerivativeCertificate.toPositiveCrossingCertificate
      model derivativeRun curvatureRun .initial)
    (finalRun.toOrientedRealDerivativeCertificate.toPositiveCrossingCertificate
      model derivativeRun curvatureRun .final)
    initialCertificate finalCertificate

/-- Scale-normalized end-to-end compiled route.  This is the preferred terminal interface: the
compiled rows retain `L + distance²`, Lean removes that strictly positive scale, and the existing
calculus and seam assembly consume the resulting oriented derivatives. -/
theorem exists_seamCompatibleContribution_tendsto_of_compiledNormalizedRealDerivativeRuns
    (outerRun : ChapterVIDOuterArcPolarCompiledGrid.CompiledRunVerdict)
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDAnchoredConnectorModel massProduct b d)
    (bulkRun : ChapterVIDConnectorFactorBulkReference.ReferenceCompiledRunVerdict)
    (derivativeRun :
      ChapterVIDConnectorFactorDerivativeReference.ReferenceCompiledRunVerdict)
    (curvatureRun :
      ChapterVIDConnectorFactorSecondDerivativeReference.ReferenceCompiledRunVerdict)
    {initialPrecision finalPrecision : ℕ}
    {initialName finalName : String}
    {initialData : CompiledNormalizedRealDerivativeData model .initial initialPrecision}
    {finalData : CompiledNormalizedRealDerivativeData model .final finalPrecision}
    (initialRun : CompiledNormalizedRealDerivativeRunVerdict initialName initialData)
    (finalRun : CompiledNormalizedRealDerivativeRunVerdict finalName finalData)
    (initialCertificate : ChapterVIDConnectorCompiledCertificate
      model.toChapterVIDPrincipalConnectorModel .initial)
    (finalCertificate : ChapterVIDConnectorCompiledCertificate
      model.toChapterVIDPrincipalConnectorModel .final) :
    ∃ compatible : ChapterVIDPrincipalConnectorModel.SeamCompatibleCertifiedConnectorPair
        outerRun model.toChapterVIDPrincipalConnectorModel,
      Filter.Tendsto
        (fun k : ℝ ↦ (-Real.log k)⁻¹ • compatible.fivePieceContribution k)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds ((2 * Real.pi * Complex.I : ℂ)⁻¹ *
          chapterVIDPrincipalMorseAmplitude massProduct b d (0, 0))) :=
  exists_seamCompatibleContribution_tendsto outerRun model bulkRun derivativeRun curvatureRun
    (initialRun.toNormalizedRealDerivativeCertificate
      |>.toOrientedRealDerivativeCertificate model .initial
      |>.toPositiveCrossingCertificate model derivativeRun curvatureRun .initial)
    (finalRun.toNormalizedRealDerivativeCertificate
      |>.toOrientedRealDerivativeCertificate model .final
      |>.toPositiveCrossingCertificate model derivativeRun curvatureRun .final)
    initialCertificate finalCertificate

/-- Conditional compiled curvature route. This theorem records the sound assembly if such
campaigns are supplied; it does not assert that nonnegative curvature is the feasible numerical
condition for the selected inverse-Morse endpoints. -/
theorem exists_seamCompatibleContribution_tendsto_of_compiledRealCurvatureRuns
    (outerRun : ChapterVIDOuterArcPolarCompiledGrid.CompiledRunVerdict)
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDAnchoredConnectorModel massProduct b d)
    (bulkRun : ChapterVIDConnectorFactorBulkReference.ReferenceCompiledRunVerdict)
    (derivativeRun :
      ChapterVIDConnectorFactorDerivativeReference.ReferenceCompiledRunVerdict)
    (curvatureRun :
      ChapterVIDConnectorFactorSecondDerivativeReference.ReferenceCompiledRunVerdict)
    {initialPrecision finalPrecision : ℕ}
    {initialName finalName : String}
    {initialData : CompiledRealCurvatureData
      model.toChapterVIDPrincipalConnectorModel .initial initialPrecision}
    {finalData : CompiledRealCurvatureData
      model.toChapterVIDPrincipalConnectorModel .final finalPrecision}
    (initialRun : CompiledRealCurvatureRunVerdict initialName initialData)
    (finalRun : CompiledRealCurvatureRunVerdict finalName finalData)
    (initialCertificate : ChapterVIDConnectorCompiledCertificate
      model.toChapterVIDPrincipalConnectorModel .initial)
    (finalCertificate : ChapterVIDConnectorCompiledCertificate
      model.toChapterVIDPrincipalConnectorModel .final) :
    ∃ compatible : ChapterVIDPrincipalConnectorModel.SeamCompatibleCertifiedConnectorPair
        outerRun model.toChapterVIDPrincipalConnectorModel,
      Filter.Tendsto
        (fun k : ℝ ↦ (-Real.log k)⁻¹ • compatible.fivePieceContribution k)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds ((2 * Real.pi * Complex.I : ℂ)⁻¹ *
          chapterVIDPrincipalMorseAmplitude massProduct b d (0, 0))) :=
  exists_seamCompatibleContribution_tendsto outerRun model bulkRun derivativeRun curvatureRun
    (initialRun.toNonnegativeRealCurvatureCertificate
      |>.toOrientedRealDerivativeCertificate model .initial
      |>.toPositiveCrossingCertificate model derivativeRun curvatureRun .initial)
    (finalRun.toNonnegativeRealCurvatureCertificate
      |>.toOrientedRealDerivativeCertificate model .final
      |>.toPositiveCrossingCertificate model derivativeRun curvatureRun .final)
    initialCertificate finalCertificate

end ChapterVIDConnectorFactorCrossing
end PoincareChapterVI
