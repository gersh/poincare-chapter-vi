/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.ChapterVIDConnectorIntegral

/-!
# Analytic endpoint collars for the D connectors

The Cartesian interval trace deliberately treats the inverse-Morse endpoint as an opaque box.
Such a box necessarily contains the collision lift and therefore cannot certify cells adjacent to
the local boundary.  The missing endpoint region is analytic rather than computational: on that
boundary the exact Morse identity makes the radicand the positive real number `k + L²`.

This file uses that uniform lower bound and Heine--Cantor on the compact connector square to
produce one positive-width collar on which the literal root-coordinate radicand is nonzero.  No
evaluation or interval enclosure of the inverse Morse map occurs.
-/

noncomputable section

open Set Topology
open scoped unitInterval

namespace PoincareChapterVI

namespace ChapterVIDPrincipalConnectorModel

/-- Distance in the affine connector parameter from the boundary shared with the local Morse
segment. -/
def connectorLocalBoundaryDistance
    {massProduct : ℂ} {b d : ℤ}
    (_model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) (point : I × I) : ℝ :=
  match side with
  | .initial => 1 - (point.2 : ℝ)
  | .final => point.2

theorem connectorLocalBoundaryDistance_nonneg
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) (point : I × I) :
    0 ≤ model.connectorLocalBoundaryDistance side point := by
  cases side
  · exact sub_nonneg.mpr point.2.property.2
  · exact point.2.property.1

theorem dist_connectorLocalBoundaryPoint
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) (point : I × I) :
    dist point (model.connectorLocalBoundaryPoint side point.1) =
      model.connectorLocalBoundaryDistance side point := by
  cases side
  · change dist point (point.1, 1) = 1 - (point.2 : ℝ)
    rw [Prod.dist_eq]
    simp only [dist_self]
    rw [max_eq_right (dist_nonneg : 0 ≤ dist point.2 (1 : I))]
    change dist (point.2 : ℝ) 1 = 1 - (point.2 : ℝ)
    rw [Real.dist_eq]
    rw [abs_of_nonpos]
    · ring
    · linarith [point.2.property.2]
  · change dist point (point.1, 0) = (point.2 : ℝ)
    rw [Prod.dist_eq]
    simp only [dist_self]
    rw [max_eq_right (dist_nonneg : 0 ≤ dist point.2 (0 : I))]
    change dist (point.2 : ℝ) 0 = (point.2 : ℝ)
    rw [Real.dist_eq]
    rw [abs_of_nonneg (by linarith [point.2.property.1])]
    ring

/-- The exact Morse normal form gives a lower bound independent of the critical-value
parameter along the complete local boundary. -/
theorem norm_rectangleRadicand_connectorLocalBoundaryPoint_ge
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) (s : I) :
    model.rootModel.L ^ 2 ≤
      ‖model.rectangleRadicand side (model.connectorLocalBoundaryPoint side s)‖ := by
  rw [model.rectangleRadicand_connectorLocalBoundaryPoint]
  have hk : 0 ≤ model.criticalValue s := (model.criticalValue_mem s).1
  have hL : 0 ≤ model.rootModel.L ^ 2 := sq_nonneg _
  simp only [connectorLocalBoundaryRadicand, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_nonneg]
  · linarith
  · positivity

/-- Semantic analytic certificate for the part of a connector adjacent to the local Morse
boundary.  Unlike the compiled bulk certificate, this object contains no numerical trace. -/
structure ConnectorEndpointCollar
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) where
  width : ℝ
  width_pos : 0 < width
  width_le_one : width ≤ 1
  radicand_ne_zero : ∀ point : I × I,
    model.connectorLocalBoundaryDistance side point < width →
      model.rectangleRadicand side point ≠ 0

/-- A power-of-two endpoint collar suitable for a finite grid boundary. -/
structure DyadicConnectorEndpointCollar
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) where
  exponent : ℕ
  radicand_ne_zero : ∀ point : I × I,
    model.connectorLocalBoundaryDistance side point < (1 / 2 : ℝ) ^ exponent →
      model.rectangleRadicand side point ≠ 0

def DyadicConnectorEndpointCollar.toEndpointCollar
    {massProduct : ℂ} {b d : ℤ}
    {model : ChapterVIDPrincipalConnectorModel massProduct b d}
    {side : ChapterVIDOuterArcSide}
    (collar : DyadicConnectorEndpointCollar model side) :
    ConnectorEndpointCollar model side where
  width := (1 / 2 : ℝ) ^ collar.exponent
  width_pos := pow_pos (by norm_num) _
  width_le_one := pow_le_one₀ (by norm_num) (by norm_num)
  radicand_ne_zero := collar.radicand_ne_zero

/-- A positive-width collar of the local boundary is free of zeros of Poincare's literal
root-coordinate radicand.  The width is uniform in the moving critical value. -/
theorem exists_connectorLocalEndpointCollar
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) :
    ∃ width : ℝ, 0 < width ∧ width ≤ 1 ∧
      ∀ point : I × I,
        model.connectorLocalBoundaryDistance side point < width →
          model.rectangleRadicand side point ≠ 0 := by
  have hcontinuous : Continuous (model.rectangleRadicand side) :=
    model.continuous_rectangleRadicand_of_coordinate_ne_zero side
      (model.rectanglePoint_ne_zero side)
  have huniform : UniformContinuous (model.rectangleRadicand side) :=
    CompactSpace.uniformContinuous_of_continuous hcontinuous
  have hLsq : 0 < model.rootModel.L ^ 2 := sq_pos_of_pos model.rootModel.L_pos
  obtain ⟨δ, hδ, hclose⟩ := Metric.uniformContinuous_iff.mp huniform
    (model.rootModel.L ^ 2 / 2) (half_pos hLsq)
  refine ⟨min δ 1, lt_min hδ zero_lt_one, min_le_right _ _, ?_⟩
  intro point hpoint
  let boundary := model.connectorLocalBoundaryPoint side point.1
  have hdistance : dist point boundary < δ := by
    rw [show boundary = model.connectorLocalBoundaryPoint side point.1 from rfl,
      model.dist_connectorLocalBoundaryPoint side point]
    exact hpoint.trans_le (min_le_left _ _)
  have hradicandDistance := hclose hdistance
  have hboundaryLower :=
    model.norm_rectangleRadicand_connectorLocalBoundaryPoint_ge side point.1
  intro hzero
  rw [hzero, dist_zero_left] at hradicandDistance
  linarith

/-- Package the uniform-continuity theorem in the certificate interface consumed by a hybrid
analytic/compiled connector grid. -/
theorem exists_endpointCollar
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) :
    Nonempty (ConnectorEndpointCollar model side) := by
  obtain ⟨width, hwidth, hwidthOne, hnonzero⟩ :=
    model.exists_connectorLocalEndpointCollar side
  exact ⟨{
    width := width
    width_pos := hwidth
    width_le_one := hwidthOne
    radicand_ne_zero := hnonzero }⟩

/-- Every analytic endpoint collar contains a power-of-two subcollar. Thus the analytic/compiled
split can always be placed on a finite dyadic mesh, even though this compactness proof does not
compute the required exponent. -/
theorem exists_dyadicEndpointCollar
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) :
    Nonempty (DyadicConnectorEndpointCollar model side) := by
  obtain ⟨collar⟩ := model.exists_endpointCollar side
  obtain ⟨exponent, hexponent⟩ := exists_pow_lt_of_lt_one collar.width_pos
    (by norm_num : (1 / 2 : ℝ) < 1)
  exact ⟨{
    exponent := exponent
    radicand_ne_zero := by
      intro point hpoint
      exact collar.radicand_ne_zero point (hpoint.trans hexponent) }⟩

end ChapterVIDPrincipalConnectorModel

end PoincareChapterVI
