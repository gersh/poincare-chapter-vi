/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.ChapterVIDRootConnectors
import PoincareChapterVI.ChapterVIDRadialClusteredCompiledGrid

/-!
# Explicit input bounds for the D connector certificates

The inverse Morse endpoint is noncomputable, but the global root model was deliberately shrunk
so that every such endpoint lies in a fixed ball about the collision lift. Combining that
analytic ball with the already checked collision-radius interval gives one concrete dyadic
rectangle containing every local endpoint on either connector.

This does not give a full connector grid by itself. It removes the need to evaluate the inverse
Morse map merely to obtain a first certified box. The final theorem below records the structural
limitation: the symmetric analytic ball also contains the collision lift, where the critical
radicand vanishes. A successful endpoint-adjacent certificate therefore needs directional Morse
information, not merely finer subdivision of this rectangle.
-/

noncomputable section

namespace PoincareChapterVI

open scoped unitInterval

namespace ChapterVIDConnectorInputBounds

abbrev Rectangle := ChapterVISignedDyadicComplexRectangle 20

def terminalIndex : Fin 28 := ⟨27, by norm_num⟩

/-- The parameter-root box from the final clustered radial cell. -/
def terminalZetaRectangle : Rectangle :=
  ⟨(ChapterVIDRadialClusteredCompiledGrid.trace terminalIndex).qCubeRoot,
    ChapterVISignedDyadicInterval.pointInt 20 0⟩

/-- The local-facing outer endpoint box from the final clustered radial cell. -/
def terminalOuterRectangle (side : ChapterVIDOuterArcSide) : Rectangle :=
  let radius := (ChapterVIDRadialClusteredCompiledGrid.trace terminalIndex).radius
  let zero := ChapterVISignedDyadicInterval.pointInt 20 0
  match side with
  | .initial => ⟨zero, radius⟩
  | .final => ⟨zero, radius.neg⟩

/-- Uniform dyadic enclosure of both noncomputable local inverse-Morse endpoints. -/
def localEndpointRectangle : Rectangle where
  real := ⟨-471080, -157023⟩
  imag := ⟨-157027, 157027⟩

/-- The coarse symmetric enclosure contains the collision point itself. This explains why it is
useful as an input bound but cannot, on its own, prove radicand separation all the way to a local
connector endpoint. -/
theorem localEndpointRectangle_contains_collisionLift :
    localEndpointRectangle.Contains chapterVIDCollisionLift := by
  have hradius := ChapterVIDRadialClusteredCompiledGrid.collisionRadius_contains
  change (314047 : ℝ) / (2 : ℝ) ^ 20 ≤ ‖chapterVIDCollisionLift‖ ∧
    ‖chapterVIDCollisionLift‖ ≤ (314053 : ℝ) / (2 : ℝ) ^ 20 at hradius
  have hcollision := chapterVIDCollisionLift_eq_neg_norm
  simp only [localEndpointRectangle,
    ChapterVISignedDyadicComplexRectangle.Contains,
    ChapterVISignedDyadicInterval.Contains,
    ChapterVISignedDyadicInterval.toRealInterval,
    ChapterVISignedDyadicInterval.scale]
  rw [hcollision]
  simp only [Complex.neg_re, Complex.ofReal_re, Complex.neg_im, Complex.ofReal_im, neg_zero]
  constructor
  · constructor <;> norm_num at ⊢ hradius <;> linarith
  · constructor <;> norm_num

/-- Every endpoint used by either affine connector belongs to the explicit dyadic box above. -/
theorem localEndpointRectangle_contains
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalGlobalRootModel massProduct b d)
    (side : ChapterVIDOuterArcSide) (k : ℝ)
    (hk : k ∈ Set.Icc 0 model.δ) :
    localEndpointRectangle.Contains (model.localConnectorEndpoint side k) := by
  have hbounds := model.localConnectorEndpoint_component_bounds side k hk
  have hradius := ChapterVIDRadialClusteredCompiledGrid.collisionRadius_contains
  change (314047 : ℝ) / (2 : ℝ) ^ 20 ≤ ‖chapterVIDCollisionLift‖ ∧
    ‖chapterVIDCollisionLift‖ ≤ (314053 : ℝ) / (2 : ℝ) ^ 20 at hradius
  simp only [localEndpointRectangle,
    ChapterVISignedDyadicComplexRectangle.Contains,
    ChapterVISignedDyadicInterval.Contains,
    ChapterVISignedDyadicInterval.toRealInterval,
    ChapterVISignedDyadicInterval.scale]
  constructor
  · constructor
    · change ((-471080 : ℤ) : ℝ) / (2 : ℝ) ^ 20 ≤
        (model.localConnectorEndpoint side k).re
      linarith [hbounds.1, hradius.2]
    · change (model.localConnectorEndpoint side k).re ≤
        ((-157023 : ℤ) : ℝ) / (2 : ℝ) ^ 20
      linarith [hbounds.2.1, hradius.1]
  · constructor
    · change ((-157027 : ℤ) : ℝ) / (2 : ℝ) ^ 20 ≤
        (model.localConnectorEndpoint side k).im
      linarith [hbounds.2.2.1, hradius.2]
    · change (model.localConnectorEndpoint side k).im ≤
        ((157027 : ℤ) : ℝ) / (2 : ℝ) ^ 20
      linarith [hbounds.2.2.2, hradius.2]

/-- Shrinking the connector model into the terminal radial cell makes one fixed compiled box
contain its parameter root over the whole connector family. -/
theorem terminalZetaRectangle_contains
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d) (s : I) :
    terminalZetaRectangle.Contains
      (chapterVIDCriticalParameterRootAtD (model.criticalValue s : ℂ)) := by
  let parameter := chapterVIDCriticalToGlobalParameter (model.criticalValue s)
  have hupper : (parameter : ℝ) ≤
      chapterVICubicClusterNode 28 (terminalIndex + 1) := by
    simpa [terminalIndex, chapterVICubicClusterNode] using parameter.property.2
  have houtputs := ChapterVIDRadialClusteredCompiledGrid.outputs_contain_cell terminalIndex
    (parameter := parameter)
    (model.globalParameter_mem_terminalCell (model.criticalValue s)
      (model.criticalValue_mem s)) hupper
  have heq := model.parameterRoot_eq_global (model.criticalValue s)
    (model.criticalValue_mem s)
  rw [heq,
    chapterVIDCommonParameterRootPath_eq_certificateValue]
  constructor
  · simpa [terminalZetaRectangle] using houtputs.1
  · simp [terminalZetaRectangle, ChapterVISignedDyadicInterval.Contains,
      ChapterVISignedDyadicInterval.toRealInterval, ChapterVIRealInterval.Contains,
      ChapterVISignedDyadicInterval.pointInt, ChapterVISignedDyadicInterval.scale]

/-- The same terminal radial trace encloses the local-facing endpoint of either outer quarter. -/
theorem terminalOuterRectangle_contains
    {massProduct : ℂ} {b d : ℤ}
    (model : ChapterVIDPrincipalConnectorModel massProduct b d)
    (side : ChapterVIDOuterArcSide) (s : I) :
    terminalOuterRectangle side |>.Contains
      (model.rootModel.outerConnectorEndpoint side (model.criticalValue s)) := by
  let parameter := chapterVIDCriticalToGlobalParameter (model.criticalValue s)
  have hupper : (parameter : ℝ) ≤
      chapterVICubicClusterNode 28 (terminalIndex + 1) := by
    simpa [terminalIndex, chapterVICubicClusterNode] using parameter.property.2
  have houtputs := ChapterVIDRadialClusteredCompiledGrid.outputs_contain_cell terminalIndex
    (parameter := parameter)
    (model.globalParameter_mem_terminalCell (model.criticalValue s)
      (model.criticalValue_mem s)) hupper
  cases side with
  | initial =>
      constructor
      · simp [terminalOuterRectangle,
          ChapterVIDPrincipalGlobalRootModel.outerConnectorEndpoint,
          chapterVIDOuterArcPoint,
          ChapterVISignedDyadicInterval.Contains,
          ChapterVISignedDyadicInterval.toRealInterval,
          ChapterVIRealInterval.Contains,
          ChapterVISignedDyadicInterval.pointInt,
          ChapterVISignedDyadicInterval.scale]
      · simpa [terminalOuterRectangle,
          ChapterVIDPrincipalGlobalRootModel.outerConnectorEndpoint,
          chapterVIDOuterArcPoint, parameter] using houtputs.2
  | final =>
      constructor
      · simp [terminalOuterRectangle,
          ChapterVIDPrincipalGlobalRootModel.outerConnectorEndpoint,
          chapterVIDOuterArcPoint,
          ChapterVISignedDyadicInterval.Contains,
          ChapterVISignedDyadicInterval.toRealInterval,
          ChapterVIRealInterval.Contains,
          ChapterVISignedDyadicInterval.pointInt,
          ChapterVISignedDyadicInterval.scale]
      · simpa [terminalOuterRectangle,
          ChapterVIDPrincipalGlobalRootModel.outerConnectorEndpoint,
          chapterVIDOuterArcPoint, parameter] using
          ChapterVISignedDyadicInterval.neg_contains houtputs.2

end ChapterVIDConnectorInputBounds

end PoincareChapterVI
