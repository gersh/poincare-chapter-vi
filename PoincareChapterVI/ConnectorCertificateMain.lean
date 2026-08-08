import PoincareChapterVI.ChapterVIDConnectorSeamCompiledGrid

/-!
# Reference runner for the Chapter VI connector certificates

This executable exercises exactly the proposal and integer-checking path used by the eventual
compiled connector artifacts.  It is intentionally not a proof: it reports whether a proposed
Cartesian trace exists, whether its output rectangle has a signed component excluding zero, and
whether all generated signed-integer claims pass the reference checker.  The `reference-coarse`
mode uses the proved endpoint enclosure.  The `scan-idealized` mode substitutes a hypothetical
tighter box around the collision lift and is only a feasibility diagnostic.
-/

open PoincareChapterVI
open PoincareChapterVI.ChapterVILeanCompCertBatch
open PoincareChapterVI.ChapterVIDConnectorCompiledGrid
open LeanCompCert.Ports.SignedProductClaims

namespace PoincareChapterVI.ConnectorCertificateMain

abbrev Interval := ChapterVISignedDyadicInterval 20
abbrev Rectangle := ChapterVISignedDyadicComplexRectangle 20

def scale : Nat := 2 ^ 20

def parameterInterval (cells index : Nat) : Interval :=
  ⟨Int.ofNat (index * scale / cells), Int.ofNat ((index + 1) * scale / cells)⟩

def outerRectangle (side : ChapterVIDOuterArcSide) : Rectangle :=
  ChapterVIDConnectorInputBounds.terminalOuterRectangle side

def zetaRectangle : Rectangle :=
  ChapterVIDConnectorInputBounds.terminalZetaRectangle

def testLocalEndpointRectangle (margin : Nat) : Rectangle :=
  ⟨⟨-314053 - Int.ofNat margin, -314047 + Int.ofNat margin⟩,
    ⟨-Int.ofNat margin, Int.ofNat margin⟩⟩

def testDirectionalEndpointRectangle (side : ChapterVIDOuterArcSide)
    (displacement margin : Nat) : Rectangle :=
  let center := match side with
    | .initial => Int.ofNat displacement
    | .final => -Int.ofNat displacement
  ⟨⟨-314053 - Int.ofNat margin, -314047 + Int.ofNat margin⟩,
    ⟨center - Int.ofNat margin, center + Int.ofNat margin⟩⟩

def testSourceRectangle (side : ChapterVIDOuterArcSide) (outer localBox : Rectangle) : Rectangle :=
  match side with
  | .initial => outer
  | .final => localBox

def testTargetRectangle (side : ChapterVIDOuterArcSide) (outer localBox : Rectangle) : Rectangle :=
  match side with
  | .initial => localBox
  | .final => outer

def separation? (rectangle : Rectangle) : Option ChapterVIComplexZeroSeparation :=
  if 0 < rectangle.real.lower then some .realPositive
  else if rectangle.real.upper < 0 then some .realNegative
  else if 0 < rectangle.imag.lower then some .imagPositive
  else if rectangle.imag.upper < 0 then some .imagNegative
  else none

/-- Separation suitable for the principal square-root slit plane.  A negative-real rectangle is
accepted only through a strict imaginary sign, never merely because it avoids zero. -/
def slitSeparation? (rectangle : Rectangle) :
    Option ChapterVIDConnectorSeamCompiledGrid.SlitPlaneSeparation :=
  if 0 < rectangle.real.lower then some .realPositive
  else if 0 < rectangle.imag.lower then some .imagPositive
  else if rectangle.imag.upper < 0 then some .imagNegative
  else none

structure Stats where
  total : Nat := 0
  argumentRejected : Nat := 0
  unseparated : Nat := 0
  notPositiveReal : Nat := 0
  meetsNegativeRealRay : Nat := 0
  meetsPositiveRealRay : Nat := 0
  meetsNegativeImagRay : Nat := 0
  meetsPositiveImagRay : Nat := 0
  plusMeetsNegativeRealRay : Nat := 0
  minusMeetsNegativeRealRay : Nat := 0
  failedClaims : Nat := 0
  deriving Repr

def sideName : ChapterVIDOuterArcSide → String
  | .initial => "initial"
  | .final => "final"

def runReference (cells : Nat) (localBox : ChapterVIDOuterArcSide → Rectangle) : IO UInt32 := do
  if cells = 0 then
    IO.eprintln "error: CELLS must be positive"
    return 1
  let mut stats : Stats := {}
  for side in [.initial, .final] do
    for index in List.range cells do
        stats := { stats with total := stats.total + 1 }
        let outer := outerRectangle side
        let source := testSourceRectangle side outer (localBox side)
        let target := testTargetRectangle side outer (localBox side)
        let parameter := parameterInterval cells index
        let coordinateTrace := ChapterVILeanCompCertProposals.lineMapTrace source target parameter
        match ChapterVILeanCompCertProposals.cartesianRadicandTrace?
            zetaRectangle coordinateTrace.output
            ChapterVIDOuterArcPolarCompiledGrid.exponentialCoefficient
            ChapterVIDOuterArcPolarCompiledGrid.inverse10001 with
        | none =>
            stats := { stats with argumentRejected := stats.argumentRejected + 1 }
            if stats.argumentRejected ≤ 12 then
              IO.println s!"argument rejected: {sideName side} connector={index}"
        | some trace =>
            if trace.product.output.real.lower ≤ 0 then
              stats := { stats with notPositiveReal := stats.notPositiveReal + 1 }
            if trace.product.output.real.lower ≤ 0 &&
                trace.product.output.imag.lower ≤ 0 &&
                0 ≤ trace.product.output.imag.upper then
              stats := { stats with meetsNegativeRealRay := stats.meetsNegativeRealRay + 1 }
              if stats.meetsNegativeRealRay ≤ 12 then
                IO.println s!"branch-cut unresolved: {sideName side} connector={index}"
            if 0 ≤ trace.product.output.real.upper &&
                trace.product.output.imag.lower ≤ 0 &&
                0 ≤ trace.product.output.imag.upper then
              stats := { stats with meetsPositiveRealRay := stats.meetsPositiveRealRay + 1 }
            if trace.product.output.imag.lower ≤ 0 &&
                trace.product.output.real.lower ≤ 0 &&
                0 ≤ trace.product.output.real.upper then
              stats := { stats with meetsNegativeImagRay := stats.meetsNegativeImagRay + 1 }
            if 0 ≤ trace.product.output.imag.upper &&
                trace.product.output.real.lower ≤ 0 &&
                0 ≤ trace.product.output.real.upper then
              stats := { stats with meetsPositiveImagRay := stats.meetsPositiveImagRay + 1 }
            let plusFactor := trace.laurentPlus.output.sub (trace.y.nsmul 2)
            let minusFactor := trace.laurentMinus.output.sub (trace.yInv.nsmul 2)
            if plusFactor.real.lower ≤ 0 && plusFactor.imag.lower ≤ 0 &&
                0 ≤ plusFactor.imag.upper then
              stats := { stats with
                plusMeetsNegativeRealRay := stats.plusMeetsNegativeRealRay + 1 }
            if minusFactor.real.lower ≤ 0 && minusFactor.imag.lower ≤ 0 &&
                0 ≤ minusFactor.imag.upper then
              stats := { stats with
                minusMeetsNegativeRealRay := stats.minusMeetsNegativeRealRay + 1 }
            match separation? plusFactor, separation? minusFactor with
            | none, _ | _, none =>
                stats := { stats with unseparated := stats.unseparated + 1 }
                if stats.unseparated ≤ 12 then
                  IO.println s!"unseparated: {sideName side} connector={index}"
            | some plusSeparation, some minusSeparation =>
                let operations := coordinateTrace.operations ++ trace.operations ++
                  [ChapterVILeanCompCertNonzeroGrid.separationOperation
                      plusFactor plusSeparation,
                    ChapterVILeanCompCertNonzeroGrid.separationOperation
                      minusFactor minusSeparation]
                let failures := failureCount (batchClaims operations)
                stats := { stats with failedClaims := stats.failedClaims + failures }
                if failures ≠ 0 then
                  IO.println s!"failed: {sideName side} connector={index} claims={failures}"
  IO.println s!"cells checked: {stats.total}"
  IO.println s!"argument-rejected cells: {stats.argumentRejected}"
  IO.println s!"unseparated cells: {stats.unseparated}"
  IO.println s!"cells without a positive-real product enclosure: {stats.notPositiveReal}"
  IO.println s!"product boxes meeting the nonpositive real ray: {stats.meetsNegativeRealRay}"
  IO.println s!"product boxes meeting the nonnegative real ray: {stats.meetsPositiveRealRay}"
  IO.println s!"product boxes meeting the nonpositive imaginary ray: {stats.meetsNegativeImagRay}"
  IO.println s!"product boxes meeting the nonnegative imaginary ray: {stats.meetsPositiveImagRay}"
  IO.println s!"plus-factor boxes meeting the nonpositive real ray: {stats.plusMeetsNegativeRealRay}"
  IO.println s!"minus-factor boxes meeting the nonpositive real ray: {stats.minusMeetsNegativeRealRay}"
  IO.println s!"failed integer claims: {stats.failedClaims}"
  pure (if stats.argumentRejected = 0 && stats.unseparated = 0 &&
      stats.failedClaims = 0 then 0 else 1)

def inLocalCollar (side : ChapterVIDOuterArcSide)
    (cells collarCells index : Nat) : Bool :=
  match side with
  | .initial => cells - collarCells ≤ index
  | .final => index < collarCells

/-- Reference implementation of the scalable route used by `FactorBulkData`: skip a declared
endpoint collar, check the two factors independently on every remaining cell, and check the
companion factor at the exact endpoint as the collar anchor. -/
def runFactorBulkReference (cells collarCells : Nat) : IO UInt32 := do
  if cells = 0 || cells ≤ collarCells then
    IO.eprintln "error: require 0 < CELLS and COLLAR-CELLS < CELLS"
    return 1
  let mut stats : Stats := {}
  for side in [.initial, .final] do
    let outer := outerRectangle side
    let source := testSourceRectangle side outer
      ChapterVIDConnectorInputBounds.localEndpointRectangle
    let target := testTargetRectangle side outer
      ChapterVIDConnectorInputBounds.localEndpointRectangle
    for index in List.range cells do
      if !inLocalCollar side cells collarCells index then
        stats := { stats with total := stats.total + 1 }
        let parameter := parameterInterval cells index
        let coordinateTrace := ChapterVILeanCompCertProposals.lineMapTrace source target parameter
        match ChapterVILeanCompCertProposals.cartesianRadicandTrace?
            zetaRectangle coordinateTrace.output
            ChapterVIDOuterArcPolarCompiledGrid.exponentialCoefficient
            ChapterVIDOuterArcPolarCompiledGrid.inverse10001 with
        | none =>
            stats := { stats with argumentRejected := stats.argumentRejected + 1 }
        | some trace =>
            let plusFactor := trace.laurentPlus.output.sub (trace.y.nsmul 2)
            let minusFactor := trace.laurentMinus.output.sub (trace.yInv.nsmul 2)
            match slitSeparation? plusFactor, slitSeparation? minusFactor with
            | none, _ | _, none =>
                stats := { stats with unseparated := stats.unseparated + 1 }
                if stats.unseparated ≤ 12 then
                  IO.println s!"bulk branch-cut unresolved: {sideName side} connector={index}"
            | some plusSeparation, some minusSeparation =>
                let operations := coordinateTrace.operations ++ trace.operations ++
                  [ChapterVIDConnectorSeamCompiledGrid.separationOperation
                      plusFactor plusSeparation,
                    ChapterVIDConnectorSeamCompiledGrid.separationOperation
                      minusFactor minusSeparation]
                let failures := failureCount (batchClaims operations)
                stats := { stats with failedClaims := stats.failedClaims + failures }
    let endpointParameter : Interval := match side with
      | .initial => ChapterVISignedDyadicInterval.pointInt 20 1
      | .final => ChapterVISignedDyadicInterval.pointInt 20 0
    let endpointCoordinate :=
      ChapterVILeanCompCertProposals.lineMapTrace source target endpointParameter
    match ChapterVILeanCompCertProposals.cartesianRadicandTrace?
        zetaRectangle endpointCoordinate.output
        ChapterVIDOuterArcPolarCompiledGrid.exponentialCoefficient
        ChapterVIDOuterArcPolarCompiledGrid.inverse10001 with
    | none =>
        stats := { stats with argumentRejected := stats.argumentRejected + 1 }
        IO.println s!"anchor argument rejected: {sideName side}"
    | some trace =>
        let minusFactor := trace.laurentMinus.output.sub (trace.yInv.nsmul 2)
        let anchorOperations := endpointCoordinate.operations ++ trace.operations ++
          [ChapterVIDConnectorSeamCompiledGrid.separationOperation
            minusFactor .realPositive]
        let failures := failureCount (batchClaims anchorOperations)
        if !(0 < minusFactor.real.lower) then
          stats := { stats with unseparated := stats.unseparated + 1 }
          IO.println s!"anchor companion factor not positive: {sideName side}"
        stats := { stats with failedClaims := stats.failedClaims + failures }
  IO.println s!"factor bulk cells checked: {stats.total}"
  IO.println s!"endpoint collar cells skipped per side: {collarCells}"
  IO.println s!"argument-rejected batches: {stats.argumentRejected}"
  IO.println s!"unseparated factor boxes/anchors: {stats.unseparated}"
  IO.println s!"failed integer claims: {stats.failedClaims}"
  pure (if stats.argumentRejected = 0 && stats.unseparated = 0 &&
      stats.failedClaims = 0 then 0 else 1)

def cliMain (args : List String) : IO UInt32 := do
  match args with
  | ["reference-coarse", cellsText] =>
      match cellsText.toNat? with
      | some cells =>
          runReference cells fun _ ↦ ChapterVIDConnectorInputBounds.localEndpointRectangle
      | none =>
          IO.eprintln "error: CELLS must be a natural number"
          pure 1
  | ["scan-idealized", cellsText, marginText] =>
      match cellsText.toNat?, marginText.toNat? with
      | some cells, some margin => runReference cells fun _ ↦ testLocalEndpointRectangle margin
      | _, _ =>
          IO.eprintln "error: CELLS and MARGIN must be natural numbers"
          pure 1
  | ["scan-directional", cellsText, displacementText, marginText] =>
      match cellsText.toNat?, displacementText.toNat?, marginText.toNat? with
      | some cells, some displacement, some margin =>
          runReference cells fun side ↦
            testDirectionalEndpointRectangle side displacement margin
      | _, _, _ =>
          IO.eprintln "error: CELLS, DISPLACEMENT, and MARGIN must be natural numbers"
          pure 1
  | ["reference-factor-bulk", cellsText, collarCellsText] =>
      match cellsText.toNat?, collarCellsText.toNat? with
      | some cells, some collarCells => runFactorBulkReference cells collarCells
      | _, _ =>
          IO.eprintln "error: CELLS and COLLAR-CELLS must be natural numbers"
          pure 1
  | _ =>
      IO.eprintln "usage: chapter-vi-connector-cert (reference-coarse CELLS | reference-factor-bulk CELLS COLLAR-CELLS | scan-idealized CELLS MARGIN | scan-directional CELLS DISPLACEMENT MARGIN)"
      pure 1

end PoincareChapterVI.ConnectorCertificateMain

def main := PoincareChapterVI.ConnectorCertificateMain.cliMain
