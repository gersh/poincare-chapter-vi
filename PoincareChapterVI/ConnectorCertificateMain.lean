import PoincareChapterVI.ChapterVIDConnectorFactorBulkCompiled
import PoincareChapterVI.ChapterVIDConnectorFactorDerivativeReference
import PoincareChapterVI.ChapterVIDConnectorFactorNormalizedDerivativeCompiled
import PoincareChapterVI.ChapterVIDConnectorFactorSecondDerivativeReference
import LeanCompCert.NativeCheck

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
open PoincareChapterVI.ChapterVIDConnectorFactorBulkReference
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

def parseSide : String → Option ChapterVIDOuterArcSide
  | "initial" => some .initial
  | "final" => some .final
  | _ => none

def parseShard (value : String) : Option (Fin shardCount) := do
  let index ← value.toNat?
  if h : index < shardCount then some ⟨index, h⟩ else none

def withFactorShard (sideText shardText : String)
    (action : ChapterVIDOuterArcSide → Fin shardCount → IO UInt32) : IO UInt32 := do
  match parseSide sideText, parseShard shardText with
  | some side, some shard => action side shard
  | _, _ =>
      IO.eprintln "error: SIDE must be initial|final and SHARD must be 0..31"
      pure 1

def factorShardArtifact (side : ChapterVIDOuterArcSide) (shard : Fin shardCount) :=
  ChapterVILeanCompCertAttestation.batchArtifact (shardArtifactName side shard)
    (referenceShardOperations side shard)

def factorShardEmittedC (side : ChapterVIDOuterArcSide) (shard : Fin shardCount) :
    Except (Array String) String :=
  match (factorShardArtifact side shard).source? with
  | some source => .ok source
  | none => .error #[s!"LeanCompCert could not emit connector shard {sideName side}/{shard.val}"]

def factorShardNativeCert (side : ChapterVIDOuterArcSide) (shard : Fin shardCount) :
    LeanCompCert.NativeCheck.Cert :=
  { name := shardArtifactName side shard
    emitted := factorShardEmittedC side shard
    certifiedValue := some 0 }

def factorAnchorArtifact (side : ChapterVIDOuterArcSide) :=
  ChapterVILeanCompCertAttestation.batchArtifact (anchorArtifactName side)
    (referenceAnchorOperations side)

def factorAnchorEmittedC (side : ChapterVIDOuterArcSide) : Except (Array String) String :=
  match (factorAnchorArtifact side).source? with
  | some source => .ok source
  | none => .error #[s!"LeanCompCert could not emit connector anchor {sideName side}"]

def factorAnchorNativeCert (side : ChapterVIDOuterArcSide) : LeanCompCert.NativeCheck.Cert :=
  { name := anchorArtifactName side
    emitted := factorAnchorEmittedC side
    certifiedValue := some 0 }

def factorShardNativeCerts (_ : Unit) : List LeanCompCert.NativeCheck.Cert :=
  ([.initial, .final] : List ChapterVIDOuterArcSide).flatMap fun side ↦
    factorAnchorNativeCert side ::
      (List.finRange shardCount).map fun shard ↦ factorShardNativeCert side shard

namespace Derivative

open ChapterVIDConnectorFactorDerivativeReference

def parseShard (side : ChapterVIDOuterArcSide) (value : String) :
    Option (Fin (shardCount side)) := do
  let index ← value.toNat?
  if h : index < shardCount side then some ⟨index, h⟩ else none

def withShard (sideText shardText : String)
    (action : (side : ChapterVIDOuterArcSide) → Fin (shardCount side) → IO UInt32) : IO UInt32 := do
  match parseSide sideText with
  | none =>
      IO.eprintln "error: SIDE must be initial|final"
      pure 1
  | some side =>
      match parseShard side shardText with
      | some shard => action side shard
      | none =>
          IO.eprintln s!"error: derivative SHARD must be below {shardCount side}"
          pure 1

def artifact (side : ChapterVIDOuterArcSide) (shard : Fin (shardCount side)) :=
  ChapterVILeanCompCertAttestation.batchArtifact (shardArtifactName side shard)
    (shardOperations side shard)

def emittedC (side : ChapterVIDOuterArcSide) (shard : Fin (shardCount side)) :
    Except (Array String) String :=
  match (artifact side shard).source? with
  | some source => .ok source
  | none => .error #[s!"LeanCompCert could not emit derivative shard {sideName side}/{shard.val}"]

def nativeCert (side : ChapterVIDOuterArcSide) (shard : Fin (shardCount side)) :
    LeanCompCert.NativeCheck.Cert :=
  { name := shardArtifactName side shard
    emitted := emittedC side shard
    certifiedValue := some 0 }

end Derivative

namespace SecondDerivative

open ChapterVIDConnectorFactorSecondDerivativeReference

def parseShard (side : ChapterVIDOuterArcSide) (value : String) :
    Option (Fin (shardCount side)) := do
  let index ← value.toNat?
  if h : index < shardCount side then some ⟨index, h⟩ else none

def withShard (sideText shardText : String)
    (action : (side : ChapterVIDOuterArcSide) → Fin (shardCount side) → IO UInt32) : IO UInt32 := do
  match parseSide sideText with
  | none =>
      IO.eprintln "error: SIDE must be initial|final"
      pure 1
  | some side =>
      match parseShard side shardText with
      | some shard => action side shard
      | none =>
          IO.eprintln s!"error: second-derivative SHARD must be below {shardCount side}"
          pure 1

def artifact (side : ChapterVIDOuterArcSide) (shard : Fin (shardCount side)) :=
  ChapterVILeanCompCertAttestation.batchArtifact (shardArtifactName side shard)
    (shardOperations side shard)

def emittedC (side : ChapterVIDOuterArcSide) (shard : Fin (shardCount side)) :
    Except (Array String) String :=
  match (artifact side shard).source? with
  | some source => .ok source
  | none => .error #[s!"LeanCompCert could not emit curvature shard {sideName side}/{shard.val}"]

def nativeCert (side : ChapterVIDOuterArcSide) (shard : Fin (shardCount side)) :
    LeanCompCert.NativeCheck.Cert :=
  { name := shardArtifactName side shard
    emitted := emittedC side shard
    certifiedValue := some 0 }

end SecondDerivative

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

def runNormalizedSlice (displacement : Nat) : IO UInt32 := do
  let mut failures := 0
  for side in ([.initial, .final] : List ChapterVIDOuterArcSide) do
    let signedDisplacement : Int := match side with
      | .initial => Int.ofNat displacement
      | .final => -Int.ofNat displacement
    let localDelta : Rectangle :=
      ⟨⟨-1, 1⟩, ⟨signedDisplacement, signedDisplacement⟩⟩
    let mut operationCount := 0
    let mut sideFailures := 0
    let mut failingCells := 0
    let mut firstFail : Option Nat := none
    let mut lastFail : Option Nat := none
    for index in List.finRange
        ChapterVIDConnectorFactorNormalizedDerivativeCompiled.referenceCellCount do
      let operations :=
        ChapterVIDConnectorFactorNormalizedDerivativeCompiled.referenceOperationsWithLocalDelta
          side
          (ChapterVIDConnectorFactorNormalizedDerivativeCompiled.referenceParameterInterval
            side index)
          localDelta
      operationCount := operationCount + operations.length
      let cellFailures := failureCount (batchClaims operations)
      sideFailures := sideFailures + cellFailures
      if cellFailures != 0 then
        failingCells := failingCells + 1
        if firstFail.isNone then firstFail := some index.val
        lastFail := some index.val
    failures := failures + sideFailures
    IO.println s!"normalized slice {sideName side} operations: {operationCount}"
    IO.println s!"normalized slice {sideName side} failed integer claims: {sideFailures}"
    IO.println s!"normalized slice {sideName side} failing cells: {failingCells}"
    IO.println s!"normalized slice {sideName side} first/last failing cell: {firstFail}/{lastFail}"
  pure (if failures = 0 then 0 else 1)

def cliMain (args : List String) : IO UInt32 := do
  match args with
  | "check-factor-native" :: rest =>
      LeanCompCert.NativeCheck.run (factorShardNativeCerts ())
        (rest ++ ["--start-dir", ".lake/packages/leancompcert/runtime/start"])
  | "check-factor-shard" :: sideText :: shardText :: rest =>
      withFactorShard sideText shardText fun side shard ↦
        LeanCompCert.NativeCheck.run [factorShardNativeCert side shard]
          (rest ++ ["--start-dir", ".lake/packages/leancompcert/runtime/start"])
  | "check-factor-anchor" :: sideText :: rest =>
      match parseSide sideText with
      | some side =>
          LeanCompCert.NativeCheck.run [factorAnchorNativeCert side]
            (rest ++ ["--start-dir", ".lake/packages/leancompcert/runtime/start"])
      | none =>
          IO.eprintln "error: SIDE must be initial|final"
          pure 1
  | "check-factor-derivative-shard" :: sideText :: shardText :: rest =>
      Derivative.withShard sideText shardText fun side shard ↦
        LeanCompCert.NativeCheck.run [Derivative.nativeCert side shard]
          (rest ++ ["--start-dir", ".lake/packages/leancompcert/runtime/start"])
  | "check-factor-second-derivative-shard" :: sideText :: shardText :: rest =>
      SecondDerivative.withShard sideText shardText fun side shard ↦
        LeanCompCert.NativeCheck.run [SecondDerivative.nativeCert side shard]
          (rest ++ ["--start-dir", ".lake/packages/leancompcert/runtime/start"])
  | ["stats-factor-shard", sideText, shardText] =>
      withFactorShard sideText shardText fun side shard ↦ do
        let shardOperations := referenceShardOperations side shard
        IO.println s!"cells: {cellsPerShard}"
        IO.println s!"operations: {shardOperations.length}"
        IO.println s!"integer claims: {(batchClaims shardOperations).length}"
        pure 0
  | ["emit-factor-shard", sideText, shardText, file] =>
      withFactorShard sideText shardText fun side shard ↦ do
        match factorShardEmittedC side shard with
        | .error errors =>
            for error in errors do IO.eprintln error
            pure 1
        | .ok source =>
            IO.FS.writeFile file source
            IO.println s!"wrote {file}"
            pure 0
  | ["emit-factor-anchor", sideText, file] =>
      match parseSide sideText with
      | some side =>
          match factorAnchorEmittedC side with
          | .error errors =>
              for error in errors do IO.eprintln error
              pure 1
          | .ok source =>
              IO.FS.writeFile file source
              IO.println s!"wrote {file}"
              pure 0
      | none =>
          IO.eprintln "error: SIDE must be initial|final"
          pure 1
  | ["stats-factor-derivative-shard", sideText, shardText] =>
      Derivative.withShard sideText shardText fun side shard ↦ do
        let shardOperations :=
          ChapterVIDConnectorFactorDerivativeReference.shardOperations side shard
        IO.println s!"cells: {ChapterVIDConnectorFactorDerivativeReference.cellsPerShard}"
        IO.println s!"operations: {shardOperations.length}"
        IO.println s!"integer claims: {(batchClaims shardOperations).length}"
        pure 0
  | ["emit-factor-derivative-shard", sideText, shardText, file] =>
      Derivative.withShard sideText shardText fun side shard ↦ do
        match Derivative.emittedC side shard with
        | .error errors =>
            for error in errors do IO.eprintln error
            pure 1
        | .ok source =>
            IO.FS.writeFile file source
            IO.println s!"wrote {file}"
            pure 0
  | ["stats-factor-second-derivative-shard", sideText, shardText] =>
      SecondDerivative.withShard sideText shardText fun side shard ↦ do
        let shardOperations :=
          ChapterVIDConnectorFactorSecondDerivativeReference.shardOperations side shard
        IO.println s!"cells: {ChapterVIDConnectorFactorSecondDerivativeReference.cellsPerShard}"
        IO.println s!"operations: {shardOperations.length}"
        IO.println s!"integer claims: {(batchClaims shardOperations).length}"
        pure 0
  | ["emit-factor-second-derivative-shard", sideText, shardText, file] =>
      SecondDerivative.withShard sideText shardText fun side shard ↦ do
        match SecondDerivative.emittedC side shard with
        | .error errors =>
            for error in errors do IO.eprintln error
            pure 1
        | .ok source =>
            IO.FS.writeFile file source
            IO.println s!"wrote {file}"
            pure 0
  | ["reference-factor-shards"] =>
      let mut checked := 0
      let mut failures := 0
      for side in ([.initial, .final] : List ChapterVIDOuterArcSide) do
        failures := failures + failureCount (batchClaims (referenceAnchorOperations side))
        checked := checked + 1
        for shard in List.finRange shardCount do
          failures := failures + failureCount (batchClaims (referenceShardOperations side shard))
          checked := checked + 1
      IO.println s!"checked shards: {checked}"
      IO.println s!"failed integer claims: {failures}"
      pure (if failures = 0 then 0 else 1)
  | ["reference-factor-derivative-shards"] =>
      let mut checked := 0
      let mut failures := 0
      for side in ([.initial, .final] : List ChapterVIDOuterArcSide) do
        for shard in List.finRange
            (ChapterVIDConnectorFactorDerivativeReference.shardCount side) do
          failures := failures + failureCount (batchClaims
            (ChapterVIDConnectorFactorDerivativeReference.shardOperations side shard))
          checked := checked + 1
      IO.println s!"checked derivative shards: {checked}"
      IO.println s!"failed integer claims: {failures}"
      pure (if failures = 0 then 0 else 1)
  | ["reference-factor-second-derivative-shards"] =>
      let mut checked := 0
      let mut failures := 0
      for side in ([.initial, .final] : List ChapterVIDOuterArcSide) do
        for shard in List.finRange
            (ChapterVIDConnectorFactorSecondDerivativeReference.shardCount side) do
          failures := failures + failureCount (batchClaims
            (ChapterVIDConnectorFactorSecondDerivativeReference.shardOperations side shard))
          checked := checked + 1
      IO.println s!"checked second-derivative shards: {checked}"
      IO.println s!"failed integer claims: {failures}"
      pure (if failures = 0 then 0 else 1)
  | ["reference-factor-normalized"] =>
      let mut failures := 0
      for side in ([.initial, .final] : List ChapterVIDOuterArcSide) do
        let operations :=
          ChapterVIDConnectorFactorNormalizedDerivativeCompiled.referenceSideOperations side
        let sideFailures := failureCount (batchClaims operations)
        failures := failures + sideFailures
        IO.println s!"normalized {sideName side} operations: {operations.length}"
        IO.println s!"normalized {sideName side} failed integer claims: {sideFailures}"
        let mut failingCells := 0
        let mut firstFail : Option Nat := none
        let mut lastFail : Option Nat := none
        for index in List.finRange
            ChapterVIDConnectorFactorNormalizedDerivativeCompiled.referenceCellCount do
          let cellFailures := failureCount (batchClaims
            (ChapterVIDConnectorFactorNormalizedDerivativeCompiled.referenceOperations side
              (ChapterVIDConnectorFactorNormalizedDerivativeCompiled.referenceParameterInterval
                side index)))
          if cellFailures != 0 then
            failingCells := failingCells + 1
            if firstFail.isNone then firstFail := some index.val
            lastFail := some index.val
        IO.println s!"normalized {sideName side} failing cells: {failingCells}"
        IO.println s!"normalized {sideName side} first/last failing cell: {firstFail}/{lastFail}"
      pure (if failures = 0 then 0 else 1)
  | ["reference-factor-normalized-nonzero"] => runNormalizedSlice 1
  | ["reference-factor-normalized-slice", displacementText] =>
      match displacementText.toNat? with
      | some displacement => runNormalizedSlice displacement
      | none =>
          IO.eprintln "error: DISPLACEMENT must be a natural number"
          pure 1
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
      IO.eprintln "usage: chapter-vi-connector-cert (reference-factor-shards | reference-factor-derivative-shards | reference-factor-second-derivative-shards | reference-factor-normalized | reference-factor-normalized-nonzero | reference-factor-normalized-slice DISPLACEMENT | stats-factor-shard SIDE SHARD | stats-factor-derivative-shard SIDE SHARD | stats-factor-second-derivative-shard SIDE SHARD | emit-factor-shard SIDE SHARD OUTPUT.c | emit-factor-derivative-shard SIDE SHARD OUTPUT.c | emit-factor-second-derivative-shard SIDE SHARD OUTPUT.c | emit-factor-anchor SIDE OUTPUT.c | check-factor-shard SIDE SHARD [OPTIONS] | check-factor-derivative-shard SIDE SHARD [OPTIONS] | check-factor-second-derivative-shard SIDE SHARD [OPTIONS] | check-factor-anchor SIDE [OPTIONS] | check-factor-native [OPTIONS] | reference-coarse CELLS | reference-factor-bulk CELLS COLLAR-CELLS | scan-idealized CELLS MARGIN | scan-directional CELLS DISPLACEMENT MARGIN)"
      pure 1

end PoincareChapterVI.ConnectorCertificateMain

def main := PoincareChapterVI.ConnectorCertificateMain.cliMain
