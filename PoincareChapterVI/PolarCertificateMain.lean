import PoincareChapterVI.ChapterVIDOuterArcPolarCompiledGrid
import LeanCompCert.NativeCheck

/-!
# Executable for the Chapter VI outer-arc certificate

This is the reproducible boundary for the large finite calculation.  It emits the restricted C
program whose semantics is related to the Lean computation by LeanCompCert, or asks the packaged
native checker to compile it with CompCert and run the zero-failure test.
-/

open LeanCompCert
open PoincareChapterVI
open PoincareChapterVI.ChapterVILeanCompCertBatch
open PoincareChapterVI.ChapterVIDOuterArcPolarCompiledGrid
open LeanCompCert.Ports.SignedProductClaims

set_option maxRecDepth 1000000

def polarComputation (side : ChapterVIDOuterArcSide) (i : Fin 28) :
    Verified.Computation :=
  batchComputation (shardArtifactName side i) (shardOperations side i)

def polarMainC (side : ChapterVIDOuterArcSide) (i : Fin 28) : String :=
  Attest.selfCheckMain (ABI.mangle (shardArtifactName side i)) 0

def polarEmittedC (side : ChapterVIDOuterArcSide) (i : Fin 28) :
    Except (Array String) String := do
  let (_, source) ← Lower.compileProgram .portable
    { functions := #[(polarComputation side i).fn] }
  pure (source ++ polarMainC side i)

def sides : List ChapterVIDOuterArcSide := [.initial, .final]

def polarNativeCert (side : ChapterVIDOuterArcSide) (i : Fin 28) : NativeCheck.Cert :=
  { name := s!"outer-polar-{sideName side}-{i.val}"
    emitted := polarEmittedC side i
    certifiedValue := some 0 }

def polarNativeCerts (_ : Unit) : List NativeCheck.Cert :=
  sides.flatMap fun side => (List.finRange 28).map fun i =>
    polarNativeCert side i

def parseSide : String → Option ChapterVIDOuterArcSide
  | "initial" => some .initial
  | "final" => some .final
  | _ => none

def parseIndex (value : String) : Option (Fin 28) := do
  let index ← value.toNat?
  if h : index < 28 then some ⟨index, h⟩ else none

def parseAngle (value : String) : Option (Fin 32) := do
  let index ← value.toNat?
  if h : index < 32 then some ⟨index, h⟩ else none

def withShard (sideText indexText : String)
    (action : ChapterVIDOuterArcSide → Fin 28 → IO UInt32) : IO UInt32 := do
  match parseSide sideText, parseIndex indexText with
  | some side, some index => action side index
  | _, _ =>
      IO.eprintln "error: SIDE must be initial|final and INDEX must be 0..27"
      pure 1

/--
`chapter-vi-polar-cert emit SIDE INDEX OUTPUT.c` emits one self-checking shard.

`chapter-vi-polar-cert check-native [OPTIONS]` invokes the cached CompCert compile/run workflow.

`chapter-vi-polar-cert stats SIDE INDEX` prints one shard's finite campaign size.
-/
def main (args : List String) : IO UInt32 := do
  match args with
  | "check-native" :: rest =>
      NativeCheck.run (polarNativeCerts ())
        (rest ++ ["--start-dir", ".lake/packages/leancompcert/runtime/start"])
  | "check-shard" :: sideText :: indexText :: rest =>
      withShard sideText indexText fun side index =>
        NativeCheck.run [polarNativeCert side index]
          (rest ++ ["--start-dir", ".lake/packages/leancompcert/runtime/start"])
  | ["stats", sideText, indexText] =>
      withShard sideText indexText fun side index => do
        IO.println s!"operations: {(shardOperations side index).length}"
        IO.println s!"integer claims: {(batchClaims (shardOperations side index)).length}"
        pure 0
  | ["stats-cell", sideText, indexText, angleText] =>
      withShard sideText indexText fun side index => do
        match parseAngle angleText with
        | some angle =>
            IO.println s!"operations: {(cellOperations side index angle).length}"
            IO.println s!"integer claims: {(batchClaims
              (cellOperations side index angle)).length}"
            pure 0
        | none =>
            IO.eprintln "error: ANGLE must be 0..31"
            pure 1
  | ["emit", sideText, indexText, file] =>
      withShard sideText indexText fun side index => do
        match polarEmittedC side index with
        | .error errors =>
            for error in errors do IO.eprintln error
            pure 1
        | .ok source =>
            IO.FS.writeFile file source
            IO.println s!"wrote {file}"
            pure 0
  | ["reference"] =>
      let mut checked := 0
      let mut failures := 0
      for side in sides do
        for index in List.finRange 28 do
          failures := failures + failureCount (batchClaims (shardOperations side index))
          checked := checked + 1
      IO.println s!"checked shards: {checked}"
      IO.println s!"failed integer claims: {failures}"
      pure (if failures = 0 then 0 else 1)
  | _ =>
      IO.eprintln "usage: chapter-vi-polar-cert (reference | stats SIDE INDEX | emit SIDE INDEX OUTPUT.c | check-shard SIDE INDEX [OPTIONS] | check-native [OPTIONS])"
      pure 1
