import Tools.Artifact.Identity.Normalization

/-! Independent opt-in identity pipeline. Original-source admission precedes
resolution; existing preparation then admits the resolved execution view again.
The identity representation is not itself an executable source language. -/

set_option autoImplicit false

namespace Tools.Artifact.Identity
open Lean (Json)
open Tools.Interactive

def selected (descriptor : Json) : Bool :=
  match descriptor with
  | .arr fields => fields[0]? == some (.str "zkc.construction/1") &&
      fields[8]? == some (.str "normalized")
  | _ => false

structure Prepared where
  original : Generic.Prepared
  resolution : Resolution
  resolvedSource : Source
  descriptor : Descriptor
  normalized : Json

def prepare (source descriptor : Json) : Result Prepared := do
  -- Decode only the carrier envelope first. Every semantic declaration and
  -- configuration is admitted by the existing independent generic machinery.
  let carrier ← Carrier.decode source
  let original ← prepareExplicitSource source
  let originalDescriptor ← decodeDescriptor original.source descriptor original.algorithmOrigins
  ensure (selected descriptor) "identity-descriptor"
  admitArtifactProfile original.source originalDescriptor
  let resolution ← resolveCarrier carrier original.library
  let descriptor ← resolveDescriptor resolution original.library descriptor
  let resolvedSource ← artifactSource resolution.carrier.json
  let descriptor ← decodeDescriptor resolvedSource descriptor (← artifactOrigins resolution.carrier.json)
  admitArtifactProfile resolvedSource descriptor
  let normalized ← normalizedProtocol original resolution.carrier descriptor.entry
  let _ ← treeBytes normalized
  return ⟨original, resolution, resolvedSource, descriptor, normalized⟩

def Prepared.configuration (prepared : Prepared) (json : Json) : Result Json :=
  resolveConfiguration prepared.resolution prepared.original.source json

def Prepared.inspection (prepared : Prepared) : Json :=
  .arr #[.str "zkc.identity-inspection/1", prepared.resolution.carrier.json,
    prepared.descriptor.json, prepared.normalized]

end Tools.Artifact.Identity
