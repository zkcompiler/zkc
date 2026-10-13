module

public import Zkc.Source.Constructed
public import Zkc.Protocols.Schnorr.Construction

@[expose] public section

/-! Canonical-RO interpretation of the selected native Schnorr primitive profile.

The imported body retains its native descriptor, attributes, Local provenance,
SSA operands, and returned transcript. This module selects mathematical meanings
for its primitive leaves. It does not identify Merlin with a random oracle.
-/
namespace Zkc.Protocols.Schnorr.NativeConstruction
open Zkc.Source
open Construction

/-- The canonical experiment retains the live binding and all observed values.
Host initialization supplies the full binding before either participant starts. -/
structure Transcript (Context F G : Type) where
  binding : Binding Context G
  commitment : Option G := none
  challenge : Option F := none
  delivered : Bool := false
  response : Option F := none
  deriving DecidableEq

abbrev Value (Context F G : Type) : String → Type
  | "i1" => Bool
  | "!algebra.field<\"bls12-381.fr\">" => F
  | "!algebra.group<\"bls12-381.g1\">" => G
  | "!local.capability<\"transcript:merlin3.bls12-381.fr64be/0\">" => Transcript Context F G
  | "!algebra.indices" => List Nat
  | _ => Unit

variable {Context F G : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq G] [DecidableEq F]

/-- Exact primitive type signatures select meanings. Unknown leaves refuse.
Static framing attributes are retained in the imported subject; they are not
interpreted as bytes by this typed ideal experiment. Empty dynamic coordinates
are required by this flat profile. -/
def primitive (proof : G × F) (op : Constructed.Primitive) :
    Values (Value Context F G) op.arguments →
      PIR.Proc (oracleSignature Context F G) (Values (Value Context F G) op.results) :=
  match op with
  | ⟨"protocol.receive", _, _, _, [], ["!algebra.group<\"bls12-381.g1\">"]⟩ =>
    fun .nil => .done (.cons proof.1 .nil)
  | ⟨"protocol.receive", _, _, _, [], ["!algebra.field<\"bls12-381.fr\">"]⟩ =>
    fun .nil => .done (.cons proof.2 .nil)
  | ⟨"algebra.exec.indices_empty", _, _, _, [], ["!algebra.indices"]⟩ =>
    fun .nil => .done (.cons [] .nil)
  | ⟨"crypto.exec.indexed_transcript_observe_data", _, _, _,
      ["!local.capability<\"transcript:merlin3.bls12-381.fr64be/0\">",
       "!algebra.group<\"bls12-381.g1\">", "!algebra.indices"],
      ["!local.capability<\"transcript:merlin3.bls12-381.fr64be/0\">"]⟩ =>
    fun (.cons state (.cons commitment (.cons indices .nil))) =>
      if indices.isEmpty && state.commitment.isNone && state.challenge.isNone then
        .done (.cons { state with commitment := some commitment } .nil)
      else .halt .refused
  | ⟨"crypto.exec.indexed_transcript_challenge", _, _, _,
      ["!local.capability<\"transcript:merlin3.bls12-381.fr64be/0\">", "!algebra.indices"],
      ["!algebra.field<\"bls12-381.fr\">",
       "!local.capability<\"transcript:merlin3.bls12-381.fr64be/0\">"]⟩ =>
    fun (.cons state (.cons indices .nil)) =>
      match state.commitment with
      | none => .halt .refused
      | some commitment =>
        if indices.isEmpty && state.challenge.isNone then
          .call (state.binding, commitment) fun (challenge : F) =>
            .done (.cons challenge (.cons { state with challenge := some challenge } .nil))
        else .halt .refused
  | ⟨"crypto.exec.indexed_transcript_observe_data", _, _, _,
      ["!local.capability<\"transcript:merlin3.bls12-381.fr64be/0\">",
       "!algebra.field<\"bls12-381.fr\">", "!algebra.indices"],
      ["!local.capability<\"transcript:merlin3.bls12-381.fr64be/0\">"]⟩ =>
    fun (.cons state (.cons value (.cons indices .nil))) =>
      match state.challenge with
      | none => .halt .refused
      | some challenge =>
        if !indices.isEmpty || state.response.isSome then .halt .refused
        else if state.delivered then .done (.cons { state with response := some value } .nil)
        else if (value : F) = challenge then .done (.cons { state with delivered := true } .nil)
        else .halt .refused
  | ⟨"algebra.group_scale", _, _, _,
      ["!algebra.group<\"bls12-381.g1\">", "!algebra.field<\"bls12-381.fr\">"],
      ["!algebra.group<\"bls12-381.g1\">"]⟩ =>
    fun (.cons base (.cons scalar .nil)) =>
      .done (.cons (@SMul.smul F G inferInstance scalar base) .nil)
  | ⟨"algebra.group_add", _, _, _,
      ["!algebra.group<\"bls12-381.g1\">", "!algebra.group<\"bls12-381.g1\">"],
      ["!algebra.group<\"bls12-381.g1\">"]⟩ =>
    fun (.cons left (.cons right .nil)) =>
      .done (.cons (@HAdd.hAdd G G G inferInstance left right) .nil)
  | ⟨"algebra.group_equal", _, _, _,
      ["!algebra.group<\"bls12-381.g1\">", "!algebra.group<\"bls12-381.g1\">"], ["i1"]⟩ =>
    fun (.cons left (.cons right .nil)) => .done (.cons (decide ((left : G) = right)) .nil)
  | _ => fun _ => .halt .refused

def meaning (proof : G × F) : Constructed.Meaning (oracleSignature Context F G) where
  Value := Value Context F G
  condition := id
  primitive := primitive proof

/-- Fixed native participant input shape, preserving the explicit transcript input. -/
def inputTypes : List String :=
  ["!algebra.group<\"bls12-381.g1\">", "!algebra.group<\"bls12-381.g1\">",
   "!local.capability<\"transcript:merlin3.bls12-381.fr64be/0\">"]

def outputTypes : List String :=
  ["i1", "!local.capability<\"transcript:merlin3.bls12-381.fr64be/0\">"]

def inputs (binding : Binding Context G) :
    Values (Values (Value Context F G)) (inputTypes.map Constructed.scalar) :=
  .cons (.cons binding.base .nil) (.cons (.cons binding.key .nil)
    (.cons (.cons (⟨binding, none, none, false, none⟩ : Transcript Context F G) .nil) .nil))

/-- The complete returned state remains available before this deliberate Boolean projection. -/
def result (reply : Values (Value Context F G) outputTypes) : Option Bool :=
  match reply with | .cons value (.cons _ .nil) => some value

/-- Adapt one admitted native subject with checked input/output shapes. This
merely defines execution; a realization theorem still must inspect its actual body. -/
def verifier {snapshot : Constructed.Snapshot} (imported : Constructed.Imported snapshot)
    (inputShape : snapshot.inputs = inputTypes) (outputShape : snapshot.outputs = outputTypes) :
    Construction.Verifier Context F G := fun binding proof =>
  let supplied := inputShape.symm ▸ inputs (F := F) binding
  (imported.denote (meaning proof) supplied).bind fun reply =>
    .done (result (outputShape ▸ reply))

end Zkc.Protocols.Schnorr.NativeConstruction
