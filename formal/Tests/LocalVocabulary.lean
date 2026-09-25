import Tools.Interactive.PhysicalLocal
import Tools.Artifact.Runtime

/-! The independent Boolean and sequence computations, including retained request
cost on failure. Point validity is a separate external-service premise; the
fixtures use canonical identity and generator bytes in both installed groups. -/
set_option autoImplicit false

namespace Tests.LocalVocabulary
open Tools.Interactive
open Lean (Json)

private def location : Reference.Location := Reference.Location.plain "test" "root" "op" "V"
private def binding (name : String) (args : List String := []) : OperationBinding :=
  ⟨"operation", name, args, ""⟩

private def evaluate (b : OperationBinding) (inputs : List Reference.Value)
    (attrs : List String := []) : Result (List Json × Nat × Nat) := do
  let request ← TypedLocal.resolveRequest [b] "op" b.name attrs
  let (result, state) := (Reference.evaluate location request inputs).run {}
  match result with
  | .error fault => throw fault.detail
  | .ok values => return (values.map Reference.Value.json, state.spent, state.events.size)

example : ((evaluate (binding "bool.not") [.boolean false]).toOption ==
    some ([.arr #[.str "bool", .str "true"]], 4, 2)) = true := by native_decide
example : ([false, true].all fun a => [false, true].all fun b =>
    (evaluate (binding "bool.or") [.boolean a, .boolean b]).toOption ==
      some ([.arr #[.str "bool", .str (toString (a || b))]], 5, 2)) = true := by native_decide
example : (evaluate (binding "bool.not") [.boolean true] ["0"]).isOk = false := by native_decide
example : (evaluate (binding "bool.or" [Bindings.fr]) [.boolean true, .boolean false]).isOk = false := by native_decide
example : (evaluate (binding "bool.not") [Reference.Value.fromArithmetic .bls (.index 0)]).isOk = false := by native_decide
example : PhysicalLocal.supported ⟨"b", "bool.not", [], "arkworks/bool.not"⟩ = true := by native_decide
example : PhysicalLocal.supported ⟨"b", "bool.or", [], "arkworks/bool.or"⟩ = true := by native_decide

private def group (r : Bool) := if r then Bindings.ristrettoGroup else Bindings.g1
private def generator (r : Bool) : ByteArray :=
  (Tools.Artifact.unhex (if r then
    "e2f2ae0a6abc4e71a884a961c500515f58e30b6aa582dd8db6a65945e08d2d76" else
    "97f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb")).toOption.getD ByteArray.empty
private def identity (r : Bool) : ByteArray :=
  if r then ⟨Array.replicate 32 0⟩ else ⟨#[192] ++ Array.replicate 47 0⟩
private def sequenceWire (r : Bool) (empty := false) : ByteArray :=
  Tools.Artifact.magic.push (if r then 17 else 10) ++ Tools.Artifact.little 4 (if empty then 0 else 2) ++
    (if empty then ByteArray.empty else identity r ++ generator r)
private def pointWire (r : Bool) : ByteArray :=
  Tools.Artifact.magic.push (if r then 16 else 9) ++ generator r
private def sequence (r : Bool) (empty := false) : Reference.Value :=
  if r then .rgroups (sequenceWire r empty) else .groups (sequenceWire r empty)
private def index (n : Nat) : Reference.Value := .fromArithmetic .bls (.index n)

example : ([false, true].all fun r =>
    ((evaluate (binding "curve.length" [group r]) [sequence r]).toOption.map (·.1)) ==
      some [.arr #[.str "index", .str "2"]]) = true := by native_decide
example : ([false, true].all fun r =>
    ((evaluate (binding "curve.length" [group r]) [sequence r true]).toOption.map (·.1)) ==
      some [.arr #[.str "index", .str "0"]]) = true := by native_decide
example : ([false, true].all fun r =>
    ((evaluate (binding "curve.get" [group r]) [sequence r, index 1]).toOption.map (·.1)) ==
      some [.arr #[.str ("group:" ++ group r), .str (Tools.Artifact.hex (pointWire r))]]) = true := by native_decide
example : ([false, true].all fun r => [2, 18446744073709551615].all fun i =>
    (evaluate (binding "curve.get" [group r]) [sequence r, index i]).toOption.isNone) = true := by native_decide
example : (evaluate (binding "curve.get" [Bindings.g1]) [sequence true, index 0]).isOk = false := by native_decide
example : (evaluate (binding "curve.length" [Bindings.ristrettoGroup]) [sequence false]).isOk = false := by native_decide
example : (evaluate (binding "curve.get" [Bindings.ristrettoGroup]) [sequence true, index 0] ["0"]).isOk = false := by native_decide

private def failedAttempt : Bool := Id.run do
  let .ok request := TypedLocal.resolveRequest [binding "curve.get" [Bindings.ristrettoGroup]] "op" "operation" [] | return false
  let inputs := [sequence true, index 2]
  let (result, state) := (Reference.evaluate location request inputs).run {}
  return result.isOk == false && state.events.size == 1 &&
    state.spent == 1 + (inputs.map Reference.Value.size).sum
example : failedAttempt = true := by native_decide

-- The artifact reference also reads sequences itself; no primitive response is
-- supplied, so an accidental external request would make these checks fail.
private def artifact (b : OperationBinding) (inputs : List Tools.Artifact.Value) : Result (List Json) := do
  let source : Source := ⟨.explicit [b], [], [], [], []⟩
  let descriptor : Tools.Artifact.Descriptor := ⟨"main", "P", "V", [], "rng", [], 0, .null⟩
  let loc : Tools.Artifact.Location := { entry := "main", binding := "root", path := [], protocol := "Main", role := "V" }
  let state : Tools.Artifact.State := { cursor := ⟨ByteArray.empty, 0⟩, root := ByteArray.empty, configuration := .null, answers := #[] }
  let (result, _) := (Tools.Artifact.evaluate source descriptor loc b.name [] inputs).run state
  match result with
  | .error fault => throw fault.detail
  | .ok values => values.mapM (fun v => v.jsonFor)
private def artifactSequence (r : Bool) : Tools.Artifact.Value :=
  if r then .nominalBytes (group r) "groups" (sequenceWire r)
  else .publicBytes "groups" (sequenceWire r)
example : ([false, true].all fun r =>
    (artifact (binding "curve.length" [group r]) [artifactSequence r]).toOption ==
      some [.arr #[.str "index", .str "5a4b4356011f0200000000000000"]]) = true := by native_decide
example : ([false, true].all fun r =>
    (artifact (binding "curve.get" [group r]) [artifactSequence r, .fromArithmetic .bls (.index 1)]).toOption ==
      some [.arr #[.str ("group:" ++ group r), .str (Tools.Artifact.hex (pointWire r))]]) = true := by native_decide
example : ([false, true].all fun r =>
    (artifact (binding "curve.get" [group r]) [artifactSequence r, .fromArithmetic .bls (.index 2)]).isOk == false) = true := by native_decide
example : ((artifact (binding "bool.not") [.boolean true]).toOption ==
    some [.arr #[.str "bool", .str "5a4b4356010500"]]) = true := by native_decide
example : ((artifact (binding "bool.or") [.boolean false, .boolean true]).toOption ==
    some [.arr #[.str "bool", .str "5a4b4356010501"]]) = true := by native_decide

end Tests.LocalVocabulary
