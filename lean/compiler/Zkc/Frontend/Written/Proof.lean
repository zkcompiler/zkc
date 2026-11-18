module

public import Zkc.Frontend.Written.Contract

@[expose] public section
set_option autoImplicit false

namespace Zkc.Frontend.Written
open Core

/-- The decision computed by the emitted instructions and a replay of those same instructions. -/
structure VerifierProof where
  decision : String
  steps : String

/-- Supply intermediate values for the generic single-instruction rules. Each proposed
value, operation, occurrence and guard is checked against the actual projected instruction
in Lean. This producer has no authority to postulate an equation about a verifier. -/
def proofSteps (p : SourcePackage) (v : View) : ExportM VerifierProof := do
  let [.protocol _ _ _ _ (.mk [g,u,_] steps [])] := p.named.definitions | unsupported "proof input layout"
  let mut env := [(g,"s.1"),(u,"s.2")]
  let mut lines := #[]
  let mut decision : Option String := none
  for step in steps do
    if decision.isSome then unsupported "code after the deciding guard"
    let args (t : String) (roles : List Role) :=
      s!"(D := roleDialect V ⟨[],[]⟩ {v.verifier}) (sem := sem) (mid := [⟨{t}, {numbers roles}⟩])"
    let value (t : String) (roles : List Role) (x : String) :=
      s!"  refine afterValue {args t roles} (.cons ({x}) .nil) ?_ ?_"
    let reply (t : String) (op x : String) :=
      s!"  refine afterReply {args t (([v.prover,v.verifier]).mergeSort)} (show ROp N from {op}) {x} (fun x => .cons x .nil) ?_ ?_"
    let atKey := fun (k : Key) => s!"⟨path, ⟨{k.number}⟩⟩"
    let (line, binding) ← match step with
      | .op _ [out] (.compute who (.row k)) operands => do
        let some sig := p.bindings.vocabulary.row k | unsupported "unresolved row"
        let [t] := sig.outs | unsupported "multi-output row"
        let t ← ty (b := p.bindings) t
        if !who.contains v.verifier then pure (value t who "()",none)
        else
          let [x,y] := operands | unsupported "verifier row arity"
          let some a := env.lookup x | unsupported "unknown verifier operand"
          let some b := env.lookup y | unsupported "unknown verifier operand"
          let result ← match (show Sum Zkc.Vocabulary.RowKey Emit.PrimitiveName from k) with
            | .inl (.group .add (.group .g1)) => pure s!"(ops.add {a} {b})"
            | .inl (.group .scale (.group .g1)) => pure s!"(ops.scale {a} {b})"
            | .inl (.group .equal (.group .g1)) => pure s!"(decide ({a} = {b}))"
            | _ => unsupported "verifier row outside the group proof library"
          pure (value t who result,some (out,result))
      | .op k [out] (.event (.flow .message who [peer]) t) _ => do
        unless who == v.prover && peer == v.verifier do unsupported "message direction"
        let x ← if v.commitment.instruction == some k.number then pure "a"
          else if v.response.instruction == some k.number then pure "b.suffix"
          else unsupported "message occurrence"
        let t ← ty (b := p.bindings) t
        pure (reply t s!".get .message {who} {atKey k} {t}" x,some (out,x))
      | .op k [out] (.event (.given (.coin law) owner peers) eventType) [] => do
        let t ← ty (b := p.bindings) eventType
        if owner == v.prover && peers.isEmpty then pure (value t [owner] "()",none)
        else
          unless v.challenge.instruction == some k.number && owner == v.verifier && peers == [v.prover] &&
              law == .uniform (.nominal (.field .bls12381Fr)) && eventType == .nominal (.inl (.field .bls12381Fr)) do
            unsupported "unexpected verifier draw, challenge type or law"
          pure (reply t s!".own (.coin challengeLaw) {numbers peers} {atKey k} [] .nil {t}" "b.challenge",
            some (out,"b.challenge"))
      | .guard k who cond .reject => do
        unless who == [v.verifier] do unsupported "decision maker"
        let some test := env.lookup cond | unsupported "unknown guard operand"
        decision := some test
        pure (s!"  refine afterDecision (D := roleDialect V ⟨[],[]⟩ {v.verifier}) (sem := sem) (mid := []) _ (.declared .reject {atKey k}) .nil ?_ ?_",none)
      | _ => unsupported "instruction in verifier proof"
    lines := (lines.push line).push "  · rfl"
    if let some pair := binding then env := pair :: env
  let some condition := decision | unsupported "missing verifier decision"
  return ⟨condition, "\n".intercalate (lines.push "  · finish_return").toList⟩

end Zkc.Frontend.Written
