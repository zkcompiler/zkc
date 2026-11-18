module

public import Zkc.Core.Scheme.Declaration
public import Zkc.Core.Program.Typed

@[expose] public section

/-!
Who proves and who verifies, the statement and the witness, and the coins that some role
hears, read from the events of a shape.
-/

namespace Zkc.Core

/-! ## Who proves, who verifies, the statement and the witness -/

/-- Whether the scheme is interactive. -/
def Declaration.interactive (declaration : Declaration) : Bool :=
  match declaration.construction with
  | .interactive => true
  | .derived _ => false

/-- Who proves and who verifies: exactly two roles are online. For an interactive scheme
nothing is inferred: the prover is the one written, the verifier the other online role. For
the others, `E` is the online roles that give to an online role and `D` the online roles that
own a coin that an online role hears. Each has at most one role, and not the same one. The
prover is the role of `E`, or, when `E` is empty, the online role not in `D`; the verifier is
the other. When both are empty, the prover is the declaration's. A prover that the declaration
writes must be the one computed. -/
def proverAndVerifier {V : Vocabulary} (hdr : ProtocolHeader V) (declaration : Declaration) :
    Option (Role × Role) :=
  match (List.range declaration.kinds.length).filter
      (fun i => declaration.kinds[i]? == some .online) with
  | [a, b] =>
      let online := fun x : Role => x == a || x == b
      let other := fun x : Role => if x = a then b else a
      if declaration.interactive then
        declaration.prover.bind fun p => if online p then some (p, other p) else none
      else
      let events := hdr.shape.events [] id
      let givers := [a, b].filter fun x => events.any fun e =>
        match e.cls with
        | .flow _ giver getters => giver == x && getters.any online
        | .given .. => false
      let drawers := [a, b].filter fun x => events.any fun e =>
        match e.cls with
        | .given (.coin ..) owner hearers => owner == x && hearers.any online
        | _ => false
      let computed : Option Role :=
        match givers, drawers with
        | [e], [] => some e
        | [], [d] => some (other d)
        | [e], [d] => if e = d then none else some e
        | [], [] => declaration.prover.bind fun p => if online p then some p else none
        | _, _ => none
      match computed with
      | some p => if declaration.prover.all (· == p) then some (p, other p) else none
      | none => none
  | _ => none

/-- The statement: the types of the inputs that both hold, in order. -/
def statementOf {V : Vocabulary} (hdr : ProtocolHeader V) (prover verifier : Role) :
    List V.Ty :=
  hdr.ins.filterMap fun a =>
    if prover ∈ a.holders ∧ verifier ∈ a.holders then some a.ty else none

/-- The witness: the types of the other inputs that the prover holds, in order. -/
def witnessOf {V : Vocabulary} (hdr : ProtocolHeader V) (prover verifier : Role) : List V.Ty :=
  hdr.ins.filterMap fun a =>
    if prover ∈ a.holders ∧ verifier ∉ a.holders then some a.ty else none

/-- The sites of the coins of a shape that some role hears: the coins that a derivation
replaces. -/
def Shape.heardCoins {V : Vocabulary} (s : Shape V) : List Site :=
  (s.events [] id).filterMap fun e =>
    match e.cls with
    | .given (.coin ..) _ (_ :: _) => some e.site
    | _ => none

end Zkc.Core
