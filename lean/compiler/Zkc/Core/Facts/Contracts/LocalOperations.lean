module

public import Zkc.Core.Program.LocalRules

@[expose] public section

namespace Zkc.Core.BodyAnalysis
variable {V : Vocabulary}

/-- Decode the signature independently of the call site's operand list. This consults the same
owned operation resolver, row declarations and unique callee lookup as the local program reader. -/
def resolveLocal (fns : List (FnHeader V)) : LocalRaw V →
    Option ((ins outs : List V.Ty) × LocalOp V fns ins outs)
  | .row key =>
    match seen : V.row key with
    | some sig => some ⟨sig.ins,sig.outs,.row key sig seen⟩
    | none => none
  | .owned name types numbers =>
    (OwnedOp.resolve name types numbers).map fun ⟨ins,outs,op⟩ => ⟨ins,outs,.owned op⟩
  | .literal t data => if reads : V.Reads t data then some ⟨[],[t],.literal t data reads⟩ else none
  | .call key =>
    match Member.withKey (·.key) key fns with
    | [⟨hdr,callee⟩] => some ⟨hdr.ins,hdr.outs,.call callee⟩
    | _ => none

def localResultCount (fns : List (FnHeader V)) (op : LocalRaw V) : Nat :=
  match resolveLocal fns op with
  | some ⟨_,outs,_⟩ => outs.length
  | none => 0

end Zkc.Core.BodyAnalysis
