import Zkc.Compiler.Blocks.Typing

/-! Fixed scalar and FRI operation signatures for the retained block clients.
These names select typed contracts; they do not attest to an external provider.
-/

set_option autoImplicit false
namespace Zkc.Protocols.BlockProfiles
open Zkc.Compiler.Blocks

def registry (profile : String) (op : String) : Option (Signature String) :=
  if profile == "sumcheck:q2305843009213697249" then
    if op == "field.add" || op == "field.mul" then
      some ⟨"scalar:q2305843009213697249","scalar:q2305843009213697249","scalar:q2305843009213697249"⟩
    else none
  else if profile == "fri:babybear-r19" then
    match op with
    | "p3.node" => some ⟨"digest:p3","digest:p3","digest:p3"⟩
    | "p3.leaf" => some ⟨"row:p3","unit","digest:p3"⟩
    | "digest.of_words" => some ⟨"words8:u32","unit","digest:p3"⟩
    | "word.odd" => some ⟨"word:u64","unit","flag"⟩
    | "word.shr" => some ⟨"word:u64","shift:u6","word:u64"⟩
    | _ => none
  else none

end Zkc.Protocols.BlockProfiles
