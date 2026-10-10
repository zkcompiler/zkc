import Zkc.Source.PhaseAdmission
import Zkc.Source.Format

/-! Untrusted loop annotations use exact array arities and a bounded decoder.
The source, policy, entry phases and allowed return phases are supplied separately.
-/

set_option autoImplicit false

namespace Zkc.Source.PhaseAdmission

open Lean
variable {Phase : Type}

def encodeCertificate (phases : Format.Codec Phase) : Certificate Phase → Json
  | .terminal => .arr #[.str "terminal"]
  | .next tail => .arr #[.str "next", encodeCertificate phases tail]
  | .branch yes no =>
    .arr #[.str "branch", encodeCertificate phases yes, encodeCertificate phases no]
  | .loop invariant body next =>
    .arr #[.str "loop", .arr (invariant.map phases.encode).toArray,
      encodeCertificate phases body, encodeCertificate phases next]
  | .bind body next =>
    .arr #[.str "bind", encodeCertificate phases body, encodeCertificate phases next]

def decodeCertificate (phases : Format.Codec Phase) :
    Nat → Json → Except Format.Error (Certificate Phase)
  | 0, _ => .error .depthLimit
  | depth + 1, json => do
    match ← Format.array json with
    | [.str "terminal"] => return .terminal
    | [.str "next", tail] => return .next (← decodeCertificate phases depth tail)
    | [.str "branch", yes, no] =>
      return .branch (← decodeCertificate phases depth yes) (← decodeCertificate phases depth no)
    | [.str "loop", invariant, body, next] =>
      return .loop (← (← Format.array invariant).mapM phases.decode)
        (← decodeCertificate phases depth body) (← decodeCertificate phases depth next)
    | [.str "bind", body, next] =>
      return .bind (← decodeCertificate phases depth body) (← decodeCertificate phases depth next)
    | _ => .error .shape

def certificateCodec (phases : Format.Codec Phase) (depth : Nat) : Format.Codec (Certificate Phase) :=
  ⟨encodeCertificate phases, decodeCertificate phases depth⟩

end Zkc.Source.PhaseAdmission
