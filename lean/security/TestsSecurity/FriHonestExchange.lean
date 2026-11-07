import ZkcSecurityExamples.FriHonestExchange

namespace TestsSecurity.FriHonestExchange
open Zkc.Source Zkc.Source.Structured ZkcExamples.Structured.FriSource
open ZkcSecurity.Domains.KoalaBearModel (model)
open ZkcSecurity.Domains.KoalaBear (Octic generator)
open ZkcSecurity.Examples.FriHonestExchange

private def check (shift : Octic) (polynomial : Octic → Octic) (fields : List Octic) (positions : List Nat) : IO Unit := do
  let .ok points := Numerical.points model.toFieldModel extension shift 32 | throw (IO.userError "coset")
  let (prover, checked) := exchange shift (points.map polynomial) fields positions
  let traffic := prover.state.oracle.provider.auxiliary
  let holderReturned := match prover.outcome with | .returned _ => true | .stopped _ => false
  unless holderReturned && traffic.fields.isEmpty && traffic.positions.isEmpty && prover.state.parents.isEmpty do
    throw (IO.userError "holder failed or consumed the wrong draws")
  let run := fun (messages : List Transfer) ↦ verifier (model := model) (m := Id) shift 3 8 0 {messages} replay receive
  let verifierAccepted := match checked.outcome with
    | .returned values => (values.get .here).bind ProtocolValue.toConcrete == some true
    | .stopped _ => false
  unless verifierAccepted && checked.state.oracle.queries == 96 && checked.state.parents.isEmpty &&
      checked.state.oracle.provider.auxiliary.messages.isEmpty do
    throw (IO.userError "honest exchange failed or left messages unread")
  -- Same-typed publication, different occurrence. Detect the swap before a
  -- later field or query draw could conceal it.
  let .word row first :: challenge :: .word nextRow next :: rest := traffic.messages
    | throw (IO.userError "initial exchange order")
  let wrong := run (.word nextRow next :: challenge :: .word row first :: rest)
  let refused := match wrong.outcome with | .stopped .refused => true | _ => false
  unless refused && wrong.state.oracle.provider.words.isEmpty do
    throw (IO.userError "a later publication occupied the first source send")

#eval do
  check generator (fun x ↦ x^7 + generator*x^4 + 11*x + 1) [0, generator + 5, 9] [31, 0, 0, 16, 27, 1, 3, 31]
  check 7 (fun _ ↦ 0) [9, 0, 9] [0, 0, 0, 0, 0, 0, 0, 0]
  IO.println "FRI-HONEST-EXCHANGE-PASS two paired runs and two misordered publication controls"

end TestsSecurity.FriHonestExchange
