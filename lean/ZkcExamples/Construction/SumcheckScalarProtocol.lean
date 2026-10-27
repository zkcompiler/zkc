module

public import ZkcExamples.Construction.SumcheckDomainRoot

@[expose] public section
/-! The finite scalar protocol normal form at the retained Sumcheck boundary.
It describes messages and challenges, without interpreting instructions. -/
set_option autoImplicit false
namespace ZkcExamples.Construction.SumcheckDomainConnection
open Zkc Zkc.Source Zkc.Source.Structured Zkc.Construction
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
variable {m : Type → Type} [Monad m]

def scalarRoundK {R : Type} (challenge : History F G → m F)
    (point : List F) (scalar : F) (history : History F G) (proof : Proof F G)
    (next : List F → F → History F G → Proof F G → m (PIR.Outcome R × Proof F G)) :
    m (PIR.Outcome R × Proof F G) :=
  match proof with
  | .field domain low :: unread =>
      if domain = "bls12-381.fr" then
        match unread with
        | .field domain high :: rest =>
            if domain = "bls12-381.fr" then
              if scalar = low + high then do
                let drawn : History F G := history ++ [.message (staticOrigin lowTemplate) (.field "bls12-381.fr" low),
                  .message (staticOrigin highTemplate) (.field "bls12-381.fr" high),
                  .challenge (staticOrigin drawTemplate)]
                let answer ← challenge drawn
                next (point ++ [answer]) ((1 - answer) * low + answer * high)
                  (drawn ++ [.message (staticOrigin deliveryTemplate) (.field "bls12-381.fr" answer)]) rest
              else pure (.stopped .reject, rest)
            else pure (.stopped .refused, unread)
        | _ => pure (.stopped .refused, unread)
      else pure (.stopped .refused, proof)
  | _ => pure (.stopped .refused, proof)

end ZkcExamples.Construction.SumcheckDomainConnection
