module

public import ZkcSecurity.FiatShamir.DomainReduction
public import Zkc.Construction.DomainView

@[expose] public section

/-! Local rules for constructed views. These rules expose an actual challenge
instruction to the existing reduction interface; they do not select a source
or replace its helper table. -/
set_option autoImplicit false
namespace ZkcSecurity.FiatShamir.DomainReduction
open Zkc.Source Zkc.Construction
variable {carriers : Structured.Carriers}

/-- A minimal interface for a query seam. Other operations refuse; clients use
this only for the corresponding local Process, never as a whole validator. -/
def queryInterface : Typed.Interface (Domain.effects carriers)
    (Domain.Event carriers) (Domain.Payload carriers) Domain.Raw
  | .query _ origin => .query (.challenge origin) some
  | _ => .refuse

def fieldReply {field : String} {origin : Origin}
    (request : origin.request = some (.draw field))
    (raw : Domain.Raw (.challenge origin : Domain.Event carriers)) : carriers.Field field := by
  simpa only [Domain.Raw, request, Request.draw] using raw

theorem drawRequest_of_request {origin : Origin} {field : String}
    (request : origin.request = some (.draw field)) : Domain.drawRequest origin = true := by
  rcases origin with ⟨entry, event, actual⟩
  simp only at request
  subst actual
  rfl

/-- The all-replies seam retains the full environment and exact nominal field.
The stored history is supplied by the caller representation, not fabricated by
receiving data. The request equality justifies the dependent reply transport. -/
theorem challenge_reading (context : Context) (suite field : String) (template : Template)
    (state coordinates : Nat) (env : Domain.Environment carriers)
    (history : Domain.History carriers) (path : List Nat) (origin : Origin)
    (transcript : env[state]? = some (.transcript suite history))
    (indices : env[coordinates]? = some (.indices path))
    (found : Domain.queryOrigin context suite field template path = some origin)
    (request : origin.request = some (.draw field)) :
    Reading queryInterface history
      (Domain.View.challenge context suite field template state coordinates
        [.data (.field field), .transcript suite] env)
      (.call (.query history origin) fun raw => .done
        (env ++ [.data (.field field (fieldReply request raw)),
          .transcript suite (history ++ [.challenge origin])])) := by
  have actual : Domain.View.challenge context suite field template state coordinates
      [.data (.field field), .transcript suite] env =
      .call (.query history origin) (fun raw => .done
        (env ++ [.data (.field field (fieldReply request raw)),
          .transcript suite (history ++ [.challenge origin])])) := by
    simp [Domain.View.challenge, transcript, indices, found, request, fieldReply,
      Domain.View.append, Domain.sortsMatch, Domain.Value.sort]
  rw [actual]
  apply ReadingTo.query (I := Domain.effects carriers) history origin _ (.query history origin) _ id
    (drawRequest_of_request request) rfl
  exact fun _ => .done _ _ trivial

theorem challenge_coherent (context : Context) (suite field : String) (template : Template)
    (state coordinates : Nat) (env : Domain.Environment carriers)
    (history : Domain.History carriers) (path : List Nat) (origin : Origin)
    (transcript : env[state]? = some (.transcript suite history))
    (indices : env[coordinates]? = some (.indices path))
    (found : Domain.queryOrigin context suite field template path = some origin)
    (request : origin.request = some (.draw field)) :
    Coherent history (Domain.View.challenge context suite field template state coordinates
      [.data (.field field), .transcript suite] env) := by
  have actual : Domain.View.challenge context suite field template state coordinates
      [.data (.field field), .transcript suite] env =
      .call (.query history origin) (fun raw => .done
        (env ++ [.data (.field field (fieldReply request raw)),
          .transcript suite (history ++ [.challenge origin])])) := by
    simp [Domain.View.challenge, transcript, indices, found, request, fieldReply,
      Domain.View.append, Domain.sortsMatch, Domain.Value.sort]
  rw [actual]
  exact .query history origin _ (drawRequest_of_request request) (fun _ => .done _ _ trivial)

end ZkcSecurity.FiatShamir.DomainReduction
