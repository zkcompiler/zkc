import Zkc.Source.Mathematical.Syntax

/-! Formation premises for the closed typed fragment. Canonical table admission,
static resource limits and wire decoding remain separate responsibilities. -/

set_option autoImplicit false
namespace Zkc.Source.Mathematical
variable {Role : Type} [DecidableEq Role] {parties : List Role} {language : Language}
  {capabilities : List (Capability Role language.Ty)} {scope : List (Signature Role language.Ty)}

def Program.sites {Γ results} : Program parties language capabilities scope Γ results → List Nat
  | .ret _ => []
  | .pure _ _ _ next => next.sites
  | .message site _ _ _ _ _ next => site :: next.sites
  | .query site _ _ _ _ _ next => site :: next.sites
  | .repeat site _ _ body next => site :: (body.sites ++ next.sites)
  | .guard site _ _ next => site :: next.sites
  | .invoke site _ _ _ next => site :: next.sites
  | .stop site _ _ => [site]

def PortsParticipate (ports : List (Port Role language.Ty)) : Prop :=
  ∀ port ∈ ports, port.roles.Nodup ∧ ∀ role ∈ port.roles, role ∈ parties

/-- Check every declared intermediate context, including dormant loop bodies. -/
def Program.participates {Γ results} (program : Program parties language capabilities scope Γ results) : Prop :=
  PortsParticipate (parties := parties) Γ ∧ PortsParticipate (parties := parties) results ∧
  match program with
  | .ret _ => True
  | .pure _ _ _ next => next.participates
  | .message _ _ sender receiver _ _ next =>
      sender ∈ parties ∧ receiver ∈ parties ∧ next.participates
  | .query _ owner _ _ _ _ next => owner ∈ parties ∧ next.participates
  | .repeat _ _ _ body next => body.participates ∧ next.participates
  | .guard _ owner _ next => owner ∈ parties ∧ next.participates
  | .invoke _ _ _ _ next => next.participates
  | .stop _ owner _ => owner ∈ parties

structure Program.Formed {Γ results}
    (program : Program parties language capabilities scope Γ results) : Prop where
  parties_unique : parties.Nodup
  sites_unique : program.sites.Nodup
  participants : program.participates

def Definitions.Formed {scope} : Definitions parties language capabilities scope → Prop
  | .nil => parties.Nodup
  | .snoc previous _ body => previous.Formed ∧ body.Formed

end Zkc.Source.Mathematical
