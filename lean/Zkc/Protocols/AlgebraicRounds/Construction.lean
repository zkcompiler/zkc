import Zkc.Protocols.AlgebraicRounds.Source

/-! Construction-level effects, distinct from logical interactive round calls. -/

set_option autoImplicit false

namespace Zkc.Protocols.AlgebraicRounds

open PIR

namespace Construction

/-- Structured frames retain unambiguous kind, position, initial claim and domain.
No byte codec, hash assumption or random-oracle security is asserted here. -/
inductive Frame (F : Type) where
  | context (domain : String) (rounds : Nat) (claim : F)
  | statement (schema : String) (values : List F)
  | message (round : Nat) (value : Message F)
  | request (round : Nat)
  | challenge (round : Nat) (value : F)
  deriving DecidableEq, Repr

inductive Call (F : Type) where
  | receive
  | absorb (message : Message F)
  | sample
  | squeeze
  | reject
  deriving DecidableEq, Repr

abbrev interface (F : Type) : Signature := ⟨Call F, fun
  | .receive => Message F
  | .sample | .squeeze => F
  | .absorb _ | .reject => Unit⟩

inductive Event (F : Type) where
  | message (value : Message F)
  | challenge (value : F)
  | query (frames : List (Frame F))
  | reject
  deriving DecidableEq, Repr

/-- Provider transitions retain residual state even when no challenge returns. -/
abbrev Draw (F Q : Type) := Q → Outcome F × Q
abbrev Query (F Q : Type) := List (Frame F) → Q → Outcome F × Q

def fresh {F : Type} : OperationInterpretation (AlgebraicRounds.interface F) (interface F)
  | .message => .call .receive .done
  | .challenge => .call .sample .done
  | .reject => .call .reject .done

def framed {F : Type} : OperationInterpretation (AlgebraicRounds.interface F) (interface F)
  | .message => .call .receive fun message => .call (.absorb message) fun _ => .done message
  | .challenge => .call .squeeze .done
  | .reject => .call .reject .done

variable {F : Type} [Semiring F] [DecidableEq F]

def freshInteraction : Interaction (interface F) where
  Role := Role
  Phase := Phase F
  owner := fun | .receive => .prover | _ => .verifier
  enabled phase op := match op with
    | .receive => interaction.enabled phase .message
    | .sample => interaction.enabled phase .challenge
    | .reject => interaction.enabled phase .reject
    | _ => False
  advance phase op reply := match op with
    | .receive => interaction.advance phase .message reply
    | .sample => interaction.advance phase .challenge reply
    | .reject => interaction.advance phase .reject reply
    | _ => phase

def freshAdmission : InterpretationAdmission (interaction (F := F)) freshInteraction fresh where
  phases := Eq
  operation := by
    intro phase op enabled lowerPhase initial
    subst lowerPhase
    cases op <;> exact ⟨⟨enabled, fun _ => trivial⟩, fun _ => rfl⟩

inductive FramedPhase (F : Type) where
  | ready (phase : Phase F)
  | pending (phase : Phase F) (message : Message F)

def framedInteraction : Interaction (interface F) where
  Role := Role
  Phase := FramedPhase F
  owner := fun | .receive => .prover | _ => .verifier
  enabled phase op := match phase, op with
    | .ready phase, .receive => interaction.enabled phase .message
    | .ready phase, .squeeze => interaction.enabled phase .challenge
    | .ready phase, .reject => interaction.enabled phase .reject
    | .pending _ expected, .absorb actual => expected = actual
    | _, _ => False
  advance phase op reply := match phase, op with
    | .ready phase, .receive => .pending phase reply
    | .ready phase, .squeeze => .ready (interaction.advance phase .challenge reply)
    | .ready phase, .reject => .ready (interaction.advance phase .reject reply)
    | .pending phase _, .absorb message => .ready (interaction.advance phase .message message)
    | _, _ => phase

def framedAdmission : InterpretationAdmission (interaction (F := F)) framedInteraction framed where
  phases phase lowerPhase := lowerPhase = .ready phase
  operation := by
    intro phase op enabled lowerPhase initial
    subst lowerPhase
    cases op with
    | message => exact ⟨⟨enabled, fun _ => ⟨rfl, fun _ => trivial⟩⟩, fun _ _ => rfl⟩
    | challenge => exact ⟨⟨enabled, fun _ => trivial⟩, fun _ => rfl⟩
    | reject => exact ⟨⟨enabled, fun _ => trivial⟩, fun _ => rfl⟩

theorem fresh_formed (count : Nat) (claim : F) :
    Conforms freshInteraction ((rounds count claim).interpret fresh) (start count claim) :=
  (freshAdmission.transport (rounds count claim) _ _ _
    (formed count claim) (returns count claim) rfl).1

theorem framed_formed (count : Nat) (claim : F) :
    Conforms framedInteraction ((rounds count claim).interpret framed) (.ready (start count claim)) :=
  (framedAdmission.transport (rounds count claim) _ _ _
    (formed count claim) (returns count claim) rfl).1

theorem framed_returns (count : Nat) (claim : F) :
    Boundary.Returns framedInteraction (fun _ phase => ∃ upperPhase,
      upperPhase = .finished ∧ phase = .ready upperPhase)
      ((rounds count claim).interpret framed) (.ready (start count claim)) :=
  (framedAdmission.transport (rounds count claim) _ _ _
    (formed count claim) (returns count claim) rfl).2

theorem fresh_bounded (count : Nat) (claim : F) :
    Within (2 * count) ((rounds count claim).interpret fresh) := by
  simpa using Proc.within_interpret fresh 1
    (fun op => by cases op <;> exact fun _ => trivial) _ _ (bounded count claim)

theorem framed_bounded (count : Nat) (claim : F) :
    Within (2 * count * 2) ((rounds count claim).interpret framed) :=
  Proc.within_interpret framed 2
    (fun op => by cases op <;> simp [framed, Within]) _ _ (bounded count claim)

theorem structured_source (construction : OperationInterpretation
    (AlgebraicRounds.interface F) (interface F)) (count : Nat)
    (env : Source.Environment (Value F) [.scalar]) :
    (program count).denote (meaning.translate construction) env =
      (rounds count (env .here)).interpret construction := by
  rw [Source.Program.denote_translate, program_denote]

end Construction
end Zkc.Protocols.AlgebraicRounds
