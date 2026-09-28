import Zkc.Source.Mathematical.Meaning

/-! Semantic separators for the mathematical core. These finite arithmetic
fixtures exercise source constructors; they are not cryptographic protocols. -/

set_option autoImplicit false
namespace Examples.Mathematical
open Zkc.Source Zkc.Source.Mathematical

inductive Party where | prover | verifier
  deriving DecidableEq, Repr

inductive TypeCode where | number | index (count : Nat)
  deriving DecidableEq, Repr

inductive Operation where | add | indexValue (count : Nat)

abbrev language : Mathematical.Language where
  Ty := TypeCode
  Op := Operation
  arguments | .add => [.number, .number] | .indexValue n => [.index n]
  result _ := .number
  index := .index
  condition := .number
  Wire _ := Unit

abbrev Value : TypeCode → Type
  | .number => Nat
  | .index n => Fin n

abbrev meaning : Interpretation language where
  Value := Value
  pure
    | .add, .cons x (.cons y .nil) => x + y
    | .indexValue _, .cons i .nil => i.val
  index i := i
  condition value := value != 0

abbrev parties : List Party := [.prover, .verifier]
abbrev shared : Port Party TypeCode := ⟨parties, .number⟩
abbrev privateInput : Port Party TypeCode := ⟨[.prover], .number⟩

/-- One authored message and one authored addition, available at both roles. -/
def doubleMessage : Mathematical.Program parties language [] [] [privateInput] [shared] :=
  .message 0 () .prover .verifier (by decide) (.exact .here)
    (.pure (roles := parties) .add (.cons ⟨parties, .here⟩ (.cons ⟨parties, .here⟩ .nil)) (by decide)
      (.ret (.cons (.exact .here) .nil)))

def privateEnv (self : Party) (sent : Nat) : Mathematical.Environment Value self [privateInput]
  | _, .here => fun _ => sent

/-- The receiver result varies with the reply, independently of the sent input. -/
theorem receiver_is_fresh (sent : Nat) :
    doubleMessage.openMeaning meaning .verifier (privateEnv .verifier sent) =
      .call (.receive (ty := .number) ⟨[], 0⟩ () .prover) (fun reply =>
        .done (.cons (fun _ => reply + reply) .nil)) := rfl

theorem sender_aliases_operand (sent : Nat) :
    doubleMessage.openMeaning meaning .prover (privateEnv .prover sent) =
      .call (.send (ty := .number) ⟨[], 0⟩ () .verifier sent) (fun _ =>
        .done (.cons (fun _ => sent + sent) .nil)) := rfl

abbrev counter : Capability Party TypeCode := ⟨[.verifier], [], .number⟩

/-- The same capability operand occurs twice; no fresh service is introduced. -/
def sharedService : Mathematical.Program parties language [counter] [] [] [] :=
  .query 0 .verifier .here (by decide) .nil (by decide)
    (.query 1 .verifier .here (by decide) .nil (by decide)
      (.stop 2 .verifier .reject))

def emptyEnv (self : Party) : Mathematical.Environment Value self [] := fun ref => nomatch ref

def counterHandler : PIR.Handler (interface Party.verifier language [counter] Value) Nat Nat
  | .query location .here _ .nil, state => ⟨.returned state, state + 1, [location.site]⟩
  | .send .., state => ⟨.returned (), state, []⟩
  | .receive .., state => ⟨.stopped .refused, state, []⟩
  | .stop location reason, state => ⟨.stopped reason, state, [location.site]⟩

theorem shared_service_preserves_stopped_state :
    (sharedService.openMeaning meaning .verifier (emptyEnv .verifier)).run counterHandler 0 =
      ⟨.stopped .reject, 2, [0, 1, 2]⟩ := rfl

abbrev helperSignature : Mathematical.Signature Party TypeCode :=
  ⟨[], [⟨[.verifier], .number⟩]⟩

def helper : Mathematical.Program parties language [counter] []
    helperSignature.arguments helperSignature.results :=
  .query 0 .verifier .here (by decide) .nil (by decide)
    (.message 1 () .verifier .prover (by decide) (.exact .here)
      (.ret (.cons (.exact (.there .here)) .nil)))

def definitions : Mathematical.Definitions parties language [counter] [helperSignature] :=
  Mathematical.Definitions.snoc (parties := parties) (language := language)
    (capabilities := [counter]) .nil helperSignature helper

def invokeTwice : Mathematical.Program parties language [counter] [helperSignature] [] [] :=
  .invoke 10 .here (fun ref => ref) .nil
    (.invoke 11 .here (fun ref => ref) .nil (.stop 12 .verifier .reject))

def locationHandler : PIR.Handler (interface Party.verifier language [counter] Value) Nat Location
  | .query location .here _ .nil, state => ⟨.returned state, state + 1, [location]⟩
  | .send location .., state => ⟨.returned (), state, [location]⟩
  | .receive .., state => ⟨.stopped .refused, state, []⟩
  | .stop location reason, state => ⟨.stopped reason, state, [location]⟩

/-- Stored helper reuse preserves both the root service and dynamic sites. -/
theorem stored_helper_keeps_state_and_paths :
    (invokeTwice.denote meaning .verifier (definitions.denote meaning .verifier)
      (fun ref => ref) [] (emptyEnv .verifier)).run locationHandler 0 =
      ⟨.stopped .reject, 2,
        [⟨[.invocation 10], 0⟩, ⟨[.invocation 10], 1⟩,
         ⟨[.invocation 11], 0⟩, ⟨[.invocation 11], 1⟩, ⟨[], 12⟩]⟩ := rfl

/-- The index is a real input to the compact body, including for symbolic n. -/
def sumIndices (n : Nat) : Mathematical.Program parties language [] [] [shared] [shared] :=
  .repeat 0 n (.cons (.exact .here) .nil)
    (.pure (roles := parties) (.indexValue n) (.cons ⟨parties, .here⟩ .nil) (by rfl)
      (.pure (roles := parties) .add
        (.cons ⟨parties, .here⟩ (.cons ⟨parties, .there (.there .here)⟩ .nil)) (by rfl)
        (.ret (.cons (.exact .here) .nil))))
    (.ret (.cons (.exact .here) .nil))

def sharedEnv (self : Party) (initial : Nat) : Mathematical.Environment Value self [shared]
  | _, .here => fun _ => initial

example (initial : Nat) :
    (sumIndices 0).openMeaning meaning .verifier (sharedEnv .verifier initial) =
      .done (.cons (fun _ => initial) .nil) := rfl

example : (sumIndices 3).openMeaning meaning .verifier (sharedEnv .verifier 7) =
    .done (.cons (fun _ => 10) .nil) := rfl

/-- An uninvolved role sees no message action and no unavailable result. -/
def bystanderSource : Mathematical.Program [0, 1, 2] language [] [] [⟨[0], .number⟩] [] :=
  .message 0 () 0 1 (by decide) (.exact .here) (.ret .nil)

def bystanderEnv (sent : Nat) : Mathematical.Environment Value 2 [⟨[0], .number⟩]
  | _, .here => fun _ => sent

example (sent : Nat) :
    bystanderSource.openMeaning meaning 2 (bystanderEnv sent) = .done .nil := rfl

example : sharedService.openMeaning meaning .prover (emptyEnv .prover) = .halt .incomplete := rfl

/-- Two formal service names can resolve to the same root. -/
def bothRoots : Mathematical.Program parties language [counter, counter] [] [] [] :=
  .query 0 .verifier .here (by decide) .nil (by decide)
    (.query 1 .verifier (.there .here) (by decide) .nil (by decide) (.stop 2 .verifier .reject))

def aliasRoots : CapabilityBinding [counter, counter]
  | _, .here => .here
  | _, .there .here => .here

def twoCounterHandler : PIR.Handler (interface Party.verifier language [counter, counter] Value)
    (Nat × Nat) Nat
  | .query _ .here _ .nil, (left, right) => ⟨.returned left, (left + 1, right), [left]⟩
  | .query _ (.there .here) _ .nil, (left, right) => ⟨.returned right, (left, right + 1), [right]⟩
  | .stop _ reason, state => ⟨.stopped reason, state, []⟩
  | .send .., state => ⟨.returned (), state, []⟩
  | .receive .., state => ⟨.stopped .refused, state, []⟩

theorem aliased_ports_share_one_state :
    (bothRoots.denote meaning .verifier (Mathematical.Definitions.denote (parties := parties) (capabilities := [counter, counter]) meaning Party.verifier .nil)
      aliasRoots [] (emptyEnv .verifier)).run twoCounterHandler (0, 0) =
      ⟨.stopped .reject, (2, 0), [0, 1]⟩ := rfl

theorem distinct_roots_keep_separate_state :
    (bothRoots.openMeaning meaning .verifier (emptyEnv .verifier)).run twoCounterHandler (0, 0) =
      ⟨.stopped .reject, (1, 1), [0, 0]⟩ := rfl

abbrev emptySignature : Mathematical.Signature Party TypeCode := ⟨[], []⟩

def entryDefinitions : Mathematical.Definitions parties language [counter] [emptySignature, helperSignature] :=
  Mathematical.Definitions.snoc definitions emptySignature invokeTwice

example : (entryDefinitions.entry meaning .verifier .here (fun ref => ref) .nil).run
    locationHandler 0 = ⟨.stopped .reject, 2,
      [⟨[.invocation 10], 0⟩, ⟨[.invocation 10], 1⟩,
       ⟨[.invocation 11], 0⟩, ⟨[.invocation 11], 1⟩, ⟨[], 12⟩]⟩ := rfl

end Examples.Mathematical
