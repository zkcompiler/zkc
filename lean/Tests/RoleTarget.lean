import Zkc.Compiler.Role.Runner

/-! Independently authored heterogeneous target and actual local branch/call table.
This consumer does not import projection or the direct source-role interpreter.
-/

set_option autoImplicit false

namespace Tests.RoleTarget

open Zkc.Source Zkc.Compiler.Role

inductive Party where
  | prover | verifier
  deriving DecidableEq, Repr

inductive Ty where
  | word | bit
  deriving DecidableEq, Repr

abbrev Value : Ty → Type
  | .word => Nat
  | .bit => Bool

inductive Op where
  | bump | valid

abbrev language : Language where
  Ty := Ty
  Op := Op
  arguments _ := [.word]
  result
    | .bump => .word
    | .valid => .bit
  condition := .bit

abbrev localSignature : DefinitionSignature Ty := ⟨[.word, .bit], .word⟩

/-- The actual local body branches on a typed input, then on a typed primitive reply. -/
def checked : Zkc.Source.Definitions language [localSignature] :=
  Zkc.Source.Definitions.snoc (language := language) .nil localSignature
    (.branch (.there .here)
      (.letOp (.primitive .valid) (.cons .here .nil)
        (.branch .here (.ret (.there .here)) (.stop .reject)))
      (.stop .refused))

/-- An actual stored local call, followed by a primitive; a stopped child skips bump. -/
def localDefinitions := checked.snoc localSignature
  (.letOp (.call .here) (.cons .here (.cons (.there .here) .nil))
    (.letOp (.primitive .bump) (.cons .here .nil) (.ret .here)))

inductive Request where
  | bump (word : Nat)
  | valid (word : Nat)

abbrev effects : PIR.Signature where
  Op := Request
  Reply
    | .bump _ => Nat
    | .valid _ => Bool

abbrev Event := String × Nat

def implementation (binding : Nat) : Protocol.LocalImplementation language Value Nat Event where
  effects := effects
  condition := id
  operation
    | .bump, .cons value .nil => .call (.bump value) .done
    | .valid, .cons value .nil => .call (.valid value) .done
  handler
    | .bump value, state => ⟨.returned (value + binding), state + 1, [("bump", value)]⟩
    | .valid value, state => ⟨.returned (value < 10), state + 1, [("valid", value)]⟩

def runtime (word : Nat) (bit : Bool) :
    Protocol.Role.Runtime Party String Nat String language Value Nat Event where
  implementations := implementation
  send {ty} _ _ _ value state :=
    match ty, value with
    | .word, value => ⟨.returned (), state + 10, [("send.word", value)]⟩
    | .bit, value => ⟨.returned (), state + 10, [("send.bit", if value then 1 else 0)]⟩
  receive ty _ _ _ state :=
    match ty with
    | .word => ⟨.returned word, state + 100, [("receive.word", word)]⟩
    | .bit => ⟨.returned bit, state + 100, [("receive.bit", if bit then 1 else 0)]⟩

abbrev outputs : List (Protocol.Port Party Ty) := [(.verifier, .word), (.verifier, .bit)]

/-- A hand-authored role body: receive/receive/actual local child/send/return.
Neither receive has a source sender operand or a packet manufactured by send.
-/
def receiver : Program Nat Party.verifier Nat String language [localSignature, localSignature] []
    [] outputs :=
  .receive .word 10 "word" .prover (by decide)
    (.receive .bit 11 "flag" .prover (by decide)
      (.localCall 12 .here (.cons (.there .here) (.cons .here .nil))
        (.send 13 "result" .prover (by decide) .here
          (.ret (.cons .here (.cons (.there .here) .nil))))))

abbrev signature : Protocol.Signature Party Ty := ⟨[], outputs⟩
def definitions : Definitions Nat Party.verifier Nat String language
    [localSignature, localSignature] [signature] :=
  Definitions.snoc (language := language) .nil signature receiver

def process := definitions.denote (Value := Value) .here "standalone" 1 []
  Protocol.Role.Environment.empty

def execute (word : Nat) (bit : Bool) :=
  process.run ((runtime word bit).handler localDefinitions) ⟨0, none⟩

def outcome : PIR.Outcome (Protocol.Role.Environment Value Party.verifier outputs) →
    PIR.Outcome (Nat × Bool)
  | .returned values => .returned (values .here, values (.there .here))
  | .stopped reason => .stopped reason

example : outcome (execute 7 true).outcome = .returned (8, true) := by cbv
example : (execute 7 true).state.localState = 212 := by cbv
example : (execute 7 true).events.map (fun event => event.value) =
    [("receive.word", 7), ("receive.bit", 1), ("valid", 7), ("bump", 7), ("send.word", 8)] := by cbv
example : outcome (execute 100 true).outcome = .stopped .reject := by cbv
example : (execute 100 true).state.localState = 201 := by cbv
example : (execute 100 true).events.map (fun event => event.value) =
    [("receive.word", 100), ("receive.bit", 1), ("valid", 100)] := by cbv
example : (execute 100 true).state.stoppedAt = some ⟨"standalone", 1, [], 12⟩ := by cbv
example : outcome (execute 7 false).outcome = .stopped .refused := by cbv
example : (execute 7 false).state.localState = 200 := by cbv
example : (execute 7 false).events.length = 2 := by cbv

/-- Actual primitive replies are arbitrary too: overriding `valid` changes the branch. -/
def hostileService : Protocol.Role.Runtime Party String Nat String language Value Nat Event :=
  { runtime 100 true with
    implementations := fun binding =>
      { implementation binding with
        handler := fun request state =>
          match request with
          | .bump value => ⟨.returned (value + binding), state + 1, [("bump", value)]⟩
          | .valid value => ⟨.returned true, state + 1, [("lie", value)]⟩ } }
example : outcome (process.run (hostileService.handler localDefinitions) ⟨0, none⟩).outcome =
    .returned (101, true) := by cbv

/-- The same-signature second target body is actually interpreted. -/
def changed := definitions.snoc signature (.stop 99 .abort)
example : outcome ((changed.denote (Value := Value) .here "standalone" 1 []
    Protocol.Role.Environment.empty).run ((runtime 7 true).handler localDefinitions)
      ⟨0, none⟩).outcome = .stopped .abort := by cbv
example : outcome ((changed.denote (Value := Value) (.there .here) "standalone" 1 []
    Protocol.Role.Environment.empty).run ((runtime 7 true).handler localDefinitions)
      ⟨0, none⟩).outcome = .returned (8, true) := by cbv

/-- Four interface actions; the local child has two finer primitive actions inside it. -/
example : PIR.Within 4 process := fun _ _ _ _ => True.intro
example : ¬ PIR.Within 3 process := by
  intro bound
  exact bound 0 false 0

/-- Consume the first receive, suspend at the second, then resume without replay. -/
def firstOnly : Protocol.Role.Ingress Party String Nat String language Value Nat Event
  | .word, location, schema, sender, state =>
      some ((runtime 7 true).receive .word location schema sender state)
  | .bit, _, _, _, _ => none

def suspended := advance ((runtime 7 true).poll localDefinitions firstOnly) 8
  ⟨process, ⟨0, none⟩, []⟩

example : (match suspended with
    | .suspended cursor => (cursor.state.localState, cursor.events.map (fun event => event.value))
    | _ => (0, [])) = (100, [("receive.word", 7)]) := by cbv
example : (match suspended with
    | .suspended ⟨.call (.receive ty location schema _) _, _, _⟩ => some (ty, location.site, schema)
    | _ => none) = some (.bit, 11, "flag") := by cbv

/-- Even repeated absence retains the same cursor exactly. -/
example : suspended.resume ((runtime 7 true).poll localDefinitions firstOnly) 8 = suspended := by cbv

example : suspended.resume (fun op state =>
    some ((runtime 7 true).handler localDefinitions op state)) 8 =
      .finished (execute 7 true) := by cbv

-- Kernel-checked theorems above; these are additional interpreter smoke outputs.
-- The three outcomes this fixture reaches: an accepted run, a bound the
-- target rejects, and a role that refuses.
#guard outcome (execute 7 true).outcome = .returned (8, true)
#guard outcome (execute 100 true).outcome = .stopped .reject
#guard outcome (execute 7 false).outcome = .stopped .refused

end Tests.RoleTarget
