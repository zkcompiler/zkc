import Zkc.Core.Functions

/-!
The shapes of protocols that differ, as typed terms.

Each is written directly in the typed program, with every proof that a term carries, and as
a definition of a program with what elaboration decides about its body. They are small on purpose: what they check is that the
typing of the protocol dialect admits each shape, with any number of roles, and, for some,
that the meaning computes.
-/

namespace Zkc.Core.Shapes

/-- A vocabulary with no nominal type and no row: the core's own types and operations, and
one law, a natural. -/
def plain : Vocabulary where
  TypeKey := Empty
  RowKey := Empty
  LawKey := Unit
  row r _ := nomatch r
  law _ _ := some ⟨[], .nat⟩
  type r _ := nomatch r
  literal r _ _ := nomatch r

/-- A model of the plain vocabulary: every natural is in the support of its law. -/
def plainModel : Model plain where
  Carrier key _ := nomatch key
  valid key _ _ := nomatch key
  literal key _ _ := nomatch key
  apply row _ _ _ _ := nomatch row
  inDomain row _ _ _ _ := nomatch row
  defined row _ _ _ _ := nomatch row
  total row _ _ _ _ _ := nomatch row
  decides row _ _ _ _ _ _ _ _ _ _ := nomatch row
  keeps row _ _ _ _ _ _ _ := nomatch row
  literals key _ _ _ := nomatch key
  support _ _ _ _ _ _ := True
  supported _ _ _ h _ _ _ _ := by
    cases h
    trivial

abbrev none : Headers plain := ⟨[], []⟩

/-- A natural held by the roles. -/
abbrev nat (holders : Holders) : LTy plain := ⟨.nat, holders⟩

/-- No functions and no protocols to apply. -/
def noFns : FnTable plainModel none.fns := fun _ f => nomatch f
def noProtocols : GTable plainModel none.protocols := fun _ p => nomatch p
def noPrograms : RTable plainModel none.protocols := fun _ p => nomatch p

/-! ## Three roles: a value passed along -/

/-- The first role gives a value to the second, and the second gives it to the third. -/
def relay : Term (protocolDialect plain none) [nat [0]] [nat [0, 1, 2]] :=
  .op ⟨1⟩ (.flow .message 0 [1] (by decide) (by decide)) (.cons .head .nil) <|
  .op ⟨2⟩ (.flow .message 1 [2] (by decide) (by decide)) (.cons .head .nil) <|
  .ret (.cons .head .nil)

def relayHeader : ProtocolHeader plain := ⟨⟨10⟩, 3, [nat [0]], [nat [0, 1, 2]], shapeOf relay⟩

def relayProgram : Defs plain ⟨[], [relayHeader]⟩ :=
  .protocol relayHeader relay ⟨by simp [Within, ProtocolOp.Within, relay, relayHeader], by decide,
    by simp [Enclosed, relay], rfl, rfl, rfl, rfl⟩ .nil

/-- The second role's program: it gets the value and gives it on. -/
example : Term (roleDialect plain none 1) [nat [0]] [nat [0, 1, 2]] := project 1 relay

/-! ## A choice over a variant that one role holds -/

/-- A natural or a truth value. -/
abbrev either : Ty Empty := .variant ⟨7⟩ (.cons .nat (.cons .bool .nil))

/-- The first role chooses on a variant that it alone holds; nobody else acts in the
regions, and nobody else learns which ran. Then it gives what the choice gave. -/
def choice : Term (protocolDialect plain none) [⟨either, [0]⟩] [nat [0, 1]] :=
  .cases (mid := [nat [0]]) ⟨1⟩ [0] .head ⟨_, _, rfl, rfl, by decide, by decide⟩
    (fun a ha r hr => by
      simp only [List.mem_singleton] at ha
      subst ha
      exact hr)
    (.cons (.ret (.cons .head .nil)) <|
      .cons
        (.op ⟨2⟩ (.compute [0] (.literal .nat [0] rfl) [] rfl (fun _ ha => nomatch ha)) .nil <|
          .ret (.cons .head .nil)) <|
      .nil) <|
  .op ⟨3⟩ (.flow .message 0 [1] (by decide) (by decide)) (.cons .head .nil) <|
  .ret (.cons .head .nil)

example : Enclosed choice := by
  simp [Enclosed, EnclosedArms, WithinArms, Within, ProtocolOp.Within, choice]

/-- The other role passes over the choice and gets the value. -/
example : Term (roleDialect plain none 1) [⟨either, [0]⟩] [nat [0, 1]] := project 1 choice

/-! ## Rounds in a loop, each an application -/

/-- One round: the second role draws a natural that the first hears, and both add it to what
is carried. -/
def round : Term (protocolDialect plain none) [nat [0, 1]] [nat [0, 1]] :=
  .op ⟨1⟩ (.given (.coin () []) 1 [0] [] .nat ⟨_, rfl, rfl, rfl⟩ (fun _ ha => nomatch ha)
    (by decide)) .nil <|
  .op ⟨2⟩ (.compute [0, 1] (.owned .natAdd) [nat [0, 1], nat [0, 1]] rfl
    (fun a ha r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl <;> exact hr)) (.cons .head (.cons (.tail .head) .nil)) <|
  .ret (.cons .head .nil)

def roundHeader : ProtocolHeader plain := ⟨⟨20⟩, 2, [nat [0, 1]], [nat [0, 1]], shapeOf round⟩

abbrev withRound : Headers plain := ⟨[], [roundHeader]⟩

/-- As many rounds as a count that both hold says, each an application of the round with the
roles as they are. The role map is computed from the list of roles. -/
def rounds : Term (protocolDialect plain withRound) [nat [0, 1], nat [0, 1]] [nat [0, 1]] :=
  .loop (carried := [nat [0, 1]]) (each := []) ⟨1⟩ [0, 1] (.value .head ⟨rfl, by decide, by decide⟩)
    (fun a ha r hr => by
      simp only [List.append_nil, List.mem_singleton] at ha
      subst ha
      exact hr)
    (.cons (.tail .head) .nil)
    (.op ⟨2⟩ (.apply (hdr := roundHeader) .head [0, 1] (by decide) rfl [nat [0, 1]]
        ⟨⟨rfl, by decide⟩, trivial⟩)
      (.cons (.tail .head) .nil) <|
      .ret (.cons .head .nil)) <|
  .ret (.cons .head .nil)

def roundsHeader : ProtocolHeader plain :=
  ⟨⟨21⟩, 2, [nat [0, 1], nat [0, 1]], [nat [0, 1]], shapeOf rounds⟩

def roundsProgram : Defs plain ⟨[], [roundsHeader, roundHeader]⟩ :=
  .protocol roundsHeader rounds
    ⟨by simp [Within, ProtocolOp.Within, rounds, roundsHeader, roundHeader], by decide,
    by simp [Enclosed, Within, ProtocolOp.Within, rounds, roundHeader], rfl, rfl, rfl, rfl⟩ <|
  .protocol roundHeader round
    ⟨by simp [Within, ProtocolOp.Within, round, roundHeader], by decide, by simp [Enclosed, round], rfl, rfl, rfl, rfl⟩ .nil

/-- The record of a run of the rounds: per iteration, the record of the round, which is the
natural drawn. -/
example : roundsHeader.record =
    .cons (.key ⟨2⟩) (.many (.record (.cons (.key ⟨1⟩) (.val .nat) .nil))) .nil := rfl

/-- The role map of a list of distinct roles sends each callee role to the role at its
position, and back. -/
example : (RoleMap.ofList [2, 0] (by decide)).to 0 = 2 ∧ (RoleMap.ofList [2, 0] (by decide)).to 1 = 0 ∧
    (RoleMap.ofList [2, 0] (by decide)).back 2 = 0 := by decide

/-! ## An attempt, and a request to a service -/

/-- The first role's attempt: with its number it asks a service, and aborts unless the answer
is below the number; a bounded retry runs the body again. The rest gives the answer. -/
def attempt : Term (protocolDialect plain none) [] [nat [0]] :=
  .attempt ⟨1⟩ [0] ⟨0, rfl⟩
    (.op ⟨2⟩ (.given (.request ⟨9⟩) 0 [] [nat [0]] .nat rfl
      (fun a ha => by
        simp only [List.mem_singleton] at ha
        subst ha
        decide) (by decide)) (.cons .head .nil) <|
     .op ⟨3⟩ (.compute [0] (.owned .natLess) [nat [0], nat [0]] rfl
      (fun a ha r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl <;> exact hr)) (.cons .head (.cons (.tail .head) .nil)) <|
     .guard ⟨4⟩ [0] .head ⟨rfl, by decide, by decide⟩ .abort <|
     .ret (.cons (.tail .head) .nil)) <|
  .ret (.cons .head .nil)

/-- Its record has the service's answer; the number of the attempt has no field. -/
example : (shapeOf attempt).fields = .cons (.key ⟨2⟩) (.val .nat) .nil := rfl

/-! ## A loop written out as blocks, whose carried type changes -/

/-- The first iteration: the first role turns its natural into a truth value. -/
def firstStep : Term (protocolDialect plain none) [nat [0]] [⟨.bool, [0]⟩] :=
  .op ⟨1⟩ (.compute [0] (.owned .natLess) [nat [0], nat [0]] rfl
    (fun a ha r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl <;> exact hr)) (.cons .head (.cons .head .nil)) <|
  .ret (.cons .head .nil)

/-- The second iteration: the first role gives the truth value to the second. -/
def secondStep :
    Term (protocolDialect plain none) [⟨.bool, [0]⟩, nat [0]] [⟨.bool, [0, 1]⟩] :=
  .op ⟨2⟩ (.flow .message 0 [1] (by decide) (by decide)) (.cons .head .nil) <|
  .ret (.cons .head .nil)

/-- Two iterations of the loop `5`, written out: what the first gives, the second takes. -/
def stepped : Term (protocolDialect plain none) [nat [0]] [⟨.bool, [0, 1]⟩] :=
  .block ⟨5⟩ 0 firstStep <|
  .block ⟨5⟩ 1 secondStep <|
  .ret (.cons .head .nil)

example : Enclosed stepped := by simp [Enclosed, stepped, firstStep, secondStep]

example : Within [0, 1] stepped := by
  simp [Within, ProtocolOp.Within, stepped, firstStep, secondStep]

/-- Its record has a field per iteration, named by the loop and the number of the iteration:
the first has no event, the second the value given. -/
example : (shapeOf stepped).fields =
    .cons (.step ⟨5⟩ 0) (.record .nil)
      (.cons (.step ⟨5⟩ 1) (.record (.cons (.key ⟨2⟩) (.val .bool) .nil)) .nil) := rfl

/-- The second role has both blocks: it does nothing in the first and gets the value in the
second. -/
example : Term (roleDialect plain none 1) [nat [0]] [⟨.bool, [0, 1]⟩] := project 1 stepped

/-- The event of the second iteration happens under the frame of that iteration. -/
example : (stepped.denote (protocolSem plainModel noFns noProtocols) []
    (Env.ofList (.cons (3 : Nat) .nil))) =
    .call (.flow .message 0 [1] ⟨[.iteration ⟨5⟩ 1], ⟨2⟩⟩ .bool false) fun _ =>
      .done (.cons false .nil) := rfl

/-! ## A loop of a written number of iterations -/

/-- The first role repeats three times, collecting the iteration number: what the loop gives
is a sequence of exactly three naturals. -/
def counted : Term (protocolDialect plain none) [] [⟨.seq .nat (some 3), [0]⟩] :=
  .loop (carried := []) (each := [nat [0]]) ⟨1⟩ [0] (.fixed 3)
    (fun a ha r hr => by
      simp only [List.nil_append, List.mem_singleton] at ha
      subst ha
      exact hr)
    .nil (.ret (.cons .head .nil)) <|
  .ret (.cons .head .nil)

example : Enclosed counted := by simp [Enclosed, Within, counted]

/-- It gives the three iteration numbers. -/
example : counted.denote (protocolSem plainModel noFns noProtocols) [] (Env.ofList .nil) =
    .done (.cons [0, 1, 2] .nil) := rfl

/-- The second role, which does not take part, has nothing of the sequence. -/
example : ((project 1 counted).denote (roleSem plainModel 1 noFns noPrograms) []
    (restrict plainModel 1 (Env.ofList .nil))) =
    .done (.cons (nothing plainModel (r := 1) (a := ⟨.seq .nat (some 3), [0]⟩) (by decide))
      .nil) := rfl

/-! ## A result narrowed to fewer holders -/

/-- Both roles hold a natural; afterwards only the first does. Nobody acts. -/
def narrowed : Term (protocolDialect plain none) [nat [0, 1]] [nat [0]] :=
  .op ⟨1⟩ (.narrow [0] (by decide)) (.cons .head .nil) <|
  .ret (.cons .head .nil)

example : Enclosed narrowed ∧ Within [] narrowed := by
  simp [Enclosed, Within, ProtocolOp.Within, narrowed]

/-- The first role keeps the value; the second has nothing of it. -/
example : ((project 0 narrowed).denote (roleSem plainModel 0 noFns noPrograms) []
    (restrict plainModel 0 (Env.ofList (.cons (4 : Nat) .nil)))) =
    .done (.cons (hide plainModel 0 (nat [0]) (4 : Nat)) .nil) := rfl

example : ((project 1 narrowed).denote (roleSem plainModel 1 noFns noPrograms) []
    (restrict plainModel 1 (Env.ofList (.cons (4 : Nat) .nil)))) =
    .done (.cons (nothing plainModel (r := 1) (a := nat [0]) (by decide)) .nil) := rfl

/-! ## Owned operations, linear types, equality of types, forks -/

/-- A truth value as the second alternative of `either`. -/
example : ownedOp plainModel (.variant ⟨7⟩ (.cons .nat (.cons .bool .nil)) (.tail .head))
    (.cons true .nil) = .done (.cons (.inr (.inl true)) .nil) := rfl

/-- The length of a sequence of a written size. -/
example : ownedOp plainModel (.seqLength .nat (some 2) rfl) (.cons ([5, 6] : List Nat) .nil) =
    .done (.cons 2 .nil) := rfl

/-- A record marked linear is linear, and so is a sequence of it; a tuple of naturals is not. -/
example : Ty.isLinear plain (.seq (.record ⟨1⟩ true (.cons .nat .nil)) Option.none) = true ∧
    Ty.isLinear plain (.tuple (.cons .nat (.cons .bool .nil))) = false := ⟨rfl, rfl⟩

example : (Ty.record ⟨1⟩ true .nil : plain.Ty) ≠ .record ⟨1⟩ false .nil := by decide

example : (nat [0, 1]) ≠ nat [0] := by decide

/-! ## Who proves -/

/-- A derived scheme of an entry, with the kinds of its roles and the prover when it is
written, and nothing else declared. -/
def derivedScheme (entry : Key) (kinds : List RoleKind) (prover : Option Role) : Declaration where
  key := ⟨1⟩
  entry := entry
  kinds := kinds
  construction := .derived ⟨[]⟩
  prover := prover
  layout := Option.none
  retry := Option.none
  samples := Option.none
  context := []
  grinds := []
  commits := []
  pins := []

/-- In a round, the second role owns a draw that the first hears: the first proves. -/
example : proverAndVerifier roundHeader (derivedScheme ⟨20⟩ [.online, .online] Option.none) =
    some (0, 1) := by decide

/-- A written prover that is not the computed one is refused. -/
example : proverAndVerifier roundHeader (derivedScheme ⟨20⟩ [.online, .online] (some 1)) =
    Option.none := by decide

/-- The rounds apply the round: its draw is heard, at the site through the application. -/
example : roundsHeader.shape.heardCoins = [⟨[⟨2⟩], ⟨1⟩⟩] := by decide

/-! ## A deployed scheme, and the run of a role -/

/-- Nothing is known, and no loop has a bound. -/
def emptyAnnotation : Annotation := ⟨[]⟩

/-- The relay, deployed with no handlers; the third role is offline. -/
def relayDeployed : Deployed plain where
  admitted := ⟨⟨_, relayProgram, by decide⟩, emptyAnnotation, ⟨⟨[], [], [], [], []⟩, []⟩⟩
  declaration := derivedScheme ⟨10⟩ [.online, .online, .offline] Option.none
  entry := relayHeader
  callee := .head
  stack := fun _ => []

/-- The first role gives to the second, which is online: the first proves. -/
example : relayDeployed.roles = some (0, 1) := by decide

/-- The second role's run under no handlers starts by getting the value from the first, at
the occurrence of the first event. -/
example : (match relayDeployed.run plainModel 1 (hideAll plainModel 1 (.cons (5 : Nat) .nil)) .nil with
    | .call (.get _ giver at_ _) _ => some (giver, at_)
    | _ => Option.none) = some (0, ⟨[], ⟨1⟩⟩) := rfl

/-- Two runs of the attempt whose services answered differently fork at the answer. -/
example : (shapeOf attempt).fields.Fork plainModel (.key ⟨2⟩) ((3 : Nat), ()) ((4 : Nat), ()) := by
  simp [Fields.Fork, Fields.agreeBefore, Fields.differAt, attempt, shapeOf, ProtocolOp.shape,
    Shape.fields, EventClass.recorded, Fields.append]

end Zkc.Core.Shapes

#print axioms Zkc.Core.RoleMap.ofList_to
#print axioms Zkc.Core.RoleMap.ofList_back
