import Zkc.Core.Functions

/-!
The shapes of protocols that differ, as typed terms.

Each is written directly in the typed program, with every proof that a term carries, and as
a definition of a program with what elaboration decides about its body. They are small on purpose: what they check is that the
typing of the protocol dialect admits each shape, with any number of roles, and, for some,
that the meaning computes.

A term is written by names: its inputs are `0, 1, 2, …` in order (`Ctx.positional`), each binding
names what it binds, and a variable is `var name`, whose proof that the context has the name at
its type is decided by evaluating the context. That a body binds each name once is decided too
(`Term.BoundOnce`). The other tests of the core write their terms with `var`.
-/

-- Lean 4.36's default Nat ordering witness reaches Classical.choice. These concrete
-- structural checks use the constructive witness from DecidableEq instead, locally.
local instance (priority := 2000) : LawfulBEq Nat := instLawfulBEq

namespace Zkc.Core.Shapes

/-- A variable of a typed term written by hand: `var name` is the name, at the type that the
context has there, with the proof that the context has it decided by evaluating the context
(`rfl`). The type is what the evaluation finds when the term around the variable does not say
it. -/
macro "var " name:term:max : term => `(⟨$name, rfl⟩)

/-- A vocabulary with no nominal type and no row: the core's own types and operations, and
one law, a natural. -/
def plain : Vocabulary where
  TypeKey := Empty
  RowKey := Empty
  LawKey := Unit
  row r := nomatch r
  law _ := some ⟨[], .nat⟩
  literal r _ := nomatch r
  decided r := nomatch r

/-- A model of the plain vocabulary: every natural is in the support of its law. -/
def plainModel : Model plain where
  Carrier key := nomatch key
  valid key _ := nomatch key
  literal key _ := nomatch key
  apply row _ _ _ := nomatch row
  inDomain row _ _ _ := nomatch row
  defined row _ _ _ := nomatch row
  total row _ _ _ _ := nomatch row
  decides row _ _ _ _ _ := nomatch row
  keeps row _ _ _ _ _ _ := nomatch row
  literals key _ _ := nomatch key
  support _ _ _ _ _ := True
  supported _ _ h _ _ _ _ := by
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
def relay : Term (protocolDialect plain none) (Ctx.positional [nat [0]]) [nat [0, 1, 2]] :=
  .op ⟨1⟩ (.flow .message 0 [1] (by decide) (by decide)) (.cons (var 0) .nil) (.cons 1 .nil) <|
  .op ⟨2⟩ (.flow .message 1 [2] (by decide) (by decide)) (.cons (var 1) .nil) (.cons 2 .nil) <|
  .ret (.cons (var 2) .nil)

def relayHeader : ProtocolHeader plain := ⟨⟨10⟩, 3, [nat [0]], [nat [0, 1, 2]], shapeOf relay⟩

def relayProgram : Defs plain ⟨[], [relayHeader]⟩ :=
  .protocol relayHeader (Names.counting 0 _) relay
    ⟨by simp [Within, ProtocolOp.Within, relay, relayHeader], by decide,
    by simp [Enclosed, relay], rfl, rfl, rfl, rfl, by unfold Term.BoundOnce; decide⟩ .nil

/-- The second role's program: it gets the value and gives it on. -/
example : Term (roleDialect plain none 1) (Ctx.positional [nat [0]]) [nat [0, 1, 2]] :=
  project 1 relay

/-! ## A choice over a variant that one role holds -/

/-- A natural or a truth value. -/
abbrev either : Ty Empty := .variant ⟨7⟩ (.cons .nat (.cons .bool .nil))

/-- The first role chooses on a variant that it alone holds; nobody else acts in the
regions, and nobody else learns which ran. Then it gives what the choice gave. -/
def choice : Term (protocolDialect plain none) (Ctx.positional [⟨either, [0]⟩]) [nat [0, 1]] :=
  .cases (mid := [nat [0]]) ⟨1⟩ [0] (var 0) ⟨_, _, rfl, rfl, by decide, by decide⟩
    (fun a ha r hr => by
      simp only [List.mem_singleton] at ha
      subst ha
      exact hr)
    (.cons (.cons 1 .nil) (.ret (.cons (var 1) .nil)) <|
      .cons (.cons 2 .nil)
        (.op ⟨2⟩ (.compute [0] (.literal .nat [0] rfl) [] rfl (fun _ ha => nomatch ha)) .nil
          (.cons 3 .nil) <|
          .ret (.cons (var 3) .nil)) <|
      .nil)
    (.cons 4 .nil) <|
  .op ⟨3⟩ (.flow .message 0 [1] (by decide) (by decide)) (.cons (var 4) .nil) (.cons 5 .nil) <|
  .ret (.cons (var 5) .nil)

example : Enclosed choice := by
  simp [Enclosed, EnclosedArms, WithinArms, Within, ProtocolOp.Within, choice]

/-- The other role passes over the choice and gets the value. -/
example : Term (roleDialect plain none 1) (Ctx.positional [⟨either, [0]⟩]) [nat [0, 1]] :=
  project 1 choice

/-! ## Rounds in a loop, each an application -/

/-- One round: the second role draws a natural that the first hears, and both add it to what
is carried. -/
def round : Term (protocolDialect plain none) (Ctx.positional [nat [0, 1]]) [nat [0, 1]] :=
  .op ⟨1⟩ (.given (.coin ()) 1 [0] [] .nat ⟨_, rfl, rfl, rfl⟩ (fun _ ha => nomatch ha)
    (by decide)) .nil (.cons 1 .nil) <|
  .op ⟨2⟩ (.compute [0, 1] (.owned .natAdd) [nat [0, 1], nat [0, 1]] rfl
    (fun a ha r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl <;> exact hr)) (.cons (var 1) (.cons (var 0) .nil))
    (.cons 2 .nil) <|
  .ret (.cons (var 2) .nil)

def roundHeader : ProtocolHeader plain := ⟨⟨20⟩, 2, [nat [0, 1]], [nat [0, 1]], shapeOf round⟩

abbrev withRound : Headers plain := ⟨[], [roundHeader]⟩

/-- As many rounds as a count that both hold says, each an application of the round with the
roles as they are. The role map is computed from the list of roles. -/
def rounds :
    Term (protocolDialect plain withRound) (Ctx.positional [nat [0, 1], nat [0, 1]]) [nat [0, 1]] :=
  .loop (carried := [nat [0, 1]]) (each := []) ⟨1⟩ [0, 1]
    (.value (var 0) ⟨rfl, by decide, by decide⟩)
    (fun a ha r hr => by
      simp only [List.append_nil, List.mem_singleton] at ha
      subst ha
      exact hr)
    (.cons (var 1) .nil)
    (.cons 2 (.cons 3 .nil))
    (.op (res := [nat [0, 1]]) ⟨2⟩ (.apply (hdr := roundHeader) .head [0, 1] (by decide) rfl
        [nat [0, 1]] ⟨⟨rfl, by decide⟩, trivial⟩)
      (.cons (var 3) .nil) (.cons 4 .nil) <|
      .ret (.cons (var 4) .nil))
    (.cons 5 .nil) <|
  .ret (.cons (var 5) .nil)

def roundsHeader : ProtocolHeader plain :=
  ⟨⟨21⟩, 2, [nat [0, 1], nat [0, 1]], [nat [0, 1]], shapeOf rounds⟩

def roundsProgram : Defs plain ⟨[], [roundsHeader, roundHeader]⟩ :=
  .protocol roundsHeader (Names.counting 0 _) rounds
    ⟨by simp [Within, ProtocolOp.Within, rounds, roundsHeader, roundHeader], by decide,
    by simp [Enclosed, Within, ProtocolOp.Within, rounds, roundHeader], rfl, rfl, rfl, rfl,
    by unfold Term.BoundOnce; decide⟩ <|
  .protocol roundHeader (Names.counting 0 _) round
    ⟨by simp [Within, ProtocolOp.Within, round, roundHeader], by decide, by simp [Enclosed, round],
    rfl, rfl, rfl, rfl, by unfold Term.BoundOnce; decide⟩ .nil

/-- The record of a run of the rounds: per iteration, the record of the round, which is the
natural drawn. -/
example : roundsHeader.record =
    .cons (.key ⟨2⟩) (.many (.record (.cons (.key ⟨1⟩) (.val .nat) .nil))) .nil := rfl

/-- The role map of a list of distinct roles sends each callee role to the role at its
position, and back. -/
example : (RoleMap.ofList [2, 0] (by decide)).to 0 = 2 ∧ (RoleMap.ofList [2, 0] (by decide)).to 1 = 0 ∧
    (RoleMap.ofList [2, 0] (by decide)).back 2 = 0 := by decide +kernel

/-! ## An attempt, and a request to a service -/

/-- The first role's attempt: with its number it asks a service, and aborts unless the answer
is below the number; a bounded retry runs the body again. The rest gives the answer. -/
def attempt : Term (protocolDialect plain none) (Ctx.positional []) [nat [0]] :=
  .attempt ⟨1⟩ [0] ⟨0, rfl⟩ (.cons 0 .nil)
    (.op ⟨2⟩ (.given (.request ⟨9⟩) 0 [] [nat [0]] .nat rfl
      (fun a ha => by
        simp only [List.mem_singleton] at ha
        subst ha
        decide) (by decide)) (.cons (var 0) .nil) (.cons 1 .nil) <|
     .op ⟨3⟩ (.compute [0] (.owned .natLess) [nat [0], nat [0]] rfl
      (fun a ha r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl <;> exact hr)) (.cons (var 1) (.cons (var 0) .nil))
      (.cons 2 .nil) <|
     .guard ⟨4⟩ [0] (var 2) ⟨rfl, by decide, by decide⟩ .abort <|
     .ret (.cons (var 1) .nil))
    (.cons 3 .nil) <|
  .ret (.cons (var 3) .nil)

/-- Its record has the service's answer; the number of the attempt has no field. -/
example : (shapeOf attempt).fields = .cons (.key ⟨2⟩) (.val .nat) .nil := rfl

/-! ## A loop written out as blocks, whose carried type changes -/

/-- The first iteration: the first role turns its natural into a truth value. -/
def firstStep : Term (protocolDialect plain none) (Ctx.positional [nat [0]]) [⟨.bool, [0]⟩] :=
  .op ⟨1⟩ (.compute [0] (.owned .natLess) [nat [0], nat [0]] rfl
    (fun a ha r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl <;> exact hr)) (.cons (var 0) (.cons (var 0) .nil))
    (.cons 1 .nil) <|
  .ret (.cons (var 1) .nil)

/-- The second iteration: the first role gives the truth value, which the first block gave as
`2`, to the second. -/
def secondStep :
    Term (protocolDialect plain none)
      ((Ctx.positional [nat [0]]).extend (.cons 2 .nil : Names [(⟨.bool, [0]⟩ : LTy plain)]))
      [⟨.bool, [0, 1]⟩] :=
  .op ⟨2⟩ (.flow .message 0 [1] (by decide) (by decide)) (.cons (var 2) .nil) (.cons 3 .nil) <|
  .ret (.cons (var 3) .nil)

/-- Two iterations of the loop `5`, written out: what the first gives, the second takes. -/
def stepped : Term (protocolDialect plain none) (Ctx.positional [nat [0]]) [⟨.bool, [0, 1]⟩] :=
  .block ⟨5⟩ 0 firstStep (.cons 2 .nil) <|
  .block ⟨5⟩ 1 secondStep (.cons 4 .nil) <|
  .ret (.cons (var 4) .nil)

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
example : Term (roleDialect plain none 1) (Ctx.positional [nat [0]]) [⟨.bool, [0, 1]⟩] :=
  project 1 stepped

/-- The event of the second iteration happens under the frame of that iteration. -/
example : (stepped.denote (protocolSem plainModel noFns noProtocols) []
    (Env.positional (.cons (3 : Nat) .nil))) =
    .call (.flow .message 0 [1] ⟨[.iteration ⟨5⟩ 1], ⟨2⟩⟩ .bool false) fun _ =>
      .done (.cons false .nil) := rfl

/-! ## A loop of a written number of iterations -/

/-- The first role repeats three times, collecting the iteration number: what the loop gives
is a sequence of exactly three naturals. -/
def counted : Term (protocolDialect plain none) (Ctx.positional []) [⟨.seq .nat (some 3), [0]⟩] :=
  .loop (carried := []) (each := [nat [0]]) ⟨1⟩ [0] (.fixed 3)
    (fun a ha r hr => by
      simp only [List.nil_append, List.mem_singleton] at ha
      subst ha
      exact hr)
    .nil (.cons 0 .nil) (.ret (.cons (var 0) .nil)) (.cons 1 .nil) <|
  .ret (.cons (var 1) .nil)

example : Enclosed counted := by simp [Enclosed, Within, counted]

/-- It gives the three iteration numbers. -/
example : counted.denote (protocolSem plainModel noFns noProtocols) [] (Env.positional .nil) =
    .done (.cons [0, 1, 2] .nil) := rfl

/-- The second role, which does not take part, has nothing of the sequence. -/
example : ((project 1 counted).denote (roleSem plainModel 1 noFns noPrograms) []
    (restrict plainModel 1 (Env.positional .nil))) =
    .done (.cons (nothing plainModel (r := 1) (a := ⟨.seq .nat (some 3), [0]⟩) (by decide))
      .nil) := rfl

/-! ## A result narrowed to fewer holders -/

/-- Both roles hold a natural; afterwards only the first does. Nobody acts. -/
def narrowed : Term (protocolDialect plain none) (Ctx.positional [nat [0, 1]]) [nat [0]] :=
  .op ⟨1⟩ (.narrow [0] (by decide)) (.cons (var 0) .nil) (.cons 1 .nil) <|
  .ret (.cons (var 1) .nil)

example : Enclosed narrowed ∧ Within [] narrowed := by
  simp [Enclosed, Within, ProtocolOp.Within, narrowed]

/-- The first role keeps the value; the second has nothing of it. -/
example : ((project 0 narrowed).denote (roleSem plainModel 0 noFns noPrograms) []
    (restrict plainModel 0 (Env.positional (.cons (4 : Nat) .nil)))) =
    .done (.cons (hide plainModel 0 (nat [0]) (4 : Nat)) .nil) := rfl

example : ((project 1 narrowed).denote (roleSem plainModel 1 noFns noPrograms) []
    (restrict plainModel 1 (Env.positional (.cons (4 : Nat) .nil)))) =
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

example : (Ty.record ⟨1⟩ true .nil : plain.Ty) ≠ .record ⟨1⟩ false .nil := by decide +kernel

example : (nat [0, 1]) ≠ nat [0] := by decide +kernel

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
    some (0, 1) := by decide +kernel

/-- A written prover that is not the computed one is refused. -/
example : proverAndVerifier roundHeader (derivedScheme ⟨20⟩ [.online, .online] (some 1)) =
    Option.none := by decide +kernel

/-- The rounds apply the round: its draw is heard, at the site through the application. -/
example : roundsHeader.shape.heardCoins = [⟨[⟨2⟩], ⟨1⟩⟩] := by decide +kernel

/-! ## A deployed scheme, and the run of a role -/

/-- Nothing is known, and no loop has a bound. -/
def emptyAnnotation : Annotation := ⟨[]⟩

/-- A process satisfies on every path what holds of every value that it returns, and stops
anyhow. -/
theorem every_of_all {S : Sig} {H A : Type} (permitted : ∀ op, S.Reply op → Prop) {P : A → Prop}
    (all : ∀ a, P a) : ∀ p : Process S H A, p.Every permitted P (fun _ => True)
  | .done a => all a
  | .halt _ => trivial
  | .call _ k => fun reply _ => every_of_all permitted all (k reply)

section
variable {D : Dialect} (sem : Semantics D) (permitted : ∀ op, sem.S.Reply op → Prop)
  {B : List (Key × Nat) → Key → Nat → Prop}

mutual
  /-- Every loop that a run of a term reaches satisfies what every count does. -/
  theorem Term.everyLoop_of_all (all : ∀ blocks key count, B blocks key count) :
      ∀ {Γ : Ctx D.Ty} {outs : List D.Ty} (t : Term D Γ outs) (path : List Frame)
        (blocks : List (Key × Nat)) (env : Env sem.Val Γ),
        t.EveryLoop sem permitted B path blocks env
    | _, _, .ret _, _, _, _ => trivial
    | _, _, .op _ _ _ _ rest, path, blocks, _ =>
        every_of_all permitted (fun _ => Term.everyLoop_of_all all rest path blocks _) _
    | _, _, .guard _ _ _ _ _ rest, path, blocks, env =>
        fun _ => Term.everyLoop_of_all all rest path blocks env
    | _, _, .choose _ _ c ok _ onTrue onFalse _ rest, path, blocks, env => by
        refine ⟨?_, every_of_all permitted
          (fun _ => Term.everyLoop_of_all all rest path blocks _) _⟩
        cases sem.holds ok (env.get c)
        · exact Term.everyLoop_of_all all onFalse path blocks env
        · exact Term.everyLoop_of_all all onTrue path blocks env
    | _, _, .cases _ _ _ _ _ arms _ rest, path, blocks, env =>
        ⟨Arms.everyLoop_of_all all arms path blocks env _,
          every_of_all permitted (fun _ => Term.everyLoop_of_all all rest path blocks _) _⟩
    | _, _, .loop key _ _ _ _ _ body _ rest, path, blocks, _ =>
        ⟨all _ _ _, fun i _ => every_of_all permitted
            (fun _ => Term.everyLoop_of_all all body (path ++ [.iteration key i]) blocks _) _,
          every_of_all permitted (fun _ => Term.everyLoop_of_all all rest path blocks _) _⟩
    | _, _, .block key number body _ rest, path, blocks, env =>
        ⟨Term.everyLoop_of_all all body (path ++ [.iteration key number])
            (blocks ++ [(key, number)]) env,
          every_of_all permitted (fun _ => Term.everyLoop_of_all all rest path blocks _) _⟩
    | _, _, .attempt _ _ _ _ body _ rest, path, blocks, _ =>
        every_of_all permitted (fun _ => ⟨Term.everyLoop_of_all all body path blocks _,
          every_of_all permitted (fun _ => every_of_all permitted
            (fun _ => Term.everyLoop_of_all all rest path blocks _) _) _⟩) _
  /-- Every loop that a run of the arm of an alternative reaches satisfies what every count
  does. -/
  theorem Arms.everyLoop_of_all (all : ∀ blocks key count, B blocks key count) :
      ∀ {Γ : Ctx D.Ty} {mid payloads : List D.Ty} (arms : Arms D Γ mid payloads)
        (path : List Frame) (blocks : List (Key × Nat)) (env : Env sem.Val Γ)
        (pick : Pick sem.Val payloads), Arms.EveryLoop sem permitted B arms path blocks env pick
    | _, _, _, .nil, _, _, _, pick => nomatch pick
    | _, _, _, .cons _ arm _, path, blocks, _, .here _ =>
        Term.everyLoop_of_all all arm path blocks _
    | _, _, _, .cons _ _ rest, path, blocks, env, .there pick =>
        Arms.everyLoop_of_all all rest path blocks env pick
end

end

/-- The relay as an admitted program, built by hand since admission refuses a protocol: no
function, and no loop bounded, which every run respects. -/
abbrev relayAdmitted : Admitted plain where
  program := ⟨_, relayProgram, by decide⟩
  annotation := emptyAnnotation
  association := ⟨⟨[], [], [], [], []⟩, []⟩
  assured M := by
    refine ⟨fun _ f => (nomatch f), fun _ f => (nomatch f), ?_⟩
    dsimp only [Respects, Defs.Respects, Defs.FunctionsRespect, Defs.ProtocolsRespect,
      relayProgram]
    refine ⟨trivial, fun r path ins _ => ?_, trivial⟩
    apply Term.everyLoop_of_all
    intro blocks key count bound found
    simp [Annotation.boundAt, emptyAnnotation] at found

/-- The relay, deployed with no handlers; the third role is offline. -/
def relayDeployed : Deployed plain where
  admitted := relayAdmitted
  declaration := derivedScheme ⟨10⟩ [.online, .online, .offline] Option.none
  found := by decide +kernel
  stack := fun _ => []

/-- The entry of the deployment is the relay, found by the key that the declaration names. -/
example : relayDeployed.entry = relayHeader := rfl

/-- The first role gives to the second, which is online: the first proves. -/
example : relayDeployed.roles = some (0, 1) := by decide +kernel

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
