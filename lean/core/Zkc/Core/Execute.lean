module

public import Std.Data.HashMap
public import Zkc.Core.Concrete
public import Zkc.Core.Serialize
public import Zkc.Core.ProjectProgramMeaning
public import Zkc.Core.DecodingLimitRoles
public import Zkc.Core.Endpoints

public section

/-! Running processes: the executor.

- `runAlone` runs one process: a draw or a sample is answered by the next coin of its site,
  and a send, a receive or a read fails the run. It recurses on the process.
- `run` and `runAll` run any number of processes against each other, one effect at a time: a
  send puts a message in the mail of its site and a receive takes the oldest one; a draw
  announces its coin at its site, where it stays, and a receive at a site without a message in
  transit hears the first coin of that site that its process has not heard. Every receiver of a
  draw hears every coin of its site, in the order announced. The messages in transit and the
  coins announced are the mail and the board of the relation `ReturnTogether` of the endpoint
  statements (`Zkc.Core.Endpoints`), and each process has the relation's count of the coins it
  has heard: the run keeps no state of its own beside them. The run ends because every effect
  continues one process and a process has no infinite path (`oneContinues_wellFounded`); no
  fuel is given, and running out of it is not an outcome.
- The coins are a parameter (`Coins`): the `k`-th coin of a site at a type, when the source has
  one. `coinNumbers` derives numbers from a seed, the site and `k`, so the same seed gives a
  grouped run and a run of the roles the same coins; the vocabulary makes the value of a law of
  them (`Vocabulary.seededCoins`). A caller with its own mapping of coins to
  values gives its own source. A source gives a sampler of the endpoint statements
  (`Coins.sampler`).
- The order of a run: the first process, in an order, that can perform its first effect does
  so; a process that drew goes to the end of the order, so that the others hear its coin before
  it draws again, and any other goes on as far as it can.

Every effect that the executor performs is a step of the relation `ReturnTogether`, so a run of
two processes in which both return is a run of the relation, whatever its order
(`Zkc.Core.ExecuteRuns`): a process that hears a coin after a later one was announced at its
site hears the earlier one first, in the executor and in the relation.

A run under a limit runs the programs of roles whose pure rows are under the limit
(`limitedRoleEntry`). A row that reaches the limit becomes a process that waits at the site that
the executor reserved (`reservedDefinition`), and a run that is given that reservation ends such
a process with the limit (`Outcome.limit`): neither a return nor a stop of the program. A
process that waits at a site of the program for a message that no process sends, a value of a
type with no value included, has failed to end, and is not the limit.
-/

set_option autoImplicit false

namespace Zkc.Core.Execute

open Zkc.Source Zkc.Core.Concrete

/-! ## Running processes -/

/-- How a run ends. -/
inductive Outcome (α : Type) where
  | returned (value : α)
  | stopped (reason : PIR.Stop)
  /-- A reading of a value reached the limit of the run on the number of elements it builds:
  the program did not return, and it did not stop. -/
  | limit (elements : Nat)
  | failed (message : String)

instance {α : Type} : Inhabited (Outcome α) := ⟨.failed "no outcome"⟩

/-- The end of a run with its returned values seen through a function. -/
@[expose] def Outcome.map {α β : Type} (view : α → β) : Outcome α → Outcome β
  | .returned value => .returned (view value)
  | .stopped reason => .stopped reason
  | .limit elements => .limit elements
  | .failed message => .failed message

def Outcome.describe {α : Type} (show_ : α → String) : Outcome α → String
  | .returned value => s!"returned {show_ value}"
  | .stopped reason => s!"stopped {repr reason}"
  | .limit elements => s!"reached the limit of {elements} elements"
  | .failed message => s!"failed: {message}"

/-- The answers of a seed so far, for a caller that steps processes itself: how often each
site was asked. The runs of this module count per site as the relations of the endpoint
statements do (`Zkc.Core.Asked`). -/
abbrev Asked := Std.HashMap (List Nat × Nat × Nat) Nat

/-- The messages in transit as data, by site, for a caller that steps processes itself. -/
abbrev Mail := Std.HashMap (List Nat × Nat × Nat) (List Datum)

/-- A source of coins: the `k`-th coin of a site at a type, when it has one. A draw or a
sample at a site takes the next coin of the site at the output type of its law; a run in which
the source has no coin for one fails there. A caller that maps coins to values in its own way
gives its own source. -/
abbrev Coins (model : Model) : Type := Site → Nat → (type : Ty) → Option (model.Value type)

/-- The sampler that a source of coins gives: its coins, and where it has none the value of the
type that every model has. A run that ends took only coins that the source has, so it is a run
under this sampler. -/
@[expose] def Coins.sampler {model : Model} (coins : Coins model) : Sampler model where
  coin site count type populated :=
    (coins site count type).getD (Ty.inhabitant (fun row => model.literal row []) type populated)

/-- The numbers of the `k`-th coin of a site under a seed, each of 512 bits: a value of a law
is made of as many of them as the law reads. The first is a digest of the seed and the place;
each later one adds a mark and its position. -/
def coinNumbers (seed : List Nat) (site : Site) (occurrence : Nat) (index : Nat) : Nat :=
  let digest := Concrete.hash (seed ++ bigEndian 8 site.definition ++ bigEndian 8 site.number ++
    bigEndian 8 occurrence ++ site.path.flatMap (bigEndian 8) ++
    (if index == 0 then [] else 255 :: bigEndian 8 index))
  numberOf (digest ++ Concrete.hash (digest ++ [0]))

/-- The first number of the `k`-th coin of a site under a seed, as an element of the scalar
field. -/
def coin (seed : List Nat) (site : Site) (occurrence : Nat) : Datum :=
  field (coinNumbers seed site occurrence 0)

def nextCoin (seed : List Nat) (site : Site) (asked : Asked) : Datum × Asked :=
  let occurrence := asked.getD (site.path, site.definition, site.number) 0
  (coin seed site occurrence, asked.insert (site.path, site.definition, site.number) (occurrence + 1))

section Run

variable (model : Model) (carrier : model.Carrier = Carrier)

/-- A datum as a value of the model, whose carrier is the concrete one, when it is a value
of the type. -/
def valueOf (type : Ty) (datum : Datum) : Option (model.Value type) :=
  cast (by rw [Model.Value, carrier]) (ofDatum type datum)

/-- A reply or a message that is not a value of its type ends a run. -/
def notValue (site : Site) : String :=
  s!"the value at site {site.definition}.{site.number} is not a value of its type"

def datumOf (type : Ty) (value : model.Value type) : Datum :=
  toDatum type (cast (by rw [Model.Value, carrier]) value)

end Run

section Alone

variable (model : Model)

/-- The limit that a process has reached, when the run reserved a site for its mark. -/
@[expose] def reached {α : Type} (reserved : Option Nat) (process : PIR.Process (Effects model) α) :
    Option Nat :=
  reserved.bind fun reserved => limitOf? model reserved process

/-- One process: a draw or a sample is answered by the next coin of its site, and a send, a
receive or a read fails the run. A process that waits at the site reserved for the mark of the
limit ends with the limit. The recursion is on the process. -/
@[expose] def runAlone {α : Type} (coins : Coins model) (process : PIR.Process (Effects model) α)
    (asked : Zkc.Core.Asked := fun _ => 0) (reserved : Option Nat := none) : Outcome α :=
  match reached model reserved process with
  | some elements => .limit elements
  | none =>
    match process with
    | .done value => .returned value
    | .halt reason => .stopped reason
    | .call (.draw site law _) next =>
        match coins site (asked site) law.output with
        | some reply => runAlone coins (next reply) (asked.next site) reserved
        | none => .failed (notValue site)
    | .call (.sample site law _) next =>
        match coins site (asked site) law.output with
        | some reply => runAlone coins (next reply) (asked.next site) reserved
        | none => .failed (notValue site)
    | .call (.send site ..) _ =>
        .failed s!"a send at site {site.definition}.{site.number} in a run of one process"
    | .call (.receive site _) _ =>
        .failed s!"a receive at site {site.definition}.{site.number} in a run of one process"
    | .call (.read site ..) _ => .failed s!"a read at site {site.definition}.{site.number}"

end Alone

/-! ## Processes against each other -/

section Several

variable {I : PIR.Signature} {A : Type}

/-- A process after one reply to its first effect. -/
inductive Continues : PIR.Process I A → PIR.Process I A → Prop
  | reply (op : I.Op) (next : I.Reply op → PIR.Process I A) (answer : I.Reply op) :
      Continues (next answer) (.call op next)

theorem Continues.of_call {op : I.Op} {next : I.Reply op → PIR.Process I A}
    {later : PIR.Process I A} (answer : I.Reply op) (same : later = next answer) :
    Continues later (.call op next) :=
  same ▸ .reply op next answer

theorem continues_wellFounded : WellFounded (@Continues I A) :=
  ⟨fun process => by
    induction process with
    | done value => exact ⟨_, fun _ step => nomatch step⟩
    | halt reason => exact ⟨_, fun _ step => nomatch step⟩
    | call op next hypothesis =>
      exact ⟨_, fun _ step => by
        cases step with
        | reply _ _ answer => exact hypothesis answer⟩⟩

/-- Processes of which one has continued and the others are as they were. -/
inductive OneContinues : List (PIR.Process I A) → List (PIR.Process I A) → Prop
  | head {later process : PIR.Process I A} {rest : List (PIR.Process I A)} :
      Continues later process → OneContinues (later :: rest) (process :: rest)
  | tail {process : PIR.Process I A} {later rest : List (PIR.Process I A)} :
      OneContinues later rest → OneContinues (process :: later) (process :: rest)

theorem oneContinues_cons {process : PIR.Process I A} {rest : List (PIR.Process I A)}
    (first : Acc Continues process) (others : Acc OneContinues rest) :
    Acc OneContinues (process :: rest) := by
  induction first generalizing rest with
  | intro process _ onFirst =>
    induction others with
    | intro rest accessible onOthers =>
      refine ⟨_, fun _ step => ?_⟩
      cases step with
      | head continued => exact onFirst _ continued ⟨rest, accessible⟩
      | tail continued => exact onOthers _ continued

/-- Every run of processes against each other ends: each effect continues one process, and a
process has no infinite path. -/
theorem oneContinues_wellFounded : WellFounded (@OneContinues I A) :=
  ⟨fun processes => by
    induction processes with
    | nil => exact ⟨_, fun _ step => nomatch step⟩
    | cons process rest hypothesis =>
      exact oneContinues_cons (continues_wellFounded.apply process) hypothesis⟩

theorem oneContinues_set : ∀ (processes : List (PIR.Process I A)) (index : Nat)
    {process later : PIR.Process I A}, processes[index]? = some process →
      Continues later process → OneContinues (processes.set index later) processes
  | [], _, _, _, found, _ => by simp at found
  | first :: rest, 0, _, _, found, continued => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at found
    subst found
    exact .head continued
  | first :: rest, index + 1, _, _, found, continued => by
    simp only [List.getElem?_cons_succ] at found
    exact .tail (oneContinues_set rest index found continued)

end Several

section Together

variable (model : Model)

/-- One process of a run against others, with the number of coins it has heard at each site. -/
structure Role (α : Type) where
  process : PIR.Process (Effects model) α
  heard : Heard

/-- What the processes of a run share: the messages in transit, every coin announced at every
site in the order announced, and the counters of the source of coins. -/
structure Shared where
  mail : Zkc.Core.Mail model
  board : Zkc.Core.Board model
  asked : Zkc.Core.Asked

/-- Nothing in transit, no coin announced, no site asked. -/
@[expose] def Shared.start : Shared model :=
  { mail := Mail.empty, board := Board.empty, asked := fun _ => 0 }

/-- What a role does next. -/
inductive Moved (α : Type) where
  /-- It performed its first effect; with whether the effect was a draw. -/
  | to (role : Role model α) (shared : Shared model) (drew : Bool)
  /-- It has ended, or its first effect cannot be performed now. -/
  | stays

/-- The oldest message of a site, as a value of a type, and the messages after it. -/
@[expose] def message? (shared : Shared model) (site : Site) (type : Ty) :
    Option (model.Value type × List ((type : Ty) × model.Value type)) :=
  match shared.mail site with
  | ⟨sent, value⟩ :: rest => if same : sent = type then some (same ▸ value, rest) else none
  | [] => none

/-- The coin of a site that a role which has heard `count` of them hears next, as a value of a
type: the coin of the board at that count. -/
@[expose] def coin? (shared : Shared model) (site : Site) (count : Nat) (type : Ty) :
    Option (model.Value type) :=
  match (shared.board site)[count]? with
  | none => none
  | some ⟨announced, coin⟩ => if same : announced = type then some (same ▸ coin) else none

/-- The first effect of a role, performed when it can be.

A send puts its value in the mail of its site. A receive takes the oldest message of its site;
when no message is in transit there, it hears the first coin announced at its site that the
role has not heard. A draw is answered by the source of coins and announces its coin at its
site, where it stays; a sample is answered and announces nothing. So every receiver of a draw
hears every coin of its site, in the order announced.

A message or a coin of another type than the receive asks for, a draw or a sample without a
coin, and a read are not performed. -/
@[expose] def move {α : Type} (coins : Coins model) (role : Role model α) (shared : Shared model) :
    Moved model α :=
  match role.process with
  | .done _ => .stays
  | .halt _ => .stays
  | .call (.send site type value) next =>
      .to { role with process := next PUnit.unit }
        { shared with mail := shared.mail.put site type value } false
  | .call (.receive site type) next =>
      match message? model shared site type with
      | some (value, rest) =>
          .to { role with process := next value }
            { shared with mail := shared.mail.set site rest } false
      | none =>
        match shared.mail site with
        | _ :: _ => .stays
        | [] =>
          match coin? model shared site (role.heard site) type with
          | some value =>
              .to { process := next value, heard := role.heard.next site } shared false
          | none => .stays
  | .call (.draw site law _) next =>
      match coins site (shared.asked site) law.output with
      | some reply =>
          .to { role with process := next reply }
            { shared with
              board := shared.board.announce site law.output reply
              asked := shared.asked.next site } true
      | none => .stays
  | .call (.sample site law _) next =>
      match coins site (shared.asked site) law.output with
      | some reply =>
          .to { role with process := next reply } { shared with asked := shared.asked.next site }
            false
      | none => .stays
  | .call (.read ..) _ => .stays

/-- A role that moves continues its process. -/
theorem move_continues {α : Type} {coins : Coins model} {role moved : Role model α}
    {shared after : Shared model} {drew : Bool}
    (performed : move model coins role shared = .to moved after drew) :
    Continues moved.process role.process := by
  unfold move at performed
  split at performed
  · cases performed
  · cases performed
  · rename_i equation
    cases performed
    rw [equation]
    exact Continues.of_call _ rfl
  · rename_i equation
    rw [equation]
    repeat' split at performed
    all_goals first | (cases performed; exact Continues.of_call _ rfl) | cases performed
  · rename_i equation
    rw [equation]
    split at performed
    · cases performed
      exact Continues.of_call _ rfl
    · cases performed
  · rename_i equation
    rw [equation]
    split at performed
    · cases performed
      exact Continues.of_call _ rfl
    · cases performed
  · cases performed

/-- The processes of a run: its roles, what they share, and the order in which the run looks
for the next role to move. -/
structure Run (α : Type) where
  roles : List (Role model α)
  shared : Shared model
  order : List Nat

/-- The first role, in an order, that can perform its first effect now, with what it does. -/
@[expose] def firstMove {α : Type} (coins : Coins model) (roles : List (Role model α))
    (shared : Shared model) : List Nat → Option (Nat × Role model α × Shared model × Bool)
  | [] => none
  | index :: later =>
    match roles[index]? with
    | none => firstMove coins roles shared later
    | some role =>
      match move model coins role shared with
      | .to moved after drew => some (index, moved, after, drew)
      | .stays => firstMove coins roles shared later

/-- What `firstMove` finds is a role of the run and its move. -/
theorem firstMove_spec {α : Type} {coins : Coins model} {roles : List (Role model α)}
    {shared after : Shared model} {moved : Role model α} {index : Nat} {drew : Bool} :
    ∀ (order : List Nat), firstMove model coins roles shared order = some (index, moved, after, drew) →
      ∃ role, roles[index]? = some role ∧ move model coins role shared = .to moved after drew
  | [], found => by simp [firstMove] at found
  | candidate :: later, found => by
    simp only [firstMove] at found
    cases at_ : roles[candidate]? with
    | none =>
      simp only [at_] at found
      exact firstMove_spec later found
    | some role =>
      simp only [at_] at found
      cases performed : move model coins role shared with
      | stays =>
        simp only [performed] at found
        exact firstMove_spec later found
      | to moved' after' drew' =>
        simp only [performed, Option.some.injEq, Prod.mk.injEq] at found
        obtain ⟨rfl, rfl, rfl, rfl⟩ := found
        exact ⟨role, at_, performed⟩

/-- One effect of a run: the first role in its order that can move performs its first effect.
A role that drew goes to the end of the order, so that the others hear its coin before it
draws again; any other role keeps its place and goes on as far as it can. -/
@[expose] def Run.next? {α : Type} (coins : Coins model) (run : Run model α) : Option (Run model α) :=
  match firstMove model coins run.roles run.shared run.order with
  | none => none
  | some (index, moved, after, drew) =>
      some { roles := run.roles.set index moved, shared := after
             order := if drew then run.order.erase index ++ [index] else run.order }

theorem Run.next?_spec {α : Type} {coins : Coins model} {run next : Run model α}
    (stepped : run.next? model coins = some next) :
    ∃ index role moved drew, run.roles[index]? = some role ∧
      move model coins role run.shared = .to moved next.shared drew ∧
        next.roles = run.roles.set index moved := by
  unfold Run.next? at stepped
  cases found : firstMove model coins run.roles run.shared run.order with
  | none => simp [found] at stepped
  | some result =>
    obtain ⟨index, moved, after, drew⟩ := result
    simp only [found, Option.some.injEq] at stepped
    subst stepped
    obtain ⟨role, at_, performed⟩ := firstMove_spec model run.order found
    exact ⟨index, role, moved, drew, at_, performed, rfl⟩

theorem Run.next?_continues {α : Type} {coins : Coins model} {run next : Run model α}
    (stepped : run.next? model coins = some next) :
    OneContinues (next.roles.map (·.process)) (run.roles.map (·.process)) := by
  obtain ⟨index, role, moved, drew, at_, performed, roles⟩ := Run.next?_spec model stepped
  rw [roles, List.map_set]
  exact oneContinues_set _ index (by simp [at_]) (move_continues model performed)

instance {α : Type} : WellFoundedRelation (List (PIR.Process (Effects model) α)) :=
  ⟨OneContinues, oneContinues_wellFounded⟩

/-- A run to its end: effects are performed one after another until no role can move. Every
process has then returned, stopped, or waits for what the run does not give. The recursion ends
because each effect continues one process. -/
def Run.finish {α : Type} (coins : Coins model) (run : Run model α) : Run model α :=
  match _stepped : run.next? model coins with
  | some next => Run.finish coins next
  | none => run
termination_by run.roles.map (·.process)
decreasing_by exact Run.next?_continues model ‹_›

theorem Run.finish_step {α : Type} {coins : Coins model} {run next : Run model α}
    (stepped : run.next? model coins = some next) :
    run.finish model coins = next.finish model coins := by
  rw [Run.finish]
  split
  · rename_i found equation
    rw [stepped] at equation
    cases equation
    rfl
  · rename_i equation
    rw [stepped] at equation
    cases equation

theorem Run.finish_end {α : Type} {coins : Coins model} {run : Run model α}
    (stopped : run.next? model coins = none) : run.finish model coins = run := by
  rw [Run.finish]
  split
  · rename_i found equation
    rw [stopped] at equation
    cases equation
  · rfl

/-- The run of processes against each other, from what they share at the start: each with no
coin heard, in the order given. -/
@[expose] def run {α : Type} (coins : Coins model) (processes : List (PIR.Process (Effects model) α))
    (shared : Shared model := Shared.start model) : Run model α :=
  Run.finish model coins
    { roles := processes.map fun process => { process, heard := Heard.start }, shared
      order := List.range processes.length }

/-- How a process that no longer moves has ended. A process that waits at the site reserved
for the mark of the limit ends with the limit; one that waits at a site of the program has
failed: for a message that is never sent, or on a message, a coin or a reply that is not a
value of the type it asks for. -/
@[expose] def ended {α : Type} (reserved : Option Nat) (shared : Shared model) (role : Role model α) :
    Outcome α :=
  match reached model reserved role.process with
  | some elements => .limit elements
  | none =>
    match role.process with
    | .done value => .returned value
    | .halt reason => .stopped reason
    | .call (.receive site type) _ =>
        match shared.mail site, (shared.board site)[role.heard site]? with
        | ⟨sent, _⟩ :: _, _ =>
            if sent = type then .failed "waits for a message that is never sent"
            else .failed (notValue site)
        | [], some ⟨listed, _⟩ =>
            if listed = type then .failed "waits for a message that is never sent"
            else .failed (notValue site)
        | [], none => .failed "waits for a message that is never sent"
    | .call (.draw site ..) _ => .failed (notValue site)
    | .call (.sample site ..) _ => .failed (notValue site)
    | .call (.send site ..) _ => .failed (notValue site)
    | .call (.read site ..) _ => .failed s!"a read at site {site.definition}.{site.number}"

/-- Processes against each other until none performs an effect, and how each has ended:
returned, stopped, reached the limit when the run reserved a site for its mark, or failed. -/
@[expose] def runAll {α : Type} (coins : Coins model) (processes : Array (PIR.Process (Effects model) α))
    (shared : Shared model := Shared.start model) (reserved : Option Nat := none) :
    Array (Outcome α) :=
  let final := run model coins processes.toList shared
  (final.roles.map (ended model reserved final.shared)).toArray

end Together

/-! ## The entry of a program -/

section Entry

variable (model : Model) {typeTable : TypeTable} {operations : List OperationSignature}
  {functions : List FunctionHeader}

/-- The meaning of the newest protocol of a program. -/
def groupedEntry (functionTable : FunctionTable model functions) (identities : Identities) :
    {protocols : List ProtocolHeader} → Protocols typeTable operations functions protocols →
      Option ((header : ProtocolHeader) × header.Meaning model)
  | _, .nil => none
  | _, .snoc (protocols := earlierHeaders) (header := header) earlier definition _ =>
      some ⟨header, definition.meaning model functionTable
        (earlier.table model functionTable identities) (identities earlierHeaders.length)⟩

/-- The program of one role of the newest protocol of a program, applications kept as
calls, as a process of the role's inputs. -/
def roleEntry (functionTable : FunctionTable model functions) (identities : Identities)
    (role : Nat) :
    {protocols : List ProtocolHeader} → Protocols typeTable operations functions protocols →
      Except String ((header : ProtocolHeader) × RoleHeader.Meaning model (roleHeader role header))
  | _, .nil => .error "the program has no protocol"
  | _, .snoc (protocols := earlierHeaders) (header := header) earlier definition wellFormed =>
      match projectProtocols (.snoc earlier definition wellFormed) with
      | .error refusal => .error s!"refused by projection: {repr refusal}"
      | .ok projected =>
          match projected.callees.find (Var.here : Var (header :: earlierHeaders) header) role with
          | none => .error s!"role {role} has no program"
          | some program =>
              .ok ⟨header, (projected.programs.table model functionTable identities).get program⟩

/-- The program of one role of the newest protocol of a program with its pure rows under a
limit, applications kept as calls, as a process of the role's inputs. The functions given are
those of the program under the same rows (`Functions.limitedTable`). -/
def limitedRoleEntry (rows : LimitedRows model) (functionTable : FunctionTable model functions)
    (identities : Identities) (role : Nat) :
    {protocols : List ProtocolHeader} → Protocols typeTable operations functions protocols →
      Except String ((header : ProtocolHeader) × RoleHeader.Meaning model (roleHeader role header))
  | _, .nil => .error "the program has no protocol"
  | _, .snoc (protocols := earlierHeaders) (header := header) earlier definition wellFormed =>
      match projectProtocols (.snoc earlier definition wellFormed) with
      | .error refusal => .error s!"refused by projection: {repr refusal}"
      | .ok projected =>
          match projected.callees.find (Var.here : Var (header :: earlierHeaders) header) role with
          | none => .error s!"role {role} has no program"
          | some program =>
              .ok ⟨header,
                (projected.programs.limitedTable model rows functionTable identities).get program⟩

/-- The program of a role under a limit is its program of the meaning, cut where a row reaches
the limit, when the functions given are so: the two entries name the same header. -/
theorem limitedRoleEntry_within (rows : LimitedRows model)
    {limitedFunctions wholeFunctions : FunctionTable model functions}
    (functionsWithin : TableWithin limitedFunctions wholeFunctions) (identities : Identities)
    (role : Nat) :
    ∀ {protocols : List ProtocolHeader}
      (program : Protocols typeTable operations functions protocols)
      (result : (header : ProtocolHeader) × RoleHeader.Meaning model (roleHeader role header)),
      limitedRoleEntry model rows limitedFunctions identities role program = .ok result →
        ∃ whole, roleEntry model wholeFunctions identities role program = .ok ⟨result.1, whole⟩ ∧
          ∀ path arguments, Within (result.2 path arguments) (whole path arguments)
  | _, .nil, _, found => by simp [limitedRoleEntry] at found
  | _, .snoc earlier definition wellFormed, result, found => by
    simp only [limitedRoleEntry] at found
    simp only [roleEntry]
    cases projection : projectProtocols (.snoc earlier definition wellFormed) with
    | error refusal => simp [projection] at found
    | ok projected =>
      simp only [projection] at found ⊢
      split at found
      · cases found
      · rename_i program named
        simp only [Except.ok.injEq] at found
        subst found
        exact ⟨_, rfl, fun path arguments =>
          RolePrograms.limitedTable_within rows functionsWithin identities projected.programs
            program path arguments⟩

end Entry

/-- The values of the ports of a signature for the side of every role, from one datum per
port, when each datum is a value of its port's type. -/
def sideValues (model : Model) (carrier : model.Carrier = Carrier) :
    (ports : List Located) → List Datum → Option (Values (SideValue model fun _ => true) ports)
  | [], _ => some .nil
  | port :: rest, data =>
      match valueOf model carrier port.type (data.headD default),
          sideValues model carrier rest data.tail with
      | some value, some values => some (.cons value values)
      | _, _ => none

def sideData (model : Model) (carrier : model.Carrier = Carrier) :
    (ports : List Located) → Values (SideValue model fun _ => true) ports → List Datum
  | [], _ => []
  | port :: rest, values =>
      datumOf model carrier port.type (values.get .here) :: sideData model carrier rest values.tail

/-- The values of a role's ports, from one datum per port, when each datum is a value of
its port's type. -/
def roleValues (model : Model) (carrier : model.Carrier = Carrier) :
    (types : List Ty) → List Datum → Option (Values model.Value types)
  | [], _ => some .nil
  | type :: rest, data =>
      match valueOf model carrier type (data.headD default), roleValues model carrier rest data.tail with
      | some value, some values => some (.cons value values)
      | _, _ => none

def roleData (model : Model) (carrier : model.Carrier = Carrier) :
    (types : List Ty) → Values model.Value types → List Datum
  | [], _ => []
  | type :: rest, values =>
      datumOf model carrier type (values.get .here) :: roleData model carrier rest values.tail

/-- The data of the ports of a signature that a role holds, in order. -/
def ownData (role : Nat) (ports : List Located) (data : List Datum) : List Datum :=
  (ports.zip data).filterMap fun (port, datum) => if port.holder == role then some datum else none

end Zkc.Core.Execute
