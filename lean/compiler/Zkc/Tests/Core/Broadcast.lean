import Zkc.Tests.Core.Samplers
import Zkc.Core.EndpointsLegal

/-! A draw is a broadcast, in order: checks of the relation of two processes run against
each other, and of the endpoint lemma over it.

- **A hearer hears every coin of a site once, in the order announced.** An owner that draws
  twice at one site and a hearer that receives twice there, for every model, sampler, site
  and law: the two return together with the hearer holding the first coin and then the
  second (`hearer_in_order`), and they return together with nothing else
  (`hearer_only_in_order`). With a board that held the coin last announced, the hearer could
  hold the second coin twice.
- **A hearer that is behind hears a stale coin.** From a board with a coin at the site that
  the hearer has not heard, the hearer of a draw holds that coin, not the coin of the draw
  (`behind_hears_stale`). The restriction law therefore starts from boards and counts at
  which each part has heard every coin of the sites where it hears (`Listeners.HeardAll`),
  which holds at the start of a run and fails at that board.
- **The conditions introduced with the relation** each hold somewhere and fail somewhere:
  `Listeners.HeardAll`, `Side.AtMostOne`, `hearsOnce`, `Hears`, `Listeners.ReadBelow` and the
  listeners of a protocol (`Protocols.listens`). The condition that the functions of a
  program perform no effect, which the restriction law now takes, holds of the functions of
  a package and fails of a function that draws.
- **A draw in a loop.** A package of a prover and a verifier with the law of `bool`: in each
  of two iterations the verifier draws a coin at one site and the prover hears it, and each
  collects its coins. For every model and every sampler the grouped run returns with the
  prover holding the verifier's two coins, in order, so by the endpoint lemma the programs
  of the two roles, run against each other, return together those collections
  (`looped_endpoints`): the prover hears two coins at one site. The listeners of the
  protocol say that the prover hears at the site of the draw and that the verifier does not;
  listeners that say that nobody hears are not those of the protocol.
-/

set_option autoImplicit false

open Zkc.Source Zkc.Core

namespace Broadcast

/-! ## Two coins at one site -/

section Pair

variable {model : Model} (sampler : Sampler model) (site : Site) (law : SamplingRow)
  (inputs : Values model.Value law.inputs)

/-- An owner that draws twice at one site and returns the two coins. -/
def drawsTwice :
    PIR.Process (Effects model) (model.Value law.output × model.Value law.output) :=
  .call (.draw site law inputs) fun first =>
    .call (.draw site law inputs) fun second => .done (first, second)

/-- A hearer that receives twice at the site and returns what it heard. -/
def hearsTwice : PIR.Process (Effects model) (model.Value law.output × model.Value law.output) :=
  .call (.receive site law.output) fun first =>
    .call (.receive site law.output) fun second => .done (first, second)

/-- The first coin of the owner, from given counters. -/
abbrev firstCoin (asked : Asked) : model.Value law.output := sampler.answer site (asked site) law

/-- The second coin of the owner, from given counters. -/
abbrev secondCoin (asked : Asked) : model.Value law.output :=
  sampler.answer site ((asked.next site) site) law

/-- The owner and the hearer return together, the hearer with the first coin and then the
second. -/
theorem hearer_in_order (asked : Asked) :
    ReturnTogether sampler (drawsTwice site law inputs) (hearsTwice (model := model) site law)
      Mail.empty Board.empty Heard.start Heard.start asked
      (firstCoin sampler site law asked, secondCoin sampler site law asked)
      (firstCoin sampler site law asked, secondCoin sampler site law asked) := by
  refine .drawLeft (.drawLeft ?_)
  refine .hearRight rfl ?_ (.hearRight rfl ?_ (.done _ _ _ _ _ _ _))
  · simp [Board.announce, Board.empty]
  · simp [Board.announce, Board.empty, Heard.next]

/-- The owner and the hearer return together with nothing else: the hearer holds the first
coin and then the second, whatever the order of the steps. In particular it does not hold
the second coin twice, unless the two coins are equal. -/
theorem hearer_only_in_order (asked : Asked)
    {held heard : model.Value law.output × model.Value law.output}
    (together : ReturnTogether sampler (drawsTwice site law inputs)
      (hearsTwice (model := model) site law) Mail.empty Board.empty Heard.start Heard.start asked
      held heard) :
    held = (firstCoin sampler site law asked, secondCoin sampler site law asked) ∧
      heard = (firstCoin sampler site law asked, secondCoin sampler site law asked) := by
  cases together with
  | receiveRight found _ => cases found
  | hearRight _ announced _ => cases announced
  | drawLeft together =>
    cases together with
    | receiveRight found _ => cases found
    | drawLeft together =>
      -- Both coins are announced before the hearer moves.
      cases together with
      | receiveRight found _ => cases found
      | hearRight _ first together =>
        cases together with
        | receiveRight found _ => cases found
        | hearRight _ second together =>
          cases together
          simp [Board.announce, Board.empty, Heard.next] at first second
          subst first second
          exact ⟨rfl, rfl⟩
    | hearRight _ first together =>
      -- The hearer hears the first coin before the second one is announced.
      cases together with
      | receiveRight found _ => cases found
      | hearRight _ second _ => simp [Board.announce, Board.empty, Heard.next] at second
      | drawLeft together =>
        cases together with
        | receiveRight found _ => cases found
        | hearRight _ second together =>
          cases together
          simp [Board.announce, Board.empty, Heard.next] at first second
          subst first second
          exact ⟨rfl, rfl⟩

/-- A run in which the hearer holds the second coin twice is a run in which the two coins
are equal. -/
theorem second_coin_twice_only_when_equal (asked : Asked)
    {held : model.Value law.output × model.Value law.output}
    (together : ReturnTogether sampler (drawsTwice site law inputs)
      (hearsTwice (model := model) site law) Mail.empty Board.empty Heard.start Heard.start asked
      held (secondCoin sampler site law asked, secondCoin sampler site law asked)) :
    firstCoin sampler site law asked = secondCoin sampler site law asked :=
  (congrArg Prod.fst (hearer_only_in_order sampler site law inputs asked together).2).symm

/-- An owner that draws once, and a hearer that receives once at the site. -/
def drawsOnce : PIR.Process (Effects model) (model.Value law.output) :=
  .call (.draw site law inputs) fun coin => .done coin

def hearsOnceAt : PIR.Process (Effects model) (model.Value law.output) :=
  .call (.receive site law.output) fun coin => .done coin

/-- From a board with a coin at the site that the hearer has not heard, the hearer of a draw
holds that stale coin, whatever the coin of the draw. -/
theorem behind_hears_stale (stale : model.Value law.output) (asked : Asked)
    {held heard : model.Value law.output}
    (together : ReturnTogether sampler (drawsOnce site law inputs)
      (hearsOnceAt (model := model) site law) Mail.empty
      ((Board.empty : Board model).announce site law.output stale) Heard.start Heard.start asked
      held heard) : heard = stale := by
  cases together with
  | receiveRight found _ => cases found
  | hearRight _ announced together =>
    cases together with
    | drawLeft together =>
      cases together
      simp [Board.announce, Board.empty] at announced
      exact announced.symm
  | drawLeft together =>
    cases together with
    | receiveRight found _ => cases found
    | hearRight _ announced together =>
      cases together
      simp [Board.announce, Board.empty] at announced
      exact announced.symm

end Pair

/-- At the one-point model with coins that alternate, the stale coin `true` is not the coin
`false` of the draw: from that board the hearer does not hold the coin of the draw. -/
theorem stale_is_not_drawn {held : Bool}
    (together : ReturnTogether (Samplers.sampler Model.unit)
      (drawsOnce (model := Model.unit) ⟨[], 0, 0⟩ ⟨0, [], .bool, rfl⟩ .nil)
      (hearsOnceAt (model := Model.unit) ⟨[], 0, 0⟩ ⟨0, [], .bool, rfl⟩) Mail.empty
      ((Board.empty : Board Model.unit).announce ⟨[], 0, 0⟩ .bool true) Heard.start Heard.start
      Asked.start held
      ((Samplers.sampler Model.unit).answer ⟨[], 0, 0⟩ 0 ⟨0, [], .bool, rfl⟩)) : False :=
  Bool.noConfusion
    (behind_hears_stale (Samplers.sampler Model.unit) ⟨[], 0, 0⟩ ⟨0, [], .bool, rfl⟩ .nil true
      Asked.start together)

/-! ## The conditions introduced with the relation -/

/-- Listeners of which the second hears everywhere. -/
def secondHears : Listeners := ⟨fun _ => false, fun _ => true⟩

/-- At the start of a run every coin has been heard. -/
theorem start_heardAll : secondHears.HeardAll (Board.empty : Board Model.unit) Heard.start
    Heard.start :=
  secondHears.heardAll_start

/-- With a coin on the board that the second has not heard, not every coin has been heard. -/
theorem behind_not_heardAll :
    ¬ secondHears.HeardAll ((Board.empty : Board Model.unit).announce ⟨[], 0, 0⟩ .bool true)
      Heard.start Heard.start := by
  intro heardAll
  have behind := heardAll.second ⟨[], 0, 0⟩ rfl
  simp [Board.announce, Board.empty] at behind

/-- A side of one role holds at most one role. -/
theorem single_atMostOne (role roles : Nat) : (single role).AtMostOne roles :=
  (Side.only_single role roles).atMostOne

/-- The side of both roles of a protocol of two roles holds two. -/
theorem both_not_atMostOne : ¬ Samplers.both.AtMostOne 2 := fun atMostOne =>
  absurd (atMostOne 0 1 (by decide) (by decide) rfl rfl) (by decide)

/-- The side of one role holds at most one of two receivers. -/
theorem single_hearsOnce : hearsOnce (single 0) [0, 1] :=
  ⟨fun _ => rfl, fun inside => Bool.noConfusion inside, trivial⟩

/-- The side of both roles holds two receivers: its process would receive twice for one
coin. -/
theorem both_hears_twice : ¬ hearsOnce Samplers.both [0, 1] := fun once =>
  Bool.noConfusion (once.1 rfl)

section Hearing

variable {model : Model} (sampler : Sampler model) (site : Site) (type : Ty)
  (coin : model.Value type)

/-- A `receive` at the site hears the coin once. -/
theorem receive_hears :
    Hears sampler site type coin true
      (.call (.receive site type) fun reply => .done reply) coin :=
  Hears.receive fun reply => reply

/-- A `receive` is not a process that performs nothing: against a process that has returned,
with no coin announced, it does not return. -/
theorem receive_not_silent :
    ¬ Hears sampler site type coin false
      (.call (.receive site type) fun reply => .done reply) coin := by
  intro silent
  have waits := silent.run (.done ()) PIR.Process.done Board.empty Heard.start Heard.start
    Asked.start () coin (fun listens => nomatch listens) (.done _ _ _ _ _ _ _)
  cases waits with
  | receiveRight found _ => cases found
  | hearRight _ announced _ => cases announced

/-- A function that draws performs an effect: a table with it is not one whose functions
perform none. The functions of a package perform none (`Samplers.honest_quiet`). -/
theorem draw_not_quiet (law : SamplingRow) (inputs : Values model.Value law.inputs) :
    ¬ (drawsOnce (model := model) site law inputs).Quiet := fun quiet => quiet

end Hearing

/-! ## A draw in a loop -/

/-- In each of two iterations the verifier, role 1, draws a coin at site 0 and the prover,
role 0, hears it. Each collects its two coins. -/
abbrev loopedRaw : Raw.Package :=
  ⟨[], [], [], [Samplers.lawOf .bool], [],
    [⟨false, 2, [], [⟨.seq .bool (some 2), 0⟩, ⟨.seq .bool (some 2), 1⟩], [],
      .step (.repeat [0, 1] (.static 2) [] [] [⟨.bool, 0⟩, ⟨.bool, 1⟩]
          (.step (.draw 1 [0] 0 0 []) (.ret [3, 2]))) <|
        .ret [0, 1]⟩],
    none⟩

kernel_refl looped_elaborates : (elaborate loopedRaw).isOk equals true

noncomputable def loopedElaborated : Typed := Typed.ofRaw loopedRaw looped_elaborates

typed_literal looped := loopedElaborated

kernel_refl looped_eq : elaborate loopedRaw equals Except.ok looped

/-- The header of the protocol: the prover's collection and the verifier's. -/
abbrev loopedHeader : ProtocolHeader :=
  ⟨2, [], [⟨.seq .bool (some 2), 0⟩, ⟨.seq .bool (some 2), 1⟩], .none, false⟩

abbrev loopedEntry : Var looped.protocols loopedHeader := ⟨0, rfl⟩

/-- The grouped meaning of the protocol: its meaning for the side of both roles. -/
noncomputable abbrev loopedGrouped (model : Model) :
    PIR.Process (Effects model) (Values (SideValue model Samplers.both) loopedHeader.outputs) :=
  (looped.program.protocols.table model (looped.program.functionTable model)
    Identities.written).get loopedEntry [] Samplers.both .nil

/-- The coins that the prover collected. -/
abbrev proverCoins (model : Model)
    (outputs : Values (SideValue model Samplers.both) loopedHeader.outputs) : List Bool :=
  (Held.value (X := model.Value (.seq .bool (some 2))) (Samplers.both 0) rfl
    (outputs.get .here)).val

/-- The coins that the verifier collected. -/
abbrev verifierCoins (model : Model)
    (outputs : Values (SideValue model Samplers.both) loopedHeader.outputs) : List Bool :=
  (Held.value (X := model.Value (.seq .bool (some 2))) (Samplers.both 1) rfl
    (outputs.get (.there .here))).val

/-- Whether the prover collected the coins that the verifier drew, in order. -/
abbrev sameCoins (model : Model) :
    Values (SideValue model Samplers.both) loopedHeader.outputs → Bool :=
  fun outputs => proverCoins model outputs == verifierCoins model outputs

/-- On every coin the grouped run returns with the prover holding the verifier's coins. -/
theorem looped_every_coin (model : Model) :
    Samplers.returnsOnEveryCoin (sameCoins model) 2 (loopedGrouped model) = true :=
  kernel_rfl%

kernel_refl looped_projects : (projectProtocols looped.program.protocols).isOk equals true

/-- The role programs of the package. -/
noncomputable def loopedRoles :
    Projected (looped.table.map (·.signature)) looped.functions looped.protocols :=
  Samplers.okValue (projectProtocols looped.program.protocols) looped_projects

kernel_refl looped_prover_named : (loopedRoles.callees.find loopedEntry 0).isSome equals true
kernel_refl looped_verifier_named : (loopedRoles.callees.find loopedEntry 1).isSome equals true

/-- The endpoint lemma at the package, for every model and every sampler: the grouped run
returns, so the programs of the prover and of the verifier, run against each other from the
start of a run, return together what each holds of what the grouped run returns, and the
prover holds the coins that the verifier drew. The prover hears two coins at one site. -/
theorem looped_endpoints (model : Model) (sampler : Sampler model) :
    ∃ (prover : Var loopedRoles.headers (roleHeader 0 loopedHeader))
      (verifier : Var loopedRoles.headers (roleHeader 1 loopedHeader)),
      loopedRoles.callees.find loopedEntry 0 = some prover ∧
      loopedRoles.callees.find loopedEntry 1 = some verifier ∧
      ∃ outputs, proverCoins model outputs = verifierCoins model outputs ∧
        ReturnTogether sampler
          ((loopedRoles.programs.table model (looped.program.functionTable model)
              Identities.written).get prover []
            (ownValues model (single 0) 0 (Side.single_inside 0) loopedHeader.inputs
              (leftValues model (single 0) (single 1) .nil)))
          ((loopedRoles.programs.table model (looped.program.functionTable model)
              Identities.written).get verifier []
            (ownValues model (single 1) 1 (Side.single_inside 1) loopedHeader.inputs
              (rightValues model (single 0) (single 1) .nil)))
          Mail.empty Board.empty Heard.start Heard.start Asked.start
          (ownValues model (single 0) 0 (Side.single_inside 0) loopedHeader.outputs
            (leftValues model (single 0) (single 1) outputs))
          (ownValues model (single 1) 1 (Side.single_inside 1) loopedHeader.outputs
            (rightValues model (single 0) (single 1) outputs)) := by
  obtain ⟨prover, namedProver⟩ := Option.isSome_iff_exists.mp looped_prover_named
  obtain ⟨verifier, namedVerifier⟩ := Option.isSome_iff_exists.mp looped_verifier_named
  obtain ⟨outputs, returns, accepts⟩ :=
    Samplers.returnsOnEveryCoin_sound sampler (sameCoins model) 2 _ Asked.start
      (looped_every_coin model)
  exact ⟨prover, verifier, namedProver, namedVerifier, outputs, eq_of_beq accepts,
    program_endpoints_return sampler (looped.program.functionTable model)
      (Functions.table_quiet looped.program.functions) Identities.written
      looped.program.protocols loopedRoles (Samplers.okValue_eq _ looped_projects)
      loopedEntry (single 0) (single 1) single_disjoint 0 1 (Side.only_single 0 _)
      (Side.only_single 1 _) (Side.single_inside 0) (Side.single_inside 1) prover verifier
      namedProver namedVerifier [] .nil outputs Asked.start returns⟩

/-- The listeners of the protocol for the prover and the verifier. -/
noncomputable abbrev loopedListeners : Listeners :=
  looped.program.protocols.listeners loopedEntry [] (single 0) (single 1)

/-- The prover hears at the site of the draw. -/
theorem prover_hears : loopedListeners.first ⟨[], 0, 0⟩ = true := kernel_rfl%

/-- The verifier, which owns the draw, does not hear at its site. -/
theorem verifier_does_not_hear : loopedListeners.second ⟨[], 0, 0⟩ = false := kernel_rfl%

/-- The listeners of the protocol are those of the protocol. -/
theorem looped_listened :
    ((looped.program.protocols.listens loopedListeners Identities.written).get loopedEntry) []
      (single 0) (single 1) :=
  Protocols.entry_listened Identities.written looped.program.protocols loopedEntry []
    (single 0) (single 1) (single_atMostOne 0 _) (single_atMostOne 1 _)

/-- The listeners of the protocol read what the protocol answers. -/
theorem looped_reads :
    loopedListeners.ReadBelow [] ((looped.program.protocols.hearers.get loopedEntry) (single 0)
      (single 1)) :=
  Listeners.below_reads [] _

/-- Listeners that say that nobody hears. -/
def deaf : Listeners := ⟨fun _ => false, fun _ => false⟩

/-- Listeners that say that nobody hears do not read what the protocol answers at the site of
the draw. -/
theorem deaf_does_not_read :
    ¬ deaf.ReadBelow [] ((looped.program.protocols.hearers.get loopedEntry) (single 0)
      (single 1)) := by
  intro reads
  have atDraw := reads [] 0 0 (true, false) kernel_rfl%
  exact Bool.noConfusion atDraw.1

/-- Listeners that say that nobody hears are not those of the protocol: the prover hears at
the site of the draw. -/
theorem deaf_not_listened :
    ¬ ((looped.program.protocols.listens deaf Identities.written).get loopedEntry) []
      (single 0) (single 1) := by
  intro listened
  have atDraw : deaf.first ⟨[], 0, 0⟩ = (single 1 1 && [0].any (single 0)) := listened.2.1.1.1.1
  exact Bool.noConfusion atDraw

#print axioms hearer_in_order
#print axioms hearer_only_in_order
#print axioms second_coin_twice_only_when_equal
#print axioms behind_hears_stale
#print axioms stale_is_not_drawn
#print axioms behind_not_heardAll
#print axioms both_not_atMostOne
#print axioms both_hears_twice
#print axioms receive_not_silent
#print axioms draw_not_quiet
#print axioms looped_endpoints
#print axioms looped_listened
#print axioms deaf_does_not_read
#print axioms deaf_not_listened

end Broadcast
