module

public import Zkc.Core.EndpointsCompleteness

public section

/-! Every run of a process returns.

`EveryRun holds process`: along every choice of the replies to its draws and samples, the
process returns a value that `holds` is true of; it never stops, sends, receives or reads.
The condition quantifies over replies, not over samplers and counters, so it is taken
apart along sequencing (`everyRun_bind`): a process followed by a continuation returns on
every run exactly when every run of the process returns a value from which every run of
the continuation returns.

The condition is completeness for every sampler (`groupedComplete_iff_everyRun`): a grouped
process returns an accepted value under every sampler exactly when every run of it returns
an accepted value. From every run to every sampler, the run under a sampler is one of the
runs. From every sampler to every run, every choice of replies is the answers of some
sampler: a run consults a sampler at a site only at counts at or above the counter
(`ReturnsAlone.of_later_coins`), and a sampler can be given any value of a populated type as
its coin at one site and count (`Sampler.withCoin`), so the reply to one draw can be chosen
without changing what the rest of the run is asked. Nothing is assumed.
-/

set_option autoImplicit false

namespace Zkc.Core

open Zkc.Source

variable {model : Model}

/-- Along every choice of replies to its draws and samples the process returns a value of
which the condition holds. -/
@[expose] def EveryRun {α : Type} (holds : α → Prop) : PIR.Process (Effects model) α → Prop
  | .done value => holds value
  | .halt _ => False
  | .call (.draw _ _ _) next => ∀ reply, EveryRun holds (next reply)
  | .call (.sample _ _ _) next => ∀ reply, EveryRun holds (next reply)
  | .call (.send ..) _ => False
  | .call (.receive ..) _ => False
  | .call (.read ..) _ => False

/-- A weaker condition holds of every run. -/
theorem EveryRun.mono {α : Type} {holds weaker : α → Prop}
    (weakens : ∀ value, holds value → weaker value) :
    ∀ {process : PIR.Process (Effects model) α}, EveryRun holds process → EveryRun weaker process
  | .done value, every => weakens value every
  | .halt _, every => every
  | .call (.draw _ _ _) _, every => fun reply => EveryRun.mono weakens (every reply)
  | .call (.sample _ _ _) _, every => fun reply => EveryRun.mono weakens (every reply)
  | .call (.send ..) _, every => every
  | .call (.receive ..) _, every => every
  | .call (.read ..) _, every => every

/-- Every run of a process followed by a continuation returns exactly when every run of
the process returns a value from which every run of the continuation returns. -/
theorem everyRun_bind {α β : Type} (holds : β → Prop)
    (next : α → PIR.Process (Effects model) β) :
    ∀ (process : PIR.Process (Effects model) α),
      EveryRun holds (process.bind next) ↔ EveryRun (fun value => EveryRun holds (next value)) process
  | .done _ => Iff.rfl
  | .halt _ => Iff.rfl
  | .call (.draw _ _ _) tail =>
      forall_congr' fun reply => everyRun_bind holds next (tail reply)
  | .call (.sample _ _ _) tail =>
      forall_congr' fun reply => everyRun_bind holds next (tail reply)
  | .call (.send ..) _ => Iff.rfl
  | .call (.receive ..) _ => Iff.rfl
  | .call (.read ..) _ => Iff.rfl

/-! ## Every run and every sampler -/

/-- A sampler with a given coin at one site, count and type, and the coins of another
sampler everywhere else. -/
@[expose] def Sampler.withCoin (sampler : Sampler model) (site : Site) (count : Nat) (type : Ty)
    (coin : model.Value type) : Sampler model where
  coin other number otherType populated :=
    if same : other = site ∧ number = count ∧ otherType = type then same.2.2 ▸ coin
    else sampler.coin other number otherType populated

/-- The sampler answers the request at the site and count with the given coin. -/
theorem Sampler.withCoin_answer (sampler : Sampler model) (site : Site) (count : Nat)
    (law : SamplingRow) (coin : model.Value law.output) :
    (sampler.withCoin site count law.output coin).answer site count law = coin := by
  show (if same : site = site ∧ count = count ∧ law.output = law.output then same.2.2 ▸ coin
    else sampler.coin site count law.output law.populated) = coin
  split
  · rfl
  · rename_i differs
    exact absurd ⟨rfl, rfl, rfl⟩ differs

/-- At another site or another count the sampler has the coins it had. -/
theorem Sampler.withCoin_elsewhere (sampler : Sampler model) (site : Site) (count : Nat)
    (type : Ty) (coin : model.Value type) {other : Site} {number : Nat}
    (elsewhere : ¬(other = site ∧ number = count)) (otherType : Ty)
    (populated : otherType.populated = true) :
    (sampler.withCoin site count type coin).coin other number otherType populated =
      sampler.coin other number otherType populated := by
  show (if same : other = site ∧ number = count ∧ otherType = type then same.2.2 ▸ coin
    else sampler.coin other number otherType populated) = _
  split
  · rename_i same
    exact absurd ⟨same.1, same.2.1⟩ elsewhere
  · rfl

/-- One more answer at a site leaves no site asked less often. -/
theorem Asked.le_next (asked : Asked) (site other : Site) : asked other ≤ asked.next site other := by
  unfold Asked.next
  split
  · exact Nat.le_succ _
  · exact Nat.le_refl _

/-- After one more answer at a site, the site was asked once more. -/
theorem Asked.next_self (asked : Asked) (site : Site) : asked.next site site = asked site + 1 := by
  unfold Asked.next
  split
  · rfl
  · rename_i differs
    exact absurd rfl differs

/-- A run consults the sampler at a site only at counts at or above the counter: a sampler
with the same coins there gives the same run. -/
theorem ReturnsAlone.of_later_coins {sampler other : Sampler model} {α : Type}
    {process : PIR.Process (Effects model) α} {asked : Asked} {value : α}
    (returns : ReturnsAlone sampler process asked value) :
    (∀ (site : Site) (count : Nat) (type : Ty) (populated : type.populated = true),
      asked site ≤ count → sampler.coin site count type populated =
        other.coin site count type populated) →
      ReturnsAlone other process asked value := by
  induction returns with
  | done value asked => exact fun _ => .done value asked
  | draw site law inputs next asked value _ ih =>
      intro same
      refine .draw site law inputs next asked value ?_
      have answer : other.answer site (asked site) law = sampler.answer site (asked site) law :=
        (same site (asked site) law.output law.populated (Nat.le_refl _)).symm
      rw [answer]
      exact ih fun later count type populated above =>
        same later count type populated (Nat.le_trans (Asked.le_next asked site later) above)
  | sample site law inputs next asked value _ ih =>
      intro same
      refine .sample site law inputs next asked value ?_
      have answer : other.answer site (asked site) law = sampler.answer site (asked site) law :=
        (same site (asked site) law.output law.populated (Nat.le_refl _)).symm
      rw [answer]
      exact ih fun later count type populated above =>
        same later count type populated (Nat.le_trans (Asked.le_next asked site later) above)

/-- A run from the counter after a request does not see the coin of that request. -/
theorem ReturnsAlone.withoutCoin {sampler : Sampler model} {α : Type}
    {process : PIR.Process (Effects model) α} {asked : Asked} {site : Site} {type : Ty}
    {coin : model.Value type} {value : α}
    (returns : ReturnsAlone (sampler.withCoin site (asked site) type coin) process
      (asked.next site) value) :
    ReturnsAlone sampler process (asked.next site) value :=
  returns.of_later_coins fun other count otherType populated above =>
    Sampler.withCoin_elsewhere sampler site (asked site) type coin
      (fun same => by
        rw [same.1, Asked.next_self, same.2] at above
        exact Nat.not_succ_le_self _ above)
      otherType populated

/-- A process that returns a value of which the condition holds under every sampler, from
some counter, returns such a value on every run. -/
theorem everyRun_of_returnsAlone {α : Type} (holds : α → Prop) :
    ∀ (process : PIR.Process (Effects model) α) (asked : Asked),
      (∀ sampler : Sampler model, ∃ value, ReturnsAlone sampler process asked value ∧ holds value) →
        EveryRun holds process
  | .done _, asked, complete => by
      obtain ⟨_, returns, accepted⟩ := complete default
      cases returns
      exact accepted
  | .halt _, asked, complete => by
      obtain ⟨_, returns, _⟩ := complete default
      cases returns
  | .call (.draw site law _) next, asked, complete => fun reply =>
      everyRun_of_returnsAlone holds (next reply) (asked.next site) fun sampler => by
        obtain ⟨value, returns, accepted⟩ :=
          complete (sampler.withCoin site (asked site) law.output reply)
        cases returns with
        | draw _ _ _ _ _ _ returned =>
            rw [Sampler.withCoin_answer] at returned
            exact ⟨value, returned.withoutCoin, accepted⟩
  | .call (.sample site law _) next, asked, complete => fun reply =>
      everyRun_of_returnsAlone holds (next reply) (asked.next site) fun sampler => by
        obtain ⟨value, returns, accepted⟩ :=
          complete (sampler.withCoin site (asked site) law.output reply)
        cases returns with
        | sample _ _ _ _ _ _ returned =>
            rw [Sampler.withCoin_answer] at returned
            exact ⟨value, returned.withoutCoin, accepted⟩
  | .call (.send ..) _, asked, complete => by
      obtain ⟨_, returns, _⟩ := complete default
      cases returns
  | .call (.receive ..) _, asked, complete => by
      obtain ⟨_, returns, _⟩ := complete default
      cases returns
  | .call (.read ..) _, asked, complete => by
      obtain ⟨_, returns, _⟩ := complete default
      cases returns

/-- A process every run of which returns a value of which the condition holds returns such
a value under every sampler, from every counter. -/
theorem returnsAlone_of_everyRun {α : Type} (holds : α → Prop) (sampler : Sampler model) :
    ∀ (process : PIR.Process (Effects model) α) (asked : Asked), EveryRun holds process →
      ∃ value, ReturnsAlone sampler process asked value ∧ holds value
  | .done value, asked, every => ⟨value, .done value asked, every⟩
  | .halt _, _, every => every.elim
  | .call (.draw site law inputs) next, asked, every => by
      obtain ⟨value, returns, accepted⟩ := returnsAlone_of_everyRun holds sampler
        (next (sampler.answer site (asked site) law)) (asked.next site) (every _)
      exact ⟨value, .draw site law inputs next asked value returns, accepted⟩
  | .call (.sample site law inputs) next, asked, every => by
      obtain ⟨value, returns, accepted⟩ := returnsAlone_of_everyRun holds sampler
        (next (sampler.answer site (asked site) law)) (asked.next site) (every _)
      exact ⟨value, .sample site law inputs next asked value returns, accepted⟩
  | .call (.send ..) _, _, every => every.elim
  | .call (.receive ..) _, _, every => every.elim
  | .call (.read ..) _, _, every => every.elim

/-- A grouped process that is complete for every sampler returns an accepted value on every
run. -/
theorem GroupedComplete.everyRun {grouped : Type} {whole : PIR.Process (Effects model) grouped}
    {accepted : grouped → Prop} (complete : GroupedComplete whole accepted) :
    EveryRun accepted whole :=
  everyRun_of_returnsAlone accepted whole Asked.start complete

/-- A grouped process every run of which returns an accepted value is complete for every
sampler. -/
theorem EveryRun.groupedComplete {grouped : Type} {whole : PIR.Process (Effects model) grouped}
    {accepted : grouped → Prop} (every : EveryRun accepted whole) :
    GroupedComplete whole accepted :=
  fun sampler => returnsAlone_of_everyRun accepted sampler whole Asked.start every

/-- Completeness for every sampler is the condition that every run returns an accepted
value. -/
theorem groupedComplete_iff_everyRun {grouped : Type}
    {whole : PIR.Process (Effects model) grouped} {accepted : grouped → Prop} :
    GroupedComplete whole accepted ↔ EveryRun accepted whole :=
  ⟨GroupedComplete.everyRun, EveryRun.groupedComplete⟩

end Zkc.Core
