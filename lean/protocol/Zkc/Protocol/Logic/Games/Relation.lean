module

public import VCVio.EvalDist.ProbabilityBounds
public import VCVio.OracleComp.ProbComp

@[expose] public section

/-! # Quantitative stage relations

A verification stage relates two attack games. A game (`Game`) packages an
adversary class, budgets, the admissibility of an adversary at a budget, and the
probability of the game's bad event for each adversary: the application event
the stage is about, such as acceptance of a false statement.

A stage relation (`Relation Src Tgt`) bounds the target game by the source game:
a target adversary admissible at budget `b` is translated, possibly with private
randomness, into source adversaries admissible at the transported budget
`budget b`, and the target's bad probability is at most the worst translated
adversary's source bad probability plus the loss `loss b`. The bound is against the
worst adversary in the translation's support, not the average over its randomness, so a
translation that succeeds only with small probability can determine it: this suffices
for bounds that hold at every budget for every admissible adversary, but a relation does
not preserve a randomized translation's average success as a computational reduction
does. Exact compilation
equalities are zero-loss deterministic translations (`Relation.ofLe`);
executable pruning is acceptance inclusion; a provider simulation translates
primitive-oracle adversaries into history-oracle adversaries with a statistical
loss.

Composition (`Relation.comp`) runs the translations in sequence and transports
budgets before evaluating the earlier stage's loss: the composed loss at `b` is
`r₂.loss b + r₁.loss (r₂.budget b)`. Losses therefore cannot be added without
transporting the resources at which they are evaluated. Composition has the
identity relation (`Relation.id`) as unit and is associative on translations,
budgets and losses (`id_comp`, `comp_id`, `comp_assoc`). A bound on the source
game transfers to the target game (`Relation.transfer`); a bound on a game is a
relation from the trivial game (`Relation.ofBound`), so a chain of stages ending
in an endpoint theorem is one relation from the trivial game, whose loss is the
end-to-end bound.

Knowledge claims stay outside: an extractor-based theorem concludes an
extraction probability, not a bad-event bound, and keeps its own endpoint.
-/

set_option autoImplicit false

namespace ZkcSecurity.Stage
open OracleComp

/-- An attack game: adversaries, budgets, the admissibility of an adversary at a
budget, and the probability of the bad event for each adversary. -/
structure Game where
  Adversary : Type
  Budget : Type
  Admissible : Budget → Adversary → Prop
  bad : Adversary → ENNReal

namespace Game

/-- The worst bad probability over the support of a randomized adversary. -/
noncomputable def worst (game : Game) (adversaries : ProbComp game.Adversary) : ENNReal :=
  ⨆ adversary ∈ support adversaries, game.bad adversary

/-- A game is bounded by `bound` when every admissible adversary's bad
probability is at most the bound at its budget. -/
def Bounded (game : Game) (bound : game.Budget → ENNReal) : Prop :=
  ∀ budget adversary, game.Admissible budget adversary → game.bad adversary ≤ bound budget

/-- The trivial game: one adversary that never wins. -/
def trivial : Game where
  Adversary := Unit
  Budget := Unit
  Admissible _ _ := True
  bad _ := 0

theorem worst_pure (game : Game) (adversary : game.Adversary) :
    game.worst (pure adversary) = game.bad adversary := by
  simp [worst]

theorem le_worst (game : Game) {adversaries : ProbComp game.Adversary} {adversary : game.Adversary}
    (member : adversary ∈ support adversaries) : game.bad adversary ≤ game.worst adversaries :=
  le_iSup₂ (f := fun adversary (_ : adversary ∈ support adversaries) => game.bad adversary)
    adversary member

theorem worst_le (game : Game) {adversaries : ProbComp game.Adversary} {bound : ENNReal}
    (bounded : ∀ adversary ∈ support adversaries, game.bad adversary ≤ bound) :
    game.worst adversaries ≤ bound :=
  iSup₂_le bounded

end Game

/-- A target game bounded by a source game, up to a randomized adversary
translation, a budget map and a loss. A target adversary admissible at `b` is
translated into source adversaries admissible at `budget b`, and its bad
probability is at most the worst translated adversary's plus `loss b`. -/
structure Relation (Src Tgt : Game) where
  translate : Tgt.Budget → Tgt.Adversary → ProbComp Src.Adversary
  budget : Tgt.Budget → Src.Budget
  admissible : ∀ b adversary, Tgt.Admissible b adversary →
    ∀ translated ∈ support (translate b adversary), Src.Admissible (budget b) translated
  loss : Tgt.Budget → ENNReal
  bound : ∀ b adversary, Tgt.Admissible b adversary →
    Tgt.bad adversary ≤ Src.worst (translate b adversary) + loss b

namespace Relation
variable {S M T U : Game}

/-- Two relations with the same translation, budget map and loss are equal. -/
theorem ext {first second : Relation S T} (translate : first.translate = second.translate)
    (budget : first.budget = second.budget) (loss : first.loss = second.loss) : first = second := by
  cases first
  cases second
  cases translate
  cases budget
  cases loss
  rfl

/-- The identity relation: no translation, no budget change, no loss. -/
def id (game : Game) : Relation game game where
  translate _ adversary := pure adversary
  budget b := b
  admissible _ _ admissible translated member := by
    rw [support_pure, Set.mem_singleton_iff] at member
    subst member
    exact admissible
  loss _ := 0
  bound _ adversary _ := by rw [Game.worst_pure, add_zero]

/-- A deterministic zero-loss relation: every admissible target adversary's bad
probability is at most that of its image. Exact compilation equalities and
acceptance inclusions have this form. -/
def ofLe (translate : T.Adversary → S.Adversary) (budget : T.Budget → S.Budget)
    (admissible : ∀ b adversary, T.Admissible b adversary → S.Admissible (budget b) (translate adversary))
    (le : ∀ b adversary, T.Admissible b adversary → T.bad adversary ≤ S.bad (translate adversary)) :
    Relation S T where
  translate _ adversary := pure (translate adversary)
  budget := budget
  admissible b adversary holds translated member := by
    rw [support_pure, Set.mem_singleton_iff] at member
    subst member
    exact admissible b adversary holds
  loss _ := 0
  bound b adversary holds := by
    rw [Game.worst_pure, add_zero]
    exact le b adversary holds

/-- A bound on a game is a relation from the trivial game whose loss is the
bound. -/
def ofBound (game : Game) (bound : game.Budget → ENNReal) (bounded : game.Bounded bound) :
    Relation Game.trivial game where
  translate _ _ := pure ()
  budget _ := ()
  admissible _ _ _ _ _ := True.intro
  loss := bound
  bound b adversary holds := (bounded b adversary holds).trans le_add_self

/-- Composition: translate into the middle game, transport the budget, then into
the source game. The loss at `b` is the later stage's loss at `b` plus the
earlier stage's loss at the transported budget. -/
def comp (first : Relation S M) (second : Relation M T) : Relation S T where
  translate b adversary := second.translate b adversary >>= fun middle =>
    first.translate (second.budget b) middle
  budget b := first.budget (second.budget b)
  admissible b adversary holds translated member := by
    rw [mem_support_bind_iff] at member
    obtain ⟨middle, middleMember, member⟩ := member
    exact first.admissible _ middle (second.admissible b adversary holds middle middleMember)
      translated member
  loss b := second.loss b + first.loss (second.budget b)
  bound b adversary holds := by
    refine (second.bound b adversary holds).trans ?_
    have worst : M.worst (second.translate b adversary) ≤
        S.worst (second.translate b adversary >>= fun middle =>
          first.translate (second.budget b) middle) + first.loss (second.budget b) := by
      refine M.worst_le fun middle member => (first.bound _ middle
        (second.admissible b adversary holds middle member)).trans ?_
      refine add_le_add_left (S.worst_le fun translated translatedMember => S.le_worst ?_) _
      exact (mem_support_bind_iff _ _ _).mpr ⟨middle, member, translatedMember⟩
    calc M.worst (second.translate b adversary) + second.loss b
        ≤ S.worst (second.translate b adversary >>= fun middle =>
            first.translate (second.budget b) middle) + first.loss (second.budget b) +
              second.loss b := add_le_add_left worst _
      _ = _ := by rw [add_assoc, add_comm (first.loss _)]

theorem comp_loss (first : Relation S M) (second : Relation M T) (b : T.Budget) :
    (first.comp second).loss b = second.loss b + first.loss (second.budget b) :=
  rfl

theorem comp_budget (first : Relation S M) (second : Relation M T) (b : T.Budget) :
    (first.comp second).budget b = first.budget (second.budget b) :=
  rfl

/-- The identity is a left unit. -/
theorem id_comp (relation : Relation S T) : (Relation.id S).comp relation = relation :=
  ext (by funext b adversary; exact bind_pure _) rfl (by funext b; exact add_zero _)

/-- The identity is a right unit. -/
theorem comp_id (relation : Relation S T) : relation.comp (Relation.id T) = relation :=
  ext (by funext b adversary; exact pure_bind _ _) rfl (by funext b; exact zero_add _)

/-- Composition is associative. -/
theorem comp_assoc (first : Relation S M) (second : Relation M T) (third : Relation T U) :
    (first.comp second).comp third = first.comp (second.comp third) :=
  ext (by funext b adversary; exact (bind_assoc _ _ _).symm) rfl
    (by funext b; exact (add_assoc _ _ _).symm)

/-- A bound on the source game transfers to the target game at the transported
budget, with the loss added. -/
theorem transfer (relation : Relation S T) {bound : S.Budget → ENNReal} (secure : S.Bounded bound) :
    T.Bounded fun b => bound (relation.budget b) + relation.loss b := by
  intro b adversary holds
  refine (relation.bound b adversary holds).trans (add_le_add_left ?_ _)
  exact S.worst_le fun translated member =>
    secure _ translated (relation.admissible b adversary holds translated member)

/-- A relation from the trivial game bounds its target by its loss. -/
theorem bounded (relation : Relation Game.trivial T) : T.Bounded relation.loss := by
  intro b adversary holds
  have := relation.transfer (bound := fun _ => 0) (fun _ _ _ => le_rfl) b adversary holds
  simpa using this

end Relation

end ZkcSecurity.Stage
