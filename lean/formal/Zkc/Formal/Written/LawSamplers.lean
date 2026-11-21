module

public import Zkc.Formal.Written.PortSamplers
public import Zkc.Formal.Written.StandardModel
public import Zkc.Core.Program.Links

@[expose] public section

/-!
The samplers of a statement, from the laws of its coins.

A law of the vocabulary has a support in a model. A probability needs a distribution, and it is
no choice of a proof: the sampler of a coin is the sampler of its law. `LawDraws` gives, for a
law, the payload of a coin and the type of its reply, the distribution that the law draws from;
`lawSamplers` are the samplers of every coin that a role owns. They read the law, the payload
and the type, and nothing of the other roles or of where the coin stands: a coin of one law is
drawn alike at every occurrence, under every audience, and in a callee as in its caller.

`serveLaws` is the service that answers each coin by the sampler of its law and nothing else.
It follows the samplers, and what it answers is permitted when what the samplers draw is: the
hypotheses of the bridge from the judgment with fees to a probability, met by a service that
answers.

In the standard model the law `uniform` of the positions below `n + 1` draws one uniformly
(`StandardModel.draws`). The other laws have no sampler there yet, so no fee is paid at their
coins.

`StandardModel.covers` says of a program by names that the standard model interprets every row
that it links (`StandardModel.interprets`) and has a sampler for every law that it draws
(`StandardModel.sampled`). It is decided by the kernel on the stored program.
-/

namespace Zkc.Formal.Written
open Core ProbabilisticProcess OracleComp ProbComp
open scoped NNRat ENNReal

section
variable {V : Vocabulary} (M : Model V)

/-- The distribution that each law draws from, at a payload and for a type of reply; none for a
law that has none in the model. -/
abbrev LawDraws :=
  (law : V.LawKey) → (ins : List V.Ty) → HList M.Val ins → (τ : V.Ty) → Option (ProbComp (M.Val τ))

variable (draws : LawDraws M)

/-- The samplers of the coins of a role: at a coin, the sampler of its law. No other effect has
one. -/
def lawSamplers : Samplers (RSig M)
  | .own (.coin law) _ _ ins payload τ => draws law ins payload τ
  | _ => none

/-- The service of the laws: it answers a coin by the sampler of its law, and nothing else. -/
def serveLaws : Service (RSig M) Unit := fun op s =>
  match lawSamplers M draws op with
  | some sampler => (fun answer => (some answer, s)) <$> sampler
  | none => pure (none, s)

theorem serveLaws_at {op : ROp M} {sampler : ProbComp ((RSig M).Reply op)}
    (has : lawSamplers M draws op = some sampler) (s : Unit) :
    serveLaws M draws op s = (fun answer => (some answer, s)) <$> sampler := by
  simp only [serveLaws, has]

/-- The service of the laws draws as the samplers do. -/
theorem serveLaws_follows : (serveLaws M draws).Follows (lawSamplers M draws) := by
  intro op sampler has s excluded
  rw [serveLaws_at M draws has s]
  refine (prEvent_map (mx := sampler) (f := fun answer => (some answer, s))
    (p := fun out : Option ((RSig M).Reply op) × Unit => ∃ v, out.1 = some v ∧ excluded v)).le.trans ?_
  exact prEvent_mono _ _ _ fun v ⟨w, same, ex⟩ => Option.some.inj same ▸ ex

/-- The service of the laws answers only what is permitted, when what each sampler draws is. -/
theorem serveLaws_permitted
    (allowed : ∀ (op : ROp M) (sampler : ProbComp ((RSig M).Reply op)),
      lawSamplers M draws op = some sampler → ∀ v, v ∈ support sampler → Permitted M op v)
    (op : ROp M) (s : Unit) (reply : (RSig M).Reply op) (t : Unit)
    (reached : (some reply, t) ∈ support (serveLaws M draws op s)) :
    Permitted M op reply := by
  cases has : lawSamplers M draws op with
  | none =>
    simp only [serveLaws, has, support_pure, Set.mem_singleton_iff, Prod.mk.injEq, reduceCtorEq,
      false_and] at reached
  | some sampler =>
    rw [serveLaws_at M draws has s] at reached
    simp only [support_map, Set.mem_image, Prod.mk.injEq, Option.some.injEq] at reached
    obtain ⟨v, drawn, rfl, _⟩ := reached
    exact allowed op sampler has v drawn

/-- The run of a process that begins with a coin, against the service of the laws, where the
sampler of the coin is a map of another draw: when what follows each reply ends with a known
outcome, an event of the outcome has the probability of the draws whose outcome is in it. -/
theorem prEvent_run_serveLaws {ι H A : Type} (op : ROp M) (base : ProbComp ι)
    (reply : ι → (RSig M).Reply op) (has : lawSamplers M draws op = some (reply <$> base))
    (next : (RSig M).Reply op → Process (RSig M) H A)
    (outcome : ι → ProbabilisticProcess.Outcome H A)
    (ends : ∀ i, run (serveLaws M draws) (next (reply i)) () = pure (outcome i, ()))
    (event : ProbabilisticProcess.Outcome H A → Prop) :
    Pr{let out ← run (serveLaws M draws) (.call op next) ()}[event out.1] =
      Pr{let i ← base}[event (outcome i)] := by
  have runs : run (serveLaws M draws) (.call op next) () = (fun i => (outcome i, ())) <$> base := by
    rw [run_call, serveLaws_at M draws has, Functor.map_map, bind_map_left]
    change (base >>= fun i => run (serveLaws M draws) (next (reply i)) ()) = _
    rw [show (fun i => run (serveLaws M draws) (next (reply i)) ()) =
      fun i => pure (outcome i, ()) from funext ends]
    exact bind_pure_comp _ _
  rw [runs, prEvent_map]

end

/-- The samplers of the laws in the standard model: `uniform` of the positions below `n + 1`
draws one of them uniformly. -/
noncomputable def StandardModel.draws {F G : Type} [DecidableEq F] [DecidableEq G]
    (D : StandardModel.Data F G) : LawDraws (StandardModel.model D)
  | .uniform (.fin (n + 1)), [], _, .fin m => if m = n + 1 then some (drawPosition n) else none
  | _, _, _, _ => none

/-- What the standard samplers draw is permitted: a position below the bound of its type. -/
theorem StandardModel.draws_permitted {F G : Type} [DecidableEq F] [DecidableEq G]
    (D : StandardModel.Data F G) (op : ROp (StandardModel.model D))
    (sampler : ProbComp ((RSig (StandardModel.model D)).Reply op))
    (has : lawSamplers (StandardModel.model D) (StandardModel.draws D) op = some sampler)
    (v : (RSig (StandardModel.model D)).Reply op) (drawn : v ∈ support sampler) :
    Permitted (StandardModel.model D) op v := by
  match op, sampler, has, v, drawn with
  | .own (.coin (.uniform (.fin (n + 1)))) _ _ [] .nil (.fin m), sampler, has, v, drawn =>
    simp only [lawSamplers, StandardModel.draws] at has
    split at has
    · rename_i same
      subst same
      obtain rfl := Option.some.inj has
      have below := lt_of_mem_support_drawPosition n v drawn
      exact ⟨below, ⟨[], .fin (n + 1)⟩, rfl, rfl, rfl, below⟩
    · exact absurd has (by simp)

/-- Whether the standard draws have a sampler for a law at a type of reply. -/
def StandardModel.sampled : Standard.LawKey → Standard.Ty → Bool
  | .uniform (.fin (n + 1)), .fin m => m == n + 1
  | _, _ => false

/-- A law that the table has is drawn. -/
theorem StandardModel.draws_of_sampled {F G : Type} [DecidableEq F] [DecidableEq G]
    (D : StandardModel.Data F G) (law : Standard.LawKey) (τ : Standard.Ty)
    (has : StandardModel.sampled law τ = true) :
    (StandardModel.draws D law [] .nil τ).isSome = true := by
  match law, τ, has with
  | .uniform (.fin (n + 1)), .fin m, has =>
    have same : m = n + 1 := by simpa [StandardModel.sampled] using has
    subst same
    simp [StandardModel.draws]

/-- **The standard model covers a program**: it interprets every row of the vocabulary that the
program links, and has a sampler for the law of every coin that the program draws. A result over
the standard model is published for a program that it covers; of another program it would speak
of rows that the model gives a constant, or of coins at which no fee can be paid. -/
def StandardModel.covers (p : NamedProgram Standard) : Bool :=
  p.rows.all StandardModel.interprets && p.laws.all fun (law, τ) => StandardModel.sampled law τ

end Zkc.Formal.Written
