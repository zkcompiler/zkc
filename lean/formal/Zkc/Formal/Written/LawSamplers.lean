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

The standard vocabulary has the uniform law at each type, so the samplers of a model of it are
given by type (`uniformDraws`). In the standard model, over any algebra, the law `uniform` of
the positions below `n + 1` draws one uniformly (`StandardModel.draws`); a model whose scalars
can be sampled draws more (`ArithmeticModel.draws`). No fee is paid at a coin whose law has no
sampler. The table of the laws with a sampler (`StandardModel.sampled`) is the table of the
draws in both directions (`StandardModel.sampled_iff_draws`).

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

/-! ## The laws of the standard vocabulary

The standard vocabulary has one law at each of its types, the uniform one, and its coins have
no payload. The samplers of a model of it are given by type: the type of the law, over the
nominal types of the vocabulary, and the type of the reply, over those of the package. -/

section
variable (M : Model Standard)

/-- The distribution of the uniform law at each type and for each type of reply; none where the
model has none. -/
abbrev UniformDraws :=
  (type : Zkc.Vocabulary.Ty) → (τ : Standard.Ty) → Option (ProbComp (M.Val τ))

/-- The samplers of the laws of the standard vocabulary, from those of the uniform law by
type. -/
def uniformDraws (draw : UniformDraws M) : LawDraws M
  | .uniform type, [], _, τ => draw type τ
  | _, _ :: _, _, _ => none

/-- What the samplers draw is permitted when, type by type, what the uniform law draws is what
the world may give at its coin. -/
theorem uniformDraws_permitted (draw : UniformDraws M)
    (allowed : ∀ (type : Zkc.Vocabulary.Ty) (τ : Standard.Ty) (sampler : ProbComp (M.Val τ)),
      draw type τ = some sampler → ∀ v, v ∈ support sampler →
        Allows M (.coin (.uniform type)) [] .nil τ v)
    (op : ROp M) (sampler : ProbComp ((RSig M).Reply op))
    (has : lawSamplers M (uniformDraws M draw) op = some sampler)
    (v : (RSig M).Reply op) (drawn : v ∈ support sampler) : Permitted M op v := by
  match op, sampler, has, v, drawn with
  | .own (.coin (.uniform type)) _ _ [] .nil τ, sampler, has, v, drawn =>
    exact allowed type τ sampler has v drawn

end

/-- The uniform law in the standard model: at the positions below `n + 1` it draws one of them
uniformly. -/
noncomputable def StandardModel.uniformDraw {F G : Type} [DecidableEq F] [DecidableEq G]
    (D : StandardModel.Data F G) : UniformDraws (StandardModel.model D)
  | .fin (n + 1), .fin m => if m = n + 1 then some (drawPosition n) else none
  | _, _ => none

/-- The samplers of the laws in the standard model: `uniform` of the positions below `n + 1`
draws one of them uniformly. -/
noncomputable def StandardModel.draws {F G : Type} [DecidableEq F] [DecidableEq G]
    (D : StandardModel.Data F G) : LawDraws (StandardModel.model D) :=
  uniformDraws (StandardModel.model D) (StandardModel.uniformDraw D)

/-- What the uniform law of the standard model draws is what the world may give: a position
below the bound of its type. -/
theorem StandardModel.uniformDraw_allowed {F G : Type} [DecidableEq F] [DecidableEq G]
    (D : StandardModel.Data F G) (type : Zkc.Vocabulary.Ty) (τ : Standard.Ty)
    (sampler : ProbComp ((StandardModel.model D).Val τ))
    (has : StandardModel.uniformDraw D type τ = some sampler)
    (v : (StandardModel.model D).Val τ) (drawn : v ∈ support sampler) :
    Allows (StandardModel.model D) (.coin (.uniform type)) [] .nil τ v := by
  unfold StandardModel.uniformDraw at has
  split at has
  · rename_i n m
    split at has
    · rename_i same
      subst same
      obtain rfl := Option.some.inj has
      have below := lt_of_mem_support_drawPosition n v drawn
      exact ⟨below, ⟨[], .fin (n + 1)⟩, rfl, rfl, rfl, below⟩
    · exact absurd has (by simp)
  · exact absurd has (by simp)

/-- What the standard samplers draw is permitted: a position below the bound of its type. -/
theorem StandardModel.draws_permitted {F G : Type} [DecidableEq F] [DecidableEq G]
    (D : StandardModel.Data F G) (op : ROp (StandardModel.model D))
    (sampler : ProbComp ((RSig (StandardModel.model D)).Reply op))
    (has : lawSamplers (StandardModel.model D) (StandardModel.draws D) op = some sampler)
    (v : (RSig (StandardModel.model D)).Reply op) (drawn : v ∈ support sampler) :
    Permitted (StandardModel.model D) op v :=
  uniformDraws_permitted _ _ (StandardModel.uniformDraw_allowed D) op sampler has v drawn

/-- Whether the standard draws have a sampler for the uniform law of a type at a type of
reply. -/
def StandardModel.sampledType : Zkc.Vocabulary.Ty → Standard.Ty → Bool
  | .fin (n + 1), .fin m => m == n + 1
  | _, _ => false

/-- Whether the standard draws have a sampler for a law at a type of reply. -/
def StandardModel.sampled : Standard.LawKey → Standard.Ty → Bool
  | .uniform type, τ => StandardModel.sampledType type τ

/-- **The table is the table of the draws.** Over every algebra, a law is in the table exactly
when the model has a sampler for it. -/
theorem StandardModel.sampled_iff_draws {F G : Type} [DecidableEq F] [DecidableEq G]
    (D : StandardModel.Data F G) (law : Standard.LawKey) (τ : Standard.Ty) :
    StandardModel.sampled law τ = (StandardModel.draws D law [] .nil τ).isSome := by
  obtain ⟨type⟩ := law
  change StandardModel.sampledType type τ = (StandardModel.uniformDraw D type τ).isSome
  unfold StandardModel.sampledType StandardModel.uniformDraw
  split
  · rename_i n m
    by_cases same : m = n + 1 <;> simp [same]
  · rfl

/-- A law that the table has is drawn. -/
theorem StandardModel.draws_of_sampled {F G : Type} [DecidableEq F] [DecidableEq G]
    (D : StandardModel.Data F G) (law : Standard.LawKey) (τ : Standard.Ty)
    (has : StandardModel.sampled law τ = true) :
    (StandardModel.draws D law [] .nil τ).isSome = true :=
  StandardModel.sampled_iff_draws D law τ ▸ has

/-- Whether a program by names links only rows that the standard model interprets and draws
only laws of a table of samplers. -/
def StandardModel.coveredBy (sampled : Standard.LawKey → Standard.Ty → Bool)
    (p : NamedProgram Standard) : Bool :=
  p.rows.all StandardModel.interprets && p.laws.all fun (law, τ) => sampled law τ

/-- **The standard model covers a program**: it interprets every row of the vocabulary that the
program links, and has a sampler for the law of every coin that the program draws. A result over
the standard model is published for a program that it covers; of another program it would speak
of rows that the model gives a constant, or of coins at which no fee can be paid. -/
def StandardModel.covers (p : NamedProgram Standard) : Bool :=
  StandardModel.coveredBy StandardModel.sampled p

end Zkc.Formal.Written
