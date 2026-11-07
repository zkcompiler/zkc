module

public import Zkc.Realization.QueryContinuation
public import Zkc.Source.Structured.OracleBody
public import Zkc.Semantics.Interaction

@[expose] public section

/-! A saved answer prefix is associated with the remaining *original* virtual
body. `PIR.Reaches` follows that body's actual continuations. The physical
indices recover its ordered, kind-indexed replies from the current arenas.
There is no separate virtual-body evaluator and no inferred mathematical law.
The controller's static continuation and captured source body must still be
connected to this relation by its entry/save/return rules.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Zkc.Realization.QuerySourceContinuation
open Zkc.Source Zkc.Source.Structured

variable {model : DomainModel} {A : Type}

/-- Only returned replies enter the saved prefix. A refused or incomplete
child never manufactures the value needed to advance its parent. -/
structure Answers (model : DomainModel) where
  kinds : List OracleKind
  values : Values (fun kind ↦ model.Value kind.answer) kinds

def Answers.empty : Answers model := ⟨[], .nil⟩

def Answers.append (before : Answers model) (request : OracleRead)
    (reply : model.Value request.kind.answer) : Answers model :=
  ⟨before.kinds ++ [request.kind], before.values.append (.cons reply .nil)⟩

/-- This is the existing source reachability judgment with an answer log as
its phase. Source operations themselves determine the requested handles,
positions and child continuations. The log does not authorize a request. -/
abbrev interaction (model : DomainModel) : PIR.Interaction (oracleReadInterface model.toCarriers) where
  Role := Unit
  Phase := Answers model
  owner := fun _ ↦ ()
  enabled := fun _ _ ↦ True
  advance := Answers.append

theorem reached_length
    {source residual : PIR.Process (oracleReadInterface model.toCarriers) A}
    {initial final : Answers model}
    (path : PIR.Reaches (interaction model) source initial residual final) :
    initial.kinds.length ≤ final.kinds.length := by
  match path with
  | .refl _ _ => exact Nat.le_refl _
  | .step request next before reply tail finish rest =>
      have ih := reached_length rest
      change (before.kinds ++ [request.kind]).length ≤ finish.kinds.length at ih
      simp only [List.length_append, List.length_cons, List.length_nil] at ih
      omega

/-- A cursor cannot skip a source query without recording its returned reply.
This also rules out reaching a different continuation with an empty prefix. -/
theorem reached_same_length
    {source residual : PIR.Process (oracleReadInterface model.toCarriers) A}
    {initial final : Answers model}
    (path : PIR.Reaches (interaction model) source initial residual final)
    (same : initial.kinds.length = final.kinds.length) :
    source = residual ∧ initial = final := by
  match path with
  | .refl _ _ => exact ⟨rfl, rfl⟩
  | .step request next before reply tail finish rest =>
      have consumed := reached_length rest
      change (before.kinds ++ [request.kind]).length ≤ finish.kinds.length at consumed
      simp only [List.length_append, List.length_cons, List.length_nil] at consumed
      omega

theorem reached_one
    {source residual : PIR.Process (oracleReadInterface model.toCarriers) A}
    {initial final : Answers model}
    (path : PIR.Reaches (interaction model) source initial residual final)
    (one : final.kinds.length = initial.kinds.length + 1) :
    ∃ (request : OracleRead)
      (next : model.Value request.kind.answer → PIR.Process (oracleReadInterface model.toCarriers) A)
      (reply : model.Value request.kind.answer),
      source = .call request next ∧ residual = next reply ∧
        final = initial.append request reply := by
  match path with
  | .refl _ _ => omega
  | .step request next before reply tail finish rest =>
      obtain ⟨sameResidual, sameAnswers⟩ := reached_same_length rest (by
        simpa only [interaction, Answers.append, List.length_append,
          List.length_cons, List.length_nil, Nat.zero_add] using one.symm)
      exact ⟨request, next, reply, rfl, sameResidual.symm, sameAnswers.symm⟩

structure Associated
    (arenas : (kind : OracleKind) → List (model.Value kind.answer))
    (source residual : PIR.Process (oracleReadInterface model.toCarriers) A)
    (indices : List Nat) where
  answers : Answers model
  reached : PIR.Reaches (interaction model) source Answers.empty residual answers
  stored : QueryContinuation.AnswersRead arenas indices answers.values

/-- The initial cursor is the actual source body, before any child has
returned. No equation about its mathematical result is required. -/
def initial
    (arenas : (kind : OracleKind) → List (model.Value kind.answer))
    (source : PIR.Process (oracleReadInterface model.toCarriers) A) :
    Associated arenas source source [] :=
  ⟨.empty, .refl (P := interaction model) source Answers.empty, .nil⟩

/-- Append-only answer storage preserves the same source residual and order. -/
def Associated.transport
    {before after : (kind : OracleKind) → List (model.Value kind.answer)}
    {source residual : PIR.Process (oracleReadInterface model.toCarriers) A}
    {indices : List Nat} (associated : Associated before source residual indices)
    (extension : ∀ kind, before kind <+: after kind) :
    Associated after source residual indices :=
  ⟨associated.answers, associated.reached, associated.stored.transport extension⟩

/-- The returned child's actual arena cell selects the next source
continuation. Both its kind and its place after earlier answers are retained.
The pending operation comes from the reached original body, not from a name
or the type of the physical answer. -/
def Associated.resume
    {arenas : (kind : OracleKind) → List (model.Value kind.answer)}
    {source : PIR.Process (oracleReadInterface model.toCarriers) A}
    {request : OracleRead}
    {next : model.Value request.kind.answer → PIR.Process (oracleReadInterface model.toCarriers) A}
    {indices : List Nat}
    (associated : Associated arenas source (.call request next) indices)
    {slot : Nat} {reply : model.Value request.kind.answer}
    (returned : (arenas request.kind)[slot]? = some reply) :
    Associated arenas source (next reply) (indices ++ [slot]) := by
  refine ⟨associated.answers.append request reply, ?_, ?_⟩
  · exact associated.reached.trans (.step (P := interaction model) request next associated.answers reply
      (next reply) (associated.answers.append request reply) (.refl _ _))
  · exact associated.stored.append (.cons returned .nil)

/-- Saved width counts actual child replies, including repeated requests and
equal-valued replies. It does not deduplicate by handle, position or value. -/
theorem Associated.width
    {arenas : (kind : OracleKind) → List (model.Value kind.answer)}
    {source residual : PIR.Process (oracleReadInterface model.toCarriers) A}
    {indices : List Nat} (associated : Associated arenas source residual indices) :
    indices.length = associated.answers.kinds.length := associated.stored.length

/-- One saved cell can only have consumed the source's first actual request.
Recover both the reply and continuation from that source; equal answer types
do not permit selecting a different pending child. -/
theorem Associated.one
    {arenas : (kind : OracleKind) → List (model.Value kind.answer)}
    {source residual : PIR.Process (oracleReadInterface model.toCarriers) A}
    {slot : Nat} (associated : Associated arenas source residual [slot]) :
    ∃ (request : OracleRead)
      (next : model.Value request.kind.answer → PIR.Process (oracleReadInterface model.toCarriers) A)
      (reply : model.Value request.kind.answer),
      source = .call request next ∧ residual = next reply ∧
        (arenas request.kind)[slot]? = some reply := by
  rcases associated with ⟨answers, reached, stored⟩
  have width := stored.length
  obtain ⟨request, next, reply, sourceEq, residualEq, answersEq⟩ := reached_one reached
    (by simpa only [Answers.empty, List.length_cons, List.length_nil] using width.symm)
  subst answers
  change QueryContinuation.AnswersRead arenas [slot] (.cons reply .nil) at stored
  cases stored with
  | cons found tail => exact ⟨request, next, reply, sourceEq, residualEq, found⟩

end Zkc.Realization.QuerySourceContinuation
