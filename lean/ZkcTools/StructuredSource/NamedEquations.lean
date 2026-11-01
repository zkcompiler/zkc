module

public import Zkc.Source.Structured.DomainEvaluation
public import Zkc.Source.Structured.CollectionReference
public import Zkc.Source.TypedABI
public meta import Lean.Elab.Tactic

@[expose] public section

/-! Use a generated complete helper equation without restating its physical
return row. The equation and codecs remain ordinary kernel-checked constants.
This convenience performs no helper execution or mathematical proof search. -/
public meta section
namespace ZkcTools.StructuredSource.NamedEquations
open Lean Meta Elab Term

/-- Normalize only typed ABI access and process plumbing, including dependent
operation schemas. No helper or primitive implementation is unfolded. -/
macro "named_reduce" : tactic =>
  `(tactic| (
    dsimp only [Zkc.Source.Structured.Op.arguments, Zkc.Source.Structured.Op.results,
      Zkc.Source.Structured.Op.regions, Zkc.Source.Structured.Primitive.arguments,
      Zkc.Source.Structured.Primitive.results]
    simp only [_root_.PIR.Process.bind_assoc, _root_.PIR.Process.bind,
      Zkc.Source.Environment.prepend, Zkc.Source.Environment.push,
      Zkc.Source.Values.get_head, Zkc.Source.Values.get_tail, Zkc.Source.Values.get,
      Zkc.Source.Values.append, Zkc.Source.Values.split] ) )

/-- Apply explicitly selected mathematical definitions together with the same
finite row plumbing. Callback invocation here is only the application adapter;
helper table entries and their implementation laws remain caller-selected. -/
macro "named_reduce " "[" laws:Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| simp only [$laws,*,
    Zkc.Source.TypedABI.get_cons_here, Zkc.Source.TypedABI.get_cons_there,
    Zkc.Source.Environment.prepend, Zkc.Source.Environment.push,
    Zkc.Source.Structured.Evaluation.invokeCallbackOn,
    _root_.PIR.Process.bind_assoc, _root_.PIR.Process.bind])

macro "named_equation " name:ident &" over " field:term:max group:term:max : tactic => do
  let equation := mkIdent (name.getId ++ `equation)
  let run := mkIdent (name.getId ++ `run)
  let encode := mkIdent (name.getId ++ `encode)
  let decode := mkIdent (name.getId ++ `decode)
  `(tactic| (
    try simp only [Zkc.Source.Structured.meaning]
    try rw [Zkc.Source.Structured.Evaluation.denote_meaning_eq_meaningOn (F := $field) (G := $group)]
    rw [$equation:term (Zkc.Source.Structured.ringModel $field $group)]
    simp only [$run:term, $encode:term, $decode:term, _root_.PIR.Process.bind_assoc, _root_.PIR.Process.bind,
      Zkc.Source.Environment.prepend, Zkc.Source.Environment.push,
      Zkc.Source.Values.get] ) )

/-- A process reference may additionally compact dependent row arguments before
this rewrite. Both the equation and the entire process come from its certificate. -/
macro "named_process " process:ident &" over " field:term:max group:term:max : tactic => do
  let equation := mkIdent (process.getId.appendAfter "_equation")
  let certificate := mkIdent (process.getId.appendAfter "_certificate")
  `(tactic| (
    try simp only [Zkc.Source.Structured.meaning]
    try rw [Zkc.Source.Structured.Evaluation.denote_meaning_eq_meaningOn (F := $field) (G := $group)]
    rw [$equation:term (Zkc.Source.Structured.ringModel $field $group)]
    dsimp only [$process:term, $certificate:term]
    named_reduce ) )

end ZkcTools.StructuredSource.NamedEquations
