module

public import Zkc.Source.Structured.CollectionFold
public meta import Lean.Elab.Tactic

public meta section

/-! Small proof conveniences for generated helper presentations. The selected
run is generated from the actual source, and every supplied rewrite is an
ordinary theorem. The generic encoded list laws own all iteration; these
macros only discharge typed plumbing and expose unresolved callback premises.
No helper names or protocol cases are inspected. -/
namespace ZkcTools.StructuredSource.CollectionProofs
open Lean

macro "collection_simp" " [" definitions:term,* "]" : tactic => do
  let definitions ← definitions.getElems.mapM fun term => `(Parser.Tactic.simpLemma| $term:term)
  let definitions := definitions ++ #[← `(Parser.Tactic.simpLemma| and_true)]
  `(tactic| simp only [$definitions,*, Zkc.Source.Structured.Primitive.evaluateOn,
    Zkc.Source.Structured.primitiveOutcome, PIR.Process.bind,
    Zkc.Source.Environment.prepend, Zkc.Source.Environment.push, Zkc.Source.Values.get,
    Zkc.Source.Values.append, Zkc.Source.Values.split,
    Zkc.Source.Structured.Op.arguments, Zkc.Source.Structured.Op.results,
    Zkc.Source.Structured.Op.regions, Zkc.Source.Structured.FoldSpec.stepHelper,
    show "".isEmpty = true by rfl, Bool.true_eq,
    Zkc.Source.Values.get_head, Zkc.Source.Values.get_tail,
    Zkc.Source.Structured.ReferenceLibrary.marked,
    Zkc.Source.Structured.ReferenceLibrary.forward,
    Zkc.Source.Structured.ReferenceLibrary.call,
    Zkc.Source.Structured.Evaluation.invokeCallbackOn,
    Zkc.Source.Region.denote, Zkc.Source.Regions.denote,
    Zkc.Source.Operands.eval, Zkc.Source.Structured.Evaluation.meaningOn,
    Zkc.Source.Structured.Evaluation.operationOn,
    Zkc.Source.Structured.SiteObservations.closed, Zkc.Source.Structured.SiteObservations.silent,
    show 0 < Zkc.Source.Structured.indexLimit by decide +kernel,
    show 1 < Zkc.Source.Structured.indexLimit by decide +kernel,
    ↓reduceIte, List.cons_append, List.nil_append, List.append_nil,
    List.flatten_replicate_singleton])

syntax "collection_loop " "(" term ")" " with_encoder " "(" term ")" " with_chunk " "(" term ")" " using " "[" term,* "]" : tactic
macro_rules
  | `(tactic| collection_loop ($selected:term) with_encoder ($encoder:term) with_chunk ($piece:term) using [$laws:term,*]) =>
    `(tactic| {
      collection_simp [$selected, $laws,*]
      erw [Zkc.Source.Structured.Evaluation.denoteLoopOn_append_encode
        (encode := $encoder) (chunk := $piece)]
      · collection_simp [$laws,*]
      · intro xs index
        collection_simp [$laws,*] })

syntax "collection_checked_loop " "(" term ")" " with_encoder " "(" term ")"
  " with_chunk " "(" term ")" " using " "[" term,* "]" : tactic
macro_rules
  | `(tactic| collection_checked_loop ($selected:term) with_encoder ($encoder:term)
      with_chunk ($piece:term) using [$laws:term,*]) =>
    `(tactic| {
      collection_simp [$selected]
      erw [Zkc.Source.Structured.Evaluation.denoteLoopOn_repeatAppend
        (encode := $encoder) (chunk := $piece)]
      · collection_simp [Zkc.Source.Finite.toProcess, $laws,*]
        first | rfl | (split <;> collection_simp [Zkc.Source.Finite.toProcess, $laws,*] <;> simp_all only [])
      · intro xs index
        collection_simp [Zkc.Source.Finite.toProcess, $laws,*] })

syntax "collection_fold " "(" term ")" " over " "(" term ")"
  " with_encoder " "(" term ")" " with_chunk " "(" term ")" " using " "[" term,* "]" : tactic
macro_rules
  | `(tactic| collection_fold ($selected:term) over ($items:term)
      with_encoder ($encoder:term) with_chunk ($piece:term) using [$laws:term,*]) =>
    `(tactic| {
      collection_simp [$selected]
      simp only [Zkc.Source.Structured.Evaluation.denoteFoldOn,
        Zkc.Source.Structured.DomainSpec.admit, Zkc.Source.Structured.DomainBody.admit,
        Zkc.Source.Structured.DomainNode.admit, Zkc.Source.Structured.Collection.values,
        Zkc.Source.Values.split, Zkc.Source.Values.get, Zkc.Source.Finite.continueWith]
      by_cases bounded : ($items).length < Zkc.Source.Structured.indexLimit
      · simp only [bounded, ↓reduceIte, Zkc.Source.Finite.continueWith,
          Zkc.Source.Finite.admitThen, Zkc.Source.Finite.fold_map]
        erw [Zkc.Source.Finite.fold_append_encode
          (encode := $encoder) (chunk := $piece)]
        · collection_simp [bounded, $laws,*]
        · intro xs item
          collection_simp [Zkc.Source.Structured.Evaluation.foldTransitionOn, $laws,*]
      · collection_simp [bounded, Zkc.Source.Finite.continueWith, Zkc.Source.Finite.admitThen, $laws,*] })

/-- Install a body law after the chosen generated view covers the entire ABI.
The source association and dependency proof are explicit inputs. -/
macro "install_collection% " law:term " for_helper " helper:term " in_definitions " definitions:term
    " linked_by " linked:term " body_at " associated:term " view_by " surjective:term
    " requiring " premise:term : term =>
  `(term| ($law).realizes (helper := $helper) $definitions $linked $associated (by
    intro arguments
    obtain ⟨view, same⟩ := $surjective arguments
    rw [same]
    cases view
    exact $premise))

end ZkcTools.StructuredSource.CollectionProofs
