module

public import ZkcSecurity.Generation.RoundDescriptors
public import ZkcSecurity.Generation.SubjectABI

@[expose] public section

/-! Propose public reference tables from the admitted producer's def-use graph.
This is candidate discovery, not an equality or a dependency theorem. A helper
may transform its input: the generated execution and target proofs must still
establish the proposed reference. Unknown sources, private tables and ambiguous
dependencies stay unresolved. No source name or author-supplied offset selects
the candidate. The operand position is part of the installed table-round schema.
-/
set_option autoImplicit false
namespace ZkcSecurity.Generation.SumcheckInputs
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcSecurity.Families.Sumcheck

abbrev Dependencies := Option (List Nat)

def dependencies (environment : List Dependencies) (operands : List Nat) : Dependencies := do
  let inputs ← operands.mapM fun operand => environment[operand]?.join
  pure inputs.flatten.eraseDups

def extend (environment : List Dependencies) (instruction : Zkc.Construction.Instruction) : List Dependencies :=
  let result := match instruction.operation with
    | .calculate _ | .call _ | .indicesEmpty | .indicesAppend =>
        dependencies environment instruction.operands
    | _ => none
  environment ++ List.replicate instruction.results.length result

def tableInput (metadata : SubjectABI.Metadata) (producer : Participant)
    (loop : RoundDescriptor.Loop) : Except String Nat := do
  let some positions := metadata.producerPositions | throw "reference-input-no-producer-interface"
  let types ← SubjectABI.atPositions metadata.types positions
  if producer.inputs != types.map ValueSort.data ++ [.transcript metadata.suite] then
    throw "reference-input-producer-interface-mismatch"
  let initial := positions.map (fun position => some [position]) ++ [none]
  let environment := (producer.instructions.take loop.index).foldl extend initial
  let some table := loop.operands[1]? | throw "reference-input-no-table-operand"
  let some origins := environment[table]?.join | throw "reference-input-unknown-dependency"
  let candidates := origins.filter fun index =>
    match metadata.types[index]? with | some (.vector _) => true | _ => false
  let [candidate] := candidates | throw "reference-input-ambiguous-table"
  if !metadata.publicPositions.contains candidate then
    throw "reference-input-private-table-requires-residual-contract"
  pure candidate

def propose (metadata : SubjectABI.Metadata) (producer validator : Participant) :
    Except String (List Nat) := do
  let rounds ← RoundDescriptors.discover producer validator
  rounds.mapM fun round => tableInput metadata producer round.producer

end ZkcSecurity.Generation.SumcheckInputs
