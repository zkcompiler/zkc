import Tools.Interactive.ReferenceState

/-! Independent external data-state transition interpreter. The ONLY trusted
service replies are Hs(bytes) and the 16-word Poseidon2 permutation. Scheduling,
canonical admission, overwrite absorption, reverse sampling, bit masking and
witness checks are computed here, including failed-check successors. No crypto
implementation or full proof-security theorem is claimed. -/
set_option autoImplicit false
namespace Tools.Interactive.Reference.External
open Lean (Json)

def magic : Nat := 1514881876
def modulus : Nat := 2013265921
private def scalarOrder : Nat := 7237005577332262213973186563042994240857116359379907606001950938285454250989
private def numbers (ns : List Nat) : Json := .arr (ns.map (Json.str ∘ toString)).toArray
private def indices (ns : List Nat) : Value := Value.fromArithmetic .bls (.indices ns)
private def getIndices (location : Location) (v : Value) : RunM (List Nat) := do
  let .indices ns ← checked location (v.toArithmetic .bls)
    | failAt location "refused" "external-operands"
  require location (ns.all (· < 2^64)) "external-u64"
  return ns
private def getIndex (location : Location) (v : Value) : RunM Nat := do
  let .index n ← checked location (v.toArithmetic .bls)
    | failAt location "refused" "external-operands"
  require location (n < 2^32) "external-u32"
  return n
private def bytes (location : Location) (ns : List Nat) : RunM Unit :=
  require location (ns.all (· < 256)) "external-byte"
private def fields (location : Location) (ns : List Nat) : RunM Unit :=
  require location (ns.all (· < modulus)) "external-noncanonical-field"
private def payload (location : Location) (v : Value) (suite width : Nat) : RunM (List Nat) := do
  let ns ← getIndices location v
  require location (ns.length == width + 3) "external-state-width"
  require location (ns.take 3 == [magic, 1, suite]) "external-state-suite"
  return ns.drop 3
private def packed (suite : Nat) (ns : List Nat) : Value := indices ([magic, 1, suite] ++ ns)

/-- Exact input and primitive version are part of the request. Replies are
explicit trusted assumptions, never an oracle for the whole transition. -/
private def primitive (location : Location) (name : String) (input : List Nat) : RunM (List Nat) := do
  let reply ← successfulReply location (← oracle location
    (.arr #[.str "zkc.external-primitive/1", location.json, .str name, numbers input]))
  let values ← checked location (Decode.array reply)
  checked location (values.mapM Decode.natural)
private def hash (location : Location) (input : List Nat) : RunM (List Nat) := do
  bytes location input
  let out ← primitive location "monero.v0.18.5.1.keccak256.reduce32" input
  require location (out.length == 32) "external-word-width"
  bytes location out
  let value := out.foldr (fun b n => b + 256*n) 0
  require location (value < scalarOrder) "external-noncanonical-scalar"
  return out

structure Duplex where
  state : List Nat
  absorb : Nat
  sample : Nat
private def unpack (location : Location) (v : Value) : RunM Duplex := do
  let ns ← payload location v 2 18
  fields location (ns.take 16)
  let a := ns[16]!
  let s := ns[17]!
  require location (a < 8 && s ≤ 8) "external-state-index"
  return ⟨ns.take 16, a, s⟩
private def pack (d : Duplex) : Value := packed 2 (d.state ++ [d.absorb, d.sample])
private def permute (location : Location) (d : Duplex) : RunM Duplex := do
  let out ← primitive location "openvm.stark-backend.v2.0.1.poseidon2.babybear.0.4.3" d.state
  require location (out.length == 16) "external-state-width"
  fields location out
  return ⟨out, 0, 8⟩
private def observe (location : Location) (d : Duplex) (xs : List Nat) : RunM Duplex := do
  fields location xs
  xs.foldlM (fun d x => do
    let next := { d with state := d.state.set d.absorb x, absorb := d.absorb + 1 }
    if next.absorb == 8 then permute location next else pure next) d
private def sample (location : Location) (d : Duplex) : RunM (Duplex × Nat) := do
  let d ← if d.absorb != 0 || d.sample == 0 then permute location d else pure d
  let next := { d with sample := d.sample - 1 }
  return (next, next.state[next.sample]!)
private def bits (location : Location) (v : Value) : RunM Nat := do
  let n ← getIndex location v
  require location (n ≤ 30) "external-invalid-bit-width"
  return n

def compute (location : Location) (contract : String) (inputs : List Value) : RunM (List Value) := do
  match contract, inputs with
  | "external.monero.init", [input] =>
      let ns ← getIndices location input
      require location (ns.length == 32) "external-word-width"
      bytes location ns
      return [packed 1 ns]
  | "external.monero.hash", [input] =>
      let ns ← getIndices location input
      require location (ns.length % 32 == 0) "external-word-width"
      return [indices (← hash location ns)]
  | "external.monero.update", [state, input] =>
      let st ← payload location state 1 32
      bytes location st
      let ns ← getIndices location input
      require location (ns.length % 32 == 0) "external-word-width"
      let out ← hash location (st ++ ns)
      return [packed 1 out, indices out]
  | "external.openvm.init", [] => return [pack ⟨List.replicate 16 0, 0, 0⟩]
  | "external.openvm.observe", [state, input] =>
      return [pack (← observe location (← unpack location state) (← getIndices location input))]
  | "external.openvm.sample", [state] =>
      let (d, x) ← sample location (← unpack location state)
      return [pack d, Value.fromArithmetic .bls (.index x)]
  | "external.openvm.sample_ext", [state] =>
      let mut d ← unpack location state
      let mut xs := []
      for _ in [:4] do
        let (next, x) ← sample location d
        d := next
        xs := xs ++ [x]
      return [pack d, indices xs]
  | "external.openvm.sample_bits", [state, width] =>
      let d ← unpack location state
      let b ← bits location width
      let (d, x) ← sample location d
      return [pack d, Value.fromArithmetic .bls (.index (x % 2^b))]
  | "external.openvm.check_witness", [state, width, witness] =>
      let d ← unpack location state
      let b ← bits location width
      let w ← getIndex location witness
      fields location [w]
      if b == 0 then return [pack d, .boolean true]
      let (d, x) ← sample location (← observe location d [w])
      return [pack d, .boolean (x % 2^b == 0)]
  | _, _ => failAt location "refused" "external-operands"
end Tools.Interactive.Reference.External
