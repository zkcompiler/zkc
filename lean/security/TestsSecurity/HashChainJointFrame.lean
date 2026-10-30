import ZkcSecurity.Transformations.HashChain.JointOpening
import ZkcTools.DeclarationAudit

/-! Controls for the hash-chain frame of a verifier with committed tables.

**Namespace separation needs the tags** (`prefixTag_collides`). The joint frame's namespaces are
proved separated from bytes (`ZkcSecurity.HashChain.Joint.TaggedRows.separated`) because the row
tags and the chain tags are pairwise non-prefix. A leaf tag that is a proper prefix of the chain's
binding tag fails that condition (`prefixTag_not_separated`), and then the leaf call of a row whose
bytes are an event's encoding, under a header that completes the binding tag, has exactly the bytes
of the binding of that event: the joint encoding is not injective, so no `Encoding` exists for it.
The installed Keccak-256 tags are separated (`ZkcSecurity.HashChain.Joint.keccak_tagsSeparated`).

**The Keccak theorem is not vacuous** (`byteRows_soundness`). Its premises are satisfiable: with
one-byte rows (a fixed-length injective codec), the committed-opening verifier over the Keccak hash
chain has the stated bound for every adversary within its calls, at every depth up to 256.

**Budgets** (`provider_budget_total`). The provider stage transports an adversary's budget to its
total number of byte-hash calls, the budget at which the commitment stage's loss is evaluated. -/

namespace TestsSecurity.HashChainJointFrame
open OracleComp OracleSpec ZkcSecurity.Commitment ZkcSecurity.HashChain ZkcSecurity.HashChain.Encoding
  ZkcSecurity.HashChain.Joint ZkcSecurity.Examples.CommittedOpeningBridge

section Prefix

/-- A leaf tag that is a proper prefix of the chain's binding tag. -/
def prefixTag : Bytes := ascii "zkc.hash-chain."

/-- The rest of the binding tag after the prefix, as a leaf header. -/
def prefixHeader : Bytes := ascii "bind/0" ++ [0]

theorem prefixTag_header : prefixTag ++ prefixHeader = bindTag := by
  decide

/-- The prefix tag is not separated from the chain tags. -/
theorem prefixTag_not_separated : ¬ TagsSeparated prefixTag keccakNodeTag := by
  decide

/-- The absorbed events of a chain with one base event, one shape and one state. -/
abbrev UnitEvent := Absorbed Unit Unit Unit

/-- An injective encoding of the unit chain's events. -/
def unitEventBytes : UnitEvent → Bytes
  | .event () => [0]
  | .root () () => [1]

theorem unitEventBytes_injective : Function.Injective unitEventBytes := by
  intro first second same
  cases first with
  | event event =>
      cases event
      cases second with
      | event other => cases other; rfl
      | root shape root =>
          cases shape
          cases root
          exact absurd same (by decide)
  | root shape root =>
      cases shape
      cases root
      cases second with
      | event other =>
          cases other
          exact absurd same (by decide)
      | root shape' root' =>
          cases shape'
          cases root'
          rfl

/-- With the prefix tag, a leaf call whose row bytes are an event's encoding collides with the
binding of that event, so row calls and chain calls are not jointly injective. -/
theorem prefixTag_collides :
    ¬ Function.Injective (Sum.elim
      (taggedCallBytes prefixTag keccakNodeTag prefixHeader unitEventBytes (fun _ : Unit => ([] : Bytes)))
      fun call : ChainCall Unit Unit Unit =>
        encodeInput (fun _ : Unit => ([] : Bytes)) unitEventBytes call.val) := by
  intro injective
  have collision := @injective (.inl (.leaf (.event ()))) (.inr ⟨.bind (.event ()), trivial⟩) (by
    simp only [Sum.elim_inl, Sum.elim_inr, taggedCallBytes, encodeInput]
    rw [prefixTag_header])
  cases collision

end Prefix

section Instance

theorem byteRows_injective : Function.Injective fun row : UInt8 => ([row] : Bytes) :=
  fun _ _ same => List.singleton_inj.mp same

/-- The committed-opening verifier over the Keccak hash chain with one-byte rows: the premises of
`ZkcSecurity.HashChain.Joint.keccak_soundness` are satisfiable, and its bound holds. -/
theorem byteRows_soundness (depth : ℕ) (fits : depth ≤ 256) (accepts : UInt8 → Bool)
    (fraction : ENNReal)
    (adversary : OracleComp (ByteHash KeccakDigest)
      (KeccakDigest × Proof (List UInt8) UInt8 KeccakDigest))
    {calls : ℕ} (bounded : IsTotalQueryBound adversary calls) :
    concreteFailure (keccakEncoding (ascii "u8") 1 (2 ^ depth) (fun row : UInt8 => ([row] : Bytes))
        Nat.one_pos (fun _ => rfl) byteRows_injective)
        1 (chainAbsorb depth 1 (keccakIndex depth fits)) (scheme (rowHashing UInt8 KeccakDigest) depth)
        (words depth 0) (fun _ : KeccakDigest => validator accepts depth) initial
        (fun root => [((), root)]) (FalseTable accepts depth fraction 0) (· = true) adversary () ≤
      (((calls + (depth + 4)) * (calls + (depth + 4)) : ℕ) : ENNReal) / 2 ^ 256 +
        (calls * ((1 - fraction) + keccakHash depth calls) +
          ((1 - fraction) + ((depth + 1 : ℕ) : ENNReal) * keccakHash depth calls)) :=
  keccak_soundness (ascii "u8") 1 (2 ^ depth) (fun row : UInt8 => ([row] : Bytes)) Nat.one_pos
    (fun _ => rfl) byteRows_injective depth fits accepts fraction 0 adversary bounded

/-- The provider stage transports a budget to the adversary's total number of byte-hash calls. -/
theorem provider_budget_total (depth : ℕ) (fits : depth ≤ 256) (accepts : UInt8 → Bool)
    (fraction : ENNReal) (budget : ZkcSecurity.FiatShamir.Provider.Budget Unit) :
    (contract (keccakEncoding (ascii "u8") 1 (2 ^ depth) (fun row : UInt8 => ([row] : Bytes))
        Nat.one_pos (fun _ => rfl) byteRows_injective)
      1 (chainAbsorb depth 1 (keccakIndex depth fits)) (scheme (rowHashing UInt8 KeccakDigest) depth)
      (words depth 0) (fun _ : KeccakDigest => validator accepts depth) initial
      (fun root => [((), root)]) (FalseTable accepts depth fraction 0) (· = true) Nat.one_pos
      (by norm_num) (fun _ => List.cons_ne_nil _ _) (1 + depth + 3)
      (deployed_queryBound depth 1 (keccakIndex depth fits) _ accepts)
      (jointReading_queryBound depth 1 (keccakIndex depth fits) accepts)).provider.budget budget =
        budget () :=
  rfl

end Instance

end TestsSecurity.HashChainJointFrame

run_cmd ZkcTools.DeclarationAudit.checkCurrent "HASH-CHAIN-JOINT-FRAME-AXIOM-PASS"
