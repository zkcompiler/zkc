import Tools.Interactive.Bindings
import Tools.Crypto.Keccak

/-! Independent finite Merkle row reference. Plain byte arrays and digest layers
are compared with Plonky3's packed tree. Successful authentication says nothing
about polynomial degree, extractability, hiding, or noninteractive security. -/
set_option autoImplicit false
namespace Tools.Interactive.OracleReference

inductive Domain where | base | extension deriving BEq, DecidableEq, Repr
def Domain.identity : Domain → String
  | .base => Bindings.rowBase | .extension => Bindings.rowExtension
def Domain.width : Domain → Nat | .base => 4 | .extension => 32
def Domain.codec : Domain → String
  | .base => "koala-bear.canonical-u32le/1"
  | .extension => "koala-bear.ext8-binomial3.ascending-u32le/1"
def Domain.parse (s : String) : Result Domain :=
  if s == Bindings.rowBase then .ok .base
  else if s == Bindings.rowExtension then .ok .extension
  else .error "oracle-domain"

private def little (width n : Nat) : ByteArray :=
  ByteArray.mk ((List.range width).map (fun i => UInt8.ofNat (n / 256^i % 256))).toArray
private def natural (bytes : ByteArray) : Nat := bytes.toList.foldr (fun b n => b.toNat+256*n) 0
private def zero : ByteArray := ByteArray.mk (Array.replicate 32 0)
private def magic : ByteArray := ByteArray.mk #[90,75,67,86,1]

def leaf (domain : Domain) (width height : Nat) (row : ByteArray) : ByteArray :=
  Tools.Crypto.Keccak.hash ("zkc.oracle.keccak256.leaf/1".toUTF8 ++ ByteArray.mk #[0] ++
    little 8 domain.codec.utf8ByteSize ++ domain.codec.toUTF8 ++ little 8 width ++ little 8 height ++ row)
def node (left right : ByteArray) : ByteArray :=
  Tools.Crypto.Keccak.hash ("zkc.oracle.keccak256.node/1".toUTF8 ++ ByteArray.mk #[0] ++ left ++ right)
def depth (height : Nat) : Nat := if height ≤ 1 then 0 else (height-1).log2+1

structure State where
  domain : Domain
  width : Nat
  height : Nat
  rows : Array ByteArray
  layers : Array (Array ByteArray)

def State.root (state : State) : ByteArray := (state.layers.back?.getD #[])[0]!

def commit (domain : Domain) (width : Nat) (vector : ByteArray) : Result State := do
  let tag := if domain == .base then 20 else 27
  ensure (vector.extract 0 6 == magic.push tag && vector.size ≥ 10) "wire-header"
  let count := natural (vector.extract 6 10)
  ensure (vector.size == 10+count*domain.width) "wire-length"
  ensure (width > 0 && count > 0 && count % width == 0) "oracle-shape"
  let height := count / width
  ensure (height ≤ 2^24) "oracle-shape"
  ensure (count ≤ 4096) "reference-oracle-work-limit"
  for i in [:count * (domain.width/4)] do
    ensure (natural (vector.extract (10+4*i) (14+4*i)) < Bindings.koalaBearModulus) "noncanonical-scalar"
  let rows := (List.range height).map fun i => vector.extract (10+i*width*domain.width) (10+(i+1)*width*domain.width)
  let mut current := (rows.map (leaf domain width height)).toArray
  for _ in [:2^(depth height)-height] do current := current.push zero
  let mut layers := #[current]
  for _ in [:depth height] do
    current := ((List.range (current.size/2)).map fun i => node current[2*i]! current[2*i+1]!).toArray
    layers := layers.push current
  return ⟨domain,width,height,rows.toArray,layers⟩

def State.open (state : State) (coordinate : Nat) : Result (ByteArray × List ByteArray) := do
  ensure (coordinate < state.height) "oracle-coordinate"
  let mut index := coordinate
  let mut path := []
  for layer in state.layers.toList.dropLast do
    path := path ++ [layer[index ^^^ 1]!]
    index := index/2
  let tag := if state.domain == .base then 20 else 27
  return (magic.push tag ++ little 4 state.width ++ state.rows[coordinate]!, path)

/-- Invalid expected coordinates refuse; false or malformed authentication is false. -/
def verify (domain : Domain) (root : ByteArray) (width height coordinate : Nat)
    (vector : ByteArray) (path : List ByteArray) : Result Bool := do
  ensure (width > 0 && height > 0 && height ≤ 2^24) "oracle-shape"
  ensure (width*height ≤ 2^20) "oracle-element-limit"
  ensure (coordinate < height) "oracle-coordinate"
  let tag := if domain == .base then 20 else 27
  ensure (vector.extract 0 6 == magic.push tag && vector.size ≥ 10) "wire-header"
  let count := natural (vector.extract 6 10)
  if count != width || vector.size != 10+width*domain.width || path.length != depth height then return false
  if root.size != 32 || path.any (·.size != 32) then return false
  let mut digest := leaf domain width height (vector.extract 10 vector.size)
  let mut index := coordinate
  for sibling in path do
    digest := if index % 2 == 0 then node digest sibling else node sibling digest
    index := index/2
  return digest == root

inductive Data where
  | root (domain : Domain) (digest : ByteArray)
  | path (domain : Domain) (digests : List ByteArray)
  | state (value : State)
  | roots (domain : Domain) (digests : List ByteArray)
  | states (domain : Domain) (values : List State)

def Data.domain : Data → Domain
  | .root d _ | .path d _ | .roots d _ | .states d _ => d
  | .state s => s.domain
def Data.kind : Data → String
  | .root .. => "commitment" | .path .. => "proof" | .state .. => "opening_state"
  | .roots .. => "commitments" | .states .. => "opening_states"
def Data.public : Data → Bool | .state .. | .states .. => false | _ => true
def Data.size : Data → Nat
  | .root _ b => b.size
  | .path _ bs | .roots _ bs => 1+(bs.map ByteArray.size).sum
  | .state s => 1+s.height*(s.width*s.domain.width+64)
  | .states _ ss => 1+(ss.map fun s => 1+s.height*(s.width*s.domain.width+64)).sum

private def tag (domain : Domain) (kind : String) : Result UInt8 :=
  match domain, kind with
  | .base, "commitment" => .ok 33 | .base, "proof" => .ok 34
  | .extension, "commitment" => .ok 35 | .extension, "proof" => .ok 36
  | .base, "commitments" => .ok 37 | .extension, "commitments" => .ok 38
  | _, _ => .error "nonserializable"

def Data.wire (value : Data) : Result ByteArray := do
  let header := magic.push (← tag value.domain value.kind)
  let (single, hashes) ← match value with
    | .root _ digest => pure (true, [digest])
    | .path _ ds | .roots _ ds => pure (false, ds)
    | _ => throw "nonserializable"
  ensure (hashes.all (·.size == 32)) "wire-length"
  ensure (hashes.length ≤ 2^20) "oracle-element-limit"
  if value.kind == "proof" then ensure (hashes.length ≤ 24) "oracle-path-length"
  return (if single then header else header ++ little 4 hashes.length) ++
    hashes.foldl (· ++ ·) ByteArray.empty

def decode (domain : Domain) (kind : String) (wire : ByteArray) : Result Data := do
  ensure (wire.extract 0 6 == magic.push (← tag domain kind)) "wire-header"
  let single := kind == "commitment"
  let offset := if single then 6 else 10
  ensure (wire.size ≥ offset) "wire-length"
  let count := if single then 1 else natural (wire.extract 6 10)
  ensure (wire.size == offset+32*count) "wire-length"
  ensure (count ≤ 2^20) "oracle-element-limit"
  if kind == "proof" then ensure (count ≤ 24) "oracle-path-length"
  let hashes := (List.range count).map fun i => wire.extract (offset+32*i) (offset+32*(i+1))
  if single then return .root domain (hashes.headD ByteArray.empty)
  return if kind == "proof" then .path domain hashes else .roots domain hashes
end Tools.Interactive.OracleReference
