import Zkc.Source.Mathematical.DeclarationAdmission
import Tests.Checks

set_option autoImplicit false
namespace Tests.MathematicalDeclarations
open Zkc.Source.Mathematical
open ManifestAdmission RegistryAdmission

-- SHA-256 of the exact ASCII descriptors, without a trailing newline.
-- These finite test contracts are installed here; the digests supply no laws.
-- test.math.scalar/v1:nominal=test-scalar:Fin7
def scalar : Raw.Identity := ⟨"test.math.scalar", "1", "dd9bb35263c600af083112e7fe79cc7d34bc7851b9e8568796eed6ad4f065d25"⟩
-- test.math.service/v1:statics=n:Vec(Fin2,n)->Fin2:ordered
def service : Raw.Identity := ⟨"test.math.service", "1", "632578cb3fd9832007ca9fc6bb0655ab81af2144f48e9462d20d3d3b8e43d23e"⟩
-- test.math.wire/v1:statics=n:Vec(Fin2,n)
def wire : Raw.Identity := ⟨"test.math.wire", "1", "8d09c5bfc5e740fe4cee1805643abcaa5e4596dc0f37da974208c54391c07503"⟩
-- test.math.copy/v1:Fin2->Fin2:total
def copy : Raw.Identity := ⟨"test.math.copy", "1", "eb568c53e02a6af6336524c5f38f39c93572f6ed83dff0ee3be802c64220a490"⟩
-- test.math.gated/v1:statics=n:Vec(Fin2,n)->Fin2:service=service(n):ordered
def gated : Raw.Identity := ⟨"test.math.gated", "1", "c9cf7cf3697574c5acd7f62e34f1d2de5e40656a0cb7ecf8f0e612b5f0ce68f9"⟩
-- test.math.paired/v1:statics=n:Vec(Fin2,n)->Fin2:services=service(n),service(n):ordered:distinct=0,1
def paired : Raw.Identity := ⟨"test.math.paired", "1", "c3e4b99ff30236ecbfe9576abc261d2396d5b8f437e0897ba67b6b7319ab2c85"⟩

inductive Op where
  | copy | gated | paired

def Payload : Category → Type
  | .operation => Op
  | _ => Unit

def installation : Installation Payload
  | .domain => ⟨[⟨scalar, (), []⟩], by simp⟩
  | .service => ⟨[⟨service, (), []⟩], by simp⟩
  | .wire => ⟨[⟨wire, (), []⟩], by simp⟩
  | .operation => ⟨[⟨copy, .copy, []⟩, ⟨gated, .gated, [⟨.service, service⟩]⟩,
      ⟨paired, .paired, [⟨.service, service⟩]⟩], by decide⟩
  | .law => ⟨[], by simp⟩

def boolean {domains target : Nat} : TypeExpansion.Shape domains target := .fin (.literal ⟨2, by decide⟩)

def serviceSignature {domains target : Nat} (count : Static.Expression target) :
    SignatureAdmission.ServiceSignature domains target := ⟨service, [count], [.vector boolean count], boolean⟩

def operationContract {domains target : Nat} (code : Op)
    (signature : SignatureAdmission.OperationSignature domains target) : Option OperationFacts :=
  match code with
  | .copy =>
      if signature = ⟨copy, [], [], [boolean], boolean⟩ then some ⟨.total, []⟩ else none
  | .gated | .paired =>
      match signature.statics with
      | [count] =>
          let (identity, services, distinct) := match code with
            | .gated => (gated, [serviceSignature count], [])
            | .paired => (paired, [serviceSignature count, serviceSignature count], [(0, 1)])
            | .copy => (copy, [], [])
          if signature = ⟨identity, [count], services, [.vector boolean count], boolean⟩ then
            some ⟨.ordered, distinct⟩
          else none
      | _ => none

def contracts : Contracts Payload where
  installation := installation
  nominal := fun _ _ _ => Fin 7
  polynomial := fun _ _ _ _ => PUnit
  residual := fun _ _ _ => PUnit
  domain := fun _ _ atom => match atom with
    | .nominal _ name arguments => name == "test-scalar" && arguments.isEmpty
    | _ => false
  service := fun _ _ signature => match signature.statics with
    | [count] => decide (signature = serviceSignature count)
    | _ => false
  operation := fun _ => operationContract
  wire := fun _ _ statics payload => match statics with
    | [count] => decide (payload = .vector boolean count)
    | _ => false
  attributes := fun _ _ _ value => match value with
    | .object [] => true
    | _ => false

def booleanUse : Raw.TypeUse := ⟨⟨0⟩, []⟩
def vectorUse : Raw.TypeUse := ⟨⟨1⟩, [.parameter 0]⟩
def capabilityUse : Raw.CapabilityUse := ⟨⟨0⟩, [.parameter 0]⟩

def module : Raw.Module :=
  ⟨["prover", "verifier"],
   [⟨0, .fin (.literal 2)⟩, ⟨1, .vector booleanUse (.parameter 0)⟩,
     ⟨0, .nominal ⟨0⟩ "test-scalar" []⟩],
   [⟨⟨0⟩, 0, [], [booleanUse], booleanUse, .total, []⟩,
     ⟨⟨1⟩, 1, [capabilityUse], [vectorUse], booleanUse, .ordered, []⟩,
     ⟨⟨2⟩, 1, [capabilityUse, capabilityUse], [vectorUse], booleanUse, .ordered, [(0, 1)]⟩],
   [⟨⟨0⟩, 1, vectorUse⟩], [⟨⟨0⟩, 1, [vectorUse], booleanUse⟩],
   [⟨⟨⟨0⟩, [.literal 3]⟩, [⟨0⟩, ⟨1⟩]⟩], [], [], ⟨⟨0⟩, [], [], []⟩⟩

def subject : Raw.Subject := ⟨⟨[scalar], [copy, gated, paired], [wire], [service], []⟩, module⟩

def admit (source : Raw.Subject := subject) (registry : Contracts Payload := contracts) (budget : Nat := 1000000) :=
  (DeclarationAdmission.admit registry source).run' budget

def refuses (source : Raw.Subject) (reason : DeclarationAdmission.Error) (registry : Contracts Payload := contracts) : Bool :=
  match admit source registry with
  | .error error => error == reason
  | .ok _ => false

def modifyOperation (index : Nat) (change : Raw.Operation → Raw.Operation) : Raw.Subject :=
  { subject with module.operations := module.operations.modify index change }

def attributeCheck (value : Raw.Attribute) : Except DeclarationAdmission.Error Bool :=
  (show DeclarationAdmission.Admission Bool from do
    let header ← DeclarationAdmission.admit contracts subject
    let operation := header.operations.get .here
    let _ ← fun remaining => (RegistryAdmission.attributes header.context header.types operation.registered value remaining)
      |>.mapError DeclarationAdmission.Error.registry
    return true).run' 1000000

-- The certificate connects every type leaf to the same installed domain
-- checker used by the admitted module, and every operation to its exact
-- authored-index manifest selection. These statements do not reduce a test.
example {source : Raw.Subject} (header : DeclarationAdmission.Header contracts source) :
    @header.types.domainCheck = @header.context.domainCheck := header.domains

example {source : Raw.Subject} (header : DeclarationAdmission.Header contracts source)
    {index : Nat} (operation : DeclarationAdmission.Operation header.context source.module header.types index) :
    operation.registered.selected.package.identity = operation.signature.identity.value :=
  operation.registered.selected.exactIdentity

def run : IO Unit := do
  let checks ← Checks.start
  checks.holds (admit).isOk "complete symbolic header and closed roots"
  checks.holds (refuses (modifyOperation 1 fun operation => { operation with purity := .total }) (.registry .operation))
    "authored totality cannot replace installed ordering"
  checks.holds (refuses (modifyOperation 2 fun operation => { operation with distinct := [] }) (.registry .operation))
    "authored declaration cannot drop root distinctness"
  checks.holds (refuses (modifyOperation 0 fun operation => { operation with result := ⟨⟨2⟩, []⟩ })
    (.registry .operation)) "well-formed replacement result is not the installed operation signature"
  checks.holds (refuses { subject with module.roles := ["prover", "prover"] } .roles) "duplicate module roles"
  checks.holds (!(admit { subject with module.roots := [⟨⟨⟨0⟩, [.add (.literal 1) (.literal 2)]⟩, [⟨0⟩]⟩] }).isOk)
    "root arguments must be authored literals"
  checks.holds (refuses { subject with module.roots := [⟨⟨⟨0⟩, [.parameter 0]⟩, [⟨0⟩]⟩] } .rootStatic)
    "root cannot refer to a static parameter"
  checks.holds (refuses { subject with module.roots := [⟨⟨⟨0⟩, [.literal 3]⟩, [⟨1⟩, ⟨0⟩]⟩] } (.port .role))
    "root permissions are canonical"
  checks.holds (refuses { subject with module.roots := [⟨⟨⟨0⟩, [.literal 3]⟩, [⟨2⟩]⟩] } (.port .role))
    "root permissions stay in module scope"
  checks.holds (refuses subject (.registry .service) { contracts with service := fun _ _ _ => false })
    "unused service declarations still require registered signatures"
  checks.holds (refuses subject (.registry .wire) { contracts with wire := fun _ _ _ _ => false })
    "unused wires still require registered signatures"
  checks.holds (refuses (modifyOperation 2 fun operation => { operation with distinct := [(0, 2)] }) (.registry .distinct)
    { contracts with operation := fun source code signature =>
      (contracts.operation source code signature).map fun facts => match code with
        | .paired => { facts with distinct := [(0, 2)] }
        | _ => facts }) "malformed installed distinct pair remains invalid"
  checks.holds (refuses (modifyOperation 1 fun operation => { operation with purity := .total }) (.registry .purity)
    { contracts with operation := fun source code signature =>
      (contracts.operation source code signature).map fun facts => match code with
        | .gated => { facts with purity := .total }
        | _ => facts }) "total operations cannot take capabilities even when a registry claims they can"
  checks.holds (!(admit { subject with module.types := module.types ++ [⟨0, .nominal ⟨0⟩ "unregistered" []⟩] }).isOk)
    "unused nominal type uses the selected domain checker"
  checks.holds ((attributeCheck (.object [])).isOk) "valid operation attributes"
  checks.holds (!(attributeCheck (.object [("unexpected", .natural 1)])).isOk) "invalid operation attributes"
  checks.holds (!(admit subject contracts 0).isOk) "header shares the work allowance"
  checks.finish "mathematical registered declarations"

#eval run
end Tests.MathematicalDeclarations
