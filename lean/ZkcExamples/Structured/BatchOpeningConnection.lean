module

public import ZkcExamples.Construction.BatchOpening
public import Zkc.Protocols.TableMembership.BatchProtocolInstallation
public import Zkc.Source.Structured.BodyBindings
public meta import ZkcTools.StructuredSource.Association

@[expose] public section

/-! Exact installation of reusable batch laws on the retained BatchOpening
source. Nominal identities, helper dependencies, role scopes and both outputs
are checked against admission; the generated bodies remain generator-owned.
These records assert point/value equality, without a PCS security claim. -/
namespace ZkcExamples.Structured.BatchOpeningConnection
open Zkc.Source Zkc.Source.Structured
open Zkc.Protocols.TableMembership

abbrev names : Zkc.Protocols.TableMembership.BatchSource.Names where
  checkOpening := "zkl_b26f24aff1f462f4c3e9ea4c594fd6eaaac4e0d13a163302bc46f14e913cc892"
  batchStep := "finite_zkl_040b90e6fc9f7c074519f3a904772619b0e3c63ed7b7a051cbc3db4b3c514ff3_s3_body"
  batchValues := "zkl_040b90e6fc9f7c074519f3a904772619b0e3c63ed7b7a051cbc3db4b3c514ff3"
  formula := "zkf_53219b51c062230506c8b229ef72062dff0e276e6336e241e0b2d30a9a6fe712"
  mathematicalAdmission := "_mathematical_admission_0"
  checkBatch := "zkl_765e0fbfb20c4afe7930d2c0cbb531d52446ae1c25c74ad1237691d8738b0a85"
  batchDomain := "finite_zkl_040b90e6fc9f7c074519f3a904772619b0e3c63ed7b7a051cbc3db4b3c514ff3_s3_domain"
  openingName := "[\"zkc.language.pack\",\"373a303a32323a62617463685f6f70656e696e673a3a4f70656e696e67313a30313a32323a313a303a31303a6b6f616c612d62656172313a30303a\"]"
  openingConstructor := "case00000000"
  checkSite := "s0"

abbrev protocolNames : Zkc.Protocols.TableMembership.BatchSource.ProtocolNames where
  name := "zkl_206d594942dc6f123848ad35c8fcdc7017b483db9ccd5c0651d1ad5c850eceab"
  producerRole := "role00000000"
  validatorRole := "role00000001"
  messageSite := "label_6261746368_0"
  checkSite := "s2"

/-- All six exact helper bodies are checked against the reusable family. -/
theorem installedBodies : BatchSource.Bodies
    ZkcExamples.Construction.BatchOpening.unit.definitions "koala-bear" names := by
  bind_structured_bodies

/-- The complete retained protocol is an instance of the reusable source body. -/
def source : Template.Association ZkcExamples.Construction.BatchOpening.unit
    (BatchSource.runSignature "koala-bear" names protocolNames)
    (BatchSource.runBody "koala-bear" names protocolNames) := by
  derive_source_association

end ZkcExamples.Structured.BatchOpeningConnection
