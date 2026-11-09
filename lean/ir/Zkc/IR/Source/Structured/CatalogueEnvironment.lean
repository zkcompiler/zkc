module

public import Zkc.IR.Source.Structured.InstalledCatalogue

@[expose] public section

/-! The environment catalogues: the installed rows the Lean readers admit.

The rows themselves are the generated installed rows (`Installed`), so their
identities, members, capability facts in native order, characteristics and
service methods are the catalog's. This module only selects which identities
each reader admits, and the sort instances of the structured profile; that
selection is the formal support boundary. -/

set_option autoImplicit false
namespace Zkc.Source.Structured

/-! The BLS12-381 environment: the rows of the scalar field, its pairing groups
and the random service, and the sort instances the structured profile admits. -/

def blsScalar : String := "bls12-381.fr"
def blsGroup : String := "bls12-381.g1"
def blsGroupTwo : String := "bls12-381.g2"
def blsTarget : String := "bls12-381.gt"
def blsRandom : String := "random.bls12-381.fr/0"
def blsModulus : Nat := Installed.Characteristics.«bls12-381.fr»

def blsCatalogue : Catalogue where
  nominals := [Installed.Domains.«bls12-381.fr», Installed.Domains.«bls12-381.g1»,
    Installed.Domains.«bls12-381.g2», Installed.Domains.«bls12-381.gt»]
  services := [Installed.Services.«random.bls12-381.fr/0»]
  types := [("field", blsScalar), ("vector", blsScalar), ("group", blsGroup)]

/-- The KoalaBear rows: the prime field and its octic extension, which share
the characteristic, and the octic random service. Carrier cardinalities belong
to the selected model. -/
def koalaBearCatalogue : Catalogue where
  nominals := [Installed.Domains.«koala-bear», Installed.Domains.«koala-bear.ext8-binomial3»]
  services := [Installed.Services.«random.koala-bear.ext8-binomial3/0»]
  types := [("field", "koala-bear"), ("vector", "koala-bear"),
    ("field", "koala-bear.ext8-binomial3"), ("vector", "koala-bear.ext8-binomial3")]

/-- The KoalaBear quartic extension row, with its base-field association.
Admission recognizes this exact nominal identity; the field laws of its carrier,
its extension presentation and any concrete realization remain explicit
premises of the model that interprets it. It shares the characteristic of the
octic extension but neither its cardinality nor its representation, and its
random service is admitted for its separately checked scalar and block index operations. -/
def koalaBearQuarticCatalogue : Catalogue where
  nominals := [Installed.Domains.«koala-bear.ext4-binomial3»]
  services := [Installed.Services.«random.koala-bear.ext4-binomial3/0»]
  types := [("field", "koala-bear.ext4-binomial3"), ("vector", "koala-bear.ext4-binomial3")]

/-- Installed binary field identities, with their exact polynomial presentations.
Their concrete carriers, bit-basis laws and executable codecs remain model obligations. -/
def binaryCatalogue : Catalogue where
  nominals := [Installed.Domains.«gf2-64.pentanomial-4-3-1»,
    Installed.Domains.«gf2-64.pentanomial-4-3-1.ext3-trinomial1»]
  services := []
  types := [("field", "gf2-64.pentanomial-4-3-1"),
    ("vector", "gf2-64.pentanomial-4-3-1"),
    ("field", "gf2-64.pentanomial-4-3-1.ext3-trinomial1"),
    ("vector", "gf2-64.pentanomial-4-3-1.ext3-trinomial1")]

/-- The rows understood by the structured importer. Admission of a row or type
is separate from operation support and mathematical law evidence. -/
def admittedCatalogue : Catalogue where
  nominals := blsCatalogue.nominals ++ koalaBearCatalogue.nominals ++ koalaBearQuarticCatalogue.nominals ++ binaryCatalogue.nominals
  services := blsCatalogue.services ++ koalaBearCatalogue.services ++ koalaBearQuarticCatalogue.services
  types := blsCatalogue.types ++ koalaBearCatalogue.types ++ koalaBearQuarticCatalogue.types ++
    binaryCatalogue.types ++
    (blsCatalogue.types ++ koalaBearCatalogue.types ++ koalaBearQuarticCatalogue.types ++
      binaryCatalogue.types).filterMap
      (fun (kind, domain) ↦ if kind == "field" then some ("polynomial", domain) else none)

/-- The transcript suites whose challenges constructed participants draw. These
rows are metadata: the sponge, encoding and decoder of a suite belong to the
model that interprets it. -/
def transcriptCatalogue : Catalogue where
  nominals := [Installed.Domains.«merlin3.bls12-381.fr64be/0»,
    Installed.Domains.«merlin3.koala-bear.ext8-binomial3.rejection31le/0»,
    Installed.Domains.«hash-chain.keccak256.koala-bear.ext8-binomial3.rejection31le/0»,
    Installed.Domains.«hash-chain.keccak256.koala-bear.ext4-binomial3.rejection31le/0»]
  services := []

/-- The rows understood by the constructed-participant reader: the structured
importer's rows and admitted instances, and the transcript suites. Structured
units name no transcript, so their importer keeps `admittedCatalogue`. -/
def constructionCatalogue : Catalogue where
  nominals := admittedCatalogue.nominals ++ transcriptCatalogue.nominals
  services := admittedCatalogue.services
  types := admittedCatalogue.types

/-- The rows a unit over this environment exports when it lists every row:
the environment's nominal and service rows, without its admitted instances. -/
def blsRows : Catalogue where
  nominals := blsCatalogue.nominals
  services := blsCatalogue.services

end Zkc.Source.Structured
