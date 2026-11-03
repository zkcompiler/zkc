#ifndef ZKC_CONTRACT_DECLARATION_SCHEMA
#define ZKC_CONTRACT_DECLARATION_SCHEMA
// Neutral logical declarations. This file deliberately has no MLIR includes.
// Common membership for explicit build-time contribution sets.
class ZKC_Declaration;
class ZKC_Contribution<string id, list<string> dependencies,
                       list<ZKC_Declaration> records> {
  string identifier = id;
  list<string> requires = dependencies;
  list<ZKC_Declaration> declarations = records;
}
// A logical type head the source language owns that is not a catalog type
// constructor: its spelling and the form, the logical meaning the frontend
// gives it. A frontend home may name one.
class ZKC_FrontendConstructor<string value, string meaning> : ZKC_Declaration {
  string name = value;
  string form = meaning;
}
class ZKC_FrontendHome<string head, string owner, list<string> exports = []> : ZKC_Declaration {
  string name = head;
  string module = owner;
  list<string> members = exports;
}
class ZKC_ServiceMethod<string value, string rule, string requirement>
    : ZKC_Declaration {
  string name = value;
  string signature = rule;
  string capability = requirement;
}
class ZKC_ParameterKind<string value> : ZKC_Declaration { string name = value; }
def DomainKind : ZKC_ParameterKind<"Domain">;
def TypeKind : ZKC_ParameterKind<"Type">;
def NatKind : ZKC_ParameterKind<"Nat">;
class ZKC_Sort<string value> : ZKC_Declaration { string name = value; }
class ZKC_Parameter<ZKC_ParameterKind k, string s = ""> : ZKC_Declaration {
  ZKC_ParameterKind kind = k;
  string sort = s;
}
class ZKC_Domain<ZKC_Sort s> : ZKC_Parameter<DomainKind, s.name>;
def TypeParameter : ZKC_Parameter<TypeKind>;
def NatParameter : ZKC_Parameter<NatKind>;
// Installed source declarations, their elaboration rules and notations grant
// source resolution and elaboration facts. They never grant execution
// authority, physical installation or formal laws.
// A source type: static parameter `index` or its associated `member`, or with
// index -1 the parameterless `constructor`.
class ZKC_SourceTerm<int position, string associated = "", string head = "">
    : ZKC_Declaration {
  int index = position;
  string member = associated;
  string constructor = head;
}
class ZKC_SourceStatic<string value, ZKC_Parameter p> : ZKC_Declaration {
  string name = value;
  ZKC_Parameter parameter = p;
}
class ZKC_SourceInput<string value, ZKC_SourceTerm t> : ZKC_Declaration {
  string name = value;
  ZKC_SourceTerm type = t;
}
// The declared shape a rule association requires. `output` has at most one
// term; an interface has none.
class ZKC_FrontendRule<string value, string declared, list<ZKC_Parameter> s,
                       list<ZKC_SourceTerm> i, list<ZKC_SourceTerm> o>
    : ZKC_Declaration {
  string name = value;
  string kind = declared;
  list<ZKC_Parameter> statics = s;
  list<ZKC_SourceTerm> inputs = i;
  list<ZKC_SourceTerm> output = o;
}
// One installed declaration with exactly one association: a `primitive`
// mathematical intrinsic or operation, or a `rule`.
class ZKC_FrontendDeclaration<string id, string owner, string value,
                              string declared, list<ZKC_SourceStatic> s,
                              list<ZKC_SourceInput> i, list<ZKC_SourceTerm> o,
                              string associationKind, string associated,
                              bit fallback> : ZKC_Declaration {
  string identity = id;
  string module = owner;
  string name = value;
  string kind = declared;
  list<ZKC_SourceStatic> statics = s;
  list<ZKC_SourceInput> inputs = i;
  list<ZKC_SourceTerm> output = o;
  string association = associationKind;
  string target = associated;
  bit implicit = fallback;
}
// An installed notation names a declaration of its owner. An empty
// associativity keeps the symbol's fixed syntax.
class ZKC_FrontendNotation<string owner, string spelling, string associativity,
                           int level, string value, bit visible>
    : ZKC_Declaration {
  string module = owner;
  string symbol = spelling;
  string fixity = associativity;
  int precedence = level;
  string target = value;
  bit public = visible;
}
class ZKC_ServiceSignature<string value, string requirement>
    : ZKC_Declaration {
  string name = value;
  string capability = requirement;
}
class ZKC_Member<string value, ZKC_Parameter from, ZKC_Parameter to> : ZKC_Declaration {
  string name = value;
  ZKC_Parameter owner = from;
  ZKC_Parameter result = to;
}
class ZKC_Term<ZKC_Parameter p> : ZKC_Declaration {
  ZKC_Parameter parameter = p;
  string name = "";
  ZKC_Term parent = ?;
  ZKC_Member member = ?;
}
class ZKC_Root<string value, ZKC_Parameter p> : ZKC_Term<p> {
  let name = value;
}
class ZKC_Project<ZKC_Term base, ZKC_Member m> : ZKC_Term<m.result> {
  let name = m.name;
  let parent = base;
  let member = m;
}
class ZKC_Custody<string value> : ZKC_Declaration { string name = value; }
def PublicValue : ZKC_Custody<"PublicValue">;
def PrivateImmutable : ZKC_Custody<"PrivateImmutable">;
def Affine : ZKC_Custody<"Affine">;
class ZKC_TypeHead<string value> : ZKC_Declaration { string name = value; }
// A source collection view: `rank` is 1 or 2 and `element` is "parameter",
// "index" or "byte".
class ZKC_TypeCollection<int r, string e> : ZKC_Declaration {
  int rank = r;
  string element = e;
}
class ZKC_Type<string value, list<ZKC_Parameter> ps = [],
               ZKC_Custody c = PublicValue, bit copyable = 1,
               bit droppable = 1> : ZKC_TypeHead<value> {
  list<ZKC_Parameter> parameters = ps;
  ZKC_Custody custody = c;
  bit copy = copyable;
  bit drop = droppable;
  // Native profile facts, separate from source usage and concrete codecs.
  bit nativeLocal = 1;
  bit mathematical = 0;
  bit participants = !eq(c, PublicValue);
  bit constructible = !eq(c, PublicValue);
  // A message frame exists for some complete applications of this head.
  // Actual domain, shape and representation admission remains independent.
  bit message = 0;
  // Source vocabulary. These columns grant no codec, transport or execution
  // authority. An unset collection or setup is null; setup is "prover" or
  // "verifier" for the setup-key constructors.
  bit sourceData = 0;
  ZKC_TypeCollection collection = ?;
  string setup = ?;
}
class ZKC_Apply<ZKC_Type head, list<ZKC_Term> args = []>
    : ZKC_Term<TypeParameter> {
  let name = head.name;
  ZKC_Type constructor = head;
  list<ZKC_Term> arguments = args;
}
class ZKC_Natural<int value> : ZKC_Term<NatParameter> {
  let name = !strconcat("n", !cast<string>(value));
  int number = value;
}
// A capability may name members of its domain sort: a domain holding it has
// every `requires` member, and a domain may have a member that some capability
// names only while holding such a capability.
class ZKC_Capability<string value, list<ZKC_Parameter> ps,
                     list<string> required = [], list<string> permitted = []>
    : ZKC_Declaration {
  string name = value;
  list<ZKC_Parameter> parameters = ps;
  list<string> requires = required;
  list<string> permits = permitted;
}
class ZKC_Holds<ZKC_Capability cap, list<ZKC_Term> args> : ZKC_Declaration {
  ZKC_Capability capability = cap;
  list<ZKC_Term> arguments = args;
}
class ZKC_Implication<ZKC_Capability p, ZKC_Capability c> : ZKC_Declaration {
  ZKC_Capability premise = p;
  ZKC_Capability conclusion = c;
}
class ZKC_Stage<string value> : ZKC_Declaration { string name = value; }
def Source : ZKC_Stage<"Source">;
def Construction : ZKC_Stage<"Construction">;
def CompilerGenerated : ZKC_Stage<"CompilerGenerated">;
def Physical : ZKC_Stage<"Physical">;
class ZKC_Parameters<string value, int min, int max> : ZKC_Declaration {
  string name = value;
  int minimum = min;
  int maximum = max; // -1 means variadic.
  string assetFormat = "";
}
def NoParameters : ZKC_Parameters<"None", 0, 0>;
def NumericalExpression : ZKC_Parameters<"NumericalExpression", 1, 1>;
def NaturalParameter : ZKC_Parameters<"Natural", 1, 1>;
def ExtentParameter : ZKC_Parameters<"Extent", 1, 1>;
def FieldLiteral : ZKC_Parameters<"FieldLiteral", 1, 1>;
def FieldLiterals : ZKC_Parameters<"FieldLiterals", 0, -1>;
def MatrixShape : ZKC_Parameters<"MatrixShape", 2, 2>;
def MatrixIdentity : ZKC_Parameters<"MatrixIdentity", 1, 1>;
def RingAssetIdentity : ZKC_Parameters<"AssetIdentity", 1, 1> {
  let assetFormat = "zkc.ring/0";
}
def RelationAssetIdentity : ZKC_Parameters<"AssetIdentity", 1, 1> {
  let assetFormat = "zkc.relation-bundle/0";
}
def MatrixVector : ZKC_Parameters<"MatrixVector", 3, 3>;
def GatherIndices : ZKC_Parameters<"GatherIndices", 0, -1>;
def ScatterIndices : ZKC_Parameters<"ScatterIndices", 1, -1>;
def NativeOrigin : ZKC_Parameters<"NativeOrigin", 1, 1>;
class NativeIndexBlockParameters<int count>
    : ZKC_Parameters<"NativeIndexBlock", count, count>;
class ZKC_Facet : ZKC_Declaration;
def PublicReplay : ZKC_Facet;
def DeterministicData : ZKC_Facet;
def AcceptanceGuard : ZKC_Facet;
def Conjunction : ZKC_Facet;
def SourceHistory : ZKC_Facet;
def ManagedHistory : ZKC_Facet;
class ZKC_History<int input, int output> : ZKC_Facet {
  int stateInput = input;
  int stateOutput = output;
}
// Output `stateOutput` is the successor of the exact resource received at
// input `stateInput`. Identity transfer only: no value equality, purity or
// reordering, and no operation acquires it from its signature shape.
class ZKC_Succession<int input, int output> : ZKC_Facet {
  int stateInput = input;
  int stateOutput = output;
}
class ZKC_Observation<int state = 0, int payload = 1, int result = 0>
    : ZKC_Facet {
  int stateInput = state;
  int payloadInput = payload;
  int stateOutput = result;
}
class ZKC_Provider<string value> : ZKC_Declaration { string name = value; }
def Entropy : ZKC_Provider<"Entropy">;
def TranscriptProvider : ZKC_Provider<"Transcript">;
class ZKC_SampleDomain<string value> : ZKC_Declaration { string name = value; }
def FieldSample : ZKC_SampleDomain<"Field">;
def VectorSample : ZKC_SampleDomain<"FieldVector">;
def IndexSample : ZKC_SampleDomain<"BoundedIndex">;
def IndexBlockSample : ZKC_SampleDomain<"IndexBlock">;
class ZKC_Sampling<ZKC_Provider p, ZKC_SampleDomain d, int bound = -1>
    : ZKC_Facet {
  ZKC_Provider provider = p;
  ZKC_SampleDomain domain = d;
  int stateInput = 0;
  int valueOutput = 0;
  int stateOutput = 1;
  int boundInput = bound;
}
class ZKC_Diagonal<int factors = 0, int values = 1, int result = 0>
    : ZKC_Facet {
  int factorsInput = factors;
  int valuesInput = values;
  int resultOutput = result;
}
class ZKC_Contraction<int coefficients = 0, int values = 1> : ZKC_Facet {
  int coefficientsInput = coefficients;
  int valuesInput = values;
}
class ZKC_Coset<int shift, int size, bit length = 0, int vector = -1,
                bit folded = 0> : ZKC_Facet {
  int shiftInput = shift;
  int sizeInput = size;
  bit sizeIsLength = length;
  int vectorOutput = vector;
  bit foldedOutput = folded;
}
class ZKC_ValueRule<string value> : ZKC_Declaration { string name = value; }
def ConstantValue : ZKC_ValueRule<"Constant">;
def LengthValue : ZKC_ValueRule<"Length">;
def MultiplyValue : ZKC_ValueRule<"Multiply">;
def DivideValue : ZKC_ValueRule<"Divide">;
class ZKC_DomainValue<ZKC_ValueRule r, int out = 0, int operand = 0, int other = 1>
    : ZKC_Facet {
  ZKC_ValueRule rule = r;
  int output = out;
  int input = operand;
  int otherInput = other;
}
// A closed signature family; its mask is a positional Boolean sequence.
class ZKC_NumericalSignature<ZKC_Term domain, string value> : ZKC_Declaration {
  ZKC_Term fieldTerm = domain;
  string result = value;
}
class ZKC_Operation<string value, list<ZKC_Term> terms,
                    list<ZKC_Term> ins, list<ZKC_Term> outs,
                    list<ZKC_Holds> needs = []> : ZKC_Declaration {
  string name = value;
  list<ZKC_Term> scope = terms;
  list<ZKC_Term> inputs = ins;
  list<ZKC_Term> outputs = outs;
  ZKC_NumericalSignature numerical = ?;
  list<ZKC_Holds> requirements = needs;
  ZKC_Stage stage = Source;
  ZKC_Parameters parameters = NoParameters;
  // Field-literal validation uses this scoped domain, never a default modulus.
  ZKC_Term parameterField = ?;
  list<ZKC_Facet> facets = [];
  ZKC_Operation derivedCounterpart = ?;
}
// A consumer-owned expectation, separate from the installed operation. The
// generator checks exact correspondence before publishing membership data.
class ZKC_ConsumerOperation<ZKC_Operation target, list<ZKC_Term> terms,
                            list<ZKC_Term> ins, list<ZKC_Term> outs,
                            list<ZKC_Holds> needs = []> : ZKC_Declaration {
  ZKC_Operation operation = target;
  string name = target.name;
  list<ZKC_Term> scope = terms;
  list<ZKC_Term> inputs = ins;
  list<ZKC_Term> outputs = outs;
  list<ZKC_Holds> requirements = needs;
  ZKC_NumericalSignature numerical = ?;
  ZKC_Stage stage = Source;
  ZKC_Parameters parameters = NoParameters;
  ZKC_Term parameterField = ?;
}
class ZKC_ConsumerProfile<string value, list<ZKC_Type> types,
                         list<string> validators,
                         list<ZKC_ConsumerOperation> entries> : ZKC_Declaration {
  string name = value;
  string implementation = "unselected";
  list<ZKC_Type> typeConstructors = types;
  list<string> parameterValidators = validators;
  list<ZKC_ConsumerOperation> operations = entries;
}
class ZKC_TypeFamily<string value> : ZKC_TypeHead<value>;
class ZKC_TypeFamilyCase<ZKC_TypeFamily f, ZKC_Type element, ZKC_Type result> : ZKC_Declaration {
  ZKC_TypeFamily family = f;
  ZKC_Type elementConstructor = element;
  ZKC_Type resultConstructor = result;
}
class ZKC_AssociatedType<ZKC_Parameter s, string m, ZKC_Type t> : ZKC_Declaration {
  ZKC_Parameter owner = s;
  string member = m;
  ZKC_Type constructor = t;
}
class ZKC_CapabilityExport<string m, string n, ZKC_Capability cap> : ZKC_Declaration {
  string module = m;
  string name = n;
  ZKC_Capability capability = cap;
}
class ZKC_TypeExport<string m, string n, ZKC_TypeHead t> : ZKC_Declaration {
  string module = m;
  string name = n;
  ZKC_TypeHead type = t;
}
// Closed mathematical vocabulary. Meanings are independent of executable
// declarations, intrinsic spellings, and realization availability.
class ZKC_ScalarLaws<string family, string shape> : ZKC_Declaration {
  string name = shape;
  string algebra = family;
  string signature = shape;
  bit associative = 0;
  bit commutative = 0;
  bit total = 0;
  string leftIdentity = "None";
  string rightIdentity = "None";
  string annihilator = "None";
  bit scalarAction = 0;
  string access = "None";
}
class ZKC_MathematicalIdentity<string value, int position> : ZKC_Declaration {
  string name = value;
  int ordinal = position;
  ZKC_ScalarLaws laws = ?;
}
class ZKC_MathematicalIntrinsic<string value, ZKC_MathematicalIdentity meaning,
                                 string domain, int position,
                                 int ns = 0, bit points = 0, bit ordered = 0>
    : ZKC_Declaration {
  string name = value;
  ZKC_MathematicalIdentity identity = meaning;
  string domainKind = domain;
  int ordinal = position;
  int naturals = ns;
  bit domainPoints = points;
  bit scalar = ordered;
}
class ZKC_Mathematical<ZKC_MathematicalIdentity meaning> : ZKC_Facet {
  ZKC_MathematicalIdentity identity = meaning;
}

// Installed instances: explicit rows declaring which nominal domains, logical
// type instances, codecs and frames exist. Identities and cross-row references
// are declared strings that zkc-tblgen resolves and checks; record names are
// presentation only. Physical choices live in the separate native installation
// schema. An unset optional field is a null or absent column.
class ZKC_ReductionTerm<int e, string c> : ZKC_Declaration {
  int exponent = e;
  string coefficient = c;
}
// `kind` is "prime" or "extension"; only an extension sets the other fields.
class ZKC_FieldStructure<string k> : ZKC_Declaration {
  string kind = k;
  string over = ?;
  int degree = ?;
  list<ZKC_ReductionTerm> reduction = ?;
}
class ZKC_TwoAdicConvention<string id, string root, int adicity,
                            string order> : ZKC_Declaration {
  string convention = id;
  string maximalRoot = root;
  int twoAdicity = adicity;
  string ordering = order;
}
class ZKC_FieldFacts<string c, ZKC_FieldStructure s> : ZKC_Declaration {
  string characteristic = c;
  ZKC_FieldStructure structure = s;
  ZKC_TwoAdicConvention twoAdic = ?;
}
class ZKC_TranscriptFacts<string f, string d, bit b> : ZKC_Declaration {
  string family = f;
  string hash = ?;
  string decoder = d;
  bit bindsSuite = b;
}
class ZKC_CommitmentFacts<string s> : ZKC_Declaration {
  string scheme = s;
  int digestBytes = ?;
  string permutation = ?;
  int digestWordBytes = ?;
}
// `members` holds ordered [member, identity] pairs.
class ZKC_InstalledDomain<string id, string s, list<list<string>> m,
                          list<string> c> : ZKC_Declaration {
  string identity = id;
  string sort = s;
  list<list<string>> members = m;
  list<string> capabilities = c;
  ZKC_FieldFacts fieldFacts = ?;
  ZKC_TranscriptFacts transcriptFacts = ?;
  ZKC_CommitmentFacts commitmentFacts = ?;
}
class ZKC_LogicalTypeInstance<string k, string d> : ZKC_Declaration {
  string kind = k;
  string domain = d;
}
class ZKC_SharedFrame<string k, string s> : ZKC_Declaration {
  string kind = k;
  string scheme = s;
}
class ZKC_FrameTag<int t, string l> : ZKC_Declaration {
  int tag = t;
  string layout = l;
  ZKC_SharedFrame shared = ?;
}
class ZKC_CodecFrame<int t> : ZKC_Declaration {
  int tag = t;
  int elementBytes = ?;
  int bytes = ?;
  int bytesPerArity = ?;
}
class ZKC_Codec<string id, string k, string d> : ZKC_Declaration {
  string identity = id;
  string kind = k;
  string domain = d;
  ZKC_CodecFrame frame = ?;
}
class ZKC_AggregateFrame<string c, string d, int t> : ZKC_Declaration {
  string constructor = c;
  string domain = d;
  int tag = t;
}
class ZKC_RandomService<string c, string f> : ZKC_Declaration {
  string contract = c;
  string fieldDomain = f;
}
class ZKC_Limit<string n, int v, string u, string o, string s, string p>
    : ZKC_Declaration {
  string name = n;
  int value = v;
  string unit = u;
  string owner = o;
  string scope = s;
  string phase = p;
}
class ZKC_FiniteDefinition<string id, string m, string o, bit f>
    : ZKC_Declaration {
  string identity = id;
  string mode = m;
  string operation = o;
  string collection = ?;
  bit filtered = f;
}
class ZKC_DomainConstructor<string id, string k, int a> : ZKC_Declaration {
  string identity = id;
  string kind = k;
  int axis = a;
}

#endif
