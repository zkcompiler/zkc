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
class ZKC_Type<string value, list<ZKC_Parameter> ps = [],
               ZKC_Custody c = PublicValue, bit copyable = 1,
               bit droppable = 1> : ZKC_TypeHead<value> {
  list<ZKC_Parameter> parameters = ps;
  ZKC_Custody custody = c;
  bit copy = copyable;
  bit drop = droppable;
  // False records describe existing special carriers or generation-only types.
  bit commonGeneric = 1;
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
class ZKC_Capability<string value, list<ZKC_Parameter> ps> : ZKC_Declaration {
  string name = value;
  list<ZKC_Parameter> parameters = ps;
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
}
def NoParameters : ZKC_Parameters<"None", 0, 0>;
def NaturalParameter : ZKC_Parameters<"Natural", 1, 1>;
def ExtentParameter : ZKC_Parameters<"Extent", 1, 1>;
def FieldLiteral : ZKC_Parameters<"FieldLiteral", 1, 1>;
def FieldLiterals : ZKC_Parameters<"FieldLiterals", 0, -1>;
def MatrixShape : ZKC_Parameters<"MatrixShape", 2, 2>;
def MatrixIdentity : ZKC_Parameters<"MatrixIdentity", 1, 1>;
def MatrixVector : ZKC_Parameters<"MatrixVector", 3, 3>;
def GatherIndices : ZKC_Parameters<"GatherIndices", 0, -1>;
def ScatterIndices : ZKC_Parameters<"ScatterIndices", 1, -1>;
def TranscriptOrigin : ZKC_Parameters<"TranscriptOrigin", 5, 5>;
class ZKC_Facet : ZKC_Declaration;
def PublicReplay : ZKC_Facet;
def AcceptanceGuard : ZKC_Facet;
def Conjunction : ZKC_Facet;
class ZKC_History<int input, int output> : ZKC_Facet {
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
class ZKC_Operation<string value, list<ZKC_Term> terms,
                    list<ZKC_Apply> ins, list<ZKC_Apply> outs,
                    list<ZKC_Holds> needs = []> : ZKC_Declaration {
  string name = value;
  list<ZKC_Term> scope = terms;
  list<ZKC_Apply> inputs = ins;
  list<ZKC_Apply> outputs = outs;
  list<ZKC_Holds> requirements = needs;
  ZKC_Stage stage = Source;
  ZKC_Parameters parameters = NoParameters;
  // Field-literal validation uses this scoped domain, never a default modulus.
  ZKC_Term parameterField = ?;
  list<ZKC_Facet> facets = [];
  ZKC_Operation derivedCounterpart = ?;
  bit commonGeneric = 1;
  // The closed local envelope preserves existing failure behavior.
  string effect = "local";
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
class ZKC_OperationExport<string m, string n, ZKC_Operation op,
                          list<string> labels> : ZKC_Declaration {
  string module = m;
  string name = n;
  ZKC_Operation operation = op;
  list<string> inputLabels = labels;
}
class ZKC_Operator<string hook, list<ZKC_Type> heads, ZKC_Operation op,
                   list<int> permutation> : ZKC_Declaration {
  string symbol = hook;
  list<ZKC_Type> operands = heads;
  ZKC_Operation operation = op;
  list<int> order = permutation;
}
#endif
