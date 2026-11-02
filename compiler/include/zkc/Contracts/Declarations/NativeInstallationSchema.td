#ifndef ZKC_NATIVE_INSTALLATION_SCHEMA
#define ZKC_NATIVE_INSTALLATION_SCHEMA
// Physical choices of the native installation: representations, provider
// preferences and units, field arithmetic forms and backend calling
// conventions. These records are not declarations and join no contribution;
// rows reference declaration keys by their declared strings, which zkc-tblgen
// resolves against the declaration records of the same catalog package. A
// provider preference is not an installation grant. Row order is `ordinal`.

// A logical type tree in an exact type pattern: a constructor application.
class ZKC_TypeTreeArgument<string k> { string kind = k; }
class ZKC_TypeTree<string c, list<ZKC_TypeTreeArgument> args> {
  string constructor = c;
  list<ZKC_TypeTreeArgument> arguments = args;
}
class ZKC_DomainTypeArgument<string s, string id>
    : ZKC_TypeTreeArgument<"domain"> {
  string sort = s;
  string identity = id;
}
class ZKC_NestedTypeArgument<ZKC_TypeTree t> : ZKC_TypeTreeArgument<"type"> {
  ZKC_TypeTree type = t;
}
class ZKC_NatTypeArgument<string v> : ZKC_TypeTreeArgument<"nat"> {
  string value = v;
}

// One static argument pattern of an applied representation.
class ZKC_ArgumentPattern<string k> { string kind = k; }
class ZKC_DomainPattern<string s, string id> : ZKC_ArgumentPattern<"domain"> {
  string sort = s;
  string identity = id;
}
class ZKC_TypePattern<ZKC_TypeTree t> : ZKC_ArgumentPattern<"type"> {
  ZKC_TypeTree type = t;
}
class ZKC_NatRangePattern<string low, string high>
    : ZKC_ArgumentPattern<"natRange"> {
  string minimum = low;
  string maximum = high;
}
class ZKC_AnyPattern : ZKC_ArgumentPattern<"any">;

// `frame` is "canonical" or "local"; `unit` owns the storage.
class ZKC_NativeRepresentation<string id, string k, string d, bit selected,
                               string l, string f, string u> {
  string identity = id;
  string kind = k;
  string domain = d;
  bit isDefault = selected;
  string layout = l;
  string frame = f;
  string unit = u;
}
class ZKC_RepresentationChild<string k, string d, string r> {
  string kind = k;
  string domain = d;
  string representation = r;
}
class ZKC_AppliedRepresentation<string c, list<ZKC_ArgumentPattern> args,
                                string id, bit selected, string f, string u> {
  string constructor = c;
  list<ZKC_ArgumentPattern> arguments = args;
  string identity = id;
  bit isDefault = selected;
  ZKC_RepresentationChild child = ?;
  string frame = f;
  string unit = u;
}
class ZKC_ProviderPreference<string d, string p, list<string> others> {
  string domain = d;
  string provider = p;
  list<string> alternatives = others;
}
class ZKC_ProviderUnit<string p, string u> {
  string provider = p;
  string unit = u;
}
class ZKC_ResidueArithmetic<string f, string r> {
  string form = f;
  string representation = r;
}
class ZKC_MontgomeryForm<int w, int r> {
  int wordBytes = w;
  int radixBits = r;
}
class ZKC_ByteEncoding<string c, string o> {
  string codec = c;
  string order = o;
}
class ZKC_FieldForm<string f> {
  string fieldDomain = f;
  ZKC_ResidueArithmetic arithmetic = ?;
  ZKC_MontgomeryForm montgomery = ?;
  ZKC_ByteEncoding byteEncoding = ?;
}
// A backend calling convention, not part of the operation's declaration.
class ZKC_PhysicalArguments<string op> { string operation = op; }

#endif
