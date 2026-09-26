#include "InspectionPrinter.h"
#include "zkc/Support/Json.h"
using namespace llvm;
namespace zkc {
void printSourceInspection(const json::Value &report, raw_ostream &out) {
  const auto &r = *report.getAsObject();
  auto name = [](const json::Value &v) { return *v.getAsString(); };
  auto pairs = [&](const json::Array &values) {
    bool first = true;
    for (const auto &value : values) {
      const auto &pair = *value.getAsArray();
      out << (first ? "" : ", ") << name(pair[0]) << " = " << name(pair[1]);
      first = false;
    }
    if (values.empty())
      out << "none";
  };
  auto predicates = [&](const json::Array &values) {
    bool first = true;
    for (const auto &value : values) {
      const auto &p = *value.getAsArray();
      out << (first ? "" : ", ") << name(p[0]) << "(";
      bool firstArg = true;
      for (const auto &argument : *p[1].getAsArray()) {
        out << (firstArg ? "" : ", ") << name(argument);
        firstArg = false;
      }
      out << ")";
      first = false;
    }
    if (values.empty())
      out << "none";
  };
  out << "Source admitted; implementation search is not performed.\n";
  for (const auto &value : *r.getArray("elaborated_calls")) {
    const auto &call = *value.getAsObject();
    out << "\n"
        << *call.getString("owner") << " [" << *call.getString("site") << "] "
        << *call.getString("kind") << " " << *call.getString("callee")
        << "\n  static arguments (" << *call.getString("static_origin")
        << "): ";
    const auto &arguments = *call.getArray("static_arguments");
    llvm::interleaveComma(arguments, out,
                          [&](const auto &arg) { out << *arg.getAsString(); });
    if (arguments.empty())
      out << "none";
    for (const auto &result : *call.getArray("results")) {
      const auto &binding = *result.getAsObject();
      out << "\n  " << *binding.getString("name") << ": "
          << *binding.getString("type");
    }
    out << '\n';
  }
  for (const auto &value : *r.getArray("definitions")) {
    const auto &d = *value.getAsObject();
    out << "\nfn " << *d.getString("name") << " ("
        << *d.getInteger("operations") << " operations)\n  parameters: ";
    pairs(*d.getArray("parameters"));
    out << "\n  declared requirements: ";
    predicates(*d.getArray("declared"));
    out << "\n  inferred requirements: ";
    predicates(*d.getArray("inferred"));
    out << '\n';
  }
  for (const auto &value : *r.getArray("configurations")) {
    const auto &c = *value.getAsObject();
    out << "\nconfigure " << *c.getString("name") << " = "
        << *c.getString("definition") << "\n  resolved arguments: ";
    pairs(*c.getArray("arguments"));
    out << "\n  remaining parameters: ";
    pairs(*c.getArray("remaining"));
    out << "\n  explicit implementations: ";
    pairs(*c.getArray("implementations"));
    out << "\n  executable use: " << (*c.getBoolean("demanded") ? "yes" : "no")
        << '\n';
  }
  out << "\nDemanded configurations and shared symbols:\n";
  for (const auto &value : *r.getArray("specializations")) {
    const auto &p = *value.getAsArray();
    out << "  " << name(p[0]) << " -> " << name(p[1]) << '\n';
  }
  const auto &module = *r.get("source")->getAsArray();
  out << "\nClosed source: " << module[2].getAsArray()->size()
      << " local functions, " << module[3].getAsArray()->size()
      << " protocols, " << module[4].getAsArray()->size() << " instances, "
      << module[5].getAsArray()->size() << " entries.\n";
}
} // namespace zkc
