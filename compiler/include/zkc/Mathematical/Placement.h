#ifndef ZKC_MATHEMATICAL_PLACEMENT_H
#define ZKC_MATHEMATICAL_PLACEMENT_H

#include "zkc/Mathematical/Installation.h"
#include "zkc/Mathematical/Subject.h"
#include "zkc/Source/Document.h"
#include <map>
#include <tuple>

namespace zkc::mathematical {

/// A binding in the captured source, independent of target names. Region paths
/// are (statement, child) pairs; binding ordinals are local to their scope.
struct SourceAddress {
  uint32_t definition;
  std::vector<uint32_t> regions;
  uint32_t binding;
  bool operator<(const SourceAddress &other) const {
    return std::tie(definition, regions, binding) <
           std::tie(other.definition, other.regions, other.binding);
  }
};
struct ComponentKey {
  SourceAddress source;
  uint32_t role; // Actual module-role ordinal, after instance substitution.
  bool operator<(const ComponentKey &other) const {
    return std::tie(source, role) < std::tie(other.source, other.role);
  }
};
struct PlacedValue {
  std::vector<uint32_t> regions;
  std::string name;
  std::vector<uint32_t> path;
};
struct ComponentMapping {
  ComponentKey component;
  PlacedValue target;
};
struct SiteMapping {
  uint64_t site;
  std::string targetSite, kind;
};
struct ResultMapping {
  uint32_t role, sourcePort, targetPort;
};
struct PlacementWitness {
  std::string source, target;
  uint32_t definition;
  std::string protocol, instance;
  std::vector<uint64_t> statics;
  std::vector<uint32_t> roles, capabilities;
  std::vector<std::pair<uint32_t, std::string>> roots, operations, wires;
  std::vector<ComponentMapping> components;
  std::vector<SiteMapping> sites;
  std::vector<ResultMapping> results;
};

/// Immutable source and actual target snapshots, with untrusted correspondence
/// data for an independent checker. Native placement is not a Lean proof.
struct Placement {
  Subject source;
  source::Document target;
  PlacementWitness witness;
};

/// Optional authored presentation names. They affect target custody only;
/// component meaning and demand remain defined by source addresses.
struct PlacementNames {
  std::string protocol = "mathematical_protocol";
  std::string instance = "mathematical_instance";
  std::string entry = "main";
  // Complete lists, or empty to use generated names. Argument names are
  // suffixed with `_at_` and the actual role because common SSA names are
  // global.
  std::vector<std::string> arguments, roots, wires;
  std::map<uint64_t, std::string> sites;
};

/// The closed scalar/group Sigma profile. Compute demand from actual terms,
/// preserve each effect occurrence, and emit inline total algebra at each
/// demanded role. Unsupported constructors refuse even when undemanded.
/// Re-admits source against the concrete installation; a Subject formed with
/// an arbitrary Registry cannot choose executable contract meanings.
llvm::Expected<Placement> place(const Subject &, const Installation &,
                                AdmissionBudget budget = {});
/// Frontend builders can use the same admission/placement boundary directly.
llvm::Expected<Placement> place(const raw::Subject &, const Installation &,
                                AdmissionBudget budget = {},
                                const PlacementNames &names = {});
llvm::Expected<llvm::json::Value> encode(const PlacementWitness &);
/// Captured actual input/output pair and untrusted correspondence witness.
llvm::Expected<llvm::json::Value> encode(const Placement &);
llvm::Expected<std::string> placementTargetDigest(const source::Module &);

} // namespace zkc::mathematical
#endif
