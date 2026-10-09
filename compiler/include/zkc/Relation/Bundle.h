#ifndef ZKC_RELATION_BUNDLE_H
#define ZKC_RELATION_BUNDLE_H

#include "zkc/Contracts/RingExpression.h"
#include "zkc/Relation/AIR.h"
#include "llvm/ADT/ArrayRef.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/Support/Error.h"
#include "llvm/Support/JSON.h"
#include <cstdint>
#include <optional>
#include <string>
#include <tuple>
#include <vector>

namespace zkc::relation {

/// Formation, admission and reference-evaluation bounds. Supplied data is
/// counted in field elements and base coordinates before any value is parsed.
struct BundleLimits {
  static constexpr size_t bytes = 8 * 1024 * 1024;
  static constexpr size_t dataBytes = 256 * 1024 * 1024;
  static constexpr uint32_t tables = 256, groups = 256, width = 65536;
  static constexpr uint32_t publics = 65536, channels = 4096, arity = 64;
  static constexpr uint32_t checks = 4096, name = 128;
  static constexpr uint32_t offset = 65536, height = 1u << 20;
  static constexpr uint64_t coordinates = 1u << 22, work = 1u << 26;
  static constexpr uint64_t analysisWork = 1u << 26;
  static constexpr uint64_t analysisInputs = 1u << 22;
  static constexpr uint64_t contributions = 1u << 22;
  static constexpr uint64_t resultRecords = 1u << 20;
  static constexpr uint64_t resultCoordinates = 1u << 22;
  static constexpr uint64_t multiplicity = UINT32_MAX;
  static constexpr uint32_t phases = 16, slots = 4096, premises = 4096;
};

/// Who fixes a column group's contents: the prover's witness, the verifier's
/// configuration, or the verifier's public instance.
enum class BundleAuthority { Witness, Config, Public };
enum class BundleHeightAuthority { Fixed, Config, Instance };
/// Fixed heights have min == max. Every present table has height >= 1.
struct BundleHeight {
  BundleHeightAuthority authority = BundleHeightAuthority::Fixed;
  uint32_t min = 1, max = 1;
  bool powerOfTwo = false;
};
enum class BundleReadModel { Finite, Cyclic };
/// Every scope is a contiguous row range of a present table of height h:
/// All [0,h), First {0}, Last {h-1}, Interior(l,r) [l,h-r) (empty when
/// l+r >= h), Interval(s,e) [s,e), which requires e <= h.
enum class BundleScopeKind { All, First, Last, Interior, Interval };
struct BundleScope {
  BundleScopeKind kind = BundleScopeKind::All;
  uint32_t first = 0, second = 0; // Interior (l,r) or Interval (s,e).
};
struct BundleGroup {
  std::string name;
  BundleAuthority authority = BundleAuthority::Witness;
  std::string field;
  uint32_t width = 1;
};
/// Closed binding of one ring input: a public scalar slot, or a same-table
/// read of `column` in `group` at the signed row offset. There is no
/// challenge, claim or selector input in the deterministic relation.
struct BundleInput {
  enum class Kind { Public, Read } kind = Kind::Public;
  uint32_t index = 0; // Public slot or group.
  int32_t offset = 0;
  uint32_t column = 0;
  static BundleInput publicSlot(uint32_t index);
  static BundleInput read(uint32_t group, int32_t offset, uint32_t column);
};
struct BundleAssertion {
  uint32_t output = 0; // Position in the table arena's ordered outputs.
  BundleScope scope;
};
/// Field-weighted balance and natural multiset equality are different
/// relations; a channel fixes which one its interactions denote.
enum class BundleChannelKind { FieldBalance, Multiset };
struct BundleChannel {
  std::string name;
  BundleChannelKind kind = BundleChannelKind::FieldBalance;
  std::vector<std::string> tuple; // Fields of the complete tuple.
  std::string count;              // Count field; prime for multisets.
};
/// Global contributions balance across all tables; Local(key) contributions
/// balance only within their table and key.
struct BundleLocality {
  bool local = false;
  uint32_t key = 0;
};
enum class BundleSide { Push, Pull };
/// FieldBalance: `count` is a field value; `bound` is an optional recorded
/// source premise that is not part of satisfaction. Multiset: `side` and the
/// required `bound`; each active multiplicity must be a natural <= bound.
struct BundleInteraction {
  BundleChannelKind kind = BundleChannelKind::FieldBalance;
  uint32_t channel = 0;
  BundleLocality locality;
  BundleScope scope;
  BundleSide side = BundleSide::Push;
  std::vector<uint32_t> tuple;
  uint32_t count = 0;
  std::optional<uint64_t> bound;
};
struct BundleTable {
  std::string name;
  bool optional = false;
  BundleHeight height;
  BundleReadModel readModel = BundleReadModel::Finite;
  std::vector<BundleGroup> groups;
  ring::Expression arena;
  std::vector<BundleInput> inputs; // One per arena input.
  std::vector<BundleAssertion> assertions;
  std::vector<BundleInteraction> interactions;
};
struct BundleSlot {
  std::string name, field;
};
struct BundleRead {
  uint32_t group = 0;
  int32_t offset = 0;
  uint32_t column = 0;
  bool operator<(const BundleRead &other) const {
    return std::tie(group, offset, column) <
           std::tie(other.group, other.offset, other.column);
  }
  bool operator==(const BundleRead &other) const {
    return group == other.group && offset == other.offset &&
           column == other.column;
  }
};
/// Derived per-output facts. Degree weights: public slots 0, every read 1
/// regardless of its group's authority.
struct BundleOutputFact {
  std::string field;
  uint32_t degree = 0;
  std::vector<BundleRead> reads; // Sorted unique syntactic reads.
  std::vector<uint32_t> publics; // Sorted unique public slots.
};

/// Supplied values are canonical base coordinates: one per prime-field
/// element and `degree` (ascending basis) per extension element. Group data
/// is row-major and flattened: element (row,column) occupies coordinates
/// [(row*width+column)*degree, ...).
using BundleColumns = std::vector<std::string>;
struct BundleConfiguration {
  struct Table {
    std::optional<uint32_t> height;    // Exactly for Config height authority.
    std::vector<BundleColumns> groups; // Config groups, in group order.
  };
  std::string relation;
  std::vector<Table> tables;
};
struct BundleInstance {
  struct Table {
    bool present = true;
    std::optional<uint32_t> height;    // Exactly for Instance height authority.
    std::vector<BundleColumns> groups; // Public groups, in group order.
  };
  std::string relation;
  std::vector<BundleColumns> publics; // One coordinate list per slot.
  std::vector<Table> tables;
};
struct BundleWitness {
  std::string relation;
  /// nullopt exactly for an absent table; otherwise witness groups in order.
  std::vector<std::optional<std::vector<BundleColumns>>> tables;
};

struct BundleResidual {
  uint32_t table, assertion, row;
  BundleColumns value;
};
struct BundleBalance {
  BundleChannelKind kind = BundleChannelKind::FieldBalance;
  uint32_t channel;
  std::optional<std::pair<uint32_t, uint32_t>> local; // (table, key).
  std::vector<BundleColumns> tuple;
  BundleColumns sum;           // Field balance: the field sum.
  uint64_t push = 0, pull = 0; // Multiset: natural totals.
  bool balanced = true;
};
struct BundleRangeFailure {
  uint32_t table, interaction, row;
};
struct BundleEvaluation {
  bool satisfied = true;
  uint64_t work = 0;
  std::vector<BundleResidual> residuals; // Every (table,assertion,row).
  std::vector<BundleBalance> balances;   // Every observed balance key.
  std::vector<BundleRangeFailure> rangeFailures;
  llvm::json::Value encode() const;
};

/// A deterministic multi-table relation R_config(instance, witness). Its
/// meaning has no protocol randomness. Formation refuses unknown fields,
/// unused or duplicate input bindings, unreferenced outputs, kind/field
/// mismatches and finite windows undefined at every height.
class Bundle {
public:
  static llvm::Expected<Bundle> create(std::vector<BundleSlot> publics,
                                       std::vector<BundleChannel> channels,
                                       std::vector<BundleTable> tables);
  llvm::ArrayRef<BundleSlot> publics() const { return publics_; }
  llvm::ArrayRef<BundleChannel> channels() const { return channels_; }
  llvm::ArrayRef<BundleTable> tables() const { return tables_; }
  /// Facts per table, per arena output position.
  llvm::ArrayRef<std::vector<BundleOutputFact>> facts() const { return facts_; }
  llvm::json::Value encode() const;
  /// SHA256 of the canonical encoding; structural, not semantic, identity.
  llvm::StringRef identity() const { return identity_; }
  llvm::json::Value analysis() const;
  /// Shape, authority, presence, heights and every read domain are checked
  /// before any value is parsed or any expression is evaluated.
  llvm::Error admit(const BundleConfiguration &, const BundleInstance &,
                    const BundleWitness &) const;
  /// Admission followed by the reference interpretation over the installed
  /// prime fields and the reference extension presentations.
  llvm::Expected<BundleEvaluation> evaluate(const BundleConfiguration &,
                                            const BundleInstance &,
                                            const BundleWitness &) const;

private:
  Bundle(std::vector<BundleSlot>, std::vector<BundleChannel>,
         std::vector<BundleTable>, std::vector<std::vector<BundleOutputFact>>);
  std::vector<BundleSlot> publics_;
  std::vector<BundleChannel> channels_;
  std::vector<BundleTable> tables_;
  std::vector<std::vector<BundleOutputFact>> facts_;
  std::string identity_;
};

llvm::Expected<Bundle> readBundle(const llvm::json::Value &);
llvm::Expected<Bundle> readBundleText(llvm::StringRef);
/// Bounded parse for supplied-data and staged-assignment carriers.
llvm::Expected<llvm::json::Value> readBundleDataJson(llvm::StringRef);
llvm::Expected<BundleConfiguration>
readBundleConfiguration(const Bundle &, const llvm::json::Value &);
llvm::Expected<BundleInstance> readBundleInstance(const Bundle &,
                                                  const llvm::json::Value &);
llvm::Expected<BundleWitness> readBundleWitness(const Bundle &,
                                                const llvm::json::Value &);
llvm::json::Value encodeBundleConfiguration(const Bundle &,
                                            const BundleConfiguration &);
llvm::json::Value encodeBundleInstance(const Bundle &, const BundleInstance &);
llvm::json::Value encodeBundleWitness(const Bundle &, const BundleWitness &);
/// Number of base coordinates per element of an admitted value field, or a
/// refusal when no reference presentation is installed.
llvm::Expected<unsigned> bundleFieldDegree(llvm::StringRef field);

/// The finite AIR as a one-table bundle: required finite table "trace" with
/// height chosen by the instance in [1, AIRLimits::height], one witness group
/// "columns" and the AIR's public slots. Every -> All, First -> First,
/// Last -> Last, Transition(k) -> Interior(0,k). An AIR whose window is
/// undefined at every height refuses here (bundle-window); AIR::create defers
/// that refusal to compile.
llvm::Expected<Bundle> embedAIR(const AIR &);
struct BundleData {
  BundleConfiguration configuration;
  BundleInstance instance;
  BundleWitness witness;
};
BundleData embedAIRData(const Bundle &, const AIRTrace &,
                        llvm::ArrayRef<std::string> statement);

/// One table of a bundle viewed through the installed `relation.table_rows`
/// kernel: dense row-major assertion residuals over one carrier field. The
/// view is homogeneous: every bundle public slot, every group of the table
/// and every assertion output has the carrier field, and every arena node an
/// assertion needs has the carrier field or, for an extension carrier, its
/// base field through an explicit embedding. Widths count elements per row;
/// `coordinates` is the base coordinates per element. The view claims nothing
/// about interactions, other tables, presence or satisfaction.
struct BundleTableView {
  uint32_t table = 0;
  std::string field;
  bool optional = false;
  BundleHeight height;
  BundleReadModel readModel = BundleReadModel::Finite;
  uint32_t publicSlots = 0;
  uint32_t witnessWidth = 0, configWidth = 0, publicWidth = 0;
  uint32_t assertions = 0;
  uint32_t degree = 0; // Largest assertion output degree; 0 without assertions.
  unsigned coordinates = 1;
};
/// Element counts of the kernel's operands and result at one height:
/// witness = height * witnessWidth, configuration = height * configWidth,
/// publicData = publicSlots + height * publicWidth, results = height *
/// assertions. Groups of one authority are concatenated in declaration order,
/// each row-major; public data starts with every bundle public slot.
struct BundleTableLengths {
  uint64_t witness = 0, configuration = 0, publicData = 0, results = 0;
};
/// The three operands laid out from admitted carriers, as canonical base
/// coordinates (`coordinates` strings per element).
struct BundleTableData {
  uint32_t height = 0;
  BundleColumns witness, configuration, publicData;
};
/// Table index and carrier facts (`relation-table-index`,
/// `relation-table-carrier`). A compiler closing an asset reference checks
/// its static table and carrier here before any data exists.
llvm::Expected<BundleTableView> bundleTableView(const Bundle &, uint32_t table,
                                                llvm::StringRef carrier);
/// Height policy, declared data bound, every assertion window at this height,
/// the reference work bound and the dense result bound, in that order, before
/// any operand length is compared (`bundle-height`, `bundle-data-limit`,
/// `bundle-scope-height`, `bundle-window`, `bundle-work-limit`,
/// `bundle-result-limit`). The work bound charges nothing for a table without
/// assertions, as bundle admission does.
llvm::Expected<BundleTableLengths>
bundleTableLengths(const Bundle &, const BundleTableView &, uint32_t height);
/// Full bundle admission of the carriers, then the table's data in the
/// kernel's layout. An absent optional table is not a view
/// (`relation-table-absent`).
llvm::Expected<BundleTableData>
sliceBundleTableData(const Bundle &, const BundleTableView &,
                     const BundleConfiguration &, const BundleInstance &,
                     const BundleWitness &);

/// Static premises of one table viewed through the installed polynomial
/// kernels `relation.table_shape`, `relation.table_input`,
/// `relation.table_scope` and `relation.table_point`. Every bundle public
/// slot, every group of the table and every arena node an assertion needs
/// has the carrier field or, for an extension carrier, its base field; a
/// base-field table is then substituted in the extension. Interaction-only
/// outputs are neither checked nor evaluated. The height policy must admit a
/// power of two of at least 2 (`relation-table-index`,
/// `relation-table-carrier`, `bundle-polynomial-two-adic`). Windows, limits
/// and quotient chunks depend on the height and are execution checks.
llvm::Error checkBundlePolynomialTable(const Bundle &, uint32_t table,
                                       llvm::StringRef carrier);
/// The static reference rule of an installed Bundle kernel contract: the
/// dense table view for `relation.table_rows`, the polynomial premises for
/// the polynomial kernels, and `relation-table-contract` otherwise.
llvm::Error checkBundleTableReference(const Bundle &, llvm::StringRef contract,
                                      uint32_t table, llvm::StringRef carrier);

/// A challenge-dependent constraint program. It references a bundle but never
/// changes that bundle's meaning: it denotes the challenge-indexed predicate
/// over the base data, its own phase groups, challenges and received claims.
/// Premises are recorded assumptions; v0 has no reduction contract.
struct StagedInput {
  enum class Kind { Public, Read, Challenge, Claim } kind = Kind::Public;
  uint32_t phase = 0, index = 0; // Read: phase 0 = bundle groups.
  int32_t offset = 0;
  uint32_t column = 0;
};
struct StagedGroup {
  std::string name, field;
  uint32_t width = 1;
};
struct StagedTable {
  std::vector<StagedGroup> groups;
  ring::Expression arena;
  std::vector<StagedInput> inputs;
  std::vector<BundleAssertion> assertions;
};
struct StagedPhase {
  std::vector<BundleSlot> challenges, claims;
  std::vector<StagedTable> tables; // One per bundle table.
};
struct StagedGlobal {
  ring::Expression arena;
  std::vector<StagedInput> inputs;  // Public, Challenge or Claim only.
  std::vector<uint32_t> assertions; // Output positions that must be zero.
};
struct StagedPremise {
  enum class Kind { Boolean, AtMostOne, Nonzero, CharacteristicExceeds } kind;
  uint32_t phase = 0, table = 0;
  std::vector<uint32_t> outputs;
  BundleScope scope;
  std::string field;
  uint64_t bound = 0;
};
struct StagedAssignment {
  struct Phase {
    std::vector<BundleColumns> challenges, claims;
    std::vector<std::optional<std::vector<BundleColumns>>> tables;
  };
  std::string program;
  std::vector<Phase> phases;
};
struct StagedEvaluation {
  bool satisfied = true;
  uint64_t work = 0;
  struct Residual {
    uint32_t phase, table, assertion, row;
    BundleColumns value;
  };
  std::vector<Residual> residuals;
  std::vector<BundleColumns> global; // One value per global assertion.
  llvm::json::Value encode() const;
};
class StagedProgram {
public:
  static llvm::Expected<StagedProgram> create(const Bundle &,
                                              std::vector<StagedPhase>,
                                              StagedGlobal,
                                              std::vector<StagedPremise>);
  llvm::StringRef relation() const { return relation_; }
  llvm::ArrayRef<StagedPhase> phases() const { return phases_; }
  const StagedGlobal &global() const { return global_; }
  llvm::ArrayRef<StagedPremise> premises() const { return premises_; }
  llvm::json::Value encode() const;
  std::string identity() const;
  /// Evaluates only the staged predicate for the supplied actual challenges
  /// and claims; the bundle's own assertions and interactions are not part of
  /// it. Base data is admitted exactly as for the bundle.
  llvm::Expected<StagedEvaluation>
  evaluate(const Bundle &, const BundleConfiguration &, const BundleInstance &,
           const BundleWitness &, const StagedAssignment &) const;

private:
  StagedProgram(std::string, std::vector<StagedPhase>, StagedGlobal,
                std::vector<StagedPremise>);
  std::string relation_;
  std::vector<StagedPhase> phases_;
  StagedGlobal global_;
  std::vector<StagedPremise> premises_;
};
llvm::Expected<StagedProgram> readStagedProgram(const Bundle &,
                                                const llvm::json::Value &);
llvm::Expected<StagedAssignment>
readStagedAssignment(const Bundle &, const StagedProgram &,
                     const llvm::json::Value &);
/// Encode an assignment admitted for this bundle and staged program.
llvm::json::Value encodeStagedAssignment(const Bundle &, const StagedProgram &,
                                         const StagedAssignment &);

} // namespace zkc::relation
#endif
