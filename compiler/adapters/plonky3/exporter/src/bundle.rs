//! Translation of an export into the deterministic relation-bundle carriers
//! (`zkc.relation-bundle/0` with its configuration, instance and witness).
//!
//! The bundle has scopes rather than selector inputs. The translation is a
//! derivation from the checked guard form, not a rewrite by selector name:
//! every selector path to an assertion root passes only through `mul` and
//! `neg`, so the residual is `+-prod(s_j^k_j) * Q` with `Q` selector-free.
//! Under the row-indicator law each selector is one on its support and zero
//! elsewhere. Substituting the constant one for every selector input and
//! restricting the assertion to the intersection of the supports therefore
//! gives the same residual value on every scope row and asserts nothing on the
//! rows where the original residual is identically zero. Assertions with two
//! different selector kinds refuse rather than rely on height-dependent scopes.
//!
//! The carrier uses the relation-bundle contract, including signed offsets as
//! decimal strings. The export remains
//! the source artifact; the bundle is downstream of it.

use crate::arena::{Arena, Node, hex_sha256};
use crate::artifact::{Instance, Witness};
use crate::field::{F, FIELD_IDENTITY, decimal};
use crate::model::{Export, SelectorKind, Slot};
use crate::refusal::{Result, ensure, refuse};
use crate::view::{ClosedView, MAX_REFERENCE_WORK, MAX_VIEW_CELLS, bounded_product};
use p3_matrix::Matrix;
use serde_json::{Value, json};

pub const BUNDLE_FORMAT: &str = "zkc.relation-bundle/0";
pub const CONFIGURATION_FORMAT: &str = "zkc.relation-configuration/0";
pub const INSTANCE_FORMAT: &str = "zkc.relation-instance/0";
pub const WITNESS_FORMAT: &str = "zkc.relation-witness/0";
/// Bundle table height limit.
pub const HEIGHT_LIMIT: usize = 1 << 20;
pub const TABLE: &str = "main";
pub const MAIN_GROUP: &str = "main";
pub const PREPROCESSED_GROUP: &str = "preprocessed";

/// Rows of one assertion's scope, as the bundle states them.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Scope {
    All,
    First,
    Last,
    /// Rows `i` with `i + 1 < h`.
    Transition,
}

impl Scope {
    pub fn value(self) -> Value {
        match self {
            Scope::All => json!(["all"]),
            Scope::First => json!(["first"]),
            Scope::Last => json!(["last"]),
            Scope::Transition => json!(["interior", 0, 1]),
        }
    }

    pub fn contains(self, row: usize, height: usize) -> bool {
        match self {
            Scope::All => true,
            Scope::First => row == 0,
            Scope::Last => row + 1 == height,
            Scope::Transition => row + 1 < height,
        }
    }
}

/// The derived bundle view of an export: one cyclic table, selector-free arena.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BundleView<'a> {
    export: &'a Export,
    arena: Arena,
    /// Export slot of each bundle input; selectors are not inputs.
    inputs: Vec<Slot>,
    scopes: Vec<Scope>,
}

impl<'a> BundleView<'a> {
    pub fn derive(export: &'a Export) -> Result<Self> {
        export.validate()?;
        let mut scopes = Vec::with_capacity(export.assertions.len());
        for (position, assertion) in export.assertions.iter().enumerate() {
            scopes.push(match assertion.selectors[..] {
                [] => Scope::All,
                [SelectorKind::FirstRow] => Scope::First,
                [SelectorKind::LastRow] => Scope::Last,
                [SelectorKind::Transition] => Scope::Transition,
                _ => {
                    return refuse(
                        "plonky3-bundle-scope",
                        format!(
                            "assertion {position} combines selectors {:?}",
                            assertion.selectors
                        ),
                    );
                }
            });
        }
        if let Some(p) = &export.layout.preprocessed {
            ensure(p.height <= HEIGHT_LIMIT, "plonky3-bundle-height", || {
                format!("fixed height {} exceeds the bundle limit", p.height)
            })?;
        }
        let mut renumber = vec![None; export.slots.len()];
        let mut inputs = vec![];
        for (i, slot) in export.slots.iter().enumerate() {
            if !matches!(slot, Slot::Selector(_)) {
                renumber[i] = Some(inputs.len());
                inputs.push(*slot);
            }
        }
        let nodes = export
            .arena
            .nodes()
            .iter()
            .map(|node| match *node {
                Node::Input(s) => renumber[s].map_or(Node::Constant(1), Node::Input),
                other => other,
            })
            .collect();
        let arena = Arena::new(inputs.len(), nodes, export.arena.outputs().to_vec())?;
        Ok(Self {
            export,
            arena,
            inputs,
            scopes,
        })
    }

    pub fn arena(&self) -> &Arena {
        &self.arena
    }

    pub fn inputs(&self) -> &[Slot] {
        &self.inputs
    }

    /// Bundle residuals on scope rows, as `(row, assertion, value)`, with
    /// cyclic reads, the bundle's configuration and the instance's publics.
    pub fn residuals(
        &self,
        trace: &p3_matrix::dense::RowMajorMatrix<F>,
        public_values: &[F],
    ) -> Result<Vec<(usize, usize, F)>> {
        let export = self.export;
        let instance = Instance {
            export_sha256: export.sha256(),
            height: trace.height(),
            public_values: public_values.to_vec(),
        };
        let closed = ClosedView::bind(export, &instance)?;
        closed.check_trace(trace)?;
        let (height, width) = (trace.height(), trace.width());
        ensure(height <= HEIGHT_LIMIT, "plonky3-bundle-height", || {
            height.to_string()
        })?;
        bounded_product(height, self.arena.outputs().len(), MAX_VIEW_CELLS)?;
        bounded_product(
            height,
            self.arena.nodes().len() + self.inputs.len() + self.scopes.len() + 1,
            MAX_REFERENCE_WORK,
        )?;
        let (fixed, fixed_width) = export
            .layout
            .preprocessed
            .as_ref()
            .map_or((&[][..], 0), |p| (&p.values[..], p.width));
        let mut result = vec![];
        for row in 0..height {
            let value = |slot: &Slot| match *slot {
                Slot::Main { offset, column } => {
                    trace.values[((row + offset) % height) * width + column]
                }
                Slot::Preprocessed { offset, column } => {
                    fixed[((row + offset) % height) * fixed_width + column]
                }
                Slot::Public(i) => public_values[i],
                Slot::Selector(_) => unreachable!("selectors are not bundle inputs"),
            };
            let values: Vec<F> = self.inputs.iter().map(value).collect();
            let outputs = self.arena.evaluate(|s| values[s]);
            for (assertion, (output, scope)) in outputs.into_iter().zip(&self.scopes).enumerate() {
                if scope.contains(row, height) {
                    result.push((row, assertion, output));
                }
            }
        }
        Ok(result)
    }
}

fn scalars(values: &[F]) -> Value {
    Value::Array(values.iter().map(|v| Value::String(decimal(*v))).collect())
}

/// The `zkc.relation-bundle/0` array.
pub fn bundle(export: &Export) -> Result<Value> {
    let view = BundleView::derive(export)?;
    let publics: Vec<Value> = (0..export.layout.public_values)
        .map(|i| json!([format!("public-{i}"), FIELD_IDENTITY]))
        .collect();
    let mut groups = vec![json!([
        MAIN_GROUP,
        "witness",
        FIELD_IDENTITY,
        export.layout.main_width
    ])];
    let height = match &export.layout.preprocessed {
        Some(p) => {
            groups.push(json!([
                PREPROCESSED_GROUP,
                "config",
                FIELD_IDENTITY,
                p.width
            ]));
            json!(["fixed", p.height])
        }
        None => json!(["instance", 1, HEIGHT_LIMIT, true]),
    };
    let inputs: Vec<Value> = view
        .inputs
        .iter()
        .map(|slot| match *slot {
            // Signed offsets are decimal strings in the bundle carrier.
            Slot::Main { offset, column } => json!(["read", 0, offset.to_string(), column]),
            Slot::Preprocessed { offset, column } => {
                json!(["read", 1, offset.to_string(), column])
            }
            Slot::Public(i) => json!(["public", i]),
            Slot::Selector(_) => unreachable!("selectors are not bundle inputs"),
        })
        .collect();
    let assertions: Vec<Value> = view
        .scopes
        .iter()
        .enumerate()
        .map(|(position, scope)| json!([position, scope.value()]))
        .collect();
    let arena: Value =
        serde_json::from_str(&view.arena.canonical()).expect("canonical arena is JSON");
    Ok(json!([
        BUNDLE_FORMAT,
        publics,
        [],
        [[
            TABLE,
            "required",
            height,
            "cyclic",
            groups,
            arena,
            inputs,
            assertions,
            []
        ]]
    ]))
}

/// Canonical compact text and its identity.
pub fn identity(value: &Value) -> (String, String) {
    let text = value.to_string();
    let digest = hex_sha256(text.as_bytes());
    (text, digest)
}

/// Verifier configuration: the AIR's fixed columns.
pub fn configuration(export: &Export, bundle_identity: &str) -> Value {
    let groups: Vec<Value> = export
        .layout
        .preprocessed
        .iter()
        .map(|p| scalars(&p.values))
        .collect();
    json!([
        CONFIGURATION_FORMAT,
        bundle_identity,
        [[Value::Null, groups]]
    ])
}

/// Verifier instance: publics and, without fixed columns, the height.
pub fn instance(export: &Export, bundle_identity: &str, instance: &Instance) -> Value {
    let height = if export.layout.preprocessed.is_some() {
        Value::Null
    } else {
        json!(instance.height)
    };
    json!([
        INSTANCE_FORMAT,
        bundle_identity,
        scalars(&instance.public_values),
        [["present", height, []]]
    ])
}

/// Prover witness: the main trace, row-major.
pub fn witness(bundle_identity: &str, witness: &Witness) -> Value {
    json!([
        WITNESS_FORMAT,
        bundle_identity,
        [[scalars(&witness.trace.values)]]
    ])
}
