//! Complete aggregate layouts, independent of their logical schemas.
use super::structural::{ParseBudget, TYPE_DEPTH_LIMIT, TYPE_NODE_LIMIT};
use super::{AdmissionError, ErrorCode, Identity, LogicalType, PhysicalType, Representation, Type};
type Result<T> = std::result::Result<T, AdmissionError>;
pub(super) const PHYSICAL_SPELLING_LIMIT: usize = 1024 * 1024;
fn invalid(detail: &str) -> AdmissionError {
    AdmissionError::new(ErrorCode::Representation, detail)
}
impl PhysicalType {
    pub(super) fn logical_children(logical: &LogicalType) -> Result<Option<Vec<LogicalType>>> {
        Ok(match logical.kind() {
            Type::Sequence => Some(vec![
                logical
                    .sequence_element()
                    .ok_or_else(|| invalid("sequence-element"))?
                    .clone(),
            ]),
            Type::FieldArray => Some(vec![LogicalType::new(
                Type::Field,
                logical
                    .field_array_parts()
                    .ok_or_else(|| invalid("field-array-element"))?
                    .0,
            )?]),
            Type::FixedVector => Some(vec![
                logical
                    .fixed_vector_parts()
                    .ok_or_else(|| invalid("fixed-vector-element"))?
                    .0
                    .clone(),
            ]),
            Type::Variant => Some(
                logical
                    .variant_descriptor()
                    .ok_or_else(|| invalid("variant-descriptor"))?
                    .alternatives()
                    .iter()
                    .flat_map(|a| a.payload().iter().cloned())
                    .collect(),
            ),
            _ => None,
        })
    }
    /// Standard aggregate storage with exact logical erasure at every child.
    /// A Contracts context separately checks ownership of contributed children.
    pub fn aggregate(
        logical: LogicalType,
        representation: Representation,
        children: Vec<Self>,
    ) -> Result<Self> {
        Self::formed_aggregate(logical, representation, children)?.check_aggregate_layout()
    }
    pub(super) fn check_aggregate_layout(self) -> Result<Self> {
        if self.children.is_none() {
            return Ok(self);
        }
        let mut remaining = TYPE_NODE_LIMIT;
        self.check_layout_bounds(0, &mut remaining)?;
        if self.descriptor_bytes() > super::Limits::TYPE_BYTES {
            return Err(AdmissionError::new(
                ErrorCode::Limit,
                "type descriptor byte ceiling",
            ));
        }
        if self
            .logical
            .spelling()
            .len()
            .saturating_add(1)
            .saturating_add(self.layout_spelling_bytes())
            > PHYSICAL_SPELLING_LIMIT
        {
            return Err(invalid("physical type spelling limit"));
        }
        Ok(self)
    }
    pub(super) fn formed_aggregate(
        logical: LogicalType,
        representation: Representation,
        children: Vec<Self>,
    ) -> Result<Self> {
        Self::check_aggregate_children(&logical, representation, &children)?;
        Ok(Self {
            logical,
            representation,
            children: Some(children.into()),
        })
    }
    /// Validate borrowed descriptors without constructing a second layout.
    /// Catalog ownership is checked separately, including every inactive child.
    pub(super) fn check_aggregate_children(
        logical: &LogicalType,
        representation: Representation,
        children: &[Self],
    ) -> Result<()> {
        let matches = match logical.kind() {
            Type::Sequence => {
                let element = logical
                    .sequence_element()
                    .ok_or_else(|| invalid("sequence-element"))?;
                matches!(children, [child] if child.logical == *element)
            }
            Type::FieldArray => {
                let (field, _) = logical
                    .field_array_parts()
                    .ok_or_else(|| invalid("field-array-element"))?;
                let element = LogicalType::new(Type::Field, field)?;
                matches!(children, [child] if child.logical == element)
            }
            Type::FixedVector => {
                let (element, _) = logical
                    .fixed_vector_parts()
                    .ok_or_else(|| invalid("fixed-vector-element"))?;
                matches!(children, [child] if child.logical == *element)
            }
            Type::Variant => logical
                .variant_descriptor()
                .ok_or_else(|| invalid("variant-descriptor"))?
                .alternatives()
                .iter()
                .flat_map(|a| a.payload())
                .eq(children.iter().map(|child| &child.logical)),
            _ => return Err(invalid("aggregate-logical-type")),
        };
        if !matches {
            return Err(invalid("aggregate-physical-children"));
        }
        if matches!(
            (logical.kind(), representation),
            (Type::FieldArray, Representation::FieldArray)
        ) && logical
            .field_array_parts()
            .is_none_or(|(f, _)| f != Identity::Bls12381Fr)
            || matches!(
                (logical.kind(), representation),
                (Type::FixedVector, Representation::FixedVector)
            ) && logical
                .fixed_vector_parts()
                .is_none_or(|(e, _)| e.kind() != Type::Field || e.identity() != Identity::KoalaBear)
        {
            return Err(invalid("unrepresented logical type"));
        }
        match (logical.kind(), representation) {
            (Type::Sequence, Representation::Sequence)
            | (Type::Variant, Representation::Variant) => {}
            (Type::FieldArray, Representation::FieldArray)
                if children[0].is_leaf(Type::Field, Identity::Bls12381Fr, Representation::Fr) => {}
            (Type::FixedVector, Representation::FixedVector)
                if children[0].is_leaf(
                    Type::Field,
                    Identity::KoalaBear,
                    Representation::KoalaBear,
                ) => {}
            (_, Representation::Extension(_)) => {} // The contributing storage owner checks its rule.
            _ => return Err(invalid("aggregate-storage-children")),
        }
        Ok(())
    }
    fn check_layout_bounds(&self, depth: usize, remaining: &mut usize) -> Result<()> {
        if depth > TYPE_DEPTH_LIMIT || *remaining == 0 {
            return Err(invalid("physical-type-limit"));
        }
        *remaining -= 1;
        for child in self.children().unwrap_or_default() {
            child.check_layout_bounds(depth + 1, remaining)?;
        }
        Ok(())
    }
    pub fn children(&self) -> Option<&[Self]> {
        self.children.as_deref()
    }
    pub fn sequence_element(&self) -> Option<&Self> {
        (self.kind() == Type::Sequence)
            .then(|| self.children()?.first())
            .flatten()
    }
    pub fn field_array_element(&self) -> Option<&Self> {
        (self.kind() == Type::FieldArray)
            .then(|| self.children()?.first())
            .flatten()
    }
    pub fn fixed_vector_element(&self) -> Option<&Self> {
        (self.kind() == Type::FixedVector)
            .then(|| self.children()?.first())
            .flatten()
    }
    pub fn variant_payload(&self, alternative: usize) -> Option<&[Self]> {
        let descriptor = self.logical.variant_descriptor()?;
        let arm = descriptor.alternatives().get(alternative)?;
        let start: usize = descriptor.alternatives()[..alternative]
            .iter()
            .map(|a| a.payload().len())
            .sum();
        self.children()?
            .get(start..start.checked_add(arm.payload().len())?)
    }
    pub fn descriptor_bytes(&self) -> usize {
        self.children().unwrap_or_default().iter().fold(
            self.logical
                .descriptor_bytes()
                .saturating_add(self.child_storage_bytes()),
            |n, c| n.saturating_add(c.descriptor_bytes()),
        )
    }
    fn child_storage_bytes(&self) -> usize {
        self.children.as_ref().map_or(0, |children| {
            256usize.saturating_add(children.len().saturating_mul(std::mem::size_of::<Self>()))
        })
    }
    /// Visit complete metadata, including inactive variant alternatives and
    /// physical child layouts. The admitted graph bounds traversal depth/width.
    pub fn visit_descriptor_backings(&self, shared: &mut dyn FnMut(super::Backing) -> bool) {
        self.logical.visit_descriptor_backings(shared);
        if let Some(children) = &self.children
            && shared(super::Backing::of(children, self.child_storage_bytes()))
        {
            for child in children.iter() {
                child.visit_descriptor_backings(shared);
            }
        }
    }
    fn default_children(&self) -> bool {
        self.children()
            .is_none_or(|children| children.iter().all(Self::is_default_layout))
    }
    fn is_default_layout(&self) -> bool {
        Self::default_representation(&self.logical).is_ok_and(|r| r == self.representation)
            && self.default_children()
    }
    fn layout_spelling(&self) -> String {
        let mut result = self.representation.name().to_owned();
        if !self.default_children() {
            result.push('[');
            for (i, c) in self.children().unwrap_or_default().iter().enumerate() {
                if i != 0 {
                    result.push(',');
                }
                result.push_str(&c.layout_spelling());
            }
            result.push(']');
        }
        result
    }
    fn layout_spelling_bytes(&self) -> usize {
        let bytes = self.representation.name().len();
        if self.default_children() {
            return bytes;
        }
        let children = self.children().unwrap_or_default();
        children.iter().fold(
            bytes
                .saturating_add(2)
                .saturating_add(children.len().saturating_sub(1)),
            |bytes, child| bytes.saturating_add(child.layout_spelling_bytes()),
        )
    }
    pub fn spelling(&self) -> String {
        format!("{}@{}", self.logical.spelling(), self.layout_spelling())
    }
    pub fn parse(spelling: &str) -> Result<Self> {
        Self::parse_with(spelling, |logical, name, children| {
            let representation = Representation::parse(name)?;
            match children {
                Some(children) => Self::formed_aggregate(logical, representation, children),
                None => Self::new(logical, representation),
            }
        })
    }
    pub(super) fn parse_with(
        spelling: &str,
        mut form: impl FnMut(LogicalType, &str, Option<Vec<Self>>) -> Result<Self>,
    ) -> Result<Self> {
        Self::parse_with_budget(spelling, &mut ParseBudget::new(), &mut form)
    }
    fn parse_with_budget(
        spelling: &str,
        budget: &mut ParseBudget,
        form: &mut impl FnMut(LogicalType, &str, Option<Vec<Self>>) -> Result<Self>,
    ) -> Result<Self> {
        if spelling.len() > PHYSICAL_SPELLING_LIMIT {
            return Err(invalid("physical type spelling limit"));
        }
        let (logical, layout) = spelling.split_once('@').ok_or_else(|| {
            AdmissionError::new(ErrorCode::Type, "physical representation required")
        })?;
        let logical = LogicalType::parse_nested(logical, 0, budget)?;
        let mut cursor = layout;
        let ty = Self::parse_layout(logical, &mut cursor, 0, budget, form)?;
        // Logical parsing validates its canonical spelling. Layout parsing checks
        // exact names and bracket elision at each node without serializing again.
        if !cursor.is_empty() {
            return Err(invalid("noncanonical physical spelling"));
        }
        ty.check_aggregate_layout()
    }
    fn parse_layout(
        logical: LogicalType,
        text: &mut &str,
        depth: usize,
        budget: &mut ParseBudget,
        form: &mut impl FnMut(LogicalType, &str, Option<Vec<Self>>) -> Result<Self>,
    ) -> Result<Self> {
        budget.node(depth)?;
        let end = text.find(['[', ']', ',']).unwrap_or(text.len());
        let name = &text[..end];
        if name.len() > super::Limits::STRING_BYTES {
            return Err(invalid("physical type spelling limit"));
        }
        if name.is_empty() || name.contains('@') {
            return Err(AdmissionError::new(
                ErrorCode::Type,
                "uninstalled representation",
            ));
        }
        if name.bytes().any(|b| b.is_ascii_whitespace()) {
            return Err(invalid("representation-identity"));
        }
        *text = &text[end..];
        let expected = Self::logical_children(&logical)?;
        let children = if let Some(expected) = expected {
            budget.allocate(expected.len().saturating_mul(std::mem::size_of::<Self>()))?;
            let explicit = text.starts_with('[');
            if explicit {
                *text = &text[1..];
            }
            let mut children = Vec::with_capacity(expected.len());
            for (i, child) in expected.into_iter().enumerate() {
                if explicit {
                    if i != 0 {
                        *text = text
                            .strip_prefix(',')
                            .ok_or_else(|| invalid("aggregate-physical-children"))?;
                    }
                    children.push(Self::parse_layout(child, text, depth + 1, budget, form)?);
                } else {
                    children.push(Self::parse_default(child, depth + 1, budget, form)?);
                }
            }
            if explicit {
                *text = text
                    .strip_prefix(']')
                    .ok_or_else(|| invalid("aggregate-physical-children"))?;
                if children.iter().all(Self::is_default_layout) {
                    return Err(invalid("noncanonical physical spelling"));
                }
            }
            Some(children)
        } else {
            if text.starts_with('[') {
                return Err(invalid("flat-layout-children"));
            }
            None
        };
        let ty = form(logical, name, children)?;
        if ty.representation.name() != name {
            return Err(invalid("noncanonical physical spelling"));
        }
        Ok(ty)
    }
    fn parse_default(
        logical: LogicalType,
        depth: usize,
        budget: &mut ParseBudget,
        form: &mut impl FnMut(LogicalType, &str, Option<Vec<Self>>) -> Result<Self>,
    ) -> Result<Self> {
        budget.node(depth)?;
        let representation = Self::default_representation(&logical)?;
        let mut children = None;
        if let Some(expected) = Self::logical_children(&logical)? {
            budget.allocate(expected.len().saturating_mul(std::mem::size_of::<Self>()))?;
            children = Some(
                expected
                    .into_iter()
                    .map(|c| Self::parse_default(c, depth + 1, budget, form))
                    .collect::<Result<_>>()?,
            );
        }
        form(logical, representation.name(), children)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn form(
        logical: LogicalType,
        name: &str,
        children: Option<Vec<PhysicalType>>,
    ) -> Result<PhysicalType> {
        let representation = Representation::parse(name)?;
        match children {
            Some(children) => PhysicalType::formed_aggregate(logical, representation, children),
            None => PhysicalType::new(logical, representation),
        }
    }
    #[test]
    fn descriptor_allocations_include_inactive_arms_and_share_only_by_identity() {
        use std::collections::HashSet;
        let resource = LogicalType::parse("resource_unit:slot").unwrap();
        let spelling = zkc_test_support::variants::logical(
            "Metadata",
            serde_json::json!([
                ["empty", []],
                ["inactive", ["sequence<index>", resource.spelling()]]
            ]),
        );
        let ty = PhysicalType::default_for(LogicalType::parse(&spelling).unwrap()).unwrap();
        let collect = |ty: &PhysicalType| {
            let mut seen = HashSet::new();
            ty.visit_descriptor_backings(&mut |backing| seen.insert(backing));
            seen
        };
        let allocations = collect(&ty);
        assert_eq!(collect(&ty.clone()), allocations);
        assert!(collect(&PhysicalType::parse(&ty.spelling()).unwrap()).is_disjoint(&allocations));
        // Every logical child also occurs in the physical layout. Those edges
        // retain the same logical descriptors, including the inactive resource.
        let duplicated = ty
            .logical()
            .variant_descriptor()
            .unwrap()
            .alternatives()
            .iter()
            .flat_map(|arm| arm.payload())
            .map(LogicalType::descriptor_bytes)
            .sum::<usize>();
        assert_eq!(
            allocations
                .iter()
                .map(super::super::Backing::bytes)
                .sum::<usize>()
                + duplicated,
            ty.descriptor_bytes()
        );
        let resource = ty.variant_payload(1).unwrap()[1].logical();
        let mut found = 0;
        resource.visit_descriptor_backings(&mut |backing| {
            assert!(allocations.contains(&backing));
            assert_eq!(backing.bytes(), 256);
            found += 1;
            true
        });
        assert_eq!(found, 1);
        // A ledger already retaining both top-level allocations does not visit
        // their children again. Releasing them follows the same graph edges.
        let mut roots = 0;
        ty.visit_descriptor_backings(&mut |_| {
            roots += 1;
            false
        });
        assert_eq!(roots, 2);
    }

    #[test]
    fn canonical_layouts_preserve_complete_children_and_clone_equality() {
        for spelling in [
            "bool@native.bool/0",
            "field:koala-bear@plonky3.koala-bear/0",
            "table:bls12-381.fr@arkworks.mle-msb/0",
            "sequence<bool>@logical.sequence/0",
            "sequence<sequence<bool>>@logical.sequence/0",
            "sequence<table:bls12-381.fr>@logical.sequence/0[arkworks.mle-msb/0]",
            "sequence<sequence<table:bls12-381.fr>>@logical.sequence/0[logical.sequence/0[arkworks.mle-msb/0]]",
            "field_array<bls12-381.fr,0>@arkworks.field-array/0",
            "fixed_vector<field:koala-bear,2>@plonky3.fixed-vector/0",
        ] {
            let ty = PhysicalType::parse(spelling).unwrap();
            assert_eq!(ty.spelling(), spelling);
            assert_eq!(ty.clone(), ty);
            assert_eq!(PhysicalType::parse(&ty.spelling()).unwrap(), ty);
            if ty.kind() == Type::Sequence {
                let child = ty.sequence_element().unwrap();
                assert_eq!(ty.children().unwrap(), std::slice::from_ref(child));
                assert_eq!(ty.logical().sequence_element().unwrap(), child.logical());
            }
        }
    }
    #[test]
    fn noncanonical_layout_syntax_refuses_without_normalization() {
        for spelling in [
            "bool:native@native.bool/0",
            "bool:@native.bool/0",
            "bool@native.bool/0[]",
            "bool@native.bool/0]",
            "bool@native.bool/0,native.bool/0",
            "bool@native.bool/0@native.bool/0",
            "bool@ native.bool/0",
            "bool@native.bool/0\n",
            "bool@native.bool/00",
            "sequence<bool>@logical.sequence/0[native.bool/0]",
            "sequence<sequence<bool>>@logical.sequence/0[logical.sequence/0]",
            "sequence<bool>@logical.sequence/0[]",
            "sequence<bool>@logical.sequence/0[native.index/0]",
            "sequence<bool>@logical.sequence/0[native.bool/0,native.bool/0]",
            "sequence<table:bls12-381.fr>@logical.sequence/0[arkworks.mle-msb/0",
            "sequence<table:bls12-381.fr>@logical.sequence/0[arkworks.mle-msb/0,]",
            "sequence<table:bls12-381.fr>@logical.sequence/0[arkworks.mle-msb/0]extra",
            "sequence<table:bls12-381.fr>@logical.sequence/0[arkworks.mle-msb/0]]",
            "field_array<bls12-381.fr,00>@arkworks.field-array/0",
            "field_array<bls12-381.fr,0>@arkworks.field-array/0[arkworks.fr/0]",
            "fixed_vector<field:koala-bear,2>@plonky3.fixed-vector/0[plonky3.koala-bear/0]",
        ] {
            assert!(PhysicalType::parse(spelling).is_err(), "{spelling}");
        }
        // Trusted formation must still return the exact representation name.
        assert!(
            PhysicalType::parse_with("bool@alias", |logical, _, _| {
                PhysicalType::new(logical, Representation::Bool)
            })
            .is_err()
        );
    }
    #[test]
    fn redundant_brackets_refuse_at_each_node_with_nondefault_siblings() {
        let empty = zkc_test_support::variants::logical("Empty", serde_json::json!([["unit", []]]));
        let logical = zkc_test_support::variants::logical(
            "Mixed",
            serde_json::json!([["items", ["sequence<bool>", &empty, "table:bls12-381.fr"]]]),
        );
        let canonical = format!(
            "{logical}@logical.variant/0[logical.sequence/0,logical.variant/0,arkworks.mle-msb/0]"
        );
        let ty = PhysicalType::parse(&canonical).unwrap();
        assert_eq!(ty.spelling(), canonical);
        assert_eq!(ty.variant_payload(0).unwrap().len(), 3);
        assert_eq!(ty.children().unwrap()[1].children(), Some([].as_slice()));
        for spelling in [
            format!("{empty}@logical.variant/0[]"),
            canonical.replace("logical.sequence/0,", "logical.sequence/0[native.bool/0],"),
            canonical.replace("logical.variant/0,", "logical.variant/0[],"),
        ] {
            let error = PhysicalType::parse(&spelling).unwrap_err();
            assert_eq!(error.code, ErrorCode::Representation);
            assert_eq!(error.detail, "noncanonical physical spelling");
        }
    }
    #[test]
    fn contributed_parent_storage_elides_only_default_children() {
        use super::super::{AggregateChildRule, ContractsBuilder, ExecutionPolicy};
        let mut builder = ContractsBuilder::empty();
        builder
            .add_aggregate_representation(
                "parser/sequence",
                Type::Sequence,
                AggregateChildRule::AnyAdmitted,
            )
            .unwrap();
        let contracts = builder.finish(ExecutionPolicy::general_purpose());
        let spelling = "sequence<bool>@parser/sequence";
        let ty = contracts.physical_type(spelling).unwrap();
        assert_eq!(ty.spelling(), spelling);
        assert_eq!(ty.clone(), ty);
        let error = contracts
            .physical_type("sequence<bool>@parser/sequence[native.bool/0]")
            .unwrap_err();
        assert_eq!(error.detail, "noncanonical physical spelling");
    }
    #[test]
    fn explicit_nondefault_layouts_keep_exact_shared_budgets() {
        let spelling = "sequence<table:bls12-381.fr>@logical.sequence/0[arkworks.mle-msb/0]";
        for nodes in [3, 4] {
            let mut budget = ParseBudget::new();
            budget.charge(TYPE_NODE_LIMIT - nodes).unwrap();
            let result = PhysicalType::parse_with_budget(spelling, &mut budget, &mut form);
            assert_eq!(result.is_ok(), nodes == 4);
            if nodes == 4 {
                assert_eq!(budget.remaining(), 0);
            }
        }
        let bytes = 512 + 256 + std::mem::size_of::<PhysicalType>();
        for available in [bytes - 1, bytes] {
            let mut budget = ParseBudget::new();
            budget
                .allocate(super::super::Limits::TYPE_BYTES - available)
                .unwrap();
            let result = PhysicalType::parse_with_budget(spelling, &mut budget, &mut form);
            assert_eq!(result.is_ok(), available == bytes);
            if let Err(error) = result {
                assert_eq!(error.code, ErrorCode::Limit);
                assert_eq!(error.detail, "type descriptor byte ceiling");
            }
        }
        let mut logical = "table:bls12-381.fr".to_owned();
        let mut layout = "arkworks.mle-msb/0".to_owned();
        for _ in 0..TYPE_DEPTH_LIMIT {
            logical = format!("sequence<{logical}>");
            layout = format!("logical.sequence/0[{layout}]");
        }
        assert!(PhysicalType::parse(&format!("{logical}@{layout}")).is_ok());
        assert!(
            PhysicalType::parse(&format!("sequence<{logical}>@logical.sequence/0[{layout}]"))
                .is_err()
        );
    }
    #[test]
    fn logical_and_layout_parsing_share_exact_node_and_allocation_bounds() {
        let spelling = "sequence<bool>@logical.sequence/0";
        for nodes in [3, 4] {
            let mut budget = ParseBudget::new();
            budget.charge(TYPE_NODE_LIMIT - nodes).unwrap();
            let result = PhysicalType::parse_with_budget(spelling, &mut budget, &mut form);
            assert_eq!(result.is_ok(), nodes == 4);
            if nodes == 4 {
                assert_eq!(budget.remaining(), 0)
            }
        }
        let bytes = 512 + 256 + std::mem::size_of::<PhysicalType>();
        for available in [bytes - 1, bytes] {
            let mut budget = ParseBudget::new();
            budget
                .allocate(super::super::Limits::TYPE_BYTES - available)
                .unwrap();
            let result = PhysicalType::parse_with_budget(spelling, &mut budget, &mut form);
            assert_eq!(result.is_ok(), available == bytes);
            if let Err(error) = result {
                assert_eq!(error.code, ErrorCode::Limit);
                assert_eq!(error.detail, "type descriptor byte ceiling")
            }
        }
    }
    #[test]
    fn omitted_layouts_cannot_reset_depth_or_cache_expanded_child_charges() {
        let leaf =
            zkc_test_support::variants::logical("Leaf", serde_json::json!([["item", ["bool"]]]));
        let logical = zkc_test_support::variants::logical(
            "Root",
            serde_json::json!([["items", [&leaf, &leaf]]]),
        );
        let spelling = format!("{logical}@logical.variant/0");
        // Logical root and two (variant,bool) subtrees, then the same physical tree.
        for nodes in [9, 10] {
            let mut budget = ParseBudget::new();
            budget.charge(TYPE_NODE_LIMIT - nodes).unwrap();
            assert_eq!(
                PhysicalType::parse_with_budget(&spelling, &mut budget, &mut form).is_ok(),
                nodes == 10
            );
        }
        let mut logical = "bool".to_owned();
        for _ in 0..TYPE_DEPTH_LIMIT {
            logical = format!("sequence<{logical}>");
        }
        let spelling = format!("{logical}@logical.sequence/0");
        assert!(PhysicalType::parse(&spelling).is_ok());
        let spelling = format!("sequence<{logical}>@logical.sequence/0");
        assert!(PhysicalType::parse(&spelling).is_err());
    }
}
