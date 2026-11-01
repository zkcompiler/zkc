//! Independent static coverage and scope checks for compact execution schedules.
use super::{Bundle, BundleError, Step, bundle::Segment};
use crate::vm::ProgramAction;
use std::collections::{BTreeMap, BTreeSet};

type Result<T> = std::result::Result<T, BundleError>;
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Scope {
    Root,
    Loop(usize),
    Branch(usize, usize),
}
// None marks a role that does not participate in this region.
type Scopes = [Option<Scope>];

struct Check<'a> {
    bundle: &'a Bundle,
    parents: Vec<Vec<Scope>>,
    next_anchor: usize,
    control_headers: BTreeMap<String, Vec<(usize, usize)>>,
    visited_controls: BTreeSet<String>,
}
impl Bundle {
    pub(super) fn validate_segments(&self) -> Result<()> {
        let mut parents = Vec::new();
        let mut control_headers = BTreeMap::<String, Vec<(usize, usize)>>::new();
        fn regions(
            actions: &[ProgramAction],
            role: usize,
            start: usize,
            end: usize,
            scope: Scope,
            parents: &mut [Scope],
            headers: &mut BTreeMap<String, Vec<(usize, usize)>>,
        ) -> Result<()> {
            let mut index = start;
            while index < end {
                parents[index] = scope;
                match &actions[index] {
                    ProgramAction::Loop {
                        site, end: last, ..
                    } => {
                        if *last <= index
                            || *last >= end
                            || !matches!(&actions[*last], ProgramAction::Yield { site: s } if s == site)
                        {
                            return Err(BundleError::Coverage);
                        }
                        headers.entry(site.clone()).or_default().push((role, index));
                        regions(
                            actions,
                            role,
                            index + 1,
                            *last,
                            Scope::Loop(index),
                            parents,
                            headers,
                        )?;
                        parents[*last] = Scope::Loop(index);
                        index = *last + 1;
                    }
                    ProgramAction::Branch {
                        site,
                        alternatives,
                        ends,
                    } => {
                        if alternatives.is_empty() || alternatives.len() != ends.len() {
                            return Err(BundleError::Coverage);
                        }
                        headers.entry(site.clone()).or_default().push((role, index));
                        let mut first = index + 1;
                        for (arm, last) in ends.iter().enumerate() {
                            if *last < first
                                || *last >= end
                                || !matches!(&actions[*last], ProgramAction::Yield { site:s } if s == site)
                            {
                                return Err(BundleError::Coverage);
                            }
                            regions(
                                actions,
                                role,
                                first,
                                *last,
                                Scope::Branch(index, arm),
                                parents,
                                headers,
                            )?;
                            parents[*last] = Scope::Branch(index, arm);
                            first = *last + 1;
                        }
                        index = first;
                    }
                    ProgramAction::Yield { .. } => return Err(BundleError::Coverage),
                    ProgramAction::Finish if scope != Scope::Root => {
                        return Err(BundleError::Coverage);
                    }
                    _ => index += 1,
                }
            }
            Ok(())
        }
        for (role_index, role) in self.roles.iter().enumerate() {
            let mut local = vec![Scope::Root; role.actions.len()];
            regions(
                &role.actions,
                role_index,
                0,
                role.actions.len(),
                Scope::Root,
                &mut local,
                &mut control_headers,
            )?;
            parents.push(local);
        }
        let mut check = Check {
            bundle: self,
            parents,
            next_anchor: 0,
            control_headers,
            visited_controls: BTreeSet::new(),
        };
        check.block(
            &self.segments,
            &vec![Some(Scope::Root); self.roles.len()],
            true,
        )
    }
}
impl Check<'_> {
    fn step(&self, index: usize, scopes: &Scopes) -> Result<Step> {
        let step = *self.bundle.steps.get(index).ok_or(BundleError::Coverage)?;
        let scope = scopes
            .get(step.role)
            .copied()
            .flatten()
            .ok_or(BundleError::Coverage)?;
        if self.parents[step.role].get(step.instruction) != Some(&scope) {
            return Err(BundleError::Coverage);
        }
        Ok(step)
    }
    fn action(&self, step: &Step) -> &ProgramAction {
        self.bundle.action(step).expect("coverage checked")
    }
    fn tail(
        &self,
        indices: &[usize],
        scopes: &Scopes,
        loops: Option<&[(usize, usize)]>,
    ) -> Result<()> {
        let roles: Vec<_> = scopes
            .iter()
            .enumerate()
            .filter_map(|(i, scope)| scope.map(|_| i))
            .collect();
        let mut cursor = 0;
        for role in roles {
            let mut step = self.step(*indices.get(cursor).ok_or(BundleError::Shape)?, scopes)?;
            if step.role == role
                && step.anchor.is_none()
                && matches!(self.action(&step), ProgramAction::Local { .. })
            {
                cursor += 1;
                step = self.step(*indices.get(cursor).ok_or(BundleError::Shape)?, scopes)?;
            }
            if step.role != role || step.anchor.is_some() {
                return Err(BundleError::Shape);
            }
            match loops {
                None if matches!(self.action(&step), ProgramAction::Finish) => {}
                Some(ends)
                    if ends.contains(&(role, step.instruction))
                        && matches!(self.action(&step), ProgramAction::Yield { .. }) => {}
                _ => return Err(BundleError::Shape),
            }
            cursor += 1;
        }
        if cursor != indices.len() {
            return Err(BundleError::Shape);
        }
        Ok(())
    }
    fn block(&mut self, nodes: &[Segment], scopes: &Scopes, root: bool) -> Result<()> {
        let mut cursor = 0;
        while cursor < nodes.len() {
            match &nodes[cursor] {
                Segment::Action(index) => {
                    let first = self.step(*index, scopes)?;
                    if first.anchor.is_none() {
                        if !root {
                            return Err(BundleError::Shape);
                        }
                        let tail = nodes[cursor..]
                            .iter()
                            .map(|node| match node {
                                Segment::Action(i) => Ok(*i),
                                _ => Err(BundleError::Shape),
                            })
                            .collect::<Result<Vec<_>>>()?;
                        return self.tail(&tail, scopes, None);
                    }
                    if first.anchor != Some(self.next_anchor) {
                        return Err(BundleError::Shape);
                    }
                    self.next_anchor += 1;
                    let mut group = Vec::new();
                    while let Some(Segment::Action(index)) = nodes.get(cursor) {
                        let step = self.step(*index, scopes)?;
                        if step.anchor != first.anchor {
                            break;
                        }
                        group.push(step);
                        cursor += 1;
                    }
                    self.bundle.group(&group)?;
                }
                Segment::Branch { entries, arms } => {
                    let mut headers = Vec::new();
                    let mut ends_by_role = Vec::new();
                    let mut position = 0;
                    let mut previous = None;
                    let mut identity = None;
                    while position < entries.len() {
                        let mut step = self.step(entries[position], scopes)?;
                        let role = step.role;
                        if previous.is_some_and(|p| p >= role)
                            || step.anchor != Some(self.next_anchor)
                        {
                            return Err(BundleError::Shape);
                        }
                        previous = Some(role);
                        if matches!(self.action(&step), ProgramAction::Local { .. }) {
                            position += 1;
                            step = self
                                .step(*entries.get(position).ok_or(BundleError::Shape)?, scopes)?;
                        }
                        if step.role != role || step.anchor != Some(self.next_anchor) {
                            return Err(BundleError::Shape);
                        }
                        let ProgramAction::Branch {
                            site,
                            alternatives,
                            ends,
                        } = self.action(&step)
                        else {
                            return Err(BundleError::Shape);
                        };
                        let current = (site.clone(), alternatives.clone());
                        if identity.as_ref().is_some_and(|old| old != &current) {
                            return Err(BundleError::Shape);
                        }
                        identity = Some(current);
                        headers.push((role, step.instruction));
                        ends_by_role.push((role, ends.clone()));
                        position += 1;
                    }
                    let Some((site, alternatives)) = identity else {
                        return Err(BundleError::Shape);
                    };
                    if self.control_headers.get(&site) != Some(&headers)
                        || !self.visited_controls.insert(site)
                    {
                        return Err(BundleError::Coverage);
                    }
                    if arms.len() != alternatives.len() {
                        return Err(BundleError::Shape);
                    }
                    self.next_anchor += 1;
                    for (arm_index, (arm, alternative)) in arms.iter().zip(alternatives).enumerate()
                    {
                        if arm.alternative != alternative {
                            return Err(BundleError::Shape);
                        }
                        let mut children = vec![None; scopes.len()];
                        for (role, header) in &headers {
                            children[*role] = Some(Scope::Branch(*header, arm_index));
                        }
                        let ends = ends_by_role
                            .iter()
                            .map(|(role, ends)| (*role, ends[arm_index]))
                            .collect::<Vec<_>>();
                        self.block(&arm.body, &children, false)?;
                        self.tail(&arm.exits, &children, Some(&ends))?;
                    }
                    cursor += 1;
                }
                Segment::Loop {
                    entries,
                    body,
                    exits,
                } => {
                    let mut children = vec![None; scopes.len()];
                    let mut ends = Vec::new();
                    let mut headers = Vec::new();
                    let mut position = 0;
                    let mut previous = None;
                    let mut identity = None;
                    while position < entries.len() {
                        let mut step = self.step(entries[position], scopes)?;
                        let role = step.role;
                        if previous.is_some_and(|p| p >= role)
                            || step.anchor != Some(self.next_anchor)
                        {
                            return Err(BundleError::Shape);
                        }
                        previous = Some(role);
                        if matches!(self.action(&step), ProgramAction::Local { .. }) {
                            position += 1;
                            step = self
                                .step(*entries.get(position).ok_or(BundleError::Shape)?, scopes)?;
                        }
                        if step.role != role || step.anchor != Some(self.next_anchor) {
                            return Err(BundleError::Shape);
                        }
                        let ProgramAction::Loop { site, maximum, end } = self.action(&step) else {
                            return Err(BundleError::Shape);
                        };
                        let current = (site.clone(), *maximum);
                        if identity.as_ref().is_some_and(|old| old != &current) {
                            return Err(BundleError::Shape);
                        }
                        identity = Some(current);
                        children[role] = Some(Scope::Loop(step.instruction));
                        ends.push((role, *end));
                        headers.push((role, step.instruction));
                        position += 1;
                    }
                    let Some((site, _)) = identity else {
                        return Err(BundleError::Shape);
                    };
                    if self.control_headers.get(&site) != Some(&headers)
                        || !self.visited_controls.insert(site)
                    {
                        return Err(BundleError::Coverage);
                    }
                    self.next_anchor += 1;
                    self.block(body, &children, false)?;
                    self.tail(exits, &children, Some(&ends))?;
                    cursor += 1;
                }
            }
        }
        if root {
            return Err(BundleError::Shape);
        }
        Ok(())
    }
}
