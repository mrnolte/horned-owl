//! EL's rule on property chains and ranges ([`crate::el::chain_range_violations`]),
//! kept up to date per chain.
//!
//! The ranges imposed on a property are those of the property and of its
//! super-properties. A range or a sub-property edge at a property changes
//! what is imposed on the property and on everything below it, so only the
//! chains whose super-property or last property lies below it are checked
//! again, at the next query.

use std::collections::{HashMap, HashSet};

use horned_owl::model::{
    AnnotatedComponent, ClassExpression, Component, ForIRI, ObjectPropertyExpression,
    SubObjectPropertyExpression,
};
use horned_owl::ontology::indexed::ForIndex;

use crate::Violation;

type Ope<A> = ObjectPropertyExpression<A>;

pub(crate) struct ChainRanges<A: ForIRI, AA: ForIndex<A>> {
    supers: HashMap<Ope<A>, HashMap<Ope<A>, usize>>,
    subs: HashMap<Ope<A>, HashMap<Ope<A>, usize>>,
    ranges: HashMap<Ope<A>, HashMap<ClassExpression<A>, usize>>,
    /// Each chain axiom with its last property and its super-property.
    chains: HashMap<AA, (Ope<A>, Ope<A>)>,
    /// The chains by their last property and by their super-property.
    by_property: HashMap<Ope<A>, HashSet<AA>>,
    violations: HashMap<AA, Vec<Violation<A>>>,
    total: usize,
    /// Properties below which the imposed ranges changed.
    dirty: HashSet<Ope<A>>,
    unchecked: HashSet<AA>,
}

impl<A: ForIRI, AA: ForIndex<A>> Default for ChainRanges<A, AA> {
    fn default() -> Self {
        ChainRanges {
            supers: HashMap::new(),
            subs: HashMap::new(),
            ranges: HashMap::new(),
            chains: HashMap::new(),
            by_property: HashMap::new(),
            violations: HashMap::new(),
            total: 0,
            dirty: HashSet::new(),
            unchecked: HashSet::new(),
        }
    }
}

impl<A: ForIRI, AA: ForIndex<A>> ChainRanges<A, AA> {
    /// Adds (`add`) or removes `member`.
    pub(crate) fn change(&mut self, member: &AA, add: bool) {
        let ac: &AnnotatedComponent<A> = member.borrow();
        match &ac.component {
            Component::SubObjectPropertyOf(x) => match &x.sub {
                SubObjectPropertyExpression::ObjectPropertyExpression(sub) => {
                    self.edge(sub, &x.sup, add)
                }
                SubObjectPropertyExpression::ObjectPropertyChain(chain) => {
                    if let Some(last) = chain.last() {
                        self.chain(member, last, &x.sup, add);
                    }
                }
            },
            Component::EquivalentObjectProperties(x) => {
                for a in &x.0 {
                    for b in &x.0 {
                        if a != b {
                            self.edge(a, b, add);
                        }
                    }
                }
            }
            Component::ObjectPropertyRange(x) => {
                step(
                    self.ranges
                        .entry(x.ope.clone())
                        .or_default()
                        .entry(x.ce.clone())
                        .or_default(),
                    add,
                );
                prune(&mut self.ranges, &x.ope);
                self.dirty.insert(x.ope.clone());
            }
            _ => {}
        }
    }

    fn edge(&mut self, sub: &Ope<A>, sup: &Ope<A>, add: bool) {
        step(
            self.supers
                .entry(sub.clone())
                .or_default()
                .entry(sup.clone())
                .or_default(),
            add,
        );
        step(
            self.subs
                .entry(sup.clone())
                .or_default()
                .entry(sub.clone())
                .or_default(),
            add,
        );
        prune(&mut self.supers, sub);
        prune(&mut self.subs, sup);
        self.dirty.insert(sub.clone());
    }

    fn chain(&mut self, member: &AA, last: &Ope<A>, sup: &Ope<A>, add: bool) {
        if add {
            self.chains
                .insert(member.clone(), (last.clone(), sup.clone()));
            for p in [last, sup] {
                self.by_property
                    .entry(p.clone())
                    .or_default()
                    .insert(member.clone());
            }
            self.unchecked.insert(member.clone());
        } else {
            let ac: &AnnotatedComponent<A> = member.borrow();
            self.chains.remove(ac);
            for p in [last, sup] {
                if let Some(set) = self.by_property.get_mut(p) {
                    set.remove(ac);
                    if set.is_empty() {
                        self.by_property.remove(p);
                    }
                }
            }
            self.unchecked.remove(ac);
            if let Some(old) = self.violations.remove(ac) {
                self.total -= old.len();
            }
        }
    }

    /// Checks the chains the changes since the last call may affect.
    pub(crate) fn update(&mut self) {
        let mut affected: HashSet<AA> = std::mem::take(&mut self.unchecked);
        let dirty: Vec<Ope<A>> = self.dirty.drain().collect();
        let mut below: HashSet<&Ope<A>> = HashSet::new();
        let mut todo: Vec<&Ope<A>> = dirty.iter().collect();
        while let Some(p) = todo.pop() {
            if below.insert(p) {
                todo.extend(self.subs.get(p).into_iter().flat_map(|m| m.keys()));
            }
        }
        for p in below {
            affected.extend(self.by_property.get(p).into_iter().flatten().cloned());
        }
        for member in affected {
            let Some((last, sup)) = self.chains.get(member.borrow()) else {
                continue;
            };
            let on_last = self.imposed(last);
            let mut missing: Vec<&ClassExpression<A>> = self
                .imposed(sup)
                .into_iter()
                .filter(|ce| !on_last.contains(ce))
                .collect();
            missing.sort();
            let ac: &AnnotatedComponent<A> = member.borrow();
            let found: Vec<Violation<A>> = missing
                .into_iter()
                .map(
                    |ce| Violation::UseOfPropertyChainWithoutRangeOnLastProperty {
                        axiom: ac.clone(),
                        ce: ce.clone(),
                    },
                )
                .collect();
            self.total += found.len();
            if let Some(old) = self.violations.insert(member.clone(), found) {
                self.total -= old.len();
            }
        }
    }

    fn imposed(&self, p: &Ope<A>) -> HashSet<&ClassExpression<A>> {
        let mut seen: HashSet<&Ope<A>> = HashSet::new();
        let mut todo = vec![p];
        let mut out = HashSet::new();
        while let Some(p) = todo.pop() {
            if seen.insert(p) {
                out.extend(self.ranges.get(p).into_iter().flat_map(|m| m.keys()));
                todo.extend(self.supers.get(p).into_iter().flat_map(|m| m.keys()));
            }
        }
        out
    }

    /// The number of violations, as of the last [`update`](Self::update).
    pub(crate) fn count(&self) -> usize {
        self.total
    }

    pub(crate) fn violations(&self) -> impl Iterator<Item = &Violation<A>> {
        self.violations.values().flatten()
    }
}

fn step(n: &mut usize, add: bool) {
    if add {
        *n += 1;
    } else {
        *n -= 1;
    }
}

/// Removes the entries of `key` that counted down to zero.
fn prune<K: Clone + Eq + std::hash::Hash, V: Eq + std::hash::Hash>(
    map: &mut HashMap<K, HashMap<V, usize>>,
    key: &K,
) {
    if let Some(m) = map.get_mut(key) {
        m.retain(|_, n| *n > 0);
        if m.is_empty() {
            map.remove(key);
        }
    }
}
