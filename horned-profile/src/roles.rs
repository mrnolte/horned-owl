//! Which object properties are composite (non-simple), kept up to date as
//! role axioms come and go.
//!
//! The same rules as [`crate::simple_property`], on named properties: a
//! property and its inverse are always both simple or both composite, so
//! the graph has one node per named property. A property is composite if it
//! is transitive or the super-property of a chain of length two or more
//! (its *reasons*), or if a sub-property of it is composite. Sub-property
//! edges come from `SubObjectPropertyOf` (a chain of length one counts as a
//! plain sub-property), both directions of `EquivalentObjectProperties` and
//! of `InverseObjectProperties`.
//!
//! Adding a reason or an edge can only make properties composite: the
//! change is carried upwards from where it starts, and nothing else is
//! visited. Removing one can only make properties simple, and only those
//! reachable from where it ends: they are taken out and those that still
//! have a reason, or a composite sub-property outside them, are put back.
//! Reasons and edges are counted, so an axiom only matters once no other
//! axiom gives the same reason or edge.

use std::collections::{HashMap, HashSet, VecDeque};

use horned_owl::model::{
    Component, ForIRI, ObjectProperty, ObjectPropertyExpression, SubObjectPropertyExpression,
};

/// What one axiom contributes to the role hierarchy.
pub(crate) struct RoleFacts<A: ForIRI> {
    reasons: Vec<ObjectProperty<A>>,
    edges: Vec<(ObjectProperty<A>, ObjectProperty<A>)>,
}

impl<A: ForIRI> RoleFacts<A> {
    pub(crate) fn of(c: &Component<A>) -> Self {
        let mut facts = RoleFacts {
            reasons: Vec::new(),
            edges: Vec::new(),
        };
        match c {
            Component::TransitiveObjectProperty(x) => facts.reasons.push(base(&x.0)),
            Component::SubObjectPropertyOf(x) => match &x.sub {
                SubObjectPropertyExpression::ObjectPropertyChain(chain) if chain.len() >= 2 => {
                    facts.reasons.push(base(&x.sup))
                }
                SubObjectPropertyExpression::ObjectPropertyChain(chain) => {
                    if let Some(single) = chain.first() {
                        facts.edges.push((base(single), base(&x.sup)));
                    }
                }
                SubObjectPropertyExpression::ObjectPropertyExpression(sub) => {
                    facts.edges.push((base(sub), base(&x.sup)))
                }
            },
            Component::EquivalentObjectProperties(x) => {
                for a in &x.0 {
                    for b in &x.0 {
                        if a != b {
                            facts.edges.push((base(a), base(b)));
                        }
                    }
                }
            }
            Component::InverseObjectProperties(x) => {
                facts.edges.push((x.0.clone(), x.1.clone()));
                facts.edges.push((x.1.clone(), x.0.clone()));
            }
            _ => {}
        }
        facts
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.reasons.is_empty() && self.edges.is_empty()
    }
}

/// The named property of `ope`.
pub(crate) fn base<A: ForIRI>(ope: &ObjectPropertyExpression<A>) -> ObjectProperty<A> {
    match ope {
        ObjectPropertyExpression::ObjectProperty(p)
        | ObjectPropertyExpression::InverseObjectProperty(p) => p.clone(),
    }
}

/// The composite properties, with what makes them so.
pub(crate) struct SimpleRoles<A: ForIRI> {
    reasons: HashMap<ObjectProperty<A>, usize>,
    up: HashMap<ObjectProperty<A>, HashMap<ObjectProperty<A>, usize>>,
    down: HashMap<ObjectProperty<A>, HashMap<ObjectProperty<A>, usize>>,
    composite: HashSet<ObjectProperty<A>>,
}

impl<A: ForIRI> Default for SimpleRoles<A> {
    fn default() -> Self {
        SimpleRoles {
            reasons: HashMap::new(),
            up: HashMap::new(),
            down: HashMap::new(),
            composite: HashSet::new(),
        }
    }
}

impl<A: ForIRI> SimpleRoles<A> {
    pub(crate) fn is_composite(&self, ope: &ObjectPropertyExpression<A>) -> bool {
        match ope {
            ObjectPropertyExpression::ObjectProperty(p)
            | ObjectPropertyExpression::InverseObjectProperty(p) => self.composite.contains(p),
        }
    }

    /// Adds `facts`; returns the properties that became composite.
    pub(crate) fn add(&mut self, facts: &RoleFacts<A>) -> Vec<ObjectProperty<A>> {
        let mut start = Vec::new();
        for p in &facts.reasons {
            *self.reasons.entry(p.clone()).or_default() += 1;
            start.push(p.clone());
        }
        for (sub, sup) in &facts.edges {
            *count(&mut self.up, sub, sup) += 1;
            *count(&mut self.down, sup, sub) += 1;
            if self.composite.contains(sub) {
                start.push(sup.clone());
            }
        }
        let mut became = Vec::new();
        let mut todo: VecDeque<ObjectProperty<A>> = start.into();
        while let Some(p) = todo.pop_front() {
            if self.composite.insert(p.clone()) {
                todo.extend(
                    self.up
                        .get(&p)
                        .into_iter()
                        .flat_map(|sups| sups.keys().cloned()),
                );
                became.push(p);
            }
        }
        became
    }

    /// Removes `facts`; returns the properties that became simple.
    pub(crate) fn remove(&mut self, facts: &RoleFacts<A>) -> Vec<ObjectProperty<A>> {
        let mut roots = Vec::new();
        for p in &facts.reasons {
            if decrement(self.reasons.get_mut(p)) {
                self.reasons.remove(p);
                roots.push(p.clone());
            }
        }
        for (sub, sup) in &facts.edges {
            let last = decrement(self.up.get_mut(sub).and_then(|m| m.get_mut(sup)));
            decrement(self.down.get_mut(sup).and_then(|m| m.get_mut(sub)));
            if last {
                forget(&mut self.up, sub, sup);
                forget(&mut self.down, sup, sub);
                roots.push(sup.clone());
            }
        }
        // What may lose its status: the composite properties reachable from
        // the roots.
        let mut suspect: HashSet<ObjectProperty<A>> = HashSet::new();
        let mut todo: Vec<ObjectProperty<A>> = roots
            .into_iter()
            .filter(|p| self.composite.contains(p))
            .collect();
        while let Some(p) = todo.pop() {
            if self.composite.contains(&p) && suspect.insert(p.clone()) {
                todo.extend(
                    self.up
                        .get(&p)
                        .into_iter()
                        .flat_map(|sups| sups.keys().cloned()),
                );
            }
        }
        for p in &suspect {
            self.composite.remove(p);
        }
        // Put back what still has a reason or a composite sub-property.
        let mut todo: VecDeque<ObjectProperty<A>> = suspect
            .iter()
            .filter(|p| {
                self.reasons.contains_key(*p)
                    || self
                        .down
                        .get(*p)
                        .is_some_and(|subs| subs.keys().any(|sub| self.composite.contains(sub)))
            })
            .cloned()
            .collect();
        while let Some(p) = todo.pop_front() {
            if self.composite.insert(p.clone()) {
                todo.extend(
                    self.up
                        .get(&p)
                        .into_iter()
                        .flat_map(|sups| sups.keys())
                        .filter(|sup| suspect.contains(*sup))
                        .cloned(),
                );
            }
        }
        suspect
            .into_iter()
            .filter(|p| !self.composite.contains(p))
            .collect()
    }
}

fn count<'a, K: Clone + Eq + std::hash::Hash>(
    map: &'a mut HashMap<K, HashMap<K, usize>>,
    from: &K,
    to: &K,
) -> &'a mut usize {
    map.entry(from.clone())
        .or_default()
        .entry(to.clone())
        .or_default()
}

/// Counts one down; `true` if that was the last.
fn decrement(n: Option<&mut usize>) -> bool {
    match n {
        Some(n) => {
            *n -= 1;
            *n == 0
        }
        None => false,
    }
}

fn forget<K: Eq + std::hash::Hash>(map: &mut HashMap<K, HashMap<K, usize>>, from: &K, to: &K) {
    if let Some(m) = map.get_mut(from) {
        m.remove(to);
        if m.is_empty() {
            map.remove(from);
        }
    }
}

/// The edges of the property chain graph that regularity looks at: each
/// chain member to the super-property, counted.
pub(crate) fn chain_edges<A: ForIRI>(
    c: &Component<A>,
) -> Vec<(ObjectProperty<A>, ObjectProperty<A>)> {
    match c {
        Component::SubObjectPropertyOf(x) => match &x.sub {
            SubObjectPropertyExpression::ObjectPropertyChain(chain) if chain.len() >= 2 => {
                let sup = base(&x.sup);
                chain
                    .iter()
                    .map(base)
                    .filter(|member| *member != sup)
                    .map(|member| (member, sup.clone()))
                    .collect()
            }
            _ => Vec::new(),
        },
        _ => Vec::new(),
    }
}

#[cfg(test)]
mod test {
    use super::{RoleFacts, SimpleRoles};
    use horned_owl::model::{
        Build, Component, EquivalentObjectProperties, ObjectPropertyExpression, RcStr,
        SubObjectPropertyExpression, SubObjectPropertyOf, TransitiveObjectProperty,
    };

    fn p(b: &Build<RcStr>, name: &str) -> ObjectPropertyExpression<RcStr> {
        b.object_property(format!("http://example.com/{name}"))
            .into()
    }

    fn sub(
        a: &ObjectPropertyExpression<RcStr>,
        b: &ObjectPropertyExpression<RcStr>,
    ) -> RoleFacts<RcStr> {
        RoleFacts::of(&Component::SubObjectPropertyOf(SubObjectPropertyOf {
            sub: SubObjectPropertyExpression::ObjectPropertyExpression(a.clone()),
            sup: b.clone(),
        }))
    }

    fn trans(a: &ObjectPropertyExpression<RcStr>) -> RoleFacts<RcStr> {
        RoleFacts::of(&Component::TransitiveObjectProperty(
            TransitiveObjectProperty(a.clone()),
        ))
    }

    #[test]
    fn a_cycle_becomes_simple_again_when_its_reason_goes() {
        let b = Build::new_rc();
        let (x, y) = (p(&b, "x"), p(&b, "y"));
        let mut roles = SimpleRoles::default();
        roles.add(&sub(&x, &y));
        roles.add(&sub(&y, &x));
        assert_eq!(roles.add(&trans(&x)).len(), 2);
        assert!(roles.is_composite(&y));
        assert_eq!(roles.remove(&trans(&x)).len(), 2);
        assert!(!roles.is_composite(&x) && !roles.is_composite(&y));
    }

    #[test]
    fn another_path_keeps_a_property_composite() {
        let b = Build::new_rc();
        let (a, c, d) = (p(&b, "a"), p(&b, "c"), p(&b, "d"));
        let mut roles = SimpleRoles::default();
        roles.add(&trans(&a));
        roles.add(&trans(&d));
        roles.add(&sub(&a, &c));
        roles.add(&sub(&d, &c));
        assert_eq!(roles.remove(&trans(&a)).len(), 1, "only a turns simple");
        assert!(roles.is_composite(&c));
        let equivalent = RoleFacts::of(&Component::EquivalentObjectProperties(
            EquivalentObjectProperties(vec![a.clone(), c.clone()]),
        ));
        assert_eq!(roles.add(&equivalent).len(), 1, "a again, through c");
        assert!(roles.is_composite(&a));
    }

    #[test]
    fn an_edge_given_twice_stays_until_both_go() {
        let b = Build::new_rc();
        let (x, y) = (p(&b, "x"), p(&b, "y"));
        let mut roles = SimpleRoles::default();
        roles.add(&trans(&x));
        roles.add(&sub(&x, &y));
        roles.add(&sub(&x, &y));
        assert!(roles.remove(&sub(&x, &y)).is_empty());
        assert_eq!(roles.remove(&sub(&x, &y)).len(), 1);
    }
}
