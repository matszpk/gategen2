// boolexpr_creator.rs - boolean expression creator.

#![cfg_attr(docsrs, feature(doc_cfg))]
//! The module to generate Gate circuits from boolean expressions.
//!
//! It defines the ExprCreator - main structure to create and hold boolean expressions.

use std::cell::RefCell;
use std::collections::HashMap;
use std::fmt::Debug;
use std::ops::Neg;
use std::rc::Rc;

use crate::gate::{Literal, VarLit};

use crate::gatesim::{Circuit, Gate};

#[cfg(test)]
macro_rules! test_println {
    () => { println!(); };
    ($($arg:tt)*) => { println!($($arg)*); };
}

#[cfg(not(test))]
macro_rules! test_println {
    () => {};
    ($($arg:tt)*) => {};
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Node<T: VarLit + Debug> {
    Single(Literal<T>),
    Negated(usize),
    And(usize, usize),
    Or(usize, usize),
    Xor(usize, usize),
    Equal(usize, usize),
    Impl(usize, usize),
}

impl<T: VarLit + Debug> Node<T> {
    fn first_path(&self) -> usize {
        match *self {
            Node::Single(_) => panic!("No first path for single node"),
            Node::Negated(first) => first,
            Node::And(first, _) => first,
            Node::Or(first, _) => first,
            Node::Xor(first, _) => first,
            Node::Equal(first, _) => first,
            Node::Impl(first, _) => first,
        }
    }

    fn second_path(&self) -> usize {
        match *self {
            Node::And(_, second) => second,
            Node::Or(_, second) => second,
            Node::Xor(_, second) => second,
            Node::Equal(_, second) => second,
            Node::Impl(_, second) => second,
            _ => panic!("No second path for single node"),
        }
    }

    #[inline]
    fn is_single(&self) -> bool {
        matches!(self, Node::Single(_))
    }

    #[inline]
    fn is_unary(&self) -> bool {
        matches!(self, Node::Single(_) | Node::Negated(_))
    }
}

/// The ExprCreator holds all expressions which will be written later.
///
/// Main purpose of ExprCreator is maintenance state of expression with its variables
/// during creating that expression by using ExprNode.
/// An ExprCreator is used with ExprNode to create new expression.
///
/// The generic parameter T is variable literal type - it can be signed integer.
#[derive(Debug, PartialEq, Eq)]
pub struct ExprCreator<T: VarLit + Debug> {
    pub(super) nodes: Vec<Node<T>>,
    pub(super) lit_to_index: Vec<usize>,
    pub(super) history_order: bool,
}

// macro to create new_* methods for ExprCreator.
macro_rules! new_xxx {
    ($t:ident, $u:ident) => {
        pub(super) fn $t(&mut self, a_index: usize, b_index: usize) -> usize {
            assert!(a_index < self.nodes.len());
            assert!(b_index < self.nodes.len());
            self.nodes.push(Node::$u(a_index, b_index));
            self.nodes.len() - 1
        }
    };
}

impl<T> ExprCreator<T>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    /// Creates new ExprCreator as returns it as RefCounter.
    pub fn new() -> Rc<RefCell<Self>> {
        Rc::new(RefCell::new(ExprCreator {
            nodes: vec![
                Node::Single(Literal::Value(false)),
                Node::Single(Literal::Value(true)),
            ],
            lit_to_index: vec![],
            history_order: false,
        }))
    }

    /// Creates new ExprCreator with history order as returns it as RefCounter.
    ///
    /// Returned ExprCreator converts expression to circuit using historical order
    /// (not tree order from outputs to inputs).
    pub fn with_history_order() -> Rc<RefCell<Self>> {
        Rc::new(RefCell::new(ExprCreator {
            nodes: vec![
                Node::Single(Literal::Value(false)),
                Node::Single(Literal::Value(true)),
            ],
            lit_to_index: vec![],
            history_order: true,
        }))
    }

    /// Returns variable count.
    #[inline]
    pub fn var_count(&self) -> T {
        T::from_usize(self.lit_to_index.len() >> 1)
    }

    pub(super) fn new_variable(&mut self) -> Literal<T> {
        self.lit_to_index.push(0); // zero - no variable
        self.lit_to_index.push(0);
        Literal::from(self.var_count())
    }

    pub(super) fn single(&mut self, l: impl Into<Literal<T>>) -> usize {
        match l.into() {
            Literal::Value(false) => 0,
            Literal::Value(true) => 1,
            Literal::VarLit(ll) => {
                assert!(ll.positive().unwrap() <= self.var_count());
                let ltoi =
                    ((ll.positive().unwrap().to_usize() - 1) << 1) + usize::from(ll < T::empty());
                let node_index = self.lit_to_index[ltoi];
                if node_index != 0 {
                    node_index
                } else {
                    self.nodes.push(Node::Single(Literal::VarLit(ll)));
                    self.lit_to_index[ltoi] = self.nodes.len() - 1;
                    self.nodes.len() - 1
                }
            }
        }
    }

    pub(super) fn new_not(&mut self, index: usize) -> usize {
        assert!(index < self.nodes.len());
        self.nodes.push(Node::Negated(index));
        self.nodes.len() - 1
    }

    new_xxx!(new_and, And);
    new_xxx!(new_or, Or);
    new_xxx!(new_xor, Xor);
    new_xxx!(new_equal, Equal);
    new_xxx!(new_impl, Impl);

    fn to_circuit_normal(
        &self,
        outputs: impl IntoIterator<Item = usize>,
    ) -> (
        Circuit<<T as VarLit>::Unsigned>,
        HashMap<T, <T as VarLit>::Unsigned>,
    )
    where
        T: std::hash::Hash,
        <T as VarLit>::Unsigned: Clone + Copy + PartialEq + Eq + PartialOrd + Ord + Default,
        <T as VarLit>::Unsigned: TryFrom<usize>,
        <<T as VarLit>::Unsigned as TryFrom<usize>>::Error: Debug,
        <T as VarLit>::Unsigned: Debug,
        usize: TryFrom<<T as VarLit>::Unsigned>,
        <usize as TryFrom<<T as VarLit>::Unsigned>>::Error: Debug,
    {
        type Unsigned<T> = <T as VarLit>::Unsigned;
        let mut input_map = HashMap::new();
        let outputs = Vec::from_iter(outputs);
        #[derive(Clone, Copy)]
        struct SimpleEntry {
            node_index: usize,
            path: usize,
        }
        impl SimpleEntry {
            #[inline]
            fn new(start: usize) -> Self {
                Self {
                    node_index: start,
                    path: 0,
                }
            }
        }
        let mut visited = vec![false; self.nodes.len()];
        // collect inputs
        for start in &outputs {
            if *start == 0 || *start == 1 {
                // skip single values
                continue;
            }
            let mut stack = vec![SimpleEntry::new(*start)];
            while !stack.is_empty() {
                let top = stack.last_mut().unwrap();
                let node_index = top.node_index;
                let node = self.nodes[top.node_index];
                let first_path = top.path == 0 && !node.is_single();
                let second_path = top.path == 1 && !node.is_unary();
                if !first_path || !visited[node_index] {
                    if first_path {
                        visited[node_index] = true;
                    }
                    match node {
                        Node::Single(l) => {
                            if let Some(l) = l.varlit() {
                                let lp = l.positive().unwrap();
                                if !input_map.contains_key(&lp) {
                                    input_map.insert(
                                        lp,
                                        Unsigned::<T>::try_from(input_map.len()).unwrap(),
                                    );
                                }
                            } else {
                                panic!("Unsupported!");
                            }
                        }
                        _ => {}
                    }
                    if first_path {
                        top.path = 1;
                        stack.push(SimpleEntry::new(node.first_path()));
                    } else if second_path {
                        top.path = 2;
                        stack.push(SimpleEntry::new(node.second_path()));
                    } else {
                        stack.pop();
                    }
                } else {
                    stack.pop();
                }
            }
        }

        // create circuit
        visited.fill(false);
        let mut gate_output_map = HashMap::<usize, (Unsigned<T>, bool)>::new();
        let input_len = input_map.len();
        let mut gates = vec![];
        let mut circ_outputs = vec![];
        for start in &outputs {
            if *start == 0 || *start == 1 {
                // skip single values
                continue;
            }
            let mut stack = vec![SimpleEntry::new(*start)];
            while !stack.is_empty() {
                let top = stack.last_mut().unwrap();
                let node_index = top.node_index;
                let node = self.nodes[top.node_index];
                let first_path = top.path == 0 && !node.is_single();
                let second_path = top.path == 1 && !node.is_unary();

                let mut new_node = || {
                    match node {
                        Node::Single(l) => {
                            let l = l.varlit().unwrap();
                            let lit = input_map[&l.positive().unwrap()];
                            gate_output_map.insert(node_index, (lit, !l.is_positive()));
                        }
                        Node::Negated(fidx) => {
                            let (gi, n) = gate_output_map.get(&fidx).unwrap();
                            gate_output_map.insert(node_index, (*gi, !n));
                        }
                        Node::And(fidx, sidx) => {
                            let (gi1, n1) = gate_output_map.get(&fidx).unwrap();
                            let (gi2, n2) = gate_output_map.get(&sidx).unwrap();
                            let (gate, n) = if *n1 {
                                if *n2 {
                                    // and(!gi1,!gi2) -> nor(gi1,gi2)
                                    (Gate::new_nor(*gi1, *gi2), false)
                                } else {
                                    (Gate::new_nimpl(*gi2, *gi1), false)
                                }
                            } else if *n2 {
                                (Gate::new_nimpl(*gi1, *gi2), false)
                            } else {
                                (Gate::new_and(*gi1, *gi2), false)
                            };
                            let gate_idx = gates.len() + input_len;
                            gate_output_map.insert(
                                node_index,
                                (Unsigned::<T>::try_from(gate_idx).unwrap(), n),
                            );
                            gates.push(gate);
                        }
                        Node::Or(fidx, sidx) => {
                            let (gi1, n1) = gate_output_map.get(&fidx).unwrap();
                            let (gi2, n2) = gate_output_map.get(&sidx).unwrap();
                            let (gate, n) = if *n1 {
                                if *n2 {
                                    (Gate::new_and(*gi1, *gi2), true)
                                } else {
                                    (Gate::new_nimpl(*gi1, *gi2), true)
                                }
                            } else if *n2 {
                                (Gate::new_nimpl(*gi2, *gi1), true)
                            } else {
                                (Gate::new_nor(*gi1, *gi2), true)
                            };
                            let gate_idx = gates.len() + input_len;
                            gate_output_map.insert(
                                node_index,
                                (Unsigned::<T>::try_from(gate_idx).unwrap(), n),
                            );
                            gates.push(gate);
                        }
                        Node::Xor(fidx, sidx) | Node::Equal(fidx, sidx) => {
                            let (gi1, n1) = gate_output_map.get(&fidx).unwrap();
                            let (gi2, n2) = gate_output_map.get(&sidx).unwrap();
                            let neg = matches!(node, Node::Equal(_, _));
                            let (gate, n) = if *n1 {
                                if *n2 {
                                    // and(!gi1,!gi2) -> nor(gi1,gi2)
                                    (Gate::new_xor(*gi1, *gi2), neg)
                                } else {
                                    (Gate::new_xor(*gi1, *gi2), !neg)
                                }
                            } else if *n2 {
                                (Gate::new_xor(*gi1, *gi2), !neg)
                            } else {
                                (Gate::new_xor(*gi1, *gi2), neg)
                            };
                            let gate_idx = gates.len() + input_len;
                            gate_output_map.insert(
                                node_index,
                                (Unsigned::<T>::try_from(gate_idx).unwrap(), n),
                            );
                            gates.push(gate);
                        }
                        Node::Impl(fidx, sidx) => {
                            let (gi1, n1) = gate_output_map.get(&fidx).unwrap();
                            let (gi2, n2) = gate_output_map.get(&sidx).unwrap();
                            let (gate, n) = if *n1 {
                                if *n2 {
                                    (Gate::new_nimpl(*gi2, *gi1), true)
                                } else {
                                    (Gate::new_nor(*gi1, *gi2), true)
                                }
                            } else if *n2 {
                                (Gate::new_and(*gi1, *gi2), true)
                            } else {
                                (Gate::new_nimpl(*gi1, *gi2), true)
                            };
                            let gate_idx = gates.len() + input_len;
                            gate_output_map.insert(
                                node_index,
                                (Unsigned::<T>::try_from(gate_idx).unwrap(), n),
                            );
                            gates.push(gate);
                        }
                    };
                };

                if !first_path || !visited[node_index] {
                    if first_path {
                        visited[node_index] = true;
                    }
                    if first_path {
                        top.path = 1;
                        stack.push(SimpleEntry::new(node.first_path()));
                    } else if second_path {
                        top.path = 2;
                        stack.push(SimpleEntry::new(node.second_path()));
                    } else {
                        new_node();
                        stack.pop();
                        if stack.is_empty() {
                            circ_outputs.push(gate_output_map[&node_index]);
                        }
                    }
                } else {
                    if !visited[node_index] {
                        new_node();
                    }
                    stack.pop();
                    if stack.is_empty() {
                        circ_outputs.push(gate_output_map[&node_index]);
                    }
                }
            }
        }
        test_println!(
            "xxx: {} {:?} {:?} {:?}",
            input_len,
            gates,
            circ_outputs,
            input_map
        );
        (
            Circuit::<<T as VarLit>::Unsigned>::new(
                Unsigned::<T>::try_from(input_len).unwrap(),
                gates,
                circ_outputs,
            )
            .unwrap(),
            input_map,
        )
    }

    fn to_circuit_history_order(
        &self,
        outputs: impl IntoIterator<Item = usize>,
    ) -> (
        Circuit<<T as VarLit>::Unsigned>,
        HashMap<T, <T as VarLit>::Unsigned>,
    )
    where
        T: std::hash::Hash,
        <T as VarLit>::Unsigned: Clone + Copy + PartialEq + Eq + PartialOrd + Ord + Default,
        <T as VarLit>::Unsigned: TryFrom<usize>,
        <<T as VarLit>::Unsigned as TryFrom<usize>>::Error: Debug,
        <T as VarLit>::Unsigned: Debug,
        usize: TryFrom<<T as VarLit>::Unsigned>,
        <usize as TryFrom<<T as VarLit>::Unsigned>>::Error: Debug,
    {
        type Unsigned<T> = <T as VarLit>::Unsigned;
        let mut input_map = HashMap::new();
        let outputs = Vec::from_iter(outputs);
        #[derive(Clone, Copy)]
        struct SimpleEntry {
            node_index: usize,
            path: usize,
        }
        impl SimpleEntry {
            #[inline]
            fn new(start: usize) -> Self {
                Self {
                    node_index: start,
                    path: 0,
                }
            }
        }
        let mut visited = vec![false; self.nodes.len()];
        // collect inputs
        for start in &outputs {
            if *start == 0 || *start == 1 {
                // skip single values
                continue;
            }
            let mut stack = vec![SimpleEntry::new(*start)];
            while !stack.is_empty() {
                let top = stack.last_mut().unwrap();
                let node_index = top.node_index;
                let node = self.nodes[top.node_index];
                let first_path = top.path == 0 && !node.is_single();
                let second_path = top.path == 1 && !node.is_unary();
                if !first_path || !visited[node_index] {
                    if first_path {
                        visited[node_index] = true;
                    }
                    match node {
                        Node::Single(l) => {
                            visited[node_index] = true;
                            if let Some(l) = l.varlit() {
                                let lp = l.positive().unwrap();
                                if !input_map.contains_key(&lp) {
                                    input_map.insert(
                                        lp,
                                        Unsigned::<T>::try_from(input_map.len()).unwrap(),
                                    );
                                }
                            } else {
                                panic!("Unsupported!");
                            }
                        }
                        _ => {}
                    }
                    if first_path {
                        top.path = 1;
                        stack.push(SimpleEntry::new(node.first_path()));
                    } else if second_path {
                        top.path = 2;
                        stack.push(SimpleEntry::new(node.second_path()));
                    } else {
                        stack.pop();
                    }
                } else {
                    stack.pop();
                }
            }
        }

        // create circuit
        let (idx_output_map, output_len) = {
            let mut idx_output_map = HashMap::<usize, Vec<usize>>::new();
            let output_len = outputs.iter().filter(|x| **x != 0 && **x != 1).count();
            for (i, o) in outputs.iter().filter(|x| **x != 0 && **x != 1).enumerate() {
                if let Some(list) = idx_output_map.get_mut(o) {
                    list.push(i);
                } else {
                    idx_output_map.insert(*o, vec![i]);
                }
            }
            (idx_output_map, output_len)
        };
        let mut gate_output_map = HashMap::<usize, (Unsigned<T>, bool)>::new();
        let input_len = input_map.len();
        let mut gates = vec![];
        let mut circ_outputs = vec![(Unsigned::<T>::default(), false); output_len];

        for (node_index, node) in self.nodes.iter().enumerate() {
            if !visited[node_index] {
                continue;
            }
            match node {
                Node::Single(l) => {
                    let l = l.varlit().unwrap();
                    let lit = input_map[&l.positive().unwrap()];
                    gate_output_map.insert(node_index, (lit, !l.is_positive()));
                }
                Node::Negated(fidx) => {
                    let (gi, n) = gate_output_map.get(&fidx).unwrap();
                    gate_output_map.insert(node_index, (*gi, !n));
                }
                Node::And(fidx, sidx) => {
                    let (gi1, n1) = gate_output_map.get(&fidx).unwrap();
                    let (gi2, n2) = gate_output_map.get(&sidx).unwrap();
                    let (gate, n) = if *n1 {
                        if *n2 {
                            // and(!gi1,!gi2) -> nor(gi1,gi2)
                            (Gate::new_nor(*gi1, *gi2), false)
                        } else {
                            (Gate::new_nimpl(*gi2, *gi1), false)
                        }
                    } else if *n2 {
                        (Gate::new_nimpl(*gi1, *gi2), false)
                    } else {
                        (Gate::new_and(*gi1, *gi2), false)
                    };
                    let gate_idx = gates.len() + input_len;
                    gate_output_map
                        .insert(node_index, (Unsigned::<T>::try_from(gate_idx).unwrap(), n));
                    gates.push(gate);
                }
                Node::Or(fidx, sidx) => {
                    let (gi1, n1) = gate_output_map.get(&fidx).unwrap();
                    let (gi2, n2) = gate_output_map.get(&sidx).unwrap();
                    let (gate, n) = if *n1 {
                        if *n2 {
                            (Gate::new_and(*gi1, *gi2), true)
                        } else {
                            (Gate::new_nimpl(*gi1, *gi2), true)
                        }
                    } else if *n2 {
                        (Gate::new_nimpl(*gi2, *gi1), true)
                    } else {
                        (Gate::new_nor(*gi1, *gi2), true)
                    };
                    let gate_idx = gates.len() + input_len;
                    gate_output_map
                        .insert(node_index, (Unsigned::<T>::try_from(gate_idx).unwrap(), n));
                    gates.push(gate);
                }
                Node::Xor(fidx, sidx) | Node::Equal(fidx, sidx) => {
                    let (gi1, n1) = gate_output_map.get(&fidx).unwrap();
                    let (gi2, n2) = gate_output_map.get(&sidx).unwrap();
                    let neg = matches!(node, Node::Equal(_, _));
                    let (gate, n) = if *n1 {
                        if *n2 {
                            // and(!gi1,!gi2) -> nor(gi1,gi2)
                            (Gate::new_xor(*gi1, *gi2), neg)
                        } else {
                            (Gate::new_xor(*gi1, *gi2), !neg)
                        }
                    } else if *n2 {
                        (Gate::new_xor(*gi1, *gi2), !neg)
                    } else {
                        (Gate::new_xor(*gi1, *gi2), neg)
                    };
                    let gate_idx = gates.len() + input_len;
                    gate_output_map
                        .insert(node_index, (Unsigned::<T>::try_from(gate_idx).unwrap(), n));
                    gates.push(gate);
                }
                Node::Impl(fidx, sidx) => {
                    let (gi1, n1) = gate_output_map.get(&fidx).unwrap();
                    let (gi2, n2) = gate_output_map.get(&sidx).unwrap();
                    let (gate, n) = if *n1 {
                        if *n2 {
                            (Gate::new_nimpl(*gi2, *gi1), true)
                        } else {
                            (Gate::new_nor(*gi1, *gi2), true)
                        }
                    } else if *n2 {
                        (Gate::new_and(*gi1, *gi2), true)
                    } else {
                        (Gate::new_nimpl(*gi1, *gi2), true)
                    };
                    let gate_idx = gates.len() + input_len;
                    gate_output_map
                        .insert(node_index, (Unsigned::<T>::try_from(gate_idx).unwrap(), n));
                    gates.push(gate);
                }
            }
            if let Some(list) = idx_output_map.get(&node_index) {
                for oidx in list {
                    circ_outputs[*oidx] = gate_output_map[&node_index];
                }
            }
        }
        test_println!(
            "xxx: {} {:?} {:?} {:?}",
            input_len,
            gates,
            circ_outputs,
            input_map
        );
        (
            Circuit::<<T as VarLit>::Unsigned>::new(
                Unsigned::<T>::try_from(input_len).unwrap(),
                gates,
                circ_outputs,
            )
            .unwrap(),
            input_map,
        )
    }

    /// Generates circuit for given variables.
    ///
    /// The `outputs` is list of output variable indices.
    /// It returns circuit and mapping of that circuit inputs (key is circuit input index,
    /// value is variable literal from expression creator).
    pub fn to_circuit(
        &self,
        outputs: impl IntoIterator<Item = usize>,
    ) -> (
        Circuit<<T as VarLit>::Unsigned>,
        HashMap<T, <T as VarLit>::Unsigned>,
    )
    where
        T: std::hash::Hash,
        <T as VarLit>::Unsigned: Clone + Copy + PartialEq + Eq + PartialOrd + Ord + Default,
        <T as VarLit>::Unsigned: TryFrom<usize>,
        <<T as VarLit>::Unsigned as TryFrom<usize>>::Error: Debug,
        <T as VarLit>::Unsigned: Debug,
        usize: TryFrom<<T as VarLit>::Unsigned>,
        <usize as TryFrom<<T as VarLit>::Unsigned>>::Error: Debug,
    {
        if self.history_order {
            self.to_circuit_history_order(outputs)
        } else {
            self.to_circuit_normal(outputs)
        }
    }
}

// types

/// Typical `ExprCreator` defined with 32-bit variable literals.
pub type ExprCreator32 = ExprCreator<i32>;
/// Typical `ExprCreator` defined with pointer sized variable literals.
pub type ExprCreatorSys = ExprCreator<isize>;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::boolexpr::{bool_ite, full_adder, BoolEqual, BoolExprNode, BoolImpl};
    use crate::dynintexpr::DynIntExprNode;
    use crate::intexpr::{BitVal, DivMod, FullMul, IntExprNode, IntModSub, TryIntConstant};
    use generic_array::typenum::*;

    macro_rules! expr_creator_testcase {
        ($ec: ident, $v: ident, $vars:expr, $expr: tt, $res: expr) => {
            $ec = ExprCreator::<isize>::new();
            $v.clear();
            $v.push(BoolExprNode::single($ec.clone(), false));
            for _ in 0..$vars {
                $v.push(BoolExprNode::variable($ec.clone()));
            }
            let expr_indices = $expr;
            assert_eq!($res, $ec.borrow().to_circuit(expr_indices));
        };
    }

    #[test]
    fn test_to_circuit_1() {
        let mut v = vec![];
        #[allow(unused_assignments)]
        let mut ec = ExprCreator::<isize>::new();
        expr_creator_testcase!(
            ec,
            v,
            1,
            { [v[1].index] },
            (
                Circuit::new(1, [], [(0, false)]).unwrap(),
                HashMap::from_iter([(1, 0)])
            )
        );
        expr_creator_testcase!(
            ec,
            v,
            1,
            { [v[1].index, 0] },
            (
                Circuit::new(1, [], [(0, false)]).unwrap(),
                HashMap::from_iter([(1, 0)])
            )
        );
        expr_creator_testcase!(
            ec,
            v,
            1,
            { [v[1].index, 1] },
            (
                Circuit::new(1, [], [(0, false)]).unwrap(),
                HashMap::from_iter([(1, 0)])
            )
        );
        expr_creator_testcase!(
            ec,
            v,
            1,
            { [(!v[1].clone()).index] },
            (
                Circuit::new(1, [], [(0, true)]).unwrap(),
                HashMap::from_iter([(1, 0)])
            )
        );
        expr_creator_testcase!(
            ec,
            v,
            1,
            { [(v[1].clone() & v[1].clone()).index] },
            (
                Circuit::new(1, [], [(0, false)]).unwrap(),
                HashMap::from_iter([(1, 0)])
            )
        );
        for (func_name, aneg, bneg, rneg, expected) in [
            (
                "and",
                false,
                false,
                false,
                (
                    Circuit::new(2, [Gate::new_and(0, 1)], [(2, false)]).unwrap(),
                    HashMap::from_iter([(1, 0), (2, 1)]),
                ),
            ),
            (
                "and",
                true,
                false,
                false,
                (
                    Circuit::new(2, [Gate::new_nimpl(1, 0)], [(2, false)]).unwrap(),
                    HashMap::from_iter([(1, 0), (2, 1)]),
                ),
            ),
            (
                "and",
                false,
                true,
                false,
                (
                    Circuit::new(2, [Gate::new_nimpl(0, 1)], [(2, false)]).unwrap(),
                    HashMap::from_iter([(1, 0), (2, 1)]),
                ),
            ),
            (
                "and",
                true,
                true,
                false,
                (
                    Circuit::new(2, [Gate::new_nor(0, 1)], [(2, false)]).unwrap(),
                    HashMap::from_iter([(1, 0), (2, 1)]),
                ),
            ),
            (
                "or",
                false,
                false,
                false,
                (
                    Circuit::new(2, [Gate::new_nor(0, 1)], [(2, true)]).unwrap(),
                    HashMap::from_iter([(1, 0), (2, 1)]),
                ),
            ),
            (
                "or",
                true,
                false,
                false,
                (
                    Circuit::new(2, [Gate::new_nimpl(0, 1)], [(2, true)]).unwrap(),
                    HashMap::from_iter([(1, 0), (2, 1)]),
                ),
            ),
            (
                "or",
                false,
                true,
                false,
                (
                    Circuit::new(2, [Gate::new_nimpl(1, 0)], [(2, true)]).unwrap(),
                    HashMap::from_iter([(1, 0), (2, 1)]),
                ),
            ),
            (
                "or",
                true,
                true,
                false,
                (
                    Circuit::new(2, [Gate::new_and(0, 1)], [(2, true)]).unwrap(),
                    HashMap::from_iter([(1, 0), (2, 1)]),
                ),
            ),
            (
                "xor",
                false,
                false,
                false,
                (
                    Circuit::new(2, [Gate::new_xor(0, 1)], [(2, false)]).unwrap(),
                    HashMap::from_iter([(1, 0), (2, 1)]),
                ),
            ),
            (
                "xor",
                true,
                false,
                false,
                (
                    Circuit::new(2, [Gate::new_xor(0, 1)], [(2, true)]).unwrap(),
                    HashMap::from_iter([(1, 0), (2, 1)]),
                ),
            ),
            (
                "xor",
                false,
                true,
                false,
                (
                    Circuit::new(2, [Gate::new_xor(0, 1)], [(2, true)]).unwrap(),
                    HashMap::from_iter([(1, 0), (2, 1)]),
                ),
            ),
            (
                "xor",
                true,
                true,
                false,
                (
                    Circuit::new(2, [Gate::new_xor(0, 1)], [(2, false)]).unwrap(),
                    HashMap::from_iter([(1, 0), (2, 1)]),
                ),
            ),
            (
                "eq",
                false,
                false,
                false,
                (
                    Circuit::new(2, [Gate::new_xor(0, 1)], [(2, true)]).unwrap(),
                    HashMap::from_iter([(1, 0), (2, 1)]),
                ),
            ),
            (
                "eq",
                true,
                false,
                false,
                (
                    Circuit::new(2, [Gate::new_xor(0, 1)], [(2, false)]).unwrap(),
                    HashMap::from_iter([(1, 0), (2, 1)]),
                ),
            ),
            (
                "eq",
                false,
                true,
                false,
                (
                    Circuit::new(2, [Gate::new_xor(0, 1)], [(2, false)]).unwrap(),
                    HashMap::from_iter([(1, 0), (2, 1)]),
                ),
            ),
            (
                "eq",
                true,
                true,
                false,
                (
                    Circuit::new(2, [Gate::new_xor(0, 1)], [(2, true)]).unwrap(),
                    HashMap::from_iter([(1, 0), (2, 1)]),
                ),
            ),
            (
                "impl",
                false,
                false,
                false,
                (
                    Circuit::new(2, [Gate::new_nimpl(0, 1)], [(2, true)]).unwrap(),
                    HashMap::from_iter([(1, 0), (2, 1)]),
                ),
            ),
            (
                "impl",
                true,
                false,
                false,
                (
                    Circuit::new(2, [Gate::new_nor(0, 1)], [(2, true)]).unwrap(),
                    HashMap::from_iter([(1, 0), (2, 1)]),
                ),
            ),
            (
                "impl",
                false,
                true,
                false,
                (
                    Circuit::new(2, [Gate::new_and(0, 1)], [(2, true)]).unwrap(),
                    HashMap::from_iter([(1, 0), (2, 1)]),
                ),
            ),
            (
                "impl",
                true,
                true,
                false,
                (
                    Circuit::new(2, [Gate::new_nimpl(1, 0)], [(2, true)]).unwrap(),
                    HashMap::from_iter([(1, 0), (2, 1)]),
                ),
            ),
            (
                "and",
                false,
                false,
                true,
                (
                    Circuit::new(2, [Gate::new_and(0, 1)], [(2, true)]).unwrap(),
                    HashMap::from_iter([(1, 0), (2, 1)]),
                ),
            ),
            (
                "or",
                true,
                false,
                true,
                (
                    Circuit::new(2, [Gate::new_nimpl(0, 1)], [(2, false)]).unwrap(),
                    HashMap::from_iter([(1, 0), (2, 1)]),
                ),
            ),
        ] {
            expr_creator_testcase!(
                ec,
                v,
                2,
                {
                    let a = if aneg { !v[1].clone() } else { v[1].clone() };
                    let b = if bneg { !v[2].clone() } else { v[2].clone() };
                    let r = match func_name {
                        "and" => a.clone() & b.clone(),
                        "or" => a.clone() | b.clone(),
                        "xor" => a.clone() ^ b.clone(),
                        "impl" => a.clone().imp(b.clone()),
                        "eq" => a.clone().bequal(b.clone()),
                        _ => {
                            panic!("Unsupported");
                        }
                    };
                    if rneg {
                        [(!r).index]
                    } else {
                        [r.index]
                    }
                },
                expected
            );
        }
        expr_creator_testcase!(
            ec,
            v,
            3,
            { [(v[1].clone() & v[2].clone() & v[3].clone()).index] },
            (
                Circuit::new(3, [Gate::new_and(0, 1), Gate::new_and(3, 2)], [(4, false)]).unwrap(),
                HashMap::from_iter([(1, 0), (3, 2), (2, 1)])
            )
        );
        expr_creator_testcase!(
            ec,
            v,
            3,
            { [(v[1].clone() & (v[2].clone() | v[3].clone())).index] },
            (
                Circuit::new(
                    3,
                    [Gate::new_nor(0, 1), Gate::new_nimpl(2, 3)],
                    [(4, false)]
                )
                .unwrap(),
                HashMap::from_iter([(2, 0), (1, 2), (3, 1)])
            )
        );
        expr_creator_testcase!(
            ec,
            v,
            3,
            { [((v[2].clone() | v[3].clone()) & v[1].clone()).index] },
            (
                Circuit::new(
                    3,
                    [Gate::new_nor(0, 1), Gate::new_nimpl(2, 3)],
                    [(4, false)]
                )
                .unwrap(),
                HashMap::from_iter([(2, 0), (1, 2), (3, 1)])
            )
        );
        expr_creator_testcase!(
            ec,
            v,
            3,
            { [(v[1].clone() & !(v[2].clone() | v[3].clone())).index] },
            (
                Circuit::new(3, [Gate::new_nor(0, 1), Gate::new_and(3, 2)], [(4, false)]).unwrap(),
                HashMap::from_iter([(2, 0), (1, 2), (3, 1)])
            )
        );
        expr_creator_testcase!(
            ec,
            v,
            3,
            { [(!(v[2].clone() | v[3].clone()) & v[1].clone()).index] },
            (
                Circuit::new(3, [Gate::new_nor(0, 1), Gate::new_and(3, 2)], [(4, false)]).unwrap(),
                HashMap::from_iter([(2, 0), (1, 2), (3, 1)])
            )
        );
        expr_creator_testcase!(
            ec,
            v,
            3,
            { [(!v[1].clone() & (v[2].clone() ^ !v[3].clone())).index] },
            (
                Circuit::new(3, [Gate::new_xor(0, 1), Gate::new_nor(3, 2)], [(4, false)]).unwrap(),
                HashMap::from_iter([(2, 0), (1, 2), (3, 1)])
            )
        );
        expr_creator_testcase!(
            ec,
            v,
            3,
            { [(!v[1].clone() | (v[2].clone() ^ !v[3].clone())).index] },
            (
                Circuit::new(3, [Gate::new_xor(0, 1), Gate::new_and(3, 2)], [(4, true)]).unwrap(),
                HashMap::from_iter([(2, 0), (1, 2), (3, 1)])
            )
        );
    }

    #[test]
    fn test_to_circuit_2() {
        let mut v = vec![];
        #[allow(unused_assignments)]
        let mut ec = ExprCreator::<isize>::new();
        expr_creator_testcase!(
            ec,
            v,
            3,
            {
                let r1 = v[1].clone() & v[2].clone() & v[3].clone();
                let r2 = r1.clone() ^ v[1].clone();
                [r1.index, r2.index]
            },
            (
                Circuit::new(
                    3,
                    [
                        Gate::new_and(0, 1),
                        Gate::new_and(3, 2),
                        Gate::new_xor(4, 0)
                    ],
                    [(4, false), (5, false)]
                )
                .unwrap(),
                HashMap::from_iter([(1, 0), (3, 2), (2, 1)])
            )
        );
        expr_creator_testcase!(
            ec,
            v,
            3,
            {
                let r1 = v[1].clone() & v[2].clone() & v[3].clone();
                let r2 = !r1.clone() ^ v[1].clone();
                [r1.index, r2.index]
            },
            (
                Circuit::new(
                    3,
                    [
                        Gate::new_and(0, 1),
                        Gate::new_and(3, 2),
                        Gate::new_xor(4, 0)
                    ],
                    [(4, false), (5, true)]
                )
                .unwrap(),
                HashMap::from_iter([(1, 0), (3, 2), (2, 1)])
            )
        );
        expr_creator_testcase!(
            ec,
            v,
            3,
            {
                let r1 = v[1].clone() & v[2].clone() & v[3].clone();
                let r2 = r1.clone() | v[1].clone();
                [r1.index, r2.index]
            },
            (
                Circuit::new(
                    3,
                    [
                        Gate::new_and(0, 1),
                        Gate::new_and(3, 2),
                        Gate::new_nor(4, 0)
                    ],
                    [(4, false), (5, true)]
                )
                .unwrap(),
                HashMap::from_iter([(1, 0), (3, 2), (2, 1)])
            )
        );
        expr_creator_testcase!(
            ec,
            v,
            3,
            {
                let r1 = v[1].clone() & v[2].clone() & v[3].clone();
                let r2 = !(r1.clone() | v[1].clone());
                [r1.index, r2.index]
            },
            (
                Circuit::new(
                    3,
                    [
                        Gate::new_and(0, 1),
                        Gate::new_and(3, 2),
                        Gate::new_nor(4, 0)
                    ],
                    [(4, false), (5, false)]
                )
                .unwrap(),
                HashMap::from_iter([(1, 0), (3, 2), (2, 1)])
            )
        );
        expr_creator_testcase!(
            ec,
            v,
            3,
            {
                let r1 = !(v[1].clone() & v[2].clone() & v[3].clone());
                let r2 = !(r1.clone() | v[1].clone());
                [r1.index, r2.index]
            },
            (
                Circuit::new(
                    3,
                    [
                        Gate::new_and(0, 1),
                        Gate::new_and(3, 2),
                        Gate::new_nimpl(4, 0)
                    ],
                    [(4, true), (5, false)]
                )
                .unwrap(),
                HashMap::from_iter([(1, 0), (3, 2), (2, 1)])
            )
        );
        expr_creator_testcase!(
            ec,
            v,
            3,
            {
                let (s, c) = full_adder(v[1].clone(), v[2].clone(), v[3].clone());
                [s.index, c.index]
            },
            (
                Circuit::new(
                    3,
                    [
                        Gate::new_xor(0, 1),
                        Gate::new_xor(3, 2),
                        Gate::new_and(3, 2),
                        Gate::new_and(0, 1),
                        Gate::new_nor(5, 6)
                    ],
                    [(4, false), (7, true)]
                )
                .unwrap(),
                HashMap::from_iter([(1, 0), (3, 2), (2, 1)])
            )
        );
        expr_creator_testcase!(
            ec,
            v,
            3,
            { [bool_ite(v[1].clone(), v[2].clone(), v[3].clone()).index] },
            (
                Circuit::new(
                    3,
                    [
                        Gate::new_and(0, 1),
                        Gate::new_nimpl(2, 0),
                        Gate::new_nor(3, 4)
                    ],
                    [(5, true)]
                )
                .unwrap(),
                HashMap::from_iter([(1, 0), (3, 2), (2, 1)])
            )
        );
    }

    #[test]
    fn test_to_circuit_2_ext() {
        let mut v = vec![];
        #[allow(unused_assignments)]
        let mut ec = ExprCreator::<isize>::new();
        expr_creator_testcase!(
            ec,
            v,
            3,
            {
                let r1 = v[1].clone() & v[2].clone();
                let r2 = v[1].clone() ^ v[2].clone();
                let r1x = r1 & v[3].clone();
                [r1x.index, r2.index]
            },
            (
                Circuit::new(
                    3,
                    [
                        Gate::new_and(0, 1),
                        Gate::new_and(3, 2),
                        Gate::new_xor(0, 1)
                    ],
                    [(4, false), (5, false)]
                )
                .unwrap(),
                HashMap::from_iter([(1, 0), (3, 2), (2, 1)])
            )
        );
        // unused paths
        expr_creator_testcase!(
            ec,
            v,
            3,
            {
                let r1 = v[1].clone() & v[2].clone();
                let ru = v[1].clone() | v[2].clone();
                let r2 = v[1].clone() ^ v[2].clone();
                let r1x = r1 & v[3].clone();
                let _ = ru.clone() | v[3].clone();
                [r1x.index, r2.index]
            },
            (
                Circuit::new(
                    3,
                    [
                        Gate::new_and(0, 1),
                        Gate::new_and(3, 2),
                        Gate::new_xor(0, 1)
                    ],
                    [(4, false), (5, false)]
                )
                .unwrap(),
                HashMap::from_iter([(1, 0), (3, 2), (2, 1)])
            )
        );
    }

    #[test]
    fn test_to_circuit_3() {
        let ec = ExprCreator::<isize>::new();
        let a = IntExprNode::<_, U3, false>::variable(ec.clone());
        let b = IntExprNode::<_, U3, false>::variable(ec.clone());
        let c = a.clone().mod_sub(b.clone());
        let mut indexes = [0; 3];
        (0..3).for_each(|x| indexes[x] = c.bit(x).index);
        let (circuit, input_map) = ec.borrow().to_circuit(indexes);
        for av in 0u32..8 {
            for bv in 0u32..8 {
                let exp_cv = (av.overflowing_sub(bv).0) & 7;
                let mut input = [false; 6];
                (0..3).for_each(|x| {
                    input[input_map[&a.bit(x).varlit().unwrap()]] = ((av >> x) & 1) != 0;
                    input[input_map[&b.bit(x).varlit().unwrap()]] = ((bv >> x) & 1) != 0;
                });
                let cv_vec = circuit.eval(input);
                let mut cv = 0;
                cv_vec.into_iter().enumerate().for_each(|(i, bv)| {
                    if bv {
                        cv |= 1 << i;
                    }
                });
                assert_eq!(exp_cv, cv, "{}-{}", av, bv);
            }
        }

        let ec = ExprCreator::<isize>::new();
        let a = IntExprNode::<_, U4, false>::variable(ec.clone());
        let b = IntExprNode::<_, U4, false>::variable(ec.clone());
        let c = a.clone().fullmul(b.clone());
        let mut indexes = [0; 8];
        (0..8).for_each(|x| indexes[x] = c.bit(x).index);
        let (circuit, input_map) = ec.borrow().to_circuit(indexes);
        for av in 0u32..16 {
            for bv in 0u32..16 {
                let exp_cv = (av * bv) & 0xff;
                let mut input = [false; 8];
                (0..4).for_each(|x| {
                    input[input_map[&a.bit(x).varlit().unwrap()]] = ((av >> x) & 1) != 0;
                    input[input_map[&b.bit(x).varlit().unwrap()]] = ((bv >> x) & 1) != 0;
                });
                let cv_vec = circuit.eval(input);
                let mut cv = 0;
                cv_vec.into_iter().enumerate().for_each(|(i, bv)| {
                    if bv {
                        cv |= 1 << i;
                    }
                });
                assert_eq!(exp_cv, cv, "fullmul({}, {})", av, bv);
            }
        }

        let ec = ExprCreator::<isize>::new();
        let a = IntExprNode::<_, U5, false>::variable(ec.clone());
        let b = IntExprNode::<_, U5, false>::variable(ec.clone());
        let (d, m, c) = a.clone().divmod(b.clone());
        let mut indexes = [0; 11];
        (0..5).for_each(|x| indexes[x] = d.bit(x).index);
        (0..5).for_each(|x| indexes[5 + x] = m.bit(x).index);
        indexes[10] = c.index;
        let (circuit, input_map) = ec.borrow().to_circuit(indexes);
        for av in 0u32..32 {
            for bv in 0u32..32 {
                let exp_dv = if bv != 0 { av / bv } else { 0 };
                let exp_mv = if bv != 0 { av % bv } else { 0 };
                let exp_cv = bv != 0;
                let mut input = [false; 10];
                (0..5).for_each(|x| {
                    input[input_map[&a.bit(x).varlit().unwrap()]] = ((av >> x) & 1) != 0;
                    input[input_map[&b.bit(x).varlit().unwrap()]] = ((bv >> x) & 1) != 0;
                });
                let rv_vec = circuit.eval(input);
                let mut dv = 0;
                let mut mv = 0;
                let mut cv = false;
                rv_vec.into_iter().enumerate().for_each(|(i, bv)| {
                    if bv {
                        if i < 5 {
                            dv |= 1 << i;
                        } else if i < 10 {
                            mv |= 1 << (i - 5);
                        } else {
                            cv = true;
                        }
                    }
                });
                println!("dcfv: {} {}: {} {} {}", av, bv, dv, mv, cv);
                assert_eq!(exp_cv, cv, "divmod({}, {}).c", av, bv);
                if exp_cv {
                    assert_eq!(exp_dv, dv, "divmod({}, {}).d", av, bv);
                    assert_eq!(exp_mv, mv, "divmod({}, {}).m", av, bv);
                }
            }
        }

        for av in 0u32..32 {
            let ec = ExprCreator::<isize>::new();
            let a = IntExprNode::<_, U5, false>::try_constant(ec.clone(), av).unwrap();
            let b = IntExprNode::<_, U5, false>::variable(ec.clone());
            let (d, m, c) = a.clone().divmod(b.clone());
            let mut indexes = [0; 11];
            (0..5).for_each(|x| indexes[x] = d.bit(x).index);
            (0..5).for_each(|x| indexes[5 + x] = m.bit(x).index);
            indexes[10] = c.index;
            let (circuit, input_map) = ec.borrow().to_circuit(indexes);
            for bv in 0u32..32 {
                let exp_dv = if bv != 0 { av / bv } else { 0 };
                let exp_mv = if bv != 0 { av % bv } else { 0 };
                let exp_cv = bv != 0;
                let mut input = [false; 10];
                (0..5).for_each(|x| {
                    input[input_map[&b.bit(x).varlit().unwrap()]] = ((bv >> x) & 1) != 0;
                });
                let rv_vec = circuit.eval(input);
                let mut dv = 0;
                let mut mv = 0;
                let mut cv = false;
                rv_vec.into_iter().enumerate().for_each(|(i, bv)| {
                    if bv {
                        if i < 5 {
                            dv |= 1 << i;
                        } else if i < 10 {
                            mv |= 1 << (i - 5);
                        } else {
                            cv = true;
                        }
                    }
                });
                println!("dcfv: {} {}: {} {} {}", av, bv, dv, mv, cv);
                assert_eq!(exp_cv, cv, "divmod({}, {}).c", av, bv);
                if exp_cv {
                    assert_eq!(exp_dv, dv, "divmod({}, {}).d", av, bv);
                    assert_eq!(exp_mv, mv, "divmod({}, {}).m", av, bv);
                }
            }
        }

        let ec = ExprCreator::<isize>::new();
        let a = IntExprNode::<_, U8, true>::variable(ec.clone());
        let b = IntExprNode::<_, U8, true>::variable(ec.clone());
        let (d, m, c) = a.clone().divmod(b.clone());
        let mut indexes = [0; 17];
        (0..8).for_each(|x| indexes[x] = d.bit(x).index);
        (0..8).for_each(|x| indexes[8 + x] = m.bit(x).index);
        indexes[16] = c.index;
        let (circuit, input_map) = ec.borrow().to_circuit(indexes);
        for av in i8::MIN..=i8::MAX {
            for bv in i8::MIN..=i8::MAX {
                let exp_cv = (bv != 0) && (av != i8::MIN || bv != -1);
                let exp_dv = if exp_cv { av / bv } else { 0 };
                let exp_mv = if exp_cv { av % bv } else { 0 };
                let mut input = [false; 16];
                (0..8).for_each(|x| {
                    input[input_map[&a.bit(x).varlit().unwrap()]] = ((av >> x) & 1) != 0;
                    input[input_map[&b.bit(x).varlit().unwrap()]] = ((bv >> x) & 1) != 0;
                });
                let rv_vec = circuit.eval(input);
                let mut dv = 0;
                let mut mv = 0;
                let mut cv = false;
                rv_vec.into_iter().enumerate().for_each(|(i, bv)| {
                    if bv {
                        if i < 8 {
                            dv |= 1 << i;
                        } else if i < 16 {
                            mv |= 1 << (i - 8);
                        } else {
                            cv = true;
                        }
                    }
                });
                println!("dcfv: {} {}: {} {} {}", av, bv, dv, mv, cv);
                assert_eq!(exp_cv, cv, "divmod({}, {}).c", av, bv);
                if exp_cv {
                    assert_eq!(exp_dv, dv, "divmod({}, {}).d", av, bv);
                    assert_eq!(exp_mv, mv, "divmod({}, {}).m", av, bv);
                }
            }
        }

        let ec = ExprCreator::<isize>::new();
        let a = DynIntExprNode::<_, false>::variable(ec.clone(), 5);
        let b = DynIntExprNode::<_, false>::variable(ec.clone(), 5);
        let (d, m, c) = a.clone().divmod(b.clone());
        let mut indexes = [0; 11];
        (0..5).for_each(|x| indexes[x] = d.bit(x).index);
        (0..5).for_each(|x| indexes[5 + x] = m.bit(x).index);
        indexes[10] = c.index;
        let (circuit, input_map) = ec.borrow().to_circuit(indexes);
        for av in 0u32..32 {
            for bv in 0u32..32 {
                let exp_dv = if bv != 0 { av / bv } else { 0 };
                let exp_mv = if bv != 0 { av % bv } else { 0 };
                let exp_cv = bv != 0;
                let mut input = [false; 10];
                (0..5).for_each(|x| {
                    input[input_map[&a.bit(x).varlit().unwrap()]] = ((av >> x) & 1) != 0;
                    input[input_map[&b.bit(x).varlit().unwrap()]] = ((bv >> x) & 1) != 0;
                });
                let rv_vec = circuit.eval(input);
                let mut dv = 0;
                let mut mv = 0;
                let mut cv = false;
                rv_vec.into_iter().enumerate().for_each(|(i, bv)| {
                    if bv {
                        if i < 5 {
                            dv |= 1 << i;
                        } else if i < 10 {
                            mv |= 1 << (i - 5);
                        } else {
                            cv = true;
                        }
                    }
                });
                println!("dcfv: {} {}: {} {} {}", av, bv, dv, mv, cv);
                assert_eq!(exp_cv, cv, "divmod({}, {}).c", av, bv);
                if exp_cv {
                    assert_eq!(exp_dv, dv, "divmod({}, {}).d", av, bv);
                    assert_eq!(exp_mv, mv, "divmod({}, {}).m", av, bv);
                }
            }
        }

        let ec = ExprCreator::<isize>::new();
        let a = DynIntExprNode::<_, true>::variable(ec.clone(), 8);
        let b = DynIntExprNode::<_, true>::variable(ec.clone(), 8);
        let (d, m, c) = a.clone().divmod(b.clone());
        let mut indexes = [0; 17];
        (0..8).for_each(|x| indexes[x] = d.bit(x).index);
        (0..8).for_each(|x| indexes[8 + x] = m.bit(x).index);
        indexes[16] = c.index;
        let (circuit, input_map) = ec.borrow().to_circuit(indexes);
        println!("Circuit len: {}", circuit.len());
        for av in i8::MIN..=i8::MAX {
            for bv in i8::MIN..=i8::MAX {
                let exp_cv = (bv != 0) && (av != i8::MIN || bv != -1);
                let exp_dv = if exp_cv { av / bv } else { 0 };
                let exp_mv = if exp_cv { av % bv } else { 0 };
                let mut input = [false; 16];
                (0..8).for_each(|x| {
                    input[input_map[&a.bit(x).varlit().unwrap()]] = ((av >> x) & 1) != 0;
                    input[input_map[&b.bit(x).varlit().unwrap()]] = ((bv >> x) & 1) != 0;
                });
                let rv_vec = circuit.eval(input);
                let mut dv = 0;
                let mut mv = 0;
                let mut cv = false;
                rv_vec.into_iter().enumerate().for_each(|(i, bv)| {
                    if bv {
                        if i < 8 {
                            dv |= 1 << i;
                        } else if i < 16 {
                            mv |= 1 << (i - 8);
                        } else {
                            cv = true;
                        }
                    }
                });
                println!("dcfv: {} {}: {} {} {}", av, bv, dv, mv, cv);
                assert_eq!(exp_cv, cv, "divmod({}, {}).c", av, bv);
                if exp_cv {
                    assert_eq!(exp_dv, dv, "divmod({}, {}).d", av, bv);
                    assert_eq!(exp_mv, mv, "divmod({}, {}).m", av, bv);
                }
            }
        }
    }

    macro_rules! expr_creator_ho_testcase {
        ($ec: ident, $v: ident, $vars:expr, $expr: tt, $res: expr) => {
            $ec = ExprCreator::<isize>::with_history_order();
            $v.clear();
            $v.push(BoolExprNode::single($ec.clone(), false));
            for _ in 0..$vars {
                $v.push(BoolExprNode::variable($ec.clone()));
            }
            let expr_indices = $expr;
            assert_eq!($res, $ec.borrow().to_circuit(expr_indices));
        };
    }

    #[test]
    fn test_to_circuit_1_ho() {
        let mut v = vec![];
        #[allow(unused_assignments)]
        let mut ec = ExprCreator::<isize>::new();
        expr_creator_ho_testcase!(
            ec,
            v,
            1,
            { [v[1].index] },
            (
                Circuit::new(1, [], [(0, false)]).unwrap(),
                HashMap::from_iter([(1, 0)])
            )
        );
        expr_creator_ho_testcase!(
            ec,
            v,
            1,
            { [v[1].index, 0] },
            (
                Circuit::new(1, [], [(0, false)]).unwrap(),
                HashMap::from_iter([(1, 0)])
            )
        );
        expr_creator_ho_testcase!(
            ec,
            v,
            1,
            { [v[1].index, 1] },
            (
                Circuit::new(1, [], [(0, false)]).unwrap(),
                HashMap::from_iter([(1, 0)])
            )
        );
        expr_creator_ho_testcase!(
            ec,
            v,
            1,
            { [(!v[1].clone()).index] },
            (
                Circuit::new(1, [], [(0, true)]).unwrap(),
                HashMap::from_iter([(1, 0)])
            )
        );
        expr_creator_ho_testcase!(
            ec,
            v,
            1,
            { [(v[1].clone() & v[1].clone()).index] },
            (
                Circuit::new(1, [], [(0, false)]).unwrap(),
                HashMap::from_iter([(1, 0)])
            )
        );
        for (func_name, aneg, bneg, rneg, expected) in [
            (
                "and",
                false,
                false,
                false,
                (
                    Circuit::new(2, [Gate::new_and(0, 1)], [(2, false)]).unwrap(),
                    HashMap::from_iter([(1, 0), (2, 1)]),
                ),
            ),
            (
                "and",
                true,
                false,
                false,
                (
                    Circuit::new(2, [Gate::new_nimpl(1, 0)], [(2, false)]).unwrap(),
                    HashMap::from_iter([(1, 0), (2, 1)]),
                ),
            ),
            (
                "and",
                false,
                true,
                false,
                (
                    Circuit::new(2, [Gate::new_nimpl(0, 1)], [(2, false)]).unwrap(),
                    HashMap::from_iter([(1, 0), (2, 1)]),
                ),
            ),
            (
                "and",
                true,
                true,
                false,
                (
                    Circuit::new(2, [Gate::new_nor(0, 1)], [(2, false)]).unwrap(),
                    HashMap::from_iter([(1, 0), (2, 1)]),
                ),
            ),
            (
                "or",
                false,
                false,
                false,
                (
                    Circuit::new(2, [Gate::new_nor(0, 1)], [(2, true)]).unwrap(),
                    HashMap::from_iter([(1, 0), (2, 1)]),
                ),
            ),
            (
                "or",
                true,
                false,
                false,
                (
                    Circuit::new(2, [Gate::new_nimpl(0, 1)], [(2, true)]).unwrap(),
                    HashMap::from_iter([(1, 0), (2, 1)]),
                ),
            ),
            (
                "or",
                false,
                true,
                false,
                (
                    Circuit::new(2, [Gate::new_nimpl(1, 0)], [(2, true)]).unwrap(),
                    HashMap::from_iter([(1, 0), (2, 1)]),
                ),
            ),
            (
                "or",
                true,
                true,
                false,
                (
                    Circuit::new(2, [Gate::new_and(0, 1)], [(2, true)]).unwrap(),
                    HashMap::from_iter([(1, 0), (2, 1)]),
                ),
            ),
            (
                "xor",
                false,
                false,
                false,
                (
                    Circuit::new(2, [Gate::new_xor(0, 1)], [(2, false)]).unwrap(),
                    HashMap::from_iter([(1, 0), (2, 1)]),
                ),
            ),
            (
                "xor",
                true,
                false,
                false,
                (
                    Circuit::new(2, [Gate::new_xor(0, 1)], [(2, true)]).unwrap(),
                    HashMap::from_iter([(1, 0), (2, 1)]),
                ),
            ),
            (
                "xor",
                false,
                true,
                false,
                (
                    Circuit::new(2, [Gate::new_xor(0, 1)], [(2, true)]).unwrap(),
                    HashMap::from_iter([(1, 0), (2, 1)]),
                ),
            ),
            (
                "xor",
                true,
                true,
                false,
                (
                    Circuit::new(2, [Gate::new_xor(0, 1)], [(2, false)]).unwrap(),
                    HashMap::from_iter([(1, 0), (2, 1)]),
                ),
            ),
            (
                "eq",
                false,
                false,
                false,
                (
                    Circuit::new(2, [Gate::new_xor(0, 1)], [(2, true)]).unwrap(),
                    HashMap::from_iter([(1, 0), (2, 1)]),
                ),
            ),
            (
                "eq",
                true,
                false,
                false,
                (
                    Circuit::new(2, [Gate::new_xor(0, 1)], [(2, false)]).unwrap(),
                    HashMap::from_iter([(1, 0), (2, 1)]),
                ),
            ),
            (
                "eq",
                false,
                true,
                false,
                (
                    Circuit::new(2, [Gate::new_xor(0, 1)], [(2, false)]).unwrap(),
                    HashMap::from_iter([(1, 0), (2, 1)]),
                ),
            ),
            (
                "eq",
                true,
                true,
                false,
                (
                    Circuit::new(2, [Gate::new_xor(0, 1)], [(2, true)]).unwrap(),
                    HashMap::from_iter([(1, 0), (2, 1)]),
                ),
            ),
            (
                "impl",
                false,
                false,
                false,
                (
                    Circuit::new(2, [Gate::new_nimpl(0, 1)], [(2, true)]).unwrap(),
                    HashMap::from_iter([(1, 0), (2, 1)]),
                ),
            ),
            (
                "impl",
                true,
                false,
                false,
                (
                    Circuit::new(2, [Gate::new_nor(0, 1)], [(2, true)]).unwrap(),
                    HashMap::from_iter([(1, 0), (2, 1)]),
                ),
            ),
            (
                "impl",
                false,
                true,
                false,
                (
                    Circuit::new(2, [Gate::new_and(0, 1)], [(2, true)]).unwrap(),
                    HashMap::from_iter([(1, 0), (2, 1)]),
                ),
            ),
            (
                "impl",
                true,
                true,
                false,
                (
                    Circuit::new(2, [Gate::new_nimpl(1, 0)], [(2, true)]).unwrap(),
                    HashMap::from_iter([(1, 0), (2, 1)]),
                ),
            ),
            (
                "and",
                false,
                false,
                true,
                (
                    Circuit::new(2, [Gate::new_and(0, 1)], [(2, true)]).unwrap(),
                    HashMap::from_iter([(1, 0), (2, 1)]),
                ),
            ),
            (
                "or",
                true,
                false,
                true,
                (
                    Circuit::new(2, [Gate::new_nimpl(0, 1)], [(2, false)]).unwrap(),
                    HashMap::from_iter([(1, 0), (2, 1)]),
                ),
            ),
        ] {
            expr_creator_ho_testcase!(
                ec,
                v,
                2,
                {
                    let a = if aneg { !v[1].clone() } else { v[1].clone() };
                    let b = if bneg { !v[2].clone() } else { v[2].clone() };
                    let r = match func_name {
                        "and" => a.clone() & b.clone(),
                        "or" => a.clone() | b.clone(),
                        "xor" => a.clone() ^ b.clone(),
                        "impl" => a.clone().imp(b.clone()),
                        "eq" => a.clone().bequal(b.clone()),
                        _ => {
                            panic!("Unsupported");
                        }
                    };
                    if rneg {
                        [(!r).index]
                    } else {
                        [r.index]
                    }
                },
                expected
            );
        }
        expr_creator_ho_testcase!(
            ec,
            v,
            3,
            { [(v[1].clone() & v[2].clone() & v[3].clone()).index] },
            (
                Circuit::new(3, [Gate::new_and(0, 1), Gate::new_and(3, 2)], [(4, false)]).unwrap(),
                HashMap::from_iter([(1, 0), (3, 2), (2, 1)])
            )
        );
        expr_creator_ho_testcase!(
            ec,
            v,
            3,
            { [(v[1].clone() & (v[2].clone() | v[3].clone())).index] },
            (
                Circuit::new(
                    3,
                    [Gate::new_nor(0, 1), Gate::new_nimpl(2, 3)],
                    [(4, false)]
                )
                .unwrap(),
                HashMap::from_iter([(2, 0), (1, 2), (3, 1)])
            )
        );
        expr_creator_ho_testcase!(
            ec,
            v,
            3,
            { [((v[2].clone() | v[3].clone()) & v[1].clone()).index] },
            (
                Circuit::new(
                    3,
                    [Gate::new_nor(0, 1), Gate::new_nimpl(2, 3)],
                    [(4, false)]
                )
                .unwrap(),
                HashMap::from_iter([(2, 0), (1, 2), (3, 1)])
            )
        );
        expr_creator_ho_testcase!(
            ec,
            v,
            3,
            { [(v[1].clone() & !(v[2].clone() | v[3].clone())).index] },
            (
                Circuit::new(3, [Gate::new_nor(0, 1), Gate::new_and(3, 2)], [(4, false)]).unwrap(),
                HashMap::from_iter([(2, 0), (1, 2), (3, 1)])
            )
        );
        expr_creator_ho_testcase!(
            ec,
            v,
            3,
            { [(!(v[2].clone() | v[3].clone()) & v[1].clone()).index] },
            (
                Circuit::new(3, [Gate::new_nor(0, 1), Gate::new_and(3, 2)], [(4, false)]).unwrap(),
                HashMap::from_iter([(2, 0), (1, 2), (3, 1)])
            )
        );
        expr_creator_ho_testcase!(
            ec,
            v,
            3,
            { [(!v[1].clone() & (v[2].clone() ^ !v[3].clone())).index] },
            (
                Circuit::new(3, [Gate::new_xor(0, 1), Gate::new_nor(3, 2)], [(4, false)]).unwrap(),
                HashMap::from_iter([(2, 0), (1, 2), (3, 1)])
            )
        );
        expr_creator_ho_testcase!(
            ec,
            v,
            3,
            { [(!v[1].clone() | (v[2].clone() ^ !v[3].clone())).index] },
            (
                Circuit::new(3, [Gate::new_xor(0, 1), Gate::new_and(3, 2)], [(4, true)]).unwrap(),
                HashMap::from_iter([(2, 0), (1, 2), (3, 1)])
            )
        );
    }

    #[test]
    fn test_to_circuit_1_ho_ext() {
        let mut v = vec![];
        #[allow(unused_assignments)]
        let mut ec = ExprCreator::<isize>::new();
        expr_creator_ho_testcase!(
            ec,
            v,
            1,
            {
                let x = (!v[1].clone()).index;
                [x, x]
            },
            (
                Circuit::new(1, [], [(0, true), (0, true)]).unwrap(),
                HashMap::from_iter([(1, 0)])
            )
        );
        expr_creator_ho_testcase!(
            ec,
            v,
            1,
            {
                let x = (v[1].clone() & v[1].clone()).index;
                [x, x]
            },
            (
                Circuit::new(1, [], [(0, false), (0, false)]).unwrap(),
                HashMap::from_iter([(1, 0)])
            )
        );
        expr_creator_ho_testcase!(
            ec,
            v,
            3,
            {
                let x1 = (!v[1].clone()).index;
                let x2 = (!v[2].clone()).index;
                let x3 = (!v[3].clone()).index;
                [x2, x1, x1, x3, x2, x1, x3]
            },
            (
                Circuit::new(
                    3,
                    [],
                    [
                        (0, true),
                        (1, true),
                        (1, true),
                        (2, true),
                        (0, true),
                        (1, true),
                        (2, true)
                    ]
                )
                .unwrap(),
                HashMap::from_iter([(1, 1), (2, 0), (3, 2)])
            )
        );
        expr_creator_ho_testcase!(
            ec,
            v,
            3,
            {
                let x1 = v[1].index;
                let x2 = v[2].index;
                let x3 = v[3].index;
                let y1 = (!v[1].clone()).index;
                let y2 = (!v[2].clone()).index;
                let y3 = (!v[3].clone()).index;
                [x2, y1, x1, x3, y2, x1, y3]
            },
            (
                Circuit::new(
                    3,
                    [],
                    [
                        (0, false),
                        (1, true),
                        (1, false),
                        (2, false),
                        (0, true),
                        (1, false),
                        (2, true)
                    ]
                )
                .unwrap(),
                HashMap::from_iter([(1, 1), (2, 0), (3, 2)])
            )
        );
    }

    #[test]
    fn test_to_circuit_2_ho() {
        let mut v = vec![];
        #[allow(unused_assignments)]
        let mut ec = ExprCreator::<isize>::new();
        expr_creator_ho_testcase!(
            ec,
            v,
            3,
            {
                let r1 = v[1].clone() & v[2].clone() & v[3].clone();
                let r2 = r1.clone() ^ v[1].clone();
                [r1.index, r2.index]
            },
            (
                Circuit::new(
                    3,
                    [
                        Gate::new_and(0, 1),
                        Gate::new_and(3, 2),
                        Gate::new_xor(4, 0)
                    ],
                    [(4, false), (5, false)]
                )
                .unwrap(),
                HashMap::from_iter([(1, 0), (3, 2), (2, 1)])
            )
        );
        expr_creator_ho_testcase!(
            ec,
            v,
            3,
            {
                let r1 = v[1].clone() & v[2].clone() & v[3].clone();
                let r2 = !r1.clone() ^ v[1].clone();
                [r1.index, r2.index]
            },
            (
                Circuit::new(
                    3,
                    [
                        Gate::new_and(0, 1),
                        Gate::new_and(3, 2),
                        Gate::new_xor(4, 0)
                    ],
                    [(4, false), (5, true)]
                )
                .unwrap(),
                HashMap::from_iter([(1, 0), (3, 2), (2, 1)])
            )
        );
        expr_creator_ho_testcase!(
            ec,
            v,
            3,
            {
                let r1 = v[1].clone() & v[2].clone() & v[3].clone();
                let r2 = r1.clone() | v[1].clone();
                [r1.index, r2.index]
            },
            (
                Circuit::new(
                    3,
                    [
                        Gate::new_and(0, 1),
                        Gate::new_and(3, 2),
                        Gate::new_nor(4, 0)
                    ],
                    [(4, false), (5, true)]
                )
                .unwrap(),
                HashMap::from_iter([(1, 0), (3, 2), (2, 1)])
            )
        );
        expr_creator_ho_testcase!(
            ec,
            v,
            3,
            {
                let r1 = v[1].clone() & v[2].clone() & v[3].clone();
                let r2 = !(r1.clone() | v[1].clone());
                [r1.index, r2.index]
            },
            (
                Circuit::new(
                    3,
                    [
                        Gate::new_and(0, 1),
                        Gate::new_and(3, 2),
                        Gate::new_nor(4, 0)
                    ],
                    [(4, false), (5, false)]
                )
                .unwrap(),
                HashMap::from_iter([(1, 0), (3, 2), (2, 1)])
            )
        );
        expr_creator_ho_testcase!(
            ec,
            v,
            3,
            {
                let r1 = !(v[1].clone() & v[2].clone() & v[3].clone());
                let r2 = !(r1.clone() | v[1].clone());
                [r1.index, r2.index]
            },
            (
                Circuit::new(
                    3,
                    [
                        Gate::new_and(0, 1),
                        Gate::new_and(3, 2),
                        Gate::new_nimpl(4, 0)
                    ],
                    [(4, true), (5, false)]
                )
                .unwrap(),
                HashMap::from_iter([(1, 0), (3, 2), (2, 1)])
            )
        );
        expr_creator_ho_testcase!(
            ec,
            v,
            3,
            {
                let (s, c) = full_adder(v[1].clone(), v[2].clone(), v[3].clone());
                [s.index, c.index]
            },
            (
                Circuit::new(
                    3,
                    [
                        Gate::new_xor(0, 1),
                        Gate::new_xor(3, 2),
                        Gate::new_and(3, 2),
                        Gate::new_and(0, 1),
                        Gate::new_nor(5, 6)
                    ],
                    [(4, false), (7, true)]
                )
                .unwrap(),
                HashMap::from_iter([(1, 0), (3, 2), (2, 1)])
            )
        );
        expr_creator_ho_testcase!(
            ec,
            v,
            3,
            { [bool_ite(v[1].clone(), v[2].clone(), v[3].clone()).index] },
            (
                Circuit::new(
                    3,
                    [
                        Gate::new_and(0, 1),
                        Gate::new_nimpl(2, 0),
                        Gate::new_nor(3, 4)
                    ],
                    [(5, true)]
                )
                .unwrap(),
                HashMap::from_iter([(1, 0), (3, 2), (2, 1)])
            )
        );
    }

    #[test]
    fn test_to_circuit_2_ho_ext() {
        let mut v = vec![];
        #[allow(unused_assignments)]
        let mut ec = ExprCreator::<isize>::new();
        expr_creator_ho_testcase!(
            ec,
            v,
            3,
            {
                let r1 = v[1].clone() & v[2].clone();
                let r2 = v[1].clone() ^ v[2].clone();
                let r1x = r1 & v[3].clone();
                [r1x.index, r2.index]
            },
            (
                Circuit::new(
                    3,
                    [
                        Gate::new_and(0, 1),
                        Gate::new_xor(0, 1),
                        Gate::new_and(3, 2)
                    ],
                    [(5, false), (4, false)]
                )
                .unwrap(),
                HashMap::from_iter([(1, 0), (3, 2), (2, 1)])
            )
        );
        // unused outputs
        expr_creator_ho_testcase!(
            ec,
            v,
            3,
            {
                let r1 = v[1].clone() & v[2].clone();
                let ru = v[1].clone() | v[2].clone(); // unused
                let r2 = v[1].clone() ^ v[2].clone();
                let _ = ru | v[3].clone(); // unused
                let r1x = r1 & v[3].clone();
                [r1x.index, r2.index]
            },
            (
                Circuit::new(
                    3,
                    [
                        Gate::new_and(0, 1),
                        Gate::new_xor(0, 1),
                        Gate::new_and(3, 2)
                    ],
                    [(5, false), (4, false)]
                )
                .unwrap(),
                HashMap::from_iter([(1, 0), (3, 2), (2, 1)])
            )
        );
        // unused outputs
        expr_creator_ho_testcase!(
            ec,
            v,
            3,
            {
                let r1 = v[1].clone() & v[2].clone();
                let ru = v[1].clone() | v[2].clone(); // unused
                let r2 = v[1].clone() ^ v[2].clone();
                let _ = ru | v[3].clone(); // unused
                let _ = r2.clone() ^ v[3].clone(); // unused
                let r1x = r1 & v[3].clone();
                [r1x.index, r2.index]
            },
            (
                Circuit::new(
                    3,
                    [
                        Gate::new_and(0, 1),
                        Gate::new_xor(0, 1),
                        Gate::new_and(3, 2)
                    ],
                    [(5, false), (4, false)]
                )
                .unwrap(),
                HashMap::from_iter([(1, 0), (3, 2), (2, 1)])
            )
        );
    }

    #[test]
    fn test_to_circuit_3_ho() {
        let ec = ExprCreator::<isize>::with_history_order();
        let a = IntExprNode::<_, U3, false>::variable(ec.clone());
        let b = IntExprNode::<_, U3, false>::variable(ec.clone());
        let c = a.clone().mod_sub(b.clone());
        let mut indexes = [0; 3];
        (0..3).for_each(|x| indexes[x] = c.bit(x).index);
        let (circuit, input_map) = ec.borrow().to_circuit(indexes);
        for av in 0u32..8 {
            for bv in 0u32..8 {
                let exp_cv = (av.overflowing_sub(bv).0) & 7;
                let mut input = [false; 6];
                (0..3).for_each(|x| {
                    input[input_map[&a.bit(x).varlit().unwrap()]] = ((av >> x) & 1) != 0;
                    input[input_map[&b.bit(x).varlit().unwrap()]] = ((bv >> x) & 1) != 0;
                });
                let cv_vec = circuit.eval(input);
                let mut cv = 0;
                cv_vec.into_iter().enumerate().for_each(|(i, bv)| {
                    if bv {
                        cv |= 1 << i;
                    }
                });
                assert_eq!(exp_cv, cv, "{}-{}", av, bv);
            }
        }

        let ec = ExprCreator::<isize>::with_history_order();
        let a = IntExprNode::<_, U4, false>::variable(ec.clone());
        let b = IntExprNode::<_, U4, false>::variable(ec.clone());
        let c = a.clone().fullmul(b.clone());
        let mut indexes = [0; 8];
        (0..8).for_each(|x| indexes[x] = c.bit(x).index);
        let (circuit, input_map) = ec.borrow().to_circuit(indexes);
        for av in 0u32..16 {
            for bv in 0u32..16 {
                let exp_cv = (av * bv) & 0xff;
                let mut input = [false; 8];
                (0..4).for_each(|x| {
                    input[input_map[&a.bit(x).varlit().unwrap()]] = ((av >> x) & 1) != 0;
                    input[input_map[&b.bit(x).varlit().unwrap()]] = ((bv >> x) & 1) != 0;
                });
                let cv_vec = circuit.eval(input);
                let mut cv = 0;
                cv_vec.into_iter().enumerate().for_each(|(i, bv)| {
                    if bv {
                        cv |= 1 << i;
                    }
                });
                assert_eq!(exp_cv, cv, "fullmul({}, {})", av, bv);
            }
        }

        let ec = ExprCreator::<isize>::with_history_order();
        let a = IntExprNode::<_, U5, false>::variable(ec.clone());
        let b = IntExprNode::<_, U5, false>::variable(ec.clone());
        let (d, m, c) = a.clone().divmod(b.clone());
        let mut indexes = [0; 11];
        (0..5).for_each(|x| indexes[x] = d.bit(x).index);
        (0..5).for_each(|x| indexes[5 + x] = m.bit(x).index);
        indexes[10] = c.index;
        let (circuit, input_map) = ec.borrow().to_circuit(indexes);
        for av in 0u32..32 {
            for bv in 0u32..32 {
                let exp_dv = if bv != 0 { av / bv } else { 0 };
                let exp_mv = if bv != 0 { av % bv } else { 0 };
                let exp_cv = bv != 0;
                let mut input = [false; 10];
                (0..5).for_each(|x| {
                    input[input_map[&a.bit(x).varlit().unwrap()]] = ((av >> x) & 1) != 0;
                    input[input_map[&b.bit(x).varlit().unwrap()]] = ((bv >> x) & 1) != 0;
                });
                let rv_vec = circuit.eval(input);
                let mut dv = 0;
                let mut mv = 0;
                let mut cv = false;
                rv_vec.into_iter().enumerate().for_each(|(i, bv)| {
                    if bv {
                        if i < 5 {
                            dv |= 1 << i;
                        } else if i < 10 {
                            mv |= 1 << (i - 5);
                        } else {
                            cv = true;
                        }
                    }
                });
                println!("dcfv: {} {}: {} {} {}", av, bv, dv, mv, cv);
                assert_eq!(exp_cv, cv, "divmod({}, {}).c", av, bv);
                if exp_cv {
                    assert_eq!(exp_dv, dv, "divmod({}, {}).d", av, bv);
                    assert_eq!(exp_mv, mv, "divmod({}, {}).m", av, bv);
                }
            }
        }

        for av in 0u32..32 {
            let ec = ExprCreator::<isize>::with_history_order();
            let a = IntExprNode::<_, U5, false>::try_constant(ec.clone(), av).unwrap();
            let b = IntExprNode::<_, U5, false>::variable(ec.clone());
            let (d, m, c) = a.clone().divmod(b.clone());
            let mut indexes = [0; 11];
            (0..5).for_each(|x| indexes[x] = d.bit(x).index);
            (0..5).for_each(|x| indexes[5 + x] = m.bit(x).index);
            indexes[10] = c.index;
            let (circuit, input_map) = ec.borrow().to_circuit(indexes);
            for bv in 0u32..32 {
                let exp_dv = if bv != 0 { av / bv } else { 0 };
                let exp_mv = if bv != 0 { av % bv } else { 0 };
                let exp_cv = bv != 0;
                let mut input = [false; 10];
                (0..5).for_each(|x| {
                    input[input_map[&b.bit(x).varlit().unwrap()]] = ((bv >> x) & 1) != 0;
                });
                let rv_vec = circuit.eval(input);
                let mut dv = 0;
                let mut mv = 0;
                let mut cv = false;
                rv_vec.into_iter().enumerate().for_each(|(i, bv)| {
                    if bv {
                        if i < 5 {
                            dv |= 1 << i;
                        } else if i < 10 {
                            mv |= 1 << (i - 5);
                        } else {
                            cv = true;
                        }
                    }
                });
                println!("dcfv: {} {}: {} {} {}", av, bv, dv, mv, cv);
                assert_eq!(exp_cv, cv, "divmod({}, {}).c", av, bv);
                if exp_cv {
                    assert_eq!(exp_dv, dv, "divmod({}, {}).d", av, bv);
                    assert_eq!(exp_mv, mv, "divmod({}, {}).m", av, bv);
                }
            }
        }

        let ec = ExprCreator::<isize>::with_history_order();
        let a = IntExprNode::<_, U8, true>::variable(ec.clone());
        let b = IntExprNode::<_, U8, true>::variable(ec.clone());
        let (d, m, c) = a.clone().divmod(b.clone());
        let mut indexes = [0; 17];
        (0..8).for_each(|x| indexes[x] = d.bit(x).index);
        (0..8).for_each(|x| indexes[8 + x] = m.bit(x).index);
        indexes[16] = c.index;
        let (circuit, input_map) = ec.borrow().to_circuit(indexes);
        for av in i8::MIN..=i8::MAX {
            for bv in i8::MIN..=i8::MAX {
                let exp_cv = (bv != 0) && (av != i8::MIN || bv != -1);
                let exp_dv = if exp_cv { av / bv } else { 0 };
                let exp_mv = if exp_cv { av % bv } else { 0 };
                let mut input = [false; 16];
                (0..8).for_each(|x| {
                    input[input_map[&a.bit(x).varlit().unwrap()]] = ((av >> x) & 1) != 0;
                    input[input_map[&b.bit(x).varlit().unwrap()]] = ((bv >> x) & 1) != 0;
                });
                let rv_vec = circuit.eval(input);
                let mut dv = 0;
                let mut mv = 0;
                let mut cv = false;
                rv_vec.into_iter().enumerate().for_each(|(i, bv)| {
                    if bv {
                        if i < 8 {
                            dv |= 1 << i;
                        } else if i < 16 {
                            mv |= 1 << (i - 8);
                        } else {
                            cv = true;
                        }
                    }
                });
                println!("dcfv: {} {}: {} {} {}", av, bv, dv, mv, cv);
                assert_eq!(exp_cv, cv, "divmod({}, {}).c", av, bv);
                if exp_cv {
                    assert_eq!(exp_dv, dv, "divmod({}, {}).d", av, bv);
                    assert_eq!(exp_mv, mv, "divmod({}, {}).m", av, bv);
                }
            }
        }

        let ec = ExprCreator::<isize>::with_history_order();
        let a = DynIntExprNode::<_, false>::variable(ec.clone(), 5);
        let b = DynIntExprNode::<_, false>::variable(ec.clone(), 5);
        let (d, m, c) = a.clone().divmod(b.clone());
        let mut indexes = [0; 11];
        (0..5).for_each(|x| indexes[x] = d.bit(x).index);
        (0..5).for_each(|x| indexes[5 + x] = m.bit(x).index);
        indexes[10] = c.index;
        let (circuit, input_map) = ec.borrow().to_circuit(indexes);
        for av in 0u32..32 {
            for bv in 0u32..32 {
                let exp_dv = if bv != 0 { av / bv } else { 0 };
                let exp_mv = if bv != 0 { av % bv } else { 0 };
                let exp_cv = bv != 0;
                let mut input = [false; 10];
                (0..5).for_each(|x| {
                    input[input_map[&a.bit(x).varlit().unwrap()]] = ((av >> x) & 1) != 0;
                    input[input_map[&b.bit(x).varlit().unwrap()]] = ((bv >> x) & 1) != 0;
                });
                let rv_vec = circuit.eval(input);
                let mut dv = 0;
                let mut mv = 0;
                let mut cv = false;
                rv_vec.into_iter().enumerate().for_each(|(i, bv)| {
                    if bv {
                        if i < 5 {
                            dv |= 1 << i;
                        } else if i < 10 {
                            mv |= 1 << (i - 5);
                        } else {
                            cv = true;
                        }
                    }
                });
                println!("dcfv: {} {}: {} {} {}", av, bv, dv, mv, cv);
                assert_eq!(exp_cv, cv, "divmod({}, {}).c", av, bv);
                if exp_cv {
                    assert_eq!(exp_dv, dv, "divmod({}, {}).d", av, bv);
                    assert_eq!(exp_mv, mv, "divmod({}, {}).m", av, bv);
                }
            }
        }

        let ec = ExprCreator::<isize>::with_history_order();
        let a = DynIntExprNode::<_, true>::variable(ec.clone(), 8);
        let b = DynIntExprNode::<_, true>::variable(ec.clone(), 8);
        let (d, m, c) = a.clone().divmod(b.clone());
        let mut indexes = [0; 17];
        (0..8).for_each(|x| indexes[x] = d.bit(x).index);
        (0..8).for_each(|x| indexes[8 + x] = m.bit(x).index);
        indexes[16] = c.index;
        let (circuit, input_map) = ec.borrow().to_circuit(indexes);
        println!("Circuit len: {}", circuit.len());
        for av in i8::MIN..=i8::MAX {
            for bv in i8::MIN..=i8::MAX {
                let exp_cv = (bv != 0) && (av != i8::MIN || bv != -1);
                let exp_dv = if exp_cv { av / bv } else { 0 };
                let exp_mv = if exp_cv { av % bv } else { 0 };
                let mut input = [false; 16];
                (0..8).for_each(|x| {
                    input[input_map[&a.bit(x).varlit().unwrap()]] = ((av >> x) & 1) != 0;
                    input[input_map[&b.bit(x).varlit().unwrap()]] = ((bv >> x) & 1) != 0;
                });
                let rv_vec = circuit.eval(input);
                let mut dv = 0;
                let mut mv = 0;
                let mut cv = false;
                rv_vec.into_iter().enumerate().for_each(|(i, bv)| {
                    if bv {
                        if i < 8 {
                            dv |= 1 << i;
                        } else if i < 16 {
                            mv |= 1 << (i - 8);
                        } else {
                            cv = true;
                        }
                    }
                });
                println!("dcfv: {} {}: {} {} {}", av, bv, dv, mv, cv);
                assert_eq!(exp_cv, cv, "divmod({}, {}).c", av, bv);
                if exp_cv {
                    assert_eq!(exp_dv, dv, "divmod({}, {}).d", av, bv);
                    assert_eq!(exp_mv, mv, "divmod({}, {}).m", av, bv);
                }
            }
        }
    }
}
