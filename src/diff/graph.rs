//! A graph representation for computing tree diffs.

use bumpalo::Bump;
use rpds::Stack;
use std::{
    cmp::min,
    fmt,
    hash::{Hash, Hasher},
};
use strsim::normalized_levenshtein;

use crate::{
    diff::changes::{insert_deep_unchanged, ChangeKind, ChangeMap},
    parse::syntax::{AtomKind, Syntax, SyntaxId},
};
use Edge::*;

/// A vertex in a directed acyclic graph that represents a diff.
///
/// Each vertex represents two pointers: one to the next unmatched LHS
/// syntax, and one to the next unmatched RHS syntax.
///
/// For example, suppose we have `X A` on the LHS and `A` on the
/// RHS. Our start vertex looks like this.
///
/// ```text
/// LHS: X A     RHS: A
///      ^            ^
/// ```
///
/// From this vertex, we could take [`Edge::NovelAtomLHS`], bringing
/// us to this vertex.
///
/// ```text
/// LHS: X A     RHS: A
///        ^          ^
/// ```
///
/// Alternatively, we could take the [`Edge::NovelAtomRHS`], bringing us
/// to this vertex.
///
/// ```text
/// LHS: X A     RHS: A
///      ^              ^
/// ```
#[derive(Debug, Clone)]
pub struct Vertex<'a> {
    pub lhs_syntax: Option<&'a Syntax<'a>>,
    pub rhs_syntax: Option<&'a Syntax<'a>>,
    parents: Stack<EnteredDelimiter<'a>>,
    lhs_parent_id: Option<SyntaxId>,
    rhs_parent_id: Option<SyntaxId>,
    can_pop_either: bool,
}

impl<'a> PartialEq for Vertex<'a> {
    fn eq(&self, other: &Self) -> bool {
        self.lhs_syntax.map(|node| node.id()) == other.lhs_syntax.map(|node| node.id())
            && self.rhs_syntax.map(|node| node.id()) == other.rhs_syntax.map(|node| node.id())
            // Strictly speaking, we should compare the whole
            // EnteredDelimiter stack, not just the immediate
            // parents. By taking the immediate parent, we have
            // vertices with different stacks that are 'equal'.
            //
            // This makes the graph traversal path dependent: the
            // first vertex we see 'wins', and we use it for deciding
            // how we can pop.
            //
            // In practice this seems to work well. The first vertex
            // has the lowest cost, so has the most PopBoth
            // occurrences, which is the best outcome.
            //
            // Handling this properly would require considering many
            // more vertices to be distinct, exponentially increasing
            // the graph size relative to tree depth.
            && self.lhs_parent_id == other.lhs_parent_id
            && self.rhs_parent_id == other.rhs_parent_id
            // We do want to distinguish whether we can pop each side
            // independently though. Without this, if we find a case
            // where we can pop sides together, we don't consider the
            // case where we get a better diff by popping each side
            // separately.
            && self.can_pop_either == other.can_pop_either
    }
}
impl<'a> Eq for Vertex<'a> {}

impl<'a> Hash for Vertex<'a> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.lhs_syntax.map(|node| node.id()).hash(state);
        self.rhs_syntax.map(|node| node.id()).hash(state);

        self.lhs_parent_id.hash(state);
        self.rhs_parent_id.hash(state);
        self.can_pop_either.hash(state);
    }
}

/// Tracks entering syntax List nodes.
#[derive(Clone)]
enum EnteredDelimiter<'a> {
    /// If we've entered the LHS or RHS separately, we can pop either
    /// side independently.
    ///
    /// Assumes that at least one stack is non-empty.
    PopEither((Stack<&'a Syntax<'a>>, Stack<&'a Syntax<'a>>)),
    /// If we've entered the LHS and RHS together, we must pop both
    /// sides together too. Otherwise we'd consider the following case to have no changes.
    ///
    /// ```text
    /// Old: (a b c)
    /// New: (a b) c
    /// ```
    PopBoth((&'a Syntax<'a>, &'a Syntax<'a>)),
}

impl<'a> fmt::Debug for EnteredDelimiter<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let desc = match self {
            EnteredDelimiter::PopEither((lhs_delims, rhs_delims)) => {
                format!(
                    "PopEither(lhs count: {}, rhs count: {})",
                    lhs_delims.size(),
                    rhs_delims.size()
                )
            }
            EnteredDelimiter::PopBoth(_) => "PopBoth".to_string(),
        };
        f.write_str(&desc)
    }
}

fn push_both_delimiters<'a>(
    entered: &Stack<EnteredDelimiter<'a>>,
    lhs_delim: &'a Syntax<'a>,
    rhs_delim: &'a Syntax<'a>,
) -> Stack<EnteredDelimiter<'a>> {
    entered.push(EnteredDelimiter::PopBoth((lhs_delim, rhs_delim)))
}

fn can_pop_either_parent(entered: &Stack<EnteredDelimiter>) -> bool {
    matches!(entered.peek(), Some(EnteredDelimiter::PopEither(_)))
}

fn try_pop_both<'a>(
    entered: &Stack<EnteredDelimiter<'a>>,
) -> Option<(&'a Syntax<'a>, &'a Syntax<'a>, Stack<EnteredDelimiter<'a>>)> {
    match entered.peek() {
        Some(EnteredDelimiter::PopBoth((lhs_delim, rhs_delim))) => {
            Some((lhs_delim, rhs_delim, entered.pop().unwrap()))
        }
        _ => None,
    }
}

fn try_pop_lhs<'a>(
    entered: &Stack<EnteredDelimiter<'a>>,
) -> Option<(&'a Syntax<'a>, Stack<EnteredDelimiter<'a>>)> {
    match entered.peek() {
        Some(EnteredDelimiter::PopEither((lhs_delims, rhs_delims))) => match lhs_delims.peek() {
            Some(lhs_delim) => {
                let mut entered = entered.pop().unwrap();
                let new_lhs_delims = lhs_delims.pop().unwrap();

                if !new_lhs_delims.is_empty() || !rhs_delims.is_empty() {
                    entered = entered.push(EnteredDelimiter::PopEither((
                        new_lhs_delims,
                        rhs_delims.clone(),
                    )));
                }

                Some((lhs_delim, entered))
            }
            None => None,
        },
        _ => None,
    }
}

fn try_pop_rhs<'a>(
    entered: &Stack<EnteredDelimiter<'a>>,
) -> Option<(&'a Syntax<'a>, Stack<EnteredDelimiter<'a>>)> {
    match entered.peek() {
        Some(EnteredDelimiter::PopEither((lhs_delims, rhs_delims))) => match rhs_delims.peek() {
            Some(rhs_delim) => {
                let mut entered = entered.pop().unwrap();
                let new_rhs_delims = rhs_delims.pop().unwrap();

                if !lhs_delims.is_empty() || !new_rhs_delims.is_empty() {
                    entered = entered.push(EnteredDelimiter::PopEither((
                        lhs_delims.clone(),
                        new_rhs_delims,
                    )));
                }

                Some((rhs_delim, entered))
            }
            None => None,
        },
        _ => None,
    }
}

fn push_lhs_delimiter<'a>(
    entered: &Stack<EnteredDelimiter<'a>>,
    delimiter: &'a Syntax<'a>,
) -> Stack<EnteredDelimiter<'a>> {
    let mut modifying_head = false;
    let (mut lhs_delims, rhs_delims) = match entered.peek() {
        Some(EnteredDelimiter::PopEither((lhs_delims, rhs_delims))) => {
            modifying_head = true;
            (lhs_delims.clone(), rhs_delims.clone())
        }
        _ => (Stack::new(), Stack::new()),
    };
    lhs_delims = lhs_delims.push(delimiter);

    let entered = if modifying_head {
        entered.pop().unwrap()
    } else {
        entered.clone()
    };
    entered.push(EnteredDelimiter::PopEither((lhs_delims, rhs_delims)))
}

fn push_rhs_delimiter<'a>(
    entered: &Stack<EnteredDelimiter<'a>>,
    delimiter: &'a Syntax<'a>,
) -> Stack<EnteredDelimiter<'a>> {
    let mut modifying_head = false;
    let (lhs_delims, mut rhs_delims) = match entered.peek() {
        Some(EnteredDelimiter::PopEither((lhs_delims, rhs_delims))) => {
            modifying_head = true;
            (lhs_delims.clone(), rhs_delims.clone())
        }
        _ => (Stack::new(), Stack::new()),
    };
    rhs_delims = rhs_delims.push(delimiter);

    let entered = if modifying_head {
        entered.pop().unwrap()
    } else {
        entered.clone()
    };
    entered.push(EnteredDelimiter::PopEither((lhs_delims, rhs_delims)))
}

impl<'a> Vertex<'a> {
    pub fn is_end(&self) -> bool {
        self.lhs_syntax.is_none() && self.rhs_syntax.is_none() && self.parents.is_empty()
    }

    pub fn new(lhs_syntax: Option<&'a Syntax<'a>>, rhs_syntax: Option<&'a Syntax<'a>>) -> Self {
        let parents = Stack::new();
        Vertex {
            lhs_syntax,
            rhs_syntax,
            parents,
            lhs_parent_id: None,
            rhs_parent_id: None,
            can_pop_either: false,
        }
    }
}

/// An edge in our graph, with an associated [`cost`](Edge::cost).
///
/// A syntax node can always be marked as novel, so a vertex will have
/// at least a NovelFoo edge. Depending on the syntax nodes of the
/// current [`Vertex`], other edges may also be available.
///
/// See [`neighbours`] for all the edges available for a given `Vertex`.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum Edge {
    UnchangedNode { depth_difference: u32 },
    EnterUnchangedDelimiter { depth_difference: u32 },
    ReplacedComment { levenshtein_pct: u8 },
    NovelAtomLHS { contiguous: bool },
    NovelAtomRHS { contiguous: bool },
    // TODO: An EnterNovelDelimiterBoth edge might help performance
    // rather doing LHS and RHS separately.
    EnterNovelDelimiterLHS { contiguous: bool },
    EnterNovelDelimiterRHS { contiguous: bool },
    ExitDelimiterLHS,
    ExitDelimiterRHS,
    ExitDelimiterBoth,
}

impl Edge {
    pub fn cost(self) -> u64 {
        match self {
            // When we're at the end of a list, there's only one exit
            // delimiter possibility, so the cost doesn't matter. We
            // choose a non-zero number as it's easier to reason
            // about.
            ExitDelimiterBoth => 1,
            // Choose a higher value for exiting individually. This
            // shouldn't matter since entering a novel delimiter is
            // already more expensive than entering a matched
            // delimiter, but be defensive.
            ExitDelimiterLHS | ExitDelimiterRHS => 2,

            // Matching nodes is always best.
            UnchangedNode { depth_difference } => min(40, u64::from(depth_difference) + 1),
            // Matching an outer delimiter is good.
            EnterUnchangedDelimiter { depth_difference } => {
                100 + min(40, u64::from(depth_difference))
            }

            // Replacing a comment is better than treating it as novel.
            ReplacedComment { levenshtein_pct } => 150 + u64::from(100 - levenshtein_pct),

            // Otherwise, we've added/removed a node.
            NovelAtomLHS { contiguous }
            | NovelAtomRHS { contiguous }
            | EnterNovelDelimiterLHS { contiguous }
            | EnterNovelDelimiterRHS { contiguous } => {
                if contiguous {
                    300
                } else {
                    // This needs to be more than 40 greater than the
                    // contiguous case. Otherwise, we end up choosing
                    // a badly positioned unchanged delimiter just
                    // because it has a better depth difference.
                    //
                    // TODO: write a test for this case.
                    350
                }
            }
        }
    }
}

/// Calculate all the neighbours from `v` and write them to `buf`.
pub fn neighbours<'a, 'b>(
    v: &Vertex<'a>,
    buf: &mut [Option<(Edge, &'b Vertex<'a>)>],
    alloc: &'b Bump,
) {
    for item in &mut *buf {
        *item = None;
    }

    let mut i = 0;

    if v.lhs_syntax.is_none() && v.rhs_syntax.is_none() {
        if let Some((lhs_parent, rhs_parent, parents_next)) = try_pop_both(&v.parents) {
            // We have exhausted all the nodes on both lists, so we can
            // move up to the parent node.

            // Continue from sibling of parent.
            buf[i] = Some((
                ExitDelimiterBoth,
                alloc.alloc(Vertex {
                    lhs_syntax: lhs_parent.next_sibling(),
                    rhs_syntax: rhs_parent.next_sibling(),
                    can_pop_either: can_pop_either_parent(&parents_next),
                    parents: parents_next,
                    lhs_parent_id: lhs_parent.parent().map(Syntax::id),
                    rhs_parent_id: rhs_parent.parent().map(Syntax::id),
                }),
            ));
            i += 1;
        }
    }

    if v.lhs_syntax.is_none() {
        if let Some((lhs_parent, parents_next)) = try_pop_lhs(&v.parents) {
            // Move to next after LHS parent.

            // Continue from sibling of parent.
            buf[i] = Some((
                ExitDelimiterLHS,
                alloc.alloc(Vertex {
                    lhs_syntax: lhs_parent.next_sibling(),
                    rhs_syntax: v.rhs_syntax,
                    can_pop_either: can_pop_either_parent(&parents_next),
                    parents: parents_next,
                    lhs_parent_id: lhs_parent.parent().map(Syntax::id),
                    rhs_parent_id: v.rhs_parent_id,
                }),
            ));
            i += 1;
        }
    }

    if v.rhs_syntax.is_none() {
        if let Some((rhs_parent, parents_next)) = try_pop_rhs(&v.parents) {
            // Move to next after RHS parent.

            // Continue from sibling of parent.
            buf[i] = Some((
                ExitDelimiterRHS,
                alloc.alloc(Vertex {
                    lhs_syntax: v.lhs_syntax,
                    rhs_syntax: rhs_parent.next_sibling(),
                    can_pop_either: can_pop_either_parent(&parents_next),
                    parents: parents_next,
                    lhs_parent_id: v.lhs_parent_id,
                    rhs_parent_id: rhs_parent.parent().map(Syntax::id),
                }),
            ));
            i += 1;
        }
    }

    if let (Some(lhs_syntax), Some(rhs_syntax)) = (&v.lhs_syntax, &v.rhs_syntax) {
        if lhs_syntax == rhs_syntax {
            let depth_difference = (lhs_syntax.num_ancestors() as i32
                - rhs_syntax.num_ancestors() as i32)
                .abs() as u32;

            // Both nodes are equal, the happy case.
            buf[i] = Some((
                UnchangedNode { depth_difference },
                alloc.alloc(Vertex {
                    lhs_syntax: lhs_syntax.next_sibling(),
                    rhs_syntax: rhs_syntax.next_sibling(),
                    parents: v.parents.clone(),
                    lhs_parent_id: v.lhs_parent_id,
                    rhs_parent_id: v.rhs_parent_id,
                    can_pop_either: v.can_pop_either,
                }),
            ));
            i += 1;
        }

        if let (
            Syntax::List {
                open_content: lhs_open_content,
                close_content: lhs_close_content,
                children: lhs_children,
                ..
            },
            Syntax::List {
                open_content: rhs_open_content,
                close_content: rhs_close_content,
                children: rhs_children,
                ..
            },
        ) = (lhs_syntax, rhs_syntax)
        {
            // The list delimiters are equal, but children may not be.
            if lhs_open_content == rhs_open_content && lhs_close_content == rhs_close_content {
                let lhs_next = lhs_children.get(0).copied();
                let rhs_next = rhs_children.get(0).copied();

                // TODO: be consistent between parents_next and next_parents.
                let parents_next = push_both_delimiters(&v.parents, lhs_syntax, rhs_syntax);

                let depth_difference = (lhs_syntax.num_ancestors() as i32
                    - rhs_syntax.num_ancestors() as i32)
                    .abs() as u32;

                buf[i] = Some((
                    EnterUnchangedDelimiter { depth_difference },
                    alloc.alloc(Vertex {
                        lhs_syntax: lhs_next,
                        rhs_syntax: rhs_next,
                        parents: parents_next,
                        lhs_parent_id: Some(lhs_syntax.id()),
                        rhs_parent_id: Some(rhs_syntax.id()),
                        can_pop_either: false,
                    }),
                ));
                i += 1;
            }
        }

        if let (
            Syntax::Atom {
                content: lhs_content,
                kind: AtomKind::Comment,
                ..
            },
            Syntax::Atom {
                content: rhs_content,
                kind: AtomKind::Comment,
                ..
            },
        ) = (lhs_syntax, rhs_syntax)
        {
            // Both sides are comments and their content is reasonably
            // similar.
            if lhs_content != rhs_content {
                let levenshtein_pct =
                    (normalized_levenshtein(lhs_content, rhs_content) * 100.0).round() as u8;
                buf[i] = Some((
                    ReplacedComment { levenshtein_pct },
                    alloc.alloc(Vertex {
                        lhs_syntax: lhs_syntax.next_sibling(),
                        rhs_syntax: rhs_syntax.next_sibling(),
                        parents: v.parents.clone(),
                        lhs_parent_id: v.lhs_parent_id,
                        rhs_parent_id: v.rhs_parent_id,
                        can_pop_either: v.can_pop_either,
                    }),
                ));
                i += 1;
            }
        }
    }

    if let Some(lhs_syntax) = &v.lhs_syntax {
        match lhs_syntax {
            // Step over this novel atom.
            Syntax::Atom { .. } => {
                buf[i] = Some((
                    NovelAtomLHS {
                        // TODO: should this apply if prev is a parent
                        // node rather than a sibling?
                        contiguous: lhs_syntax.prev_is_contiguous(),
                    },
                    alloc.alloc(Vertex {
                        lhs_syntax: lhs_syntax.next_sibling(),
                        rhs_syntax: v.rhs_syntax,
                        parents: v.parents.clone(),
                        lhs_parent_id: v.lhs_parent_id,
                        rhs_parent_id: v.rhs_parent_id,
                        can_pop_either: v.can_pop_either,
                    }),
                ));
                i += 1;
            }
            // Step into this partially/fully novel list.
            Syntax::List { children, .. } => {
                let lhs_next = children.get(0).copied();

                let parents_next = push_lhs_delimiter(&v.parents, lhs_syntax);

                buf[i] = Some((
                    EnterNovelDelimiterLHS {
                        contiguous: lhs_syntax.prev_is_contiguous(),
                    },
                    alloc.alloc(Vertex {
                        lhs_syntax: lhs_next,
                        rhs_syntax: v.rhs_syntax,
                        parents: parents_next,
                        lhs_parent_id: Some(lhs_syntax.id()),
                        rhs_parent_id: v.rhs_parent_id,
                        can_pop_either: true,
                    }),
                ));
                i += 1;
            }
        }
    }

    if let Some(rhs_syntax) = &v.rhs_syntax {
        match rhs_syntax {
            // Step over this novel atom.
            Syntax::Atom { .. } => {
                buf[i] = Some((
                    NovelAtomRHS {
                        contiguous: rhs_syntax.prev_is_contiguous(),
                    },
                    alloc.alloc(Vertex {
                        lhs_syntax: v.lhs_syntax,
                        rhs_syntax: rhs_syntax.next_sibling(),
                        parents: v.parents.clone(),
                        lhs_parent_id: v.lhs_parent_id,
                        rhs_parent_id: v.rhs_parent_id,
                        can_pop_either: v.can_pop_either,
                    }),
                ));
                i += 1;
            }
            // Step into this partially/fully novel list.
            Syntax::List { children, .. } => {
                let rhs_next = children.get(0).copied();

                let parents_next = push_rhs_delimiter(&v.parents, rhs_syntax);

                buf[i] = Some((
                    EnterNovelDelimiterRHS {
                        contiguous: rhs_syntax.prev_is_contiguous(),
                    },
                    alloc.alloc(Vertex {
                        lhs_syntax: v.lhs_syntax,
                        rhs_syntax: rhs_next,
                        parents: parents_next,
                        lhs_parent_id: v.lhs_parent_id,
                        rhs_parent_id: Some(rhs_syntax.id()),
                        can_pop_either: true,
                    }),
                ));
                i += 1;
            }
        }
    }
    assert!(
        i > 0,
        "Must always find some next steps if node is not the end"
    );
}

pub fn populate_change_map<'a>(route: &[(Edge, Vertex<'a>)], change_map: &mut ChangeMap<'a>) {
    for (e, v) in route {
        match e {
            ExitDelimiterBoth | ExitDelimiterLHS | ExitDelimiterRHS => {
                // Nothing to do: we have already marked this node when we entered it.
            }
            UnchangedNode { .. } => {
                // No change on this node or its children.
                let lhs = v.lhs_syntax.unwrap();
                let rhs = v.rhs_syntax.unwrap();

                insert_deep_unchanged(lhs, rhs, change_map);
                insert_deep_unchanged(rhs, lhs, change_map);
            }
            EnterUnchangedDelimiter { .. } => {
                // No change on the outer delimiter, but children may
                // have changed.
                let lhs = v.lhs_syntax.unwrap();
                let rhs = v.rhs_syntax.unwrap();
                change_map.insert(lhs, ChangeKind::Unchanged(rhs));
                change_map.insert(rhs, ChangeKind::Unchanged(lhs));
            }
            ReplacedComment { levenshtein_pct } => {
                let lhs = v.lhs_syntax.unwrap();
                let rhs = v.rhs_syntax.unwrap();

                if *levenshtein_pct > 40 {
                    change_map.insert(lhs, ChangeKind::ReplacedComment(lhs, rhs));
                    change_map.insert(rhs, ChangeKind::ReplacedComment(rhs, lhs));
                } else {
                    change_map.insert(lhs, ChangeKind::Novel);
                    change_map.insert(rhs, ChangeKind::Novel);
                }
            }
            NovelAtomLHS { .. } | EnterNovelDelimiterLHS { .. } => {
                let lhs = v.lhs_syntax.unwrap();
                change_map.insert(lhs, ChangeKind::Novel);
            }
            NovelAtomRHS { .. } | EnterNovelDelimiterRHS { .. } => {
                let rhs = v.rhs_syntax.unwrap();
                change_map.insert(rhs, ChangeKind::Novel);
            }
        }
    }
}
