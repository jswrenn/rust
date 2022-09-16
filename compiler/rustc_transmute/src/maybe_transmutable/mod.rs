use crate::Map;
use crate::{Answer, Reason};

#[cfg(test)]
mod tests;

mod query_context;
use query_context::QueryContext;

use crate::layout::{self, dfa, Byte, Dfa, Nfa, Tree, Uninhabited};
pub(crate) struct MaybeTransmutableQuery<L, C>
where
    C: QueryContext,
{
    src: L,
    dst: L,
    scope: <C as QueryContext>::Scope,
    assume: crate::Assume,
    context: C,
}

impl<L, C> MaybeTransmutableQuery<L, C>
where
    C: QueryContext,
{
    pub(crate) fn new(
        src: L,
        dst: L,
        scope: <C as QueryContext>::Scope,
        assume: crate::Assume,
        context: C,
    ) -> Self {
        Self { src, dst, scope, assume, context }
    }

    pub(crate) fn map_layouts<F, M>(
        self,
        f: F,
    ) -> Result<MaybeTransmutableQuery<M, C>, Answer<<C as QueryContext>::Ref>>
    where
        F: FnOnce(
            L,
            L,
            <C as QueryContext>::Scope,
            &C,
        ) -> Result<(M, M), Answer<<C as QueryContext>::Ref>>,
    {
        let Self { src, dst, scope, assume, context } = self;

        let (src, dst) = f(src, dst, scope, &context)?;

        Ok(MaybeTransmutableQuery { src, dst, scope, assume, context })
    }
}

#[cfg(feature = "rustc")]
mod rustc {
    use super::*;
    use crate::layout::tree::Err;

    use rustc_middle::ty::Ty;
    use rustc_middle::ty::TyCtxt;

    impl<'tcx> MaybeTransmutableQuery<Ty<'tcx>, TyCtxt<'tcx>> {
        /// This method begins by converting `src` and `dst` from `Ty`s to `Tree`s,
        /// then computes an answer using those trees.
        #[instrument(level = "debug", skip(self), fields(src = ?self.src, dst = ?self.dst))]
        pub fn answer(self) -> Answer<<TyCtxt<'tcx> as QueryContext>::Ref> {
            let query_or_answer = self.map_layouts(|src, dst, scope, &context| {
                // Convert `src` and `dst` from their rustc representations, to `Tree`-based
                // representations. If these conversions fail, conclude that the transmutation is
                // unacceptable; the layouts of both the source and destination types must be
                // well-defined.
                let src = Tree::from_ty(src, context).map_err(|err| match err {
                    // Answer `Yes` here, because "Unknown Type" will already be reported by
                    // rustc. No need to spam the user with more errors.
                    Err::Unknown => Answer::Yes,
                    Err::Unspecified => Answer::No(Reason::SrcIsUnspecified),
                })?;

                let dst = Tree::from_ty(dst, context).map_err(|err| match err {
                    Err::Unknown => Answer::Yes,
                    Err::Unspecified => Answer::No(Reason::DstIsUnspecified),
                })?;

                Ok((src, dst))
            });

            match query_or_answer {
                Ok(query) => query.answer(),
                Err(answer) => answer,
            }
        }
    }
}

impl<C> MaybeTransmutableQuery<Tree<<C as QueryContext>::Def, <C as QueryContext>::Ref>, C>
where
    C: QueryContext,
{
    /// Answers whether a `Tree` is transmutable into another `Tree`.
    ///
    /// This method begins by de-def'ing `src` and `dst`, and prunes private paths from `dst`,
    /// then converts `src` and `dst` to `Nfa`s, and computes an answer using those NFAs.
    #[inline(always)]
    #[instrument(level = "debug", skip(self), fields(src = ?self.src, dst = ?self.dst))]
    pub(crate) fn answer(self) -> Answer<<C as QueryContext>::Ref> {
        let assume_visibility = self.assume.safety;
        let query_or_answer = self.map_layouts(|src, dst, scope, context| {
            // Remove all `Def` nodes from `src`, without checking their visibility.
            let src = src.prune(&|def| true);

            trace!(?src, "pruned src");

            // Remove all `Def` nodes from `dst`, additionally...
            let dst = if assume_visibility {
                // ...if visibility is assumed, don't check their visibility.
                dst.prune(&|def| true)
            } else {
                // ...otherwise, prune away all unreachable paths through the `Dst` layout.
                dst.prune(&|def| context.is_accessible_from(def, scope))
            };

            trace!(?dst, "pruned dst");

            // Convert `src` from a tree-based representation to an NFA-based representation.
            // If the conversion fails because `src` is uninhabited, conclude that the transmutation
            // is acceptable, because instances of the `src` type do not exist.
            let src = Nfa::from_tree(src).map_err(|Uninhabited| Answer::Yes)?;

            // Convert `dst` from a tree-based representation to an NFA-based representation.
            // If the conversion fails because `src` is uninhabited, conclude that the transmutation
            // is unacceptable, because instances of the `dst` type do not exist.
            let dst =
                Nfa::from_tree(dst).map_err(|Uninhabited| Answer::No(Reason::DstIsPrivate))?;

            Ok((src, dst))
        });

        match query_or_answer {
            Ok(query) => query.answer(),
            Err(answer) => answer,
        }
    }
}

impl<C> MaybeTransmutableQuery<Nfa<<C as QueryContext>::Ref>, C>
where
    C: QueryContext,
{
    /// Answers whether a `Nfa` is transmutable into another `Nfa`.
    ///
    /// This method converts `src` and `dst` to DFAs, then computes an answer using those DFAs.
    #[inline(always)]
    #[instrument(level = "debug", skip(self), fields(src = ?self.src, dst = ?self.dst))]
    pub(crate) fn answer(self) -> Answer<<C as QueryContext>::Ref> {
        let query_or_answer = self
            .map_layouts(|src, dst, scope, context| Ok((Dfa::from_nfa(src), Dfa::from_nfa(dst))));

        match query_or_answer {
            Ok(query) => query.answer(),
            Err(answer) => answer,
        }
    }
}

impl<C> MaybeTransmutableQuery<Dfa<<C as QueryContext>::Ref>, C>
where
    C: QueryContext,
{
    /// Answers whether a `Nfa` is transmutable into another `Nfa`.
    ///
    /// This method converts `src` and `dst` to DFAs, then computes an answer using those DFAs.
    pub(crate) fn answer(self) -> Answer<<C as QueryContext>::Ref> {
        MaybeTransmutableQuery {
            src: &self.src,
            dst: &self.dst,
            scope: self.scope,
            assume: self.assume,
            context: self.context,
        }
        .answer()
    }
}

impl<'l, C> MaybeTransmutableQuery<&'l Dfa<<C as QueryContext>::Ref>, C>
where
    C: QueryContext,
{
    pub(crate) fn answer(&mut self) -> Answer<<C as QueryContext>::Ref> {
        self.answer_memo(&mut Map::default(), self.src.start, self.dst.start)
    }

    #[inline(always)]
    #[instrument(level = "debug", skip(self))]
    fn answer_memo(
        &self,
        cache: &mut Map<(dfa::State, dfa::State), Answer<<C as QueryContext>::Ref>>,
        src_state: dfa::State,
        dst_state: dfa::State,
    ) -> Answer<<C as QueryContext>::Ref> {
        if let Some(answer) = cache.get(&(src_state, dst_state)) {
            answer.clone()
        } else {
            let answer = if dst_state == self.dst.accepting {
                // truncation: `size_of(Src) >= size_of(Dst)`
                Answer::Yes
            } else if src_state == self.src.accepting {
                // extension: `size_of(Src) >= size_of(Dst)`
                if let Some(dst_state_prime) = self.dst.byte_from(dst_state, Byte::Uninit) {
                    self.answer_memo(cache, src_state, dst_state_prime)
                } else {
                    Answer::No(Reason::DstIsTooBig)
                }
            } else {
                // How should we reduce potential paths through the types into answers about transmutability?
                let (initial, operator, is_anihilator): (_, fn(_, _) -> _, for<'a> fn(&'a _) -> _) =
                    if self.assume.validity {
                        // if the compiler may assume that the programmer is doing additional validity checks,
                        // (e.g.: that `src != 3u8` when the destination type is `bool`)
                        // then there must exist at least one transition out of `src_state` such that the transmute is viable...
                        (Answer::No(Reason::DstIsBitIncompatible), Answer::or, Answer::is_yes)
                    } else {
                        // if the compiler cannot assume that the programmer is doing additional validity checks,
                        // then for all transitions out of `src_state`, such that the transmute is viable...
                        // then there must exist at least one transition out of `src_state` such that the transmute is viable...
                        (Answer::Yes, Answer::and, Answer::is_no)
                    };

                let via_bytes = self
                    .src
                    .bytes_from(src_state)
                    .unwrap_or(&Map::default())
                    .into_iter()
                    .map(|(&src_validity, &src_state_prime)| {
                        if let Some(dst_state_prime) = self.dst.byte_from(dst_state, src_validity) {
                            self.answer_memo(cache, src_state_prime, dst_state_prime)
                        } else if let Some(dst_state_prime) =
                            self.dst.byte_from(dst_state, Byte::Uninit)
                        {
                            self.answer_memo(cache, src_state_prime, dst_state_prime)
                        } else {
                            Answer::No(Reason::DstIsBitIncompatible)
                        }
                    })
                    .reduce_answers(initial, operator, is_anihilator);

                if is_anihilator(&via_bytes) {
                    return via_bytes;
                }

                self.src
                    .refs_from(src_state)
                    .unwrap_or(&Map::default())
                    .into_iter()
                    .map(|(&src_ref, &src_state_prime)| {
                        self.dst
                            .refs_from(dst_state)
                            .unwrap_or(&Map::default())
                            .into_iter()
                            .map(|(&dst_ref, &dst_state_prime)| {
                                Answer::IfTransmutable { src: src_ref, dst: dst_ref }
                                    .and(self.answer_memo(cache, src_state_prime, dst_state_prime))
                            })
                            .reduce_answers(
                                Answer::No(Reason::DstIsBitIncompatible),
                                Answer::or,
                                Answer::is_yes,
                            )
                    })
                    .reduce_answers(via_bytes, operator, is_anihilator)
            };
            cache.insert((src_state, dst_state), answer.clone());
            answer
        }
    }
}

impl<R> Answer<R>
where
    R: layout::Ref,
{
    pub(crate) fn and(self, rhs: Self) -> Self {
        match (self, rhs) {
            (_, Self::No(reason)) | (Self::No(reason), _) => Self::No(reason),
            (Self::Yes, Self::Yes) => Self::Yes,
            (Self::IfAll(mut lhs), Self::IfAll(ref mut rhs)) => {
                lhs.append(rhs);
                Self::IfAll(lhs)
            }
            (constraint, Self::IfAll(mut constraints))
            | (Self::IfAll(mut constraints), constraint) => {
                constraints.push(constraint);
                Self::IfAll(constraints)
            }
            (lhs, rhs) => Self::IfAll(vec![lhs, rhs]),
        }
    }

    pub(crate) fn or(self, rhs: Self) -> Self {
        match (self, rhs) {
            (Self::Yes, _) | (_, Self::Yes) => Self::Yes,
            (Self::No(lhr), Self::No(rhr)) => Self::No(lhr),
            (Self::IfAny(mut lhs), Self::IfAny(ref mut rhs)) => {
                lhs.append(rhs);
                Self::IfAny(lhs)
            }
            (constraint, Self::IfAny(mut constraints))
            | (Self::IfAny(mut constraints), constraint) => {
                constraints.push(constraint);
                Self::IfAny(constraints)
            }
            (lhs, rhs) => Self::IfAny(vec![lhs, rhs]),
        }
    }
}

trait IterExt<R>: Iterator<Item = Answer<R>>
where
    R: layout::Ref,
    Self: Sized,
{
    fn reduce_answers(
        mut self,
        initial: Answer<R>,
        operator: impl Fn(Answer<R>, Answer<R>) -> Answer<R>,
        is_anihilator: impl Fn(&Answer<R>) -> bool,
    ) -> Answer<R> {
        use std::ops::ControlFlow::{Break, Continue};
        let (Continue(result) | Break(result)) = self.try_fold(initial, |answers, answer| {
            let answer = operator(answers, answer);
            if is_anihilator(&answer) { Break(answer) } else { Continue(answer) }
        });
        result
    }
}

impl<R, I> IterExt<R> for I
where
    R: layout::Ref,
    I: Iterator<Item = Answer<R>>,
{
}
